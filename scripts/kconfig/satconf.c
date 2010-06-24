#include <assert.h>
#include <locale.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define LKC_DIRECT_LINK
#include "bitset.h"
#include "cnf.h"
#include "lkc.h"
#include "picosat.h"

static unsigned int nr_sat_variables;
static struct symbol **sat_variables;

static void assign_sat_variables(void)
{
	unsigned int i;
	struct symbol *sym;
	unsigned int variable = 0;

	assert(nr_sat_variables == 0);

	/* The solver uses variable 0 as an end-of-clause marker. */
	++nr_sat_variables;

	/* Just count the number of variables we'll need */
	for_all_symbols(i, sym) {
		switch (sym->type) {
		case S_BOOLEAN:
			nr_sat_variables += 1;
			break;
		case S_TRISTATE:
			nr_sat_variables += 2;
			break;
		default:
			break;
		}
	}

	sat_variables = malloc(nr_sat_variables * sizeof(*sat_variables));
	sat_variables[variable++] = NULL;

	/* Assign variables to each symbol */
	for_all_symbols(i, sym) {
		switch (sym->type) {
		case S_BOOLEAN:
			sym->sat_variable = variable;
			sat_variables[variable++] = sym;
			break;
		case S_TRISTATE:
			sym->sat_variable = variable;
			sat_variables[variable++] = sym;
			sat_variables[variable++] = sym;
			break;
		default:
			break;
		}
	}

	assert(variable == nr_sat_variables);

	printf("%u variables\n", nr_sat_variables);
}

enum bool_op {
	CONST,
	VAR,

	NOT,
	AND,
	OR,
};

struct bool_expr {
	enum bool_op op;

	union {
		bool nullary;
		unsigned int var;

		struct bool_expr *unary;
		struct {
			struct bool_expr *a;
			struct bool_expr *b;
		} binary;
	};

	/* The reference counting rules: Every time a pointer is stored in
	 * a heap structure, it should have its reference count incremented.
	 * Constructors that take arguments therefore typically increment
	 * the reference counts of its arguments. Temporary objects (those
	 * that are constructed only for the purpose of being passed to
	 * another function) should have their reference count decremented
	 * before that function returns. */
	unsigned int refcount;
};

/* When the program exits, the number of destroyed bools should equal the
 * number of created bools. This is for leak debugging. */
static unsigned int nr_bool_created = 0;
static unsigned int nr_bool_destroyed = 0;

static struct bool_expr *bool_new(enum bool_op op)
{
	struct bool_expr *e = malloc(sizeof(*e));
	assert(e);

	e->op = op;
	e->refcount = 1;

	++nr_bool_created;
	return e;
}

static struct bool_expr *bool_get(struct bool_expr *e)
{
	assert(e->refcount > 0);

	++e->refcount;
	return e;
}

static void bool_put(struct bool_expr *e)
{
	assert(e->refcount > 0);

	--e->refcount;
	if (e->refcount == 0) {
		switch (e->op) {
		case NOT:
			bool_put(e->unary);
			break;
		case AND:
		case OR:
			bool_put(e->binary.a);
			bool_put(e->binary.b);
			break;
		default:
			break;
		}

		++nr_bool_destroyed;
		free(e);
	}
}

static void bool_printf(struct bool_expr *e)
{
	switch (e->op) {
	case CONST:
		printf("%s", e->nullary ? "T" : "F");
		break;
	case VAR:
		printf("%u/%s", e->var, sat_variables[e->var]->name ?: "<unknown>");
		break;
	case NOT:
		printf("!");
		bool_printf(e->unary);
		break;
	case AND:
		printf("(");
		bool_printf(e->binary.a);
		printf(" && ");
		bool_printf(e->binary.b);
		printf(")");
		break;
	case OR:
		printf("(");
		bool_printf(e->binary.a);
		printf(" || ");
		bool_printf(e->binary.b);
		printf(")");
		break;
	default:
		assert(false);
	}
}

static bool bool_equal(struct bool_expr *a, struct bool_expr *b)
{
	if (a == b)
		return true;

	if (a->op != b->op)
		return false;

	switch (a->op) {
	case CONST:
		return a->nullary == b->nullary;

	case VAR:
		return a->var == b->var;

	case NOT:
		return bool_equal(a->unary, b->unary);

	case AND:
	case OR:
		return bool_equal(a->binary.a, b->binary.a) && bool_equal(a->binary.b, b->binary.b);
	default:
		assert(false);
	}
}

static struct bool_expr *bool_and(struct bool_expr *a, struct bool_expr *b);
static struct bool_expr *bool_or(struct bool_expr *a, struct bool_expr *b);

static struct bool_expr *bool_const(bool v)
{
	static struct bool_expr bool_true = {
		.op = CONST,
		{ .nullary = true, },
		.refcount = 1,
	};

	static struct bool_expr bool_false = {
		.op = CONST,
		{ .nullary = false, },
		.refcount = 1,
	};

	return bool_get(v ? &bool_true : &bool_false);
}

static struct bool_expr *bool_var(unsigned int var)
{
	struct bool_expr *e = bool_new(VAR);
	e->var = var;
	return e;
}

static struct bool_expr *bool_not(struct bool_expr *expr)
{
	if (expr->op == VAR) {
		struct bool_expr *e = bool_new(NOT);
		e->unary = bool_get(expr);
		return e;
	}

	switch (expr->op) {
	case CONST:
		return bool_const(!expr->nullary);

	case NOT:
		/* !!x => x */
		return bool_get(expr->unary);

	case AND:
	{
		/* !(a && b) => !a || !b */
		struct bool_expr *t1, *t2, *ret;

		t1 = bool_not(expr->binary.a);
		t2 = bool_not(expr->binary.b);
		ret = bool_or(t1, t2);

		bool_put(t1);
		bool_put(t2);
		return ret;
	}

	case OR:
	{
		/* !(a || b) => !a && !b */
		struct bool_expr *t1, *t2, *ret;

		t1 = bool_not(expr->binary.a);
		t2 = bool_not(expr->binary.b);
		ret = bool_and(t1, t2);

		bool_put(t1);
		bool_put(t2);
		return ret;
	}

	default:
		assert(false);
	}
}

static struct bool_expr *bool_and(struct bool_expr *a, struct bool_expr *b)
{
	if (a->op == CONST)
		return bool_get(a->nullary ? b : a);
	if (b->op == CONST)
		return bool_get(b->nullary ? a : b);

	struct bool_expr *e = bool_new(AND);
	e->binary.a = bool_get(a);
	e->binary.b = bool_get(b);
	return e;
}

static struct bool_expr *bool_or(struct bool_expr *a, struct bool_expr *b)
{
	if (a->op == CONST)
		return bool_get(a->nullary ? a : b);
	if (b->op == CONST)
		return bool_get(b->nullary ? b : a);

	struct bool_expr *e = bool_new(OR);
	e->binary.a = bool_get(a);
	e->binary.b = bool_get(b);
	return e;
}

static struct bool_expr *bool_dep(struct bool_expr *a, struct bool_expr *b)
{
	struct bool_expr *t = bool_not(a);
	struct bool_expr *ret = bool_or(t, b);

	bool_put(t);
	return ret;
}

static struct bool_expr *bool_eq(struct bool_expr *a, struct bool_expr *b)
{
	/* XXX: Introduce extra variables */

	/* a == b => (a && b) || (!a && !b) */
	struct bool_expr *t1 = bool_and(a, b);
	struct bool_expr *t2 = bool_not(a);
	struct bool_expr *t3 = bool_not(b);
	struct bool_expr *t4 = bool_and(t2, t3);
	struct bool_expr *ret = bool_or(t1, t4);

	bool_put(t1);
	bool_put(t2);
	bool_put(t3);
	bool_put(t4);
	return ret;
}

static void expr_to_bool_expr(struct symbol *lhs, struct expr *e, struct bool_expr *result[2]);

static void symbol_to_bool_expr(struct symbol *sym, struct bool_expr *result[2])
{
	if (sym == &symbol_no) {
		result[0] = bool_const(false);
		result[1] = bool_const(false);
		return;
	}

	if (sym == &symbol_mod) {
		result[0] = bool_const(true);
		result[1] = bool_const(true);
		return;
	}

	if (sym == &symbol_yes) {
		result[0] = bool_const(true);
		result[1] = bool_const(false);
		return;
	}

	switch (sym->type) {
	case S_UNKNOWN:
		/* XXX: Is this correct? */
		result[0] = bool_const(false);
		result[1] = bool_const(false);
		return;
	case S_BOOLEAN:
		result[0] = bool_var(sym->sat_variable);
		result[1] = bool_const(false);
		return;
	case S_TRISTATE:
		result[0] = bool_var(sym->sat_variable);
		result[1] = bool_var(sym->sat_variable + 1);
		return;
	default:
		printf("%s %d\n", sym->name, sym->type);
		assert(false);
	}
}

static void or_expr_to_bool_expr(struct symbol *lhs,
	struct expr *in_a, struct expr *in_b, struct bool_expr *out[2])
{
	struct bool_expr *a[2];
	struct bool_expr *b[2];
	struct bool_expr *t1, *t2, *t3, *t4;

	expr_to_bool_expr(lhs, in_a, a);
	expr_to_bool_expr(lhs, in_b, b);

	t1 = bool_or(a[0], a[1]);
	t2 = bool_or(b[0], b[1]);

	out[0] = bool_or(t1, t2);
	bool_put(t1);
	bool_put(t2);

	t1 = bool_or(a[1], b[1]);
	t2 = bool_dep(a[0], a[1]);
	t3 = bool_dep(b[0], b[1]);
	t4 = bool_and(t2, t3);

	out[1] = bool_and(t1, t4);
	bool_put(t1);
	bool_put(t2);
	bool_put(t3);
	bool_put(t4);

	bool_put(a[0]);
	bool_put(a[1]);
	bool_put(b[0]);
	bool_put(b[1]);
}

static void and_expr_to_bool_expr(struct symbol *lhs,
	struct expr *in_a, struct expr *in_b, struct bool_expr *out[2])
{
	struct bool_expr *a[2];
	struct bool_expr *b[2];
	struct bool_expr *t1, *t2;

	expr_to_bool_expr(lhs, in_a, a);
	expr_to_bool_expr(lhs, in_b, b);

	out[0] = bool_and(a[0], b[0]);

	t1 = bool_and(a[0], b[1]);
	t2 = bool_and(a[1], b[0]);

	out[1] = bool_or(t1, t2);
	bool_put(t1);
	bool_put(t2);

	bool_put(a[0]);
	bool_put(a[1]);
	bool_put(b[0]);
	bool_put(b[1]);
}

static void not_expr_to_bool_expr(struct symbol *lhs,
	struct expr *in, struct bool_expr *out[2])
{
	struct bool_expr *e[2];

	expr_to_bool_expr(lhs, in, e);

	out[0] = bool_dep(e[0], e[1]);
	out[1] = e[1];

	bool_put(e[0]);
	/* bool_put(e[1]); */
}

static struct bool_expr *equal_expr_to_bool_expr(struct symbol *in_a, struct symbol *in_b)
{
	switch (in_a->type) {
	case S_UNKNOWN:
		/* XXX */
		return bool_const(in_a == in_b);
	case S_BOOLEAN:
	case S_TRISTATE:
	{
		struct bool_expr *a[2];
		struct bool_expr *b[2];
		struct bool_expr *t1, *t2, *ret;

		symbol_to_bool_expr(in_a, a);
		symbol_to_bool_expr(in_b, b);

		t1 = bool_eq(a[0], b[0]);
		t2 = bool_eq(a[1], b[1]);
		ret = bool_and(t1, t2);

		bool_put(t1);
		bool_put(t2);
		bool_put(a[0]);
		bool_put(a[1]);
		bool_put(b[0]);
		bool_put(b[1]);
		return ret;
	}
	case S_INT:
	case S_HEX:
	case S_STRING: {
		const char *a_str = sym_get_string_value(in_a);
		const char *b_str = sym_get_string_value(in_b);

		if (!a_str || !b_str) {
			fprintf(stderr, "warning: Undefined value for string: %s\n", in_a->name);
			return bool_const(false);
		}

		return bool_const(strcmp(a_str, b_str) == 0);
	}
	default:
		printf("%d %d\n", in_a->type, in_b->type);
		assert(false);
	}
}

static void expr_to_bool_expr(struct symbol *lhs, struct expr *e, struct bool_expr *result[2])
{
	switch (e->type) {
	case E_OR:
		or_expr_to_bool_expr(lhs, e->left.expr, e->right.expr, result);
		return;
	case E_AND:
		and_expr_to_bool_expr(lhs, e->left.expr, e->right.expr, result);
		return;
	case E_NOT:
		not_expr_to_bool_expr(lhs, e->left.expr, result);
		return;
	case E_EQUAL:
		result[0] = equal_expr_to_bool_expr(e->left.sym, e->right.sym);
		result[1] = bool_const(false);
		return;
	case E_UNEQUAL:
	{
		struct bool_expr *t;

		t = equal_expr_to_bool_expr(e->left.sym, e->right.sym);
		result[0] = bool_not(t);
		result[1] = bool_const(false);
		bool_put(t);
		return;
	}
	case E_LIST:
		break;
	case E_SYMBOL:
		if (!lhs) {
			symbol_to_bool_expr(e->left.sym, result);
			return;
		}

		/* This is a special case. If you "depends on m", it means
		 * that the value of the left-hand side symbol can only be
		 * "m" or "n". */
		/* XXX: In the future (when only satconfig is used), we
		 * should get rid of the "depends on m" special case
		 * altogether and rewrite those as "depends on SELF=m". */
		if (e->left.sym == &symbol_mod) {
			assert(lhs->type == S_TRISTATE);

			struct bool_expr *t1, *t2;

			t1 = bool_var(lhs->sat_variable);
			t2 = bool_var(lhs->sat_variable + 1);
			result[0] = bool_dep(t1, t2);
			result[1] = bool_const(false);

			bool_put(t1);
			bool_put(t2);
			return;
		}

		/* An undefined symbol typically means that something was
		 * defined only in some architectures' kconfig files, but
		 * was referenced in an arch-independent kconfig files.
		 *
		 * Assume it to be false. */
		if (!e->left.sym->name || e->left.sym->type == S_UNKNOWN) {
			result[0] = bool_const(false);
			result[1] = bool_const(false);
			return;
		}

		result[0] = bool_var(e->left.sym->sat_variable);
		result[1] = bool_const(false);
		return;
	case E_RANGE:
		break;
	default:
		assert(false);
	}

	printf("%d\n", e->type);
	assert(false);
}

static struct cnf *bool_to_cnf(struct bool_expr *e)
{
	switch (e->op) {
	case CONST:
		assert(e->nullary);
		return cnf_new();

	case VAR:
		return cnf_new_single_positive(nr_sat_variables, e->var);

	case NOT:
		assert(e->unary->op == VAR);
		return cnf_new_single_negative(nr_sat_variables, e->unary->var);

	case AND: {
		struct cnf *t1, *t2, *ret;

		t1 = bool_to_cnf(e->binary.a);
		t2 = bool_to_cnf(e->binary.b);
		ret = cnf_and(t1, t2);

		cnf_put(t1);
		cnf_put(t2);
		return ret;
	}

	case OR: {
		struct cnf *t1, *t2, *ret;

		t1 = bool_to_cnf(e->binary.a);
		t2 = bool_to_cnf(e->binary.b);
		ret = cnf_or(t1, t2);

		cnf_put(t1);
		cnf_put(t2);
		return ret;
	}

	default:
		printf("%d\n", e->op);
		assert(false);
	}
}

static void add_positive(unsigned int bit)
{
	picosat_add(bit);
}

static void add_negative(unsigned int bit)
{
	picosat_add(-bit);
}

static void add_clause(struct cnf_clause *clause)
{

	if (clause->positive)
		bitset_call_for_each_bit(clause->positive, &add_positive);
	if (clause->negative)
		bitset_call_for_each_bit(clause->negative, &add_negative);
	picosat_add(0);

}

static void add_cnf(struct cnf *cnf)
{
	struct cnf_clause *i;

	for (i = cnf->first; i; i = i->next)
		add_clause(i);
}

static bool build_clauses(void)
{
	unsigned int i;
	struct symbol *sym;
	struct symbol *modules_sym = sym_find("MODULES");
	assert(modules_sym);

	for_all_symbols(i, sym) {
		struct property *prop;

		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		if (sym->type == S_TRISTATE) {
			struct bool_expr *t1, *t2, *t3, *t4;
			struct cnf *t5;

			t1 = bool_var(sym->sat_variable);
			t2 = bool_var(sym->sat_variable + 1);
			t3 = bool_var(modules_sym->sat_variable);

			/* Add the VAR_m -> VAR restriction */
			t4 = bool_dep(t2, t1);
			t5 = bool_to_cnf(t4);

			add_cnf(t5);

			bool_put(t4);
			cnf_put(t5);

			/* Add the VAR_m -> MODULES restriction */
			t4 = bool_dep(t2, t3);
			t5 = bool_to_cnf(t4);

			add_cnf(t5);

			bool_put(t4);
			cnf_put(t5);

			bool_put(t1);
			bool_put(t2);
			bool_put(t3);
		}

		/* Add "depends on" dependencies */
		for_all_prompts(sym, prop) {
			struct bool_expr *e[2];
			struct bool_expr *t1, *t2;
			struct cnf *t3;

			if (!prop->visible.expr)
				continue;

			expr_to_bool_expr(sym, prop->visible.expr, e);

			t1 = bool_var(sym->sat_variable);
			t2 = bool_dep(t1, e[0]);
			t3 = bool_to_cnf(t2);

			add_cnf(t3);

			bool_put(e[0]);
			bool_put(e[1]);
			bool_put(t1);
			bool_put(t2);
			cnf_put(t3);
		}

		/* Add "select" dependencies */
		for_all_properties(sym, prop, P_SELECT) {
			struct bool_expr *e[2];
			struct bool_expr *t1, *t2;
			struct cnf *t3;

			expr_to_bool_expr(sym, prop->expr, e);

			t1 = bool_var(sym->sat_variable);
			t2 = bool_dep(t1, e[0]);
			t3 = bool_to_cnf(t2);

			add_cnf(t3);

			bool_put(e[0]);
			bool_put(e[1]);
			bool_put(t1);
			bool_put(t2);
			cnf_put(t3);
		}

		/* Assign default values to options with no prompt */
		/* XXX: Do this for non-bool/non-tristate options too */
		if (!sym_has_prompt(sym)) {
			struct bool_expr *symbol_value[2];
			symbol_to_bool_expr(sym, symbol_value);

			struct property *prop;
			for_all_defaults(sym, prop) {
				struct bool_expr *condition[2];
				struct bool_expr *value[2];
				struct bool_expr *t1, *t2, *t3, *t4;
				struct cnf *t5;

				if (prop->menu && prop->menu->dep) {
					expr_to_bool_expr(sym, prop->menu->dep, condition);
				} else {
					condition[0] = bool_const(true);
					/* Not used */
					condition[1] = bool_const(false);
				}

				assert(prop->expr);
				expr_to_bool_expr(NULL, prop->expr, value);

				t1 = bool_eq(value[0], symbol_value[0]);
				t2 = bool_eq(value[1], symbol_value[1]);
				t3 = bool_and(t1, t2);
				t4 = bool_dep(condition[0], t3);

				t5 = bool_to_cnf(t4);

				add_cnf(t5);

				bool_put(condition[0]);
				bool_put(condition[1]);
				bool_put(value[0]);
				bool_put(value[1]);
				bool_put(t1);
				bool_put(t2);
				bool_put(t3);
				bool_put(t4);
				cnf_put(t5);
			}

			bool_put(symbol_value[0]);
			bool_put(symbol_value[1]);
		}
	}

	return true;
}

int main(int argc, char *argv[])
{
	setlocale(LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);

	picosat_init();
	picosat_set_global_default_phase(-1);

	conf_parse(argv[1]);

	/* XXX: We need this to initialise values for non-boolean (and non-
	 * tristate) variables. This should go away when we read .satconfig
	 * instead for these kinds of variables. */
	conf_read_simple(NULL, S_DEF_USER);
	conf_read_simple(".satconfig", S_DEF_SAT);

	{
		/* We need to do this in order to give strings from the
		 * environment get their values in the proper place. It
		 * is also necessary for INT/HEX values, but doesn't
		 * seem to make any difference for BOOL/TRISTATE
		 * variables (we set them below anyway). */
		unsigned int i;
		struct symbol *sym;
		for_all_symbols(i, sym) {
			if (sym->flags & (SYMBOL_DEF << S_DEF_SAT))
				sym->curr = sym->def[S_DEF_SAT];
			else if (sym->flags & (SYMBOL_DEF << S_DEF_USER))
				sym->curr = sym->def[S_DEF_USER];
		}
	}

	assign_sat_variables();
	picosat_adjust(nr_sat_variables);

	{
		/* Modules are preferred over built-ins; tell that to the
		 * solver. XXX: This is rather fragile, there is a
		 * possibility that this can all go away when proper
		 * support for default values has been added. */
		unsigned int i;
		struct symbol *sym;
		for_all_symbols(i, sym) {
			if (sym->type != S_TRISTATE)
				continue;

			picosat_set_default_phase_lit(sym->sat_variable + 1, 1);
		}
	}

	{
		struct symbol *modules_sym = sym_find("MODULES");
		assert(modules_sym);

		picosat_set_default_phase_lit(modules_sym->sat_variable, 1);
	}

	if (!build_clauses()) {
		fprintf(stderr, "error: inconsistent kconfig files while "
			"building clauses\n");
		exit(EXIT_FAILURE);
	}

	assert(nr_bool_created == nr_bool_destroyed);

	{
		/* First do a check to see if the instance is solvable
		 * without any assumptions. If this is not the case, then
		 * something is weird with the kconfig files. */
		int sat = picosat_sat(-1);
		unsigned int i;

		if (sat != PICOSAT_SATISFIABLE) {
			fprintf(stderr, "error: inconsistent kconfig files\n");
			exit(EXIT_FAILURE);
		}
	}

	{
		/* Use assumptions */
		unsigned int i;
		struct symbol *sym;
		for_all_symbols(i, sym) {
			if (!(sym->flags & (SYMBOL_DEF << S_DEF_SAT)))
				continue;
			if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
				continue;

			switch (sym->curr.tri) {
			case no:
				picosat_assume(-sym->sat_variable);
				break;
			case yes:
				picosat_assume(sym->sat_variable);
				break;
			case mod:
				assert(sym->type == S_TRISTATE);
				picosat_assume(sym->sat_variable + 1);
				break;
			}
		}
	}

	{
		int sat = picosat_sat(-1);
		unsigned int i;

		if (sat != PICOSAT_SATISFIABLE) {
			fprintf(stderr, "error: unsatisfiable constraints\n");
			exit(EXIT_FAILURE);
		}

		struct symbol *sym;
		for_all_symbols(i, sym) {
			struct property *prop;

			if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
				continue;

			{
				int v = picosat_deref(sym->sat_variable);
				assert(v != 0);

				if (v == 1)
					sym->curr.tri = yes;
				else if (v == -1)
					sym->curr.tri = no;
			}

			if (sym->type == S_TRISTATE) {
				int v = picosat_deref(sym->sat_variable + 1);
				assert(v != 0);

				if (v == 1)
					sym->curr.tri = mod;
			}

			sym->flags |= SYMBOL_VALID;
			sym->flags |= SYMBOL_WRITE;
		}
	}

	if (conf_write(".config")) {
		fprintf(stderr, "error: writing configuration\n");
		exit(EXIT_FAILURE);
	}

	printf("ok\n");
	return EXIT_SUCCESS;
}
