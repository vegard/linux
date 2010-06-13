#include <assert.h>
#include <locale.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define LKC_DIRECT_LINK
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

/* XXX: Reference count */
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
};

static void bool_printf(struct bool_expr *e)
{
	switch (e->op) {
	case CONST:
		printf("%s", e->nullary ? "T" : "F");
		break;
	case VAR:
		printf("%u", e->var);
		//printf("%u/%s", e->var, sat_variables[e->var]->name ?: "<unknown>");
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
	struct bool_expr *e = malloc(sizeof(*e));
	assert(e);

	e->op = CONST;
	e->nullary = v;
	return e;
}

static struct bool_expr *bool_var(unsigned int var)
{
	struct bool_expr *e = malloc(sizeof(*e));
	assert(e);

	e->op = VAR;
	e->var = var;
	return e;
}

static struct bool_expr *bool_not(struct bool_expr *expr)
{
	if (expr->op == VAR) {
		struct bool_expr *e = malloc(sizeof(*e));
		assert(e);

		e->op = NOT;
		e->unary = expr;
		return e;
	}

	switch (expr->op) {
	case CONST:
		return bool_const(!expr->nullary);

	case NOT:
		/* !!x => x */
		return expr->unary;

	case AND:
		/* !(a && b) => !a || !b */
		return bool_or(bool_not(expr->binary.a), bool_not(expr->binary.b));

	case OR:
		/* !(a || b) => !a && !b */
		return bool_and(bool_not(expr->binary.a), bool_not(expr->binary.b));

	default:
		assert(false);
	}
}

static struct bool_expr *bool_and(struct bool_expr *a, struct bool_expr *b)
{
	if (a->op == CONST)
		return a->nullary ? b : a;
	if (b->op == CONST)
		return b->nullary ? a : b;

	struct bool_expr *e = malloc(sizeof(*e));
	assert(e);

	e->op = AND;
	e->binary.a = a;
	e->binary.b = b;
	return e;
}

static struct bool_expr *bool_or(struct bool_expr *a, struct bool_expr *b)
{
	if (a->op == CONST)
		return a->nullary ? a : b;
	if (b->op == CONST)
		return b->nullary ? b : a;

	struct bool_expr *e = malloc(sizeof(*e));
	assert(e);

	e->op = OR;
	e->binary.a = a;
	e->binary.b = b;
	return e;
}

static struct bool_expr *bool_dep(struct bool_expr *a, struct bool_expr *b)
{
	return bool_or(bool_not(a), b);
}

static struct bool_expr *bool_eq(struct bool_expr *a, struct bool_expr *b)
{
	/* XXX: Introduce extra variables */

	/* a == b => (a && b) || (!a && !b) */
	return bool_or(bool_and(a, b), bool_and(bool_not(a), bool_not(b)));
}

static struct bool_expr *equal_expr_to_bool_expr(struct symbol *left, struct symbol *right)
{
	assert(left != &symbol_no);
	assert(left != &symbol_yes);
	assert(left != &symbol_mod);

	if (left->type == S_UNKNOWN) {
		if (right == &symbol_no)
			return bool_const(true);
		if (right == &symbol_yes)
			return bool_const(false);
		if (right == &symbol_mod)
			return bool_const(false);

		assert(false);
	}

	/* We can't solve for non-boolean variables */
	if (left->type == S_INT
		|| left->type == S_HEX
		|| left->type == S_STRING)
	{
		if (!sym_get_string_value(left) || !sym_get_string_value(right)) {
			fprintf(stderr, "warning: Undefined value for string: %s\n", left->name);
			return bool_const(false);
		}

		return bool_const(strcmp(sym_get_string_value(left),
					 sym_get_string_value(right)) == 0);
	}

	assert(left->type == S_BOOLEAN
		|| left->type == S_TRISTATE);

	if (right == &symbol_no)
		return bool_not(bool_var(left->sat_variable));

	if (right == &symbol_yes)
		return bool_var(left->sat_variable);

	if (right == &symbol_mod) {
		assert(left->type == S_TRISTATE);
		return bool_var(left->sat_variable + 1);
	}

	if (left->type == S_BOOLEAN) {
		return bool_eq(bool_var(left->sat_variable),
			       bool_var(right->sat_variable));
	}

	if (left->type == S_TRISTATE) {
		return bool_and(bool_eq(bool_var(left->sat_variable),
					bool_var(right->sat_variable)),
				bool_eq(bool_var(left->sat_variable + 1),
					bool_var(right->sat_variable + 1)));
	}

	assert(false);
}

/* Convert a kconfig expression into a purely boolean expression */
static struct bool_expr *expr_to_bool_expr(struct symbol *lhs, struct expr *e)
{
	switch (e->type) {
	case E_OR:
		return bool_or(expr_to_bool_expr(lhs, e->left.expr),
			       expr_to_bool_expr(lhs, e->right.expr));
	case E_AND:
		return bool_and(expr_to_bool_expr(lhs, e->left.expr),
			        expr_to_bool_expr(lhs, e->right.expr));
	case E_NOT:
		return bool_not(expr_to_bool_expr(lhs, e->left.expr));
	case E_EQUAL:
		return equal_expr_to_bool_expr(e->left.sym, e->right.sym);
	case E_UNEQUAL:
		return bool_not(equal_expr_to_bool_expr(e->left.sym, e->right.sym));
	case E_LIST:
		break;
	case E_SYMBOL:
		/* This is a special case. If you "depend on m", it means
		 * that the value of the left-hand side symbol can only be
		 * "m" or "n". */
		if (e->left.sym == &symbol_mod) {
			assert(lhs->type == S_TRISTATE);

			/* We already have the VAR_m -> VAR clause, so we
			 * only need to add VAR -> VAR_m to make it a bi-
			 * conditional. */
			return bool_dep(bool_var(lhs->sat_variable),
					bool_var(lhs->sat_variable + 1));
		}

		/* An undefined symbol typically means that something was
		 * defined only in some architectures' kconfig files, but
		 * was referenced in an arch-independent kconfig files.
		 *
		 * Assume it to be false. */
		if (!e->left.sym->name)
			return bool_const(false);
		if (e->left.sym->type == S_UNKNOWN)
			return bool_const(false);

		return bool_var(e->left.sym->sat_variable);
	case E_RANGE:
		break;
	default:
		assert(false);
	}

	assert(false);
}

static struct bool_expr *bool_to_cnf(struct bool_expr *e)
{
	/* XXX: All of this is hugely inefficient */
	if (e->op == AND) {
		return bool_and(bool_to_cnf(e->binary.a),
				bool_to_cnf(e->binary.b));
	}

	if (e->op == OR) {
		struct bool_expr *a = bool_to_cnf(e->binary.a);
		struct bool_expr *b = bool_to_cnf(e->binary.b);

		if (a->op == AND) {
			return bool_and(bool_to_cnf(bool_or(b, a->binary.a)),
					bool_to_cnf(bool_or(b, a->binary.b)));
		}

		if (b->op == AND) {
			return bool_and(bool_to_cnf(bool_or(a, b->binary.a)),
					bool_to_cnf(bool_or(a, b->binary.b)));
		}

		return bool_or(a, b);
	}

	return e;
}

static bool bool_to_clause(struct bool_expr *e)
{
	switch (e->op) {
	case CONST:
		return e->nullary;
	case VAR:
		picosat_add(e->var);
		return true;
	case NOT:
		assert(e->unary->op == VAR);
		picosat_add(-e->unary->var);
		return true;
	case OR:
		return bool_to_clause(e->binary.a)
			&& bool_to_clause(e->binary.b);
	default:
		assert(false);
	}
}

static bool bool_to_clauses(struct bool_expr *e)
{
	switch (e->op) {
	case CONST:
		return e->nullary;
	case VAR:
		picosat_add(e->var);
		picosat_add(0);
		return true;
	case NOT:
		assert(e->unary->op == VAR);
		picosat_add(-e->unary->var);
		picosat_add(0);
		return true;
	case AND:
		return bool_to_clauses(e->binary.a)
			&& bool_to_clauses(e->binary.b);
	case OR:
		if (!bool_to_clause(e->binary.a))
			return false;
		if (!bool_to_clause(e->binary.b))
			return false;
		picosat_add(0);
		return true;
	default:
		assert(false);
	}
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
			struct bool_expr *e;

			/* Add the VAR_m -> VAR restriction */
			e = bool_dep(bool_var(sym->sat_variable + 1),
				     bool_var(sym->sat_variable));
			if (!bool_to_clauses(bool_to_cnf(e)))
				return false;

			/* Add the VAR_m -> MODULES restriction */
			e = bool_dep(bool_var(sym->sat_variable + 1),
				     bool_var(modules_sym->sat_variable));
			if (!bool_to_clauses(bool_to_cnf(e)))
				return false;
		}

		/* Add dependencies */
		for_all_prompts(sym, prop) {
			struct bool_expr *e;

			/* XXX: ??? */
			if (!sym->name)
				continue;
			if (!prop->visible.expr)
				continue;

			e = bool_dep(bool_var(sym->sat_variable),
				     expr_to_bool_expr(sym, prop->visible.expr));
			if (!bool_to_clauses(bool_to_cnf(e)))
				return false;
		}

		/* Add "select" dependencies */
		for_all_properties(sym, prop, P_SELECT) {
			struct bool_expr *e;

			/* XXX: ??? */
			if (!sym->name)
				continue;

			e = bool_dep(bool_var(sym->sat_variable),
				     expr_to_bool_expr(sym, prop->expr));
			if (!bool_to_clauses(bool_to_cnf(e)))
				return false;
		}
	}

	return true;
}

/* XXX: For debugging purposes only! */
static void check_conf(void)
{
	unsigned int i;
	struct symbol *sym;
	struct property *prop;

	for_all_symbols(i, sym) {
		if (sym->name)
			continue;

		for_all_prompts(sym, prop) {
			if (!prop->file)
				continue;

			printf("symbol defined at %s:%d has no name\n",
				prop->file->name, prop->file->lineno);
		}

		printf("reverse dependencies: ");
		expr_fprint(sym->rev_dep.expr, stdout);
		printf("\n");
	}
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

	{
		/* We need to do this in order to give strings from the
		 * environment get their values in the proper place. It
		 * is also necessary for INT/HEX values, but doesn't
		 * seem to make any difference for BOOL/TRISTATE
		 * variables (we set them below anyway). */
		unsigned int i;
		struct symbol *sym;
		for_all_symbols(i, sym)
			sym_calc_value(sym);
	}

	if (false)
		check_conf();

	assign_sat_variables();
	picosat_adjust(nr_sat_variables);

	if (!build_clauses()) {
		fprintf(stderr, "error: inconsistent kconfig files while "
			"building clauses\n");
		exit(EXIT_FAILURE);
	}

	{
		int sat = picosat_sat(-1);
		unsigned int i;

		if (sat == PICOSAT_UNKNOWN) {
			fprintf(stderr, "error: inconsistent kconfig files "
				"(unsatisfiable instance?)\n");
			exit(EXIT_FAILURE);
		}

		if (sat == PICOSAT_UNSATISFIABLE) {
			fprintf(stderr, "error: inconsistent kconfig files "
				"(unsatisfiable instance)\n");
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

#if 0
			sym->def[S_DEF_USER] = sym->curr;
#endif
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
