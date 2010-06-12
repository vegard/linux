#include <assert.h>
#include <locale.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define LKC_DIRECT_LINK
#include "lkc.h"

static unsigned int nr_sat_variables;
static struct symbol **sat_variables;

static void assign_sat_variables(void)
{
	unsigned int i;
	struct symbol *sym;
	unsigned int variable = 0;

	assert(nr_sat_variables == 0);

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
			return bool_or(bool_var(lhs->sat_variable),
				       bool_not(bool_var(lhs->sat_variable + 1)));
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

	printf("%d\n", e->type);
	assert(false);
}

static void build_clauses(void)
{
	unsigned int i;
	struct symbol *sym;

	for_all_symbols(i, sym) {
		struct property *prop;

		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		if (sym->type == S_TRISTATE) {
			/* Add the VAR_m -> VAR restriction */

			/* XXX: Actually do it. */
			bool_or(bool_var(sym->sat_variable + 1),
				bool_not(bool_var(sym->sat_variable)));
		}

#if 0
		/* XXX: For debugging purposes */
		for_all_prompts(sym, prop) {
			if (!sym->name)
				continue;

			printf("%s:\n", sym->name);

			expr_fprint(prop->visible.expr, stdout);
			printf("\n");

			if (prop->visible.expr) {
				bool_printf(expr_to_bool_expr(sym, prop->visible.expr));
				printf("\n");
			}

			printf("\n");
		}
#endif

		/* Add dependencies */
		for_all_prompts(sym, prop) {
			if (!sym->name)
				continue;

			if (prop->visible.expr) {
				/* XXX: Actually do it. */
				expr_to_bool_expr(sym, prop->visible.expr);
			}
		}

		/* XXX: Add "select"ed dependencies */
	}
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

	conf_parse(argv[1]);

	/* XXX: We need this to initialise values for non-boolean (and non-
	 * tristate) variables. This should go away when we read .satconfig
	 * instead for these kinds of variables. */
	conf_read(NULL);

	if (false)
		check_conf();

	assign_sat_variables();
	build_clauses();

	printf("ok\n");
	return EXIT_SUCCESS;
}
