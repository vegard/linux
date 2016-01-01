#define _GNU_SOURCE
#include <assert.h>
#include <locale.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define LKC_DIRECT_LINK
#include "bool.h"
#include "lkc.h"
#include "picosat.h"
#include "satconf.h"

#define CONFIG_DEBUG 0

#if CONFIG_DEBUG
#define DEBUG(fmt, ...) fprintf(stderr, fmt, ## __VA_ARGS__)
#else
#define DEBUG(fmt, ...)
#endif

static struct bool_expr *bool_true;

static unsigned int nr_symbol_variables;
static struct symbol **symbol_variables;

static unsigned int nr_prompt_variables;
static struct property **prompt_variables;

static unsigned int nr_default_variables;
static struct property **default_variables;

/* Number of variables (not including variables introduced by the Tseitin
 * encoding) */
static unsigned int nr_sat_variables;

static unsigned int sym_y(struct symbol *sym)
{
	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);
	assert(sym->sat_variable <= nr_sat_variables);
	return sym->sat_variable + 0;
}

static unsigned int sym_m(struct symbol *sym)
{
	assert(sym->type == S_TRISTATE);
	assert(sym->sat_variable + 1 <= nr_sat_variables);
	return sym->sat_variable + 1;
}

/* Returns the variable indicating whether the symbol was forced to a specific
 * value by the user. */
static unsigned int sym_assumed(struct symbol *sym)
{
	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);
	return sym->sat_variable + (sym->type == S_TRISTATE) + 1;
}

/* Returns the variable indicating whether the symbol was selected */
static unsigned int sym_selected(struct symbol *sym)
{
	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);
	return sym->sat_variable + (sym->type == S_TRISTATE) + 2;
}

static const char **clauses;
static unsigned int max_clauses;

static void assign_sat_variables(void)
{
	unsigned int i;
	struct symbol *sym;
	unsigned int variable = 1;
	unsigned int symbol_variable = 0;
	unsigned int prompt_variable = 0;
	unsigned int default_variable = 0;

	assert(nr_symbol_variables == 0);
	assert(nr_prompt_variables == 0);
	assert(nr_default_variables == 0);

	/* Just count the number of variables we'll need */
	for_all_symbols(i, sym) {
		struct property *prop;

		switch (sym->type) {
		case S_BOOLEAN:
			nr_symbol_variables += 3;
			break;
		case S_TRISTATE:
			nr_symbol_variables += 4;
			break;
		default:
			break;
		}

		for_all_prompts(sym, prop)
			nr_prompt_variables += 1;

		for_all_defaults(sym, prop)
			nr_default_variables += 1;
	}

	nr_sat_variables = nr_symbol_variables + nr_prompt_variables + nr_default_variables;
	symbol_variables = malloc(nr_symbol_variables * sizeof(*symbol_variables));
	prompt_variables = malloc(nr_prompt_variables * sizeof(*prompt_variables));
	default_variables = malloc(nr_default_variables * sizeof(*default_variables));

	/* Assign variables to each symbol */
	for_all_symbols(i, sym) {
		switch (sym->type) {
		case S_BOOLEAN:
			DEBUG("var %d = bool symbol %s\n", variable, sym->name ?: "<unknown>");
			sym->sat_variable = variable;
			variable += 3;
			symbol_variables[symbol_variable++] = sym;
			symbol_variables[symbol_variable++] = sym;
			symbol_variables[symbol_variable++] = sym;
			break;
		case S_TRISTATE:
			DEBUG("var %d = tristate symbol %s\n", variable, sym->name ?: "<unknown>");
			sym->sat_variable = variable;
			variable += 4;
			symbol_variables[symbol_variable++] = sym;
			symbol_variables[symbol_variable++] = sym;
			symbol_variables[symbol_variable++] = sym;
			symbol_variables[symbol_variable++] = sym;
			break;
		default:
			break;
		}
	}

	assert(symbol_variable == nr_symbol_variables);

	/* Assign variables to each prompt */
	for_all_symbols(i, sym) {
		struct property *prop;

		for_all_prompts(sym, prop) {
			DEBUG("var %d = prompt for %s\n", variable, sym->name ?: "<unknown>");
			prop->sat_variable = variable++;
			prompt_variables[prompt_variable++] = prop;
		}
	}

	assert(prompt_variable == nr_prompt_variables);

	/* Assign variables to each default */
	for_all_symbols(i, sym) {
		struct property *prop;

		for_all_defaults(sym, prop) {
			DEBUG("var %d = default for %s\n", variable, sym->name ?: "<unknown>");
			prop->sat_variable = variable++;
			default_variables[default_variable++] = prop;
		}
	}

	assert(default_variable == nr_default_variables);

	assert(symbol_variable + prompt_variable + default_variable == nr_sat_variables);
	assert(variable == nr_sat_variables + 1);

	/* Make sure CONFIG_MODULES got assigned something -- this can happen
	 * if "option modules" was not specified on any symbol. */
	assert(modules_sym);
	assert(modules_sym->sat_variable > 0);
	assert(modules_sym->sat_variable <= nr_sat_variables);

	printf("%u variables (%u symbols, %u prompts, %u defaults)\n",
		nr_sat_variables, nr_symbol_variables, nr_prompt_variables, nr_default_variables);
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
		assert(sym->sat_variable <= nr_sat_variables);
		result[0] = bool_var(sym->sat_variable);
		result[1] = bool_const(false);
		return;
	case S_TRISTATE:
		assert(sym->sat_variable + 1 <= nr_sat_variables);
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
	struct bool_expr *t1, *t2;

	expr_to_bool_expr(lhs, in_a, a);
	expr_to_bool_expr(lhs, in_b, b);

	out[0] = bool_or(a[0], b[0]);

	t1 = bool_dep(a[0], a[1]);
	t2 = bool_dep(b[0], b[1]);
	out[1] = bool_and_put(bool_get(out[0]), bool_and_put(t1, t2));

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

	out[1] = bool_or_put(t1, t2);

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
		ret = bool_and_put(t1, t2);

		bool_put(a[0]);
		bool_put(a[1]);
		bool_put(b[0]);
		bool_put(b[1]);
		return ret;
	}
	case S_INT:
	case S_HEX:
	case S_STRING: {
		const char *a_str;
		const char *b_str;

		a_str = sym_get_string_value(in_a);
		if (!a_str)
			a_str = "";

		if (in_b && in_b->name)
			b_str = in_b->name;
		else
			b_str = "";

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
		result[0] = bool_not_put(t);
		result[1] = bool_const(false);
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
			/* XXX: This will fail:
			 * 
			 * config NF_CONNTRACK_SECMARK
			 * bool "Connection tracking"
			 * default m
			 */
			assert(lhs->type == S_TRISTATE);

			assert(lhs->sat_variable + 1 <= nr_sat_variables);
			result[0] = bool_dep_put(bool_var(lhs->sat_variable), bool_var(lhs->sat_variable + 1));
			result[1] = bool_const(false);
			return;
		}

		/* An undefined symbol typically means that something was
		 * defined only in some architectures' kconfig files, but
		 * was referenced in an arch-independent kconfig files.
		 *
		 * Assume it to be false. */
		if (e->left.sym->type == S_UNKNOWN || e->left.sym->type == S_STRING) {
			result[0] = bool_const(false);
			result[1] = bool_const(false);
			return;
		}

		assert(e->left.sym->type == S_BOOLEAN || e->left.sym->type == S_TRISTATE);

		assert(e->left.sym->sat_variable <= nr_sat_variables);
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

static void add_clause(const char *name, unsigned int nr_literals, ...)
{
	va_list ap;
	va_start(ap, nr_literals);

	DEBUG("%s: ", name);

	unsigned int i;
	for (i = 0; i < nr_literals; ++i) {
		int lit = va_arg(ap, int);
		assert(lit != 0);
		picosat_add(lit);

		DEBUG("%d ", lit);
	}

	int clause_index = picosat_add(0);

	DEBUG("\n");

	va_end(ap);

	if (clause_index >= max_clauses) {
		unsigned int new_max_clauses;
		const char **new_clauses;

		new_max_clauses = (max_clauses + 7) * 2;
		/* XXX: make sure it's bigger than clause_index */
		new_clauses = realloc(clauses, new_max_clauses * sizeof(*clauses));
		if (!new_clauses) {
			fprintf(stderr, "error: out of memory\n");
			exit(EXIT_FAILURE);
		}

		max_clauses = new_max_clauses;
		clauses  = new_clauses;
	}

	clauses[clause_index] = name;
}

/* Use the Tseitin encoding to convert the boolean expression to CNF. The
 * encoding involves introducing extra variables for every internal node of
 * the boolean expression. 
 *
 * This function returns the literal associated with the expression. The
 * boolean expression is left intact and must be freed by the called (no
 * references are taken). */
static int _add_clauses(struct bool_expr *e, const char *name)
{
	switch (e->op) {
	case CONST:
		/* XXX: Do this properly. */
		return e->nullary ? bool_true->literal : -bool_true->literal;

	case LITERAL:
		return e->literal;

	case NOT: {
		int x = _add_clauses(e->unary, name);
		bool_put(e->unary);
		e->op = LITERAL;
		return (e->literal = -x);
	}

	case AND: {
		int a = _add_clauses(e->binary.a, name);
		bool_put(e->binary.a);
		int b = _add_clauses(e->binary.b, name);
		bool_put(e->binary.b);
		int c = picosat_inc_max_var();
		e->op = LITERAL;
		e->literal = c;

		add_clause(name, 3, c, -a, -b);
		add_clause(name, 2, -c, a);
		add_clause(name, 2, -c, b);
		return c;
	}

	case OR: {
		int a = _add_clauses(e->binary.a, name);
		bool_put(e->binary.a);
		int b = _add_clauses(e->binary.b, name);
		bool_put(e->binary.b);
		int c = picosat_inc_max_var();
		e->op = LITERAL;
		e->literal = c;

		add_clause(name, 3, -c, a, b);
		add_clause(name, 2, c, -a);
		add_clause(name, 2, c, -b);
		return c;
	}

	case EQ: {
		int a = _add_clauses(e->binary.a, name);
		bool_put(e->binary.a);
		int b = _add_clauses(e->binary.b, name);
		bool_put(e->binary.b);
		int c = picosat_inc_max_var();
		e->op = LITERAL;
		e->literal = c;

		add_clause(name, 3, c, a, b);
		add_clause(name, 3, c, -a, -b);
		add_clause(name, 3, -c, a, -b);
		add_clause(name, 3, -c, -a, b);
		return c;
	}

	default:
		fprintf(stderr, "unknown expression!? ");
		bool_fprint(stderr, e);
		fprintf(stderr, "\n");
		assert(false);
	}
}

static void add_clauses(struct bool_expr *e, const char *fmt, ...)
{
	if (e->op == CONST) {
		assert(e->unary);
		return;
	}

	va_list ap;
	char *name;
	int ret;

	va_start(ap, fmt);
	ret = vasprintf(&name, fmt, ap);
	va_end(ap);

	if (ret == -1) {
		fprintf(stderr, "error: out of memory\n");
		exit(1);
	}

#if CONFIG_DEBUG
	fprintf(stderr, "%s: ", name);
	bool_fprint(stderr, e);
	fprintf(stderr, "\n");
#endif

	/* XXX: Should REALLY fix this. It introduces way too many unit
	 * clauses. We can and should simplify before passing the clauses
	 * to the SAT solver. */
	int x = _add_clauses(e, name);
	add_clause(name, 1, x);
}

static bool build_choice_clauses(struct symbol *sym)
{
	struct property *prop;
	struct property *prompt;
	struct bool_expr *visible;

	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);

	prompt = sym_get_prompt(sym);
	assert(prompt);

	assert(prompt->sat_variable <= nr_sat_variables);
	visible = bool_var(prompt->sat_variable);

	/* If the symbol is not optional, then it must be enabled */
	if (!sym_is_optional(sym)) {
		struct bool_expr *t1, *t2;

		assert(sym->sat_variable <= nr_sat_variables);
		t1 = bool_var(sym->sat_variable);
		t2 = bool_dep(visible, t1);
		bool_put(t1);

		add_clauses(t2, "<choice block> is mandatory");
		bool_put(t2);
	}

	/* If the choice block is not optional, then one of
	 * options must be set. */
	if (!sym_is_optional(sym)) {
		struct bool_expr *block;
		struct bool_expr *any_visible;
		struct bool_expr *dep;

		/* This is a conjunction of all the choice values */
		block = bool_const(false);

		for_all_choices(sym, prop) {
			struct expr *expr;
			struct symbol *choice;

			assert(prop->expr->type == E_LIST);
			expr_list_for_each_sym(prop->expr, expr, choice) {
				struct bool_expr *t1, *t2;

				assert(choice->sat_variable <= nr_sat_variables);
				t1 = bool_var(choice->sat_variable);
				t2 = bool_or_put(block, t1);
				block = t2;
			}
		}

		/* This is a disjunction of the visibility of all the choice prompts */
		any_visible = bool_const(false);

		for_all_choices(sym, prop) {
			struct expr *expr;
			struct symbol *choice;

			assert(prop->expr->type == E_LIST);
			expr_list_for_each_sym(prop->expr, expr, choice) {
				struct property *prompt;

				for_all_prompts(choice, prompt) {
					assert(prompt->sat_variable <= nr_sat_variables);
					any_visible = bool_or_put(any_visible, bool_var(prompt->sat_variable));
				}
			}
		}

		dep = bool_dep_put(bool_and(visible, any_visible), block);
		bool_put(any_visible);

		add_clauses(dep, "<choice block> depends on <one of the choices>");
		bool_put(dep);
	}

	/* The choices are mutually exclusive */
	for_all_choices(sym, prop) {
		struct expr *expr;
		struct symbol *choice;

		expr_list_for_each_sym(prop->expr, expr, choice) {
			struct bool_expr *t1, *t2;
			struct expr *expr2;
			struct symbol *choice2;

			assert(choice->sat_variable <= nr_sat_variables);
			t1 = bool_var(choice->sat_variable);
			t2 = bool_not_put(t1);

			expr_list_for_each_sym(prop->expr, expr2, choice2) {
				struct bool_expr *t3, *t4, *t5;

				/* Don't add the same clause twice */
				if (expr <= expr2)
					continue;

				assert(choice2->sat_variable <= nr_sat_variables);
				t3 = bool_var(choice2->sat_variable);
				t4 = bool_not_put(t3);

				t5 = bool_or(t2, t4);
				bool_put(t4);

				add_clauses(t5, "%s and %s are mutual exclusive",
					choice->name ?: "<choice>",
					choice2->name ?: "<choice>");
				bool_put(t5);
			}

			bool_put(t2);
		}
	}

	/* Build the default clauses. This is similar to how we build default
	 * clauses for regular symbols, but still different. For one, the
	 * default directive doesn't specify the default value of the current
	 * symbol, but of the choice symbol. For another, choice symbols have
	 * only one menu. */
	struct bool_expr *cond = bool_const(false);

	/* Choice block defaults only apply if none of the choices were
	 * visible or selected. */
	for_all_choices(sym, prop) {
		struct expr *expr;
		struct symbol *choice;

		expr_list_for_each_sym(prop->expr, expr, choice) {
			struct property *prompt;

			cond = bool_or_put(cond, bool_var(sym_selected(choice)));
			for_all_prompts(choice, prompt) {
				assert(prompt->sat_variable <= nr_sat_variables);
				cond = bool_or_put(cond, bool_var(prompt->sat_variable));
			}
		}
	}

	cond = bool_not_put(cond);

	for_all_defaults(sym, prop) {
		struct bool_expr *e[2];
		struct bool_expr *t1, *t2, *t3, *t4, *t5, *t6, *t7;
		struct gstr str1, str2;

		if (prop->visible.expr) {
			expr_to_bool_expr(NULL, prop->visible.expr, e);
		} else {
			e[0] = bool_const(true);
			e[1] = bool_const(false);
		}

		t1 = bool_and(cond, e[0]);
		bool_put(e[0]);
		bool_put(e[1]);

		assert(prop->sat_variable <= nr_sat_variables);
		t2 = bool_var(prop->sat_variable);
		t3 = bool_dep(t1, t2);
		bool_put(t1);

		t4 = bool_not(t2);
		cond = bool_and_put(cond, t4);

		/* XXX: We want e[1] to be true if prop->expr a bool-type symbol */
		expr_to_bool_expr(sym, prop->expr, e);

		t5 = bool_and_put(e[0], e[1]);
		t6 = bool_dep_put(t2, t5);
		t7 = bool_and_put(t3, t6);

		str1 = str_new();
		expr_gstr_print(prop->expr, &str1);
		str2 = str_new();
		expr_gstr_print(prop->visible.expr, &str2);
		add_clauses(t7, "<choice> default %s if %s", str_get(&str1), str_get(&str2));
		bool_put(t7);
		str_free(&str1);
		str_free(&str2);
	}

	bool_put(cond);
	bool_put(visible);
	return true;
}

static bool build_tristate_clauses(struct symbol *sym)
{
	struct bool_expr *t1, *t2, *t3, *t4;

	assert(sym->sat_variable + 1 <= nr_sat_variables);
	assert(modules_sym->sat_variable <= nr_sat_variables);
	t1 = bool_var(sym->sat_variable);
	t2 = bool_var(sym->sat_variable + 1);
	t3 = bool_var(modules_sym->sat_variable);

	/* Add the VAR_m -> VAR_y restriction */
	t4 = bool_dep(t2, t1);
	add_clauses(t4, "%s_m -> %s_y", sym->name ?: "<choice>", sym->name ?: "<choice>");
	bool_put(t4);

	/* Add the VAR_m -> MODULES restriction */
	t4 = bool_dep(t2, t3);
	add_clauses(t4, "%s_m -> MODULES", sym->name ?: "<choice>");
	bool_put(t4);

	bool_put(t1);
	bool_put(t2);
	bool_put(t3);

	return true;
}

static bool build_prompt_visibility_clauses(struct property *prop)
{
	struct bool_expr *e[2];
	struct bool_expr *t1;
	struct gstr str;

	/* visible.expr is a conjunction of the menu's dependencies
	 * (parent menus' "depends on", this menu' "depends on", and the
	 * "if" part of the prompt). Which is exactly what we need.
	 *
	 * For choices, it is a conjunction of the choice block symbol
	 * and the choice's "depends on". */
	if (prop->visible.expr) {
		expr_to_bool_expr(prop->sym, prop->visible.expr, e);
	} else {
		e[0] = bool_const(true);
		e[1] = bool_const(false);
	}

	/* Prompts are visible if and only if
	 *  - the menu is visible ("depends on", etc.)
	 *  - the prompt's dependencies are satisfied (the "if" part) */
	assert(prop->sat_variable <= nr_sat_variables);
	t1 = bool_eq_put(bool_var(prop->sat_variable), e[0]);
	bool_put(e[1]);

	str = str_new();
	expr_gstr_print(prop->visible.expr, &str);
	add_clauses(t1, "\"%s\" prompt depends on %s", prop->text, str_get(&str));
	bool_put(t1);
	str_free(&str);

	return true;
}

static bool build_select_clauses(struct symbol *sym, struct property *prop)
{
	struct bool_expr *condition[2];
	struct bool_expr *e[2];
	struct bool_expr *t2, *t3;
	struct gstr str1, str2;

	if (prop->visible.expr) {
		expr_to_bool_expr(sym, prop->visible.expr, condition);
	} else {
		condition[0] = bool_const(true);
		condition[1] = bool_const(false);
	}

	assert(sym->sat_variable <= nr_sat_variables);
	t2 = bool_and_put(bool_var(sym->sat_variable), condition[0]);
	bool_put(condition[1]);

	/* Update the selected symbol's 'selected_expr' to reflect that this
	 * symbol may have selected it. */
	{
		/* The symbol being selected */
		assert(prop->expr->type == E_SYMBOL);
		struct symbol *selected_sym = prop->expr->left.sym;
		/* XXX: And for other symbols? */
		if (selected_sym->type == S_BOOLEAN || selected_sym->type == S_TRISTATE) {
			assert(sym->sat_variable <= nr_sat_variables);
			selected_sym->selected_expr = bool_or_put(selected_sym->selected_expr, bool_get(t2));
		}
	}

	expr_to_bool_expr(sym, prop->expr, e);
	t3 = bool_dep_put(t2, e[0]);
	bool_put(e[1]);

	str1 = str_new();
	expr_gstr_print(prop->expr, &str1);
	str2 = str_new();
	if (prop->visible.expr) {
		str_append(&str2, " if ");
		expr_gstr_print(prop->visible.expr, &str2);
	}
	add_clauses(t3, "%s select %s%s", sym->name ?: "<choice>",
		str_get(&str1), str_get(&str2));
	bool_put(t3);
	str_free(&str1);
	str_free(&str2);
	return true;
}

static bool build_sym_select_clauses(struct symbol *sym)
{
	struct property *prop;

	for_all_properties(sym, prop, P_SELECT) {
		if (!build_select_clauses(sym, prop))
			return false;
	}

	return true;
}

static bool build_default_clauses(struct symbol *sym)
{
	struct bool_expr *sym_expr[2];
	struct bool_expr *cond;
	struct property *prop;

	symbol_to_bool_expr(sym, sym_expr);

	cond = bool_var(sym_selected(sym));
	for_all_prompts(sym, prop) {
		assert(prop->sat_variable <= nr_sat_variables);
		cond = bool_or_put(cond, bool_var(prop->sat_variable));
	}

	cond = bool_not_put(cond);

	/* 'cond' now encodes "symbol was not selected and no prompt is visible" */

	for_all_defaults(sym, prop) {
		struct bool_expr *e[2];
		struct bool_expr *t1, *t2, *t3, *t4, *t5, *t6;
		struct gstr str1, str2;

		/* XXX: This should be the "if" part of the expression. However,
		 * as it turns out, it is actually a conjunction of the menu's
		 * dependencies AND the "if" part. (Note, however, the prompt's
		 * dependencies are not included.) */
		/* XXX: Maybe we should pass NULL for sym here? The idea being
		 * that if the Kconfig has "default n if y" (which happens),
		 * then this means "default n", noth "default n if <SYM>=y". */
		if (prop->visible.expr) {
			expr_to_bool_expr(NULL, prop->visible.expr, e);
		} else {
			/* Defaults without a visibility condition
			 * ("default ... if ...") default to visible. */
			e[0] = bool_const(true);
			e[1] = bool_const(false);
		}

		t1 = bool_and(cond, e[0]);
		t2 = bool_not(e[0]);
		bool_put(e[0]);
		bool_put(e[1]);

		cond = bool_and_put(cond, t2);

		/* We pass NULL here, because we don't want "default m" to be
		 * interpreted as FOO = (FOO = m) when we have config FOO
		 * default m. */
		expr_to_bool_expr(NULL, prop->expr, e);

		/* XXX: We may get trouble with MODULES=n and "default m" */
		t3 = bool_eq(sym_expr[0], e[0]);
		t4 = bool_eq(sym_expr[1], e[1]);
		bool_put(e[0]);
		bool_put(e[1]);
		t5 = bool_and_put(t3, t4);
		t6 = bool_dep_put(t1, t5);

		str1 = str_new();
		expr_gstr_print(prop->expr, &str1);
		str2 = str_new();
		expr_gstr_print(prop->visible.expr, &str2);
		add_clauses(t6, "%s default %s if %s", sym->name, str_get(&str1), str_get(&str2));
		bool_put(t6);
		str_free(&str1);
		str_free(&str2);
	}

	/* If no default matched, force the symbol value to 'n'. */
	{
		struct bool_expr *t1, *t2;

		t1 = bool_not(sym_expr[0]);
		t2 = bool_dep(cond, t1);
		bool_put(t1);

		add_clauses(t2, "%s (implicit) default n", sym->name);
		bool_put(t2);
	}

	bool_put(sym_expr[0]);
	bool_put(sym_expr[1]);
	bool_put(cond);

	return true;
}

static void build_symbol_clauses(struct symbol *sym)
{
	/* A symbol can only be enabled (true) if:
	 *  - a prompt was visible (and this prompt was selected),
	 *  - a default value was used
	 *  - it was selected
	 */

	struct bool_expr *cond = bool_const(false);

	struct property *prompt;
	for_all_prompts(sym, prompt)
		cond = bool_or_put(cond, bool_var(prompt->sat_variable));

	struct property *prop;
	for_all_defaults(sym, prop)
		cond = bool_or_put(cond, bool_var(prop->sat_variable));

	cond = bool_or_put(cond, bool_var(sym_selected(sym)));

	struct bool_expr *t1 = bool_dep_put(bool_var(sym_y(sym)), cond);
	add_clauses(t1, "%s must have a prompt, a default, or be selected",
		sym->name ?: "<choice>");
	bool_put(t1);
}

static bool build_clauses(void)
{
	unsigned int i;
	struct symbol *sym;

	for_all_symbols(i, sym) {
		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		sym->selected_expr = bool_const(false);
	}

	for_all_symbols(i, sym) {
		if (sym_is_choice(sym)) {
			if (!build_choice_clauses(sym))
				return false;
		}

		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		if (sym->type == S_TRISTATE) {
			if (!build_tristate_clauses(sym))
				return false;
		}

		struct property *prop;

		/* Prompt visibility dependencies */
		for_all_prompts(sym, prop) {
			if (!build_prompt_visibility_clauses(prop))
				return false;
		}

		if (!sym_is_choice(sym)) {
			if (!build_default_clauses(sym))
				return false;
		}

		if (!build_sym_select_clauses(sym))
			return false;

		build_symbol_clauses(sym);
	}

	for_all_symbols(i, sym) {
		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		struct bool_expr *e = bool_eq_put(bool_var(sym_selected(sym)), sym->selected_expr);
		add_clauses(e, "%s selected", sym->name);
		bool_put(e);
	}

	return true;
}

static unsigned int nr_changed = 0;

static void check_sym_value(struct symbol *sym, tristate value)
{
	static const char *tristate_names[] = {
		[no] = "no",
		[mod] = "mod",
		[yes] = "yes",
	};

	if (sym->flags & (SYMBOL_DEF << S_DEF_SAT)) {
		if (sym->curr.tri != value) {
			fprintf(stderr, "warning: symbol %s changed from %s to %s\n",
				sym->name ?: "<choice>",
				tristate_names[value],
				tristate_names[sym->curr.tri]);

			++nr_changed;
		}
	}
}

void satconfig_init(const char *Kconfig_file, bool randomize)
{
	picosat_init();
	picosat_enable_trace_generation();

	conf_parse(Kconfig_file);

	/* XXX: We need this to initialise values for non-boolean (and non-
	 * tristate) variables. This should go away when we read .satconfig
	 * instead for these kinds of variables. */
	conf_read_simple(NULL, S_DEF_USER);

	assign_sat_variables();

	/* We _will_ need more variables as we build the clauses, but
	 * picosat_inc_max_var() takes care of it. */
	picosat_adjust(1 + nr_sat_variables);

	/* Create a boolean variable that we force to be true */
	bool_true = bool_var(picosat_inc_max_var());
	add_clause("true", 1, bool_true->literal);

	if (!build_clauses()) {
		fprintf(stderr, "error: inconsistent kconfig files while "
			"building clauses\n");
		exit(EXIT_FAILURE);
	}

	bool_put(bool_true);
	assert(nr_bool_created == nr_bool_destroyed);

	/* Annoyingly, we have to set phases before doing the first solve. */
	if (randomize) {
		picosat_set_seed(time(NULL));
		picosat_set_global_default_phase(3);
	} else {
		picosat_set_global_default_phase(0);
	}

	picosat_set_default_phase_lit(modules_sym->sat_variable, 1);

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


	printf("%u clauses\n", picosat_added_original_clauses());

	{
		/* First do a check to see if the instance is solvable
		 * without any assumptions. If this is not the case, then
		 * something is weird with the kconfig files. */
		int sat = picosat_sat(-1);

		if (sat != PICOSAT_SATISFIABLE) {
			unsigned int i;

			fprintf(stderr, "error: inconsistent kconfig files "
				"(no valid configurations possible)\n");

			for (i = 0; i < picosat_added_original_clauses(); ++i) {
				if (picosat_coreclause(i))
					fprintf(stderr, "clause: %d: %s\n", i, clauses[i]);
			}

			exit(EXIT_FAILURE);
		}
	}
}

void satconfig_update_symbol(struct symbol *sym)
{
	if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
		return;

	bool assume = true;

	if (!(sym->flags & SYMBOL_SAT)) {
		assume = false;
	} else if (sym->flags & SYMBOL_CHOICE) {
		assume = false;
	} else {
		switch (sym->def[S_DEF_SAT].tri) {
		case no:
			picosat_assume(-sym_y(sym));
			break;
		case yes:
			picosat_assume(sym_y(sym));
			if (sym->type == S_TRISTATE)
				picosat_assume(-sym_m(sym));
			break;
		case mod:
			assert(sym->type == S_TRISTATE);
			picosat_assume(sym_y(sym));
			picosat_assume(sym_m(sym));
			break;
		}
	}

	if (assume)
		picosat_assume(sym_assumed(sym));
	else
		picosat_assume(-sym_assumed(sym));
}

void satconfig_update_all_symbols(void)
{
	unsigned int i;
	struct symbol *sym;
	struct expr *e;

	/* We need to do this in order to give strings from the
	 * environment get their values in the proper place. It
	 * is also necessary for INT/HEX values, but doesn't
	 * seem to make any difference for BOOL/TRISTATE
	 * variables (we set them below anyway). */
	for_all_symbols(i, sym) {
		if (sym->flags & SYMBOL_SAT)
			sym->curr = sym->def[S_DEF_SAT];
		else if (sym->flags & SYMBOL_DEF_USER)
			sym->curr = sym->def[S_DEF_USER];
	}

	expr_list_for_each_sym(sym_env_list, e, sym) {
		struct property *prop;
		struct symbol *env_sym;

		prop = sym_get_env_prop(sym);
		env_sym = prop_get_symbol(prop);
		if (!env_sym)
			continue;

		sym->curr.val = getenv(env_sym->name);
	}

	/* Use assumptions */
	for_all_symbols(i, sym)
		satconfig_update_symbol(sym);
}

void satconfig_solve(void)
{
	int sat = picosat_sat(-1);
	unsigned int i;

	if (sat != PICOSAT_SATISFIABLE) {
		fprintf(stderr, "error: unsatisfiable constraints\n");

		for (i = 0; i < picosat_added_original_clauses(); ++i) {
			if (picosat_coreclause(i))
				fprintf(stderr, "clause: %s\n", clauses[i]);
		}

		exit(EXIT_FAILURE);
	}

	struct symbol *sym;
	for_all_symbols(i, sym) {
		if (!sym->name)
			continue;
		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		{
			int y = picosat_deref(sym_y(sym));
			assert(y != 0);

			if (y == 1) {
				if (sym->type == S_TRISTATE) {
					int m = picosat_deref(sym_m(sym));
					assert(m != 0);

					if (m == 1)
						sym->curr.tri = mod;
					else if (m == -1)
						sym->curr.tri = yes;
				} else {
					sym->curr.tri = yes;
				}
			} else if (y == -1) {
				if (sym->type == S_TRISTATE) {
					int m = picosat_deref(sym_m(sym));
					assert(m == -1);
				}

				sym->curr.tri = no;
			}
		}

		sym->flags |= SYMBOL_VALID;
		sym->flags |= SYMBOL_WRITE;
	}
}
