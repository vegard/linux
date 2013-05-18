#define _GNU_SOURCE
#include <assert.h>
#include <locale.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define LKC_DIRECT_LINK
#include "bool.h"
#include "lkc.h"
#include "picosat.h"

#if 0
#define DEBUG(fmt, ...) printf(fmt, ## __VA_ARGS__)
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

static bool is_symbol_variable(unsigned int var)
{
	unsigned int x = var - 1;
	return x < nr_symbol_variables;
}

static bool is_prompt_variable(unsigned int var)
{
	unsigned int x = var - 1 - nr_symbol_variables;
	return x < nr_prompt_variables;
}

static struct symbol *get_symbol_variable(unsigned int var)
{
	assert(is_symbol_variable(var));
	return symbol_variables[var - 1];
}

static struct property *get_prompt_variable(unsigned int var)
{
	assert(is_prompt_variable(var));
	return prompt_variables[var - 1 - nr_symbol_variables];
}

static unsigned int sym_y(struct symbol *sym)
{
	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);
	return sym->sat_variable + 0;
}

static unsigned int sym_m(struct symbol *sym)
{
	assert(sym->type == S_TRISTATE);
	return sym->sat_variable + 1;
}

/* Returns the variable indicating whether the symbol was forced to a specific
 * value by the user. */
static unsigned int sym_assumed(struct symbol *sym)
{
	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);
	return sym->sat_variable + (sym->type == S_TRISTATE) + 1;
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
			nr_symbol_variables += 2;
			break;
		case S_TRISTATE:
			nr_symbol_variables += 3;
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
			variable += 2;
			symbol_variables[symbol_variable++] = sym;
			symbol_variables[symbol_variable++] = sym;
			break;
		case S_TRISTATE:
			DEBUG("var %d = tristate symbol %s\n", variable, sym->name ?: "<unknown>");
			sym->sat_variable = variable;
			variable += 3;
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

	assert(default_variable = nr_default_variables);

	assert(symbol_variable + prompt_variable + default_variable == nr_sat_variables);
	assert(variable == nr_sat_variables + 1);

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

	t1 = bool_and(a[1], b[1]);
	t2 = bool_dep(b[0], b[1]);
	t3 = bool_dep(a[0], b[1]);
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
			/* XXX: This will fail:
			 * 
			 * config NF_CONNTRACK_SECMARK
			 * bool "Connection tracking"
			 * default m
			 */
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
		if (e->left.sym->type == S_UNKNOWN) {
			result[0] = bool_const(false);
			result[1] = bool_const(false);
			return;
		}

		result[0] = bool_var(e->left.sym->sat_variable);
		/* XXX: hould this be true or false? It used to be false, but
		 * in the case of "select <symbol>" we want these result[]
		 * variables to be the consequences of selecting the symbol. */
		result[1] = bool_const(true);
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

	va_start(ap, fmt);
	vasprintf(&name, fmt, ap);
	va_end(ap);

	/* XXX: Should REALLY fix this. It introduces way too many unit
	 * clauses. We can and should simplify before passing the clauses
	 * to the SAT solver. */
	int x = _add_clauses(e, name);
	add_clause(name, 1, x);
}

static const char *get_variable_name(unsigned int var)
{
	if (is_symbol_variable(var))
		return get_symbol_variable(var)->name;
	if (is_prompt_variable(var))
		return get_prompt_variable(var)->sym->name;

	/* Is Tseitin-encoding variable */
	assert(false);
}

static bool build_choice_clauses(struct symbol *sym)
{
	struct property *prop;
	struct property *prompt;
	struct bool_expr *visible;

	assert(sym->type == S_BOOLEAN || sym->type == S_TRISTATE);

	prompt = sym_get_prompt(sym);
	assert(prompt);

	visible = bool_var(prompt->sat_variable);

	/* If the symbol is not optional, then it must be enabled */
	if (!sym_is_optional(sym)) {
		struct bool_expr *t1, *t2;

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
		struct bool_expr *t1;
		struct bool_expr *dep;

		/* This is a conjunction of all the choice values */
		block = bool_const(false);

		for_all_choices(sym, prop) {
			struct expr *expr;
			struct symbol *choice;

			assert(prop->expr->type == E_LIST);
			expr_list_for_each_sym(prop->expr, expr, choice) {
				struct bool_expr *t1, *t2;

				t1 = bool_var(choice->sat_variable);
				t2 = bool_or(block, t1);
				bool_put(block);
				bool_put(t1);
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
					struct bool_expr *t;
					struct bool_expr *old_any_visible;

					t = bool_var(prompt->sat_variable);
					any_visible = bool_or(old_any_visible = any_visible, t);
					bool_put(old_any_visible);
					bool_put(t);
				}
			}
		}

		t1 = bool_and(visible, any_visible);
		bool_put(any_visible);

		dep = bool_dep(t1, block);
		bool_put(t1);
		bool_put(block);

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

			t1 = bool_var(choice->sat_variable);
			t2 = bool_not(t1);
			bool_put(t1);

			expr_list_for_each_sym(prop->expr, expr2, choice2) {
				struct bool_expr *t3, *t4, *t5;

				/* Don't add the same clause twice */
				if (expr <= expr2)
					continue;

				t3 = bool_var(choice2->sat_variable);
				t4 = bool_not(t3);
				bool_put(t3);

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
	struct bool_expr *cond;

	{
		struct bool_expr *t1;

		/* XXX: Choice block variables can _never_ be assumed since
		 * they are anonymous... Yikes, I think we need to do something
		 * like (any of the choices were forced). */
		t1 = bool_var(sym_assumed(sym));
		cond = bool_not(t1);
		bool_put(t1);
	}

	for_all_defaults(sym, prop) {
		struct bool_expr *e[2];
		struct bool_expr *t1, *t2, *t3, *t4, *t5, *t6, *t7;
		struct bool_expr *old_cond;
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

		t2 = bool_var(prop->sat_variable);
		t3 = bool_dep(t1, t2);
		bool_put(t1);

		t4 = bool_not(t2);
		cond = bool_and(old_cond = cond, t4);
		bool_put(old_cond);
		bool_put(t4);

		/* XXX: We want e[1] to be true if prop->expr a bool-type symbol */
		expr_to_bool_expr(sym, prop->expr, e);

		t5 = bool_and(e[0], e[1]);
		bool_put(e[0]);
		bool_put(e[1]);

		t6 = bool_dep(t2, t5);
		bool_put(t2);
		bool_put(t5);

		t7 = bool_and(t3, t6);
		bool_put(t3);
		bool_put(t6);

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
	struct bool_expr *t1, *t2;
	struct gstr str;

	/* visible.expr is a conjunction of the menu's dependencies
	 * (parent menus' "depends on", this menu' "depends on", and the
	 * "if" part of the prompt). Which is exactly what we need. */
	if (prop->visible.expr) {
		expr_to_bool_expr(prop->sym, prop->visible.expr, e);
	} else {
		e[0] = bool_const(true);
		e[1] = bool_const(false);
	}

	/* Prompts are visible if and only if
	 *  - the menu is visible ("depends on", etc.)
	 *  - the prompt's dependencies are satisfied (the "if" part) */
	t1 = bool_var(prop->sat_variable);
	t2 = bool_eq(t1, e[0]);
	bool_put(t1);
	bool_put(e[0]);
	bool_put(e[1]);

	str = str_new();
	expr_gstr_print(prop->visible.expr, &str);
	add_clauses(t2, "\"%s\" prompt depends on %s", prop->text, str_get(&str));
	bool_put(t2);
	str_free(&str);

	return true;
}

static bool build_select_clauses(struct symbol *sym, struct property *prop)
{
	struct bool_expr *condition[2];
	struct bool_expr *e[2];
	struct bool_expr *t1, *t2, *t3, *t4;
	struct gstr str1, str2;

	if (prop->visible.expr) {
		expr_to_bool_expr(sym, prop->visible.expr, condition);
	} else {
		condition[0] = bool_const(true);
		condition[1] = bool_const(false);
	}

	expr_to_bool_expr(sym, prop->expr, e);

	t1 = bool_var(sym->sat_variable);
	t2 = bool_and(t1, condition[0]);
	bool_put(t1);
	bool_put(condition[0]);
	bool_put(condition[1]);

	t3 = bool_and(e[0], e[1]);
	bool_put(e[0]);
	bool_put(e[1]);

	t4 = bool_dep(t2, t3);
	bool_put(t2);
	bool_put(t3);

	str1 = str_new();
	expr_gstr_print(prop->expr, &str1);
	str2 = str_new();
	if (prop->visible.expr) {
		str_append(&str2, " if ");
		expr_gstr_print(prop->visible.expr, &str2);
	}
	add_clauses(t4, "%s select %s%s", sym->name ?: "<choice>",
		str_get(&str1), str_get(&str2));
	bool_put(t4);
	str_free(&str1);
	str_free(&str2);
	return true;
}

static bool build_sym_select_clauses(struct symbol *sym)
{
	struct property *prop;

	for_all_properties(sym, prop, P_SELECT)
		build_select_clauses(sym, prop);

	return true;
}

static bool build_default_clauses(struct symbol *sym)
{
	struct bool_expr *sym_expr[2];
	struct bool_expr *cond;
	struct property *prop;

	symbol_to_bool_expr(sym, sym_expr);

	cond = bool_const(false);
	for_all_prompts(sym, prop) {
		struct bool_expr *t;
		struct bool_expr *old_cond;

		t = bool_var(prop->sat_variable);
		cond = bool_or(old_cond = cond, t);
		bool_put(old_cond);
		bool_put(t);
	}

	{
		struct bool_expr *old_cond;

		cond = bool_not(old_cond = cond);
		bool_put(old_cond);
	}

	for_all_defaults(sym, prop) {
		struct bool_expr *e[2];
		struct bool_expr *t1, *t2, *t3, *t4, *t5, *t6, *t7, *t8, *t9;
		struct bool_expr *old_cond;
		struct gstr str1, str2;

		/* XXX: This should be the "if" part of the expression. However,
		 * as it turns out, it is actually a conjunction of the menu's
		 * dependencies AND the "if" part. (Note, however, the prompt's
		 * dependencies are not included.) */
		if (prop->visible.expr) {
			expr_to_bool_expr(sym, prop->visible.expr, e);
		} else {
			e[0] = bool_const(true);
			e[1] = bool_const(false);
		}

		t1 = bool_and(cond, e[0]);
		bool_put(e[0]);
		bool_put(e[1]);

		t2 = bool_var(prop->sat_variable);
		t3 = bool_dep(t1, t2);
		bool_put(t1);

		t4 = bool_not(t2);

		cond = bool_and(old_cond = cond, t4);
		bool_put(old_cond);
		bool_put(t4);

		/* We pass NULL here, because we don't want "default m" to be
		 * interpreted as FOO = (FOO = m) when we have config FOO
		 * default m. */
		expr_to_bool_expr(NULL, prop->expr, e);

		/* XXX: We may get trouble with MODULES=n and "default m" */
		t5 = bool_eq(sym_expr[0], e[0]);
		t6 = bool_eq(sym_expr[1], e[1]);
		bool_put(e[0]);
		bool_put(e[1]);
		t7 = bool_and(t5, t6);
		bool_put(t5);
		bool_put(t6);

		t8 = bool_dep(t2, t7);
		bool_put(t2);
		bool_put(t7);

		t9 = bool_and(t3, t8);
		bool_put(t3);
		bool_put(t8);

		str1 = str_new();
		expr_gstr_print(prop->expr, &str1);
		str2 = str_new();
		expr_gstr_print(prop->visible.expr, &str2);
		add_clauses(t9, "%s default %s if %s", sym->name, str_get(&str1), str_get(&str2));
		bool_put(t9);
		str_free(&str1);
		str_free(&str2);
	}

#if 0 /* XXX: We can't do it, because we need to allow for selects... */
	/* If no default matched, force the symbol value to 'n'. */
	{
		struct bool_expr *t1, *t2;

		t1 = bool_not(sym_expr[0]);
		t2 = bool_dep(cond, t1);
		bool_put(t1);

		add_clauses(t2, "%s (implicit) default n", sym->name);
		bool_put(t2);
	}
#endif

	bool_put(sym_expr[0]);
	bool_put(sym_expr[1]);
	bool_put(cond);

	return true;
}

static bool build_clauses(void)
{
	unsigned int i;
	struct symbol *sym;

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
	}

	return true;
}

#if 0
static bool build_default_clauses(struct symbol *sym, struct bool_expr *symbol_value[2],
	unsigned int sat_variable, struct bool_expr *visible,
	struct property *prop)
{
	struct bool_expr *menu_cond[2];
	struct bool_expr *cond;
	unsigned int nr_conjuncts;
	struct cnf_clause *i;
	struct bool_expr *value[2];
	struct bool_expr *t1, *t2, *t3, *t4, *t5, *t6, *t7;
	struct cnf *cnf;
	struct gstr str1, str2;

	if (prop->visible.expr) {
		expr_to_bool_expr(sym, prop->visible.expr, menu_cond);
	} else {
		menu_cond[0] = bool_const(true);
		menu_cond[1] = bool_const(false);
	}

	cond = bool_const(false);
	nr_conjuncts = 0;
	for (i = kconfig_cnf->first; i; i = i->next) {
		struct bool_expr *old_cond;
		struct bool_expr *conj;

		if (i->positive && bitset_test(i->positive, sat_variable)) {
			conj = clause_to_bool_except(i, sat_variable);
		} else if (i->negative && bitset_test(i->negative, sat_variable)) {
			conj = clause_to_bool_except(i, sat_variable);
		} else
			continue;

		cond = bool_or(old_cond = cond, conj);
		bool_put(old_cond);
		bool_put(conj);

		++nr_conjuncts;
	}

	if (nr_conjuncts == 0) {
		bool_put(cond);
		cond = bool_const(true);
	}

	assert(prop->expr);
	expr_to_bool_expr(NULL, prop->expr, value);

	t1 = bool_eq(value[0], symbol_value[0]);
	t2 = bool_eq(value[1], symbol_value[1]);
	bool_put(value[0]);
	bool_put(value[1]);
	t3 = bool_and(t1, t2);
	bool_put(t1);
	bool_put(t2);

	t4 = bool_and(menu_cond[0], cond);
	bool_put(menu_cond[0]);
	bool_put(menu_cond[1]);
	bool_put(cond);

	t5 = bool_not(visible);

	t6 = bool_and(t4, t5);
	bool_put(t4);
	bool_put(t5);

	t7 = bool_dep(t6, t3);
	bool_put(t6);
	bool_put(t3);

	cnf = bool_to_cnf(t7);
	bool_put(t7);

	str1 = str_new();
	expr_gstr_print(prop->expr, &str1);
	str2 = str_new();

	if (prop->visible.expr) {
		str_append(&str2, " if ");
		expr_gstr_print(prop->visible.expr, &str2);
	}
	add_cnf(cnf, "%s default %s%s", sym->name ?: "<choice>",
		str_get(&str1), str_get(&str2));
	str_free(&str1);
	str_free(&str2);

	cnf_put(cnf);
	return true;
}

static bool build_all_default_clauses(void)
{
	unsigned int i;
	struct symbol *sym;

	/* XXX: This is O(N * M) where N is the number of variables
	 * and M is the number of clauses. Optimise. */
	for_all_symbols(i, sym) {
		struct property *prompt;
		struct bool_expr *symbol_value[2];
		struct property *prop;
		unsigned int nr_prompts;

		if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
			continue;

		/* Choice defaults are interpreted differently */
		if (sym_is_choice(sym))
			continue;

		/* Choice values don't have defaults */
		if (sym_is_choice_value(sym))
			continue;

		symbol_to_bool_expr(sym, symbol_value);

		nr_prompts = 0;
		for_all_prompts(sym, prompt) {
			struct bool_expr *visible[2];
			unsigned int nr_defaults;

			++nr_prompts;

			if (prompt->visible.expr) {
				expr_to_bool_expr(sym, prompt->visible.expr, visible);
			} else {
				visible[0] = bool_const(true);
				visible[1] = bool_const(false);
			}

			nr_defaults = 0;
			for_all_defaults(sym, prop) {
				if (prop->menu != prompt->menu)
					continue;

				++nr_defaults;
				build_default_clauses(sym, symbol_value, prompt->sat_variable, visible[0], prop);
			}

#if 0
			/* Default to 'n' */
			if (nr_defaults == 0) {
				build_default_clauses(sym, symbol_value, prompt, visible[0], 
			}
#endif

			bool_put(visible[0]);
			bool_put(visible[1]);
		}

		if (nr_prompts == 0) {
			for_all_defaults(sym, prop) {
				build_default_clauses(sym, symbol_value, sym->sat_variable, bool_const(false), prop);
			}
		}

		bool_put(symbol_value[0]);
		bool_put(symbol_value[1]);
	}

	return true;
}
#endif

static unsigned int nr_changed = 0;

static void check_sym_value(struct symbol *sym, tristate value)
{
	static const char *tristate_names[] = {
		[no] = "no",
		[mod] = "mod",
		[yes] = "yes",
	};

	if (sym->curr.tri == value)
		return;

#if 1
	fprintf(stderr, "warning: symbol %s changed from %s to %s\n",
		sym->name ?: "<choice>",
		tristate_names[value],
		tristate_names[sym->curr.tri]);
#endif
	++nr_changed;
}

int main(int argc, char *argv[])
{
	setlocale(LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);

	picosat_init();
	picosat_enable_trace_generation();
	picosat_set_global_default_phase(0);

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

		struct expr *e;
		expr_list_for_each_sym(sym_env_list, e, sym) {
			struct property *prop;
			struct symbol *env_sym;

			prop = sym_get_env_prop(sym);
			env_sym = prop_get_symbol(prop);
			if (!env_sym)
				continue;

			sym->curr.val = getenv(env_sym->name);
		}
	}

	assign_sat_variables();

	/* We _will_ need more variables as we build the clauses, but
	 * picosat_inc_max_var() takes care of it. */
	picosat_adjust(1 + nr_sat_variables);

	/* Create a boolean variable that we force to be false */
	bool_true = bool_var(picosat_inc_max_var());
	add_clause("true", 1, bool_true->literal);

	if (!build_clauses()) {
		fprintf(stderr, "error: inconsistent kconfig files while "
			"building clauses\n");
		exit(EXIT_FAILURE);
	}

#if 0
	if (!build_all_default_clauses()) {
		fprintf(stderr, "error: inconsistent kconfig files while "
			"building default clauses\n");
		exit(EXIT_FAILURE);
	}
#endif

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

	picosat_set_default_phase_lit(modules_sym->sat_variable, 1);

#if 0
	{
		unsigned int i;
		struct symbol *sym;

		for_all_symbols(i, sym) {
			if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
				continue;
			if (!build_visible(sym))
				return false;
		}
	}
#endif

	bool_put(bool_true);
	assert(nr_bool_created == nr_bool_destroyed);

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

	{
		/* Use assumptions */
		unsigned int i;
		struct symbol *sym;
		for_all_symbols(i, sym) {
			if (sym->type != S_BOOLEAN && sym->type != S_TRISTATE)
				continue;

			bool assume = true;

			if (!(sym->flags & (SYMBOL_DEF << S_DEF_SAT))) {
				assume = false;
			} else if (sym->flags & SYMBOL_CHOICE) {
				assume = false;
			} else {
				switch (sym->curr.tri) {
				case no:
					picosat_assume(-sym_y(sym));
					break;
				case yes:
					picosat_assume(sym_y(sym));
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
	}

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

	if (conf_write(".config")) {
		fprintf(stderr, "error: writing configuration\n");
		exit(EXIT_FAILURE);
	}

	if (conf_write_autoconf()) {
		fprintf(stderr, "error: writing configuration\n");
		exit(EXIT_FAILURE);
	}

	{
		/* Check that none of the symbol values changed while writing
		 * out the configuration files. */
		unsigned int i;
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
							check_sym_value(sym, mod);
						else if (m == -1)
							check_sym_value(sym, yes);
					} else {
						check_sym_value(sym, yes);
					}
				} else if (y == -1) {
					if (sym->type == S_TRISTATE) {
						int m = picosat_deref(sym_m(sym));
						assert(m == -1);
					}

					check_sym_value(sym, no);
				}
			}
		}

		if (nr_changed) {
			fprintf(stderr, "warning: %u symbols differ "
				"from their SAT assignments\n", nr_changed);
		}
	}

	return EXIT_SUCCESS;
}
