#ifndef BOOL_H
#define BOOL_H

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

enum bool_op {
	CONST,
	LITERAL,

	NOT,
	AND,
	OR,
	EQ,
};

struct bool_expr {
	enum bool_op op;

	union {
		bool nullary;
		int literal;

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
		case CONST:
			break;

		case LITERAL:
			break;

		case NOT:
			bool_put(e->unary);
			break;

		case AND:
		case OR:
		case EQ:
			bool_put(e->binary.a);
			bool_put(e->binary.b);
			break;

		default:
			assert(false);
		}

		free(e);

		++nr_bool_destroyed;
	}
}

static struct bool_expr *bool_and(struct bool_expr *a, struct bool_expr *b);
static struct bool_expr *bool_or(struct bool_expr *a, struct bool_expr *b);

static struct bool_expr *bool_const(bool v)
{
	/* XXX: Integrate this with "bool_true" in satconf.c? */

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

static struct bool_expr *bool_literal(int literal)
{
	struct bool_expr *e = bool_new(LITERAL);
	e->literal = literal;
	return e;
}

static struct bool_expr *bool_var(unsigned int var)
{
	return bool_literal(var);
}

static struct bool_expr *bool_not(struct bool_expr *expr)
{
	if (expr->op == CONST)
		return bool_const(!expr->nullary);
	if (expr->op == LITERAL)
		return bool_literal(-expr->literal);
	if (expr->op == NOT)
		return bool_get(expr->unary);

	struct bool_expr *e = bool_new(NOT);
	e->unary = bool_get(expr);
	return e;
}

static struct bool_expr *bool_not_put(struct bool_expr *expr)
{
	struct bool_expr *e = bool_new(NOT);
	e->unary = expr;
	return e;
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

static struct bool_expr *bool_and_put(struct bool_expr *a, struct bool_expr *b)
{
	/* XXX: Don't get in the first place */
	struct bool_expr *ret = bool_and(a, b);
	bool_put(a);
	bool_put(b);
	return ret;
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

static struct bool_expr *bool_or_put(struct bool_expr *a, struct bool_expr *b)
{
	/* XXX: Don't get in the first place */
	struct bool_expr *ret = bool_or(a, b);
	bool_put(a);
	bool_put(b);
	return ret;
}

static struct bool_expr *bool_dep(struct bool_expr *a, struct bool_expr *b)
{
	struct bool_expr *t = bool_not(a);
	struct bool_expr *ret = bool_or(t, b);

	bool_put(t);
	return ret;
}

static struct bool_expr *bool_dep_put(struct bool_expr *a, struct bool_expr *b)
{
	/* XXX: Don't get in the first place */
	struct bool_expr *ret = bool_dep(a, b);
	bool_put(a);
	bool_put(b);
	return ret;
}

static struct bool_expr *bool_eq(struct bool_expr *a, struct bool_expr *b)
{
	if (a->op == CONST)
		return a->nullary ? bool_get(b) : bool_not(b);
	if (b->op == CONST)
		return b->nullary ? bool_get(a) : bool_not(a);

	struct bool_expr *e = bool_new(EQ);
	e->binary.a = bool_get(a);
	e->binary.b = bool_get(b);
	return e;
}

static struct bool_expr *bool_eq_put(struct bool_expr *a, struct bool_expr *b)
{
	/* XXX: Don't get in the first place */
	struct bool_expr *ret = bool_eq(a, b);
	bool_put(a);
	bool_put(b);
	return ret;
}

static void bool_fprint(FILE *out, struct bool_expr *e)
{
	assert(e);

	switch (e->op) {
	case CONST:
		fprintf(out, "%s", e->nullary ? "true" : "false");
		break;
	case LITERAL:
		fprintf(out, "%d", e->literal);
		break;
	case NOT:
		fprintf(out, "!(");
		bool_fprint(out, e->unary);
		fprintf(out, ")");
		break;
	case AND:
		fprintf(out, "(");
		bool_fprint(out, e->binary.a);
		fprintf(out, " && ");
		bool_fprint(out, e->binary.b);
		fprintf(out, ")");
		break;
	case OR:
		fprintf(out, "(");
		bool_fprint(out, e->binary.a);
		fprintf(out, " || ");
		bool_fprint(out, e->binary.b);
		fprintf(out, ")");
		break;
	case EQ:
		fprintf(out, "(");
		bool_fprint(out, e->binary.a);
		fprintf(out, " == ");
		bool_fprint(out, e->binary.b);
		fprintf(out, ")");
		break;

	default:
		assert(false);
	}
}

#endif
