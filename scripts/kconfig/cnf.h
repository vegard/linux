#ifndef CNF_H
#define CNF_H

#include "bitset.h"

struct cnf_clause {
	unsigned int refcount;

	/* This is not counted as a reference from the preceding clause,
	 * but from the owning CNF structure. */
	struct cnf_clause *next;

	struct bitset *positive;
	struct bitset *negative;
};

static inline void cnf_clause_init(struct cnf_clause *c,
	struct bitset *positive, struct bitset *negative)
{
	c->refcount = 1;
	c->next = NULL;
	c->positive = bitset_get(positive);
	c->negative = bitset_get(negative);
}

static inline struct cnf_clause *cnf_clause_get(struct cnf_clause *clause)
{
	assert(clause->refcount > 0);

	++clause->refcount;
	return clause;
}

static inline void cnf_clause_put(struct cnf_clause *clause)
{
	assert(clause->refcount > 0);

	if (--clause->refcount == 0) {
		bitset_put(clause->negative);
		bitset_put(clause->positive);
		free(clause);
	}
}

static inline struct cnf_clause *cnf_clause_new(struct bitset *positive, struct bitset *negative)
{
	struct cnf_clause *r;

	r = malloc(sizeof(*r));
	if (!r)
		return r;

	cnf_clause_init(r, positive, negative);
	return r;
}

struct cnf {
	unsigned int refcount;

	struct cnf_clause *first;
	struct cnf_clause *last;
};

#define cnf_for_each_clause(cnf, clause) \
	for (clause = cnf->first; clause; clause = clause->next)

static inline void cnf_init(struct cnf *cnf)
{
	cnf->refcount = 1;
	cnf->first = NULL;
	cnf->last = NULL;
}

static unsigned int nr_cnf_created = 0;
static unsigned int nr_cnf_destroyed = 0;

static inline struct cnf *cnf_new(void)
{
	struct cnf *r;

	r = malloc(sizeof(*r));
	if (!r)
		return r; 

	cnf_init(r);
	++nr_cnf_created;
	return r;
}

static inline struct cnf *cnf_get(struct cnf *cnf)
{
	assert(cnf->refcount > 0);

	++cnf->refcount;
	return cnf;
}

static inline void cnf_put(struct cnf *cnf)
{
	assert(cnf->refcount > 0);

	if (--cnf->refcount == 0) {
		struct cnf_clause *i, *next;

		for (i = cnf->first; i; i = next) {
			next = i->next;
			cnf_clause_put(i);
		}

		free(cnf);

		++nr_cnf_destroyed;
	}
}

static inline void cnf_add_clause(struct cnf *cnf, struct cnf_clause *clause)
{
	assert(!clause->next);

	if (!cnf->first)
		cnf->first = clause;
	if (cnf->last)
		cnf->last->next = clause;
	cnf->last = cnf_clause_get(clause);
}

static inline struct cnf *cnf_new_single_positive(unsigned int size, unsigned int var)
{
	struct bitset *t1;
	struct cnf_clause *t2;
	struct cnf *cnf;

	cnf = cnf_new();
	t1 = bitset_new_single(size, var);
	t2 = cnf_clause_new(t1, NULL);
	cnf_add_clause(cnf, t2);
	bitset_put(t1);
	cnf_clause_put(t2);
	return cnf;
}

static inline struct cnf *cnf_new_single_negative(unsigned int size, unsigned int var)
{
	struct bitset *t1;
	struct cnf_clause *t2;
	struct cnf *cnf;

	cnf = cnf_new();
	t1 = bitset_new_single(size, var);
	t2 = cnf_clause_new(NULL, t1);
	cnf_add_clause(cnf, t2);
	bitset_put(t1);
	cnf_clause_put(t2);
	return cnf;
}

/* Append y to x, destroying y in the process (it must not be shared). */
static inline void cnf_append(struct cnf *x, struct cnf *y)
{
	assert(y->refcount == 1);

	if (x->first)
		x->last->next = y->first;
	else
		x->first = y->first;

	if (y->last)
		x->last = y->last;

	y->first = NULL;
	y->last = NULL;

	cnf_put(y);
}

static inline struct cnf *cnf_and(struct cnf *x, struct cnf *y)
{
	/* Just append the list of x and y to form the result */

	struct cnf *r;
	struct cnf_clause *i;

	r = cnf_new();

	cnf_for_each_clause(x, i) {
		struct cnf_clause *t;

		t = cnf_clause_new(i->positive, i->negative);
		cnf_add_clause(r, t);
		cnf_clause_put(t);
	}

	cnf_for_each_clause(y, i) {
		struct cnf_clause *t;

		t = cnf_clause_new(i->positive, i->negative);
		cnf_add_clause(r, t);
		cnf_clause_put(t);
	}

	return r;
}

static inline struct cnf *cnf_or(struct cnf *x, struct cnf *y)
{
	/* Make the cross product of x and y to form the result */

	struct cnf *r;
	struct cnf_clause *i, *j;

	r = cnf_new();

	for (i = x->first; i; i = i->next) {
		for (j = y->first; j; j = j->next) {
			struct bitset *positive, *negative;

			positive = bitset_union(i->positive, j->positive);
			negative = bitset_union(i->negative, j->negative);
			if (bitset_empty_intersection(positive, negative)) {
				struct cnf_clause *t1;

				t1 = cnf_clause_new(positive, negative);
				cnf_add_clause(r, t1);
				cnf_clause_put(t1);
			}

			bitset_put(positive);
			bitset_put(negative);
		}
	}

	return r;
}

#endif
