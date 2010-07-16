#ifndef BITSET_H
#define BITSET_H

#include <math.h>
#include <stdbool.h>
#include <stdint.h>

#define BITSET_NR_CHILDREN_PER_NODE 4
#define BITSET_NR_UNITS_PER_LEAF 1

typedef unsigned long bitset_unit;
static const unsigned int bitset_bits_per_unit = 8 * sizeof(bitset_unit);

/* assert(BITSET_NR_CHILDREN_PER_NODE > 1); */
/* assert(BITSET_NR_UNITS_PER_LEAF > 0); */
/* assert(sizeof(struct bitset_node *) == sizeof(bitset_unit *)); */

struct bitset_node {
	unsigned int refcount;

	union {
		/* Internal node */
		struct bitset_node *children[BITSET_NR_CHILDREN_PER_NODE];

		/* Leaf node */
		bitset_unit *data[BITSET_NR_CHILDREN_PER_NODE];
	};
};

static struct bitset_node *bitset_node_get(struct bitset_node *node)
{
	if (!node)
		return node;

	assert(node->refcount > 0);

	++node->refcount;
	return node;
}

static void bitset_node_put(struct bitset_node *node, unsigned int level)
{
	if (!node)
		return;

	assert(node->refcount > 0);

	if (--node->refcount == 0) {
		unsigned int i;

		if (level == 0) {
			for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
				free(node->data[i]);
		} else {
			for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
				bitset_node_put(node->children[i], level - 1);
		}

		free(node);
	}
}

struct bitset {
	unsigned int refcount;
	unsigned int size;
	unsigned int real_size;
	unsigned int levels;

	struct bitset_node root;
};

static inline unsigned int ceildiv(unsigned int dividend, unsigned int divisor)
{
	return (dividend + divisor - 1) / divisor;
}

static inline unsigned int ceililog2(unsigned int size)
{
	unsigned int bits = 8 * sizeof(size) - 1 - __builtin_clz(size);

	return bits + !!(size & ((1U << (bits - 1)) - 1));
}

static inline unsigned int ceililog(unsigned int base, unsigned int size)
{
	return ceildiv(ceililog2(size), ceililog2(base));
}

static inline void bitset_init(struct bitset *bitset, unsigned int size)
{
	bitset->refcount = 1;
	bitset->size = size;
	bitset->levels = ceililog(BITSET_NR_CHILDREN_PER_NODE,
		ceildiv(size, (BITSET_NR_UNITS_PER_LEAF * bitset_bits_per_unit)));

	{
		unsigned int i;
		unsigned int real_size = bitset_bits_per_unit
			* BITSET_NR_UNITS_PER_LEAF;

		for (i = 0; i < bitset->levels; ++i)
			real_size *= BITSET_NR_CHILDREN_PER_NODE;

#if 0
		printf("%u: %u %f (%u)\n", size, bitset->levels,
			log(1. * size / (BITSET_NR_UNITS_PER_LEAF * bitset_bits_per_unit))
				/ log(BITSET_NR_CHILDREN_PER_NODE),
			real_size);
#endif

		assert(real_size >= size);

		bitset->real_size = real_size;
	}

	if (bitset->levels == 1) {
		unsigned int i;

		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
			bitset->root.data[i] = NULL;
	} else {
		unsigned int i;

		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
			bitset->root.children[i] = NULL;
	}
}

static inline struct bitset_node *bitset_node_new(void)
{
	struct bitset_node *node;
	unsigned int i;

	node = malloc(sizeof(*node));
	if (!node)
		return node;

	node->refcount = 1;
	for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
		node->children[i] = NULL;

	return node;
}

static inline bitset_unit *bitset_leaf_new(void)
{
	return calloc(BITSET_NR_UNITS_PER_LEAF, sizeof(bitset_unit));
}

static inline void bitset_leaf_print(bitset_unit *data, unsigned int offset)
{
	unsigned int i;

	if (!data)
		return;

	for (i = 0; i < BITSET_NR_UNITS_PER_LEAF; ++i) {
		unsigned int j;

		for (j = 0; j < bitset_bits_per_unit; ++j) {
			if (data[i] & ((bitset_unit) 1 << j)) {
				printf("%u ", BITSET_NR_UNITS_PER_LEAF * bitset_bits_per_unit
					* offset + bitset_bits_per_unit * i + j);
			}
		}
	}
}

static inline void bitset_node_print(struct bitset_node *node,
	unsigned int level, unsigned int offset)
{
	unsigned int i;

	if (!node)
		return;

	if (level == 0) {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			bitset_leaf_print(node->data[i],
				offset * BITSET_NR_CHILDREN_PER_NODE + i);
		}
	} else {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			bitset_node_print(node->children[i], level - 1,
				offset * BITSET_NR_CHILDREN_PER_NODE + i);
		}
	}
}

static inline void bitset_print(struct bitset *bitset)
{
	printf("{ ");
	bitset_node_print(&bitset->root, bitset->levels - 1, 0);
	printf("}");
}

static inline struct bitset *bitset_get(struct bitset *bitset)
{
	if (!bitset)
		return NULL;

	assert(bitset->refcount > 0);

	++bitset->refcount;
	return bitset;
}

static inline void bitset_put(struct bitset *bitset)
{
	if (!bitset)
		return;

	assert(bitset->refcount > 0);

	if (--bitset->refcount == 0) {
		unsigned int i;

		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
			bitset_node_put(bitset->root.children[i], bitset->levels - 2);

		free(bitset);
	}
}

static inline struct bitset *bitset_new(unsigned int size)
{
	struct bitset *r;

	r = malloc(sizeof(*r));
	if (!r)
		return r;

	bitset_init(r, size);
	return r;
}

static inline void bitset_leaf_set(bitset_unit *data, unsigned int mask, unsigned int index)
{
	unsigned int i = index / mask;
	unsigned int j = index % mask;

	data[i] |= (bitset_unit) 1 << j;
}

static inline void bitset_node_set(struct bitset_node *node,
	unsigned int level, unsigned int mask, unsigned int index)
{
	if (level == 0) {
		unsigned int i = index / mask;

		if (!node->data[i])
			node->data[i] = bitset_leaf_new();

		bitset_leaf_set(node->data[i], mask / BITSET_NR_UNITS_PER_LEAF, index % mask);
	} else {
		unsigned int i = index / mask;

		if (!node->children[i])
			node->children[i] = bitset_node_new();
		bitset_node_set(node->children[i],
			level - 1, mask / BITSET_NR_CHILDREN_PER_NODE, index % mask);
	}
}

static inline void bitset_set(struct bitset *bitset, unsigned int index)
{
	bitset_node_set(&bitset->root, bitset->levels - 1,
		bitset->real_size / BITSET_NR_CHILDREN_PER_NODE, index);
}

static inline bool bitset_leaf_test(bitset_unit *data, unsigned int mask, unsigned int index)
{
	unsigned int i = index / mask;
	unsigned int j = index % mask;

	return data[i] & (bitset_unit) 1 << j;
}

static inline bool bitset_node_test(struct bitset_node *node,
	unsigned int level, unsigned int mask, unsigned int index)
{
	if (level == 0) {
		unsigned int i = index / mask;

		if (!node->data[i])
			return false;

		return bitset_leaf_test(node->data[i],
			mask / BITSET_NR_UNITS_PER_LEAF, index % mask);
	} else {
		unsigned int i = index / mask;

		if (!node->children[i])
			return false;

		return bitset_node_test(node->children[i],
			level - 1, mask / BITSET_NR_CHILDREN_PER_NODE, index % mask);
	}
}

static inline bool bitset_test(struct bitset *bitset, unsigned int index)
{
	return bitset_node_test(&bitset->root, bitset->levels - 1,
		bitset->real_size / BITSET_NR_CHILDREN_PER_NODE, index);
}

static inline struct bitset *bitset_new_single(unsigned int size, unsigned int bit)
{
	struct bitset *bitset;

	bitset = bitset_new(size);
	bitset_set(bitset, bit);
	return bitset;
}

static inline bool bitset_leaf_empty_intersection(bitset_unit *x, bitset_unit *y)
{
	unsigned int i;

	if (!x || !y)
		return true;

	for (i = 0; i < BITSET_NR_UNITS_PER_LEAF; ++i) {
		if (x[i] & y[i])
			return false;
	}

	return true;
}

static inline bool bitset_node_empty_intersection(struct bitset_node *x, struct bitset_node *y,
	unsigned int level)
{
	unsigned int i;

	if (!x || !y)
		return true;

	if (level == 0) {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			if (!bitset_leaf_empty_intersection(x->data[i], y->data[i]))
				return false;
		}
	} else {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			if (!bitset_node_empty_intersection(x->children[i], y->children[i], level - 1))
				return false;
		}
	}

	return true;
}

static inline bool bitset_empty_intersection(struct bitset *x, struct bitset *y)
{
	if (!x || !y)
		return true;

	assert(x->size == y->size);
	assert(x->levels == y->levels);

	return bitset_node_empty_intersection(&x->root, &y->root, x->levels - 1);
}

static inline bitset_unit *bitset_leaf_union(bitset_unit *x, bitset_unit *y)
{
	/* XXX: Share leaves as well */
	unsigned int i;

	if (!x && !y)
		return NULL;

	bitset_unit *r = bitset_leaf_new();

	if (x) {
		if (y) {
			for (i = 0; i < BITSET_NR_UNITS_PER_LEAF; ++i)
				r[i] = x[i] | y[i];
		} else {
			for (i = 0; i < BITSET_NR_UNITS_PER_LEAF; ++i)
				r[i] = x[i];
		}
	} else {
		if (y) {
			for (i = 0; i < BITSET_NR_UNITS_PER_LEAF; ++i)
				r[i] = y[i];
		} else {
			assert(false);
		}
	}

	return r;
}

static inline void bitset_node_union(struct bitset_node *x, struct bitset_node *y,
	struct bitset_node *r, unsigned int level)
{
	unsigned int i;

	if (level == 0) {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i)
			r->data[i] = bitset_leaf_union(x->data[i], y->data[i]);
	} else {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			if (!x->children[i]) {
				r->children[i] = bitset_node_get(y->children[i]);
				continue;
			}

			if (!y->children[i]) {
				r->children[i] = bitset_node_get(x->children[i]);
				continue;
			}

			r->children[i] = bitset_node_new();
			bitset_node_union(x->children[i], y->children[i],
				r->children[i], level - 1);
		}
	}
}

static inline struct bitset *bitset_union(struct bitset *x, struct bitset *y)
{
	struct bitset *r;

	if (!x)
		return bitset_get(y);
	if (!y)
		return bitset_get(x);

	assert(x->size == y->size);
	assert(x->levels == y->levels);

	r = bitset_new(x->size);
	bitset_node_union(&x->root, &y->root, &r->root, x->levels - 1);
	return r;
}

static inline void bitset_leaf_call_for_each_bit(bitset_unit *data,
	unsigned int offset,
	void (*func)(void *, unsigned int), void *priv)
{
	unsigned int i;

	if (!data)
		return;

	for (i = 0; i < BITSET_NR_UNITS_PER_LEAF; ++i) {
		unsigned int j;

		for (j = 0; j < bitset_bits_per_unit; ++j) {
			if (data[i] & ((bitset_unit) 1 << j)) {
				func(priv, BITSET_NR_UNITS_PER_LEAF * bitset_bits_per_unit
					* offset + bitset_bits_per_unit * i + j);
			}
		}
	}
}

static inline void bitset_node_call_for_each_bit(struct bitset_node *node,
	unsigned int level, unsigned int offset,
	void (*func)(void *, unsigned int), void *priv)
{
	unsigned int i;

	if (!node)
		return;

	if (level == 0) {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			bitset_leaf_call_for_each_bit(node->data[i],
				offset * BITSET_NR_CHILDREN_PER_NODE + i, func, priv);
		}
	} else {
		for (i = 0; i < BITSET_NR_CHILDREN_PER_NODE; ++i) {
			bitset_node_call_for_each_bit(node->children[i], level - 1,
				offset * BITSET_NR_CHILDREN_PER_NODE + i, func, priv);
		}
	}
}

static inline void bitset_call_for_each_bit(struct bitset *bitset,
	void (*func)(void *, unsigned int), void *priv)
{
	bitset_node_call_for_each_bit(&bitset->root, bitset->levels - 1, 0, func, priv);
}

#endif
