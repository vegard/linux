#ifndef LINUX_MM_REF_TYPES_H
#define LINUX_MM_REF_TYPES_H

#include <linux/list.h>
#include <linux/stacktrace.h>

#define NR_MM_REF_STACK_ENTRIES 10

enum mm_ref_state {
	/*
	 * Pick 0 as uninitialized so we have a chance at catching
	 * uninitialized references by noticing that they are zero.
	 *
	 * The rest are random 32-bit integers.
	 */
	MM_REF_UNINITIALIZED	= 0,
	MM_REF_INITIALIZED	= 0x28076894UL,
	MM_REF_ACTIVE		= 0xdaf46189UL,
	MM_REF_INACTIVE		= 0xf5358bafUL,
};

struct mm_ref {
	/*
	 * See ->mm_users_list/->mm_count_list in struct mm_struct.
	 * Access is protected by ->mm_refs_lock.
	 */
	struct list_head list_entry;

	enum mm_ref_state state;
	int pid;
	struct stack_trace trace;
	unsigned long trace_entries[NR_MM_REF_STACK_ENTRIES];
};

#define MM_REF_INIT(name) \
	{ LIST_HEAD_INIT(name.list_entry), MM_REF_INITIALIZED, }

#define MM_REF(name) \
	struct mm_ref name = MM_REF_INIT(name)

#endif
