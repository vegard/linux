#include <linux/mm_types.h>
#include <linux/rbtree.h>
#include <linux/rwsem.h>
#include <linux/spinlock.h>
#include <linux/list.h>
#include <linux/cpumask.h>

#include <linux/atomic.h>
#include <asm/pgtable.h>
#include <asm/mmu.h>

#ifndef INIT_MM_CONTEXT
#define INIT_MM_CONTEXT(name)
#endif

struct mm_struct init_mm = {
	.mm_rb		= RB_ROOT,
	.pgd		= swapper_pg_dir,
	.mm_refs_lock	= __SPIN_LOCK_UNLOCKED(init_mm.mm_refs_lock),
	.mm_users	= ATOMIC_INIT(2),
	.mm_users_list	= LIST_HEAD_INIT(init_mm.mm_users_list),
	.mm_users_ref	= MM_REF_INIT(init_mm.mm_users_ref),
	.mm_count	= ATOMIC_INIT(1),
	.mm_count_list	= LIST_HEAD_INIT(init_mm.mm_count_list),
	.mmap_sem	= __RWSEM_INITIALIZER(init_mm.mmap_sem),
	.page_table_lock =  __SPIN_LOCK_UNLOCKED(init_mm.page_table_lock),
	.mmlist		= LIST_HEAD_INIT(init_mm.mmlist),
	INIT_MM_CONTEXT(init_mm)
};

MM_REF(init_mm_ref);
