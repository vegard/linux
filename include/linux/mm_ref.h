#ifndef LINUX_MM_REF_H
#define LINUX_MM_REF_H

#include <linux/mm_types.h>
#include <linux/mm_ref_types.h>

struct mm_struct;

extern void INIT_MM_REF(struct mm_ref *ref);

extern void _get_mm_ref(struct mm_struct *mm, struct list_head *list,
	struct mm_ref *ref);
extern void _put_mm_ref(struct mm_struct *mm, struct list_head *list,
	struct mm_ref *ref);
extern void _move_mm_ref(struct mm_struct *mm, struct list_head *list,
	struct mm_ref *old_ref, struct mm_ref *new_ref);

static inline void get_mm_ref(struct mm_struct *mm, struct mm_ref *ref)
{
	_get_mm_ref(mm, &mm->mm_count_list, ref);
}

static inline void put_mm_ref(struct mm_struct *mm, struct mm_ref *ref)
{
	_put_mm_ref(mm, &mm->mm_count_list, ref);
}

static inline void move_mm_ref(struct mm_struct *mm, struct mm_ref *old_ref, struct mm_ref *new_ref)
{
	_move_mm_ref(mm, &mm->mm_count_list, old_ref, new_ref);
}

static inline void get_mm_users_ref(struct mm_struct *mm, struct mm_ref *ref)
{
	_get_mm_ref(mm, &mm->mm_users_list, ref);
}

static inline void put_mm_users_ref(struct mm_struct *mm, struct mm_ref *ref)
{
	_put_mm_ref(mm, &mm->mm_users_list, ref);
}

static inline void move_mm_users_ref(struct mm_struct *mm, struct mm_ref *old_ref, struct mm_ref *new_ref)
{
	_move_mm_ref(mm, &mm->mm_users_list, old_ref, new_ref);
}

#endif
