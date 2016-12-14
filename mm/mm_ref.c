#include <linux/list.h>
#include <linux/mm_ref.h>
#include <linux/mm_types.h>
#include <linux/sched.h>
#include <linux/stacktrace.h>

static void _mm_ref_save_trace(struct mm_ref *ref)
{
	ref->pid = current->pid;

	/* Save stack trace */
	ref->trace.nr_entries = 0;
	ref->trace.entries = ref->trace_entries;
	ref->trace.max_entries = NR_MM_REF_STACK_ENTRIES;
	ref->trace.skip = 1;
	save_stack_trace(&ref->trace);
}

void INIT_MM_REF(struct mm_ref *ref)
{
	_mm_ref_save_trace(ref);
	INIT_LIST_HEAD(&ref->list_entry);
	ref->state = MM_REF_INITIALIZED;
}

static void dump_refs_list(const char *label, struct list_head *list)
{
	struct mm_ref *ref;

	if (list_empty(list)) {
		printk(KERN_ERR "%s: no refs\n", label);
		return;
	}

	printk(KERN_ERR "%s:\n", label);
	list_for_each_entry(ref, list, list_entry) {
		printk(KERN_ERR " - %p %x acquired by %d at:%s\n",
			ref, ref->state,
			ref->pid,
			ref->state == MM_REF_ACTIVE ? "" : " (bogus)");
		if (ref->state == MM_REF_ACTIVE)
			print_stack_trace(&ref->trace, 2);
	}
}

static void dump_refs(struct mm_struct *mm)
{
	unsigned long flags;

	spin_lock_irqsave(&mm->mm_refs_lock, flags);
	printk(KERN_ERR "mm_users = %u\n", atomic_read(&mm->mm_users));
	dump_refs_list("mm_users_list", &mm->mm_users_list);
	printk(KERN_ERR "mm_count = %u\n", atomic_read(&mm->mm_count));
	dump_refs_list("mm_count_list", &mm->mm_count_list);
	spin_unlock_irqrestore(&mm->mm_refs_lock, flags);
}

static bool _mm_ref_expect_inactive(struct mm_struct *mm, struct mm_ref *ref)
{
	if (ref->state == MM_REF_INITIALIZED || ref->state == MM_REF_INACTIVE)
		return true;

	if (ref->state == MM_REF_ACTIVE) {
		printk(KERN_ERR "trying to overwrite active ref %p to mm %p\n", ref, mm);
		printk(KERN_ERR "previous ref taken by %d at:\n", ref->pid);
		print_stack_trace(&ref->trace, 0);
	} else {
		printk(KERN_ERR "trying to overwrite ref %p in unknown state %x to mm %p\n",
			ref, ref->state, mm);
	}

	return false;
}

static bool _mm_ref_expect_active(struct mm_struct *mm, struct mm_ref *ref)
{
	if (ref->state == MM_REF_ACTIVE)
		return true;

	if (ref->state == MM_REF_INITIALIZED || ref->state == MM_REF_INACTIVE) {
		printk(KERN_ERR "trying to put inactive ref %p to mm %p\n", ref, mm);
		if (ref->state == MM_REF_INITIALIZED)
			printk(KERN_ERR "ref initialized by %d at:\n", ref->pid);
		else
			printk(KERN_ERR "previous ref dropped by %d at:\n", ref->pid);
		print_stack_trace(&ref->trace, 0);
	} else {
		printk(KERN_ERR "trying to put ref %p in unknown state %x to mm %p\n",
			ref, ref->state, mm);
	}

	return false;
}

void _get_mm_ref(struct mm_struct *mm, struct list_head *list, struct mm_ref *ref)
{
	unsigned long flags;

	if (!_mm_ref_expect_inactive(mm, ref)) {
		dump_refs(mm);
		BUG();
	}

	_mm_ref_save_trace(ref);

	spin_lock_irqsave(&mm->mm_refs_lock, flags);
	list_add_tail(&ref->list_entry, list);
	spin_unlock_irqrestore(&mm->mm_refs_lock, flags);

	ref->state = MM_REF_ACTIVE;
}

void _put_mm_ref(struct mm_struct *mm, struct list_head *list, struct mm_ref *ref)
{
	unsigned long flags;

	if (!_mm_ref_expect_active(mm, ref)) {
		dump_refs(mm);
		BUG();
	}

	_mm_ref_save_trace(ref);

	spin_lock_irqsave(&mm->mm_refs_lock, flags);
	BUG_ON(list_empty(&ref->list_entry));
	list_del_init(&ref->list_entry);
	spin_unlock_irqrestore(&mm->mm_refs_lock, flags);

	ref->state = MM_REF_INACTIVE;
}

/*
 * TODO: we have a choice here whether to ignore mm == NULL or
 * treat it as an error.
 * TODO: there's also a question about whether old_ref == new_ref
 * is an error or not.
 */
void _move_mm_ref(struct mm_struct *mm, struct list_head *list,
	struct mm_ref *old_ref, struct mm_ref *new_ref)
{
	unsigned long flags;

	if (!_mm_ref_expect_active(mm, old_ref)) {
		dump_refs(mm);
		BUG();
	}
	if (!_mm_ref_expect_inactive(mm, new_ref)) {
		dump_refs(mm);
		BUG();
	}

	_mm_ref_save_trace(old_ref);
	_mm_ref_save_trace(new_ref);

	spin_lock_irqsave(&mm->mm_refs_lock, flags);
	BUG_ON(list_empty(&old_ref->list_entry));
	list_del_init(&old_ref->list_entry);
	list_add_tail(&new_ref->list_entry, list);
	spin_unlock_irqrestore(&mm->mm_refs_lock, flags);

	old_ref->state = MM_REF_INACTIVE;
	new_ref->state = MM_REF_ACTIVE;
}
