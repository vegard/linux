#include <linux/init.h>
#include <linux/kernel.h>

#include <libvex.h>

__attribute__ ((noreturn))
static void failure_exit(void)
{
	panic("LibVEX exited");
}

static void log_bytes(char *str, int n)
{
	printk(KERN_DEBUG "%.*s\n", n, str);
}

static VexControl clo_vex_control = {
	.iropt_verbosity = 10,
	/* XXX */.iropt_level = 0,
	.iropt_precise_memory_exns = true,
	.iropt_unroll_thresh = 0,
	.guest_max_insns = 50,
	.guest_chase_thresh = 10,
	.guest_chase_cond = false,
};

int __init kmemcheck2_init(void)
{
	LibVEX_Init(&failure_exit, &log_bytes, 1, false, &clo_vex_control);

	printk("kmemcheck2: Initialized\n");
	return 0;
}

early_initcall(kmemcheck2_init);
