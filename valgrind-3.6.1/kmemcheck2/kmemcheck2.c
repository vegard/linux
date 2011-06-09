#include <linux/gfp.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/slab.h>

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

static Bool chase_into_ok(void *private, Addr64 addr)
{
	printk(KERN_DEBUG "chase_into_ok(%p)\n", (void *) addr);
	return false;
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

#ifdef CONFIG_X86_32
#define KMEMCHECK2_VEX_ARCH VexArchX86
#endif

#ifdef CONFIG_X86_64
#define KMEMCHECK2_VEX_ARCH VexArchAMD64
#endif

static const VexArchInfo arch_info = {
	.hwcaps = 0,
	.ppc_cache_line_szB = 0,
};

static const VexAbiInfo abi_info = {
#ifdef CONFIG_X86_64
	.guest_stack_redzone_size = 128,
#else
	.guest_stack_redzone_size = 0,
#endif
	.guest_ppc_zap_RZ_at_blr = False,
	.guest_ppc_zap_RZ_at_bl = NULL,
	.guest_ppc_sc_continues_at_LR = False,
	.host_ppc_calls_use_fndescrs = False,
	.host_ppc32_regalign_int64_args = False,
};

static bool ran_translated_code = false;

static void translated_code(void)
{
	printk(KERN_DEBUG "kmemcheck2: translated_code\n");
	ran_translated_code = true;
}

static void dispatch(void)
{
	/* Just return */
}

int __init kmemcheck2_init(void)
{
	LibVEX_Init(&failure_exit, &log_bytes, 1, false, &clo_vex_control);

	VexTranslateArgs args;

	args.arch_guest = KMEMCHECK2_VEX_ARCH;
	args.archinfo_guest = arch_info;
	args.arch_host = KMEMCHECK2_VEX_ARCH;
	args.archinfo_host = arch_info;
	args.abiinfo_both = abi_info;

	args.callback_opaque = NULL;

	args.guest_bytes = (void *) &translated_code;
	args.guest_bytes_addr = (Addr64) &translated_code;

	args.chase_into_ok = &chase_into_ok;

	VexGuestExtents extents;
	extents.base[0] = 0;
	extents.base[1] = 0;
	extents.base[2] = 0;
	extents.len[0] = 0;
	extents.len[1] = 0;
	extents.len[2] = 0;
	extents.n_used = 0;

	args.guest_extents = &extents;

	Int host_bytes_used = 0;
	args.host_bytes = kmalloc(PAGE_SIZE, GFP_KERNEL);
	args.host_bytes_size = PAGE_SIZE;
	args.host_bytes_used = &host_bytes_used;

	args.instrument1 = NULL;
	args.instrument2 = NULL;
	args.finaltidy = NULL;

	args.do_self_check = False;

	args.preamble_function = NULL;

	args.traceflags = -1;

	args.dispatch = &dispatch;

	VexTranslateResult res;
	res = LibVEX_Translate(&args);

	if (res == VexTransOK) {
		printk(KERN_DEBUG "LibVEX_Translate OK\n");

		/* Execute translated code */
		((void (*)(void)) extents.base[0])();

		BUG_ON(!ran_translated_code);
	} else if (res == VexTransAccessFail) {
		printk(KERN_DEBUG "LibVEX_Translate AccessFail\n");
	} else if (res == VexTransOutputFull) {
		printk(KERN_DEBUG "LibVEX_Translate OutputFull\n");
	}

	printk(KERN_INFO "kmemcheck2: Initialized\n");
	return 0;
}

early_initcall(kmemcheck2_init);
