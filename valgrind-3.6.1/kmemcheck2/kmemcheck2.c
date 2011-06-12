#include <linux/gfp.h>
#include <linux/init.h>
#include <linux/module.h>
#include <linux/kallsyms.h>
#include <linux/kernel.h>
#include <linux/rbtree.h>
#include <linux/slab.h>

#include <libvex.h>

__attribute__ ((noreturn))
static void failure_exit(void)
{
	panic("LibVEX exited");
}

static void log_bytes(char *str, int n)
{
	printk("%.*s", n, str);
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



static IRSB *kmemcheck2_instrument(void *data, IRSB *sb_in,
	VexGuestLayout *layout, VexGuestExtents *vge,
	IRType gwt, IRType hwt)
{
	Int i;
	IRSB *sb_out;
	char symname[KSYM_SYMBOL_LEN];

	sb_out = deepCopyIRSBExceptStmts(sb_in);
	symname[0] = '\0';

	for (i = 0; i < sb_in->stmts_used; ++i) {
		IRStmt *st = sb_in->stmts[i];

		if (st->tag == Ist_IMark)
			sprint_symbol(symname, st->Ist.IMark.addr);

		printk(KERN_DEBUG "%s: ", symname);
		ppIRStmt(st);
		printk("\n");

		addStmtToIRSB(sb_out, st);
	}

	return sb_out;
}

static struct rb_root kmemcheck2_translations;

struct kmemcheck2_translation {
	struct rb_node node;

	void *original;
	void *translated;
};

static inline struct kmemcheck2_translation *
rb_search_translations(void *address)
{
	struct rb_node *n = kmemcheck2_translations.rb_node;
	struct kmemcheck2_translation *t;

	while (n) {
		t = rb_entry(n, struct kmemcheck2_translation, node);
		if (address < t->original)
			n = n->rb_left;
		else if (address > t->original)
			n = n->rb_right;
		else
			return t;
	}

	return NULL;
}

static inline struct kmemcheck2_translation *
__rb_insert_translation(void *address, struct rb_node *node)
{
	struct rb_node **p = &kmemcheck2_translations.rb_node;
	struct rb_node *parent = NULL;
	struct kmemcheck2_translation *t;

	while (*p) {
		parent = *p;

		t = rb_entry(parent, struct kmemcheck2_translation, node);
		if (address < t->original)
			p = &(*p)->rb_left;
		else if (address > t->original)
			p = &(*p)->rb_right;
		else
			return t;
	}

	rb_link_node(node, parent, p);
	return NULL;
}

static inline struct kmemcheck2_translation *
rb_insert_translation(void *address, struct rb_node *node)
{
	struct kmemcheck2_translation *ret;

	ret = __rb_insert_translation(address, node);
	if (!ret)
		rb_insert_color(node, &kmemcheck2_translations);

	return ret;
}

static VexTranslateArgs args;
static VexGuestExtents extents;
static Int host_bytes_used;

static void kmemcheck2_translate_init(void)
{
	args.arch_guest = KMEMCHECK2_VEX_ARCH;
	args.archinfo_guest = arch_info;
	args.arch_host = KMEMCHECK2_VEX_ARCH;
	args.archinfo_host = arch_info;
	args.abiinfo_both = abi_info;

	args.callback_opaque = NULL;

	args.chase_into_ok = &chase_into_ok;

	extents.base[0] = 0;
	extents.base[1] = 0;
	extents.base[2] = 0;
	extents.len[0] = 0;
	extents.len[1] = 0;
	extents.len[2] = 0;
	extents.n_used = 0;

	args.guest_extents = &extents;

	args.host_bytes = NULL;
	args.host_bytes_size = 0;
	args.host_bytes_used = &host_bytes_used;

	args.instrument1 = &kmemcheck2_instrument;
	args.instrument2 = NULL;
	args.finaltidy = NULL;

	args.do_self_check = False;

	args.preamble_function = NULL;

	args.traceflags = 0;

	args.dispatch = &dispatch;
}

/*
 * Translate a single function. addr must point to the function's entry
 * point. Does not use the translation cache.
 */
static void *_kmemcheck2_translate(void *addr)
{
	VexTranslateResult res;

	args.guest_bytes = addr;
	args.guest_bytes_addr = (Addr64) addr;

	while (1) {
		res = LibVEX_Translate(&args);
		if (res == VexTransOK)
			break;

		if (res == VexTransOutputFull) {
			args.host_bytes = kmalloc(PAGE_SIZE, GFP_KERNEL);
			args.host_bytes_size = PAGE_SIZE;
			host_bytes_used = 0;
			continue;
		}

		BUG();
	}

	return (void *) extents.base[0];
}

/*
 * Translate a single function. Will use the cache if possible.
 */
void *kmemcheck2_translate(void *addr)
{
	struct kmemcheck2_translation *t;

	/* XXX: We should be able to optimise this by looking up the rb
	 * node only once. (We currently do it once for lookup and once
	 * for insertion if it's not there.) */
	t = rb_search_translations(addr);
	if (t)
		goto out;

	t = kmalloc(sizeof(*t), GFP_KERNEL);
	/* XXX: Check result */BUG_ON(!t);

	t->original = addr;
	t->translated = _kmemcheck2_translate(addr);

	rb_insert_translation(addr, &t->node);

out:
	return t->translated;
}

int __init kmemcheck2_init(void)
{
	LibVEX_Init(&failure_exit, &log_bytes, 1, false, &clo_vex_control);

	kmemcheck2_translate_init();

	/* Translate and execute stub */
	void (*func)(void) = kmemcheck2_translate(&translated_code);
	func();
	BUG_ON(!ran_translated_code);

	printk(KERN_INFO "kmemcheck2: Initialized\n");
	return 0;
}

early_initcall(kmemcheck2_init);
