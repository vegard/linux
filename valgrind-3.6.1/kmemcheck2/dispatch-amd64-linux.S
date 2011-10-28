#include <libvex_guest_offsets.h>

	.text
	.globl kmemcheck2_dispatch
kmemcheck2_dispatch:
	/* Save guest state on the stack */
	pushq %rbx
	pushq %rcx
	pushq %rdx
	pushq %rsi
	pushq %rbp
	pushq %r8
	pushq %r9
	pushq %r10
	pushq %r11
	pushq %r12
	pushq %r13
	pushq %r14
	pushq %r15
	pushq %rdi /* Guest state pointer */

	/* Fetch guest RIP into %rax */
	movq OFFSET_amd64_RIP(%rdi), %rdi

	/* XXX: flags/FP/SSE/etc. registers */

	/* Call the scheduler, which will translate the next piece of code
	 * if necessary. */
	call kmemcheck2_schedule

	/* Restore guest state from the stack */
	popq %rdi
	movq %rax, OFFSET_amd64_RIP(%rdi)

	popq %r15
	popq %r14
	popq %r13
	popq %r12
	popq %r11
	popq %r10
	popq %r9
	popq %r8
	popq %rbp
	popq %rsi
	popq %rdx
	popq %rcx
	popq %rbx
	ret
