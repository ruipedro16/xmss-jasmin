	.att_syntax
	.text
	.p2align	5
	.globl	_keccakf1600_array
	.globl	keccakf1600_array
	.globl	_keccakf1600_ptr
	.globl	keccakf1600_ptr
_keccakf1600_array:
keccakf1600_array:
	movq	%rsp, %rax
	leaq	-256(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 208(%rsp)
	movq	%rbp, 216(%rsp)
	movq	%r12, 224(%rsp)
	movq	%r13, 232(%rsp)
	movq	%r14, 240(%rsp)
	movq	%rax, 248(%rsp)
	leaq	8(%rsp), %rax
	movq	(%rdi), %rcx
	movq	%rcx, (%rax)
	movq	8(%rdi), %rcx
	movq	%rcx, 8(%rax)
	movq	16(%rdi), %rcx
	movq	%rcx, 16(%rax)
	movq	24(%rdi), %rcx
	movq	%rcx, 24(%rax)
	movq	32(%rdi), %rcx
	movq	%rcx, 32(%rax)
	movq	40(%rdi), %rcx
	movq	%rcx, 40(%rax)
	movq	48(%rdi), %rcx
	movq	%rcx, 48(%rax)
	movq	56(%rdi), %rcx
	movq	%rcx, 56(%rax)
	movq	64(%rdi), %rcx
	movq	%rcx, 64(%rax)
	movq	72(%rdi), %rcx
	movq	%rcx, 72(%rax)
	movq	80(%rdi), %rcx
	movq	%rcx, 80(%rax)
	movq	88(%rdi), %rcx
	movq	%rcx, 88(%rax)
	movq	96(%rdi), %rcx
	movq	%rcx, 96(%rax)
	movq	104(%rdi), %rcx
	movq	%rcx, 104(%rax)
	movq	112(%rdi), %rcx
	movq	%rcx, 112(%rax)
	movq	120(%rdi), %rcx
	movq	%rcx, 120(%rax)
	movq	128(%rdi), %rcx
	movq	%rcx, 128(%rax)
	movq	136(%rdi), %rcx
	movq	%rcx, 136(%rax)
	movq	144(%rdi), %rcx
	movq	%rcx, 144(%rax)
	movq	152(%rdi), %rcx
	movq	%rcx, 152(%rax)
	movq	160(%rdi), %rcx
	movq	%rcx, 160(%rax)
	movq	168(%rdi), %rcx
	movq	%rcx, 168(%rax)
	movq	176(%rdi), %rcx
	movq	%rcx, 176(%rax)
	movq	184(%rdi), %rcx
	movq	%rcx, 184(%rax)
	movq	192(%rdi), %rcx
	movq	%rcx, 192(%rax)
	movq	%rdi, (%rsp)
	leaq	-224(%rsp), %rsp
	call	L_keccakf1600$1
Lkeccakf1600_array$1:
	leaq	224(%rsp), %rsp
	movq	(%rsp), %rcx
	movq	(%rax), %rdx
	movq	%rdx, (%rcx)
	movq	8(%rax), %rdx
	movq	%rdx, 8(%rcx)
	movq	16(%rax), %rdx
	movq	%rdx, 16(%rcx)
	movq	24(%rax), %rdx
	movq	%rdx, 24(%rcx)
	movq	32(%rax), %rdx
	movq	%rdx, 32(%rcx)
	movq	40(%rax), %rdx
	movq	%rdx, 40(%rcx)
	movq	48(%rax), %rdx
	movq	%rdx, 48(%rcx)
	movq	56(%rax), %rdx
	movq	%rdx, 56(%rcx)
	movq	64(%rax), %rdx
	movq	%rdx, 64(%rcx)
	movq	72(%rax), %rdx
	movq	%rdx, 72(%rcx)
	movq	80(%rax), %rdx
	movq	%rdx, 80(%rcx)
	movq	88(%rax), %rdx
	movq	%rdx, 88(%rcx)
	movq	96(%rax), %rdx
	movq	%rdx, 96(%rcx)
	movq	104(%rax), %rdx
	movq	%rdx, 104(%rcx)
	movq	112(%rax), %rdx
	movq	%rdx, 112(%rcx)
	movq	120(%rax), %rdx
	movq	%rdx, 120(%rcx)
	movq	128(%rax), %rdx
	movq	%rdx, 128(%rcx)
	movq	136(%rax), %rdx
	movq	%rdx, 136(%rcx)
	movq	144(%rax), %rdx
	movq	%rdx, 144(%rcx)
	movq	152(%rax), %rdx
	movq	%rdx, 152(%rcx)
	movq	160(%rax), %rdx
	movq	%rdx, 160(%rcx)
	movq	168(%rax), %rdx
	movq	%rdx, 168(%rcx)
	movq	176(%rax), %rdx
	movq	%rdx, 176(%rcx)
	movq	184(%rax), %rdx
	movq	%rdx, 184(%rcx)
	movq	192(%rax), %rax
	movq	%rax, 192(%rcx)
	movq	208(%rsp), %rbx
	movq	216(%rsp), %rbp
	movq	224(%rsp), %r12
	movq	232(%rsp), %r13
	movq	240(%rsp), %r14
	movq	248(%rsp), %rsp
	ret
_keccakf1600_ptr:
keccakf1600_ptr:
	movq	%rsp, %rax
	leaq	-256(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rbx, 208(%rsp)
	movq	%rbp, 216(%rsp)
	movq	%r12, 224(%rsp)
	movq	%r13, 232(%rsp)
	movq	%r14, 240(%rsp)
	movq	%rax, 248(%rsp)
	leaq	8(%rsp), %rax
	movq	(%rdi), %rcx
	movq	%rcx, (%rax)
	movq	8(%rdi), %rcx
	movq	%rcx, 8(%rax)
	movq	16(%rdi), %rcx
	movq	%rcx, 16(%rax)
	movq	24(%rdi), %rcx
	movq	%rcx, 24(%rax)
	movq	32(%rdi), %rcx
	movq	%rcx, 32(%rax)
	movq	40(%rdi), %rcx
	movq	%rcx, 40(%rax)
	movq	48(%rdi), %rcx
	movq	%rcx, 48(%rax)
	movq	56(%rdi), %rcx
	movq	%rcx, 56(%rax)
	movq	64(%rdi), %rcx
	movq	%rcx, 64(%rax)
	movq	72(%rdi), %rcx
	movq	%rcx, 72(%rax)
	movq	80(%rdi), %rcx
	movq	%rcx, 80(%rax)
	movq	88(%rdi), %rcx
	movq	%rcx, 88(%rax)
	movq	96(%rdi), %rcx
	movq	%rcx, 96(%rax)
	movq	104(%rdi), %rcx
	movq	%rcx, 104(%rax)
	movq	112(%rdi), %rcx
	movq	%rcx, 112(%rax)
	movq	120(%rdi), %rcx
	movq	%rcx, 120(%rax)
	movq	128(%rdi), %rcx
	movq	%rcx, 128(%rax)
	movq	136(%rdi), %rcx
	movq	%rcx, 136(%rax)
	movq	144(%rdi), %rcx
	movq	%rcx, 144(%rax)
	movq	152(%rdi), %rcx
	movq	%rcx, 152(%rax)
	movq	160(%rdi), %rcx
	movq	%rcx, 160(%rax)
	movq	168(%rdi), %rcx
	movq	%rcx, 168(%rax)
	movq	176(%rdi), %rcx
	movq	%rcx, 176(%rax)
	movq	184(%rdi), %rcx
	movq	%rcx, 184(%rax)
	movq	192(%rdi), %rcx
	movq	%rcx, 192(%rax)
	movq	%rdi, (%rsp)
	leaq	-216(%rsp), %rsp
	call	L_keccakf1600_ref1$1
Lkeccakf1600_ptr$1:
	leaq	216(%rsp), %rsp
	movq	(%rsp), %rcx
	movq	(%rax), %rdx
	movq	%rdx, (%rcx)
	movq	8(%rax), %rdx
	movq	%rdx, 8(%rcx)
	movq	16(%rax), %rdx
	movq	%rdx, 16(%rcx)
	movq	24(%rax), %rdx
	movq	%rdx, 24(%rcx)
	movq	32(%rax), %rdx
	movq	%rdx, 32(%rcx)
	movq	40(%rax), %rdx
	movq	%rdx, 40(%rcx)
	movq	48(%rax), %rdx
	movq	%rdx, 48(%rcx)
	movq	56(%rax), %rdx
	movq	%rdx, 56(%rcx)
	movq	64(%rax), %rdx
	movq	%rdx, 64(%rcx)
	movq	72(%rax), %rdx
	movq	%rdx, 72(%rcx)
	movq	80(%rax), %rdx
	movq	%rdx, 80(%rcx)
	movq	88(%rax), %rdx
	movq	%rdx, 88(%rcx)
	movq	96(%rax), %rdx
	movq	%rdx, 96(%rcx)
	movq	104(%rax), %rdx
	movq	%rdx, 104(%rcx)
	movq	112(%rax), %rdx
	movq	%rdx, 112(%rcx)
	movq	120(%rax), %rdx
	movq	%rdx, 120(%rcx)
	movq	128(%rax), %rdx
	movq	%rdx, 128(%rcx)
	movq	136(%rax), %rdx
	movq	%rdx, 136(%rcx)
	movq	144(%rax), %rdx
	movq	%rdx, 144(%rcx)
	movq	152(%rax), %rdx
	movq	%rdx, 152(%rcx)
	movq	160(%rax), %rdx
	movq	%rdx, 160(%rcx)
	movq	168(%rax), %rdx
	movq	%rdx, 168(%rcx)
	movq	176(%rax), %rdx
	movq	%rdx, 176(%rcx)
	movq	184(%rax), %rdx
	movq	%rdx, 184(%rcx)
	movq	192(%rax), %rax
	movq	%rax, 192(%rcx)
	movq	208(%rsp), %rbx
	movq	216(%rsp), %rbp
	movq	224(%rsp), %r12
	movq	232(%rsp), %r13
	movq	240(%rsp), %r14
	movq	248(%rsp), %rsp
	ret
L_keccakf1600_ref1$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%rcx, 8(%rsp)
	leaq	24(%rsp), %rcx
	movq	$0, %rdx
	jmp 	L_keccakf1600_ref1$2
L_keccakf1600_ref1$3:
	movq	8(%rsp), %rsi
	movq	(%rsi,%rdx,8), %rsi
	movq	%rsi, 16(%rsp)
	movq	(%rax), %r10
	movq	8(%rax), %r9
	movq	16(%rax), %r11
	movq	24(%rax), %rbx
	movq	32(%rax), %rbp
	xorq	40(%rax), %r10
	xorq	48(%rax), %r9
	xorq	56(%rax), %r11
	xorq	64(%rax), %rbx
	xorq	72(%rax), %rbp
	xorq	80(%rax), %r10
	xorq	88(%rax), %r9
	xorq	96(%rax), %r11
	xorq	104(%rax), %rbx
	xorq	112(%rax), %rbp
	xorq	120(%rax), %r10
	xorq	128(%rax), %r9
	xorq	136(%rax), %r11
	xorq	144(%rax), %rbx
	xorq	152(%rax), %rbp
	xorq	160(%rax), %r10
	xorq	168(%rax), %r9
	xorq	176(%rax), %r11
	xorq	184(%rax), %rbx
	xorq	192(%rax), %rbp
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%rbp, %rsi
	movq	%r11, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbx, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%rbp, %r9
	rolq	$1, %r9
	xorq	%r11, %r9
	rolq	$1, %r10
	xorq	%rbx, %r10
	movq	(%rax), %r11
	xorq	%rsi, %r11
	movq	48(%rax), %rbx
	xorq	%rdi, %rbx
	rolq	$44, %rbx
	movq	96(%rax), %rbp
	xorq	%r8, %rbp
	rolq	$43, %rbp
	movq	144(%rax), %r12
	xorq	%r9, %r12
	rolq	$21, %r12
	movq	192(%rax), %r13
	xorq	%r10, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	16(%rsp), %r14
	movq	%r14, (%rcx)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 8(%rcx)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 16(%rcx)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 24(%rcx)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 32(%rcx)
	movq	24(%rax), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	72(%rax), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	80(%rax), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	128(%rax), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	176(%rax), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	movq	%r14, 40(%rcx)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 48(%rcx)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 56(%rcx)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 64(%rcx)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 72(%rcx)
	movq	8(%rax), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	56(%rax), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	104(%rax), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	152(%rax), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	160(%rax), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	movq	%r14, 80(%rcx)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 88(%rcx)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 96(%rcx)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 104(%rcx)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 112(%rcx)
	movq	32(%rax), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	40(%rax), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	88(%rax), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	136(%rax), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	184(%rax), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	movq	%r14, 120(%rcx)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 128(%rcx)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 136(%rcx)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 144(%rcx)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 152(%rcx)
	movq	16(%rax), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	64(%rax), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	112(%rax), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	120(%rax), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	168(%rax), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	movq	%r8, %rdi
	notq	%rdi
	andq	%r9, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 160(%rcx)
	movq	%r9, %rdi
	notq	%rdi
	andq	%r10, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 168(%rcx)
	movq	%r10, %rdi
	notq	%rdi
	andq	%rsi, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 176(%rcx)
	movq	%rsi, %rdi
	notq	%rdi
	andq	%r11, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 184(%rcx)
	notq	%r11
	andq	%r8, %r11
	xorq	%rsi, %r11
	movq	%r11, 192(%rcx)
	movq	8(%rsp), %rsi
	movq	8(%rsi,%rdx,8), %rsi
	movq	%rsi, 16(%rsp)
	movq	(%rcx), %r10
	movq	8(%rcx), %r9
	movq	16(%rcx), %r11
	movq	24(%rcx), %rbx
	movq	32(%rcx), %rbp
	xorq	40(%rcx), %r10
	xorq	48(%rcx), %r9
	xorq	56(%rcx), %r11
	xorq	64(%rcx), %rbx
	xorq	72(%rcx), %rbp
	xorq	80(%rcx), %r10
	xorq	88(%rcx), %r9
	xorq	96(%rcx), %r11
	xorq	104(%rcx), %rbx
	xorq	112(%rcx), %rbp
	xorq	120(%rcx), %r10
	xorq	128(%rcx), %r9
	xorq	136(%rcx), %r11
	xorq	144(%rcx), %rbx
	xorq	152(%rcx), %rbp
	xorq	160(%rcx), %r10
	xorq	168(%rcx), %r9
	xorq	176(%rcx), %r11
	xorq	184(%rcx), %rbx
	xorq	192(%rcx), %rbp
	movq	%r9, %rsi
	rolq	$1, %rsi
	xorq	%rbp, %rsi
	movq	%r11, %rdi
	rolq	$1, %rdi
	xorq	%r10, %rdi
	movq	%rbx, %r8
	rolq	$1, %r8
	xorq	%r9, %r8
	movq	%rbp, %r9
	rolq	$1, %r9
	xorq	%r11, %r9
	rolq	$1, %r10
	xorq	%rbx, %r10
	movq	(%rcx), %r11
	xorq	%rsi, %r11
	movq	48(%rcx), %rbx
	xorq	%rdi, %rbx
	rolq	$44, %rbx
	movq	96(%rcx), %rbp
	xorq	%r8, %rbp
	rolq	$43, %rbp
	movq	144(%rcx), %r12
	xorq	%r9, %r12
	rolq	$21, %r12
	movq	192(%rcx), %r13
	xorq	%r10, %r13
	rolq	$14, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	xorq	16(%rsp), %r14
	movq	%r14, (%rax)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 8(%rax)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 16(%rax)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 24(%rax)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 32(%rax)
	movq	24(%rcx), %r11
	xorq	%r9, %r11
	rolq	$28, %r11
	movq	72(%rcx), %rbx
	xorq	%r10, %rbx
	rolq	$20, %rbx
	movq	80(%rcx), %rbp
	xorq	%rsi, %rbp
	rolq	$3, %rbp
	movq	128(%rcx), %r12
	xorq	%rdi, %r12
	rolq	$45, %r12
	movq	176(%rcx), %r13
	xorq	%r8, %r13
	rolq	$61, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	movq	%r14, 40(%rax)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 48(%rax)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 56(%rax)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 64(%rax)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 72(%rax)
	movq	8(%rcx), %r11
	xorq	%rdi, %r11
	rolq	$1, %r11
	movq	56(%rcx), %rbx
	xorq	%r8, %rbx
	rolq	$6, %rbx
	movq	104(%rcx), %rbp
	xorq	%r9, %rbp
	rolq	$25, %rbp
	movq	152(%rcx), %r12
	xorq	%r10, %r12
	rolq	$8, %r12
	movq	160(%rcx), %r13
	xorq	%rsi, %r13
	rolq	$18, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	movq	%r14, 80(%rax)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 88(%rax)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 96(%rax)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 104(%rax)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 112(%rax)
	movq	32(%rcx), %r11
	xorq	%r10, %r11
	rolq	$27, %r11
	movq	40(%rcx), %rbx
	xorq	%rsi, %rbx
	rolq	$36, %rbx
	movq	88(%rcx), %rbp
	xorq	%rdi, %rbp
	rolq	$10, %rbp
	movq	136(%rcx), %r12
	xorq	%r8, %r12
	rolq	$15, %r12
	movq	184(%rcx), %r13
	xorq	%r9, %r13
	rolq	$56, %r13
	movq	%rbx, %r14
	notq	%r14
	andq	%rbp, %r14
	xorq	%r11, %r14
	movq	%r14, 120(%rax)
	movq	%rbp, %r14
	notq	%r14
	andq	%r12, %r14
	xorq	%rbx, %r14
	movq	%r14, 128(%rax)
	movq	%r12, %r14
	notq	%r14
	andq	%r13, %r14
	xorq	%rbp, %r14
	movq	%r14, 136(%rax)
	movq	%r13, %rbp
	notq	%rbp
	andq	%r11, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 144(%rax)
	notq	%r11
	andq	%rbx, %r11
	xorq	%r13, %r11
	movq	%r11, 152(%rax)
	movq	16(%rcx), %r11
	xorq	%r8, %r11
	rolq	$62, %r11
	movq	64(%rcx), %r8
	xorq	%r9, %r8
	rolq	$55, %r8
	movq	112(%rcx), %r9
	xorq	%r10, %r9
	rolq	$39, %r9
	movq	120(%rcx), %r10
	xorq	%rsi, %r10
	rolq	$41, %r10
	movq	168(%rcx), %rsi
	xorq	%rdi, %rsi
	rolq	$2, %rsi
	movq	%r8, %rdi
	notq	%rdi
	andq	%r9, %rdi
	xorq	%r11, %rdi
	movq	%rdi, 160(%rax)
	movq	%r9, %rdi
	notq	%rdi
	andq	%r10, %rdi
	xorq	%r8, %rdi
	movq	%rdi, 168(%rax)
	movq	%r10, %rdi
	notq	%rdi
	andq	%rsi, %rdi
	xorq	%r9, %rdi
	movq	%rdi, 176(%rax)
	movq	%rsi, %rdi
	notq	%rdi
	andq	%r11, %rdi
	xorq	%r10, %rdi
	movq	%rdi, 184(%rax)
	notq	%r11
	andq	%r8, %r11
	xorq	%rsi, %r11
	movq	%r11, 192(%rax)
	addq	$2, %rdx
L_keccakf1600_ref1$2:
	cmpq	$23, %rdx
	jb  	L_keccakf1600_ref1$3
	ret
L_keccakf1600$1:
	leaq	glob_data + 0(%rip), %rcx
	movq	%rcx, 8(%rsp)
	leaq	32(%rsp), %rcx
	movq	$0, %r10
	jmp 	L_keccakf1600$2
L_keccakf1600$3:
	movq	%r10, 16(%rsp)
	movq	8(%rsp), %rdx
	movq	(%rdx,%r10,8), %rdx
	movq	%rdx, 24(%rsp)
	movq	(%rax), %r9
	movq	8(%rax), %r8
	movq	16(%rax), %r11
	movq	24(%rax), %rbx
	movq	32(%rax), %rbp
	xorq	40(%rax), %r9
	xorq	48(%rax), %r8
	xorq	56(%rax), %r11
	xorq	64(%rax), %rbx
	xorq	72(%rax), %rbp
	xorq	80(%rax), %r9
	xorq	88(%rax), %r8
	xorq	96(%rax), %r11
	xorq	104(%rax), %rbx
	xorq	112(%rax), %rbp
	xorq	120(%rax), %r9
	xorq	128(%rax), %r8
	xorq	136(%rax), %r11
	xorq	144(%rax), %rbx
	xorq	152(%rax), %rbp
	xorq	160(%rax), %r9
	xorq	168(%rax), %r8
	xorq	176(%rax), %r11
	xorq	184(%rax), %rbx
	xorq	192(%rax), %rbp
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbp, %rdx
	movq	%r11, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%rbx, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbp, %r8
	rolq	$1, %r8
	xorq	%r11, %r8
	rolq	$1, %r9
	xorq	%rbx, %r9
	movq	(%rax), %r11
	xorq	%rdx, %r11
	movq	48(%rax), %rbx
	xorq	%rsi, %rbx
	rolq	$44, %rbx
	movq	96(%rax), %rbp
	xorq	%rdi, %rbp
	rolq	$43, %rbp
	movq	144(%rax), %r12
	xorq	%r8, %r12
	rolq	$21, %r12
	movq	192(%rax), %r13
	xorq	%r9, %r13
	rolq	$14, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	xorq	24(%rsp), %r14
	movq	%r14, (%rcx)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 8(%rcx)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 16(%rcx)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 24(%rcx)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 32(%rcx)
	movq	24(%rax), %r11
	xorq	%r8, %r11
	rolq	$28, %r11
	movq	72(%rax), %rbx
	xorq	%r9, %rbx
	rolq	$20, %rbx
	movq	80(%rax), %rbp
	xorq	%rdx, %rbp
	rolq	$3, %rbp
	movq	128(%rax), %r12
	xorq	%rsi, %r12
	rolq	$45, %r12
	movq	176(%rax), %r13
	xorq	%rdi, %r13
	rolq	$61, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 40(%rcx)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 48(%rcx)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 56(%rcx)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 64(%rcx)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 72(%rcx)
	movq	8(%rax), %r11
	xorq	%rsi, %r11
	rolq	$1, %r11
	movq	56(%rax), %rbx
	xorq	%rdi, %rbx
	rolq	$6, %rbx
	movq	104(%rax), %rbp
	xorq	%r8, %rbp
	rolq	$25, %rbp
	movq	152(%rax), %r12
	xorq	%r9, %r12
	rolq	$8, %r12
	movq	160(%rax), %r13
	xorq	%rdx, %r13
	rolq	$18, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 80(%rcx)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 88(%rcx)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 96(%rcx)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 104(%rcx)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 112(%rcx)
	movq	32(%rax), %r11
	xorq	%r9, %r11
	rolq	$27, %r11
	movq	40(%rax), %rbx
	xorq	%rdx, %rbx
	rolq	$36, %rbx
	movq	88(%rax), %rbp
	xorq	%rsi, %rbp
	rolq	$10, %rbp
	movq	136(%rax), %r12
	xorq	%rdi, %r12
	rolq	$15, %r12
	movq	184(%rax), %r13
	xorq	%r8, %r13
	rolq	$56, %r13
	andnq	%rbp, %rbx, %r14
	xorq	%r11, %r14
	movq	%r14, 120(%rcx)
	andnq	%r12, %rbp, %r14
	xorq	%rbx, %r14
	movq	%r14, 128(%rcx)
	andnq	%r13, %r12, %r14
	xorq	%rbp, %r14
	movq	%r14, 136(%rcx)
	andnq	%r11, %r13, %rbp
	xorq	%r12, %rbp
	movq	%rbp, 144(%rcx)
	andnq	%rbx, %r11, %r11
	xorq	%r13, %r11
	movq	%r11, 152(%rcx)
	movq	16(%rax), %r11
	xorq	%rdi, %r11
	rolq	$62, %r11
	movq	64(%rax), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	112(%rax), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	120(%rax), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	168(%rax), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	andnq	%r8, %rdi, %rsi
	xorq	%r11, %rsi
	movq	%rsi, 160(%rcx)
	andnq	%r9, %r8, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 168(%rcx)
	andnq	%rdx, %r9, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 176(%rcx)
	andnq	%r11, %rdx, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 184(%rcx)
	andnq	%rdi, %r11, %rsi
	xorq	%rdx, %rsi
	movq	%rsi, 192(%rcx)
	movq	8(%rsp), %rdx
	movq	8(%rdx,%r10,8), %rdx
	movq	%rdx, 24(%rsp)
	movq	(%rcx), %r9
	movq	8(%rcx), %r8
	movq	16(%rcx), %r10
	movq	24(%rcx), %r11
	movq	32(%rcx), %rbx
	xorq	40(%rcx), %r9
	xorq	48(%rcx), %r8
	xorq	56(%rcx), %r10
	xorq	64(%rcx), %r11
	xorq	72(%rcx), %rbx
	xorq	80(%rcx), %r9
	xorq	88(%rcx), %r8
	xorq	96(%rcx), %r10
	xorq	104(%rcx), %r11
	xorq	112(%rcx), %rbx
	xorq	120(%rcx), %r9
	xorq	128(%rcx), %r8
	xorq	136(%rcx), %r10
	xorq	144(%rcx), %r11
	xorq	152(%rcx), %rbx
	xorq	160(%rcx), %r9
	xorq	168(%rcx), %r8
	xorq	176(%rcx), %r10
	xorq	184(%rcx), %r11
	xorq	192(%rcx), %rbx
	movq	%r8, %rdx
	rolq	$1, %rdx
	xorq	%rbx, %rdx
	movq	%r10, %rsi
	rolq	$1, %rsi
	xorq	%r9, %rsi
	movq	%r11, %rdi
	rolq	$1, %rdi
	xorq	%r8, %rdi
	movq	%rbx, %r8
	rolq	$1, %r8
	xorq	%r10, %r8
	rolq	$1, %r9
	xorq	%r11, %r9
	movq	(%rcx), %r10
	xorq	%rdx, %r10
	movq	48(%rcx), %r11
	xorq	%rsi, %r11
	rolq	$44, %r11
	movq	96(%rcx), %r12
	xorq	%rdi, %r12
	rolq	$43, %r12
	movq	144(%rcx), %rbx
	xorq	%r8, %rbx
	rolq	$21, %rbx
	movq	192(%rcx), %rbp
	xorq	%r9, %rbp
	rolq	$14, %rbp
	andnq	%r12, %r11, %r13
	xorq	%r10, %r13
	xorq	24(%rsp), %r13
	movq	%r13, (%rax)
	andnq	%rbx, %r12, %r13
	xorq	%r11, %r13
	movq	%r13, 8(%rax)
	andnq	%rbp, %rbx, %r13
	xorq	%r12, %r13
	movq	%r13, 16(%rax)
	andnq	%r10, %rbp, %r12
	xorq	%rbx, %r12
	movq	%r12, 24(%rax)
	andnq	%r11, %r10, %r10
	xorq	%rbp, %r10
	movq	%r10, 32(%rax)
	movq	24(%rcx), %r10
	xorq	%r8, %r10
	rolq	$28, %r10
	movq	72(%rcx), %r11
	xorq	%r9, %r11
	rolq	$20, %r11
	movq	80(%rcx), %r12
	xorq	%rdx, %r12
	rolq	$3, %r12
	movq	128(%rcx), %rbx
	xorq	%rsi, %rbx
	rolq	$45, %rbx
	movq	176(%rcx), %rbp
	xorq	%rdi, %rbp
	rolq	$61, %rbp
	andnq	%r12, %r11, %r13
	xorq	%r10, %r13
	movq	%r13, 40(%rax)
	andnq	%rbx, %r12, %r13
	xorq	%r11, %r13
	movq	%r13, 48(%rax)
	andnq	%rbp, %rbx, %r13
	xorq	%r12, %r13
	movq	%r13, 56(%rax)
	andnq	%r10, %rbp, %r12
	xorq	%rbx, %r12
	movq	%r12, 64(%rax)
	andnq	%r11, %r10, %r10
	xorq	%rbp, %r10
	movq	%r10, 72(%rax)
	movq	8(%rcx), %r10
	xorq	%rsi, %r10
	rolq	$1, %r10
	movq	56(%rcx), %r11
	xorq	%rdi, %r11
	rolq	$6, %r11
	movq	104(%rcx), %r12
	xorq	%r8, %r12
	rolq	$25, %r12
	movq	152(%rcx), %rbx
	xorq	%r9, %rbx
	rolq	$8, %rbx
	movq	160(%rcx), %rbp
	xorq	%rdx, %rbp
	rolq	$18, %rbp
	andnq	%r12, %r11, %r13
	xorq	%r10, %r13
	movq	%r13, 80(%rax)
	andnq	%rbx, %r12, %r13
	xorq	%r11, %r13
	movq	%r13, 88(%rax)
	andnq	%rbp, %rbx, %r13
	xorq	%r12, %r13
	movq	%r13, 96(%rax)
	andnq	%r10, %rbp, %r12
	xorq	%rbx, %r12
	movq	%r12, 104(%rax)
	andnq	%r11, %r10, %r10
	xorq	%rbp, %r10
	movq	%r10, 112(%rax)
	movq	32(%rcx), %r10
	xorq	%r9, %r10
	rolq	$27, %r10
	movq	40(%rcx), %r11
	xorq	%rdx, %r11
	rolq	$36, %r11
	movq	88(%rcx), %r12
	xorq	%rsi, %r12
	rolq	$10, %r12
	movq	136(%rcx), %rbx
	xorq	%rdi, %rbx
	rolq	$15, %rbx
	movq	184(%rcx), %rbp
	xorq	%r8, %rbp
	rolq	$56, %rbp
	andnq	%r12, %r11, %r13
	xorq	%r10, %r13
	movq	%r13, 120(%rax)
	andnq	%rbx, %r12, %r13
	xorq	%r11, %r13
	movq	%r13, 128(%rax)
	andnq	%rbp, %rbx, %r13
	xorq	%r12, %r13
	movq	%r13, 136(%rax)
	andnq	%r10, %rbp, %r12
	xorq	%rbx, %r12
	movq	%r12, 144(%rax)
	andnq	%r11, %r10, %r10
	xorq	%rbp, %r10
	movq	%r10, 152(%rax)
	movq	16(%rcx), %r10
	xorq	%rdi, %r10
	rolq	$62, %r10
	movq	64(%rcx), %rdi
	xorq	%r8, %rdi
	rolq	$55, %rdi
	movq	112(%rcx), %r8
	xorq	%r9, %r8
	rolq	$39, %r8
	movq	120(%rcx), %r9
	xorq	%rdx, %r9
	rolq	$41, %r9
	movq	168(%rcx), %rdx
	xorq	%rsi, %rdx
	rolq	$2, %rdx
	andnq	%r8, %rdi, %rsi
	xorq	%r10, %rsi
	movq	%rsi, 160(%rax)
	andnq	%r9, %r8, %rsi
	xorq	%rdi, %rsi
	movq	%rsi, 168(%rax)
	andnq	%rdx, %r9, %rsi
	xorq	%r8, %rsi
	movq	%rsi, 176(%rax)
	andnq	%r10, %rdx, %rsi
	xorq	%r9, %rsi
	movq	%rsi, 184(%rax)
	andnq	%rdi, %r10, %rsi
	xorq	%rdx, %rsi
	movq	%rsi, 192(%rax)
	movq	16(%rsp), %r10
	addq	$2, %r10
L_keccakf1600$2:
	cmpq	$23, %r10
	jb  	L_keccakf1600$3
	ret
	.data
	.p2align	5
_glob_data:
glob_data:
      .byte 1
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -126
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -118
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -117
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 9
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -118
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -120
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 9
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -117
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -119
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 3
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 2
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 10
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 10
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -127
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte -128
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte -128
      .byte 1
      .byte 0
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte 0
      .byte 8
      .byte -128
      .byte 0
      .byte -128
      .byte 0
      .byte 0
      .byte 0
      .byte -128
