	.file	"test.bc"
	.text
	.globl	main
	.align	16, 0x90
	.type	main,@function
main:                                   # @main
.Leh_func_begin0:
# BB#0:
	movl	$1, sp(%rip)
	movl	$100, -4(%rsp)
	leaq	-4(%rsp), %rax
	movq	%rax, stack(%rip)
	movl	$200, -8(%rsp)
	leaq	-8(%rsp), %rax
	movq	%rax, stack+8(%rip)
	movslq	sp(%rip), %rax
	movq	stack(,%rax,8), %rax
	movl	(%rax), %eax
	ret
.Ltmp0:
	.size	main, .Ltmp0-main
.Leh_func_end0:

	.type	s,@object               # @s
	.section	.rodata,"a",@progbits
s:
	.asciz	 "%lld\n"
	.size	s, 6

	.type	stack,@object           # @stack
	.data
	.globl	stack
	.align	16
stack:
	.zero	8000
	.size	stack, 8000

	.type	sp,@object              # @sp
	.globl	sp
	.align	4
sp:
	.zero	4
	.size	sp, 4

	.section	.eh_frame,"a",@progbits
.LEH_frame0:
.Lsection_eh_frame0:
.Leh_frame_common0:
.Lset0 = .Leh_frame_common_end0-.Leh_frame_common_begin0 # Length of Common Information Entry
	.long	.Lset0
.Leh_frame_common_begin0:
	.long	0                       # CIE Identifier Tag
	.byte	1                       # DW_CIE_VERSION
	.asciz	 "zR"                   # CIE Augmentation
	.byte	1                       # CIE Code Alignment Factor
	.byte	120                     # CIE Data Alignment Factor
	.byte	16                      # CIE Return Address Column
	.byte	1                       # Augmentation Size
	.byte	3                       # FDE Encoding = udata4
	.byte	12                      # DW_CFA_def_cfa
	.byte	7                       # Register
	.byte	8                       # Offset
	.byte	144                     # DW_CFA_offset + Reg (16)
	.byte	1                       # Offset
	.align	8
.Leh_frame_common_end0:
.Lmain.eh = 0


	.section	".note.GNU-stack","",@progbits
