	.data
	.globl	__hash__stringlit_1
__hash__stringlit_1:
	.byte	69
	.byte	114
	.byte	114
	.byte	111
	.byte	114
	.byte	33
	.byte	32
	.byte	109
	.byte	97
	.byte	108
	.byte	108
	.byte	111
	.byte	99
	.byte	32
	.byte	114
	.byte	101
	.byte	116
	.byte	117
	.byte	114
	.byte	110
	.byte	115
	.byte	32
	.byte	110
	.byte	117
	.byte	108
	.byte	108
	.byte	10
	.byte	0
	.data
	.globl	_remaining
_remaining:
	.long	0
	.data
	.globl	_temp
_temp:
	.space	4
	.text
	.align 2
Lchatting$i$stub:
	mflr	r0
	stwu	r1, -56(r1)
	stw	r0, 60(r1)
	addis	r11, 0, ha16(Lchatting$i$ptr)
	lwz	r11, lo16(Lchatting$i$ptr)(r11)
	mtctr	r11
	bctrl
	lwz	r0, 60(r1)
	mtlr	r0
	addi	r1, r1, 56
	blr
	.non_lazy_symbol_pointer
Lchatting$i$ptr:
	.indirect_symbol _chatting
	.long	0
	.text
	.align 2
Lmalloc$stub:
	addis	r11, 0, ha16(Lmalloc$ptr)
	lwz	r11, lo16(Lmalloc$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
Lmalloc$ptr:
	.indirect_symbol _malloc
	.long	0
	.text
	.align 2
LMakeHash$stub:
	addis	r11, 0, ha16(LMakeHash$ptr)
	lwz	r11, lo16(LMakeHash$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
LMakeHash$ptr:
	.indirect_symbol _MakeHash
	.long	0
	.text
	.align 2
LHashLookup$stub:
	addis	r11, 0, ha16(LHashLookup$ptr)
	lwz	r11, lo16(LHashLookup$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
LHashLookup$ptr:
	.indirect_symbol _HashLookup
	.long	0
	.text
	.align 2
LHashInsert$stub:
	addis	r11, 0, ha16(LHashInsert$ptr)
	lwz	r11, lo16(LHashInsert$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
LHashInsert$ptr:
	.indirect_symbol _HashInsert
	.long	0
	.text
	.align 2
LHashDelete$stub:
	addis	r11, 0, ha16(LHashDelete$ptr)
	lwz	r11, lo16(LHashDelete$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
LHashDelete$ptr:
	.indirect_symbol _HashDelete
	.long	0
	.text
	.align 2
Lmemset$stub:
	addis	r11, 0, ha16(Lmemset$ptr)
	lwz	r11, lo16(Lmemset$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
Lmemset$ptr:
	.indirect_symbol _memset
	.long	0
	.text
	.align 2
Llocalmalloc$stub:
	addis	r11, 0, ha16(Llocalmalloc$ptr)
	lwz	r11, lo16(Llocalmalloc$ptr)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
Llocalmalloc$ptr:
	.indirect_symbol _localmalloc
	.long	0
	.text
	.align 2
	.globl Llocalmalloc$stub
Llocalmalloc$stub:
	stwu	r1, -32(r1)
	mflr	r2
	stw	r2, 12(r1)
	stw	r13, 28(r1)
	mr	r13, r3
	addis	r2, 0, ha16(_remaining)
	lwz	r6, lo16(_remaining)(r2)
	cmpw	cr0, r13, r6
	bf	1, L100
	addis	r3, 0, 0
	ori	r3, r3, 32768
	bl	Lmalloc$stub
	addis	r2, 0, ha16(_temp)
	stw	r3, lo16(_temp)(r2)
	addis	r2, 0, ha16(_temp)
	lwz	r3, lo16(_temp)(r2)
	cmplwi	cr0, r3, 0
	bf	2, L101
	addis	r3, 0, hi16(__hash__stringlit_1)
	ori	r3, r3, lo16(__hash__stringlit_1)
	bl	Lchatting$i$stub
L101:
	addis	r8, 0, 0
	ori	r8, r8, 32768
	addis	r2, 0, ha16(_remaining)
	stw	r8, lo16(_remaining)(r2)
L100:
	addis	r2, 0, ha16(_temp)
	lwz	r3, lo16(_temp)(r2)
	add	r4, r3, r13
	addis	r2, 0, ha16(_temp)
	stw	r4, lo16(_temp)(r2)
	addis	r2, 0, ha16(_remaining)
	lwz	r5, lo16(_remaining)(r2)
	subfc	r7, r13, r5
	addis	r2, 0, ha16(_remaining)
	stw	r7, lo16(_remaining)(r2)
	lwz	r13, 28(r1)
	lwz	r2, 12(r1)
	mtlr	r2
	lwz	r1, 0(r1)
	blr
	.text
	.align 2
	.globl LMakeHash$stub
LMakeHash$stub:
	stwu	r1, -48(r1)
	mflr	r2
	stw	r2, 12(r1)
	stw	r13, 36(r1)
	stw	r14, 40(r1)
	stw	r15, 44(r1)
	mr	r14, r3
	mr	r13, r4
	addi	r3, 0, 16
	bl	Llocalmalloc$stub
	mr	r15, r3
	rlwinm	r3, r14, 2, 0xfffffffc
	bl	Llocalmalloc$stub
	stw	r3, 0(r15)
	lwz	r3, 0(r15)
	addi	r4, 0, 0
	rlwinm	r5, r14, 2, 0xfffffffc
	bl	Lmemset$stub
	stw	r13, 4(r15)
	stw	r14, 8(r15)
	addi	r3, 0, 0
	stw	r3, 12(r15)
	mr	r3, r15
	lwz	r13, 36(r1)
	lwz	r14, 40(r1)
	lwz	r15, 44(r1)
	lwz	r2, 12(r1)
	mtlr	r2
	lwz	r1, 0(r1)
	blr
	.text
	.align 2
	.globl LHashLookup$stub
LHashLookup$stub:
	stwu	r1, -48(r1)
	mflr	r2
	stw	r2, 12(r1)
	stw	r13, 28(r1)
	stw	r14, 32(r1)
	mr	r14, r3
	mr	r13, r4
	lwz	r8, 4(r13)
	mr	r0, r8
	mr	r3, r14
	mtctr	r0
	bctrl
	lwz	r4, 0(r13)
	rlwinm	r5, r3, 2, 0xfffffffc
	lwzx	r3, r4, r5
L102:
	cmplwi	cr0, r3, 0
	bt	2, L103
	lwz	r7, 0(r3)
	cmplw	cr0, r7, r14
	bt	2, L104
	addi	r6, 0, 1
	b	L105
L104:
	addi	r6, 0, 0
	b	L105
L103:
	addi	r6, 0, 0
L105:
	cmpwi	cr0, r6, 0
	bt	2, L106
	lwz	r3, 8(r3)
	b	L102
L106:
	cmplwi	cr0, r3, 0
	bt	2, L107
	lwz	r3, 4(r3)
	b	L108
L107:
	addi	r3, 0, 0
L108:
	lwz	r13, 28(r1)
	lwz	r14, 32(r1)
	lwz	r2, 12(r1)
	mtlr	r2
	lwz	r1, 0(r1)
	blr
	.text
	.align 2
	.globl LHashInsert$stub
LHashInsert$stub:
	stwu	r1, -48(r1)
	mflr	r2
	stw	r2, 12(r1)
	stw	r13, 28(r1)
	stw	r14, 32(r1)
	stw	r15, 36(r1)
	stw	r16, 40(r1)
	mr	r14, r3
	mr	r13, r4
	mr	r16, r5
	lwz	r6, 4(r16)
	mr	r0, r6
	mr	r3, r13
	mtctr	r0
	bctrl
	mr	r15, r3
	addi	r3, 0, 16
	bl	Llocalmalloc$stub
	lwz	r7, 0(r16)
	rlwinm	r4, r15, 2, 0xfffffffc
	lwzx	r5, r7, r4
	stw	r5, 8(r3)
	lwz	r5, 0(r16)
	stwx	r3, r5, r4
	stw	r13, 0(r3)
	stw	r14, 4(r3)
	# undef r3
	lwz	r13, 28(r1)
	lwz	r14, 32(r1)
	lwz	r15, 36(r1)
	lwz	r16, 40(r1)
	lwz	r2, 12(r1)
	mtlr	r2
	lwz	r1, 0(r1)
	blr
	.text
	.align 2
	.globl LHashDelete$stub
LHashDelete$stub:
	stwu	r1, -48(r1)
	mflr	r2
	stw	r2, 12(r1)
	stw	r13, 28(r1)
	stw	r14, 32(r1)
	mr	r14, r3
	mr	r13, r4
	lwz	r9, 4(r13)
	mr	r0, r9
	mr	r3, r14
	mtctr	r0
	bctrl
	lwz	r4, 0(r13)
	rlwinm	r8, r3, 2, 0xfffffffc
	add	r3, r4, r8
L109:
	lwz	r5, 0(r3)
	cmplwi	cr0, r5, 0
	bt	2, L110
	lwz	r4, 0(r5)
	cmplw	cr0, r4, r14
	bt	2, L111
	addi	r7, 0, 1
	b	L112
L111:
	addi	r7, 0, 0
	b	L112
L110:
	addi	r7, 0, 0
L112:
	cmpwi	cr0, r7, 0
	bt	2, L113
	lwz	r10, 0(r3)
	addi	r3, r10, 8
	b	L109
L113:
	lwz	r4, 0(r3)
	lwz	r6, 8(r4)
	stw	r6, 0(r3)
	# undef r3
	lwz	r13, 28(r1)
	lwz	r14, 32(r1)
	lwz	r2, 12(r1)
	mtlr	r2
	lwz	r1, 0(r1)
	blr
