	.text
	.align 2
Latoi$i$stub:
	mflr	r0
	stwu	r1, -56(r1)
	stw	r0, 60(r1)
	addis	r11, 0, ha16(Latoi$i$ptr)
	lwz	r11, lo16(Latoi$i$ptr)(r11)
	mtctr	r11
	bctrl
	lwz	r0, 60(r1)
	mtlr	r0
	addi	r1, r1, 56
	blr
	.non_lazy_symbol_pointer
Latoi$i$ptr:
	.indirect_symbol _atoi
	.long	0
	.text
	.align 2
	.globl _dealwithargs
_dealwithargs:
	stwu	r1, -32(r1)
	mflr	r2
	stw	r2, 12(r1)
	cmpwi	cr0, r3, 1
	bt	1, L100
	addi	r3, 0, 1024
	b	L101
L100:
	lwz	r3, 4(r4)
	bl	Latoi$i$stub
L101:
	lwz	r2, 12(r1)
	mtlr	r2
	lwz	r1, 0(r1)
	blr
