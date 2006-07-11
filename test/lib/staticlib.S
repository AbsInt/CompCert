/* Work around MacOX shared-library lossage.
   (No static version of the C library.) */

.macro GLUE
	.text
	.globl	_$0_static
_$0_static:
	addis	r11, 0, ha16(L$0)
	lwz	r11, lo16(L$0)(r11)
	mtctr	r11
	bctr
	.non_lazy_symbol_pointer
L$0:	
	.indirect_symbol _$0
	.long 0
.endmacro

	GLUE cos
	GLUE sin
	GLUE atan2
	GLUE asin
	GLUE sqrt
	GLUE fmod
	GLUE fabs
        GLUE memcpy
        GLUE memset
        