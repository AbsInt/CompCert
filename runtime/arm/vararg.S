@ *****************************************************************
@
@               The Compcert verified compiler
@
@           Xavier Leroy, INRIA Paris-Rocquencourt
@
@ Copyright (c) 2013 Institut National de Recherche en Informatique et
@  en Automatique.
@
@ Redistribution and use in source and binary forms, with or without
@ modification, are permitted provided that the following conditions are met:
@     * Redistributions of source code must retain the above copyright
@       notice, this list of conditions and the following disclaimer.
@     * Redistributions in binary form must reproduce the above copyright
@       notice, this list of conditions and the following disclaimer in the
@       documentation and/or other materials provided with the distribution.
@     * Neither the name of the <organization> nor the
@       names of its contributors may be used to endorse or promote products
@       derived from this software without specific prior written permission.
@
@ THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
@ "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
@ LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
@ A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
@ HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
@ EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
@ PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
@ PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
@ LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
@ NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
@ SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
@
@ *********************************************************************

@ Helper functions for variadic functions <stdarg.h>.  ARM version

#include "sysdeps.h"

@ typedef void * va_list;
@ unsigned int __compcert_va_int32(va_list * ap);
@ unsigned long long __compcert_va_int64(va_list * ap);
@ double __compcert_va_float64(va_list * ap);

FUNCTION(__compcert_va_int32)
	                        @ r0 = ap parameter
        ldr     r1, [r0, #0]    @ r1 = pointer to next argument
        ADD     r1, r1, #4      @ advance ap by 4
        str     r1, [r0, #0]
        ldr     r0, [r1, #-4]    @ load next argument and return it in r0
        bx      lr
ENDFUNCTION(__compcert_va_int32)

FUNCTION(__compcert_va_int64)
	                        @ r0 = ap parameter
        ldr     r1, [r0, #0]    @ r1 = pointer to next argument
        ADD     r1, r1, #15     @ 8-align and advance by 8
        BIC     r1, r1, #7
        str     r1, [r0, #0]    @ update ap
        ldr     r0, [r1, #-8]   @ load next argument and return it in r0,r1
        ldr     r1, [r1, #-4]
        bx      lr
ENDFUNCTION(__compcert_va_int64)

FUNCTION(__compcert_va_float64)
	                        @ r0 = ap parameter
        ldr     r1, [r0, #0]    @ r1 = pointer to next argument
        ADD     r1, r1, #15     @ 8-align and advance by 8
        BIC     r1, r1, #7
        str     r1, [r0, #0]    @ update ap
#ifdef ABI_eabi
        ldr     r0, [r1, #-8]   @ load next argument and return it in r0,r1
        ldr     r1, [r1, #-4]
#else
        vldr    d0, [r1, #-8]   @ load next argument and return it in d0
#endif
        bx      lr
ENDFUNCTION(__compcert_va_float64)

FUNCTION(__compcert_va_composite)
	                        @ r0 = ap parameter
	                        @ r1 = size of the composite, in bytes
        ldr     r2, [r0, #0]    @ r2 = pointer to next argument
	ADD     r3, r2, r1      @ advance by size
        ADD     r3, r3, #3      @ 4-align
        BIC     r3, r3, #3
        str     r3, [r0, #0]    @ update ap
	mov     r0, r2          @ result is pointer to composite in stack
        bx      lr
ENDFUNCTION(__compcert_va_composite)
