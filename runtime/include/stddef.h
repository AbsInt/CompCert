/* This file is part of the Compcert verified compiler.
 *
 * Copyright (c) 2015 Institut National de Recherche en Informatique et
 *  en Automatique.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the <organization> nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
 * HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* <stddef.h> -- common definitions (ISO C99 7.17) */

/* We actually need to define this also if stddef.h is included and __STDDEF_H is
   already defined since the gcc stddef also defines it if __need_wint_t is present
   in any case */
#if defined (__need_wint_t)
#ifndef _WINT_T
#define _WINT_T

#ifndef __WINT_TYPE__
#define __WINT_TYPE__ unsigned int
#endif
typedef __WINT_TYPE__ wint_t;
#endif
#undef __need_wint_t
#endif

#ifndef _STDDEF_H

/* Glibc compatibility: if one of the __need_ macros is set,
   just define the corresponding type or macro
   and don't consider this file as fully included yet. */
#if !defined(__need_size_t) && !defined(__need_ptrdiff_t) && !defined(__need_wchar_t) && !defined(__need_NULL) && !defined(__need_wint_t)
#define _STDDEF_H
#endif

#ifdef __DCC__
#if !defined(__size_t) && !defined(_SIZE_T)
#define	__size_t
#define _SIZE_T
typedef unsigned int size_t;
#endif
#undef __need_size_t
#else
#if defined(_STDDEF_H) || defined(__need_size_t)
#ifndef _SIZE_T
#define _SIZE_T
typedef unsigned long size_t;
#endif
#undef __need_size_t
#endif
#endif

#if defined(_STDDEF_H) || defined(__need_ptrdiff_t)
#ifndef _PTRDIFF_T
#define _PTRDIFF_T
typedef signed long ptrdiff_t;
#endif
#undef __need_ptrdiff_t
#endif

#ifdef __DCC__
#ifndef _WCHART
#define _WCHART
#ifndef	__wchar_t
#define	__wchar_t
#ifdef _TYPE_wchar_t
_TYPE_wchar_t;
#else
typedef unsigned short wchar_t;
#endif
#endif
#undef __need_wchar_t
#endif
#else
#if defined(_STDDEF_H) || defined(__need_wchar_t)
#ifndef _WCHAR_T
#define _WCHAR_T
#ifdef _WIN32
typedef unsigned short wchar_t;
#else
typedef signed int wchar_t;
#endif
#endif
#undef __need_wchar_t
#endif
#endif


#if defined(_STDDEF_H) || defined(__need_NULL)
#ifndef NULL
#define NULL ((void *) 0)
#endif
#undef __need_NULL
#endif

#if defined(_STDDEF_H) && !defined(offsetof)
#define offsetof(ty,member) (__builtin_offsetof(ty,member))
#endif

#ifdef _STDDEF_H
/* Type whose alignment is supported in every context and is at least
   as great as that of any standard type not using alignment
   specifiers. Since we do not support long double per default the type
   with the maximum alignment supported in every context is long long.
*/
typedef long long max_align_t;
#endif

#endif
