/* *********************************************************************/
/*                                                                     */
/*              The Compcert verified compiler                         */
/*                                                                     */
/*          Xavier Leroy, INRIA Paris-Rocquencourt                     */
/*                                                                     */
/*  Copyright Institut National de Recherche en Informatique et en     */
/*  Automatique.  All rights reserved.  This file is distributed       */
/*  under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation, either version 2 of the License, or  */
/*  (at your option) any later version.  This file is also distributed */
/*  under the terms of the INRIA Non-Commercial License Agreement.     */
/*                                                                     */
/* *********************************************************************/

/* Thin wrapper around stdio, redefining stdin, stdout and stderr.
   Needed under MacOS X because of linking issues with dynamic libraries. */

#ifndef _COMPCERT_STDIO_H
#define _COMPCERT_STDIO_H

#include "/usr/include/stdio.h"

extern FILE * compcert_stdin(void);
extern FILE * compcert_stdout(void);
extern FILE * compcert_stderr(void);

#undef stdin
#define stdin (compcert_stdin())
#undef stdout
#define stdout (compcert_stdout())
#undef stderr
#define stderr (compcert_stderr())

#endif
