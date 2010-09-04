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

#include "/usr/include/stdio.h"

FILE * compcert_stdin(void)  { return stdin; }
FILE * compcert_stdout(void) { return stdout; }
FILE * compcert_stderr(void) { return stderr; }
