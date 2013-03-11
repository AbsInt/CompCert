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

#include <caml/mlvalues.h>
#include <caml/alloc.h>

value cparser_int64_unsigned_div(value v1, value v2)
{
  return caml_copy_int64((uint64) Int64_val(v1) / (uint64) Int64_val(v2));
}

value cparser_int64_unsigned_mod(value v1, value v2)
{
  return caml_copy_int64((uint64) Int64_val(v1) % (uint64) Int64_val(v2));
}

value cparser_int64_unsigned_compare(value v1, value v2)
{
  uint64 n1 = (uint64) Int64_val(v1);
  uint64 n2 = (uint64) Int64_val(v2);
  if (n1 < n2) return Val_int(-1);
  if (n1 > n2) return Val_int(1);
  return Val_int(0);
}

