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

#include <stdarg.h>
#include <stdlib.h>
#define _INSIDE_COMPCERT_COMPATIBILITY_LIBRARY
#include "stdio.h"

static compcert_FILE * compcert_alloc_file(FILE * f)
{
  struct compcert_FILE_ * r;
  r = malloc(sizeof(struct compcert_FILE_));
  if (r == NULL) return NULL;
  r->fstr = (void *) f;
  return r;
}

compcert_FILE * compcert_stdin;
compcert_FILE * compcert_stdout;
compcert_FILE * compcert_stderr;

static __attribute__((constructor)) void compcert_stdio_init(void)
{
  compcert_stdin = compcert_alloc_file(stdin);
  compcert_stdout = compcert_alloc_file(stdout);
  compcert_stderr = compcert_alloc_file(stderr);
}

void compcert_clearerr(compcert_FILE * f)
{
  clearerr((FILE *)(f->fstr));
}

int compcert_fclose(compcert_FILE * f)
{
  int errcode = fclose((FILE *)(f->fstr));
  free(f);
  return errcode;
}

int compcert_feof(compcert_FILE * f)
{
  return feof((FILE *)(f->fstr));
}

int compcert_ferror(compcert_FILE * f)
{
  return ferror((FILE *)(f->fstr));
}

int compcert_fflush(compcert_FILE * f)
{
  return fflush((FILE *)(f->fstr));
}

int compcert_fgetc(compcert_FILE * f)
{
  return fgetc((FILE *)(f->fstr));
}

char *compcert_fgets(char * s, int n, compcert_FILE * f)
{
  return fgets(s, n, (FILE *)(f->fstr));
}

compcert_FILE *compcert_fopen(const char * p, const char * m)
{
  FILE * f = fopen(p, m);
  if (f == NULL) return NULL;
  return compcert_alloc_file(f);
}

int compcert_fprintf(compcert_FILE * f, const char * s, ...)
{
  va_list ap;
  int retcode;
  va_start(ap, s);
  retcode = vfprintf((FILE *)(f->fstr), s, ap);
  va_end(ap);
  return retcode;
}

int compcert_fputc(int c, compcert_FILE * f)
{
  return fputc(c, (FILE *)(f->fstr));
}

int compcert_fputs(const char * s, compcert_FILE * f)
{
  return fputs(s, (FILE *)(f->fstr));
}

size_t compcert_fread(void * s, size_t p, size_t q, compcert_FILE * f)
{
  return fread(s, p, q, (FILE *)(f->fstr));
}

compcert_FILE *compcert_freopen(const char * s, const char * m,
                                compcert_FILE * f)
{
  FILE * nf = freopen(s, m, (FILE *)(f->fstr));
  if (nf == NULL) return NULL;
  f->fstr = nf;
  return f;
}

int compcert_fscanf(compcert_FILE * f, const char * s, ...)
{
  va_list ap;
  int retcode;
  va_start(ap, s);
  retcode = vfscanf((FILE *)(f->fstr), s, ap);
  va_end(ap);
  return retcode;
}

int compcert_fseek(compcert_FILE * f, long p, int q)
{
  return fseek((FILE *)(f->fstr), p, q);
}

long compcert_ftell(compcert_FILE *f)
{
  return ftell((FILE *)(f->fstr));
}

size_t compcert_fwrite(const void * b, size_t p, size_t q, compcert_FILE * f)
{
  return fwrite(b, p, q, (FILE *)(f->fstr));
}

int compcert_getc(compcert_FILE * f)
{
  return getc((FILE *)(f->fstr));
}

int compcert_putc(int c , compcert_FILE * f)
{
  return putc(c, (FILE *)(f->fstr));
}

void compcert_rewind(compcert_FILE * f)
{
  rewind((FILE *)(f->fstr));
}

int compcert_ungetc(int c, compcert_FILE * f)
{
  return ungetc(c, (FILE *)(f->fstr));
}
