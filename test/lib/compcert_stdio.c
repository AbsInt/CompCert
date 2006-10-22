#include <stdarg.h>
#define INSIDE_COMPCERT_COMPATIBILITY_LIBRARY
#include "compcert_stdio.h"

compcert_FILE * compcert_stdin = (compcert_FILE *) stdin;
compcert_FILE * compcert_stdout = (compcert_FILE *) stdout;
compcert_FILE * compcert_stderr = (compcert_FILE *) stderr;

void	 compcert_clearerr(compcert_FILE * f)
{
  clearerr((FILE *) f);
}

int	 compcert_fclose(compcert_FILE * f)
{
  return fclose((FILE *) f);
}

int	 compcert_feof(compcert_FILE * f)
{
  return feof((FILE *) f);
}

int	 compcert_ferror(compcert_FILE * f)
{
  return ferror((FILE *) f);
}

int	 compcert_fflush(compcert_FILE * f)
{
  return fflush((FILE *) f);
}

int	 compcert_fgetc(compcert_FILE * f)
{
  return fgetc((FILE *) f);
}

char	*compcert_fgets(char * s, int n, compcert_FILE * f)
{
  return fgets(s, n, (FILE *) f);
}

compcert_FILE	*compcert_fopen(const char * p, const char * m)
{
  return (compcert_FILE *) fopen(p, m);
}

int	 compcert_fprintf(compcert_FILE * f, const char * s, ...)
{
  va_list ap;
  int retcode;
  va_start(ap, s);
  retcode = vfprintf((FILE *) f, s, ap);
  va_end(ap);
  return retcode;
}

int	 compcert_fputc(int c, compcert_FILE * f)
{
  return fputc(c, (FILE *) f);
}

int	 compcert_fputs(const char * s, compcert_FILE * f)
{
  return fputs(s, (FILE *) f);
}

size_t	 compcert_fread(void * s, size_t p, size_t q, compcert_FILE * f)
{
  return fread(s, p, q, (FILE *) f);
}

compcert_FILE	*compcert_freopen(const char * s, const char * m,
                                  compcert_FILE * f)
{
  return (compcert_FILE *) freopen(s, m, (FILE *) f);
}

int	 compcert_fscanf(compcert_FILE * f, const char * s, ...)
{
  va_list ap;
  int retcode;
  va_start(ap, s);
  retcode = vfscanf((FILE *) f, s, ap);
  va_end(ap);
  return retcode;
}

int	 compcert_fseek(compcert_FILE * f, long p, int q)
{
  return fseek((FILE *) f, p, q);
}

long	 compcert_ftell(compcert_FILE *f)
{
  return ftell((FILE *) f);
}

size_t	 compcert_fwrite(const void * b, size_t p, size_t q, compcert_FILE * f)
{
  return fwrite(b, p, q, (FILE *) f);
}

int	 compcert_getc(compcert_FILE * f)
{
  return getc((FILE *) f);
}

int	 compcert_putc(int c , compcert_FILE * f)
{
  return putc(c, (FILE *) f);
}

void	 compcert_rewind(compcert_FILE * f)
{
  rewind((FILE *) f);
}

int	 compcert_ungetc(int c, compcert_FILE * f)
{
  return ungetc(c, (FILE *) f);
}

int	 compcert_vfprintf(compcert_FILE * f, const char * s, va_list va)
{
  return vfprintf((FILE *) f, s, va);
}
