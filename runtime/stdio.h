#ifndef _COMPCERT_STDIO_H
#define _COMPCERT_STDIO_H

#include "/usr/include/stdio.h"

typedef struct compcert_FILE_ { void * fstr; } compcert_FILE;

extern compcert_FILE * compcert_stdin;
extern compcert_FILE * compcert_stdout;
extern compcert_FILE * compcert_stderr;
extern void	 compcert_clearerr(compcert_FILE *);
extern int	 compcert_fclose(compcert_FILE *);
extern int	 compcert_feof(compcert_FILE *);
extern int	 compcert_ferror(compcert_FILE *);
extern int	 compcert_fflush(compcert_FILE *);
extern int	 compcert_fgetc(compcert_FILE *);
extern char	*compcert_fgets(char * , int, compcert_FILE *);
extern compcert_FILE	*compcert_fopen(const char * , const char * );
extern int	 compcert_fprintf(compcert_FILE * , const char * , ...);
extern int	 compcert_fputc(int, compcert_FILE *);
extern int	 compcert_fputs(const char * , compcert_FILE * );
extern size_t	 compcert_fread(void * , size_t, size_t, compcert_FILE * );
extern compcert_FILE	*compcert_freopen(const char * , const char * ,
                                          compcert_FILE * );
extern int	 compcert_fscanf(compcert_FILE * , const char * , ...);
extern int	 compcert_fseek(compcert_FILE *, long, int);
extern long	 compcert_ftell(compcert_FILE *);
extern size_t	 compcert_fwrite(const void * , size_t, size_t, compcert_FILE * );
extern int	 compcert_getc(compcert_FILE *);
extern int	 compcert_putc(int, compcert_FILE *);
extern void	 compcert_rewind(compcert_FILE *);
extern int	 compcert_ungetc(int, compcert_FILE *);
extern int	 compcert_vfprintf(compcert_FILE *, const char *, va_list);

#ifndef _INSIDE_COMPCERT_COMPATIBILITY_LIBRARY
#define FILE compcert_FILE
#undef stdin
#define stdin compcert_stdin
#undef stdout
#define stdout compcert_stdout
#undef stderr
#define stderr compcert_stderr
#define clearerr compcert_clearerr
#define fclose compcert_fclose
#define feof compcert_feof
#define ferror compcert_ferror
#define fflush compcert_fflush
#define fgetc compcert_fgetc
#define fgets compcert_fgets
#define fopen compcert_fopen
#define fprintf compcert_fprintf
#define fputc compcert_fputc
#define fputs compcert_fputs
#define fread compcert_fread
#define freopen compcert_freopen
#define fscanf compcert_fscanf
#define fseek compcert_fseek
#define ftell compcert_ftell
#define fwrite compcert_fwrite
#define getc compcert_getc
#define putc compcert_putc
#define rewind compcert_rewind
#define ungetc compcert_ungetc
#define vfprintf compcert_vfprintf
#endif

#endif
