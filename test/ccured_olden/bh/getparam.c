/****************************************************************************/
/* GETPARAM.C: export version prompts user for values. Public routines:     */
/* initparam(), getparam(), getiparam(), getbparam(), getrparam().          */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

#include "stdinc.h"
#include "real.h"
#include <string.h>
#include <stdlib.h>

void *allocate(int);
void error(string, ...);

local string *defaults = NULL;			/* "name=value" strings     */

/*
 * INITPARAM: ignore arg vector, remember defaults.
 */

void initparam(string *argv, string *defv)
{
    defaults = defv;
}

/*
 * GETPARAM: export version prompts user for value of name.
 */

local int scanbind(string *, string);
local string extrvalue(string);

string getparam(string name)
{
    int i, len;
    string def;
    char buf[128];

    if (defaults == NULL)			/* check initialization     */
	error("getparam: called before initparam\n");
    i = scanbind(defaults, name);		/* find name in defaults    */
    if (i < 0)
	error("getparam: %s unknown\n", name);
    def = extrvalue(defaults[i]);		/* extract default value    */
    if (*def == NULLCHR)
	fprintf(stderr, "enter %s: ", name);	/* prompt user for value    */
    else
	fprintf(stderr, "enter %s [%s]: ", name, def);
    gets(buf);					/* read users response      */
    len = strlen(buf);
    if (len > 0)				/* if user gave a value...  */
	return (strcpy((string) allocate(len+1), buf));
    else					/* else return default      */
	return (def);
}

/*
 * GETIPARAM, ..., GETDPARAM: get int, long, bool, or double parameters.
 */

int getiparam(string name)
{
    string val;

    for (val = ""; *val == NULLCHR; )		/* while nothing input      */
	val = getparam(name);                   /*   obtain value from user */
    return (atoi(val));                         /* convert to an integer    */
}

bool getbparam(string name)
{
    string val;

    for (val = ""; *val == NULLCHR; )
	val = getparam(name);
    if (strchr("tTyY1", *val) != NULLCHR)		/* is value true? */
        return (TRUE);
    if (strchr("fFnN0", *val) != NULLCHR)		/* is value false? */
        return (FALSE);
    error("getbparam: %s=%s not bool\n", name, val);
    return (FALSE);
}

real getrparam(string name)
{
    string val;

    for (val = ""; *val == NULLCHR; )
	val = getparam(name);
    return ((real) atof(val));			/* convert & return real    */
}

/*
 * SCANBIND: scan binding vector for name, return index.
 */

local bool matchname(string, string);

local int scanbind(string bvec[], string name)
{
    int i;

    for (i = 0; bvec[i] != NULL; i++)
	if (matchname(bvec[i], name))
	    return (i);
    return (-1);
}

/*
 * MATCHNAME: determine if "name=value" matches "name".
 */

local bool matchname(string bind, string name)
{
    char *bp, *np;

    bp = bind;
    np = name;
    while (*bp == *np) {
	bp++;
	np++;
    }
    return (*bp == '=' && *np == NULLCHR);
}

/*
 * EXTRVALUE: extract value from name=value string.
 */

local string extrvalue(string arg)
{
    char *ap;

    ap = (char *) arg;
    while (*ap != NULLCHR)
	if (*ap++ == '=')
	    return ((string) ap);
    return (NULL);
}

