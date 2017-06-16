/* Warning, not error */

#define NULL ((void *) 0)

int t[2] = { NULL, NULL };

/* But this is an error in CompCert */

/* char u = NULL; */
