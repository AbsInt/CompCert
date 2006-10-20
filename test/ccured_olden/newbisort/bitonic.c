/* For copyright information, see olden_v1.0/COPYRIGHT */

/* =================== PROGRAM bitonic===================== */
/* UP - 0, DOWN - 1 */

#include "node.h"   /* Node Definition */
#include "proc.h"   /* Procedure Types/Nums */

#define CONST_m1 10000
#define CONST_b 31415821
#define RANGE 100

#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN

#define put(a) chatting("%d",a)
#define puts(a) chatting(a)


int flag=0,foo=0;

#define NewNode(h,v) \
  \
{ \
    h = (HANDLE *) malloc(sizeof(struct node)); \
      h->value = v; \
	h->left = NIL; \
	  h->right = NIL; \
	  };


void InOrder(h)
     HANDLE *h;
{
  HANDLE *l, *r;
  if ((h != NIL))
    {
      l = h->left;
      r = h->right;
      InOrder(l);
      chatting("%d @ 0x%x\n",h->value,h);
      InOrder(r);
    }
}

int mult(int p, int q)
{
	int p1, p0, q1, q0;
	
	p1=p/CONST_m1; p0=p%CONST_m1;
	q1=q/CONST_m1; q0=q%CONST_m1;
	return (((p0*q1+p1*q0) % CONST_m1)*CONST_m1+p0*q0);
}

int skiprand(int seed, int n)
{
#ifdef SS_PLAIN
  for (; n; n--) seed=mult(seed,CONST_b)+1;
#else SS_PLAIN
  for (; n; n--) seed=random(seed);
#endif SS_PLAIN
  return seed;
}

#ifndef SS_PLAIN
int random(int seed)
{
  int tmp;
  tmp = (mult(seed,CONST_b)+1);
  return tmp;
}
#endif SS_PLAIN

HANDLE* RandTree(n,seed,level)
     int n,seed,level;

{
  int next_val,my_name;
  HANDLE *h;
  my_name=foo++;

  if (n > 1)
    {
#ifdef SS_PLAIN
      seed = mult(seed,CONST_b)+1;
#else SS_PLAIN
      seed = random(seed);
#endif SS_PLAIN
      next_val=seed % RANGE;
      NewNode(h,next_val);

      h->left = RandTree((n/2),seed,level+1);
      h->right =  RandTree((n/2),skiprand(seed,(n)+1),level+1);
    }
  else 
    h = NIL;
  return(h);
} 

void SwapVal(l,r)
     HANDLE *l, *r;
{ 
  int temp;
  
  temp = l->value; /* MISS PROBLEM */
  l->value = r->value;
  r->value = temp;
} 

void SwapLeft(l,r)
     HANDLE *l, *r;
{
  HANDLE *h;

  h = r->left;
  r->left = l->left;
  l->left = h;
}

void SwapRight(l,r)
     HANDLE *l, *r;
{  
  HANDLE *h;

  h = r->right;
  r->right = l->right; /* MISS PROBLEM */
  l->right = h;
} 

int Bimerge(root,spr_val,dir)
     HANDLE *root;
     int spr_val,dir;
{ 
  int rightexchange, elementexchange;
  HANDLE *pl, *pr;

  /*chatting("enter bimerge %x\n", root);*/
  rightexchange = ((root->value > spr_val) ^ dir);
  if (rightexchange)
    {
      int temp;
      temp = root->value;
      root->value = spr_val;
      spr_val = temp;
    }
  
  pl = root->left;
  pr = root->right;

  while (pl != NIL)
    {
      elementexchange = ((pl->value > /* MISS PROBLEM */pr->value) ^ dir); 
      if (rightexchange)
	{
	  if (elementexchange)
	    { 
	      SwapVal(pl,pr);
	      SwapRight(pl,pr);
	      pl = pl->left;
	      pr = pr->left;
	    }
	  else 
	    { 
	      pl = pl->right;
	      pr = pr->right;
	    }
	}
      else 
	{
	  if (elementexchange)
	    { 
	      SwapVal(pl,pr);
	      SwapLeft(pl,pr);
	      pl = pl->right;
	      pr = pr->right;
	    }
	  else 
	    { 
	      pl = pl->left;
	      pr = pr->left; /* MISS PROBLEM */
	    }
	}
    }

  if (root->left != NIL)
    { 
      root->value=Bimerge(root->left,root->value,dir);
      spr_val=Bimerge(root->right,spr_val,dir);
    }
  /*chatting("exit bimerge %x\n", root);*/
  return spr_val;
} 

int Bisort(root,spr_val,dir)
     HANDLE *root;
     int spr_val,dir;
{ 
  /*chatting("bisort %x\n", root);*/
  if (root->left == NIL)
    { 
     if ((root->value > spr_val) ^ dir)
        {
	  int val;
	  val = spr_val;
	  spr_val = root->value;
	  root->value =val;
	}
    }
  else 
    {
      /* Bisort both halves of the tree and merge */
      root->value=Bisort(root->left,root->value,dir);
      spr_val=Bisort(root->right,spr_val,!dir);
      spr_val=Bimerge(root,spr_val,dir);
    }
  /*chatting("exit bisort %x\n", root);*/
  return spr_val;
} 

void main(argc,argv)
  int argc;
 char *argv[];


{ 
  HANDLE *h;
  int sval;
  int n;
   
  n = dealwithargs(argc,argv);

  chatting("Bisort with %d size\n", n);
  h = RandTree(n,12345768,0);
#ifdef SS_PLAIN
  sval = (mult(245867,CONST_b)+1) % RANGE;
#else SS_PLAIN
  sval = random(245867) % RANGE;
#endif SS_PLAIN
  if (flag) {
    InOrder(h);
    chatting("%d\n",sval);
   }
  chatting("**************************************\n");
  chatting("BEGINNING BITONIC SORT ALGORITHM HERE\n");
  chatting("**************************************\n");

  chatting("Sorting forward...");
  sval=Bisort(h,sval,0);
  if (flag) {
    chatting("Sorted Tree:\n"); 
    InOrder(h);
    chatting("%d\n",sval);
   }
  chatting("done\n");

  chatting("sorting backward...");
  sval=Bisort(h,sval,1);
  if (flag) {
    chatting("Sorted Tree:\n"); 
    InOrder(h);
    chatting("%d\n",sval);
   }
  chatting("done\n");
  exit(0);
} 

