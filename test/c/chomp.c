#include <stdio.h>
#include <stdlib.h>

#define NDATA (int *)malloc(ncol * sizeof(int))
#define NLIST (struct _list *)malloc(sizeof(struct _list))
#define NPLAY (struct _play *)malloc(sizeof(struct _play))

struct _list
{
  int *data;
  struct _list *next;
} *wanted;

struct _play
{
  int value;
  int *state;
  struct _list *first;
  struct _play *next;
} *game_tree;

int nrow,ncol;      /* global so as to avoid passing them all over the place */

int *copy_data(int* data) /* creates a duplicate of a given -data list */
{
  int *new = NDATA;
  int counter = ncol;
  while (counter --)
      new[counter] = data[counter];
  return new;
}

int next_data(int *data)  /* gives the next logical setup to the one passed */
                          /* new setup replaces the old. Returns 0 if no valid */
{                         /* setup exists after the one passed */
  int counter = 0;
  int valid = 0;     /* default to none */
  while ((counter != ncol) && (! valid)) /* until its done */
    {
      if (data[counter] == nrow) /* if we hit a border */
        {
	  data[counter] = 0;     /* reset it to zero     */
	  counter ++;      /* and take next column */
	}
       else
        {
	  data[counter] ++;      /* otherwise, just increment row number */
	  valid = 1;                /* and set valid to true. */
	}
    }
  return valid;                     /* return whether or not */
}                                   /* a next could be found */

void melt_data(int *data1,int *data2) /* melts 2 _data's into the first one. */
{
  int counter = ncol;
  while (counter --)     /* do every column */
    {
      if (data1[counter] > data2[counter]) /* take the lowest one */
          data1[counter] = data2[counter]; /* and put in first _data */
    }
}

int equal_data(int *data1,int *data2) /* check if both _data's are equal */
{
  int counter = ncol;
  while ((counter --) && (data1[counter] == data2[counter]));
  return (counter < 0);
}

int valid_data(int *data) /* checks if the play could ever be achieved. */
{
  int low;      /* var to hold the current height */
  int counter = 0;
  low = nrow;   /* default to top of board */
  while (counter != ncol) /* for every column */
    {
      if (data[counter] > low) break;  /* if you get something higher */
      low = data[counter];             /* set this as current height */
      counter ++;
    }
  return (counter == ncol);
}

void dump_list(struct _list *list) /* same for a _list structure */
{
  if (list != NULL)
    {
      dump_list(list -> next); /* dump the rest of it */
      free(list -> data); /* and its _data structure */
      free(list);
    }
}

void dump_play(struct _play *play) /* and for the entire game tree */
{
  if (play != NULL)
    {
      dump_play(play -> next);  /* dump the rest of the _play */
      dump_list(play -> first); /* its _list */
      free(play -> state); /* and its _data */
      free(play);
    }
}

int get_value(int *data) /* get the value (0 or 1) for a specific _data */
{
  struct _play *search;
  search = game_tree; /* start at the begginig */
  while (! equal_data(search -> state,data)) /* until you find a match */
      search = search -> next; /* take next element */
  return search -> value; /* return its value */
}

void show_data(int *data) /* little display routine to give off results */
{
  int counter = 0;
  while (counter != ncol)
    {
      printf("%d",data[counter ++]);
      if (counter != ncol) putchar(',');
    }
}

void show_move(int *data) /* puts in the "(" and ")" for show_data() */
{
  putchar('(');
  show_data(data);
  printf(")\n");
}

void show_list(struct _list *list) /* show the entire list of moves */
{
  while (list != NULL)
    {
      show_move(list -> data);
      list = list -> next;
    }
}

void show_play(struct _play *play) /* to diplay the whole tree */
{
  while (play != NULL)
    {
      printf("For state :\n");
      show_data(play -> state);
      printf("  value = %d\n",play -> value);
      printf("We get, in order :\n");
      show_list(play -> first);
      play = play -> next;
    }
}

int in_wanted(int *data) /* checks if the current _data is in the wanted list */
{
  struct _list *current;
  current = wanted; /* start at the begginig */
  while (current != NULL) /* unitl the last one */
    {
      if (equal_data(current -> data,data)) break; /* break if found */
      current = current -> next; /* take next element */
    }
  if (current == NULL) return 0; /* if at the end, not found */
  return 1;
}

int *make_data(int row,int col) /* creates a new _data with the correct */
                                /* contents for the specified row & col */
{
  int count;
  int *new = NDATA;
  for (count = 0;count != col;count ++) /* creates col-1 cells with nrow */
      new[count] = nrow;
  for (;count != ncol;count ++) /* and the rest with row as value */
      new[count] = row;
  return new;         /* and return pointer to first element */
}

struct _list *make_list(int *data,int *value,int *all) /* create the whole _list of moves */
                                                          /* for the _data structure data */
{
  int row,col;
  int *temp;
  struct _list *head,*current;
  *value = 1; /* set to not good to give */
  head = NLIST; /* create dummy header */
  head -> next = NULL; /* set NULL as next element */
  current = head;      /* start from here */
  for (row = 0;row != nrow;row ++) /* for every row */
    {
      for (col = 0;col != ncol;col ++) /* for every column */
        {
	  temp = make_data(row,col); /* create _data for this play */
	  melt_data(temp,data);      /* melt it with the current one */
	  if (! equal_data(temp,data)) /* if they are different, it good */
	    {
	      current -> next = NLIST; /* create new element in list */
	      current -> next -> data = copy_data(temp); /* copy data, and place in list */
	      current -> next -> next = NULL; /* NULL the next element */
	      current = current -> next; /* advance pointer */
	      if (*value == 1) /* if still not found a good one */
	          *value = get_value(temp); /* look at this value */
	      if ((! *all) && (*value == 0))
	        {  /* if we found it, and all is not set */
		  col = ncol - 1; /* do what it take sto break out now */
		  row = nrow - 1;
	          if (in_wanted(temp)) /* if in the wanted list */
		      *all = 2; /* flag it */
		}
	    }
	   else /* if its not a valid move */
	    {
	      if (col == 0) row = nrow - 1; /* break out if at first column */
	      col = ncol - 1;               /* but make sure you break out */
	    }                               /* of the col for-loop anyway */
	  free(temp); /* dump this unneeded space */
	}
    }
  current = head -> next; /* skip first element */
  free(head); /* dump it */
  if (current != NULL) *value = 1 - *value; /* invert value if its */
  return current;                           /* not the empty board */
}

struct _play *make_play(int all) /* make up the entire tree-like stuff */
{
  int val;
  int *temp;
  struct _play *head,*current;
  head = NPLAY; /* dummy header again */
  current = head; /* start here */
  game_tree = NULL; /* no elements yet */
  temp = make_data(0,0); /* new data, for empty board */
  temp[0] --;   /* set it up at (-1,xx) so that next_data() returns (0,xx) */
  while (next_data(temp)) /* take next one, and break if none */
    {
      if (valid_data(temp)) /* if board position is possible */
        {
	  current -> next = NPLAY; /* create a new _play cell */
	  if (game_tree == NULL) game_tree = current -> next;
	      /* set up game_tree if it was previously NULL */
	  current -> next -> state = copy_data(temp); /* make a copy of temp */
	  current -> next -> first = make_list(temp,&val,&all);
	      /* make up its whole list of possible moves */
	  current -> next -> value = val; /* place its value */
	  current -> next -> next = NULL; /* no next element */
	  current = current -> next;      /* advance pointer */
	  if (all == 2)                   /* if found flag is on */
	    {
	      free(temp);            /* dump current temp */
	      temp = make_data(nrow,ncol); /* and create one that will break */
	    }
	}
    }
  current = head -> next; /* skip first element */
  free(head);             /* dump it */
  return current;         /* and return pointer to start of list */
}

void make_wanted(int *data) /* makes up the list of positions from the full board */
{
         /* everything here is almost like in the previous function. */
	 /* The reason its here, is that it does not do as much as   */
	 /* the one before, and thus goes faster. Also, it saves the */
	 /* results directly in wanted, which is a global variable.  */

  int row,col;
  int *temp;
  struct _list *head,*current;
  head = NLIST;
  head -> next = NULL;
  current = head;
  for (row = 0;row != nrow;row ++)
    {
      for (col = 0;col != ncol;col ++)
        {
	  temp = make_data(row,col);
	  melt_data(temp,data);
	  if (! equal_data(temp,data))
	    {
	      current -> next = NLIST;
	      current -> next -> data = copy_data(temp);
	      current -> next -> next = NULL;
	      current = current -> next;
	    }
	   else
	    {
	      if (col == 0) row = nrow - 1;
	      col = ncol - 1;
	    }
	  free(temp);
	}
    }
  current = head -> next;
  free(head);
  wanted = current;
}

int *get_good_move(struct _list *list) /* gets the first good move from a _list */
{
  if (list == NULL) return NULL; /* if list is NULL, say so */
      /* until end-of-list or a good one is found */
      /* a good move is one that gives off a zero value */
  while ((list -> next != NULL) && (get_value(list -> data)))
      list = list -> next;
  return copy_data(list -> data); /* return the value */
}

int *get_winning_move(struct _play *play) /* just scans for the first good move */
                                          /* in the last _list of a _play. This */
{                                         /* is the full board */
  int *temp;
  while (play -> next != NULL) play = play -> next; /* go to end of _play */
  temp = get_good_move(play -> first); /* get good move */
  return temp;                         /* return it */
}

struct _list *where(int *data,struct _play *play)
{
  while (! equal_data(play -> state,data)) /* search for given _data */
      play = play -> next;
  return play -> first;  /* return the pointer */
}

void get_real_move(int *data1,int *data2,int *row,int *col) /* returns row & col of the move */
                                                           /* which created data1 from data2 */
{
  *col = 0;
  while (data1[*col] == data2[*col]) /* until there is a change */
      (*col) ++;             /* and increment col number */
  *row = data1[*col];  /* row is given by the content of the structure */
}

int main(void)
{
  int row,col,player;
  int *current,*temp;
  struct _play *tree;


  ncol = 7;
  nrow = 7;
  tree = make_play(1); /* create entire tree structure, not just the */
  player = 0;          /* needed part for first move */
  current = make_data(nrow,ncol); /* start play at full board */
  while (current != NULL)
    {
      temp = get_good_move(where(current,tree)); /* get best move */
      if (temp != NULL)  /* temp = NULL when the poison pill is taken */
        {
          get_real_move(temp,current,&row,&col); /* calculate coordinates */
          /* print it out nicely */
          printf("player %d plays at (%d,%d)\n",player,row,col);
          player = 1 - player; /* next player to do the same */
          free(current);  /* dump for memory management */
        }
      current = temp; /* update board */
    }
  dump_play(tree); /* dump unneeded tree */
  printf("player %d loses\n",1 - player); /* display winning player */
  return 0;
}

/*****************************************************************************/
