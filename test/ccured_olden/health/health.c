/* For copyright information, see olden_v1.0/COPYRIGHT */

/******************************************************************* 
 *  Health.c : Model of the Colombian Health Care System           *
 *******************************************************************/ 
#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "health.h"
#include <assert.h>

struct Village *alloc_tree(int level, int label, struct Village *back) 
{  
  if (level == 0) 
    {
      return NULL;
    }
  else 
    {
      int                  i;
      struct Village       *new;

      new = (struct Village *)malloc(sizeof(struct Village));

      new->back = back;
      new->label = label;
      new->seed = label * (IQ + seed); 
      new->hosp.personnel = (int)pow(2, level - 1);
      new->hosp.free_personnel = new->hosp.personnel;
      new->hosp.num_waiting_patients = 0;
      new->hosp.assess.forward = NULL;
      new->hosp.assess.back = NULL;
      new->hosp.waiting.forward = NULL;
      new->hosp.waiting.back = NULL;
      new->hosp.inside.forward = NULL;
      new->hosp.inside.back = NULL;
      new->returned.back = NULL;
      new->returned.forward = NULL;

      for (i = 0; i < 4; i++)       
	new->forward[i] = 
	  alloc_tree(level - 1, (label * 4) + i + 1, new); 

      return new;
    }
}


struct Results get_results(struct Village *village)
{
  int                    i;
  struct List            *list;
  struct Patient         *p;
  struct Village         *v;
  struct Results         r1;

  r1.total_hosps = 0.0;
  r1.total_patients = 0.0;
  r1.total_time = 0.0;

  if (village == NULL) return r1;

  for (i = 0; i < 4; i++ ) {
    struct Results res;

    v = village->forward[i];
    res = get_results(v); 

    r1.total_hosps += res.total_hosps;
    r1.total_patients += res.total_patients;
    r1.total_time += res.total_time; 
  }

  list = village->returned.forward;
  while (list != NULL) {
    p = list->patient;
    r1.total_hosps += (float)(p->hosps_visited);
    r1.total_time += (float)(p->time); 
    r1.total_patients += 1.0;
    list = list->forward; 
  }
  
  return r1; 
}


void check_patients_inside(struct Village *village, struct List *list) 
{
  struct Patient         *p;
  
  while (list != NULL) 
    {

      p = list->patient;
      p->time_left--;
      
      if (p->time_left == 0) 
	{
	  village->hosp.free_personnel++;
	  removeList(&(village->hosp.inside), p); 
	  addList(&(village->returned), p); 
	}    
      list = list->forward; 
    } 
}


struct List *check_patients_assess(struct Village *village, struct List *list) 
{
  float                 rand;
  struct Patient          *p;
  int                      label;

  while (list != NULL) 
    {
      p = list->patient;
      p->time_left--;
      label = village->label;

      if (p->time_left == 0) 
	{ 
	  rand = my_rand(village->seed);
	  village->seed = (long)(rand * IM);
	  label = village->label;

	  if (rand > 0.1 || label == 0) 
	    {
	      removeList(&(village->hosp.assess), p);
	      addList(&(village->hosp.inside), p);
	      p->time_left = 10;
	      p->time += p->time_left;
	    }
	  else 
	    {
	      village->hosp.free_personnel++;
	      removeList(&(village->hosp.assess), p);
	      addList(&(village->hosp.up), p); 
	    } 
	}
      
      list = list->forward; 
    } 
  return &(village->hosp.up);
}


void check_patients_waiting(struct Village *village, struct List *list) 
{
  int                      i;
  struct Patient           *p;
  
  while (list != NULL) 
    {
      i = village->hosp.free_personnel;
      p = list->patient; /* This is a bad load */

      if (i > 0) 
	{
	  village->hosp.free_personnel--;
	  p->time_left = 3;
	  p->time += p->time_left;
	  removeList(&(village->hosp.waiting), p);
	  addList(&(village->hosp.assess), p); 
	}
      else 
	{
	  p->time++; /* so is this */ 
	}
      list = list->forward; 
    } 
}


void put_in_hosp(struct Hosp *hosp, struct Patient *patient) 
{  
  patient->hosps_visited++;

  if (hosp->free_personnel > 0) 
    {
      hosp->free_personnel--;
      addList(&(hosp->assess), patient); 
      patient->time_left = 3;
      patient->time += patient->time_left;
    } 
  else 
    {
      addList(&(hosp->waiting), patient); 
    }
}


struct Patient *generate_patient(struct Village *village) 
{
  struct Patient *patient = NULL;
  float rand;
  
  rand = my_rand(village->seed);
  village->seed = (long)(rand * IM);

  if (rand > 0.666) 
    {
      patient = (struct Patient *)mymalloc(sizeof(struct Patient));
      patient->hosps_visited = 0;
      patient->time = 0;
      patient->time_left = 0;
      patient->home_village = village; 
    }

  return patient; 
}
    
int
main(int argc, char *argv[]) 
{ 
  struct Results         results;
  struct Village         *top;
  long                   i;
  float                  total_time,
                         total_patients,
                         total_hosps;  
  
  dealwithargs(argc, argv);

  top = alloc_tree(max_level, 0, NULL);
  
  chatting("\n\n    Colombian Health Care Simulator\n\n");
  chatting("Working...\n");
  
  // sm: changed "%d" to "%ld" to silence gcc warning
  fprintf(stderr, "This is max_time right before the loop: %ld\n", max_time);
  for (i = 0; i < max_time; i++) 
    {
      //printf("This is i with each iteration: %d\n", i);
      if ((i % 10) == 0) 
	chatting("iteration %d\n", i);
      sim(top);   
    }
  
  results = get_results(top);
  total_patients = results.total_patients;
  total_time = results.total_time;
  total_hosps = results.total_hosps;

  chatting("Done.\n\n");
  chatting("# of people treated:              %f people\n",
	   total_patients);
  chatting("Average length of stay:           %f time units\n", 
	   total_time / total_patients);
  chatting("Average # of hospitals visited:   %f hospitals\n\n",
	   total_hosps / total_patients);
  return 0;
}


struct List *sim(struct Village *village)
{
  int                    i;
  struct Patient         *patient, *p;
  struct List            *l, *vl, *up;

  if (village == NULL) 
    return NULL;
 
  for (i = 0; i < 4; i++) 
    { 
      l = vl = sim(village->forward[i]);

      if (l != NULL) 
	{
	  l = l->forward;
	  while (l != NULL) 
	    {
	      p = l->patient; 
	      put_in_hosp(&(village->hosp), p);
	      removeList(vl, p);
	      l = l->forward; 
	    } 
	} 
    }
  

  /* Uses lists inside, and return */
  check_patients_inside(village, village->hosp.inside.forward);
  
  /* Uses lists assess, inside, and up */
  up = check_patients_assess(village, village->hosp.assess.forward);

  /* Uses lists waiting, and assess */
  check_patients_waiting(village, village->hosp.waiting.forward);
  
  if ((patient = generate_patient(village)) != NULL) 
    {  
      put_in_hosp(&(village->hosp), patient); 
    }

  return up;
}








