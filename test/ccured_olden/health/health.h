/* For copyright information, see olden_v1.0/COPYRIGHT */

/****************************************************************
 * health.h: header file for health.c                           *
 *************************************************************** */


#ifndef _HEALTH
#define _HEALTH

#include <stdio.h>
#include <stdlib.h>

#define IA 16807
#define IM 2147483647
#define AM (1.0 / IM)
#define IQ 127773
#define IR 2836
#define MASK 123459876

int                      max_level;
long                     max_time,
                         seed;

struct Results {
  float                  total_patients;
  float                  total_time;
  float                  total_hosps; };  

struct Patient {
  int                    hosps_visited;
  int                    time;
  int                    time_left;
  struct Village         *home_village; };

struct List {
  struct Patient         *patient;
  struct List            *back;
  struct List            *forward; };

struct Hosp {
  int                    personnel; 
  int                    free_personnel; 
  int                    num_waiting_patients; 
  struct List            waiting; 
  struct List            assess; 
  struct List            inside;
  struct List    up; };
  
struct Village {
  struct Village         *forward[4],
                         *back;
  struct List            returned;
  struct Hosp            hosp;   
  int                    label;
  long                   seed; };

void dealwithargs(int argc, char *argv[]);
float my_rand(long idum);
struct Patient *generate_patient(struct Village *village);
void put_in_hosp(struct Hosp *hosp, struct Patient *patient);
void addList(struct List *list, struct Patient *patient);
void removeList(struct List *list, struct Patient *patient);
struct List *sim(struct Village *village);
void check_patients_inside(struct Village *village, struct List *list);
struct List *check_patients_assess(struct Village *village, struct List *list);
void check_patients_waiting(struct Village *village, struct List *list);
float get_num_people(struct Village *village);
float get_total_time(struct Village *village);
float get_total_hosps(struct Village *village);
struct Results get_results(struct Village *village);

#endif



