/* Resizable arrays */

struct array {
  int size;                     /* Number of elements in the array */
  int capacity;                 /* Max number of elements before resizing */
  void * data;                  /* Actual data -- variable sized */
};

struct array * alloc_array(int eltsize, int initialsize);

void grow_array(int eltsize, struct array * arr);

struct array * copy_array(int eltsize, struct array * arr, int extrasize);

#define new_array(ty,sz) alloc_array(sizeof(ty), sz)

#define data_array(ty,arr) ((ty *) (arr)->data)

#define get_array(ty,arr,idx) (data_array(ty,arr)[idx])

#define get_array_large(dst,ty,arr,idx) \
  ASSIGN(dst, data_array(ty,arr)[idx])

#define set_array(ty,arr,idx,newval) (data_array(ty,arr)[idx] = (newval))

#define set_array_large(ty,arr,idx,newval) \
  ASSIGN(data_array(ty,arr)[idx], newval)

#define extend_array(ty,arr) \
  if ((arr)->size >= (arr)->capacity) grow_array(sizeof(ty), (arr)); \
  (arr)->size++
