int (*pf)(void);
int f(void) {

   pf = &f; // This looks ok
   pf = ***f; // Dereference a function?
   pf(); // Invoke a function pointer?     
   (****pf)();  // Looks strange but Ok
   (***************f)(); // Also Ok             
   return 0;
}
