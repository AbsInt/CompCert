void quicksort(int lo, int hi, int base[])
{ 
  int i,j;
  int pivot,temp;
    
  if (lo<hi) {
    for (i=lo,j=hi,pivot=base[hi];i<j;) {
      while (i<hi && base[i]<=pivot) i++;
      while (j>lo && base[j]>=pivot) j--;
      if (i<j) { temp=base[i]; base[i]=base[j]; base[j]=temp; }
    }
    temp=base[i]; base[i]=base[hi]; base[hi]=temp;
    quicksort(lo,i-1,base);  quicksort(i+1,hi,base);
  }
}

