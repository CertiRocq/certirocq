#include <stdio.h>
#include "int63_tinfo.h"

unsigned long long zero_int63() {
  return 1;
}

unsigned long long one_int63() {
  return 3;
} 

extern unsigned long long add_int63(unsigned long long * tf, unsigned long long i1, unsigned long long i2) {

  //more efficient way to do this?
  
  return ((((i1>>1) + (i2>>1))<<1) + 1);

  
  // This might be problematic because of overflow/underflow
  // return (i1 + (i2 - 1);
  // return (i1 + i2 - 1);
}


extern unsigned long long print_int63(unsigned long long * tf, unsigned long long i) {
  printf ("%d", (i>>1));  
}


void print_new_line(unsigned long long u) {
  printf("\n");
}
