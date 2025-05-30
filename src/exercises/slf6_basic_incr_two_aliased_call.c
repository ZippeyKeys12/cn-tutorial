#include "slf0_basic_incr.c"


void incr_two (unsigned int *p, unsigned int *q)
/*@ requires take n1 = RW(p);
             ptr_eq(q,p);
    ensures take n2 = RW(p);
            n2 == n1 + 2u32;
@*/
{
  incr(p);
  incr(q);
}



void aliased_call (unsigned int *p)
/*@ requires take n1 = RW(p);
    ensures  take n2 = RW(p);
             n2 == n1 + 2u32;
@*/
{
  incr_two(p, p);
}
