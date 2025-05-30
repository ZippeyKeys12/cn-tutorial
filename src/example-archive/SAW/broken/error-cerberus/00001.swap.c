// Tags: main, for, stdio
/** Source: SAW Exercises
 */

/*

include "../../../common/helpers.saw";
import "Swap.cry";
swapmod <- llvm_load_module "swap.bc";

let swap_diff_spec = do {
    // NOTE: Could use ptr_to_fresh instead
    x <- llvm_fresh_var "x" (llvm_int 32);
    xp <- llvm_alloc (llvm_int 32);
    llvm_points_to xp (llvm_term x);

    y <- llvm_fresh_var "y" (llvm_int 32);
    yp <- llvm_alloc (llvm_int 32);
    llvm_points_to yp (llvm_term y);

    llvm_execute_func [xp, yp];

    llvm_points_to yp (llvm_term x);
    llvm_points_to xp (llvm_term y);
};

// Verify swap
swap_diff_ov <- llvm_verify swapmod "swap" [] true swap_diff_spec z3;

let swap_same_spec = do {
    (x, x_ptr) <- ptr_to_fresh "x" (llvm_int 32);

    llvm_execute_func [x_ptr, x_ptr];

    llvm_points_to x_ptr (llvm_term x);
};

swap_same_ov <- llvm_verify swapmod "swap" [] true swap_same_spec z3;

// Verify xor_swap
llvm_verify swapmod "xor_swap" [] true swap_diff_spec z3;

let selection_sort_spec len = do {
    (a, a_ptr) <- ptr_to_fresh "a" (llvm_array len (llvm_int 32));

    llvm_execute_func [a_ptr, (llvm_term {{ `len : [64]}})];

    llvm_points_to a_ptr (llvm_term {{ selection_sort a }});
};

let a_len = 4;

// Play with the `len` paramter for this exercise.  At len=4 it solves quickly.
// At len=8, the term has blown up.  Will it solve at all?
llvm_verify swapmod "selection_sort" [swap_diff_ov, swap_same_ov] true (selection_sort_spec a_len) (do {
    //simplify (cryptol_ss());
    //print_goal;
    z3;
});

// Now we crank a_len up and show the original proof blow up.  How can we fix
// it?
let a_len = 8;

let argmin_spec len = do {
    // NOTE: Need to be careful to use "ptr_to_fresh_readonly" here.  I
    // originally made the mistake of making this a "ptr_to_fresh", which
    // broke the input to swap afterwards by effectively wiping the array.
    (a, a_ptr) <- ptr_to_fresh_readonly "a" (llvm_array len (llvm_int 32));

    llvm_execute_func [a_ptr, (llvm_term {{ `len : [64]}})];

    llvm_return (llvm_term {{ argmin a }});
};

// NOTE: Another mistake I made was to use the override below.
// This works for size a_len, but on the second time through the loop the override
// doesn't match because the size of the ./headers.has changed!  Ultimately need a
// loop here.

{-/
argmin_ov <- llvm_verify swapmod "argmin" [] true (argmin_spec a_len) (do {
    print_goal;
    z3;
});
/-}

argmin_ovs <- for (eval_list {{ [1..a_len] : [a_len][64]}}) (\len ->
    llvm_verify swapmod "argmin" [] true (argmin_spec (eval_int len)) z3
);

// NOTE: The reason we created a swap_array function was to get "swap_list" in
// our goal and reduce the number of ITEs, which in turn will help the solver
let swap_array_spec len = do {
    (a, a_ptr) <- ptr_to_fresh "a" (llvm_array len (llvm_int 32));

    i <- llvm_fresh_var "i" (llvm_int 64);
    j <- llvm_fresh_var "j" (llvm_int 64);

    llvm_precond {{ i < `len }};
    llvm_precond {{ j < `len }};

    llvm_execute_func [ a_ptr, llvm_term i, llvm_term j ];

    llvm_points_to a_ptr (llvm_term {{ swap_list a i j }});
};

swap_array_ov <- llvm_verify swapmod "swap_array"
    [swap_diff_ov, swap_same_ov]
    true
    (swap_array_spec a_len)
    (w4_unint_z3 []);

sort_ov <- llvm_verify swapmod "selection_sort_composed"
    (concat [swap_diff_ov, swap_same_ov, swap_array_ov] argmin_ovs)
    true
    (selection_sort_spec a_len)
    (do {
        //unfolding ["selection_sort"];
        //simplify (cryptol_ss());
        //print_goal;
        w4_unint_z3 [];
});

llvm_verify swapmod "wacky_sort"
    (concat argmin_ovs [sort_ov, swap_array_ov])
    true
    (selection_sort_spec a_len)
    (do {
        //simplify (cryptol_ss());
        //print_goal;
        w4_unint_z3 ["selection_sort"];
});
  
*/


#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

void swap(uint32_t *x, uint32_t *y)
/*@ requires take xv0 = RW<uint32_t>(x);
             take yv0 = RW<uint32_t>(y); 
    ensures  take xv1 = RW<uint32_t>(x);
             take yv1 = RW<uint32_t>(y);
	     xv1 == yv0;
	     yv1 == xv0; 
@*/
{
    uint32_t tmp = *x;
    *x = *y;
    *y = tmp;
}

void xor_swap(uint32_t *x, uint32_t *y)
/*@ requires take xv0 = RW<uint32_t>(x);
             take yv0 = RW<uint32_t>(y); 
    ensures  take xv1 = RW<uint32_t>(x);
             take yv1 = RW<uint32_t>(y);
	     xv1 == yv0;
	     yv1 == xv0; 
@*/
{
    *x ^= *y;
    *y ^= *x;
    *x ^= *y;
}

// selection sort
void selection_sort(uint32_t *a, size_t len)
/*@ requires take av0 = each(size_t  j; 0u64 <= j && j < len) { RW<int>(array_shift<int>(a,j)) }; 
    ensures  take av1 = each(size_t  j; 0u64 <= j && j < len) { RW<int>(array_shift<int>(a,j)) }; 
@*/
{
    for (size_t i = 0; i < len - 1; ++i)
      /*@ inv take avl = each(u64 k; 0u64 <= k && k < i) { RW<int>(array_shift<int>(a,k)) };
	      take avr = each(u64 k; i <= k && k < len) { RW<int>(array_shift<int>(a,k)) } ;
	      {a} unchanged; {len} unchanged;
	      i <= len; 
      @*/
      {
        size_t j_min = i;
        for (size_t j = i; j < len; ++j)
	  /*@ inv take avl = each(u64 k; 0u64 <= k && k < i) { RW<int>(array_shift<int>(a,k)) };
	          take avr = each(u64 k; i <= k && k < j)    { RW<int>(array_shift<int>(a,k)) };
		  take avr = each(u64 k; j <= k && k < len) { RW<int>(array_shift<int>(a,k)) };
		  {a} unchanged; {len} unchanged;
		  j <= len; 
		  @*/
	  {
            if (a[j] < a[j_min]) {
                j_min = j;
            }
        }
        swap(a+i, a+j_min);
    }
}


int main() {
    for (int i = 1; i <= 5; i++) {
        printf("%d\n", i);
    }
    return 0;
}
