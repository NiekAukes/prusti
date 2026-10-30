//@ known-failure
// `old(..)` of a `&mut` argument in a loop invariant fails with an internal
// error ("insufficient permission" in the postcondition), with or without a
// quantifier around it.
use prusti_contracts::*;

fn f(a: &mut [i32; 3]) {
    let mut k = 0;
    while k < 3 {
        body_invariant!(k < 3);
        body_invariant!(forall(|i: usize| i < k ==> a[i] == old(a[i]) + 1));
        body_invariant!(forall(|i: usize| k <= i && i < 3 ==> a[i] == old(a[i])));
        a[k] = a[k] + 1;
        k += 1;
    }
    prusti_assert!(a[0] == old(a[0]) + 1);
}

fn main() {}
