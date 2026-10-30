// `old(..)` inside a quantifier's closure reads the pre-state of the captured
// places, so each of these postconditions is false.
use prusti_contracts::*;

#[ensures(forall(|i: usize| old(*a) == *a))] //~ERROR: postcondition might not hold
fn int(a: &mut i32) {
    *a = 5;
}

#[ensures(forall(|i: usize| old(*a) == *a))] //~ERROR: postcondition might not hold
fn uint(a: &mut u8) {
    *a = 5;
}

#[ensures(forall(|i: usize| old(a.0) == a.0))] //~ERROR: postcondition might not hold
fn tuple_field(a: &mut (i32, i32)) {
    a.0 = 5;
}

#[ensures(forall(|i: usize| old(**a) == **a))] //~ERROR: postcondition might not hold
fn boxed(a: &mut Box<i32>) {
    **a = 5;
}

#[ensures(forall(|i: usize| old(a[0]) == a[0]))] //~ERROR: postcondition might not hold
fn array_index(a: &mut [i32; 2]) {
    a[0] = 5;
}

#[ensures(exists(|i: usize| old(*a) != *a) ==> false)] //~ERROR: postcondition might not hold
fn exists_(a: &mut i32) {
    *a = 5;
}

#[pure]
fn p(x: i32, y: i32) -> bool {
    x == y
}

#[ensures(forall(|i: usize| p(old(*a), *a)))] //~ERROR: postcondition might not hold
fn pure_fn(a: &mut i32) {
    *a = 5;
}

#[ensures(forall(|i: usize| forall(|j: usize| *a == old(*a))))] //~ERROR: postcondition might not hold
fn nested(a: &mut i32) {
    *a += 1;
}

// `old` around the whole quantifier reads the pre-state throughout.
#[requires(*a == 1)]
#[ensures(old(forall(|i: usize| *a == 2)))] //~ERROR: postcondition might not hold
fn old_around(a: &mut i32) {
    *a = 2;
}

fn main() {}
