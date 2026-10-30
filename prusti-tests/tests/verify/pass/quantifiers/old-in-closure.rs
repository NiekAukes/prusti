// `old(..)` inside a quantifier's closure reads the pre-state of the captured
// places, while the other captures read the post-state.
use prusti_contracts::*;

#[ensures(forall(|i: usize| *a == old(*a) + 1))]
fn int(a: &mut i32) {
    *a += 1
}

#[ensures(forall(|i: usize| a.1 == old(a.1) && a.0 == 5))]
fn tuple_field(a: &mut (i32, i32)) {
    a.0 = 5;
}

#[ensures(forall(|i: usize| i < 2 ==> a[i] == old(a[i])))]
fn array_unchanged(a: &mut [i32; 2]) {}

#[ensures(exists(|i: usize| old(**a) == **a))]
fn boxed_unchanged(a: &mut Box<i32>) {}

#[ensures(forall(|i: usize| forall(|j: usize| *a == old(*a) + 1)))]
fn nested(a: &mut i32) {
    *a += 1
}

// `old` around the whole quantifier reads the pre-state throughout.
#[requires(*a == 1)]
#[ensures(old(forall(|i: usize| *a == 1)))]
#[ensures(*a == 2)]
fn old_around(a: &mut i32) {
    *a = 2
}

fn main() {}
