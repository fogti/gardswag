#![forbid(unsafe_code)]

mod varstack;
pub use varstack::{Iter as VarStackIter, VarStack};

pub mod ty;
pub use ty::{Ty, TyLit, TyVar};

use core::cmp;
use std::collections::BTreeSet;

pub trait Substitutable {
    type In: cmp::Eq + cmp::Ord;
    type Out: std::clone::Clone;

    fn fv(&self, accu: &mut BTreeSet<Self::In>, do_add: bool);

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&Self::In) -> Option<Self::Out>;
}
