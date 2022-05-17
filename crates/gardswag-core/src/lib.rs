#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

pub mod ty;
pub use ty::{Ty, TyLit, TyVar};

use core::cmp;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[enum_dispatch::enum_dispatch]
pub trait Substitutable {
    type In: cmp::Eq + cmp::Ord;
    type Out: std::clone::Clone;

    fn fv(&self, accu: &mut BTreeSet<Self::In>, do_add: bool);

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&Self::In) -> Option<Self::Out>;
}

impl<V: Substitutable> Substitutable for [V] {
    type In = V::In;
    type Out = V::Out;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.iter().for_each(|i| i.fv(accu, do_add))
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        self.iter_mut().for_each(|i| i.apply(f));
    }
}

impl<V: Substitutable> Substitutable for Vec<V> {
    type In = V::In;
    type Out = V::Out;

    #[inline]
    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        (**self).fv(accu, do_add)
    }

    #[inline]
    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        (**self).apply(f)
    }
}

impl<V: Substitutable + cmp::Ord> Substitutable for BTreeSet<V> {
    type In = V::In;
    type Out = V::Out;

    #[inline]
    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.iter().for_each(|i| i.fv(accu, do_add))
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        *self = core::mem::take(self)
            .into_iter()
            .map(|mut i| {
                i.apply(f);
                i
            })
            .collect();
    }
}

impl<K: cmp::Eq + cmp::Ord, V: Substitutable> Substitutable for BTreeMap<K, V> {
    type In = V::In;
    type Out = V::Out;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.values().for_each(|i| i.fv(accu, do_add))
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        self.values_mut().for_each(|i| i.apply(f));
    }
}

impl<K: core::hash::Hash + cmp::Eq, V: Substitutable> Substitutable for HashMap<K, V> {
    type In = V::In;
    type Out = V::Out;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.values().for_each(|i| i.fv(accu, do_add))
    }

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        self.values_mut().for_each(|i| i.apply(f));
    }
}
