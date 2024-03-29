#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

use core::cmp;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// trait which handles the detection of placeholder variables
pub trait FreeVars<In> {
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool);
}

/// trait which handles replacing placeholder variables
pub trait Substitutable<In>: FreeVars<In> {
    type Out: std::clone::Clone;

    fn apply<F>(&mut self, f: &mut F)
    where
        F: FnMut(&In) -> Option<Self::Out>;
}

impl<In, V: FreeVars<In>> FreeVars<In> for [V] {
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        self.iter().for_each(|i| i.fv(accu, do_add))
    }
}

impl<In, V: Substitutable<In>> Substitutable<In> for [V] {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &mut F)
    where
        F: FnMut(&In) -> Option<V::Out>,
    {
        self.iter_mut().for_each(|i| i.apply(f));
    }
}

impl<In, V: FreeVars<In>> FreeVars<In> for Vec<V> {
    #[inline]
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        (**self).fv(accu, do_add)
    }
}

impl<In, V: Substitutable<In>> Substitutable<In> for Vec<V> {
    type Out = V::Out;

    #[inline]
    fn apply<F>(&mut self, f: &mut F)
    where
        F: FnMut(&In) -> Option<V::Out>,
    {
        (**self).apply(f)
    }
}

impl<In, V: FreeVars<In> + cmp::Ord> FreeVars<In> for BTreeSet<V> {
    #[inline]
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        self.iter().for_each(|i| i.fv(accu, do_add))
    }
}

impl<In, V: Substitutable<In> + cmp::Ord> Substitutable<In> for BTreeSet<V> {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &mut F)
    where
        F: FnMut(&In) -> Option<V::Out>,
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

impl<In, K: cmp::Eq + cmp::Ord, V: FreeVars<In>> FreeVars<In> for BTreeMap<K, V> {
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        self.values().for_each(|i| i.fv(accu, do_add))
    }
}

// ugly hack
impl<In, V: FreeVars<In>, V2> FreeVars<In> for (V, V2) {
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        self.0.fv(accu, do_add)
    }
}

impl<In, K: cmp::Eq + cmp::Ord, V: Substitutable<In>> Substitutable<In> for BTreeMap<K, V> {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &mut F)
    where
        F: FnMut(&In) -> Option<V::Out>,
    {
        self.values_mut().for_each(|i| i.apply(f));
    }
}

impl<In, K: core::hash::Hash + cmp::Eq, V: FreeVars<In>> FreeVars<In> for HashMap<K, V> {
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        self.values().for_each(|i| i.fv(accu, do_add))
    }
}

impl<In, K: core::hash::Hash + cmp::Eq, V: Substitutable<In>> Substitutable<In> for HashMap<K, V> {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &mut F)
    where
        F: FnMut(&In) -> Option<V::Out>,
    {
        self.values_mut().for_each(|i| i.apply(f));
    }
}

#[cfg(feature = "varstack")]
impl<In, S: Copy, V: FreeVars<In>> FreeVars<In> for varstack::VarStack<'_, S, V> {
    fn fv(&self, accu: &mut BTreeSet<In>, do_add: bool) {
        self.iter().for_each(|(_, i)| i.fv(accu, do_add))
    }
}

pub trait AutoImpl: Sized + Copy + core::cmp::Eq + core::cmp::Ord {}
impl AutoImpl for usize {}

impl<T: AutoImpl> FreeVars<T> for T {
    #[inline]
    fn fv(&self, accu: &mut BTreeSet<T>, do_add: bool) {
        if do_add {
            accu.insert(*self);
        } else {
            accu.remove(self);
        }
    }
}

impl<T: AutoImpl> Substitutable<T> for T {
    type Out = T;
    #[inline]
    fn apply<F: FnMut(&T) -> Option<T>>(&mut self, f: &mut F) {
        if let Some(x) = f(self) {
            *self = x;
        }
    }
}
