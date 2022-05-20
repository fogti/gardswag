use core::cmp;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// trait which handles the detection of placeholder variables
pub trait FreeVars {
    type In: cmp::Eq + cmp::Ord;
    fn fv(&self, accu: &mut BTreeSet<Self::In>, do_add: bool);
}

/// trait which handles replacing placeholder variables
pub trait Substitutable: FreeVars {
    type Out: std::clone::Clone;

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&Self::In) -> Option<Self::Out>;
}

impl<V: FreeVars> FreeVars for [V] {
    type In = V::In;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.iter().for_each(|i| i.fv(accu, do_add))
    }
}

impl<V: Substitutable> Substitutable for [V] {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        self.iter_mut().for_each(|i| i.apply(f));
    }
}

impl<V: FreeVars> FreeVars for Vec<V> {
    type In = V::In;

    #[inline]
    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        (**self).fv(accu, do_add)
    }
}

impl<V: Substitutable> Substitutable for Vec<V> {
    type Out = V::Out;

    #[inline]
    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        (**self).apply(f)
    }
}

impl<V: FreeVars + cmp::Ord> FreeVars for BTreeSet<V> {
    type In = V::In;

    #[inline]
    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.iter().for_each(|i| i.fv(accu, do_add))
    }
}

impl<V: Substitutable + cmp::Ord> Substitutable for BTreeSet<V> {
    type Out = V::Out;

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

impl<K: cmp::Eq + cmp::Ord, V: FreeVars> FreeVars for BTreeMap<K, V> {
    type In = V::In;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.values().for_each(|i| i.fv(accu, do_add))
    }
}

// ugly hack
impl<V: FreeVars, V2> FreeVars for (V, V2) {
    type In = V::In;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.0.fv(accu, do_add)
    }
}

impl<K: cmp::Eq + cmp::Ord, V: Substitutable> Substitutable for BTreeMap<K, V> {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        self.values_mut().for_each(|i| i.apply(f));
    }
}

impl<K: core::hash::Hash + cmp::Eq, V: FreeVars> FreeVars for HashMap<K, V> {
    type In = V::In;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.values().for_each(|i| i.fv(accu, do_add))
    }
}

impl<K: core::hash::Hash + cmp::Eq, V: Substitutable> Substitutable for HashMap<K, V> {
    type Out = V::Out;

    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&V::In) -> Option<V::Out>,
    {
        self.values_mut().for_each(|i| i.apply(f));
    }
}

impl<V: FreeVars> FreeVars for gardswag_varstack::VarStack<'_, '_, V> {
    type In = V::In;

    fn fv(&self, accu: &mut BTreeSet<V::In>, do_add: bool) {
        self.iter().for_each(|(_, i)| i.fv(accu, do_add))
    }
}
