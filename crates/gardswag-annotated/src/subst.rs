use crate::Annot;
use core::cmp;
use gardswag_subst::{FreeVars, Substitutable};

impl<In, T, X> FreeVars for Annot<T, X>
where
    In: cmp::Eq + cmp::Ord,
    T: FreeVars<In = In>,
    X: FreeVars<In = In>,
{
    type In = T::In;

    fn fv(&self, accu: &mut std::collections::BTreeSet<In>, do_add: bool) {
        self.inner.fv(accu, do_add);
        self.extra.fv(accu, do_add);
    }
}

impl<In, Out, T, X> Substitutable for Annot<T, X>
where
    In: cmp::Eq + cmp::Ord,
    Out: Clone,
    T: Substitutable<In = In, Out = Out>,
    X: Substitutable<In = In, Out = Out>,
{
    type Out = Out;

    #[inline]
    fn apply<F>(&mut self, f: &F)
    where
        F: Fn(&In) -> Option<Out>,
    {
        self.inner.apply(f);
        self.extra.apply(f);
    }
}
