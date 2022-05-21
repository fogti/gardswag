use crate::Annot;
use gardswag_subst::{FreeVars, Substitutable};

impl<In, T, X> FreeVars<In> for Annot<T, X>
where
    T: FreeVars<In>,
    X: FreeVars<In>,
{
    fn fv(&self, accu: &mut std::collections::BTreeSet<In>, do_add: bool) {
        self.inner.fv(accu, do_add);
        self.extra.fv(accu, do_add);
    }
}

impl<In, Out, T, X> Substitutable<In> for Annot<T, X>
where
    Out: Clone,
    T: Substitutable<In, Out = Out>,
    X: Substitutable<In, Out = Out>,
{
    type Out = Out;

    #[inline]
    fn apply<F: FnMut(&In) -> Option<Out>>(&mut self, f: &mut F) {
        self.inner.apply(f);
        self.extra.apply(f);
    }
}
