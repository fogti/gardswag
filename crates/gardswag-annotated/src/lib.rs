#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

use core::fmt;

#[derive(Clone, PartialEq, Eq, serde::Deserialize, serde::Serialize)]
pub struct Annot<T, A = ()> {
    pub offset: usize,
    pub inner: T,
    pub extra: A,
}

impl<T, X> Annot<T, X> {
    pub fn map_leaf<F, R>(self, f: &mut F) -> Annot<T, R>
    where
        F: FnMut(X) -> R,
    {
        let Annot {
            offset,
            inner,
            extra,
        } = self;
        Annot {
            offset,
            inner,
            extra: f(extra),
        }
    }
}

pub trait AnnotFmap<NewExtra> {
    type Extra;
    type Output: AnnotFmap<NewExtra, Extra = NewExtra>;
    fn map<F>(self, f: &mut F) -> Self::Output
    where
        F: FnMut(Self::Extra) -> NewExtra;
}

impl<T: std::error::Error + 'static> std::error::Error for Annot<T> {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.inner)
    }
}

impl<T: fmt::Display, X: fmt::Debug> fmt::Display for Annot<T, X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}: {},{:?}", self.offset, self.inner, self.extra)
    }
}

impl<T: fmt::Debug, X: fmt::Debug> fmt::Debug for Annot<T, X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}: {:?},{:?}", self.offset, self.inner, self.extra)
    }
}

impl<T, A, NewExtra> AnnotFmap<NewExtra> for Annot<T, A>
where
    T: AnnotFmap<NewExtra, Extra = A>,
{
    type Extra = A;
    type Output = Annot<T::Output, NewExtra>;
    fn map<F>(self, f: &mut F) -> Self::Output
    where
        F: FnMut(Self::Extra) -> NewExtra,
    {
        let Annot {
            offset,
            inner,
            extra,
        } = self;
        Annot {
            offset,
            inner: inner.map(f),
            extra: f(extra),
        }
    }
}

impl<T, E, X> From<Annot<Result<T, E>, X>> for Result<Annot<T, X>, Annot<E, X>> {
    #[inline]
    fn from(
        Annot {
            offset,
            inner,
            extra,
        }: Annot<Result<T, E>, X>,
    ) -> Self {
        match inner {
            Ok(inner) => Ok(Annot {
                offset,
                inner,
                extra,
            }),
            Err(inner) => Err(Annot {
                offset,
                inner,
                extra,
            }),
        }
    }
}

impl<T, NewExtra> AnnotFmap<NewExtra> for Option<T>
where
    T: AnnotFmap<NewExtra>,
{
    type Extra = T::Extra;
    type Output = Option<T::Output>;
    fn map<F>(self, f: &mut F) -> Self::Output
    where
        F: FnMut(Self::Extra) -> NewExtra,
    {
        self.map(|x| x.map(f))
    }
}

impl<T, NewExtra> AnnotFmap<NewExtra> for Box<T>
where
    T: AnnotFmap<NewExtra>,
{
    type Extra = T::Extra;
    type Output = Box<T::Output>;
    fn map<F>(self, f: &mut F) -> Self::Output
    where
        F: FnMut(T::Extra) -> NewExtra,
    {
        Box::new((*self).map(f))
    }
}

impl<T, NewExtra> AnnotFmap<NewExtra> for Vec<T>
where
    T: AnnotFmap<NewExtra>,
{
    type Extra = T::Extra;
    type Output = Vec<T::Output>;
    fn map<F>(self, f: &mut F) -> Self::Output
    where
        F: FnMut(Self::Extra) -> NewExtra,
    {
        self.into_iter().map(|i| i.map(f)).collect()
    }
}
