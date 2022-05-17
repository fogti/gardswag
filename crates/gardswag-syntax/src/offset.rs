use core::fmt;

#[derive(Clone, PartialEq, Eq, serde::Deserialize, serde::Serialize)]
pub struct Offsetted<T> {
    pub offset: usize,
    pub inner: T,
}

impl<T: std::error::Error + 'static> std::error::Error for Offsetted<T> {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.inner)
    }
}

impl<T: fmt::Display> fmt::Display for Offsetted<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}: {}", self.offset, self.inner)
    }
}

impl<T: fmt::Debug> fmt::Debug for Offsetted<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}: {:?}", self.offset, self.inner)
    }
}

macro_rules! impl_inner_tr {
    ($from:ty, $to:ty) => {
        impl From<Offsetted<$from>> for Offsetted<$to> {
            #[inline]
            fn from(Offsetted { offset, inner }: Offsetted<$from>) -> Self {
                Self {
                    offset,
                    inner: inner.into(),
                }
            }
        }
    };
}

impl_inner_tr!(crate::lex::ErrorKind, crate::ErrorKind);
impl_inner_tr!(crate::DotIntermed<crate::Expr>, crate::ExprKind);

impl<T, E> From<Offsetted<Result<T, E>>> for Result<Offsetted<T>, Offsetted<E>> {
    #[inline]
    fn from(Offsetted { offset, inner }: Offsetted<Result<T, E>>) -> Self {
        match inner {
            Ok(inner) => Ok(Offsetted { offset, inner }),
            Err(inner) => Err(Offsetted { offset, inner }),
        }
    }
}
