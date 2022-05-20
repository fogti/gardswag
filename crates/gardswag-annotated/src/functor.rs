pub trait AnnotFmap<NewExtra> {
    type Extra;
    type Output: AnnotFmap<NewExtra, Extra = NewExtra>;
    fn map<F>(self, f: &mut F) -> Self::Output
    where
        F: FnMut(Self::Extra) -> NewExtra;
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
