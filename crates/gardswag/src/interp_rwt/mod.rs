use core::cmp;
use crossbeam_channel as chan;
use crossbeam_utils::thread;
use gardswag_syntax::Symbol;
use once_cell::sync::Lazy;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;
use rayon::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Builtin {
    Plus,
    Minus,
    Mult,
    Eq,
    Leq,
    Not,
    SpawnThread,
    MakeChan,
    ChanSend,
    ChanRecv,
    StdioWrite,
}

impl Builtin {
    fn argc(self) -> usize {
        match self {
            Self::Plus | Self::Minus | Self::Mult | Self::Eq | Self::Leq => 2,
            Self::Not | Self::SpawnThread | Self::StdioWrite => 1,
            Self::MakeChan => 1,
            Self::ChanSend => 2,
            Self::ChanRecv => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct LambdaRef(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct DupPreRef(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct DupResRef(Lazy<Value>);

#[derive(Clone, Debug, Default)]
#[must_use = "the interpreter shouldn't blindly discard values"]
pub enum Value {
    /// this the value that gets passed to argument-unused lambdas
    #[default]
    Poison,

    Unit,
    Boolean(bool),
    Integer(i32),
    PureString(String),

    /// reference to an enclosing lambda argument
    LambdaRef(LambdaRef),

    /// reference to an enclosing dup result, before processing of MkDup
    DupPreRef(DupPreRef),

    /// reference to an enclosing dup result, after processing of MkDup
    DupResRef(Arc<DupResRef>),

    Record(BTreeMap<Symbol, Value>),

    Tagger {
        key: Symbol,
    },
    Tagged {
        key: Symbol,
        value: Box<Value>,
    },

    Builtin {
        f: Builtin,
        args: Vec<Value>,
    },

    Lambda(Box<Value>),
    FixLambda(Box<Value>),

    MkDup {
        /// value to be duplicated
        arg: Value,
        /// value in which it is inserted
        rest: Value,
    },

    Apply {
        /// lambda to be called
        prim: Value,
        /// value to be inserted as lambda arg
        arg: Value,
    },

    ChanSend(chan::Sender<Value>),
    ChanRecv(chan::Receiver<Value>),
}

impl cmp::PartialEq for Value {
    fn eq(&self, oth: &Self) -> bool {
        use Value as V;
        match (self, oth) {
            (V::Unit, V::Unit) => true,
            (V::Boolean(a), V::Boolean(b)) => a == b,
            (V::Integer(a), V::Integer(b)) => a == b,
            (V::PureString(a), V::PureString(b)) => a == b,
            (V::Record(a), V::Record(b)) => a == b,
            (V::Tagger { key: a }, V::Tagger { key: b }) => a == b,
            (V::Tagged { key: ka, value: va }, V::Tagged { key: kb, value: vb }) => ka == kb && va == vb,
            (V::Builtin { f: fa, args: aa }, V::Builtin { f: fb, args: ab }) => fa == fb && aa == ab,
            (V::Lambda(a), V::Lambda(b)) => a == b,
            (V::FixLambda(a), V::FixLambda(b)) => a == b,
            (V::MkDup { arg: aa, rest: ra, .. }, V::MkDup { arg: ab, rest: rb, .. }) =>
                aa == ab && ra == rb,
            (V::Apply { prim: pa, arg: aa }, V::Apply { prim: pb, arg: ab }) => pa == pb && aa == ab,
            (_, _) => false,
        }
    }
}

impl Value {
    fn mk_lazy<F: FnOnce() -> Value>(f: F) -> Self {
        V::DupResRef(DupResRef(Lazy::new(f)))
    }

    pub fn walk_mut<F: Fn(&mut Value) + Send + Sync>(&mut self, f: &F) {
        f(self);
        match self {
            V::Poison | V::Unit | V::Boolean(_) | V::Integer(_) | V::PureString(_) | V::LambdaRef(_) | V::DupPreRef(_) | V::DupResRef(_) | V::Tagger { .. } | V::ChanSend(_) | V::ChanRecv(_)  => {},

            V::Record(xs) => xs.par_iter_mut().for_each(|i| i.walk_mut(f)),

            Tagged {
                value,
                ..
            } => {
                value.walk_mut(f);
            },

            Builtin {
                args,
                ..
            } => {
                args.walk_mut(f);
            },

            Lambda(x) => x.walk_mut(f),
            FixLambda(x) => x.walk_mut(f),

            MkDup {
                arg,
                rest,
            } => {
                rayon::join(|| arg.walk_mut(f), || rest.walk_mut(f));
            },

            Apply {
                prim,
                arg,
            } => {
                rayon::join(|| prim.walk_mut(f), || arg.walk_mut(f));
            },
        }
    }

    pub fn prepare_dup(&mut self) {
        use rayon::prelude::*;
        use Value as V;
        match core::mem::replace(self, V::Poison) {
            v @ (V::Poison | V::Unit | V::Boolean(_) | V::Integer(_) | V::PureString(_) | V::LambdaRef(_) | V::DupPreRef(_) | V::DupResRef(_) | V::Tagger { .. } | V::ChanSend(_) | V::ChanRecv(_)) => {
                *self = v;
            },
            V::Record(mut xs) => {
                *self = Self::mk_lazy(move || {
                    xs.par_iter_mut().for_each(|i| i.prepare_dup());
                    V::Record(xs)
                });
            },

            V::Tagged {
                key: Symbol,
                mut value: Box<Value>,
            } => {
                value.prepare_dup();
                *self = V::Tagged {
                    key,
                    value,
                };
            },

            V::Builtin {
                f: Builtin,
                mut args: Vec<Value>,
            } => {
                *self = if args.is_empty() {
                    V::Builtin { f, args }
                } else {
                    Self::mk_lazy(move || {
                        args.par_iter_mut().for_each(|i| i.prepare_dup());
                        V::Builtin {
                            f,
                            args,
                        }
                    })
                };
            },

            V::Lambda(x) => {
                x.prepare_dup();
                *self = V::Lambda(x);
            },
            V::FixLambda(x) => {
                x.prepare_dup();
                *self = V::FixLambda(x);
            },

            V::MkDup {
                arg,
                rest,
            } => {
                rayon::join(|| arg.prepare_dup(), || rest.prepare_dup());
                *self = V::MkDup {
                    arg,
                    rest,
                };
            },

            V::Apply {
                prim,
                arg,
            } => {
                *self = Self::mk_lazy(move || {
                    rayon::join(|| prim.prepare_dup(), || arg.prepare_dup());
                    V::Apply {
                        prim,
                        arg,
                    }
                });
            },
        }
    }
}

macro_rules! dict {
    ($($name:ident),*) => {
        /// dictionary of symbols used by the standard library
        #[derive(Debug)]
        pub struct Dict {
            $(pub $name: Symbol),
        }

        impl Dict {
            pub fn new(itn: &mut gardswag_interner::Interner) -> Self {
                Self {
                    $($name: itn.get_or_intern(stringify!($name))),
                }
            }
        }
    }
}

dict!(send, recv, Some, None);
