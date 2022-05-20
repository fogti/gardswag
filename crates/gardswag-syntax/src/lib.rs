#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub mod lex;

mod annot;
pub use annot::{Annot, AnnotFmap};

mod block;
use block::parse_block;
pub use block::Block;

#[cfg(test)]
mod tests;

pub type Error = Annot<ErrorKind>;

#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum ErrorKind {
    #[error("(lexer) {0}")]
    Lex(#[from] lex::ErrorKind),

    #[error("(parser) unexpected end of expression")]
    UnexpectedEoe,

    #[error("unexpected token {0:?}")]
    UnexpectedToken(lex::Token),

    #[error("duplicate key {0:?}")]
    DuplicateKey(String),
}

pub type Identifier<X> = Annot<String, X>;
pub type Expr<X> = Annot<ExprKind<X>, X>;

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum ExprKind<X> {
    Let {
        lhs: Identifier<()>,
        rhs: Box<Expr<X>>,
        rest: Block<X>,
    },
    Block(Block<X>),

    If {
        cond: Box<Expr<X>>,
        then: Block<X>,
        or_else: Block<X>,
    },

    Lambda {
        arg: String,
        body: Box<Expr<X>>,
    },
    Call {
        prim: Box<Expr<X>>,
        arg: Box<Expr<X>>,
    },

    // fixpoint operator
    Fix {
        arg: String,
        body: Box<Expr<X>>,
    },

    // record stuff
    // - introduction
    Record(BTreeMap<String, Expr<X>>),
    // - elimination
    Dot {
        prim: Box<Expr<X>>,
        key: Identifier<()>,
    },
    // - transformation
    Update {
        orig: Box<Expr<X>>,
        ovrd: Box<Expr<X>>,
    },

    // discriminated/tagged union stuff
    // - introduction
    Tagger {
        key: String,
    },

    // R & DU - elimination
    Match {
        inp: Box<Expr<X>>,
        cases: Vec<Case<X>>,
    },

    FormatString(Vec<Expr<X>>),

    // literal stuff
    Identifier(String),
    Unit,
    Boolean(bool),
    Integer(i32),
    PureString(String),
}

impl<X> ExprKind<X> {
    pub fn typ(&self) -> &'static str {
        match self {
            Self::Let { .. } => "let",
            Self::Block(_) => "block",
            Self::If { .. } => "if",
            Self::Lambda { .. } => "lambda",
            Self::Call { .. } => "call",
            Self::Record(_) => "record",
            Self::Dot { .. } => "dot",
            Self::Update { .. } => "update",
            Self::Tagger { .. } => "tagger",
            Self::Match { .. } => "match",
            Self::Fix { .. } => "fix",
            Self::FormatString(_) => "fmtstr",
            Self::Identifier(_) => "ident",
            Self::Unit => "lit.unit",
            Self::Boolean(_) => "lit.bool",
            Self::Integer(_) => "lit.int",
            Self::PureString(_) => "lit.str",
        }
    }

    /// checks if a variable is used anywhere in a expression
    pub fn is_var_accessed(&self, v: &str) -> bool {
        match self {
            Self::Let { lhs, rhs, rest } => {
                rhs.inner.is_var_accessed(v) || (lhs.inner != v && rest.is_var_accessed(v))
            }
            Self::Block(blk) => blk.is_var_accessed(v),
            Self::If {
                cond,
                then,
                or_else,
            } => {
                cond.inner.is_var_accessed(v)
                    || then.is_var_accessed(v)
                    || or_else.is_var_accessed(v)
            }
            Self::Lambda { arg, body } | Self::Fix { arg, body } => {
                arg != v && body.inner.is_var_accessed(v)
            }
            Self::Call { prim, arg } => {
                prim.inner.is_var_accessed(v) || arg.inner.is_var_accessed(v)
            }
            Self::Record(rcd) => rcd.values().any(|i| i.inner.is_var_accessed(v)),
            Self::Dot { prim, .. } => prim.inner.is_var_accessed(v),
            Self::Update { orig, ovrd } => {
                orig.inner.is_var_accessed(v) || ovrd.inner.is_var_accessed(v)
            }
            Self::Match { inp, cases } => {
                inp.inner.is_var_accessed(v)
                    || cases
                        .iter()
                        .any(|i| !i.pat.is_var_defined(v) && i.body.inner.is_var_accessed(v))
            }
            Self::FormatString(exs) => exs.iter().any(|i| i.inner.is_var_accessed(v)),
            Self::Identifier(id) => id == v,
            Self::Tagger { key: _ }
            | Self::Unit
            | Self::Boolean(_)
            | Self::Integer(_)
            | Self::PureString(_) => false,
        }
    }
}

impl<X, NewExtra> AnnotFmap<NewExtra> for ExprKind<X> {
    type Extra = X;
    type Output = ExprKind<NewExtra>;
    fn map<F>(self, f: &mut F) -> ExprKind<NewExtra>
    where
        F: FnMut(X) -> NewExtra,
    {
        match self {
            ExprKind::Let { lhs, rhs, rest } => ExprKind::Let {
                lhs,
                rhs: rhs.map(f),
                rest: rest.map(f),
            },
            ExprKind::Block(x) => ExprKind::Block(x.map(f)),

            ExprKind::If {
                cond,
                then,
                or_else,
            } => ExprKind::If {
                cond: cond.map(f),
                then: then.map(f),
                or_else: or_else.map(f),
            },

            ExprKind::Lambda { arg, body } => ExprKind::Lambda {
                arg,
                body: body.map(f),
            },
            ExprKind::Call { prim, arg } => ExprKind::Call {
                prim: prim.map(f),
                arg: arg.map(f),
            },

            ExprKind::Fix { arg, body } => ExprKind::Fix {
                arg,
                body: body.map(f),
            },

            ExprKind::Record(x) => {
                ExprKind::Record(x.into_iter().map(|(k, v)| (k, v.map(f))).collect())
            }
            ExprKind::Dot { prim, key } => ExprKind::Dot {
                prim: prim.map(f),
                key,
            },
            ExprKind::Update { orig, ovrd } => ExprKind::Update {
                orig: orig.map(f),
                ovrd: ovrd.map(f),
            },

            ExprKind::Tagger { key } => ExprKind::Tagger { key },

            ExprKind::Match { inp, cases } => ExprKind::Match {
                inp: inp.map(f),
                cases: cases.map(f),
            },

            ExprKind::FormatString(x) => ExprKind::FormatString(x.map(f)),

            ExprKind::Identifier(x) => ExprKind::Identifier(x),
            ExprKind::Unit => ExprKind::Unit,
            ExprKind::Boolean(x) => ExprKind::Boolean(x),
            ExprKind::Integer(x) => ExprKind::Integer(x),
            ExprKind::PureString(x) => ExprKind::PureString(x),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Case<X> {
    pub pat: Pattern<X>,
    pub body: Expr<X>,
}

impl<X, NewExtra> AnnotFmap<NewExtra> for Case<X> {
    type Extra = X;
    type Output = Case<NewExtra>;
    fn map<F>(self, f: &mut F) -> Case<NewExtra>
    where
        F: FnMut(X) -> NewExtra,
    {
        let Case { pat, body } = self;
        Case {
            pat: pat.map(f),
            body: body.map(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum Pattern<X> {
    Unit,
    Identifier(Identifier<X>),
    Tagged {
        key: Identifier<()>,
        value: Box<Pattern<X>>,
    },
    Record(Annot<BTreeMap<String, Pattern<X>>>),
}

impl<X, NewExtra> AnnotFmap<NewExtra> for Pattern<X> {
    type Extra = X;
    type Output = Pattern<NewExtra>;
    fn map<F>(self, f: &mut F) -> Pattern<NewExtra>
    where
        F: FnMut(X) -> NewExtra,
    {
        match self {
            Pattern::Unit => Pattern::Unit,
            Pattern::Identifier(Annot {
                offset,
                extra,
                inner,
            }) => Pattern::Identifier(Annot {
                offset,
                extra: f(extra),
                inner,
            }),
            Pattern::Tagged { key, value } => Pattern::Tagged {
                key,
                value: value.map(f),
            },
            Pattern::Record(Annot {
                offset,
                extra: _,
                inner,
            }) => Pattern::Record(Annot {
                offset,
                extra: (),
                inner: inner.into_iter().map(|(k, v)| (k, v.map(f))).collect(),
            }),
        }
    }
}

impl<X> Pattern<X> {
    /// checks if a variable is defined anywhere in the pattern
    pub fn is_var_defined(&self, v: &str) -> bool {
        match self {
            Self::Unit => false,
            Self::Identifier(x) => x.inner == v,
            Self::Tagged { value, .. } => value.is_var_defined(v),
            Self::Record(xs) => xs.inner.values().any(|i| i.is_var_defined(v)),
        }
    }

    pub fn is_wildcard(&self) -> bool {
        if let Self::Identifier(x) = self {
            x.inner.is_empty()
        } else {
            false
        }
    }
}

#[allow(clippy::enum_variant_names)]
enum ParseResult<T, E> {
    /// EOF or invalid token
    PNone,

    /// parsing successful
    POk(T),

    /// parsing failed
    PErr(Annot<E>),
}
use ParseResult::*;

impl<'a, T, E> ParseResult<T, &'a E> {
    fn cloned_err(self) -> ParseResult<T, E>
    where
        E: Clone,
    {
        match self {
            PNone => PNone,
            POk(x) => POk(x),
            PErr(Annot {
                offset,
                inner,
                extra,
            }) => PErr(Annot {
                offset,
                inner: inner.clone(),
                extra,
            }),
        }
    }
}

impl<T, E> From<Option<Result<T, Annot<E>>>> for ParseResult<T, E> {
    fn from(x: Option<Result<T, Annot<E>>>) -> ParseResult<T, E> {
        match x {
            None => PNone,
            Some(Ok(y)) => POk(y),
            Some(Err(y)) => PErr(y),
        }
    }
}

impl<'a, T, E> From<Option<&'a Result<T, Annot<E>>>> for ParseResult<&'a T, &'a E> {
    fn from(x: Option<&'a Result<T, Annot<E>>>) -> ParseResult<&'a T, &'a E> {
        match x {
            None => PNone,
            Some(Ok(y)) => POk(y),
            Some(Err(Annot {
                offset,
                inner,
                extra,
            })) => PErr(Annot {
                offset: *offset,
                inner,
                extra: *extra,
            }),
        }
    }
}

impl<T, E> From<Result<T, Annot<E>>> for ParseResult<T, E> {
    fn from(x: Result<T, Annot<E>>) -> ParseResult<T, E> {
        match x {
            Ok(y) => POk(y),
            Err(y) => PErr(y),
        }
    }
}

macro_rules! xtry {
    ($x:expr) => {{
        match $x.into() {
            PNone => return PNone,
            PErr(Annot {
                offset,
                inner,
                extra,
            }) => {
                return PErr(Annot {
                    offset,
                    inner: inner.into(),
                    extra,
                })
            }
            POk(x) => x,
        }
    }};
}

fn unexpect_eoe<T, E: Into<ErrorKind>>(offset: usize, x: ParseResult<T, E>) -> Result<T, Error> {
    match x {
        PNone => Err(Annot {
            offset,
            inner: ErrorKind::UnexpectedEoe,
            extra: (),
        }),
        PErr(Annot {
            offset,
            inner,
            extra,
        }) => Err(Annot {
            offset,
            inner: inner.into(),
            extra,
        }),
        POk(y) => Ok(y),
    }
}

type PeekLexer<'a> = core::iter::Peekable<lex::Lexer<'a>>;

fn expect_token_noeof<F, R>(super_offset: usize, lxr: &mut PeekLexer<'_>, f: F) -> Result<R, Error>
where
    F: FnOnce(lex::Token) -> Result<R, lex::Token>,
{
    let tok = unexpect_eoe(super_offset, lxr.next().into())?;
    f(tok).map_err(|tok| Error {
        offset: super_offset,
        inner: ErrorKind::UnexpectedToken(tok),
        extra: (),
    })
}

fn expect_token_exact(
    super_offset: usize,
    lxr: &mut PeekLexer<'_>,
    tk: lex::TokenKind,
) -> Result<usize, Error> {
    expect_token_noeof(super_offset, lxr, |t| match t {
        lex::Token { inner, offset, .. } if inner == tk => Ok(offset),
        _ => Err(t),
    })
}

fn handle_wildcard(s: String) -> String {
    if s == "_" {
        String::new()
    } else {
        s
    }
}

enum DotIntermed<T> {
    Identifier(String),
    Record(BTreeMap<String, T>),
}

impl<X> From<DotIntermed<Expr<X>>> for ExprKind<X> {
    fn from(x: DotIntermed<Expr<X>>) -> ExprKind<X> {
        match x {
            DotIntermed::Identifier(x) => ExprKind::Identifier(x),
            DotIntermed::Record(rcd) => ExprKind::Record(rcd),
        }
    }
}

impl<X> From<Annot<DotIntermed<Pattern<X>>, X>> for Pattern<X> {
    fn from(
        Annot {
            offset,
            inner,
            extra,
        }: Annot<DotIntermed<Pattern<X>>, X>,
    ) -> Pattern<X> {
        match inner {
            DotIntermed::Identifier(inner) => Pattern::Identifier(Annot {
                offset,
                inner: handle_wildcard(inner),
                extra,
            }),
            DotIntermed::Record(inner) => Pattern::Record(Annot {
                offset,
                inner,
                extra: (),
            }),
        }
    }
}

/// helper function for parsing dot record terms
/// ` .{ key1: value1; key2: value2; } `
fn try_parse_record<'a, T, F>(
    super_offset: usize,
    lxr: &mut PeekLexer<'a>,
    f: F,
) -> ParseResult<T, ErrorKind>
where
    F: Fn(&mut PeekLexer<'a>) -> ParseResult<T, ErrorKind>,
    T: From<Annot<DotIntermed<T>>>,
{
    use lex::{Token, TokenKind as Tk};
    let backtrack = lxr.clone();
    let Annot { inner, offset, .. } = xtry!(unexpect_eoe(super_offset, lxr.next().into()));
    if inner != Tk::LcBracket {
        *lxr = backtrack;
        return PNone;
    }
    core::mem::drop(backtrack);
    let mut rcd = BTreeMap::new();
    while let Some(Ok(Token {
        offset,
        inner: Tk::Identifier(id),
        extra: (),
    })) = lxr.next_if(|i| {
        matches!(
            i,
            Ok(Token {
                inner: Tk::Identifier(_),
                ..
            })
        )
    }) {
        let dcd = xtry!(expect_token_noeof(
            offset,
            lxr,
            |lex::Token {
                 inner,
                 offset,
                 extra,
             }| {
                match inner {
                    Tk::EqSym => Ok(true),
                    Tk::SemiColon => Ok(false),
                    _ => Err(lex::Token {
                        inner,
                        offset,
                        extra,
                    }),
                }
            }
        ));
        let value = if dcd {
            let value = xtry!(unexpect_eoe(offset, f(lxr)));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::SemiColon));
            value
        } else {
            (Annot {
                offset,
                inner: DotIntermed::Identifier(id.clone()),
                extra: (),
            })
            .into()
        };
        use std::collections::btree_map::Entry;
        match rcd.entry(id) {
            Entry::Vacant(v) => {
                v.insert(value);
            }
            Entry::Occupied(occ) => {
                return PErr(Annot {
                    offset,
                    inner: ErrorKind::DuplicateKey(occ.key().to_string()),
                    extra: (),
                });
            }
        }
    }
    let _ = xtry!(expect_token_exact(offset, lxr, Tk::RcBracket));
    POk((Annot {
        offset,
        inner: DotIntermed::Record(rcd),
        extra: (),
    })
    .into())
}

fn parse_pattern(lxr: &mut PeekLexer<'_>) -> ParseResult<Pattern<()>, ErrorKind> {
    use lex::TokenKind as Tk;
    let Annot { offset, inner, .. } = xtry!(lxr.next());
    match inner {
        Tk::Identifier(x) => POk(Pattern::Identifier(Annot {
            offset,
            inner: handle_wildcard(x),
            extra: (),
        })),
        Tk::Dot => {
            match try_parse_record(offset, lxr, parse_pattern) {
                PNone => {}
                y => return y,
            }
            let Annot {
                inner: key,
                offset,
                extra,
            } = xtry!(expect_token_noeof(
                offset,
                lxr,
                |Annot {
                     inner,
                     offset,
                     extra,
                 }| match inner {
                    Tk::Identifier(x) => Ok(Annot {
                        inner: x,
                        offset,
                        extra
                    }),
                    _ => Err(Annot {
                        inner,
                        offset,
                        extra
                    }),
                }
            ));
            let value = xtry!(unexpect_eoe(offset, parse_pattern(lxr)));
            POk(Pattern::Tagged {
                key: Annot {
                    offset,
                    inner: key,
                    extra,
                },
                value: Box::new(value),
            })
        }
        Tk::LParen => POk(
            if lxr
                .next_if(|i| {
                    matches!(
                        i,
                        Ok(lex::Token {
                            inner: Tk::RParen,
                            ..
                        })
                    )
                })
                .is_some()
            {
                Pattern::Unit
            } else {
                let inner = xtry!(unexpect_eoe(offset, parse_pattern(lxr)));
                let _ = xtry!(expect_token_exact(offset, lxr, Tk::RParen));
                inner
            },
        ),
        inner => PErr(Error {
            offset,
            inner: ErrorKind::UnexpectedToken(Annot {
                offset,
                inner,
                extra: (),
            }),
            extra: (),
        }),
    }
}

fn parse_expr(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr<()>, ErrorKind> {
    use lex::{Keyword as Kw, Token, TokenKind as Tk};
    let Token {
        mut offset, inner, ..
    } = xtry!(lxr.next_if(|i| {
        if let Ok(Token { inner, .. }) = i {
            !matches!(
                inner,
                Tk::RcBracket | Tk::RParen | Tk::SemiColon | Tk::Pipe | Tk::Case | Tk::StringEnd
            )
        } else {
            true
        }
    }));
    let inner = match inner {
        Tk::Keyword(Kw::Let) => {
            let is_rec = if let Some(Ok(Token {
                inner: Tk::Keyword(Kw::Rec),
                ..
            })) = lxr.peek()
            {
                let _ = lxr.next();
                true
            } else {
                false
            };
            let lhs = xtry!(expect_token_noeof(offset, lxr, |t| match t {
                Token {
                    offset,
                    inner: Tk::Identifier(inner),
                    extra,
                } => Ok(Identifier {
                    offset,
                    inner,
                    extra
                }),
                _ => Err(t),
            }));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::EqSym));
            let mut rhs = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
            let blk_offset = xtry!(expect_token_exact(offset, lxr, Tk::SemiColon));
            let rest = if lxr.peek().is_none() {
                Block::default()
            } else {
                xtry!(parse_block(blk_offset, lxr))
            };
            if is_rec {
                // desugar `let rec` to `fix`
                rhs = Expr {
                    offset: rhs.offset,
                    inner: ExprKind::Fix {
                        arg: lhs.inner.clone(),
                        body: Box::new(rhs),
                    },
                    extra: (),
                };
            }
            Ok(ExprKind::Let {
                lhs,
                rhs: Box::new(rhs),
                rest,
            })
        }
        Tk::Keyword(Kw::If) => {
            let cond = xtry!(unexpect_eoe(offset, parse_expr(lxr)));
            let then = xtry!(parse_block(offset, lxr));
            let or_else = if let Some(Ok(Annot {
                inner: Tk::SemiColon,
                ..
            }))
            | None = lxr.peek()
            {
                Block::default()
            } else {
                xtry!(parse_block(offset, lxr))
            };
            Ok(ExprKind::If {
                cond: Box::new(cond),
                then,
                or_else,
            })
        }
        Tk::Keyword(Kw::Match) => {
            let inp = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
            let mut cases = Vec::new();
            while let Some(Ok(Token {
                offset: c_offset,
                inner: Tk::Case,
                ..
            })) = lxr.next_if(|i| {
                matches!(
                    i,
                    Ok(Token {
                        inner: Tk::Case,
                        ..
                    })
                )
            }) {
                let pat = xtry!(unexpect_eoe(c_offset, parse_pattern(lxr)));
                let _ = xtry!(expect_token_exact(c_offset, lxr, Tk::CaseThen));
                let body = xtry!(unexpect_eoe(c_offset, parse_expr_greedy(lxr)));
                cases.push(Case { pat, body });
            }
            if cases.is_empty() {
                let _ = xtry!(expect_token_exact(offset, lxr, Tk::Case));
                unreachable!();
            }
            Ok(ExprKind::Match {
                inp: Box::new(inp),
                cases,
            })
        }
        Tk::Lambda(lam) => {
            let expr = xtry!(unexpect_eoe(offset, parse_expr_calls(lxr)));
            Ok(ExprKind::Lambda {
                arg: handle_wildcard(lam),
                body: Box::new(expr),
            })
        }
        Tk::Identifier(id) => Ok(ExprKind::Identifier(id)),
        Tk::Keyword(Kw::False) => Ok(ExprKind::Boolean(false)),
        Tk::Keyword(Kw::True) => Ok(ExprKind::Boolean(true)),
        Tk::Integer(i) => Ok(ExprKind::Integer(i)),
        Tk::LcBracket => {
            let block = xtry!(parse_block(offset, lxr));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::RcBracket));
            Ok(ExprKind::Block(block))
        }
        Tk::LParen => Ok(
            if lxr
                .next_if(|i| {
                    matches!(
                        i,
                        Ok(Token {
                            inner: Tk::RParen,
                            ..
                        })
                    )
                })
                .is_some()
            {
                ExprKind::Unit
            } else {
                let Annot {
                    inner,
                    offset: new_offset,
                    ..
                } = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
                let _ = xtry!(expect_token_exact(offset, lxr, Tk::RParen));
                offset = new_offset;
                inner
            },
        ),
        Tk::StringStart => {
            // handle format strings
            let mut parts = Vec::new();
            loop {
                if let Some(Ok(Token {
                    offset: s_offset,
                    inner: Tk::PureString(s),
                    ..
                })) = lxr.next_if(|i| {
                    matches!(
                        i,
                        Ok(Token {
                            inner: Tk::PureString(_),
                            ..
                        })
                    )
                }) {
                    parts.push(Annot {
                        offset: s_offset,
                        inner: ExprKind::PureString(s),
                        extra: (),
                    });
                    continue;
                }
                match parse_expr_greedy(lxr) {
                    PNone => break,
                    PErr(e) => return PErr(e),
                    POk(x) => parts.push(x),
                }
            }
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::StringEnd));
            Ok(ExprKind::FormatString(parts))
        }
        Tk::Dot => match try_parse_record(offset, lxr, &parse_expr_greedy) {
            PNone => {
                let key = xtry!(expect_token_noeof(
                    offset,
                    lxr,
                    |Annot {
                         inner,
                         offset,
                         extra,
                     }| match inner {
                        Tk::Identifier(x) => Ok(Annot {
                            inner: x,
                            offset,
                            extra
                        }),
                        _ => Err(Annot {
                            inner,
                            offset,
                            extra
                        }),
                    }
                ))
                .inner;
                Ok(ExprKind::Tagger { key })
            }
            PErr(e) => return PErr(e),
            POk(y) => Ok(y.inner),
        },
        _ => {
            return PErr(Annot {
                offset,
                inner: ErrorKind::UnexpectedToken(Annot {
                    offset,
                    inner,
                    extra: (),
                }),
                extra: (),
            });
        }
    };

    match inner {
        Ok(mut inner) => {
            // handle `.` chains
            while let Some(Ok(Annot {
                inner: Tk::Dot,
                offset: new_offset,
                extra: (),
            })) = lxr.peek()
            {
                let new_offset = *new_offset;
                let _ = lxr.next();
                let key = xtry!(expect_token_noeof(new_offset, lxr, |t| match t {
                    Token {
                        inner: Tk::Identifier(id),
                        offset,
                        extra,
                    } => Ok(Annot {
                        offset,
                        inner: id,
                        extra
                    }),
                    _ => Err(t),
                }));
                inner = ExprKind::Dot {
                    prim: Box::new(Annot {
                        offset,
                        inner,
                        extra: (),
                    }),
                    key,
                };
                offset = new_offset;
            }
            POk(Annot {
                offset,
                inner,
                extra: (),
            })
        }
        Err(inner) => PErr(Annot {
            offset,
            inner,
            extra: (),
        }),
    }
}

fn parse_expr_calls(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr<()>, ErrorKind> {
    let Annot {
        mut inner,
        offset,
        extra: (),
    } = xtry!(parse_expr(lxr));
    // hanble arguments
    loop {
        let save_lxr = (*lxr).clone();
        let expr = match parse_expr(lxr) {
            PNone => break,
            PErr(e) => {
                if let ErrorKind::UnexpectedToken(..) = e.inner {
                    // recover if we hit something unparsable
                    *lxr = save_lxr;
                    break;
                } else {
                    return PErr(e);
                }
            }
            POk(x) => x,
        };
        inner = ExprKind::Call {
            prim: Box::new(Annot {
                offset,
                inner,
                extra: (),
            }),
            arg: Box::new(expr),
        };
    }
    POk(Annot {
        offset,
        inner,
        extra: (),
    })
}

fn parse_expr_greedy(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr<()>, ErrorKind> {
    use lex::TokenKind as Tk;
    let mut ret = xtry!(parse_expr_calls(lxr));
    // handle pipes and updates
    while let Some(x) = lxr.next_if(|i| {
        matches!(
            i,
            Ok(lex::Token {
                inner: Tk::Pipe | Tk::Update,
                ..
            }) | Err(_)
        )
    }) {
        let x = xtry!(x);
        let expr = xtry!(unexpect_eoe(x.offset, parse_expr_calls(lxr)));
        ret = Annot {
            offset: x.offset,
            inner: match x.inner {
                Tk::Pipe => ExprKind::Call {
                    prim: Box::new(expr),
                    arg: Box::new(ret),
                },
                Tk::Update => ExprKind::Update {
                    orig: Box::new(ret),
                    ovrd: Box::new(expr),
                },
                _ => unreachable!(),
            },
            extra: (),
        };
    }
    POk(ret)
}

#[inline]
pub fn parse(inp: &str) -> Result<Block<()>, Error> {
    let mut lxr = lex::Lexer::new(inp).peekable();
    parse_block(0, &mut lxr)
}
