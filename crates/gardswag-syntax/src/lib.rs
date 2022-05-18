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
mod offset;
pub use offset::Offsetted;

pub type Error = Offsetted<ErrorKind>;

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

pub type Identifier = Offsetted<String>;
pub type Expr = Offsetted<ExprKind>;

#[derive(Clone, Debug, Default, PartialEq, Deserialize, Serialize)]
pub struct Block {
    pub stmts: Vec<Expr>,
    pub term: Option<Box<Expr>>,
}

impl Block {
    pub fn is_var_accessed(&self, v: &str) -> bool {
        self.stmts
            .iter()
            .chain(self.term.as_ref().into_iter().map(|a| &**a))
            .any(|i| i.inner.is_var_accessed(v))
    }
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum ExprKind {
    Let {
        lhs: Identifier,
        rhs: Box<Expr>,
        rest: Block,
    },
    Block(Block),

    If {
        cond: Box<Expr>,
        then: Block,
        or_else: Block,
    },

    Lambda {
        arg: String,
        body: Box<Expr>,
    },
    Call {
        prim: Box<Expr>,
        arg: Box<Expr>,
    },

    // fixpoint operator
    Fix {
        arg: String,
        body: Box<Expr>,
    },

    // record stuff
    // - introduction
    Record(BTreeMap<String, Expr>),
    // - elimination
    Dot {
        prim: Box<Expr>,
        key: Identifier,
    },
    // - transformation
    Update {
        orig: Box<Expr>,
        ovrd: Box<Expr>,
    },

    // discriminated/tagged union stuff
    // - introduction
    Tagged {
        key: String,
        value: Box<Expr>,
    },

    // R & DU - elimination
    Match {
        inp: Box<Expr>,
        cases: Vec<Case>,
    },

    FormatString(Vec<Expr>),

    // literal stuff
    Identifier(String),
    Boolean(bool),
    Integer(i32),
    PureString(String),
}

impl ExprKind {
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
            Self::Tagged { .. } => "tagged",
            Self::Match { .. } => "match",
            Self::Fix { .. } => "fix",
            Self::FormatString(_) => "fmtstr",
            Self::Identifier(_) => "ident",
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
            Self::Tagged { value, .. } => value.inner.is_var_accessed(v),
            Self::Match { inp, cases } => {
                inp.inner.is_var_accessed(v)
                    || cases
                        .iter()
                        .any(|i| !i.pat.is_var_defined(v) && i.body.inner.is_var_accessed(v))
            }
            Self::FormatString(exs) => exs.iter().any(|i| i.inner.is_var_accessed(v)),
            Self::Identifier(id) => id == v,
            Self::Boolean(_) | Self::Integer(_) | Self::PureString(_) => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Case {
    pub pat: Pattern,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum Pattern {
    Identifier(Identifier),
    Tagged {
        key: Identifier,
        value: Box<Pattern>,
    },
    Record(Offsetted<BTreeMap<String, Pattern>>),
}

impl Pattern {
    /// checks if a variable is defined anywhere in the pattern
    pub fn is_var_defined(&self, v: &str) -> bool {
        match self {
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
    PErr(Offsetted<E>),
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
            PErr(Offsetted { offset, inner }) => PErr(Offsetted {
                offset,
                inner: inner.clone(),
            }),
        }
    }
}

impl<T, E> From<Option<Result<T, Offsetted<E>>>> for ParseResult<T, E> {
    fn from(x: Option<Result<T, Offsetted<E>>>) -> ParseResult<T, E> {
        match x {
            None => PNone,
            Some(Ok(y)) => POk(y),
            Some(Err(y)) => PErr(y),
        }
    }
}

impl<'a, T, E> From<Option<&'a Result<T, Offsetted<E>>>> for ParseResult<&'a T, &'a E> {
    fn from(x: Option<&'a Result<T, Offsetted<E>>>) -> ParseResult<&'a T, &'a E> {
        match x {
            None => PNone,
            Some(Ok(y)) => POk(y),
            Some(Err(Offsetted { offset, inner })) => PErr(Offsetted {
                offset: *offset,
                inner,
            }),
        }
    }
}

impl<T, E> From<Result<T, Offsetted<E>>> for ParseResult<T, E> {
    fn from(x: Result<T, Offsetted<E>>) -> ParseResult<T, E> {
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
            PErr(Offsetted { offset, inner }) => {
                return PErr(Offsetted {
                    offset,
                    inner: inner.into(),
                })
            }
            POk(x) => x,
        }
    }};
}

fn unexpect_eoe<T, E: Into<ErrorKind>>(offset: usize, x: ParseResult<T, E>) -> Result<T, Error> {
    match x {
        PNone => Err(Offsetted {
            offset,
            inner: ErrorKind::UnexpectedEoe,
        }),
        PErr(Offsetted { offset, inner }) => Err(Offsetted {
            offset,
            inner: inner.into(),
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
    })
}

fn expect_token_exact(
    super_offset: usize,
    lxr: &mut PeekLexer<'_>,
    tk: lex::TokenKind,
) -> Result<usize, Error> {
    expect_token_noeof(super_offset, lxr, |t| match t {
        lex::Token { inner, offset } if inner == tk => Ok(offset),
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
    Tagged { key: String, value: T },
}

impl From<DotIntermed<Expr>> for ExprKind {
    fn from(x: DotIntermed<Expr>) -> ExprKind {
        match x {
            DotIntermed::Identifier(x) => ExprKind::Identifier(x),
            DotIntermed::Record(rcd) => ExprKind::Record(rcd),
            DotIntermed::Tagged { key, value } => ExprKind::Tagged {
                key,
                value: Box::new(value),
            },
        }
    }
}

impl From<Offsetted<DotIntermed<Pattern>>> for Pattern {
    fn from(Offsetted { offset, inner }: Offsetted<DotIntermed<Pattern>>) -> Pattern {
        match inner {
            DotIntermed::Identifier(inner) => Pattern::Identifier(Offsetted {
                offset,
                inner: handle_wildcard(inner),
            }),
            DotIntermed::Record(inner) => Pattern::Record(Offsetted { offset, inner }),
            DotIntermed::Tagged { key, value } => Pattern::Tagged {
                key: Offsetted { offset, inner: key },
                value: Box::new(value),
            },
        }
    }
}

/// helper function for parsing dot terms, e.g. records and variants
/// * record: ` .{ key1: value1; key2: value2; } `
/// * tagged: `.key value1`
fn parse_dot_helper<'a, T, F>(
    super_offset: usize,
    lxr: &mut PeekLexer<'a>,
    f: F,
) -> ParseResult<T, ErrorKind>
where
    F: Fn(&mut PeekLexer<'a>) -> ParseResult<T, ErrorKind>,
    T: From<Offsetted<DotIntermed<T>>>,
{
    use lex::{Token, TokenKind as Tk};
    enum CaseTy {
        Record,
        Tag(String),
    }
    let Offsetted { inner, offset } = xtry!(expect_token_noeof(
        super_offset,
        lxr,
        |Token { inner, offset }| match inner {
            Tk::LcBracket => Ok(Offsetted {
                inner: CaseTy::Record,
                offset
            }),
            Tk::Identifier(x) => Ok(Offsetted {
                inner: CaseTy::Tag(x),
                offset
            }),
            _ => Err(Token { inner, offset }),
        }
    ));
    let intermed = match inner {
        CaseTy::Record => {
            let mut rcd = BTreeMap::new();
            while let Some(Ok(Token {
                offset,
                inner: Tk::Identifier(id),
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
                    |lex::Token { inner, offset }| {
                        match inner {
                            Tk::EqSym => Ok(true),
                            Tk::SemiColon => Ok(false),
                            _ => Err(lex::Token { inner, offset }),
                        }
                    }
                ));
                let value = if dcd {
                    let value = xtry!(unexpect_eoe(offset, f(lxr)));
                    let _ = xtry!(expect_token_exact(offset, lxr, Tk::SemiColon));
                    value
                } else {
                    (Offsetted {
                        offset,
                        inner: DotIntermed::Identifier(id.clone()),
                    })
                    .into()
                };
                use std::collections::btree_map::Entry;
                match rcd.entry(id) {
                    Entry::Vacant(v) => {
                        v.insert(value);
                    }
                    Entry::Occupied(occ) => {
                        return PErr(Offsetted {
                            offset,
                            inner: ErrorKind::DuplicateKey(occ.key().to_string()),
                        });
                    }
                }
            }
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::RcBracket));
            DotIntermed::Record(rcd)
        }
        CaseTy::Tag(key) => {
            let value = xtry!(unexpect_eoe(offset, f(lxr)));
            DotIntermed::Tagged { key, value }
        }
    };
    POk((Offsetted {
        offset,
        inner: intermed,
    })
    .into())
}

fn parse_pattern(lxr: &mut PeekLexer<'_>) -> ParseResult<Pattern, ErrorKind> {
    use lex::TokenKind as Tk;
    let Offsetted { offset, inner } = xtry!(lxr.next_if(|i| {
        if let Ok(Offsetted { inner, .. }) = i {
            matches!(inner, Tk::Identifier(_) | Tk::Dot)
        } else {
            true
        }
    }));
    match inner {
        Tk::Identifier(x) => POk(Pattern::Identifier(Offsetted {
            offset,
            inner: handle_wildcard(x),
        })),
        Tk::Dot => parse_dot_helper(offset, lxr, parse_pattern),
        _ => unreachable!(),
    }
}

fn parse_expr(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr, ErrorKind> {
    use lex::{Keyword as Kw, Token, TokenKind as Tk};
    let Token { mut offset, inner } = xtry!(lxr.next_if(|i| {
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
                } => Ok(Identifier { offset, inner }),
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
            let or_else = if let Some(Ok(Offsetted {
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
            let expr = xtry!(unexpect_eoe(offset, parse_expr(lxr)));
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
        Tk::LParen => {
            let Offsetted {
                inner,
                offset: new_offset,
            } = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::RParen));
            offset = new_offset;
            Ok(inner)
        }
        Tk::StringStart => {
            // handle format strings
            let mut parts = Vec::new();
            loop {
                if let Some(Ok(Token {
                    offset: s_offset,
                    inner: Tk::PureString(s),
                })) = lxr.next_if(|i| {
                    matches!(
                        i,
                        Ok(Token {
                            inner: Tk::PureString(_),
                            ..
                        })
                    )
                }) {
                    parts.push(Offsetted {
                        offset: s_offset,
                        inner: ExprKind::PureString(s),
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
        Tk::Dot => Ok(xtry!(parse_dot_helper(offset, lxr, parse_expr_greedy)).inner),
        _ => {
            return PErr(Offsetted {
                offset,
                inner: ErrorKind::UnexpectedToken(Offsetted { offset, inner }),
            });
        }
    };

    match inner {
        Ok(mut inner) => {
            // handle `.` chains
            while let Some(Ok(Offsetted {
                inner: Tk::Dot,
                offset: new_offset,
            })) = lxr.peek()
            {
                let new_offset = *new_offset;
                let _ = lxr.next();
                let key = xtry!(expect_token_noeof(new_offset, lxr, |t| match t {
                    Token {
                        inner: Tk::Identifier(id),
                        offset,
                    } => Ok(Offsetted { offset, inner: id }),
                    _ => Err(t),
                }));
                inner = ExprKind::Dot {
                    prim: Box::new(Offsetted { offset, inner }),
                    key,
                };
                offset = new_offset;
            }
            POk(Offsetted { offset, inner })
        }
        Err(inner) => PErr(Offsetted { offset, inner }),
    }
}

fn parse_expr_calls(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr, ErrorKind> {
    let Offsetted { mut inner, offset } = xtry!(parse_expr(lxr));
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
            prim: Box::new(Offsetted { offset, inner }),
            arg: Box::new(expr),
        };
    }
    POk(Offsetted { offset, inner })
}

fn parse_expr_greedy(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr, ErrorKind> {
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
        ret = Offsetted {
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
        };
    }
    POk(ret)
}

fn parse_block(super_offset: usize, lxr: &mut PeekLexer<'_>) -> Result<Block, Error> {
    use lex::TokenKind as Tk;

    // this handles errors and EOF
    let Offsetted {
        offset: fi_offset,
        inner: fi_inner,
    } = unexpect_eoe(super_offset, ParseResult::from(lxr.peek()).cloned_err())?;
    let fi_offset: usize = *fi_offset;

    let mut expect_close_brack = false;
    match fi_inner {
        Tk::LcBracket => {
            expect_close_brack = true;
            let _ = lxr.next();
        }
        Tk::RcBracket => {
            return Ok(Block::default());
        }
        Tk::RParen | Tk::SemiColon => {
            return Err(Offsetted {
                offset: fi_offset,
                inner: ErrorKind::UnexpectedToken(lxr.next().unwrap().unwrap()),
            });
        }
        _ => {}
    }

    let mut b = Block::default();

    loop {
        if let Some(Ok(Offsetted {
            inner: Tk::RcBracket,
            ..
        })) = lxr.peek()
        {
            if expect_close_brack {
                let _ = lxr.next();
            }
            // end of block
            break;
        }

        let expr = match parse_expr_greedy(lxr) {
            PNone if !expect_close_brack => {
                // no terminator
                break;
            }
            PNone => {
                return Err(Offsetted {
                    offset: fi_offset,
                    inner: ErrorKind::UnexpectedEoe,
                })
            }
            PErr(e) => return Err(e),
            POk(x) => x,
        };

        match lxr.peek() {
            None if expect_close_brack => {
                return Err(Offsetted {
                    offset: fi_offset,
                    inner: ErrorKind::UnexpectedEoe,
                })
            }
            None => {
                // got terminator
                b.term = Some(Box::new(expr));
            }
            Some(x) => {
                match x.as_ref().map_err(|e| e.clone())?.inner {
                    Tk::SemiColon => {
                        b.stmts.push(expr);
                        let _ = lxr.next();
                    }
                    Tk::RcBracket => {
                        // got terminator
                        b.term = Some(Box::new(expr));
                        if expect_close_brack {
                            let _ = lxr.next();
                        }
                        // end of block
                        break;
                    }
                    _ => {
                        return Err(Offsetted {
                            offset: fi_offset,
                            inner: ErrorKind::UnexpectedToken(lxr.next().unwrap().unwrap()),
                        });
                    }
                }
            }
        }
    }

    Ok(b)
}

#[inline]
pub fn parse(inp: &str) -> Result<Block, Error> {
    let mut lxr = lex::Lexer::new(inp).peekable();
    parse_block(0, &mut lxr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn block_term() {
        insta::assert_yaml_snapshot!(parse("{ a }").unwrap());
    }

    #[test]
    fn hello_world() {
        insta::assert_yaml_snapshot!(parse(r#"std.stdio.write("Hello world!\n");"#).unwrap());
    }

    #[test]
    fn fibo() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                let a = 1;
                let b = 1;
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                std.stdio.write "{fib 1 1 6}\m";
            "#
        )
        .unwrap());
    }

    #[test]
    fn complex_fstr() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                "{
                  let a = 1;
                  std.stdio.write("{a}\n");
                  a
                }"
            "#
        )
        .unwrap());
    }

    #[test]
    fn record() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                let id = \x x;
                .{
                   id = id;
                   id2 = id;
                   torben = id 1;
                }
            "#
        )
        .unwrap());
    }

    #[test]
    fn record_inherit() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                let id = \x x;
                let torben = id 1;
                .{
                   id;
                   id2 = id;
                   torben;
                }
            "#
        )
        .unwrap());
    }

    #[test]
    fn pipe() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                let id = \x x |> \y y;
                \z (id z |> \m std.plus m 1 |> \m std.minus m 2)
            "#
        )
        .unwrap());
    }

    #[test]
    fn op_update() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                .{
                  a = 1;
                  b = "what";
                  c = .{};
                } // .{
                  b = 50;
                  c = "now";
                }
            "#
        )
        .unwrap());
    }

    proptest::proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(4096))]

        #[test]
        fn doesnt_crash(s in "\\PC*") {
            let _ = parse(&s);
        }
    }
}
