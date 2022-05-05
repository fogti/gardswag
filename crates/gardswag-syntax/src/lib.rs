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

    #[error("unexpected token @{}: {:?}", .0.offset, .0.inner)]
    UnexpectedToken(lex::Token),
}

pub type Identifier = Offsetted<String>;
pub type Expr = Offsetted<ExprKind>;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct Block {
    pub stmts: Vec<Expr>,
    pub term: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum ExprKind {
    Let {
        lhs: Identifier,
        rhs: Box<Expr>,
        rest: Block,
    },
    // assignment is not allowed to change types
    Assign {
        lhs: Identifier,
        rhs: Box<Expr>,
    },
    Block(Block),
    Loop(Block),

    If {
        cond: Box<Expr>,
        then: Block,
        or_else: Block,
    },
    Break(Option<Box<Expr>>),

    Call {
        prim: Box<Expr>,
        args: Vec<Expr>,
    },
    Dot {
        prim: Box<Expr>,
        key: Identifier,
    },

    Identifier(Identifier),
    Integer(i32),
    PureString(String),
    FormatString(Vec<Expr>),
    Std,
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

fn parse_expr(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr, ErrorKind> {
    use lex::{Keyword as Kw, Token, TokenKind as Tk};
    let Token { mut offset, inner } = xtry!(lxr.next_if(|i| {
        if let Ok(Token { inner, .. }) = i {
            !matches!(
                inner,
                Tk::RcBracket | Tk::RParen | Tk::SemiColon | Tk::StringEnd
            )
        } else {
            true
        }
    }));
    let inner = match inner {
        Tk::Keyword(Kw::Let) => {
            let lhs = xtry!(expect_token_noeof(offset, lxr, |t| match t {
                Token {
                    offset,
                    inner: Tk::Identifier(inner),
                } => Ok(Identifier { offset, inner }),
                _ => Err(t),
            }));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::EqSym));
            let rhs = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
            let blk_offset = xtry!(expect_token_exact(offset, lxr, Tk::SemiColon));
            let rest = if lxr.peek().is_none() {
                Block::default()
            } else {
                xtry!(parse_block(blk_offset, lxr))
            };
            Ok(ExprKind::Let {
                lhs,
                rhs: Box::new(rhs),
                rest,
            })
        }
        Tk::Keyword(Kw::Loop) => {
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::LcBracket));
            let block = xtry!(parse_block(offset, lxr));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::RcBracket));
            Ok(ExprKind::Loop(block))
        }
        Tk::Keyword(Kw::Break) => Ok(ExprKind::Break(match parse_expr(lxr) {
            PNone => None,
            POk(x) => Some(Box::new(x)),
            PErr(e) => return PErr(e),
        })),
        Tk::Keyword(Kw::If) => {
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::LParen));
            let cond = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
            let _ = xtry!(expect_token_exact(offset, lxr, Tk::RParen));
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
        Tk::Identifier(id) => {
            let id = Offsetted { offset, inner: id };
            Ok(
                if let Some(Ok(Offsetted {
                    inner: Tk::EqSym, ..
                })) = lxr.peek()
                {
                    let _ = lxr.next();
                    let rhs = xtry!(unexpect_eoe(offset, parse_expr_greedy(lxr)));
                    ExprKind::Assign {
                        lhs: id,
                        rhs: Box::new(rhs),
                    }
                } else {
                    ExprKind::Identifier(id)
                },
            )
        }
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
                    if let Ok(Token { inner, .. }) = i {
                        matches!(inner, Tk::PureString(_))
                    } else {
                        false
                    }
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

fn parse_expr_greedy(lxr: &mut PeekLexer<'_>) -> ParseResult<Expr, ErrorKind> {
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
        if let ExprKind::Call { ref mut args, .. } = &mut inner {
            args.push(expr);
        } else {
            inner = ExprKind::Call {
                prim: Box::new(Offsetted { offset, inner }),
                args: vec![expr],
            };
        }
    }
    POk(Offsetted { offset, inner })
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

    // like the fibo example. but without string literals
    #[test]
    fn fibo_simpler() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                let a = 1;
                let b = 1;
                loop {
                    if (std.leq b a) {
                        break;
                    } {};
                    a = std.plus a b;
                    std.stdio.write(a);
                    b = std.plus a b;
                    std.stdio.write(b);
                }
            "#
        )
        .unwrap());
    }

    #[test]
    fn fibo() {
        insta::assert_yaml_snapshot!(parse(
            r#"
                let a = 1;
                let b = 1;
                loop {
                    if (std.leq b a) {
                        break;
                    } {};
                    a = std.plus a b;
                    std.stdio.write("{a}\n");
                    b = std.plus a b;
                    std.stdio.write("{b}\n");
                }
            "#
        )
        .unwrap());
    }
}
