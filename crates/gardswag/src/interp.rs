use gardswag_syntax::{self as synt, Block, Expr};
use gardswag_varstack::VarStack;
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub enum Builtin {
    Plus,
    Minus,
    Mult,
    Eq,
    Leq,
    Not,
    StdioWrite,
}

impl Builtin {
    fn argc(self) -> usize {
        match self {
            Self::Plus | Self::Minus | Self::Mult | Self::Eq | Self::Leq => 2,
            Self::Not | Self::StdioWrite => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, serde::Serialize)]
#[must_use = "the interpreter shouldn't discard values"]
pub enum Value<'a> {
    Unit,
    Boolean(bool),
    Integer(i32),
    PureString(String),

    Record(BTreeMap<&'a str, Value<'a>>),

    Tagged {
        key: &'a str,
        value: Box<Value<'a>>,
    },

    Builtin {
        f: Builtin,
        args: Vec<Value<'a>>,
    },
    Lambda {
        argname: &'a str,
        f: &'a Expr,
        stacksave: BTreeMap<String, Value<'a>>,
    },
    FixLambda {
        argname: &'a str,
        f: &'a Expr,
    },
}

impl From<Builtin> for Value<'static> {
    fn from(x: Builtin) -> Self {
        Value::Builtin {
            f: x,
            args: Vec::new(),
        }
    }
}

pub fn run_block<'a, 's>(blk: &'a Block, stack: &'s VarStack<'s, Value<'a>>) -> Value<'a> {
    for i in &blk.stmts {
        let _ = run(i, stack);
    }
    if let Some(i) = &blk.term {
        run(i, stack)
    } else {
        Value::Unit
    }
}

fn run_stacksave<'a, 's, 's3, I, S>(
    expr: &'a Expr,
    stack: &'s VarStack<'s, Value<'a>>,
    mut stacksave: I,
) -> Value<'a>
where
    I: Iterator<Item = (S, Value<'a>)>,
    S: AsRef<str>,
{
    match stacksave.next() {
        Some((name, value)) => run_stacksave(
            expr,
            &VarStack {
                parent: Some(stack),
                name: name.as_ref(),
                value,
            },
            stacksave,
        ),
        None => run(expr, stack),
    }
}

/// this function has a difficult signature,
/// because we really want to avoid all unnecessary allocations,
/// because it otherwise would be prohibitively costly...
fn run_pat<'a, 'b>(
    coll: &mut BTreeMap<&'a str, &'b Value<'a>>,
    pat: &'a synt::Pattern,
    inp: &'b Value<'a>,
) -> Option<()> {
    tracing::trace!("pat {:?}", pat);

    use synt::Pattern;

    match pat {
        Pattern::Identifier(i) => {
            coll.insert(&*i.inner, inp);
            Some(())
        }
        Pattern::Tagged { key, value } => match inp {
            Value::Tagged {
                key: got_key,
                value: got_value,
            } if key.inner == *got_key => run_pat(coll, value, got_value),
            _ => None,
        },
        Pattern::Record(synt::Offsetted { inner: rcpat, .. }) => match inp {
            Value::Record(rcm) if rcpat.len() <= rcm.len() => {
                for (key, value) in rcpat {
                    let got_value = rcm.get(&**key)?;
                    run_pat(coll, value, got_value)?;
                }
                Some(())
            }
            _ => None,
        },
    }
}

pub fn run<'a, 's>(expr: &'a Expr, stack: &'s VarStack<'s, Value<'a>>) -> Value<'a> {
    tracing::debug!("expr@{} : {}", expr.offset, expr.inner.typ());
    tracing::trace!("stack={:?}", stack);
    use gardswag_syntax::ExprKind as Ek;
    let res = match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let v_rhs = run(rhs, stack);
            run_block(
                rest,
                &VarStack {
                    parent: Some(stack),
                    name: &lhs.inner,
                    value: v_rhs,
                },
            )
        }
        Ek::Block(blk) => run_block(blk, stack),
        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let v_cond = match run(cond, stack) {
                Value::Boolean(x) => x,
                x => panic!("invalid if condition: {:?}", x),
            };
            run_block(if v_cond { then } else { or_else }, stack)
        }
        Ek::Lambda { arg, body } => {
            let mut stacksave = std::collections::BTreeMap::new();
            for (k, v) in stack.iter() {
                if stacksave.contains_key(k) || k == arg || !body.inner.is_var_accessed(k) {
                    continue;
                }
                stacksave.insert(k.to_string(), v.clone());
            }

            Value::Lambda {
                argname: arg,
                f: body,
                stacksave,
            }
        }
        Ek::Call { prim, arg } => {
            let v_arg = run(arg, stack);
            let v_prim = run(prim, stack);
            match v_prim {
                Value::Builtin { f, mut args } => {
                    args.push(v_arg);
                    if f.argc() > args.len() {
                        Value::Builtin { f, args }
                    } else {
                        assert_eq!(f.argc(), args.len());
                        use Builtin as Bi;
                        match f {
                            Bi::Plus => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                (Value::Integer(a), Value::Integer(b)) => Value::Integer(*a + *b),
                                _ => panic!("std.plus called with {:?}", args),
                            },
                            Bi::Minus => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                (Value::Integer(a), Value::Integer(b)) => Value::Integer(*a - *b),
                                _ => panic!("std.minus called with {:?}", args),
                            },
                            Bi::Mult => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                (Value::Integer(a), Value::Integer(b)) => Value::Integer(*a * *b),
                                _ => panic!("std.minus called with {:?}", args),
                            },
                            Bi::Leq => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                (Value::Integer(a), Value::Integer(b)) => Value::Boolean(*a <= *b),
                                _ => panic!("std.minus called with {:?}", args),
                            },
                            Bi::Eq => Value::Boolean(args.get(0) == args.get(1)),
                            Bi::Not => match args.get(0).unwrap() {
                                Value::Boolean(b) => Value::Boolean(!*b),
                                a => panic!("std.not called with {:?}", a),
                            },
                            Bi::StdioWrite => {
                                match args.get(0).unwrap() {
                                    Value::PureString(s) => print!("{}", s),
                                    x => panic!("std.stdio.write called with {:?}", x),
                                }
                                Value::Unit
                            }
                        }
                    }
                }
                Value::Lambda {
                    argname,
                    f,
                    stacksave,
                } => run_stacksave(
                    f,
                    &VarStack {
                        parent: Some(stack),
                        name: argname,
                        value: v_arg,
                    },
                    stacksave.into_iter(),
                ),
                f => panic!("called non-callable {:?} with argument {:?}", f, v_arg),
            }
        }
        Ek::Dot { prim, key } => match run(prim, stack) {
            Value::Record(mut rcm) => rcm
                .remove(&*key.inner)
                .expect("unable to find key in record"),
            x => panic!("called .{} on non-record {:?}", key.inner, x),
        },
        Ek::Fix { arg, body } => run(
            body,
            &VarStack {
                parent: Some(stack),
                name: arg,
                value: Value::FixLambda {
                    argname: arg,
                    f: body,
                },
            },
        ),
        Ek::FormatString(fsts) => {
            let mut r = String::new();
            for i in fsts {
                use core::fmt::Write;
                match run(i, stack) {
                    Value::PureString(s) => r += &s,
                    Value::Integer(i) => write!(&mut r, "{}", i).unwrap(),
                    Value::Boolean(b) => write!(&mut r, "_{}", if b { '1' } else { '0' }).unwrap(),
                    Value::Unit => {}
                    x => panic!("invoked format' stringify on non-stringifyable {:?}", x),
                }
            }
            Value::PureString(r)
        }
        Ek::Record(rcde) => {
            let mut rcd = BTreeMap::new();
            for (k, v) in rcde {
                rcd.insert(&**k, run(v, stack));
            }
            Value::Record(rcd)
        }
        Ek::Update { orig, ovrd } => {
            let v_orig = run(orig, stack);
            match run(ovrd, stack) {
                Value::Record(mut rcd) => {
                    match v_orig {
                        Value::Record(rcd_pull) => {
                            for (k, v) in rcd_pull.into_iter() {
                                if let std::collections::btree_map::Entry::Vacant(vac) =
                                    rcd.entry(k)
                                {
                                    vac.insert(v);
                                }
                            }
                        }
                        _ => panic!("invoked record update (lhs) on non-record {:?}", v_orig),
                    }
                    Value::Record(rcd)
                }
                v => panic!("invoked record update (rhs) on non-record {:?}", v),
            }
        }
        Ek::Tagged { key, value } => Value::Tagged {
            key: &*key,
            value: Box::new(run(value, stack)),
        },
        Ek::Match { inp, cases } => {
            let v_inp = run(inp, stack);
            let mut res = None;
            for i in cases {
                let mut coll = Default::default();
                if let Some(()) = run_pat(&mut coll, &i.pat, &v_inp) {
                    res = Some(run_stacksave(
                        &i.body,
                        stack,
                        coll.into_iter().map(|(key, value)| (key, value.clone())),
                    ));
                    break;
                }
            }
            res.expect("disformed match")
        }
        Ek::Identifier(id) => {
            let r = stack.find(id).unwrap().clone();
            if let Value::FixLambda { argname, f } = r {
                run(
                    f,
                    &VarStack {
                        parent: Some(stack),
                        name: argname,
                        value: Value::FixLambda { argname, f },
                    },
                )
            } else {
                r
            }
        }
        Ek::Boolean(b) => Value::Boolean(*b),
        Ek::Integer(i) => Value::Integer(*i),
        Ek::PureString(s) => Value::PureString(s.clone()),
    };
    tracing::debug!(
        "expr@{} : {} : res={:?}",
        expr.offset,
        expr.inner.typ(),
        res
    );
    res
}
