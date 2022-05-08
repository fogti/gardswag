use crate::bytecode::{Builtin, LiteralExpr, Module, VmInstr};
use core::fmt;
use std::collections::BTreeMap;
use string_interner::symbol::SymbolU32 as Symbol;

#[derive(Clone, PartialEq)]
pub enum Value {
    Literal(LiteralExpr),
    Record(BTreeMap<Symbol, Value>),

    Builtin { f: Builtin, args: Vec<Value> },
    Lambda { f: usize, stacksave: Vec<Value> },
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Literal(lit) => write!(f, "{:?}", lit),
            Value::Builtin { f: blti, args } => {
                write!(f, "Builtin::{:?}{:?}", blti, args)
            }
            Value::Lambda { f: bb, stacksave } => {
                write!(f, "Lambda@{}(saved stack ={:?})", bb, stacksave)
            }
            Value::Record(rcm) => f
                .debug_map()
                .entries(rcm.iter().map(|(k, v)| {
                    use string_interner::Symbol as _;
                    (k.to_usize(), v)
                }))
                .finish(),
        }
    }
}

pub struct VmState<'a> {
    pub modul: &'a Module,
    stack: Vec<Value>,
}

impl<'a> VmState<'a> {
    pub fn new(modul: &'a Module) -> Self {
        Self {
            modul,
            stack: Vec::new(),
        }
    }
}

#[derive(Debug)]
struct BbsItem {
    nextbb: usize,
    killstackspan: core::ops::Range<usize>,
}

impl VmState<'_> {
    pub fn run(&mut self) -> Option<Value> {
        let mut bbstk = vec![BbsItem {
            nextbb: 0,
            killstackspan: 0..0,
        }];
        while let Some(curbb) = bbstk.pop() {
            tracing::debug!(?curbb, ?bbstk, "BB stack");
            tracing::trace!("with value stack: {:?}", self.stack);
            let bbr = self.modul.bbs.get(curbb.nextbb).unwrap();

            use crate::bytecode::JumpDst;

            for i in &bbr.instrs {
                tracing::trace!("instr {:?}", i);
                match i {
                    VmInstr::Discard => {
                        self.stack.pop().expect("discard failed");
                    }
                    VmInstr::Push(lite) => {
                        self.stack.push(Value::Literal(lite.clone()));
                    }
                    VmInstr::Builtin(f) => {
                        self.stack.push(Value::Builtin {
                            f: *f,
                            args: Vec::new(),
                        });
                    }
                    VmInstr::Lambda(lambb) => {
                        // TODO: this is too expensive -> try HVM-dup instead
                        let stacksave = self.stack.clone();
                        self.stack.push(Value::Lambda {
                            f: *lambb,
                            stacksave,
                        });
                    }
                    VmInstr::Assign(up) => {
                        let val = self.stack.pop().unwrap();
                        let trgstkpos = self.stack.len() - (1 + up);
                        self.stack[trgstkpos] = val;
                    }
                    VmInstr::Lift(up) => {
                        let srcstkpos = self.stack.len() - (1 + up);
                        // TODO: HVM-style dup management
                        // see also: https://github.com/Kindelia/HVM/blob/master/HOW.md
                        let val = self.stack[srcstkpos].clone();
                        self.stack.push(val);
                    }
                    VmInstr::Swap => {
                        let stkspltp = self.stack.len() - 1;
                        let (a, b) = self.stack.split_at_mut(stkspltp);
                        core::mem::swap(a.last_mut().unwrap(), &mut b[0]);
                    }
                    VmInstr::Dot(elem) => match self.stack.pop().unwrap() {
                        Value::Record(mut rcm) => self.stack.push(rcm.remove(elem).unwrap()),
                        x => panic!(
                            ".{} called on non-record {:?}",
                            self.modul.interner.resolve(*elem).unwrap(),
                            x
                        ),
                    },
                    VmInstr::StringAppend => {
                        use LiteralExpr as LitEx;
                        let b = match self.stack.pop().unwrap() {
                            Value::Literal(LitEx::Unit) => String::new(),
                            Value::Literal(LitEx::Boolean(true)) => "_1".to_string(),
                            Value::Literal(LitEx::Boolean(false)) => "_0".to_string(),
                            Value::Literal(LitEx::Integer(i)) => i.to_string(),
                            Value::Literal(LitEx::PureString(s)) => s,
                            x => panic!("stringify called on invalid value {:?}", x),
                        };
                        let mut a = match self.stack.pop().unwrap() {
                            Value::Literal(LitEx::PureString(s)) => s,
                            x => panic!("stringify called on non-string {:?}", x),
                        };
                        a += &b;
                        self.stack.push(Value::Literal(LitEx::PureString(a)));
                    }
                    VmInstr::BuildRecord(rcdesc) => {
                        let mut rcrd = BTreeMap::new();
                        for i in rcdesc {
                            let val = self.stack.pop().unwrap();
                            rcrd.insert(*i, val);
                        }
                        self.stack.push(Value::Record(rcrd));
                    }
                }
            }
            if let Some(x) = bbr.condf_jump {
                let condres = match self.stack.pop().unwrap() {
                    Value::Literal(LiteralExpr::Boolean(b)) => b,
                    y => panic!("`if` called with invalid condition {:?}", y),
                };
                if condres {
                    bbstk.push(BbsItem {
                        nextbb: x,
                        killstackspan: curbb.killstackspan,
                    });
                    continue;
                }
            }
            match bbr.jump {
                JumpDst::Halt => {
                    self.stack.drain(curbb.killstackspan);
                    bbstk.clear();
                }
                JumpDst::Return => {
                    self.stack.drain(curbb.killstackspan);
                }
                JumpDst::Continue(nextbb) => {
                    bbstk.push(BbsItem {
                        nextbb,
                        killstackspan: curbb.killstackspan,
                    });
                }
            }
            if bbr.invoke {
                tracing::trace!("run invoke on stack={:?}", self.stack);
                let arg = self.stack.pop().unwrap();
                match self.stack.pop().unwrap() {
                    Value::Builtin { f, mut args } => {
                        assert!(usize::from(f.argc()) > args.len());
                        args.push(arg);
                        self.stack.push(if usize::from(f.argc()) > args.len() {
                            // needs more arguments
                            Value::Builtin { f, args }
                        } else {
                            // has all required arguments
                            let mut args = args.into_iter();
                            use LiteralExpr as LitEx;
                            match f {
                                Builtin::Plus => {
                                    match (args.next().unwrap(), args.next().unwrap()) {
                                        (
                                            Value::Literal(LitEx::Integer(a)),
                                            Value::Literal(LitEx::Integer(b)),
                                        ) => Value::Literal(LitEx::Integer(a + b)),
                                        (a, b) => panic!(
                                            "std.plus called with invalid args [{:?}, {:?}]",
                                            a, b
                                        ),
                                    }
                                }
                                Builtin::Minus => {
                                    match (args.next().unwrap(), args.next().unwrap()) {
                                        (
                                            Value::Literal(LitEx::Integer(a)),
                                            Value::Literal(LitEx::Integer(b)),
                                        ) => Value::Literal(LitEx::Integer(a - b)),
                                        (a, b) => panic!(
                                            "std.minus called with invalid args [{:?}, {:?}]",
                                            a, b
                                        ),
                                    }
                                }
                                Builtin::Mult => {
                                    match (args.next().unwrap(), args.next().unwrap()) {
                                        (
                                            Value::Literal(LitEx::Integer(a)),
                                            Value::Literal(LitEx::Integer(b)),
                                        ) => Value::Literal(LitEx::Integer(a * b)),
                                        (a, b) => panic!(
                                            "std.mult called with invalid args [{:?}, {:?}]",
                                            a, b
                                        ),
                                    }
                                }
                                Builtin::Leq => {
                                    match (args.next().unwrap(), args.next().unwrap()) {
                                        (
                                            Value::Literal(LitEx::Integer(a)),
                                            Value::Literal(LitEx::Integer(b)),
                                        ) => Value::Literal(LitEx::Boolean(a <= b)),
                                        (a, b) => panic!(
                                            "std.leq called with invalid args [{:?}, {:?}]",
                                            a, b
                                        ),
                                    }
                                }
                                Builtin::Eq => Value::Literal(LitEx::Boolean(
                                    args.next().unwrap() == args.next().unwrap(),
                                )),
                                Builtin::Not => match args.next().unwrap() {
                                    Value::Literal(LitEx::Boolean(x)) => {
                                        Value::Literal(LitEx::Boolean(!x))
                                    }
                                    a => panic!("std.not called with invalid args [{:?}]", a),
                                },
                                Builtin::StdioWrite => match args.next().unwrap() {
                                    Value::Literal(LitEx::PureString(x)) => {
                                        print!("{}", x);
                                        Value::Literal(LitEx::Unit)
                                    }
                                    a => {
                                        panic!("std.stdio.write called with invalid args [{:?}]", a)
                                    }
                                },
                            }
                        });
                    }
                    Value::Lambda { f, stacksave } => {
                        let orig_stkl = self.stack.len();
                        self.stack.extend(stacksave);
                        let after_stksave = self.stack.len();
                        self.stack.push(arg);
                        bbstk.push(BbsItem {
                            nextbb: f,
                            killstackspan: orig_stkl..after_stksave,
                        });
                    }
                    val => panic!(
                        "called non-callable {{{:?}}} with invalid arg {{{:?}}}",
                        val, arg
                    ),
                }
            }
        }

        let ret = self.stack.pop();
        if !self.stack.is_empty() {
            tracing::warn!("leftover stack contents: {:?}", self.stack);
            self.stack.clear();
        }
        ret
    }
}
