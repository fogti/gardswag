use gardswag_syntax::{Block as SynBlock, ExprKind, Offsetted};
use serde::{Deserialize, Serialize};
use string_interner::{symbol::SymbolU32 as Symbol, StringInterner};
use tracing::trace;

#[derive(Debug, Deserialize, Serialize)]
pub struct Module {
    pub bbs: Vec<BasicBlock>,
    pub tg: gardswag_typesys::Scheme,
    pub interner: StringInterner,
}

impl Module {
    pub fn push_instr(&mut self, instr: VmInstr) {
        self.bbs.last_mut().unwrap().instrs.push(instr);
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum JumpDst {
    /// stop execution
    Halt,
    /// pop value from call stack and return there
    Return,
    /// continue at specified basic block
    Continue(usize),
}

impl Default for JumpDst {
    #[inline(always)]
    fn default() -> Self {
        Self::Halt
    }
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct BasicBlock {
    pub instrs: Vec<VmInstr>,

    // if set, this pops a value from the stack
    // and will jump to the block with the specified index
    // if the top value evaluates to false
    pub condf_jump: Option<usize>,

    // if true: (invoke)
    //   takes the top-level stack element (argument) and the previous stack element (closure)
    //   and produces the return value
    pub invoke: bool,

    // if set, and no conditional jump happened,
    // the execution will continue at the specified block index
    pub jump: JumpDst,
}

#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub enum LiteralExpr {
    Unit,
    Boolean(bool),
    Integer(i32),
    PureString(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Deserialize, Serialize)]
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
    #[inline]
    pub fn argc(&self) -> u8 {
        match self {
            Self::Plus | Self::Minus | Self::Mult | Self::Eq | Self::Leq => 2,
            Self::Not | Self::StdioWrite => 1,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum VmInstr {
    // drops the top-level stack element
    Discard,

    // pushes a simple value onto the stack
    Push(LiteralExpr),

    // pushes a builtin closure onto the stack
    Builtin(Builtin),

    // pushes a lambda bb reference onto the stack
    Lambda(usize),

    // takes the top-level stack element and assigns it to the stack element at -$0
    Assign(usize),

    // clones the stack element at -$0 and pushes it onto the stack
    Lift(usize),

    // swaps the two topmost elements on the stack
    Swap,

    // Dot(elem) :: record -> record.$elem
    //
    // takes the top-level stack element (must be a record)
    // and pushes the subelement with name $elem.
    Dot(Symbol),

    // takes and converts the top-level element to a string,
    // then takes the next element, and appends the top-level element to it,
    // the pushes the result.
    StringAppend,

    // takes the top #$0 elements from the stack (first one = top-level)
    // and builds a record out of them, then pushes the record
    BuildRecord(Vec<Symbol>),
}

#[derive(Clone, Copy, Debug)]
pub struct VarStack<'a> {
    pub parent: Option<&'a VarStack<'a>>,
    pub last: &'a str,
}

impl VarStack<'_> {
    pub fn find(self, x: &str) -> Option<usize> {
        if self.last == x {
            Some(0)
        } else if let Some(parent) = self.parent {
            parent.find(x).map(|y| y + 1)
        } else {
            None
        }
    }
}

pub trait CodeGen {
    fn ser_to_bytecode(&self, modul: &mut Module, vstk: Option<VarStack<'_>>);
}

impl<T: CodeGen> CodeGen for Offsetted<T> {
    #[inline(always)]
    fn ser_to_bytecode(&self, modul: &mut Module, vstk: Option<VarStack<'_>>) {
        self.inner.ser_to_bytecode(modul, vstk);
    }
}

impl CodeGen for SynBlock {
    fn ser_to_bytecode(&self, modul: &mut Module, vstk: Option<VarStack<'_>>) {
        for i in &self.stmts {
            i.ser_to_bytecode(modul, vstk);
            let y = modul.bbs.last_mut().unwrap();
            if let Some(VmInstr::Push(_)) = y.instrs.last() {
                y.instrs.pop();
            } else {
                y.instrs.push(VmInstr::Discard);
            }
        }
        if let Some(x) = &self.term {
            x.ser_to_bytecode(modul, vstk);
        } else {
            modul.push_instr(VmInstr::Push(LiteralExpr::Unit));
        }
    }
}

impl CodeGen for ExprKind {
    fn ser_to_bytecode(&self, modul: &mut Module, vstk: Option<VarStack<'_>>) {
        use ExprKind as Ek;
        match self {
            Ek::Let { lhs, rhs, rest } => {
                rhs.ser_to_bytecode(modul, vstk);
                rest.ser_to_bytecode(
                    modul,
                    Some(VarStack {
                        parent: vstk.as_ref(),
                        last: &lhs.inner,
                    }),
                );
                modul.push_instr(VmInstr::Swap);
                modul.push_instr(VmInstr::Discard);
            }
            Ek::Assign { lhs, rhs } => {
                let lid = vstk.unwrap().find(&lhs.inner).unwrap();
                rhs.ser_to_bytecode(modul, vstk);
                modul.push_instr(VmInstr::Assign(lid));
            }
            Ek::Block(block) => block.ser_to_bytecode(modul, vstk),
            Ek::If {
                cond,
                then,
                or_else,
            } => {
                trace!("bb={}: if-cond {:?}", modul.bbs.len() - 1, cond);
                cond.ser_to_bytecode(modul, vstk);
                let cond_bb = modul.bbs.len() - 1;
                trace!("bb={}: if-cond /end", cond_bb);
                modul.bbs.last_mut().unwrap().jump = JumpDst::Continue(modul.bbs.len());

                trace!("bb={}: if-then", modul.bbs.len());
                modul.bbs.push(Default::default());
                then.ser_to_bytecode(modul, vstk);
                let next_bb = modul.bbs.len();
                let then_bb = next_bb - 1;
                modul.bbs[cond_bb].condf_jump = Some(next_bb);

                trace!("bb={}: if-else", modul.bbs.len());
                modul.bbs.push(Default::default());
                or_else.ser_to_bytecode(modul, vstk);
                let next_bb = JumpDst::Continue(modul.bbs.len());
                modul.bbs.last_mut().unwrap().jump = next_bb;
                modul.bbs[then_bb].jump = next_bb;
                modul.bbs.push(Default::default());
                trace!("bb={}: endif", modul.bbs.len());
            }
            Ek::Lambda { arg, body } => {
                let orig_bb = modul.bbs.len() - 1;
                trace!("bb={} lambda", modul.bbs.len());
                modul.push_instr(VmInstr::Lambda(orig_bb + 1));
                modul.bbs.push(Default::default());
                body.ser_to_bytecode(
                    modul,
                    Some(VarStack {
                        parent: vstk.as_ref(),
                        last: &arg.inner,
                    }),
                );
                modul.push_instr(VmInstr::Swap);
                modul.push_instr(VmInstr::Discard);
                modul.bbs.last_mut().unwrap().jump = JumpDst::Return;
                let next_bb = JumpDst::Continue(modul.bbs.len());
                modul.bbs[orig_bb].jump = next_bb;
                trace!("bb={} lambda end", modul.bbs.len());
                modul.bbs.push(Default::default());
            }
            Ek::Call { prim, args } => {
                let mut args2: Vec<_> = args.iter().rev().cloned().collect();
                let arg = args2.pop().unwrap();
                prim.ser_to_bytecode(modul, vstk);
                arg.ser_to_bytecode(modul, vstk);
                {
                    let bbscnt = modul.bbs.len();
                    let mut lbb = modul.bbs.last_mut().unwrap();
                    lbb.invoke = true;
                    lbb.jump = JumpDst::Continue(bbscnt);
                }
                modul.bbs.push(Default::default());

                while let Some(arg) = args2.pop() {
                    arg.ser_to_bytecode(modul, vstk);
                    {
                        let bbscnt = modul.bbs.len();
                        let mut lbb = modul.bbs.last_mut().unwrap();
                        lbb.invoke = true;
                        lbb.jump = JumpDst::Continue(bbscnt);
                    }
                    modul.bbs.push(Default::default());
                }
            }
            Ek::Dot { prim, key } => {
                prim.ser_to_bytecode(modul, vstk);
                let s_key = modul.interner.get_or_intern(&key.inner);
                modul.push_instr(VmInstr::Dot(s_key));
            }
            Ek::Fix(e) => {
                e.ser_to_bytecode(modul, vstk);
                // this duplicates the top-level stack element
                modul.push_instr(VmInstr::Lift(0));
                // which then gets invoked with itself as argument
                {
                    let bbscnt = modul.bbs.len();
                    let mut lbb = modul.bbs.last_mut().unwrap();
                    lbb.invoke = true;
                    lbb.jump = JumpDst::Continue(bbscnt);
                }
                modul.bbs.push(Default::default());
            }
            Ek::FormatString(fmts) => {
                modul.push_instr(VmInstr::Push(LiteralExpr::PureString(String::new())));
                for i in fmts {
                    i.ser_to_bytecode(modul, vstk);
                    modul.push_instr(VmInstr::StringAppend);
                }
            }
            Ek::Record(rcm) => {
                let mut rcks = Vec::new();
                for (k, v) in rcm.iter() {
                    v.ser_to_bytecode(modul, vstk);
                    rcks.push(modul.interner.get_or_intern(k));
                }
                rcks = rcks.into_iter().rev().collect();
                modul.push_instr(VmInstr::BuildRecord(rcks));
            }
            Ek::Identifier(id) => {
                modul.push_instr(VmInstr::Lift(vstk.unwrap().find(&id.inner).unwrap()));
            }
            Ek::Boolean(x) => {
                modul.push_instr(VmInstr::Push(LiteralExpr::Boolean(*x)));
            }
            Ek::Integer(x) => {
                modul.push_instr(VmInstr::Push(LiteralExpr::Integer(*x)));
            }
            Ek::PureString(x) => {
                modul.push_instr(VmInstr::Push(LiteralExpr::PureString(x.clone())));
            }
        }
    }
}
