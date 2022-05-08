use std::path::PathBuf;
use tracing::debug;

mod bytecode;
mod infer;
mod interp;

#[derive(Clone, PartialEq, clap::ArgEnum)]
enum Mode {
    /// check if the file passes parsing + type-check
    Check,

    /// perform checks, then execute the expression
    Run,
}

#[derive(clap::Parser)]
#[clap(version)]
struct Args {
    /// file to interpret
    #[clap(short, long)]
    file: PathBuf,

    /// specify the mode
    #[clap(arg_enum, short = 'm', long)]
    mode: Mode,

    #[clap(long)]
    print_bytecode: bool,
}

fn mk_env_std(ctx: &mut gardswag_typesys::Context) -> gardswag_typesys::Scheme {
    use gardswag_typesys::{Scheme as TyScheme, Ty, TyLit};

    macro_rules! tl {
        (int) => {{
            Ty::Literal(TyLit::Int)
        }};
        (bool) => {{
            Ty::Literal(TyLit::Bool)
        }};
        (str) => {{
            Ty::Literal(TyLit::String)
        }};
        (()) => {{
            Ty::Literal(TyLit::Unit)
        }};
    }
    macro_rules! ta {
        ($a:expr $(=> $b:expr)*) => {{
            let mut x = vec![$a];
            $(x.push($b);)+
            let mut it = x.into_iter().rev();
            let mut y = it.next().unwrap();
            for i in it {
                y = Ty::Arrow(Box::new(i), Box::new(y));
            }
            y
        }}
    }
    macro_rules! tr {
        ({ $($key:ident: $value:expr),* $(,)? }) => {{
            Ty::Record([
                $((stringify!($key).to_string(), $value)),*
            ].into_iter().collect())
        }};
    }

    let tyvars: Vec<usize> = (0..2).map(|_| ctx.fresh_tyvars.next().unwrap()).collect();
    let gtv = |i| Ty::Var(tyvars[i]);

    let t = tr!({
        plus: ta!(tl!(int) => tl!(int) => tl!(int)),
        minus: ta!(tl!(int) => tl!(int) => tl!(int)),
        mult: ta!(tl!(int) => tl!(int) => tl!(int)),
        eq: ta!(gtv(0) => gtv(1) => tl!(bool)),
        leq: ta!(tl!(int) => tl!(int) => tl!(bool)),
        not: ta!(tl!(bool) => tl!(bool)),
        stdio: tr!({
            write: ta!(tl!(str) => tl!(())),
        }),
    });

    TyScheme {
        forall: tyvars
            .into_iter()
            .map(|_| (ctx.fresh_tyvars.next().unwrap(), Default::default()))
            .collect(),
        t,
    }
}

fn main() {
    let args = <Args as clap::Parser>::parse();

    let dat = std::fs::read(&args.file).expect("unable to read file");
    let dat = String::from_utf8(dat).expect("file doesn't contain UTF-8 text");

    tracing_subscriber::fmt::init();

    let parsed = gardswag_syntax::parse(&dat).expect("unable to parse file");

    let mut ctx = gardswag_typesys::Context::default();

    let mut env = infer::Env {
        vars: [("std".to_string(), mk_env_std(&mut ctx))]
            .into_iter()
            .collect(),
    };

    let tg = match infer::infer_block(&env, &mut ctx, &parsed) {
        Ok(t) => {
            use gardswag_typesys::Substitutable as _;
            debug!("type check ok");
            debug!("=T> {}", t);
            // generalize the type
            env.vars.apply(&ctx);
            let tg = t.clone().generalize(&env, &ctx);
            // garbage collection
            env.gc(&mut ctx, core::iter::once(t));
            debug!("--TV--");
            for (k, v) in &ctx.m {
                debug!("\t${}:\t{}", k, v);
            }
            debug!("--CG--");
            for (k, v) in &ctx.g {
                debug!("\t${}:\t{:?}", k, v);
            }
            tracing::info!("=G> {}", tg);
            tg
        }
        Err(e) => panic!("type checking error: {:?}", e),
    };

    core::mem::drop(env);

    let mut modul = bytecode::Module {
        bbs: vec![bytecode::BasicBlock::default()],
        tg,
        interner: Default::default(),
    };

    {
        // std
        use bytecode::{Builtin as Bi, VmInstr as Vi};
        modul.push_instr(Vi::Builtin(Bi::StdioWrite));
        let s_write = modul.interner.get_or_intern("write");
        modul.push_instr(Vi::BuildRecord(vec![s_write]));
        let mut record = Vec::new();
        for (blti, name) in [
            (Bi::Add, "add"),
            (Bi::Minus, "minus"),
            (Bi::Mult, "mult"),
            (Bi::Eq, "eq"),
            (Bi::Leq, "leq"),
            (Bi::Not, "not"),
        ] {
            modul.push_instr(Vi::Builtin(blti));
            record.push(name);
        }
        let brcrdat = record
            .into_iter()
            .rev()
            .chain(core::iter::once("stdio"))
            .map(|i| modul.interner.get_or_intern(i))
            .collect();
        modul.push_instr(Vi::BuildRecord(brcrdat));
    }

    bytecode::CodeGen::ser_to_bytecode(
        &parsed,
        &mut modul,
        Some(bytecode::VarStack {
            parent: None,
            last: "std",
        }),
    );

    core::mem::drop(parsed);

    if args.print_bytecode {
        println!(
            "bytecode:\n{}",
            serde_yaml::to_string(&modul).expect("unable to serialize bytecode")
        );
    }

    if args.mode == Mode::Check {
        return;
    }

    println!("result: {:?}", interp::VmState::new(&modul).run());
}
