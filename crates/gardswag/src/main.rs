use std::path::PathBuf;

mod bytecode;
mod infer;

#[derive(Clone, clap::ArgEnum)]
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
}

fn mk_env_std() -> gardswag_typesys::Scheme {
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

    TyScheme {
        forall: [].into_iter().map(|i| (i, Default::default())).collect(),
        t: tr!({
            plus: ta!(tl!(int) => tl!(int) => tl!(int)),
            minus: ta!(tl!(int) => tl!(int) => tl!(int)),
            leq: ta!(tl!(int) => tl!(int) => tl!(bool)),
            not: ta!(tl!(bool) => tl!(bool)),
            stdio: tr!({
                write: ta!(tl!(str) => tl!(())),
            }),
        }),
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
        vars: [("std".to_string(), mk_env_std())].into_iter().collect(),
    };

    let tg = match infer::infer_block(&env, &mut ctx, &parsed) {
        Ok(t) => {
            use gardswag_typesys::Substitutable as _;
            println!("type check ok");
            println!("=T> {}", t);
            // generalize the type
            env.vars.apply(&ctx);
            let tg = t.clone().generalize(&env, &ctx);
            // garbage collection
            env.gc(&mut ctx, core::iter::once(t));
            println!("--TV--");
            for (k, v) in &ctx.m {
                println!("\t${}:\t{}", k, v);
            }
            println!("--CG--");
            for (k, v) in &ctx.g {
                println!("\t${}:\t{:?}", k, v);
            }
            println!("=G> {}", tg);
            tg
        }
        Err(e) => panic!("type checking error: {:?}", e),
    };

    core::mem::drop(env);

    let mut modul = bytecode::Module {
        bbs: vec![bytecode::BasicBlock::default()],
        tg,
    };

    {
        // std
        use bytecode::{Builtin as Bi, VmInstr as Vi};
        modul.push_instr(Vi::Builtin(Bi::StdioWrite));
        modul.push_instr(Vi::BuildRecord(
            ["write"].into_iter().map(|i| i.to_string()).collect(),
        ));
        modul.push_instr(Vi::Builtin(Bi::Not));
        modul.push_instr(Vi::Builtin(Bi::Leq));
        modul.push_instr(Vi::Builtin(Bi::Minus));
        modul.push_instr(Vi::Builtin(Bi::Add));
        modul.push_instr(Vi::BuildRecord(
            ["add", "minus", "leq", "not", "stdio"]
                .into_iter()
                .map(|i| i.to_string())
                .collect(),
        ));
    }

    bytecode::CodeGen::ser_to_bytecode(
        &parsed,
        &mut modul,
        Some(bytecode::VarStack {
            parent: None,
            last: "std",
        }),
    );

    println!(
        "bytecode:\n{}",
        serde_yaml::to_string(&modul.bbs).expect("unable to serialize bytecode")
    );
}
