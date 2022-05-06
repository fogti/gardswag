use std::path::PathBuf;

mod infer;

#[derive(clap::Parser)]
#[clap(version)]
struct Args {
    /// file to interpret
    #[clap(short, long)]
    file: PathBuf,
}

fn mk_env_std() -> gardswag_typesys::Scheme<infer::TyVar> {
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
            Ty::Record {
                m: [
                    $((stringify!($key).to_string(), $value)),*
                ].into_iter().collect(),
                partial: false,
            }
        }};
    }

    TyScheme {
        forall: [0, 1].into_iter().collect(),
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

    let env = infer::Env {
        vars: [("std".to_string(), mk_env_std())].into_iter().collect(),
        tracker: std::rc::Rc::new(std::cell::RefCell::new(infer::Tracker {
            fresh_tyvars: 100..,
            subst: Default::default(),
        })),
    };

    match env.infer_block(&parsed) {
        Ok(t) => {
            println!("type check ok");
            for (k, v) in env
                .tracker
                .borrow()
                .subst
                .iter()
                .collect::<std::collections::BTreeMap<_, _>>()
            {
                println!("\t${}:\t{}", k, v);
            }
            println!("=> {}", t);
        }
        Err(e) => panic!("type checking error: {:?}", e),
    }
}
