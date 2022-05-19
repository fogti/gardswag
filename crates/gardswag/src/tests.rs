use super::*;

fn dflsubscr() -> impl tracing::subscriber::Subscriber {
    tracing_subscriber::fmt::Subscriber::builder()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .finish()
}

macro_rules! assert_interp {
    ($x:expr) => {{
        let result = crossbeam_utils::thread::scope(|s| main_interp(s, $x))
            .expect("unable to join threads");
        insta::assert_debug_snapshot!(result);
    }}
}

#[test]
fn chk_hello() {
    insta::assert_yaml_snapshot!(main_check(r#"std.stdio.write("Hello world!\n");"#).unwrap());
}

#[test]
fn chk_fibo() {
    tracing::subscriber::with_default(dflsubscr(), || {
        insta::assert_yaml_snapshot!(main_check(
            r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib
            "#
        )
        .unwrap());
    });
}

#[test]
fn run_fibo0() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib 1 1 0
            "#,
        )
        .unwrap();
        assert_interp!(&x.0);
    });
}

#[test]
fn run_fibo1() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib 1 1 1
            "#,
        )
        .unwrap();
        assert_interp!(&x.0);
    });
}

#[test]
fn run_fibo() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib 1 1 5
            "#,
        )
        .unwrap();
        insta::assert_yaml_snapshot!(x);
        assert_interp!(&x.0);
    });
}

#[test]
fn chk_implicit_restr() {
    tracing::subscriber::with_default(dflsubscr(), || {
        insta::assert_yaml_snapshot!(main_check(
            r#"
                \x
                let id = \y y;
                .{
                  id;
                  x;
                  y = "{x}";
                }
            "#
        )
        .unwrap());
    });
}

#[test]
fn run_id() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                let id = \x x;
                id 1
            "#,
        )
        .unwrap();
        insta::assert_yaml_snapshot!(x);
        assert_interp!(&x.0);
    });
}

#[test]
fn run_call_blti() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                std.plus 1 1
            "#,
        )
        .unwrap();
        insta::assert_yaml_snapshot!(x);
        assert_interp!(&x.0);
    });
}

#[test]
fn run_fix() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                let rec f = \a if (std.eq a 0) { 0 } { f 0 };
                f 1
            "#,
        )
        .unwrap();
        insta::assert_yaml_snapshot!(x);
        assert_interp!(&x.0);
    });
}

#[test]
fn run_update() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check(
            r#"
                .{
                  a = "what";
                  b = 1;
                  c = .{};
                } // .{
                  b = "no";
                  c = 50;
                }
            "#,
        )
        .unwrap();
        insta::assert_yaml_snapshot!(x);
        assert_interp!(&x.0);
    });
}

#[test]
fn error_int_update() {
    tracing::subscriber::with_default(dflsubscr(), || {
        insta::assert_yaml_snapshot!(main_check("0//0").map_err(|e| e.to_string()));
    });
}

#[test]
fn run_ctrl_match() {
    tracing::subscriber::with_default(dflsubscr(), || {
        let x = main_check("match .this_is_a_variant 1 | .this_is_a_variant x => std.plus x 1")
            .unwrap();
        insta::assert_yaml_snapshot!(x);
        assert_interp!(&x.0);
    });
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(8192))]

    #[test]
    fn doesnt_crash(s in "[ -~]+") {
        if let Ok(x) = main_check(&s) {
            let _ = crossbeam_utils::thread::scope(|s| main_interp(s, &x.0))
                .expect("unable to join threads");
        }
    }
}
