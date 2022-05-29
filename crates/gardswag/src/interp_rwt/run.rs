use super::*;

pub fn run_til_whnf(dict: &Arc<Dict>, val: &mut Value) {
    let mut modified = true;

    while modified {
        modified = false;
        use Value as V;

        *val = match core::mem::replace(val, Value::Poison) {
            v @ (V::Unit | V::Boolean(_) | V::Integer(_) | V::PureString(_) | V::ChanSend(_) | V::ChanRecv(_) | V::Record(..) | V::Tagger { .. } | V::Tagged { .. } | V::Lambda(_)) => v,
            v @ (V::Poison | V::LambdaRef(_) | V::DupPreRef(_)) => panic!("illegal unrewritten reference: {:?}", v),
            V::DupResRef(drr) => {
                modified = true;
                Lazy::force(&drr.0).clone()
            },
            V::Builtin { f, args } if args.len() < f.argc() => V::Builtin { f, args },
            V::Builtin { f, mut args } => {
                args.par_iter_mut().for_each(|i| run(dict, i));
                let mut ait = args.into_iter();
                match f {
                    Builtin::Plus => {
                        let a = ait.next().unwrap();
                        let b = ait.next().unwrap();
                        match (a, b) {
                            (V::Integer(a), V::Integer(b)) => V::Integer(a + b),
                            (a, b) => panic!("std.plus incorrectly invoked with ({:?}, {:?})", a ,b),
                        }
                    }
                    Builtin::Minus => {
                        let a = ait.next().unwrap();
                        let b = ait.next().unwrap();
                        match (a, b) {
                            (V::Integer(a), V::Integer(b)) => V::Integer(a - b),
                            (a, b) => panic!("std.minus incorrectly invoked with ({:?}, {:?})", a ,b),
                        }
                    }
                    Builtin::Mult => {
                        let a = ait.next().unwrap();
                        let b = ait.next().unwrap();
                        match (a, b) {
                            (V::Integer(a), V::Integer(b)) => V::Integer(a * b),
                            (a, b) => panic!("std.mult incorrectly invoked with ({:?}, {:?})", a ,b),
                        }
                    }
                    Builtin::Eq => {
                        let a = ait.next().unwrap();
                        let b = ait.next().unwrap();
                        V::Boolean(a == b)
                    }
                    Builtin::Leq => {
                        let a = ait.next().unwrap();
                        let b = ait.next().unwrap();
                        match (a, b) {
                            (V::Integer(a), V::Integer(b)) => V::Integer(a <= b),
                            (a, b) => panic!("std.leq incorrectly invoked with ({:?}, {:?})", a ,b),
                        }
                    }
                    Builtin::Not => {
                        let a = ait.next().unwrap();
                        if let V::Boolean(a) = a {
                            V::Boolean(!a)
                        } else {
                            panic!("std.not incorrectly invoked with ({:?})", a)
                        }
                    }
                    Builtin::SpawnThread => {
                        let a = ait.next().unwrap();
                        if let V::Lambda(a) = a {
                            std::thread::spawn(move || {
                                let mut x = V::Apply { prim: a, arg: V::Unit };
                                if !matches!(x, V::Unit) {
                                    panic!("std.spawn_thread worker lambda returned {:?}", x);
                                }
                            });
                            V::Unit
                        } else {
                            panic!("std.spawn_thread incorrectly invoked with ({:?})", a)
                        }
                    }
                    Builtin::MakeChan => {
                        let a = ait.next().unwrap();
                        if !matches!(a, V::Unit) {
                            panic!("std.make_chan incorrectly invoked with ({:?})", a);
                        }
                        let (s, r) = chan::unbounded();
                        V::Record(
                            [
                                (dict.send, V::ChanSend(s)),
                                (dict.recv, V::ChanRecv(r)),
                            ]
                            .into_iter()
                            .collect()
                        );
                    }
                    Builtin::ChanSend => {
                        let val = ait.next().unwrap();
                        let chans = ait.next().unwrap();
                        match chans {
                            V::ChanSend(s) => V::Boolean(s.send(val).is_ok()),
                            _ => panic!("std.chan_send incorrectly invoked with (_, {:?})", chans),
                        }
                    }
                    Builtin::ChanRecv => {
                        match ait.next().unwrap() {
                            V::ChanRecv(r) => match r.recv() {
                                Ok(x) => V::Tagged {
                                    key: dict.Some,
                                    value: Box::new(x),
                                },
                                Err(_) => V::Tagged {
                                    key: dict.None,
                                    value: Box::new(V::Unit),
                                },
                            },
                            x => panic!("std.chan_recv incorrectly invoked with ({:?})", x),
                        }
                    }
                }
            }

            V::FixLambda(x) => {
                let mut x = *x;
                x.prepare_dup();
                // TODO
                let mut x2 = x.clone();
                V::Apply {
                    prim: x,
                    arg: x2,
                }
            }
            // etc.
        };
    }
}

pub fn run(dict: &Arc<Dict>, mut val: &mut Value) {
    run_til_whnf(dict, val);

    match &mut val {
        V::Unit | V::Boolean(_) | V::Integer(_) | V::PureString(_) | V::ChanSend(_) | V::ChanRecv(_) | V::Tagger { .. } | V::Lambda(_) => {},
        V::Poison | V::LambdaRef(_) | V::DupPreRef(_) | V::DupResRef(_) => panic!("illegal unrewritten reference: {:?}", val),
        V::FixLambda(_) | V::MkDup { .. } | V::Apply { .. } => panic!("illegal unrewritten term: {:?}", val),
        V::Record(xs) => xs.par_iter_mut().for_each(|i| run_til_whnf(dict, i)),
        V::Tagged { value, .. } => run_til_whnf(dict, value),
        V::Builtin { args, .. } => args.par_iter_mut().for_each(|i| run_til_whnf(dict, i)),
    }
}
