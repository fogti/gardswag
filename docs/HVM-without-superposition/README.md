[HVM](https://github.com/Kindelia/HVM/blob/master/HOW.md) is really nice,
but getting the superposition stuff working correctly is pretty hard and
error-prone. Some I'm first trying to build lambda duplication without it,
and look forward to the point where I get stuck, to learn how it is
supposed to work and what exactly it does solve.

# Lambda Duplication

```javascript
dup a b = λx(body)
------------------ Dup-Lam
a <- λx0 [x/x0](b0)
b <- λx1 [x/x1](b1)
dup b0 b1 = body
```

```javascript
dup a b = λx λy (Pair x y)
(Pair a b)
------------------ Dup-Lam
dup a b = λy (Pair x y)
(Pair (λx0 [x/x0]a) (λx1 [x/x1]b))
------------------ Dup-Lam
dup a b = (Pair x y)
(Pair
  (λx0 [x/x0](λy0 [y/y0]a))
  (λx1 [x/x1](λy1 [y/y1]b))
)
------------------ Dup-Ctr
dup a b = x
dup c d = y
(Pair
  (λx0 [x/x0](λy0 [y/y0][x/a][y/c](Pair x y)))
  (λx1 [x/x1](λy1 [y/y1][x/b][y/d](Pair x y)))
)
------------------ Fwd-Binders
(Pair
  (λx0 [x/x0](λy0 [y/y0](Pair x y)))
  (λx1 [x/x1](λy1 [y/y1](Pair x y)))
)
------------------ Apply-Subst
(Pair
  (λx0 (λy0 [y/y0](Pair x0 y)))
  (λx1 (λy1 [y/y1](Pair x1 y)))
)
------------------ Apply-Subst
(Pair
  (λx0 (λy0 (Pair x0 y0)))
  (λx1 (λy1 (Pair x1 y1)))
)
```

> This allows us to share computations inside lambdas, something that GHC isn't
> capable of. For example, consider the following reduction:

```javascript
dup f g = ((λx λy (Pair (+ x x) y)) 2)
(Pair (f 10) (g 20))
-------------------------------------- App-Lam
dup f g = (λy (Pair (+ 2 2) y))
(Pair (f 10) (g 20))
-------------------------------------- Dup-Lam
dup f g = (Pair (+ 2 2) y)
(Pair ((λy0 [y/y0]f) 10) ((λy1 [y/y1]g) 20))
-------------------------------------- App-Lam
dup f g = (Pair (+ 2 2) y)
(Pair ([y/10]f) ([y/20]g))
-------------------------------------- Dup-Ctr
dup a b = (+ 2 2)
dup c d = y
(Pair ([y/10](Pair a c)) ([y/20](Pair b d)))
-------------------------------------- Op2-U32
dup a b = 4
dup c d = y
(Pair ([y/10](Pair a c)) ([y/20](Pair b d)))
-------------------------------------- Dup-U32
dup c d = y
(Pair ([y/10](Pair 4 c)) ([y/20](Pair 4 d)))
-------------------------------------- Fwd-Binders
(Pair ([y/10](Pair 4 y)) ([y/20](Pair 4 y)))
-------------------------------------- Apply-Subst
(Pair (Pair 4 10) (Pair 4 20))
```

> Notice that the `(+ 2 2)` addition only happened once, even though it was
> nested inside two copied lambda binders! In Haskell, this situation would lead
> to the un-sharing of the lambdas, and `(+ 2 2)` would happen twice. Notice also
> how, in some steps, lambdas were applied to arguments that appeared outside of
> their bodies. This is all fine, and, in the end, the result is correct.
