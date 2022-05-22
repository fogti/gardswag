(same as the README, but uses be-bruijn-indices instead for lambda binders.)

# Lambda Duplication

```javascript
dup a b = λ(body)
------------------ Dup-Lam
a <- λ b0
b <- λ b1
dup b0 b1 = body
```

```javascript
dup a b = λ λ (Pair @1 @0)
(Pair a b)
------------------ Dup-Lam
dup a b = λ (Pair @1 @0)
(Pair (λ a) (λ b))
------------------ Dup-Lam
dup a b = (Pair @1 @0)
(Pair
  (λ (λ a))
  (λ (λ b))
)
------------------ Dup-Ctr (@ refs get implicitly clones)
(Pair
  (λ (λ (Pair @1 @0)))
  (λ (λ (Pair @1 @0)))
)
```

> This allows us to share computations inside lambdas, something that GHC isn't
> capable of. For example, consider the following reduction:

```javascript
dup f g = ((λ λ (Pair (+ @1 @1) @0)) 2)
(Pair (f 10) (g 20))
-------------------------------------- App-Lam
dup f g = (λ (Pair (+ 2 2) @0))
(Pair (f 10) (g 20))
-------------------------------------- Dup-Lam
dup f g = (Pair (+ 2 2) @0)
(Pair ((λ f) 10) ((λ g) 20))
-------------------------------------- Dup-Ctr
dup a b = (+ 2 2)
(Pair ((λ (Pair a @0)) 10) ((λ (Pair b @0)) 20))
-------------------------------------- App-Lam
dup a b = (+ 2 2)
(Pair (Pair a 10) (Pair b 20))
-------------------------------------- Op2-U32
dup a b = 4
(Pair (Pair a 10) (Pair b 20))
-------------------------------------- Dup-U32
(Pair (Pair 4 10) (Pair 4 20))
```

> Notice that the `(+ 2 2)` addition only happened once, even though it was
> nested inside two copied lambda binders! In Haskell, this situation would lead
> to the un-sharing of the lambdas, and `(+ 2 2)` would happen twice. Notice also
> how, in some steps, lambdas were applied to arguments that appeared outside of
> their bodies. This is all fine, and, in the end, the result is correct.
