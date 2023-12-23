
IntN representation approach?

I'm starting to tinker with how signed fixed-width integer types `IntN` (similar to Lean's `UIntN` types) could be efficiently represented.

Any knee-jerk thoughts on how the underlying Lean representation (i.e., non-C definitions)  might be best modeled?

At the moment I'm playing around with a type `Fin2C n` that is a sort of play on `Fin` but for two's complement arithmetic in a sense:


```lean
/--
`Fin2C n` is an integer `i` with the constraint that `-n ≤ i < n`.
-/
structure Fin2C (n : Nat)where
  /-- If `i : Fin2C n`, then `i.val : ℤ` is the described number. It can also be
  written as `i.1` or just `i` when the target type is known. -/
  val  : Int
  /-- If `i : Fin2C n`, then `i.2` is a proof that `-n ≥ i.1`. -/
  isGe : LE.le (-↑n) val
  /-- If `i : Fin2C n`, then `i.3` is a proof that `i.1 < n`. -/
  isLt : LT.lt val n
```

and then you define `Int64` as `Fin2C 2^63`.

But a more generic, arbitrary finite interval over ℤ could also work:

```lean
/--
`FinZ n m` is an integer `i` with the constraint that `n ≤ i < n + m`.
-/
structure FinZ (n : Int) (m : Nat) where
  /-- If `i : FinZ n m`, then `i.val : ℤ` is the described number. It can also be
  written as `i.1` or just `i` when the target type is known. -/
  val  : Int
  /-- If `i : FinZ n m`, then `i.2` is a proof that `i.1 ≥ n`. -/
  isGe : GE.ge val n
  /-- If `i : FinZ n m`, then `i.3` is a proof that `i.1 < n + m`. -/
  isLt : LT.lt val (n + m)
```

from which you define `Int64` as `FinZ -2^63 2^64`.

I'm not far enough along to have strong opinions about which approach is best. (Just starting to define various `Fin2C n` definitions by translating `Fin n` definitions.)

Any thoughts are welcome =) I'll keep hacking away at definitions in the mean time to see if that proves elucidating.



def landTests
  (intN : IntN)
  [AndOp intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  1,  1),
  ( 1,  2,  0),
  ( 2,  3,  2),
  (intN.minInt, intN.maxInt, intN.maxInt),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := AndOp.and,
  opName := "AndOp.and",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def negTests (intN : IntN)
  [Neg intN.type]
  : List (UnOpTest intN) := [
  (0, 0),
  (1, -1),
  (42, -42),
  (intN.minInt, intN.minInt),
  (intN.maxInt, 0 - intN.maxInt),
].foldr (init := []) <| fun (arg, expected) tests => [
  {arg := arg,
   op := Neg.neg,
   opName := "Neg.neg"
   expected := expected},
  {arg := expected,
   op := Neg.neg,
   opName := "Neg.neg"
   expected := arg},
  ] ++ tests