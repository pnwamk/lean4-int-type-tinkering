import Std.Tactic.GuardExpr

def Nat.ldiff : Nat → Nat → Nat := Nat.bitwise fun x y => x && not y

structure Int8 where
  ofUInt8 ::
  toUInt8 : UInt8
  deriving DecidableEq

def Int8.size : Nat := UInt8.size
def Int8.minValue : Int8 := ⟨UInt8.ofNat (UInt8.size >>> 1)⟩
def Int8.maxValue : Int8 := ⟨Int8.minValue.toUInt8 - 1⟩

-- @[extern "lean_uint8_of_nat"]
-- def UInt8.ofNat (n : @& Nat) : UInt8 := ⟨Fin.ofNat n⟩
def Int8.ofNat (x : Nat) : Int8 := ⟨UInt8.ofNat x⟩

instance : OfNat Int8 n   := ⟨Int8.ofNat n⟩

------------------------
-- sign insensitive ops:
------------------------
-- addition
-- subtraction
-- multiplication
-- negation
-- bitwise AND
-- bitwise OR
-- bitwise XOR
-- bitwise NOT
-- left shift
------------------------
-- sign sensitive ops:
------------------------
-- division := fun (n m : IntN) : IntN := IntN.ofInt (n.toInt / m.toInt)
-- modulo := fun (n m : IntN) : IntN := IntN.ofInt (n.toInt % m.toInt)
-- right shift ...
-- comparisons (except equality) ...
------------------------

def Int8.complement (a : Int8) : Int8 := ⟨UInt8.complement a.toUInt8⟩
def Int8.neg (a : Int8) : Int8 := Int8.ofUInt8 <| UInt8.sub 0 a.toUInt8

instance : Neg Int8 := ⟨Int8.neg⟩

def Int8.sign (a : Int8) : Int8 :=
  if a.toUInt8 == 0 then 0
  else if a.toUInt8 > Int8.maxValue.toUInt8 then -1
  else 1

abbrev Nat.toInt8 := Int8.ofNat

def Int8.ofInt : Int → Int8
| Int.ofNat n => Int8.ofNat n
| Int.negSucc n => Int8.ofNat (Nat.ldiff (Int8.size - 1) n)

def Int8.toInt (a : Int8) : Int :=
  let s := a.sign
  if s == 0 || s == 1 then Int.ofNat a.toUInt8.toNat
  else Int.negOfNat (Int8.size - a.toUInt8.toNat)

def Int8.add (a b : Int8) : Int8 := ⟨UInt8.add a.toUInt8 b.toUInt8⟩
def Int8.sub (a b : Int8) : Int8 := ⟨UInt8.sub a.toUInt8 b.toUInt8⟩
def Int8.mul (a b : Int8) : Int8 := ⟨UInt8.mul a.toUInt8 b.toUInt8⟩
-- def UInt8.div (a b : UInt8) : UInt8 := ⟨a.val / b.val⟩
-- def UInt8.mod (a b : UInt8) : UInt8 := ⟨a.val % b.val⟩
-- def UInt8.modn (a : UInt8) (n : @& Nat) : UInt8 := ⟨Fin.modn a.val n⟩
def Int8.land (a b : Int8) : Int8 := ⟨UInt8.land a.toUInt8 b.toUInt8⟩
def Int8.lor (a b : Int8) : Int8 := ⟨UInt8.lor a.toUInt8 b.toUInt8⟩
def Int8.xor (a b : Int8) : Int8 := ⟨UInt8.xor a.toUInt8 b.toUInt8⟩
def Int8.shiftLeft (a b : Int8) : Int8 := ⟨UInt8.shiftLeft a.toUInt8 b.toUInt8⟩

-- @[extern "lean_uint8_shift_right"]
-- def UInt8.shiftRight (a b : UInt8) : UInt8 := ⟨a.val >>> (modn b 8).val⟩

-- def UInt8.lt (a b : UInt8) : Prop := a.val < b.val

-- def UInt8.le (a b : UInt8) : Prop := a.val ≤ b.val

instance : Add Int8       := ⟨Int8.add⟩
-- instance : Sub UInt8       := ⟨UInt8.sub⟩
instance : Sub Int8       := ⟨Int8.sub⟩
-- instance : Mul UInt8       := ⟨UInt8.mul⟩
instance : Mul Int8       := ⟨Int8.mul⟩
-- instance : Mod UInt8       := ⟨UInt8.mod⟩
-- instance : Mod Int8       := ⟨Int8.mod⟩
-- instance : HMod UInt8 Nat UInt8 := ⟨UInt8.modn⟩
-- instance : HMod Int8 Nat Int8 := ⟨Int8.modn⟩
-- instance : Div UInt8       := ⟨UInt8.div⟩
-- instance : Div Int8       := ⟨Int8.div⟩
-- instance : LT UInt8        := ⟨UInt8.lt⟩
-- instance : LT Int8        := ⟨Int8.lt⟩
-- instance : LE UInt8        := ⟨UInt8.le⟩
-- instance : LE Int8        := ⟨Int8.le⟩

-- instance : Complement UInt8 := ⟨UInt8.complement⟩
instance : Complement Int8 := ⟨Int8.complement⟩
-- instance : AndOp UInt8     := ⟨UInt8.land⟩
instance : AndOp Int8     := ⟨Int8.land⟩
-- instance : OrOp UInt8      := ⟨UInt8.lor⟩
instance : OrOp Int8      := ⟨Int8.lor⟩
-- instance : Xor UInt8       := ⟨UInt8.xor⟩
instance : Xor Int8       := ⟨Int8.xor⟩
-- instance : ShiftLeft UInt8  := ⟨UInt8.shiftLeft⟩
instance : ShiftLeft Int8  := ⟨Int8.shiftLeft⟩
-- instance : ShiftRight UInt8 := ⟨UInt8.shiftRight⟩

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_uint8_dec_lt"]
-- def UInt8.decLt (a b : UInt8) : Decidable (a < b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n < m))

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_uint8_dec_le"]
-- def UInt8.decLe (a b : UInt8) : Decidable (a ≤ b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n <= m))

-- instance (a b : UInt8) : Decidable (a < b) := UInt8.decLt a b
-- instance (a b : UInt8) : Decidable (a ≤ b) := UInt8.decLe a b
-- instance : Max UInt8 := maxOfLe
-- instance : Min UInt8 := minOfLe



instance : ToString Int8 := ⟨fun i => toString i.toInt⟩


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

structure IntN where
  type : Type u
  size : Nat
  ofInt : Int → type
  toInt : type → Int


abbrev int8Impl : IntN :=
{
  type := Int8,
  size := Int8.size,
  ofInt := Int8.ofInt,
  toInt := Int8.toInt,
}


def IntN.minInt (intN : IntN) : Int := -↑(intN.size >>> 1)
def IntN.maxInt (intN : IntN) : Int := ↑(intN.size >>> 1) - 1

structure UnOpTest (intN : IntN) where
  arg : Int
  opName : String
  op : intN.type → intN.type
  expected : Int

def UnOpTest.run {intN : IntN} (test : UnOpTest intN) : Option String :=
  let actual : Int := intN.toInt <| test.op (intN.ofInt test.arg)
  if actual == test.expected then do
    none
  else
    some s!"{test.opName} {test.arg}) failed: expected {test.expected} but got {actual}"



/-- Check that integers convert to and from IntN as expected for common and edge cases. -/
def intConversionTests (intN : IntN) : List (UnOpTest intN) := [
  (0, 0),
  (1, 1),
  (2, 2),
  (-1, -1),
  (-2, -2),
  (42, 42),
  (-42, -42),
  (intN.minInt, intN.minInt),
  (intN.minInt - 1, intN.maxInt),
  (intN.minInt + 1, intN.minInt + 1),
  (intN.maxInt, intN.maxInt),
  (intN.maxInt - 1, intN.maxInt - 1),
  (intN.maxInt + 1, intN.minInt),
].map <| fun (arg, expected) => {
  arg := arg,
  op := intN.ofInt ∘ intN.toInt,
  opName := "intN.ofInt ∘ intN.toInt"
  expected := expected,
}


def negTests (intN : IntN)
  [Neg intN.type]
  : List (UnOpTest intN) := [
  (0, 0),
  (1, -1),
  (-1, 1),
  (intN.minInt, intN.minInt),
  (intN.maxInt, 0 - intN.maxInt),
  (-intN.maxInt, intN.maxInt),
].map <| fun (arg, expected) => {
  arg := arg,
  op := Neg.neg,
  opName := "Neg.neg"
  expected := expected
}

def complementTests (intN : IntN)
  [Complement intN.type]
  : List (UnOpTest intN) := [
  (0, -1),
  (-1, 0),
  (1, -2),
  (-2, 1),
  (intN.minInt, intN.maxInt),
  (intN.maxInt, intN.minInt),
].map <| fun (arg, expected) => {
  arg := arg,
  op := Complement.complement,
  opName := "Complement.complement"
  expected := expected
}

structure BinOpTest (intN : IntN) where
  lhs : Int
  rhs : Int
  op : intN.type → intN.type → intN.type
  opName : String
  expected : Int
  isCommutative : Bool := false

def BinOpTest.run {intN : IntN} (test : BinOpTest intN) : Option String :=
  let actual : Int := intN.toInt <| test.op (intN.ofInt test.lhs) (intN.ofInt test.rhs)
  let actual' : Int := intN.toInt <| test.op (intN.ofInt test.rhs) (intN.ofInt test.lhs)
  if actual == test.expected then do
    if test.isCommutative then
      if actual' == test.expected then
        none
      else
        some s!"({test.opName} {test.rhs} {test.lhs}) failed: expected {test.expected} but got {actual'}"
    else
      none
  else
    some s!"({test.opName} {test.lhs} {test.rhs}) failed: expected {test.expected} but got {actual}"


def addTests
  (intN : IntN)
  [Add intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  1),
  ( 1,  2,  3),
  (-1,  0,  -1),
  (-1,  1,  0),
  ( 42, 42, 84),
  -- max value addition
  (intN.maxInt, 0,  intN.maxInt),
  (intN.maxInt, -1, intN.maxInt -1),
  (intN.maxInt, 1,  intN.minInt),
  (intN.maxInt, intN.maxInt, -2),
  -- min value addition
  (intN.minInt, 0,           intN.minInt),
  (intN.minInt, -1,          intN.maxInt),
  (intN.minInt, 1,           intN.minInt + 1),
  (intN.minInt, intN.minInt, 0),
].foldr (init := []) <| fun (lhs, rhs, expected) tests => [
  {lhs := lhs,
   rhs := rhs,
   op := Add.add,
   opName := "Add.add",
   expected := expected,
   isCommutative := true,
   : BinOpTest intN},
  ] ++ tests


def subTests
  (intN : IntN)
  [Sub intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  -1),
  ( 1,  0,  1),
  ( 1,  2,  -1),
  ( 2,  1,  1),
  ( 2,  2,  0),
  (-1,  -1,  0),
  (-1,  1,  -2),
  -- max value subtraction
  (intN.maxInt, 0,  intN.maxInt),
  (intN.maxInt, 1, intN.maxInt - 1),
  (intN.maxInt, -1, intN.minInt),
  (intN.maxInt, intN.maxInt, 0),
  -- min value subtraction
  (intN.minInt, 0,           intN.minInt),
  (intN.minInt, -1,          intN.minInt + 1),
  (intN.minInt, 1,           intN.maxInt),
  (intN.minInt, intN.minInt, 0),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := Sub.sub,
  opName := "Sub.sub",
  expected := expected,
  : BinOpTest intN
}

def mulTests
  (intN : IntN)
  [Mul intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  2,  2),
  (-1,  0,  0),
  (-1,  1,  -1),
  (-1,  2,  -2),
  ( 42, 2, 42 * 2),
  -- max value addition
  (intN.maxInt, 0,  0),
  (intN.maxInt, 1,  intN.maxInt),
  (intN.maxInt, -1, intN.minInt + 1),
  (intN.maxInt, 2,  -2),
  -- min value addition
  (intN.minInt, 0,  0),
  (intN.minInt, 1,  intN.minInt),
  (intN.minInt, -1, intN.minInt),
  (intN.minInt, 2, 0),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := Mul.mul,
  opName := "Mul.mul",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def landTests
  (intN : IntN)
  [AndOp intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  1,  1),
  ( 1,  2,  0),
  ( 2,  3,  2),
  (intN.minInt, intN.maxInt, 0),
  (intN.maxInt, -intN.maxInt, 1),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := AndOp.and,
  opName := "AndOp.and",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def lorTests
  (intN : IntN)
  [OrOp intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  1),
  ( 1,  1,  1),
  ( 1,  2,  3),
  ( 2,  3,  3),
  (intN.minInt, intN.maxInt, -1),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := OrOp.or,
  opName := "OrOp.or",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def xorTests
  (intN : IntN)
  [Xor intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  1),
  ( 1,  1,  0),
  ( 1,  2,  3),
  ( 2,  3,  1),
  (intN.minInt, intN.maxInt, -1),
  (intN.maxInt, -intN.maxInt, -2),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := Xor.xor,
  opName := "Xor.xor",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def shiftLeftTests
  (intN : IntN)
  [ShiftLeft intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  0,  1),
  ( 1,  1,  2),
  ( -1,  1,  -2),
  ( -1,  2,  -4),
  (intN.minInt, 1, 0),
  (intN.maxInt, 1, -2),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := ShiftLeft.shiftLeft,
  opName := "ShiftLeft.shiftLeft",
  expected := expected,
  : BinOpTest intN
}

-- BOOKMARK
-- Additional sign-sensitive ops:
-- modulo := fun (n m : IntN) : IntN := IntN.ofInt (n.toInt % m.toInt)
-- right shift ...
-- comparisons (except equality) ...


-- FIXME
def divTests
  (intN : IntN)
  [Div intN.type]
: List (BinOpTest intN) := []

-- FIXME
def modTests
  (intN : IntN)
  [Mod intN.type]
: List (BinOpTest intN) := []

-- FIXME
def hmodTests
  (intN : IntN)
  [HMod intN.type Int Int8]
: List (BinOpTest intN) := []

#guard (intConversionTests int8Impl).filterMap UnOpTest.run == []
#guard (negTests int8Impl).filterMap UnOpTest.run == []
#guard (complementTests int8Impl).filterMap UnOpTest.run == []
#guard (addTests int8Impl).filterMap BinOpTest.run == []
#guard (subTests int8Impl).filterMap BinOpTest.run == []
#guard (mulTests int8Impl).filterMap BinOpTest.run == []
#guard (landTests int8Impl).filterMap BinOpTest.run == []
#guard (lorTests int8Impl).filterMap BinOpTest.run == []
#guard (xorTests int8Impl).filterMap BinOpTest.run == []
#guard (shiftLeftTests int8Impl).filterMap BinOpTest.run == []
