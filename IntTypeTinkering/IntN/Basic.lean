
structure Int8 where
  ofUInt8 ::
  toUInt8 : UInt8
  deriving DecidableEq

def Int8.size : Nat := UInt8.size
def Int8.maxValue : Int8 := ⟨UInt8.ofNat (UInt8.size / 2 - 1)⟩
def Int8.minValue : Int8 := ⟨UInt8.ofNat (UInt8.size / 2)⟩
def Int8.ofNat (x : Nat) : Int8 := ⟨UInt8.ofNat x⟩
instance : OfNat Int8 n := ⟨Int8.ofNat n⟩

def Int8.isNeg (a : Int8) : Bool := a.toUInt8 > Int8.maxValue.toUInt8

abbrev Nat.toInt8 := Int8.ofNat

def Int8.complement (a : Int8) : Int8 := ⟨a.toUInt8.complement⟩
instance : Complement Int8 := ⟨Int8.complement⟩

def Int8.ofInt : Int → Int8
| Int.ofNat n => .ofNat n
| Int.negSucc n => ~~~.ofNat n

def Int8.toInt (a : Int8) : Int :=
  if a.isNeg
  then Int.negOfNat (Int8.size - a.toUInt8.toNat)
  else Int.ofNat a.toUInt8.toNat

instance : ToString Int8 := ⟨fun i => toString i.toInt⟩

def Int8.neg (a : Int8) : Int8 := ⟨0 - a.toUInt8⟩
instance : Neg Int8 := ⟨Int8.neg⟩

def Int8.unsignedAbs (a : Int8) : UInt8 :=
  if a.isNeg
  then 0 - a.toUInt8
  else a.toUInt8

def Int8.abs (a : Int8) : Int8 := ⟨a.unsignedAbs⟩

def Int8.add (a b : Int8) : Int8 := ⟨UInt8.add a.toUInt8 b.toUInt8⟩
instance : Add Int8 := ⟨Int8.add⟩

def Int8.sub (a b : Int8) : Int8 := ⟨UInt8.sub a.toUInt8 b.toUInt8⟩
instance : Sub Int8 := ⟨Int8.sub⟩

def Int8.mul (a b : Int8) : Int8 := ⟨UInt8.mul a.toUInt8 b.toUInt8⟩
instance : Mul Int8 := ⟨Int8.mul⟩

-- @[extern "lean_int8_div"]
def Int8.div (a b : Int8) : Int8 :=
  match a.isNeg, b.isNeg with
  | true,  true => ⟨(-a).toUInt8 / (-b).toUInt8⟩
  | true,  false => -⟨(-a).toUInt8 / b.toUInt8⟩
  | false, true => -⟨a.toUInt8 / (-b).toUInt8⟩
  | false, false => ⟨a.toUInt8 / b.toUInt8⟩
instance : Div Int8 := ⟨Int8.div⟩

-- @[extern "lean_int8_mod"]
def Int8.mod (a b : Int8) : Int8 :=
  match a.isNeg, b.isNeg with
  | true,  true => -⟨(-a).toUInt8 % (-b).toUInt8⟩
  | true,  false => -⟨(-a).toUInt8 % b.toUInt8⟩
  | false, true => ⟨a.toUInt8 % (-b).toUInt8⟩
  | false, false => ⟨a.toUInt8 % b.toUInt8⟩
instance : Mod Int8 := ⟨Int8.mod⟩

def Int8.modn (a : Int8) (n : @& Nat) : Int8 := ⟨UInt8.modn a.toUInt8 n⟩
instance : HMod Int8 Nat Int8 := ⟨Int8.modn⟩

def Int8.land (a b : Int8) : Int8 := ⟨UInt8.land a.toUInt8 b.toUInt8⟩
instance : AndOp Int8 := ⟨Int8.land⟩

def Int8.lor (a b : Int8) : Int8 := ⟨UInt8.lor a.toUInt8 b.toUInt8⟩
instance : OrOp Int8 := ⟨Int8.lor⟩

def Int8.xor (a b : Int8) : Int8 := ⟨UInt8.xor a.toUInt8 b.toUInt8⟩
instance : Xor Int8 := ⟨Int8.xor⟩

def Int8.shiftLeft (a b : Int8) : Int8 := ⟨UInt8.shiftLeft a.toUInt8 b.toUInt8⟩
instance : ShiftLeft Int8 := ⟨Int8.shiftLeft⟩

def Int8.shiftRight (a b : Int8) : Int8 := ⟨UInt8.shiftRight a.toUInt8 b.toUInt8⟩
instance : ShiftRight Int8 := ⟨Int8.shiftRight⟩

def Int8.lt (a b : Int8) : Prop := a.toInt < b.toInt
instance : LT Int8 := ⟨Int8.lt⟩

def Int8.le (a b : Int8) : Prop := a.toInt ≤ b.toInt
instance : LE Int8 := ⟨Int8.le⟩

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_int8_dec_lt"]
def Int8.decLt (a b : Int8) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toInt < b.toInt))
instance (a b : Int8) : Decidable (a < b) := Int8.decLt a b

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_int8_dec_le"]
def Int8.decLe (a b : Int8) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toInt ≤ b.toInt))
instance (a b : Int8) : Decidable (a ≤ b) := Int8.decLe a b

instance : Max Int8 := maxOfLe
instance : Min Int8 := minOfLe
