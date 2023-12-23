import LeanCopilot
import Std.Data.Int.Lemmas

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Copy of Fin contents from Init.Predule
-- with Fin2C translations where applicable
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --


-- /--
-- `Fin n` is a natural number `i` with the constraint that `0 ≤ i < n`.
-- It is the "canonical type with `n` elements".
-- -/
-- structure Fin (n : Nat) where
--   /-- If `i : Fin n`, then `i.val : ℕ` is the described number. It can also be
--   written as `i.1` or just `i` when the target type is known. -/
--   val  : Nat
--   /-- If `i : Fin n`, then `i.2` is a proof that `i.1 < n`. -/
--   isLt : LT.lt val n

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


-- theorem Fin.eq_of_val_eq {n} : ∀ {i j : Fin n}, Eq i.val j.val → Eq i j
--   | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Fin2C.eq_of_val_eq {n} : ∀ {i j : Fin2C n}, Eq i.val j.val → Eq i j
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl


-- theorem Fin.val_eq_of_eq {n} {i j : Fin n} (h : Eq i j) : Eq i.val j.val :=
--   h ▸ rfl

theorem Fin2C.val_eq_of_eq {n} {i j : Fin2C n} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

-- theorem Fin.ne_of_val_ne {n} {i j : Fin n} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
--   fun h' => absurd (val_eq_of_eq h') h

theorem Fin2C.ne_of_val_ne {n} {i j : Fin2C n} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h


-- instance (n : Nat) : DecidableEq (Fin n) :=
--   fun i j =>
--     match decEq i.val j.val with
--     | isTrue h  => isTrue (Fin.eq_of_val_eq h)
--     | isFalse h => isFalse (Fin.ne_of_val_ne h)

instance (n : Nat) : DecidableEq (Fin2C n) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (Fin2C.eq_of_val_eq h)
    | isFalse h => isFalse (Fin2C.ne_of_val_ne h)

-- instance {n} : LT (Fin n) where
--   lt a b := LT.lt a.val b.val

instance {n} : LT (Fin2C n) where
  lt a b := LT.lt a.val b.val


-- instance {n} : LE (Fin n) where
--   le a b := LE.le a.val b.val

instance {n} : LE (Fin2C n) where
  le a b := LE.le a.val b.val


-- instance Fin.decLt {n} (a b : Fin n) : Decidable (LT.lt a b) := Nat.decLt ..
-- instance Fin.decLe {n} (a b : Fin n) : Decidable (LE.le a b) := Nat.decLe ..

instance Fin2C.decLt {n} (a b : Fin2C n) : Decidable (LT.lt a b) := Int.decLt ..
instance Fin2C.decLe {n} (a b : Fin2C n) : Decidable (LE.le a b) := Int.decLe ..








namespace Fin2C

-- instance coeToNat : CoeOut (Fin n) Nat :=
--   ⟨fun v => v.val⟩

instance coeToInt : CoeOut (Fin2C n) Int :=
  ⟨fun v => v.val⟩

-- def elim0.{u} {α : Sort u} : Fin 0 → α
--   | ⟨_, h⟩ => absurd h (not_lt_zero _)


def elim0.{u} {α : Sort u} : Fin2C 0 → α
  | ⟨_, h₁, h₂⟩ => absurd h₁ (Int.not_le.2 h₂)


-- def succ : Fin n → Fin n.succ
--   | ⟨i, h⟩ => ⟨i+1, Nat.succ_lt_succ h⟩

def succ : Fin2C n → Fin2C n.succ
  | ⟨i, h₁, h₂⟩ =>
    have hle : LE.le (-↑(n+1)) (i+1) := by
      simp [Int.neg_add]
      apply Int.add_le_add h₁
      constructor
    have hlt : LT.lt (i+1) (n+1) := by
      apply Int.add_le_add h₂
      constructor
    ⟨i+1, hle, hlt⟩


variable {n : Nat}

-- protected def ofNat {n : Nat} (a : Nat) : Fin n.succ :=
--   ⟨a % (n+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

-- BOOKMARK
-- protected def ofNat {n : Nat} (a : Nat) : Fin2C n.succ :=
--     have hle : LE.le (-↑(n+1)) (a % (n+1)) := by sorry
--     have hlt : LT.lt (i+1) (n+1) := by sorry
--     exact ⟨i+1, hle, hlt⟩
--   ⟨a % (n+1), hle, hlt⟩

-- protected def ofNat' {n : Nat} (a : Nat) (h : n > 0) : Fin n :=
--   ⟨a % n, Nat.mod_lt _ h⟩

-- private theorem mlt {b : Nat} : {a : Nat} → a < n → b % n < n
--   | 0,   h => Nat.mod_lt _ h
--   | _+1, h =>
--     have : n > 0 := Nat.lt_trans (Nat.zero_lt_succ _) h;
--     Nat.mod_lt _ this

-- protected def add : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, mlt h⟩

-- protected def mul : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a * b) % n, mlt h⟩

-- protected def sub : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + (n - b)) % n, mlt h⟩

-- /-!
-- Remark: land/lor can be defined without using (% n), but
-- we are trying to minimize the number of Nat theorems
-- needed to bootstrap Lean.
-- -/

-- protected def mod : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨a % b,  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

-- protected def div : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h⟩

-- def modn : Fin n → Nat → Fin n
--   | ⟨a, h⟩, m => ⟨a % m, Nat.lt_of_le_of_lt (Nat.mod_le _ _) h⟩

-- def land : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.land a b) % n, mlt h⟩

-- def lor : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.lor a b) % n, mlt h⟩

-- def xor : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.xor a b) % n, mlt h⟩

-- def shiftLeft : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a <<< b) % n, mlt h⟩

-- def shiftRight : Fin n → Fin n → Fin n
--   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a >>> b) % n, mlt h⟩

-- instance : Add (Fin n) where
--   add := Fin.add

-- instance : Sub (Fin n) where
--   sub := Fin.sub

-- instance : Mul (Fin n) where
--   mul := Fin.mul

-- instance : Mod (Fin n) where
--   mod := Fin.mod

-- instance : Div (Fin n) where
--   div := Fin.div

-- instance : AndOp (Fin n) where
--   and := Fin.land
-- instance : OrOp (Fin n) where
--   or := Fin.lor
-- instance : Xor (Fin n) where
--   xor := Fin.xor
-- instance : ShiftLeft (Fin n) where
--   shiftLeft := Fin.shiftLeft
-- instance : ShiftRight (Fin n) where
--   shiftRight := Fin.shiftRight

-- instance : OfNat (Fin (no_index (n+1))) i where
--   ofNat := Fin.ofNat i

-- instance : Inhabited (Fin (no_index (n+1))) where
--   default := 0

-- theorem val_ne_of_ne {i j : Fin n} (h : i ≠ j) : val i ≠ val j :=
--   fun h' => absurd (eq_of_val_eq h') h

-- theorem modn_lt : ∀ {m : Nat} (i : Fin n), m > 0 → (modn i m).val < m
--   | _, ⟨_, _⟩, hp =>  by simp [modn]; apply Nat.mod_lt; assumption

-- theorem val_lt_of_le (i : Fin b) (h : b ≤ n) : i.val < n :=
--   Nat.lt_of_lt_of_le i.isLt h

end Fin2C

-- instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
--   getElem xs i h := getElem xs i.1 h

-- macro_rules
--   | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)
