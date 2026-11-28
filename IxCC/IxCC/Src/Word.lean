import IxCC.BigNat.LimbOps

/-! # Fixed-width words: widths, operations and their exact meaning

The operations of `UInt8`, `UInt16`, `UInt32` and `UInt64` that IxCC treats as primitives
(`docs/data-and-roots-design.md`, DR2, stage W1), and their exact meaning `WordOp.eval` on every
`Nat`, in range or not.

Each line of `WordOp.eval` transcribes the reference body of Lean 4.34.1
(`Init/Data/UInt/Basic.lean`, `Init/Data/BitVec/BasicAux.lean`, `Init/Prelude.lean`), so it agrees
with the body even on numbers at or above the width's size, which only a false proof can put in a
word:

* `add`, `mul`, `ofNat`, `neg`, `shiftLeft`: through `BitVec.ofNat n _`, which reduces mod `2^n`;
* `sub`: `BitVec.sub x y = .ofNat n ((2^n - y) + x)`, truncated `Nat` subtraction first;
* `div`, `mod`, `land`, `lor`, `xor`, `shiftRight`: through `BitVec.ofNatLT`, no reduction
  (`Nat`'s `x / 0 = 0` and `x % 0 = x`);
* `complement`: `allOnes n ^^^ x` with `allOnes n = 2^n - 1`;
* shifts: the amount is `UIntN.mod b bits`, so `b % bits` (a shift by the width or more wraps
  the amount; it does not clear the word);
* `convert` to a narrower width is `toNat` then `ofNat` (a reduction); to a wider one keeps the
  number;
* the decisions compare the numbers (unsigned).

`USize` is not a width here: its width is `System.Platform.numBits`, an opaque the kernel does not
unfold (DR5). The agreement of `eval` with Lean's operations is tested in `IxCCTests.Src.Words`
against Lean's C implementations (compiled) and against the reference bodies (the kernel's
`decide`). -/

namespace IxCC.Src

/-- A fixed width. -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Width

def bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- `UIntN.size`, `2 ^ bits`. -/
def size (w : Width) : Nat := 2 ^ w.bits

def all : List Width := [.w8, .w16, .w32, .w64]

def name : Width → String
  | .w8 => "UInt8" | .w16 => "UInt16" | .w32 => "UInt32" | .w64 => "UInt64"

theorem size_pos (w : Width) : 0 < w.size := Nat.two_pow_pos _

theorem bits_pos (w : Width) : 0 < w.bits := by cases w <;> decide

theorem size_le_of_bits_le {w w' : Width} (h : w.bits ≤ w'.bits) : w.size ≤ w'.size :=
  Nat.pow_le_pow_right (by decide) h

end Width

/-- The operations of a width, as Lean 4.34.1 defines them: the arithmetic and bitwise
operations, the three decisions (`decEq`, `decLt`, `decLe`, whose results are `Decidable`
values), the conversions from and to `Nat`, the conversions to another width
(`UIntN.toUIntM`), and the 9 scalar 64-bit hardware limb-component operations
(DR2 Stage W2 / `IxCC.BigNat.LimbOps`: lowered directly to `Lir.Stmt.limb` and `Lir.Rhs.bsr64`,
with adjacent pairs fused into single hardware instructions with zero heap allocation). -/
inductive WordOp where
  | add | sub | mul | div | mod | land | lor | xor | shiftLeft | shiftRight
  | complement | neg
  | decEq | decLt | decLe
  | ofNat | toNat
  | convert (to : Width)
  -- Scalar 64-bit limb primitives (outside Stage W1 `ofWidth` / `primitives`):
  | clz64
  | mulWideLo | mulWideHi
  | divWideQ | divWideR
  | addCarryLo | addCarryOut
  | subBorrowLo | subBorrowOut
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace WordOp

def arity : WordOp → Nat
  | .complement | .neg | .ofNat | .toNat | .convert _ | .clz64 => 1
  | .divWideQ | .divWideR | .addCarryLo | .addCarryOut | .subBorrowLo | .subBorrowOut => 3
  | _ => 2

/-- Whether the operation is one of the 9 scalar 64-bit limb-component primitives. -/
def isLimb : WordOp → Bool
  | .clz64 | .mulWideLo | .mulWideHi | .divWideQ | .divWideR
  | .addCarryLo | .addCarryOut | .subBorrowLo | .subBorrowOut => true
  | _ => false

/-- The 9 scalar 64-bit limb-component operations. -/
def limbOps : List WordOp :=
  [.clz64, .mulWideLo, .mulWideHi, .divWideQ, .divWideR,
   .addCarryLo, .addCarryOut, .subBorrowLo, .subBorrowOut]

/-- Every Stage W1 operation of a width `w` (the conversions to the three other widths).
Kept exact for `src-tables.tsv` and Stage W1 pin/rule checks. -/
def ofWidth (w : Width) : List WordOp :=
  [.add, .sub, .mul, .div, .mod, .land, .lor, .xor, .shiftLeft, .shiftRight, .complement, .neg,
   .decEq, .decLt, .decLe, .ofNat, .toNat] ++ (Width.all.filter (· ≠ w)).map .convert

/-- Every operation of width `w`, including the 64-bit scalar limb primitives at `.w64`. -/
def allOfWidth (w : Width) : List WordOp :=
  ofWidth w ++ if w == .w64 then limbOps else []

/-- The Lean name of the operation's constant at width `w` (diagnostics and the pin table:
`UInt64.add`, `UInt64.toUInt8`, …). -/
def leanName (w : Width) : WordOp → String
  | .add => s!"{w.name}.add" | .sub => s!"{w.name}.sub" | .mul => s!"{w.name}.mul"
  | .div => s!"{w.name}.div" | .mod => s!"{w.name}.mod" | .land => s!"{w.name}.land"
  | .lor => s!"{w.name}.lor" | .xor => s!"{w.name}.xor"
  | .shiftLeft => s!"{w.name}.shiftLeft" | .shiftRight => s!"{w.name}.shiftRight"
  | .complement => s!"{w.name}.complement" | .neg => s!"{w.name}.neg"
  | .decEq => s!"{w.name}.decEq" | .decLt => s!"{w.name}.decLt" | .decLe => s!"{w.name}.decLe"
  | .ofNat => s!"{w.name}.ofNat" | .toNat => s!"{w.name}.toNat"
  | .convert w' => s!"{w.name}.to{w'.name}"
  | .clz64 => "IxCC.BigNat.clz64"
  | .mulWideLo => "IxCC.BigNat.mulWide64.lo"
  | .mulWideHi => "IxCC.BigNat.mulWide64.hi"
  | .divWideQ => "IxCC.BigNat.divWide64.q"
  | .divWideR => "IxCC.BigNat.divWide64.r"
  | .addCarryLo => "IxCC.BigNat.addCarry64.lo"
  | .addCarryOut => "IxCC.BigNat.addCarry64.carry"
  | .subBorrowLo => "IxCC.BigNat.subBorrow64.lo"
  | .subBorrowOut => "IxCC.BigNat.subBorrow64.borrow"

/-- Whether the operation is a decision (its result a `Decidable` value). -/
def isDecision : WordOp → Bool
  | .decEq | .decLt | .decLe => true
  | _ => false

/-- Whether the operation is a primitive at every level (stage W1): every operation but the
decisions, whose reference bodies reduce to `Nat`'s own decisions on the two numbers (they never
build the width's size, so they compile as they are) and whose model fact would need what a
`Decidable` value is, not only what `decide` of it is. -/
def isPrimitive (op : WordOp) : Bool := !op.isDecision

/-- The primitive operations of a width. -/
def primitives (w : Width) : List WordOp := (ofWidth w).filter isPrimitive

/-- The width of an operation's word result (a conversion's target, otherwise its own). -/
def resultWidth (w : Width) : WordOp → Width
  | .convert w' => w'
  | _ => w

end WordOp

/-- A word operation's result: a word of a width, a `Nat`, or a decision. -/
inductive WordResult where
  | word (w : Width) (n : Nat)
  | nat (n : Nat)
  | dec (b : Bool)
  deriving BEq, DecidableEq, Repr

/-- The number a result stands for (a decision as `0` or `1`). -/
def WordResult.val : WordResult → Nat
  | .word _ n | .nat n => n
  | .dec b => if b then 1 else 0

namespace WordOp

/-- **The exact meaning** of operation `op` at width `w`, on every `Nat` (the second argument is
ignored by the unary operations; `ofNat`'s first is a `Nat`, every other argument a word's
number); the module's docstring gives the reference body each line transcribes. -/
def eval (w : Width) : WordOp → Nat → Nat → WordResult
  | .add, a, b => .word w ((a + b) % w.size)
  | .sub, a, b => .word w ((w.size - b + a) % w.size)
  | .mul, a, b => .word w ((a * b) % w.size)
  | .div, a, b => .word w (a / b)
  | .mod, a, b => .word w (a % b)
  | .land, a, b => .word w (a &&& b)
  | .lor, a, b => .word w (a ||| b)
  | .xor, a, b => .word w (a ^^^ b)
  | .shiftLeft, a, b => .word w ((a <<< (b % w.bits)) % w.size)
  | .shiftRight, a, b => .word w (a >>> (b % w.bits))
  | .complement, a, _ => .word w ((w.size - 1) ^^^ a)
  | .neg, a, _ => .word w ((w.size - a) % w.size)
  | .decEq, a, b => .dec (a == b)
  | .decLt, a, b => .dec (decide (a < b))
  | .decLe, a, b => .dec (decide (a ≤ b))
  | .ofNat, a, _ => .word w (a % w.size)
  | .toNat, a, _ => .nat a
  | .convert w', a, _ => if w.bits ≤ w'.bits then .word w' a else .word w' (a % w'.size)
  | .clz64, a, _ => .word w (if a == 0 then 64 else 63 - Nat.log2 a)
  | .mulWideLo, a, b => .word w ((a * b) % w.size)
  | .mulWideHi, a, b => .word w ((a * b) / w.size)
  | .divWideQ, _, _ | .divWideR, _, _
  | .addCarryLo, _, _ | .addCarryOut, _, _
  | .subBorrowLo, _, _ | .subBorrowOut, _, _ => .word w 0

/-- **The exact meaning** of ternary 64-bit limb-component operations on `Nat`s; `none` on
`divWideQ`/`divWideR` when `hi ≥ d` (including `d = 0`, where x86 `div` traps) and on non-ternary
operations. -/
def eval3 (w : Width) : WordOp → Nat → Nat → Nat → Option WordResult
  | .divWideQ, hi, lo, d => if hi < d then some (.word w ((hi * w.size + lo) / d)) else none
  | .divWideR, hi, lo, d => if hi < d then some (.word w ((hi * w.size + lo) % d)) else none
  | .addCarryLo, a, b, c =>
    let cin := if c == 0 then 0 else 1
    some (.word w ((a + b + cin) % w.size))
  | .addCarryOut, a, b, c =>
    let cin := if c == 0 then 0 else 1
    some (.word w (if w.size ≤ a + b + cin then 1 else 0))
  | .subBorrowLo, a, b, c =>
    let bin := if c == 0 then 0 else 1
    some (.word w (if a < b + bin then w.size + a - (b + bin) else a - (b + bin)))
  | .subBorrowOut, a, b, c =>
    let bin := if c == 0 then 0 else 1
    some (.word w (if a < b + bin then 1 else 0))
  | _, _, _, _ => none

/-- **In range in, in range out**: every word result of an operation on words below `2^w` is
below its own width's size (what the tagged lowering, and a raw representation later, need).
`ofNat`'s argument is a `Nat` and needs no bound. These are exactly the arguments F6w passes
(`Program.wordValue`): it reads a word only below its width's size (`asWord?`), passes `ofNat`'s
literal as it is, and passes `0` as a unary operation's second argument; so every tower F6w builds
is in range. -/
theorem eval_word_lt (w : Width) (op : WordOp) (a b : Nat) (ha : op = .ofNat ∨ a < w.size)
    (hb : b < w.size) (w' : Width) (n : Nat) (h : eval w op a b = .word w' n) : n < w'.size := by
  have hs := w.size_pos
  have hge65 : 65 ≤ w.size := by cases w <;> decide
  have hpow : ∀ x, x < w.size → x < 2 ^ w.bits := fun _ hx => hx
  cases op
  case ofNat =>
    simp only [eval, WordResult.word.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Nat.mod_lt _ hs
  all_goals replace ha : a < w.size := ha.resolve_left (by simp)
  all_goals simp only [eval, WordResult.word.injEq, reduceCtorEq] at h
  case convert w'' =>
    by_cases hw : w.bits ≤ w''.bits
    · simp only [hw, ↓reduceIte, WordResult.word.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.lt_of_lt_of_le ha (Width.size_le_of_bits_le hw)
    · simp only [hw, ↓reduceIte, WordResult.word.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.mod_lt _ (Width.size_pos _)
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact Nat.mod_lt _ hs
  · exact Nat.mod_lt _ hs
  · exact Nat.mod_lt _ hs
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha
  · exact Nat.lt_of_le_of_lt Nat.and_le_left ha
  · exact Nat.or_lt_two_pow (hpow _ ha) (hpow _ hb)
  · exact Nat.xor_lt_two_pow (hpow _ ha) (hpow _ hb)
  · exact Nat.mod_lt _ hs
  · exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  · exact Nat.xor_lt_two_pow (hpow _ (Nat.sub_lt hs Nat.one_pos)) (hpow _ ha)
  · exact Nat.mod_lt _ hs
  · split <;> omega
  · exact Nat.mod_lt _ hs
  · have hmul : a * b < w.size * w.size := by
      have h1 : a * b ≤ (w.size - 1) * b := Nat.mul_le_mul_right b (by omega)
      have h2 : (w.size - 1) * b ≤ (w.size - 1) * w.size :=
        Nat.mul_le_mul_left (w.size - 1) (Nat.le_of_lt hb)
      have h3 : (w.size - 1) * w.size + w.size = w.size * w.size := by
        rw [Nat.sub_mul, Nat.one_mul]
        have := Nat.le_mul_of_pos_left w.size hs
        omega
      omega
    exact (Nat.div_lt_iff_lt_mul hs).2 hmul
  · exact hs
  · exact hs
  · exact hs
  · exact hs
  · exact hs
  · exact hs

/-- **In range in, in range out** for ternary limb-component operations. -/
theorem eval3_word_lt (w : Width) (op : WordOp) (a b c : Nat) (ha : a < w.size) (hb : b < w.size)
    (hc : c < w.size) (w' : Width) (n : Nat) (h : eval3 w op a b c = some (.word w' n)) :
    n < w'.size := by
  have hs := w.size_pos
  have hge2 : 2 ≤ w.size := by cases w <;> decide
  cases op <;> simp only [eval3, Option.some.injEq, WordResult.word.injEq, reduceCtorEq] at h
  case divWideQ =>
    split at h
    · rename_i hlt
      simp only [Option.some.injEq, WordResult.word.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd : 0 < c := by omega
      rw [Nat.div_lt_iff_lt_mul hd]
      have hle : (a + 1) * w.size ≤ c * w.size := Nat.mul_le_mul_right w.size hlt
      rw [Nat.add_mul, Nat.one_mul] at hle
      rw [Nat.mul_comm w.size c]
      omega
    · cases h
  case divWideR =>
    split at h
    · rename_i hlt
      simp only [Option.some.injEq, WordResult.word.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hc
    · cases h
  case addCarryLo =>
    obtain ⟨rfl, rfl⟩ := h
    exact Nat.mod_lt _ hs
  case addCarryOut =>
    obtain ⟨rfl, rfl⟩ := h
    split <;> split <;> omega
  case subBorrowLo =>
    obtain ⟨rfl, rfl⟩ := h
    split <;> split <;> omega
  case subBorrowOut =>
    obtain ⟨rfl, rfl⟩ := h
    split <;> split <;> omega

end WordOp

/-! ## Hardware 64-bit Limb Primitives (`IxCC.BigNat.LimbOps`)

The five user-level 64-bit hardware limb primitives pinned from `IxCC.BigNat.LimbOps`, their
decomposition into scalar `WordOp` components (erased into `Prod.mk` and eliminated by `Anf.shrink`,
then pair-fused directly onto single `Lir.Stmt.limb` / `Lir.Rhs.bsr64` instructions with zero heap
allocation), and exact conservativity theorems against `IxCC.BigNat.LimbOps`. -/

/-- The five 64-bit hardware limb primitives in `IxCC.BigNat.LimbOps`. -/
inductive LimbOp where
  | addCarry64
  | subBorrow64
  | mulWide64
  | divWide64
  | clz64
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace LimbOp

def all : List LimbOp := [.addCarry64, .subBorrow64, .mulWide64, .divWide64, .clz64]

def leanName : LimbOp → String
  | .addCarry64 => "IxCC.BigNat.addCarry64"
  | .subBorrow64 => "IxCC.BigNat.subBorrow64"
  | .mulWide64 => "IxCC.BigNat.mulWide64"
  | .divWide64 => "IxCC.BigNat.divWide64"
  | .clz64 => "IxCC.BigNat.clz64"

/-- Full source-level arity (including `divWide64`'s proof argument `_h : hi < d`). -/
def srcArity : LimbOp → Nat
  | .addCarry64 => 3
  | .subBorrow64 => 3
  | .mulWide64 => 2
  | .divWide64 => 4
  | .clz64 => 1

/-- The scalar `WordOp` component(s) that a `LimbOp` decomposes into. -/
def components : LimbOp → WordOp × Option WordOp
  | .addCarry64 => (.addCarryLo, some .addCarryOut)
  | .subBorrow64 => (.subBorrowLo, some .subBorrowOut)
  | .mulWide64 => (.mulWideLo, some .mulWideHi)
  | .divWide64 => (.divWideQ, some .divWideR)
  | .clz64 => (.clz64, none)

/-- Whether the second component of a pair-returning limb op is a `Bool` (vs `UInt64`). -/
def sndIsBool : LimbOp → Bool
  | .addCarry64 | .subBorrow64 => true
  | .mulWide64 | .divWide64 | .clz64 => false

/-! ### Conservativity Theorems against `IxCC.BigNat.LimbOps` -/

theorem clz64_conservative (x : UInt64) :
    (WordOp.eval .w64 .clz64 x.toNat 0).val = (IxCC.BigNat.clz64 x).toNat := by
  by_cases hx : x = 0
  · subst hx; decide
  · have hx0 : x.toNat ≠ 0 := fun h0 => hx (UInt64.toNat_inj.mp (by simpa using h0))
    have hbeq : (x.toNat == 0) = false := beq_false_of_ne hx0
    rw [IxCC.BigNat.clz64_toNat_of_ne_zero x hx]
    simp only [WordOp.eval, WordResult.val, hbeq, Bool.false_eq_true, ↓reduceIte]

theorem mulWide64_lo_conservative (a b : UInt64) :
    (WordOp.eval .w64 .mulWideLo a.toNat b.toNat).val = (IxCC.BigNat.mulWide64 a b).1.toNat := by
  unfold IxCC.BigNat.mulWide64
  simp only [WordOp.eval, WordResult.val, Width.size, Width.bits, UInt64.toNat_ofNat']
  exact (Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)).symm

theorem mulWide64_hi_conservative (a b : UInt64) :
    (WordOp.eval .w64 .mulWideHi a.toNat b.toNat).val = (IxCC.BigNat.mulWide64 a b).2.toNat := by
  unfold IxCC.BigNat.mulWide64
  have ha := IxCC.BigNat.uint64_toNat_lt a
  have hb := IxCC.BigNat.uint64_toNat_lt b
  have hdiv : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]
    have h1 : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  simp only [WordOp.eval, WordResult.val, Width.size, Width.bits, UInt64.toNat_ofNat']
  exact (Nat.mod_eq_of_lt hdiv).symm

theorem divWide64_q_conservative (hi lo d : UInt64) (h : hi < d) :
    WordOp.eval3 .w64 .divWideQ hi.toNat lo.toNat d.toNat =
      some (.word .w64 (IxCC.BigNat.divWide64 hi lo d h).1.toNat) := by
  have hlt : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
  rw [IxCC.BigNat.divWide64_fst hi lo d h]
  simp only [WordOp.eval3, Width.size, Width.bits, hlt, ↓reduceIte]

theorem divWide64_r_conservative (hi lo d : UInt64) (h : hi < d) :
    WordOp.eval3 .w64 .divWideR hi.toNat lo.toNat d.toNat =
      some (.word .w64 (IxCC.BigNat.divWide64 hi lo d h).2.toNat) := by
  have hlt : hi.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp h
  rw [IxCC.BigNat.divWide64_snd hi lo d h]
  simp only [WordOp.eval3, Width.size, Width.bits, hlt, ↓reduceIte]

theorem addCarry64_lo_conservative (a b : UInt64) (c : Bool) :
    WordOp.eval3 .w64 .addCarryLo a.toNat b.toNat c.toNat =
      some (.word .w64 (IxCC.BigNat.addCarry64 a b c).1.toNat) := by
  cases c <;>
    simp [WordOp.eval3, IxCC.BigNat.addCarry64, Width.size, Width.bits]

theorem addCarry64_out_conservative (a b : UInt64) (c : Bool) :
    WordOp.eval3 .w64 .addCarryOut a.toNat b.toNat c.toNat =
      some (.word .w64 (IxCC.BigNat.addCarry64 a b c).2.toNat) := by
  cases c
  · simp only [WordOp.eval3, IxCC.BigNat.addCarry64, Width.size, Width.bits, Bool.toNat_false,
      beq_self_eq_true, ↓reduceIte, Nat.add_zero, Option.some.injEq, WordResult.word.injEq, true_and]
    split <;> simp [*]
  · simp only [WordOp.eval3, IxCC.BigNat.addCarry64, Width.size, Width.bits, Bool.toNat_true,
      show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
      WordResult.word.injEq, true_and]
    split <;> simp [*]

theorem subBorrow64_lo_conservative (a b : UInt64) (bIn : Bool) :
    WordOp.eval3 .w64 .subBorrowLo a.toNat b.toNat bIn.toNat =
      some (.word .w64 (IxCC.BigNat.subBorrow64 a b bIn).1.toNat) := by
  have ha := IxCC.BigNat.uint64_toNat_lt a
  have hb := IxCC.BigNat.uint64_toNat_lt b
  cases bIn
  · simp only [WordOp.eval3, IxCC.BigNat.subBorrow64, Width.size, Width.bits, Bool.toNat_false,
      UInt64.toNat_ofNat', beq_self_eq_true, ↓reduceIte]
    split <;> · congr 2; exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [WordOp.eval3, IxCC.BigNat.subBorrow64, Width.size, Width.bits, Bool.toNat_true,
      UInt64.toNat_ofNat', show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    split <;> · congr 2; exact (Nat.mod_eq_of_lt (by omega)).symm

theorem subBorrow64_out_conservative (a b : UInt64) (bIn : Bool) :
    WordOp.eval3 .w64 .subBorrowOut a.toNat b.toNat bIn.toNat =
      some (.word .w64 (IxCC.BigNat.subBorrow64 a b bIn).2.toNat) := by
  cases bIn
  · simp only [WordOp.eval3, IxCC.BigNat.subBorrow64, Bool.toNat_false,
      beq_self_eq_true, ↓reduceIte, Nat.add_zero, Option.some.injEq, WordResult.word.injEq, true_and]
    split <;> simp [*]
  · simp only [WordOp.eval3, IxCC.BigNat.subBorrow64, Bool.toNat_true,
      show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
      WordResult.word.injEq, true_and]
    split <;> simp [*]

end LimbOp

end IxCC.Src
