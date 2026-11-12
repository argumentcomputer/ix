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
values), the conversions from and to `Nat`, and the conversions to another width
(`UIntN.toUIntM`). -/
inductive WordOp where
  | add | sub | mul | div | mod | land | lor | xor | shiftLeft | shiftRight
  | complement | neg
  | decEq | decLt | decLe
  | ofNat | toNat
  | convert (to : Width)
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace WordOp

def arity : WordOp → Nat
  | .complement | .neg | .ofNat | .toNat | .convert _ => 1
  | _ => 2

/-- Every operation of a width `w` (the conversions to the three other widths). -/
def ofWidth (w : Width) : List WordOp :=
  [.add, .sub, .mul, .div, .mod, .land, .lor, .xor, .shiftLeft, .shiftRight, .complement, .neg,
   .decEq, .decLt, .decLe, .ofNat, .toNat] ++ (Width.all.filter (· ≠ w)).map .convert

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

/-- **In range in, in range out**: every word result of an operation on words below `2^w` is
below its own width's size (what the tagged lowering, and a raw representation later, need).
`ofNat`'s argument is a `Nat` and needs no bound. These are exactly the arguments F6w passes
(`Program.wordValue`): it reads a word only below its width's size (`asWord?`), passes `ofNat`'s
literal as it is, and passes `0` as a unary operation's second argument; so every tower F6w builds
is in range. -/
theorem eval_word_lt (w : Width) (op : WordOp) (a b : Nat) (ha : op = .ofNat ∨ a < w.size)
    (hb : b < w.size) (w' : Width) (n : Nat) (h : eval w op a b = .word w' n) : n < w'.size := by
  have hs := w.size_pos
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

end WordOp

end IxCC.Src
