/-!
# Fixed point with 16 fractional bits and bounded accumulation

`Fx16` is a fixed-point number `raw / 2^16`, the format chosen for training in `plan.md`. Like
`IxAICore.Fx` (8 fractional bits, kept unchanged for the certified triage models), sums are exact,
a product rounds once toward negative infinity, and a dot product accumulates exactly and rounds
once, so results do not depend on the order of accumulation.

Arithmetic is bounded: `Bounds` is part of a training configuration, and a value or an
accumulation that leaves it is a defined training error, not a silent overflow. An accumulation is
checked by the sum of the absolute values of its terms (`absSum`), which bounds every partial sum
in every order (`natAbs_sum_take_le`, `absSum_perm`), so a fixed-width accumulator of that size is
exact for any evaluation order.
-/

namespace IxAIData

structure Fx16 where
  raw : Int
  deriving DecidableEq, Repr, Inhabited

namespace Fx16

def fracBits : Nat := 16
def scale : Int := 65536

def zero : Fx16 := ⟨0⟩
def one : Fx16 := ⟨65536⟩
def ofInt (n : Int) : Fx16 := ⟨n * 65536⟩

def add (a b : Fx16) : Fx16 := ⟨a.raw + b.raw⟩
def sub (a b : Fx16) : Fx16 := ⟨a.raw - b.raw⟩
/-- `a·b`, rounded once toward negative infinity. -/
def mul (a b : Fx16) : Fx16 := ⟨(a.raw * b.raw) >>> 16⟩

/-- Exact sum of exact products. Extra elements of the longer list are ignored. -/
def dotRaw : List Fx16 → List Fx16 → Int
  | a :: as, b :: bs => a.raw * b.raw + dotRaw as bs
  | _, _ => 0

/-- `Σ aᵢ·bᵢ`, accumulated exactly and rounded once. -/
def dot (as bs : List Fx16) : Fx16 := ⟨dotRaw as bs >>> 16⟩

/-- `w - lr·g/n` with `lr = lrRaw / 2^16`, for a gradient `g` summed exactly over `n` examples:
the learning rate and the batch average are folded into one division, rounded once toward
negative infinity. -/
def step (lrRaw : Int) (n : Nat) (w g : Fx16) : Fx16 :=
  ⟨w.raw - (lrRaw * g.raw) / (65536 * (max n 1 : Nat))⟩

end Fx16

/-- The bounds of bounded arithmetic: every stored value (weights, activations, scores) has
`|raw| ≤ value`, and every exact accumulation (dot products, batch gradient sums, learning-rate
products) has `Σ |term| ≤ acc`. The standard bounds keep each product of two values within the
accumulator and the accumulator within a signed 64-bit word with headroom (`plan.md`: 2^55). -/
structure Bounds where
  value : Nat
  acc : Nat
  deriving DecidableEq, Repr

def Bounds.standard : Bounds := ⟨2 ^ 27, 2 ^ 55⟩

/-- A training run that leaves its bounds stops with the place it left them. -/
inductive BoundError where
  | value (what : String) (raw : Int)
  | acc (what : String) (absSum : Nat)
  deriving Repr

def Bounds.checkValue (b : Bounds) (what : String) (x : Int) : Except BoundError Unit :=
  if x.natAbs ≤ b.value then pure () else throw (.value what x)

def Bounds.checkAcc (b : Bounds) (what : String) (s : Nat) : Except BoundError Unit :=
  if s ≤ b.acc then pure () else throw (.acc what s)

/-- `Σ |tᵢ|`. -/
def absSum : List Int → Nat
  | [] => 0
  | a :: as => a.natAbs + absSum as

def sumInt : List Int → Int
  | [] => 0
  | a :: as => a + sumInt as

/-- Every prefix sum is bounded by the absolute sum. -/
theorem natAbs_sum_take_le (l : List Int) (k : Nat) : (sumInt (l.take k)).natAbs ≤ absSum l := by
  induction l generalizing k with
  | nil => simp [sumInt, absSum]
  | cons a as ih =>
    cases k with
    | zero => simp [sumInt]
    | succ k =>
      simp only [List.take_succ_cons, sumInt, absSum]
      exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left (ih k) _)

/-- The absolute sum does not depend on the order of the terms. -/
theorem absSum_perm {l l' : List Int} (h : l.Perm l') : absSum l = absSum l' := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [absSum, ih]
  | swap a b l => simp only [absSum]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- So within the bound, every partial sum in every order fits the accumulator. -/
theorem partial_sum_within (b : Bounds) {l l' : List Int} (hp : l.Perm l') (hb : absSum l ≤ b.acc)
    (k : Nat) : (sumInt (l'.take k)).natAbs ≤ b.acc :=
  Nat.le_trans (natAbs_sum_take_le l' k) ((absSum_perm hp).symm ▸ hb)

end IxAIData
