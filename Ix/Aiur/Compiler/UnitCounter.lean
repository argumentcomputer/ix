module
public import Ix.Aiur.Stages.Bytecode

/-!
Unit-counter certificates for singleton recursive components.

The checker follows only field constants, addition, subtraction by constants,
and multiplication by one (or two constants). Other instruction outputs remain
unknown. Each constrained self-call must shift the same input by exactly one,
or each returning path must contain at most one self-call and return its chosen
output shifted by exactly one. Both directions are supported. Every branch is
checked; shared continuations are conservatively left ranked.

No source name, type annotation, hint equation, or memory-tree assumption is
trusted. The native constructor repeats this check over its actual bytecode.
A finite provider cycle in such a function would be a nonempty unit-step field
cycle. The lemmas below exclude every such cycle shorter than the characteristic.
The verified bound on lookup consumers bounds every simple provider cycle by
a strictly smaller number. Component ordering still excludes cross-component
cycles; all unrecognized recursive components retain their dynamic ranks.
-/

public section
@[expose] section

namespace Aiur.Bytecode.UnitCounter

structure Affine where
  base : Option Nat
  offset : Aiur.G
  deriving BEq, Repr

def constant (x : Aiur.G) : Affine := ⟨none, x⟩
def affVar (i : Nat) : Affine := ⟨some i, 0⟩

def add (a b : Option Affine) : Option Affine := do
  let a ← a
  let b ← b
  match a.base, b.base with
  | none, base | base, none => pure ⟨base, a.offset + b.offset⟩
  | _, _ => none

def sub (a b : Option Affine) : Option Affine := do
  let a ← a
  let b ← b
  if b.base.isNone then pure ⟨a.base, a.offset - b.offset⟩ else none

def mul (a b : Option Affine) : Option Affine := do
  let a ← a
  let b ← b
  if a.base.isNone && a.offset == 1 then pure b
  else if b.base.isNone && b.offset == 1 then pure a
  else if a.base.isNone && b.base.isNone then pure (constant (a.offset * b.offset))
  else none

inductive Mode where
  | input
  | output
  deriving BEq, Repr

structure Certificate where
  mode : Mode
  column : Nat
  step : Aiur.G
  deriving Repr

structure State where
  values : Array (Option Affine)
  recursiveOutput : Option Nat := none

def outputCount : Bytecode.Op → Nat
  | .const .. | .add .. | .sub .. | .mul .. | .eqZero .. | .store ..
  | .u8ShiftLeft .. | .u8ShiftRight .. | .u8Xor .. | .u8And .. | .u8Or ..
  | .u8LessThan .. | .u32LessThan .. | .unconstrainedGInverse ..
  | .u32ToField .. => 1
  | .call _ _ n _ | .load n _ | .ioRead _ _ n => n
  | .ioGetInfo .. | .u8Add .. | .u8Mul .. | .u8Sub .. | .u8XorSplit7 ..
  | .u8XorSplit4 .. | .unconstrainedBigUintDivMod .. => 2
  | .u8BitDecomposition .. | .unconstrainedGToBytes .. => 8
  | .unconstrainedU32Add .. | .unconstrainedU32Add3 .. => 5
  | .assertEq .. | .ioSetInfo .. | .ioWrite .. | .debug ..
  | .u8RangeCheck .. => 0

def stepOp (self : Nat) (candidate : Certificate) (state : State)
    (op : Bytecode.Op) : Option State := do
  let get := fun i => (state.values[i]?).getD none
  match op with
  | .const x => pure { state with values := state.values.push (some (constant x)) }
  | .add i j => pure { state with values := state.values.push (add (get i) (get j)) }
  | .sub i j => pure { state with values := state.values.push (sub (get i) (get j)) }
  | .mul i j => pure { state with values := state.values.push (mul (get i) (get j)) }
  | .call callee args n false =>
    if callee == self then
      match candidate.mode with
      | .input =>
        let argument ← args[candidate.column]?
        if get argument != some ⟨some candidate.column, candidate.step⟩ then none
        else pure { state with values := state.values ++ Array.replicate n none }
      | .output =>
        if state.recursiveOutput.isSome || candidate.column ≥ n then none
        else
          let marker := state.values.size + candidate.column
          let outputs := (Array.range n).map fun j =>
            if j == candidate.column then some (affVar marker) else none
          pure { values := state.values ++ outputs, recursiveOutput := some marker }
    else pure { state with values := state.values ++ Array.replicate n none }
  | op => pure { state with values := state.values ++ Array.replicate (outputCount op) none }

def check (fuel : Nat) (self : Nat) (candidate : Certificate) (state : State)
    (block : Bytecode.Block) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match block.ops.foldlM (stepOp self candidate) state with
    | none => false
    | some state =>
      match block.ctrl with
      | .return _ outputs =>
        match candidate.mode, state.recursiveOutput with
        | .input, _ | .output, none => true
        | .output, some marker =>
          match outputs[candidate.column]? with
          | none => false
          | some index =>
            (state.values[index]?).getD none == some ⟨some marker, candidate.step⟩
      | .match _ cases fallback =>
        cases.all (fun (_, branch) => check fuel self candidate state branch) &&
          fallback.all (check fuel self candidate state)
      | .yield .. | .matchContinue .. => false

def resultSize? (fuel : Nat) (block : Bytecode.Block) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match block.ctrl with
    | .return _ output => some output.size
    | .match _ cases fallback =>
      (cases.findSome? (fun (_, b) => resultSize? fuel b)).orElse
        (fun _ => fallback.bind (resultSize? fuel))
    | _ => none

/-- Infer a checked unit-step relation on a function input or output. Only
self-recursive calls are eligible; the component validator separately rules
out any unranked internal edge to a different function. -/
def find? (self : Nat) (f : Bytecode.Function) : Option Certificate := Id.run do
  -- Exceeding the analysis depth conservatively retains ordinary ranks.
  let fuel := 256
  let state : State := {
    values := (Array.range f.layout.inputSize).map (some ∘ affVar) }
  for mode in [Mode.input, Mode.output] do
    let columns := match mode with
      | .input => f.layout.inputSize
      | .output => (resultSize? fuel f.body).getD 0
    for column in [:columns] do
      for step in [(1 : Aiur.G), (0 : Aiur.G) - 1] do
        let candidate := { mode, column, step }
        if check fuel self candidate state f.body then return some candidate
  return none


namespace Proofs

theorem add_mod_ne_self {p a m : Nat} (ha : a < p)
    (hm : 0 < m) (hmp : m < p) : (a + m) % p ≠ a := by
  intro h
  by_cases hlt : a + m < p
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hge : p ≤ a + m := by omega
    have hsub : a + m - p < p := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at h
    omega

theorem unit_walk {p m : Nat} (value : Nat → Nat)
    (initial : value 0 < p)
    (step : ∀ i, i < m → value (i + 1) = (value i + 1) % p) :
    ∀ i, i ≤ m → value i = (value 0 + i) % p := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [Nat.mod_eq_of_lt initial]
  | succ i ih =>
    intro hi
    rw [step i (by omega), ih (by omega)]
    simp [Nat.add_assoc, Nat.mod_add_mod]

theorem no_short_unit_cycle {p m : Nat} (value : Nat → Nat)
    (initial : value 0 < p) (positive : 0 < m) (short : m < p)
    (step : ∀ i, i < m → value (i + 1) = (value i + 1) % p) :
    value m ≠ value 0 := by
  rw [unit_walk value initial step m (by omega)]
  exact add_mod_ne_self initial positive short

theorem no_short_reverse_unit_cycle {p m : Nat} (value : Nat → Nat)
    (bounded : ∀ i, i ≤ m → value i < p) (positive : 0 < m) (short : m < p)
    (step : ∀ i, i < m → value i = (value (i + 1) + 1) % p) :
    value m ≠ value 0 := by
  let reversed := fun i => value (m - i)
  have initial : reversed 0 < p := by
    simpa [reversed] using bounded m (by omega)
  have rstep : ∀ i, i < m → reversed (i + 1) = (reversed i + 1) % p := by
    intro i hi
    have h := step (m - (i + 1)) (by omega)
    have heq : m - (i + 1) + 1 = m - i := by omega
    simpa [reversed, heq] using h
  have h := no_short_unit_cycle reversed initial positive short rstep
  simp only [reversed, Nat.sub_self, Nat.sub_zero] at h
  exact Ne.symm h

end Proofs

namespace Proofs

theorem no_short_field_cycle {m : Nat} (value : Nat → G)
    (positive : 0 < m) (short : m < gSize.toNat)
    (step : ∀ i, i < m → value (i + 1) = value i + 1) :
    value m ≠ value 0 := by
  have initial : (value 0).n < gSize.toNat := by
    simpa only [G.n, UInt64.lt_iff_toNat_lt] using (value 0).property
  have nstep : ∀ i, i < m → (value (i + 1)).n = ((value i).n + 1) % gSize.toNat := by
    intro i hi
    rw [step i hi, G.add_one_n]
  intro h
  exact no_short_unit_cycle (fun i => (value i).n) initial positive short nstep
    (congrArg G.n h)

end Proofs

namespace Proofs

theorem no_short_reverse_field_cycle {m : Nat} (value : Nat → G)
    (positive : 0 < m) (short : m < gSize.toNat)
    (step : ∀ i, i < m → value i = value (i + 1) + 1) :
    value m ≠ value 0 := by
  have bounded : ∀ i, i ≤ m → (value i).n < gSize.toNat := by
    intro i _
    simpa only [G.n, UInt64.lt_iff_toNat_lt] using (value i).property
  have nstep : ∀ i, i < m → (value i).n = ((value (i + 1)).n + 1) % gSize.toNat := by
    intro i hi
    rw [step i hi, G.add_one_n]
  intro h
  exact no_short_reverse_unit_cycle (fun i => (value i).n) bounded positive short nstep
    (congrArg G.n h)

theorem no_short_decrement_cycle {m : Nat} (value : Nat → G)
    (positive : 0 < m) (short : m < gSize.toNat)
    (step : ∀ i, i < m → value (i + 1) = value i - 1) :
    value m ≠ value 0 := by
  apply no_short_reverse_field_cycle value positive short
  intro i hi
  rw [step i hi, G.sub_one_add_one]

theorem no_short_negative_field_cycle {m : Nat} (value : Nat → G)
    (positive : 0 < m) (short : m < gSize.toNat)
    (step : ∀ i, i < m → value (i + 1) = value i + ((0 : G) - 1)) :
    value m ≠ value 0 := by
  apply no_short_decrement_cycle value positive short
  intro i hi
  rw [step i hi, G.add_neg_one_eq_sub]

end Proofs

end Aiur.Bytecode.UnitCounter

end
end
