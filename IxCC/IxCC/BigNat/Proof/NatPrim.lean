import IxCC.BigNat.Proof.NatEntry
import IxCC.Lam.Syntax

/-! # The library's contract, indexed by the evaluators' primitives (`IxCC.BigNat.Proof.NatPrim`)

Design note: `plans/ONE-PIPELINE.md`, sections 4.3, 4.4 and 4.6; statement `NatLib.Spec` of the
design's statement library.

`Lam.Prim.sem` is the meaning every evaluator from Lam to `Fir` gives a `Nat` primitive on
literals. `primEntry` is the library's answer for the same primitive: its entry over `Nat`
(`IxCC.BigNat.NatEntry`), applied to the same naturals. `primEntry_eq_sem` says the two are the
same function for every `Nat` primitive: where the primitive has a result, the entry returns
it, and they agree on an arity mismatch as well.

`primEntry_spec` is the design's `NatLib.Spec` with the Lean function in place of the run of
the compiled image: `op.sem ns = some r → primEntry op ns = some r`. It is a theorem about Lean
functions. `NatLib.Spec` proper is about `Fir.run` of the pinned image of these functions and
is obtained from this one by the correctness of the pipeline on the library as a program
(grounding, progress, the front theorem); until then it is the ledger's named hypothesis
(decision D6). Nothing here imports an evaluator: only the primitive type and its meaning.
-/

set_option autoImplicit false

namespace IxCC.BigNat.NatEntry

open IxCC.Src (PrimResult)

/-- **The library's answer for a `Nat` primitive** on literal arguments: its entry over `Nat`.
`none` on an arity mismatch and for a word primitive, which has no slow path. -/
def primEntry : Lam.Prim → List Nat → Option PrimResult
  | .natAdd, [a, b] => some (.nat (add a b))
  | .natSub, [a, b] => some (.nat (sub a b))
  | .natMul, [a, b] => some (.nat (mul a b))
  | .natDiv, [a, b] => some (.nat (div a b))
  | .natMod, [a, b] => some (.nat (mod a b))
  | .natPow, [a, b] => some (.nat (pow a b))
  | .natGcd, [a, b] => some (.nat (gcd a b))
  | .natBeq, [a, b] => some (.bool (beq a b))
  | .natBle, [a, b] => some (.bool (ble a b))
  | .natBlt, [a, b] => some (.bool (blt a b))
  | .natLand, [a, b] => some (.nat (land a b))
  | .natLor, [a, b] => some (.nat (lor a b))
  | .natXor, [a, b] => some (.nat (xor a b))
  | .natShl, [a, b] => some (.nat (shiftLeft a b))
  | .natShr, [a, b] => some (.nat (shiftRight a b))
  | .natPred, [a] => some (.nat (pred a))
  | _, _ => none

/-- The Lean constant that is the slow path of each `Nat` primitive (`none` for a word). -/
def primEntryName : Lam.Prim → Option String
  | .natAdd => some "IxCC.BigNat.NatEntry.add"
  | .natSub => some "IxCC.BigNat.NatEntry.sub"
  | .natMul => some "IxCC.BigNat.NatEntry.mul"
  | .natDiv => some "IxCC.BigNat.NatEntry.div"
  | .natMod => some "IxCC.BigNat.NatEntry.mod"
  | .natPow => some "IxCC.BigNat.NatEntry.pow"
  | .natGcd => some "IxCC.BigNat.NatEntry.gcd"
  | .natBeq => some "IxCC.BigNat.NatEntry.beq"
  | .natBle => some "IxCC.BigNat.NatEntry.ble"
  | .natBlt => some "IxCC.BigNat.NatEntry.blt"
  | .natLand => some "IxCC.BigNat.NatEntry.land"
  | .natLor => some "IxCC.BigNat.NatEntry.lor"
  | .natXor => some "IxCC.BigNat.NatEntry.xor"
  | .natShl => some "IxCC.BigNat.NatEntry.shiftLeft"
  | .natShr => some "IxCC.BigNat.NatEntry.shiftRight"
  | .natPred => some "IxCC.BigNat.NatEntry.pred"
  | .word _ _ => none

/-- Division as the evaluators write it. -/
theorem div_eq_sem (a b : Nat) : div a b = if b == 0 then 0 else a / b := by
  rw [div_eq]
  by_cases h : b = 0
  · have hb : (b == 0) = true := beq_iff_eq.mpr h
    rw [ite_eq_left hb, h, Nat.div_zero]
  · have hb : ¬ (b == 0) = true := fun hc => h (eq_of_beq hc)
    rw [ite_eq_right hb]

/-- Remainder as the evaluators write it. -/
theorem mod_eq_sem (a b : Nat) : mod a b = if b == 0 then a else a % b := by
  rw [mod_eq]
  by_cases h : b = 0
  · have hb : (b == 0) = true := beq_iff_eq.mpr h
    rw [ite_eq_left hb, h, Nat.mod_zero]
  · have hb : ¬ (b == 0) = true := fun hc => h (eq_of_beq hc)
    rw [ite_eq_right hb]

/-- Right shift as the evaluators write it. -/
theorem shiftRight_eq_sem (a b : Nat) :
    shiftRight a b = if a.log2 < b then 0 else a / 2 ^ b := by
  rw [shiftRight_eq_div]
  by_cases h : a.log2 < b
  · rw [ite_eq_left h]
    by_cases h0 : a = 0
    · subst h0
      exact Nat.zero_div _
    · exact Nat.div_eq_of_lt ((Nat.log2_lt h0).mp h)
  · rw [ite_eq_right h]

/-- **The library computes every `Nat` primitive**: on every argument list, the entry's answer
is the primitive's meaning. -/
theorem primEntry_eq_sem (op : Lam.Prim) (ns : List Nat) (hop : op.isWord = false) :
    primEntry op ns = op.sem ns := by
  cases op with
  | word w o => cases hop
  | natAdd =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (add_eq a b)
  | natSub =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (sub_eq a b)
  | natMul =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (mul_eq a b)
  | natDiv =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (div_eq_sem a b)
  | natMod =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (mod_eq_sem a b)
  | natPow =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (pow_eq a b)
  | natGcd =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (gcd_eq a b)
  | natBeq =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.bool t)) (beq_eq a b)
  | natBle =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.bool t)) (ble_eq a b)
  | natBlt =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.bool t)) (blt_eq a b)
  | natLand =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (land_eq a b)
  | natLor =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (lor_eq a b)
  | natXor =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (xor_eq a b)
  | natShl =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (shiftLeft_eq_mul a b)
  | natShr =>
    match ns with
    | [] | [_] | _ :: _ :: _ :: _ => rfl
    | [a, b] => exact congrArg (fun t => some (PrimResult.nat t)) (shiftRight_eq_sem a b)
  | natPred =>
    match ns with
    | [] | _ :: _ :: _ => rfl
    | [a] => exact congrArg (fun t => some (PrimResult.nat t)) (pred_eq a)

/-- **`NatLib.Spec` for the library's Lean functions**: whatever a `Nat` primitive means on
literals, the library's entry returns. -/
theorem primEntry_spec (op : Lam.Prim) (ns : List Nat) (r : PrimResult)
    (hop : op.isWord = false) (hs : op.sem ns = some r) : primEntry op ns = some r := by
  rw [primEntry_eq_sem op ns hop]
  exact hs

/-- An entry answers exactly where the primitive has a meaning. -/
theorem primEntry_isSome (op : Lam.Prim) (ns : List Nat) (hop : op.isWord = false) :
    (primEntry op ns).isSome = (op.sem ns).isSome := by
  rw [primEntry_eq_sem op ns hop]

/-- Every `Nat` primitive has an entry, and no word primitive has one. -/
theorem primEntryName_isSome (op : Lam.Prim) : (primEntryName op).isSome = !op.isWord := by
  cases op <;> rfl

end IxCC.BigNat.NatEntry
