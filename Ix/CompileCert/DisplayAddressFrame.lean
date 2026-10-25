import Ix.Compile.Pass.SideCar
import Ix.CompileCert.Loop
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

/-! # Original-name keys under the actual display edit

Reserved destinations cannot recreate a nonreserved key. This is a local
map equation, with no destination-value or later live-state assertion.
-/

namespace Ix.CompileCert.DisplayAddressFrame
open Ix (Name)
open Ix.Compile.Pass
open Ix.Compile.ExactKey (ExactName)

theorem appendComps_reserved {n : Name} (reserved : hasReserved n = true) (cs : List Comp) :
    hasReserved (appendComps n cs) = true := by
  induction cs generalizing n with
  | nil => exact reserved
  | cons c cs ih =>
    cases c <;> apply ih <;> simp [hasReserved, Name.mkStr, Name.mkNat, Id.run, reserved]

/-- Both actual naming branches insert the reserved component; the stored
hashes and the selected prefix's identity are irrelevant to this fact. -/
theorem ixAuxName_reserved {members : Array Name} {rep0 n d : Name} {perm : Array (Option Nat)}
    (run : ixAuxName members rep0 perm n = some d) : hasReserved d = true := by
  have marker : isReservedComponent ixComponent = true := by
    simp [isReservedComponent]
  unfold ixAuxName at run
  simp only [Id.run, Loop.idBind, Loop.idPure] at run
  repeat' first
    | split at run
    | (cases run <;> apply appendComps_reserved <;>
        simp only [hasReserved, Name.mkStr, Id.run, marker, Bool.true_or])

def ReservedRange (edit : SideCarEdit) : Prop :=
  ∀ (key : ExactName) d, edit.display.get? key = some d → hasReserved d = true

/-- The actual insert-then-erase loop, in its original order. The final
extra-name loop changes no address. No injectivity of the rename is needed. -/
theorem sideCar_original_keys (edit : SideCarEdit) (named : Array (Name × Ixon.Named))
    (input : Std.HashMap ExactName Address) (extra : Std.HashSet Name)
    (range : ReservedRange edit) (q : ExactName) (plain : hasReserved q = false) :
    (edit.apply named input extra).2.1.get? q =
      if edit.display.contains q then none else input.get? q := by
  let step (m : Std.HashMap ExactName Address) (p : ExactName × Address) :=
    match edit.display.get? p.1 with
    | none => m
    | some d => (m.insert d p.2).erase p.1
  have evaluated : (edit.apply named input extra).2.1 = input.toList.foldl step input := by
    unfold SideCarEdit.apply
    simp only [Id.run, Loop.idBind, Loop.idPure, Std.HashMap.forIn_eq_forIn_toList]
    rw [Loop.forIn_id_list _ (by intro _ _; split <;> rfl)]
    congr 1
    funext m p
    dsimp only [step]
    cases edit.display.get? p.1 <;> rfl
  rw [evaluated]
  have contains (key : ExactName) : edit.display.contains key = (edit.display.get? key).isSome :=
    Std.HashMap.contains_eq_isSome_getElem?
  have getStep (m : Std.HashMap ExactName Address) (p : ExactName × Address) :
      (step m p).get? q =
        if p.1 == q then (if edit.display.contains q then none else m.get? q) else m.get? q := by
    obtain ⟨key, value⟩ := p
    by_cases same : key = q
    · subst key
      cases lookup : edit.display.get? q <;>
        simp only [step, lookup, beq_self_eq_true, contains, Option.isSome_none,
          Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      exact Std.HashMap.getElem?_erase_self
    · cases lookup : edit.display.get? key with
      | none => simp only [step, lookup, beq_iff_eq, same, ↓reduceIte]
      | some d =>
        have different : (show ExactName from d) ≠ q := by
          intro equal
          have reserved := range key d lookup
          rw [equal, plain] at reserved
          cases reserved
        simp only [step, lookup]
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase,
          Std.HashMap.getElem?_insert (k := (show ExactName from d)) (a := q)]
        have unequal : ((show ExactName from d) == q) = false := beq_eq_false_iff_ne.mpr different
        simp only [beq_iff_eq, same, unequal, Bool.false_eq_true, ↓reduceIte]
        exact (Std.HashMap.get?_eq_getElem?).symm
  cases lookup : edit.display.get? q with
  | none =>
    have absent : edit.display.contains q = false := by
      rw [contains, lookup]; rfl
    rw [absent]
    apply List.foldlRecOn (motive := fun m : Std.HashMap ExactName Address => m.get? q = input.get? q)
    · rfl
    · intro m held p _; simpa only [getStep, absent, Bool.false_eq_true, ↓reduceIte, ite_self] using held
  | some d =>
    have present : edit.display.contains q = true := by
      rw [contains, lookup]; rfl
    rw [present]
    have keepsNone (xs : List (ExactName × Address)) (m : Std.HashMap ExactName Address)
        (empty : m.get? q = none) : (xs.foldl step m).get? q = none := by
      apply List.foldlRecOn (motive := fun m : Std.HashMap ExactName Address => m.get? q = none)
      · exact empty
      · intro m held p _; simp only [getStep, present, ↓reduceIte, held, ite_self]
    cases old : input.get? q with
    | none => exact keepsNone input.toList input old
    | some value =>
      have member : (q, value) ∈ input.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr old
      obtain ⟨pre, post, whole⟩ := List.mem_iff_append.mp member
      rw [whole, List.foldl_append, List.foldl_cons]
      apply keepsNone
      simp only [getStep, beq_self_eq_true, present, ↓reduceIte]

end Ix.CompileCert.DisplayAddressFrame
