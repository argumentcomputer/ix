import Ix.Compile.Pass.SideCar
import Ix.CompileCert.Loop
import Init.Data.String.Lemmas.Pattern.TakeDrop.String
import Ix.Compile.Pass.Driver
import Ix.CompileCert.BlobWrites
import Ix.CompileCert.DisplayRun

/-! # Original-name keys under the actual display edit

Reserved destinations cannot recreate a nonreserved key. This is a local
map equation, with no destination-value or later live-state assertion.
-/

namespace Ix.CompileCert.DisplayAddressFrame
open Ix (Name)
open Ix.Compile.Pass
open Ix.Compile.ExactKey (ExactName)
open Ix.CompileM

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

private def addChoice (f : Name → Option Name) (m : Std.HashMap ExactName Name) (n : ExactName) :=
  if m.contains n then m else match f n with | none => m | some d => m.insert n d

private structure Choices (f : Name → Option Name) (pre : List ExactName) (m : Std.HashMap ExactName Name) : Prop where
  correct : ∀ (q : ExactName) d, m.get? q = some d → f q = some d
  present : ∀ (q : ExactName), q ∈ pre → m.get? q = f q

private theorem choice_get {f pre m} (held : Choices f pre m) (n q : ExactName) :
    (addChoice f m n).get? q = if n == q then f q else m.get? q := by
  have contains (k : ExactName) : m.contains k = (m.get? k).isSome := Std.HashMap.contains_eq_isSome_getElem?
  by_cases same : n = q
  · subst n
    cases old : m.get? q with
    | none =>
      cases pick : f q <;>
        simp only [addChoice, contains, old, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          pick, beq_self_eq_true]
      exact Std.HashMap.getElem?_insert_self
    | some d =>
      simp only [addChoice, contains, old, Option.isSome_some, ↓reduceIte, beq_self_eq_true]
      exact (held.correct q d old).symm
  · unfold addChoice
    split
    · simp only [beq_iff_eq, same, ↓reduceIte]
    · cases pick : f n with
      | none => simp only [beq_iff_eq, same, ↓reduceIte]
      | some d =>
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        simp only [beq_iff_eq, same, ↓reduceIte]
        exact (Std.HashMap.get?_eq_getElem?).symm

private theorem Choices.add {f pre m} (held : Choices f pre m) (n : ExactName) :
    Choices f (pre ++ [n]) (addChoice f m n) := by
  constructor
  · intro q d hit
    rw [choice_get held] at hit
    split at hit
    · exact hit
    · exact held.correct q d hit
  · intro q member
    rw [choice_get held]
    split
    · rfl
    · rename_i distinct
      rcases List.mem_append.mp member with old | added
      · exact held.present q old
      · have same : q = n := List.mem_singleton.mp added
        subst q
        simp at distinct

private theorem choices_fold (f : Name → Option Name) (xs : Array ExactName) :
    Choices f xs.toList (xs.foldl (addChoice f) {}) := by
  have walk (rest pre : List ExactName) (m : Std.HashMap ExactName Name) (held : Choices f pre m) :
      Choices f (pre ++ rest) (rest.foldl (addChoice f) m) := by
    induction rest generalizing pre m with
    | nil => simpa only [List.append_nil, List.foldl_nil] using held
    | cons n rest ih =>
      simpa only [List.append_assoc, List.singleton_append, List.foldl_cons] using ih (pre ++ [n]) _ (held.add n)
  rw [← Array.foldl_toList]
  exact walk xs.toList [] {} ⟨(by intro q d hit; simp [Std.HashMap.get?_eq_getElem?] at hit),
    (by intro q absent; cases absent)⟩

private theorem names_keep_addresses (table : Std.HashMap ExactName Name) :
    Preserves BlockState.auxNameToAddr
      (forIn (m := CompileM) table () (fun p _ => do compileName p.2; pure (.yield ()))) := by
  rw [Std.HashMap.forIn_eq_forIn_toList]
  apply Preserves.forIn_list
  intro p _
  apply Preserves.bind ?_ (fun _ => Preserves.pure _ _)
  intro context before
  have frame := congrArg BlockState.auxNameToAddr (BlobWrites.compileName_preserves p.2 context before).1
  simpa only [BlobWrites.withoutNamesBlobs] using frame

/-- The real successful move, at every nonreserved key: precisely the
computed selection/naming branch erases it; every skipped key retains its
local lookup. This neither erases nor frames an older GLOBAL entry. -/
theorem moveToDisplay_original_keys {cenv : CompileEnv} {benv : BlockEnv} {before after : BlockState}
    {all : Array Name} {rep0 : Name} {perm : Array (Option Nat)} {sel : Name → Bool}
    (run : CompileM.run cenv benv before (moveToDisplay all rep0 perm sel) = .ok ((), after)) :
    ∀ (q : ExactName), hasReserved q = false → after.auxNameToAddr.get? q =
      if sel q && (ixAuxName all rep0 perm q).isSome then none else before.auxNameToAddr.get? q := by
  let pick (n : Name) := if hasReserved n || !sel n then none else ixAuxName all rep0 perm n
  let registered : Array Name := before.auxNameToAddr.fold
    (fun acc n _ => acc.push n) (before.auxNamed.map (·.1))
  let table := registered.foldl (addChoice pick) {}
  have chosen := choices_fold pick registered
  have reserved : ReservedRange ⟨table⟩ := by
    intro q d hit
    have choice := chosen.correct q d hit
    dsimp only [pick] at choice
    split at choice
    · cases choice
    · exact ixAuxName_reserved choice
  have body (n : Name) (m : Std.HashMap ExactName Name) :
      (if m.contains n || hasReserved n || !sel n then pure (ForInStep.yield m)
       else (ixAuxName all rep0 perm n).elim (pure (ForInStep.yield m))
         (fun d => pure (ForInStep.yield (m.insert n d))) :
        CompileM (ForInStep (Std.HashMap ExactName Name))) =
      pure (ForInStep.yield (addChoice pick m n)) := by
    cases a : m.contains n <;> cases b : hasReserved n <;> cases c : sel n <;>
      cases d : ixAuxName all rep0 perm n <;> simp [addChoice, pick, a, b, c, d]
  have actual := run_success run
  rw [moveToDisplay_eq] at actual
  have loop :
      (forIn (m := CompileM) (α := Name) registered ({} : Std.HashMap ExactName Name) fun (n : Name) m =>
        if m.contains n || hasReserved n || !sel n then pure (ForInStep.yield m)
        else (ixAuxName all rep0 perm n).elim (pure (ForInStep.yield m))
          (fun d => pure (ForInStep.yield (m.insert n d)))) = pure table := by
    calc
      _ = forIn (m := CompileM) (α := Name) registered ({} : Std.HashMap ExactName Name)
          (fun (n : Name) m => pure (ForInStep.yield (addChoice pick m n))) := by
        apply congrArg (fun f => forIn (m := CompileM) (α := Name) registered ({} : Std.HashMap ExactName Name) f)
        funext n m
        exact body n m
      _ = pure table := Array.forIn_pure_yield_eq_foldl _ _
  simp only [rawRun_bind, rawRun_get] at actual
  dsimp only [registered, ExactName] at loop
  rw (transparency := .default) [loop, rawRun_pure] at actual
  dsimp only at actual
  intro q plain
  have framed : after.auxNameToAddr.get? q = if table.contains q then none else before.auxNameToAddr.get? q := by
    split at actual
    · rename_i empty
      rw [rawRun_pure] at actual
      cases actual
      have absent : table.contains q = false := by
        exact Std.HashMap.contains_of_isEmpty empty
      simp only [absent, Bool.false_eq_true, ↓reduceIte]
    · rw [rawRun_bind, rawRun_modify] at actual
      dsimp only at actual
      have frame := Preserves.of_ok ((names_keep_addresses table).bind (fun _ => Preserves.pure _ ())) actual
      rw [frame]
      exact sideCar_original_keys ⟨table⟩ before.auxNamed before.auxNameToAddr before.auxGenExtraNames reserved q plain
  rw [framed]
  cases old : before.auxNameToAddr.get? q with
  | none => simp only [ite_self]
  | some value =>
    have inMap : (q, value) ∈ before.auxNameToAddr.toList :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr old
    have member : q ∈ registered.toList := by
      dsimp only [registered]
      rw (transparency := .default) [Std.HashMap.fold_eq_foldl_toList, Array.foldl_toList_eq_map]
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨(q, value), inMap, rfl⟩)
    have lookup := chosen.present q member
    have contains : table.contains q = (pick q).isSome := by
      rw [Std.HashMap.contains_eq_isSome_getElem?]
      change (table.get? q).isSome = (pick q).isSome
      rw [lookup]
    rw [contains]
    cases selected : sel q <;> simp [pick, plain, selected]

end Ix.CompileCert.DisplayAddressFrame
