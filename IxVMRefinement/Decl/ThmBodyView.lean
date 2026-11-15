import IxC.Kernel.Core
import IxC.Kernel.Verify.EnvWF

/-! # The checker view of hthm theorem bodies

The theorem's constant value and every non-theorem entry are exact. Only the hthm stored
body of a theorem can differ. This relation is internal to the role-checking fold.
-/

namespace IxVM.Refinement.Decl.ThmBodyView

open Ix.Kernel

inductive Entry {md : Mode} : Option (ConstantInfo md) → Option (ConstantInfo md) → Prop
  | same (value : Option (ConstantInfo md)) : Entry value value
  | thm (cv : ConstantVal md) (v w : Expr md) : Entry (some (.thmInfo cv v)) (some (.thmInfo cv w))

def Agrees {md : Mode} (source target : Env md) : Prop :=
  ∀ name, Entry (source.find? name) (target.find? name)

theorem Entry.observe {md : Mode} {a b : Option (ConstantInfo md)} (h : Entry a b)
    {α : Type u} (read : Option (ConstantInfo md) → α)
    (hthm : ∀ cv v w, read (some (.thmInfo cv v)) = read (some (.thmInfo cv w))) :
    read a = read b := by
  cases h with
  | same => rfl
  | thm cv v w => exact hthm cv v w

namespace Agrees

variable {md : Mode} {source target : Env md} (h : Agrees source target)

include h

theorem observe (name : Key md) {α : Type u} (read : Option (ConstantInfo md) → α)
    (hthm : ∀ cv v w, read (some (.thmInfo cv v)) = read (some (.thmInfo cv w))) :
    read (source.find? name) = read (target.find? name) :=
  (h name).observe read hthm

theorem cons (ci : ConstantInfo md) :
    Agrees ⟨ci :: source.consts⟩ ⟨ci :: target.consts⟩ := by
  intro name
  rw [Env.find?_cons, Env.find?_cons]
  split
  · exact .same _
  · exact h name

theorem consThm (cv : ConstantVal md) (v w : Expr md) :
    Agrees ⟨.thmInfo cv v :: source.consts⟩ ⟨.thmInfo cv w :: target.consts⟩ := by
  intro name
  rw [Env.find?_cons, Env.find?_cons]
  change Entry (if cv.name = name then some (.thmInfo cv v) else source.find? name)
    (if cv.name = name then some (.thmInfo cv w) else target.find? name)
  split
  · exact .thm cv v w
  · exact h name

theorem findCV (name : Key md) : source.findCV? name = target.findCV? name :=
  h.observe name (fun c => c.map ConstantInfo.toConstantVal) (by intros; rfl)

theorem isSome (name : Key md) : (source.find? name).isSome = (target.find? name).isSome :=
  h.observe name Option.isSome (by intros; rfl)

theorem findProj (T : Key md) (i : Nat) : source.findProj? T i = target.findProj? T i :=
  h.observe (projTableName T)
    (fun c => match c with
      | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
      | _ => none) (by intros; rfl)

theorem isCtorApp (e : Expr md) : Ix.Kernel.isCtorApp source e = Ix.Kernel.isCtorApp target e := by
  unfold Ix.Kernel.isCtorApp
  cases e.getAppFn with
  | const c us => exact h.observe c _ (by intros; rfl)
  | _ => rfl

theorem etaCtorShape (e : Expr md) : Ix.Kernel.etaCtorShape source e = Ix.Kernel.etaCtorShape target e := by
  unfold Ix.Kernel.etaCtorShape
  cases e.getAppFn with
  | const c us => exact h.observe c _ (by intros; rfl)
  | _ => rfl

theorem unfoldDefinition (e : Expr md) :
    Ix.Kernel.unfoldDefinition source e = Ix.Kernel.unfoldDefinition target e := by
  unfold Ix.Kernel.unfoldDefinition
  cases e.getAppFn with
  | const c us => exact h.observe c _ (by intros; rfl)
  | _ => rfl

theorem unfoldableHead (e : Expr md) :
    Ix.Kernel.unfoldableHead source e = Ix.Kernel.unfoldableHead target e := by
  unfold Ix.Kernel.unfoldableHead
  cases e.getAppFn with
  | const c us => exact h.observe c _ (by intros; rfl)
  | _ => rfl

theorem headHint (e : Expr md) : Ix.Kernel.headHint source e = Ix.Kernel.headHint target e := by
  unfold Ix.Kernel.headHint
  cases e.getAppFn with
  | const c us => exact h.observe c _ (by intros; rfl)
  | _ => rfl

theorem natLitSupported : Ix.Kernel.natLitSupported source = Ix.Kernel.natLitSupported target := by
  unfold Ix.Kernel.natLitSupported
  rw [h.observe natName natIndOk (by intros; rfl),
    h.observe natZeroName natZeroOk (by intros; rfl),
    h.observe natSuccName natSuccOk (by intros; rfl)]

theorem strLitSupported : Ix.Kernel.strLitSupported source = Ix.Kernel.strLitSupported target := by
  unfold Ix.Kernel.strLitSupported
  rw [h.natLitSupported,
    h.observe stringName stringTyOk (by intros; rfl),
    h.observe charName charTyOk (by intros; rfl),
    h.observe listName listTyOk (by intros; rfl),
    h.observe listNilName listNilTyOk (by intros; rfl),
    h.observe listConsName listConsTyOk (by intros; rfl),
    h.observe charOfNatName charOfNatTyOk (by intros; rfl),
    h.observe stringOfListName stringOfListTyOk (by intros; rfl)]

theorem natOpStored (name : Key md) :
    Ix.Kernel.natOpStored source name = Ix.Kernel.natOpStored target name :=
  h.observe name (fun c => match c with | some (.defnInfo _ _ _) => true | _ => false)
    (by intros; rfl)

theorem isUnitLikeTy (e : Expr md) :
    Ix.Kernel.isUnitLikeTy source e = Ix.Kernel.isUnitLikeTy target e := by
  cases e with
  | const name levels =>
    unfold Ix.Kernel.isUnitLikeTy
    have hi := h.observe punitName
      (fun c => match c with | some (.indInfo _ _) => true | _ => false) (by intros; rfl)
    have hr := h.observe punitRecName
      (fun c => match c with | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
        | _ => false) (by intros; rfl)
    rw [hi, hr]
  | _ => rfl

theorem towerSlotsAll (T : Key md) (n : Nat) :
    Ix.Kernel.towerSlotsAll source T n = Ix.Kernel.towerSlotsAll target T n := by
  unfold Ix.Kernel.towerSlotsAll
  congr 1
  funext i
  rw [h.findProj]

theorem recSlotsAll (T : Key md) (n : Nat) :
    Ix.Kernel.recSlotsAll source T n = Ix.Kernel.recSlotsAll target T n := by
  unfold Ix.Kernel.recSlotsAll
  congr 1
  funext i
  exact h.observe (projFnName T i) _ (by intros; rfl)

theorem etaProjs (T : Key md) (us : List Level) (args : List (Expr md)) (b : Expr md) (n : Nat) :
    Ix.Kernel.etaProjs source T us args b n = Ix.Kernel.etaProjs target T us args b n := by
  unfold Ix.Kernel.etaProjs
  rw [h.towerSlotsAll]

theorem etaFabArgsE (T : Key md) (us : List Level) (args : List (Expr md)) (b : Expr md) (n : Nat) :
    Ix.Kernel.etaFabArgsE source T us args b n = Ix.Kernel.etaFabArgsE target T us args b n := by
  unfold Ix.Kernel.etaFabArgsE
  rw [h.etaProjs]

theorem andRescueSlots (ctor : Key md) (nP : Nat) (us : List Level) :
    Ix.Kernel.andRescueSlots source ctor nP us = Ix.Kernel.andRescueSlots target ctor nP us := by
  have hp : source.findProj? = target.findProj? := funext fun T => funext fun i => h.findProj T i
  unfold Ix.Kernel.andRescueSlots
  rw [hp]

theorem headTypePW (e : Expr md) (n : Nat) :
    Ix.Kernel.headTypePW source.find? e n = Ix.Kernel.headTypePW target.find? e n := by
  cases e with
  | const name levels => exact h.observe name _ (by intros; rfl)
  | _ => rfl

theorem typeSortPW (e : Expr md) :
    Ix.Kernel.typeSortPW source.find? e = Ix.Kernel.typeSortPW target.find? e := by
  unfold Ix.Kernel.typeSortPW
  cases e with
  | forallE _ _ _ | sort _ => rfl
  | _ => exact h.headTypePW _ _

theorem headProofPW (e : Expr md) :
    Ix.Kernel.headProofPW source.find? e = Ix.Kernel.headProofPW target.find? e := by
  have ht : Ix.Kernel.typeSortPW source.find? = Ix.Kernel.typeSortPW target.find? :=
    funext fun e => h.typeSortPW e
  cases e with
  | const name levels =>
    unfold Ix.Kernel.headProofPW
    rw [← ht]
    exact h.observe name _ (by intros; rfl)
  | fvar _ _ => exact h.typeSortPW _
  | _ => rfl

theorem proofPW (e : Expr md) :
    Ix.Kernel.proofPW source.find? e = Ix.Kernel.proofPW target.find? e := by
  unfold Ix.Kernel.proofPW
  cases e with
  | lam _ _ _ => rfl
  | _ => exact h.headProofPW _

theorem notProofFast (e : Expr md) :
    Ix.Kernel.notProofFast source.find? e = Ix.Kernel.notProofFast target.find? e := by
  unfold Ix.Kernel.notProofFast
  rw [h.proofPW]

theorem isProofFast (e : Expr md) :
    Ix.Kernel.isProofFast source.find? e = Ix.Kernel.isProofFast target.find? e := by
  unfold Ix.Kernel.isProofFast
  rw [h.proofPW]

end Agrees
end IxVM.Refinement.Decl.ThmBodyView
