module

public import IxC.Kernel.Model.LevelRenKit
public import IxC.Kernel.Model.StoreCompanions
public import IxC.Kernel.Model.StoreLate

@[expose] public section

/-!
# A stored theorem's value mentions only the theorem's level parameters

`ThmLevels` (`Model/LevelRenKit.lean`) holds of the empty environment and every step over
derivations keeps it: the theorem step checks the stored value's level parameters
(`ValueFrontRunJ`) and stores that value (`rulesJ.thmValue`); no other step stores a theorem.
`StoreAr` holds of the empty environment (the witness that the bundle is inhabited).
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel (Env Key Expr ConstantInfo ConstantVal RecRule Declaration ThmLevels StoreAr)

theorem ThmLevels.empty : ThmLevels (md := md) Env.empty := by
  intro n cv v h
  simp [Env.find?, Env.empty] at h

theorem StoreAr.empty : StoreAr (md := md) Env.empty where
  type := fun h => by simp [Env.find?, Env.empty] at h
  defn := fun h => by simp [Env.find?, Env.empty] at h
  thm := fun h => by simp [Env.find?, Env.empty] at h
  rhs := fun h => by simp [Env.find?, Env.empty] at h
  proj := fun h => by simp [Env.findProj?, Env.find?, Env.empty] at h
  bool := by
    intro c hst hcb n ci hn hf
    simp [Env.find?, Env.empty] at hf

/-- **A step that stores no theorem keeps `ThmLevels`.** -/
theorem ThmLevels.step_noThm {env env₂ : Env md} (h : ThmLevels env)
    (hno : NewSat env env₂ NotThm) : ThmLevels env₂ := by
  intro n cv v hf
  rcases hno _ _ hf with h' | h'
  · exact h n cv v h'
  · exact absurd rfl (h' cv v)

/-- **Every declaration step over derivations keeps `ThmLevels`.** -/
theorem thmLevels_declRunJ {env env₂ : Env md} {d : Declaration md} (h : ThmLevels env)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) : ThmLevels env₂ := by
  cases d with
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, hvf, rfl⟩ := hrun
    intro n cv' v hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · obtain ⟨rfl, rfl⟩ := ConstantInfo.thmInfo.inj (Option.some.inj hf)
      exact hvf.2.2.2.1
    · exact h n cv' v hf
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hrun
    exact ThmLevels.step_noThm h (NewSat.cons (fun _ _ heq => nomatch heq))
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := hrun
    exact ThmLevels.step_noThm h (NewSat.cons (fun _ _ heq => nomatch heq))
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact h
    · exact ThmLevels.step_noThm h (NewSat.cons (fun _ _ heq => nomatch heq))
    · exact h
  | basisDecl kind => exact ThmLevels.step_noThm h (basis_newSat_noThm hrun)
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact ThmLevels.step_noThm h (basis_newSat_noThm hrun)
    · exact ThmLevels.step_noThm h (indRoutes_newSat_noThm hrun)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact ThmLevels.step_noThm h (basis_newSat_noThm hrun)
    · subst hrun
      exact h

/-- **The late recursor's step keeps `ThmLevels`.** -/
theorem thmLevels_late {J : Judgements md} {env env₂ : Env md} {fam : NativeFam md}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)} (h : ThmLevels env)
    (hrun : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) : ThmLevels env₂ :=
  ThmLevels.step_noThm h (nativeRecLate_newSat (fun _ _ _ _ _ _ heq => nomatch heq) hrun)

end Ix.Kernel.Model
