module

public import IxC.Kernel.Model.Rules.Inputs
import IxC.Kernel.Model.Rules.Reads
import IxC.Kernel.Model.CtxOkKit

public section

/-!
# Equality reflection is sound (S2's N13, lane l5)

`Red.eqProof` rewrites a constant application `a` to `b` given a proof of
`@Eq.{u} T a b`. In the model `Eq` denotes equality (`eq_law`): the proof's
reading is a member of `eqv ⟦a⟧ ⟦b⟧`, so `⟦a⟧ = ⟦b⟧`. The typings of `a` and `b`
at `T` and of `T` at `u` supply the law's three domain memberships; the proof's
inferred type supplies `b`'s frame and reading. No new model input: `eq_law` is
an `EnvModelM` field.
-/

namespace Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key ConstantInfo)
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {m : EnvModel V env}
  {φ : LevelParam → Nat}

/-- An application's reading is the application of its parts' readings. -/
theorem denoteMeta_app_inv {acval : Key md → (LevelParam → Nat) → AnnotTerm} {d : Nat}
    {f x : Expr md} {r : AnnotTerm} (h : denoteMeta acval env φ d (.app f x) = some r) :
    ∃ fr xr, denoteMeta acval env φ d f = some fr ∧ denoteMeta acval env φ d x = some xr ∧
      r = .app fr xr := by
  rw [denoteMeta_app] at h
  cases hf : denoteMeta acval env φ d f with
  | none => simp [hf] at h
  | some fr =>
    cases hx : denoteMeta acval env φ d x with
    | none => simp [hf, hx] at h
    | some xr =>
      simp [hf, hx] at h
      exact ⟨fr, xr, rfl, rfl, h.symm⟩

/-- An application's frame gives its parts'. -/
theorem frame_app_split {d : Nat} {f x : Expr md} (h : Frame d (.app f x)) :
    Frame d f ∧ Frame d x := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩,
    ⟨hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩⟩

/-- **`Red.eqProof` is sound.** -/
theorem Red.eqProof_sound (hin : RulesInputs V m φ) {d : Nat} {a b p T ta tb sT : Expr md}
    {u v : Level} {ci : ConstantInfo md}
    (hfE : env.find? eqName = some ci)
    (hp : Infer env .full d p (.app (.app (.app (.const eqName [u]) T) a) b))
    (hwp : p.wscopedB d = true) (hbp : p.looseBVarsBounded 0 = true)
    (hlp : ∀ l ∈ p.fvarLeaves, l ∈ a.fvarLeaves)
    (sp : InferSemFull m φ d p (.app (.app (.app (.const eqName [u]) T) a) b))
    (sa : InferSemFull m φ d a ta) (sda : DefEqSem m φ d ta T)
    (sb : InferSemFull m φ d b tb) (sdb : DefEqSem m φ d tb T)
    (sTT : InferSemFull m φ d T sT) (sred : RedSem m φ d sT (.sort v))
    (hv : ∀ φ : LevelParam → Nat, Level.eval φ v = Level.eval φ u) :
    RedSem m φ d a b := by
  intro hfa Δa aa hCa haa _
  -- the proof reads, with its type
  have hwp' : Expr.WScoped d p := Expr.WScoped.of_wscopedB hwp
  have hLp : Expr.LeavesBounded p := fun l hl => hfa.2.2 l (hlp l hl)
  have hCp : CtxOk m φ d Δa p := hCa.of_subset hlp
  obtain ⟨pa, hpa⟩ := Ix.Kernel.Model.infer_reads m φ hp rfl hwp' hbp hLp
  obtain ⟨hfS, hsubS, Sa, hSa, -, -, hmemP⟩ :=
    sp (⟨hwp', hbp, hLp⟩ : Expr.WScoped d p ∧ p.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded p) hCp hpa
  -- the type's pieces
  obtain ⟨hf3, hfb⟩ := frame_app_split hfS
  obtain ⟨hf2, -⟩ := frame_app_split hf3
  obtain ⟨-, hfT⟩ := frame_app_split hf2
  have hCT : CtxOk m φ d Δa T :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  have hCb : CtxOk m φ d Δa b :=
    hCp.of_subset (fun l hl => hsubS l (by simp [Expr.fvarLeaves, hl]))
  obtain ⟨r3, br, h3, hbr, rfl⟩ := denoteMeta_app_inv hSa
  obtain ⟨r2, ar, h2, har, rfl⟩ := denoteMeta_app_inv h3
  obtain ⟨Er, Tr, h1, hTr, rfl⟩ := denoteMeta_app_inv h2
  obtain rfl : ar = aa := Option.some.inj (har.symm.trans haa)
  -- the stored `Eq` is the pinned one, and its reading is the leaf
  have hci : ci = eqA := by
    rw [(m.basis_pinned eqName ci hfE (by (cases md <;> decide))).1]
    unfold pinnedInfo
    rw [if_pos rfl]
  subst hci
  rw [denoteMeta_const hfE (by rfl)] at h1
  obtain rfl := Option.some.inj h1
  -- the typings
  obtain ⟨hfta, hsubta, tar, htar, -, hgta, hmemA⟩ := sa hfa hCa haa
  obtain ⟨hfsT, hsubsT, sTr, hsTr, hgT, hgsT, hmemT⟩ := sTT hfT hCT hTr
  obtain ⟨hftb, hsubtb, tbr, htbr, hgB, hgtb, hmemB⟩ := sb hfb hCb hbr
  have heqA := sda hfta hfT (hCa.of_subset hsubta) hCT htar hTr hgta hgT
  have heqB := sdb hftb hfT (hCb.of_subset hsubtb) hCT htbr hTr hgtb hgT
  obtain ⟨-, -, sa', hsa', -, heqS⟩ := sred hfsT (hCT.of_subset hsubsT) hsTr hgsT
  rw [denoteMeta_sort] at hsa'
  obtain rfl : sa' = AnnotTerm.sort (v.eval φ) := (Option.some.inj hsa').symm
  have hlaw := (hin.eq_law hfE (Level.substFn φ (eqA (md := md)).toConstantVal.levelParams [u])).1
  refine ⟨hfb, fun l hl => hlp l (hsubS l (by simp [Expr.fvarLeaves, hl])), br, hbr, hgB,
    fun ρ hρ => ?_⟩
  have hTu : interp V ρ Tr ∈ˢ
      (univ (Level.substFn φ (eqA (md := md)).toConstantVal.levelParams [u] uN) : V) := by
    have h := hmemT ρ hρ
    rw [heqS ρ hρ, interp_sort, hv φ] at h
    exact h
  have ha' : interp V ρ aa ∈ˢ interp V ρ Tr := heqA ρ hρ ▸ hmemA ρ hρ
  have hb' : interp V ρ br ∈ˢ interp V ρ Tr := heqB ρ hρ ▸ hmemB ρ hρ
  have hP := hmemP ρ hρ
  simp only [interp_app] at hP
  rw [hlaw ρ _ _ _ hTu ha' hb'] at hP
  exact mem_eqv hP

end Ix.Kernel.Model.Rules
