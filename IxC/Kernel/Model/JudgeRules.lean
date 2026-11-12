module

public import IxC.Kernel.Model.JudgeSound
public import IxC.Kernel.Model.FoldJ
public import IxC.Kernel.Model.DeclIndJ
public import IxC.Kernel.Rules.Annot
public import IxC.Kernel.Model.Rules.Sound
public import IxC.Kernel.Model.Rules.Reads
import IxC.Kernel.Rules.Inversion
import IxC.Kernel.Model.Annot.Bit
import IxC.Kernel.SetModel.Ops
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Verify.Leaves
public import IxC.Kernel.Model.Inductives.NativeJudge
import IxC.Kernel.Verify.ProjSlots
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.Tiers
import IxC.Kernel.Model.Inductives.DeclNative
import IxC.Kernel.Semantics.Inductives.DeclNativeExtJ
/- `PropWhen` seals its representation; the bit lemmas below compute the pinned
`Eq`'s instantiated type by `rfl`, which needs the view (as `Model/AxiomBits.lean`). -/
import all IxC.Kernel.PropWhen

public section

/-!
# The derivation package

`rulesJ` is the judgement package of the rules tier: annotation is `Annot`
(`Rules/Annot.lean`), inference is `Infer` at the full grade, conversion is
`DefEq`, a sort check is a reduction to a sort, the proposition test is a level
that is zero under every assignment, and a theorem is stored with its annotated
value (so that the value can be read in the model). It is the package the records
an IxVM refinement produces are stated over.

`judgeSound_rulesJ` discharges `JudgeSound` at any model whose rules inputs hold,
from the derivations' soundness (`Rules.infer_sound`, `Rules.defeq_sound`) and
the readability of an accepted subject (`infer_reads`, by recursion on the
derivation). `axiomBits_rulesJ` gives the pinned axioms' bits over derivations
(by inversion, `Rules/Inversion.lean`), and `foldRules` is `foldJ` at this package,
which then asks only for the inductive kind's step; `foldRulesModeled` discharges
it when every inductive block takes the modeled route (`Model/DeclIndJ.lean`), and
`foldRulesRoutes` over every route of `IndRoutesJ`: the native one by
`nativeStep_rulesJ` (`declNativeJ`, `Model/Inductives/DeclNative.lean`) and the
native one without a recursor record by `nativeNoRecStep_rulesJ` (`declNativeNoRecJ`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo Declaration)
open Ix.Kernel.Rules (Annot Infer DefEq Red Certs DefEqList EtaProjCerts Grade)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **The derivation package.** -/
@[expose] def rulesJ : Judgements md where
  annot _ d e e' := Annot d e e'
  infer env d e t := Infer env .full d e t
  defeq env d a b := DefEq env d a b
  sort env d t u := Red env d t (.sort u)
  isZero u := ∀ φ : LevelParam → Nat, Level.eval φ u = 0
  thmValue _ v' := v'

/-- A theorem is stored with its annotated value. -/
theorem rulesJ_thmValue : ∀ v v' : Expr md, (rulesJ (md := md)).thmValue v v' = v' :=
  fun _ _ => rfl

/-! ## The scoping an annotation keeps -/

theorem annot_wscoped {d : Nat} {e e' : Expr md} (h : Annot d e e') :
    Expr.WScoped d e → Expr.WScoped d e' := by
  induction h with
  | bvar | fvar _ | sort | const | lit => exact id
  | app _ _ ihf iha =>
    intro hw
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨ihf hw.1, iha hw.2⟩
  | forallE _ _ ihty ihbody =>
    intro hw
    simp only [Expr.WScoped] at hw ⊢
    have hwty' := ihty hw.1
    exact ⟨hwty', Ix.Kernel.WScoped.abstract1 0 (ihbody (hwty'.instantiate1 0 hw.2))⟩
  | lam _ _ ihty ihbody =>
    intro hw
    simp only [Expr.WScoped] at hw ⊢
    have hwty' := ihty hw.1
    exact ⟨hwty', Ix.Kernel.WScoped.abstract1 0 (ihbody (hwty'.instantiate1 0 hw.2))⟩
  | proj _ ih =>
    intro hw
    simp only [Expr.WScoped] at hw ⊢
    exact ih hw
  | letE _ ih =>
    intro hw
    simp only [Expr.WScoped] at hw
    exact ih (Expr.WScoped.instantiate1_gen hw.2.1 0 hw.2.2)

theorem annot_bounded {d : Nat} {e e' : Expr md} (h : Annot d e e') :
    e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true := by
  induction h with
  | bvar | fvar _ | sort | const | lit => exact id
  | app _ _ ihf iha =>
    intro hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf hb.1, iha hb.2⟩
  | forallE _ _ ihty ihbody =>
    intro hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihty hb.1, Ix.Kernel.looseBVarsBounded_abstract1 _ 0
      (ihbody (Ix.Kernel.looseBVarsBounded_instantiate1 _ 0 hb.2))⟩
  | lam _ _ ihty ihbody =>
    intro hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihty hb.1, Ix.Kernel.looseBVarsBounded_abstract1 _ 0
      (ihbody (Ix.Kernel.looseBVarsBounded_instantiate1 _ 0 hb.2))⟩
  | proj _ ih =>
    intro hb
    simp only [Expr.looseBVarsBounded] at hb ⊢
    exact ih hb
  | letE _ ih =>
    intro hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ih (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)

theorem annot_leaves {d : Nat} {e e' : Expr md} (h : Annot d e e') :
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves := by
  induction h with
  | bvar | fvar _ | sort | const | lit => exact fun _ _ _ hl => hl
  | app _ _ ihf iha =>
    intro hw hb l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihf hw.1 hb.1 l hl)
    · exact Or.inr (iha hw.2 hb.2 l hl)
  | forallE hty hbody ihty ihbody =>
    intro hw hb l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hwty' := annot_wscoped hty hw.1
    have hwbody' := annot_wscoped hbody (hwty'.instantiate1 0 hw.2)
    have hsubbody := ihbody (hwty'.instantiate1 0 hw.2)
      (Ix.Kernel.looseBVarsBounded_instantiate1 _ 0 hb.2)
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty hw.1 hb.1 l hl)
    · obtain ⟨hl', hlt⟩ := Expr.fvarLeaves_abstract1_lt _ 0 hwbody' l hl
      rcases Expr.fvarLeaves_instantiate1 _ 0 (hsubbody l hl') with h2 | h2
      · exact Or.inr h2
      · simp only [Expr.fvarLeaves, List.mem_cons] at h2
        rcases h2 with rfl | h2
        · omega
        · exact Or.inl (ihty hw.1 hb.1 l h2)
  | lam hty hbody ihty ihbody =>
    intro hw hb l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hwty' := annot_wscoped hty hw.1
    have hwbody' := annot_wscoped hbody (hwty'.instantiate1 0 hw.2)
    have hsubbody := ihbody (hwty'.instantiate1 0 hw.2)
      (Ix.Kernel.looseBVarsBounded_instantiate1 _ 0 hb.2)
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty hw.1 hb.1 l hl)
    · obtain ⟨hl', hlt⟩ := Expr.fvarLeaves_abstract1_lt _ 0 hwbody' l hl
      rcases Expr.fvarLeaves_instantiate1 _ 0 (hsubbody l hl') with h2 | h2
      · exact Or.inr h2
      · simp only [Expr.fvarLeaves, List.mem_cons] at h2
        rcases h2 with rfl | h2
        · omega
        · exact Or.inl (ihty hw.1 hb.1 l h2)
  | proj _ ih =>
    intro hw hb l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.fvarLeaves] at hl ⊢
    exact ih hw hb l hl
  | letE _ ih =>
    intro hw hb l hl
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hsub := ih (Expr.WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
      (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
    simp only [Expr.fvarLeaves, List.mem_append]
    rcases Expr.fvarLeaves_instantiate1 _ 0 (hsub l hl) with h2 | h2
    · exact Or.inr h2
    · exact Or.inl (Or.inr h2)

/-- **The derivation package's annotations keep scoping.** -/
theorem judgeFrames_rulesJ (env : Env md) : JudgeFrames rulesJ env where
  annot_syntax := fun hann hf hb =>
    ⟨Expr.not_hasFvar_of_fvarsBelow_zero
        ((annot_wscoped hann (Expr.WScoped.of_not_hasFvar hf)).fvarsBelow),
      annot_bounded hann hb⟩
  annot_wscoped := fun hann hw => annot_wscoped hann hw
  annot_bounded := fun hann hb => annot_bounded hann hb
  annot_leaves := fun hann hw hb => annot_leaves hann hw hb

/-! ## The package is sound at a model whose rules inputs hold -/

/-- **`JudgeSound` for derivations.** -/
theorem judgeSound_rulesJ {env : Env md} (m : EnvModel V env)
    (hin : ∀ φ, Rules.RulesInputs V m φ) : JudgeSound rulesJ m where
  toJudgeFrames := judgeFrames_rulesJ env
  accepted := fun φ _ _ _ h hws hb hL => infer_reads m φ h rfl hws hb hL
  infer := fun φ => by
    intro d e t Δa h hws hb hL ea ta hC hea hta
    have hs : Rules.InferSemFull m φ d e t := Rules.infer_sound hin h
    obtain ⟨-, -, ta', hta', hgE, hgT, hmem⟩ :=
      hs (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e) hC hea
    obtain rfl : ta' = ta := Option.some.inj (hta'.symm.trans hta)
    exact ⟨hgE, hgT, hmem⟩
  defeq := fun φ => by
    intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba' hCa hCb hra hrb hga hgb
    have hs : Rules.DefEqSem m φ d a b := Rules.defeq_sound hin h
    exact hs (⟨hwa, hba, hLa⟩ : Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a)
      (⟨hwb, hbb, hLb⟩ : Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded b) hCa hCb hra hrb hga hgb
  reads := fun φ => by
    intro d e t Δa ea h hws hb hL hC hea
    have hs : Rules.InferSemFull m φ d e t := Rules.infer_sound hin h
    obtain ⟨-, -, ta, hta, -⟩ :=
      hs (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e) hC hea
    exact ⟨ta, hta⟩
  frame := fun φ => by
    intro d e t Δa ea h hws hb hL hC hea
    have hs : Rules.InferSemFull m φ d e t := Rules.infer_sound hin h
    obtain ⟨⟨hwt, hbt, -⟩, hsub, -⟩ :=
      hs (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e) hC hea
    exact ⟨hwt, hbt, hsub⟩

/-! ## The pinned axioms' bits over derivations

`propext_bits`/`choice_bits` (`Model/AxiomBits.lean`) read the kernel's recorded
run; here the same three moves read a derivation: the `∀` inversions give each
binder's validation `zeronessOf v = pw`, the innermost codomain's sort is computed
(the `Eq`-spine infers `Prop`; `choice`'s is the outer binder's variable), and a
sort reduces only to itself (`Rules.Red.rigid`), so each codomain sort is the
inferred one and the telescope collapse carries the bit outward. -/

/-- **The `Eq`-spine at the pinned `Eq` infers `Prop`**, over derivations. -/
theorem eqSpine_typeR {env : Env md} {d : Nat} {X Y Z bt : Expr md}
    (hEq : env.find? eqName = some eqA)
    (h : Infer env .full d (.app (.app (.app (.const eqName [.succ .zero]) X) Y) Z) bt) :
    bt = .sort .zero := by
  obtain ⟨tf1, ty1, b1, m1, ta1, h1, hw1, -, -, rfl⟩ := Rules.Infer.app_inv h
  obtain ⟨tf2, ty2, b2, m2, ta2, h2, hw2, -, -, rfl⟩ := Rules.Infer.app_inv h1
  obtain ⟨tf3, ty3, b3, m3, ta3, h3, hw3, -, -, rfl⟩ := Rules.Infer.app_inv h2
  obtain ⟨ci, hci, -, -, rfl⟩ := Rules.Infer.const_inv h3
  rw [hEq] at hci
  obtain rfl := Option.some.inj hci
  rw [show (Expr.instantiateLevelParams (eqA (md := md)).toConstantVal.levelParams
        [Level.zero.succ] (eqA (md := md)).toConstantVal.type)
      = .forallE (.sort (.succ .zero))
        (.forallE (.bvar 0)
          (.forallE (.bvar 1) (.sort .zero)
            { pw := .never }) { pw := .never })
        { pw := .never } from rfl] at hw3
  injection Rules.Red.rigid hw3 rfl with e1 e2 e3
  subst e2
  rw [show (Expr.forallE (.bvar 0)
        (.forallE (.bvar 1) (.sort .zero)
          { pw := .never }) { pw := .never }).instantiate1 X
      = .forallE X
        (.forallE X (.sort .zero)
          { pw := .never }) { pw := .never } from rfl] at hw2
  injection Rules.Red.rigid hw2 rfl with f1 f2 f3
  subst f2
  rw [show (Expr.forallE X
        (.sort .zero) { pw := .never }).instantiate1 Y
      = .forallE (X.instantiate1 Y 0)
        (.sort .zero) { pw := .never } from rfl] at hw1
  injection Rules.Red.rigid hw1 rfl with g1 g2 g3
  subst g2
  rfl

/-- **`propext`'s bits, over derivations.** -/
theorem propext_bitsR {env : Env md} (hEq : env.find? eqName = some eqA)
    {m₁ m₂ m₃ : BinderMeta} {d : Nat} {stype : Expr md}
    (h : Infer env .full d
      (.forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.sort .zero)) (.bvar 2)) (.bvar 1)) m₃) m₂) m₁) stype)
    (φ : LevelParam → Nat) :
    pwBit φ m₁.pw = 0 ∧ pwBit φ m₂.pw = 0 ∧ pwBit φ m₃.pw = 0 := by
  obtain ⟨-, u1, bs1, v1, -, -, hb1, hv1, hz1, -⟩ := Rules.Infer.forallE_inv h
  obtain ⟨-, u2, bs2, v2, -, -, hb2, hv2, hz2, rfl⟩ := Rules.Infer.forallE_inv hb1
  obtain ⟨-, u3, bs3, v3, -, -, hb3, hv3, hz3, rfl⟩ := Rules.Infer.forallE_inv hb2
  obtain rfl : bs3 = .sort .zero := eqSpine_typeR hEq hb3
  obtain rfl : v3 = .zero := Rules.Red.sort_eq hv3
  have hb3' : pwBit φ m₃.pw = 0 := by
    rw [← hz3]; exact (pwBit_zeronessOf φ _).mpr rfl
  obtain rfl : v2 = .imax u3 .zero := Rules.Red.sort_eq hv2
  have hb2' : pwBit φ m₂.pw = 0 := by
    rw [← hz2]; exact (pwBit_zeronessOf φ _).mpr (by simp [Level.eval])
  obtain rfl : v1 = .imax u2 (.imax u3 .zero) := Rules.Red.sort_eq hv1
  have hb1' : pwBit φ m₁.pw = 0 := by
    rw [← hz1]; exact (pwBit_zeronessOf φ _).mpr (by simp [Level.eval])
  exact ⟨hb1', hb2', hb3'⟩

/-- **`Classical.choice`'s bits, over derivations.** -/
theorem choice_bitsR {env : Env md} {m₁ m₂ : BinderMeta} {d : Nat} {stype : Expr md}
    (h : Infer env .full d
      (.forallE (.sort (.param uN))
        (.forallE
          (.app (.const nonemptyName [.param uN]) (.bvar 0))
          (.bvar 1) m₂) m₁) stype) (φ : LevelParam → Nat) :
    (pwBit φ m₁.pw = 0 ↔ φ uN = 0) ∧ (pwBit φ m₂.pw = 0 ↔ φ uN = 0) := by
  obtain ⟨-, u1, bs1, v1, -, -, hb1, hv1, hz1, -⟩ := Rules.Infer.forallE_inv h
  obtain ⟨-, u2, bs2, v2, -, -, hb2, hv2, hz2, rfl⟩ := Rules.Infer.forallE_inv hb1
  -- the innermost codomain is the outer binder's own variable
  obtain rfl : bs2 = .sort (.param uN) := Rules.Infer.fvar_inv hb2
  obtain rfl : v2 = .param uN := Rules.Red.sort_eq hv2
  have hb2' : pwBit φ m₂.pw = 0 ↔ φ uN = 0 := by
    rw [← hz2, pwBit_zeronessOf]; simp [Level.eval]
  obtain rfl : v1 = .imax u2 (.param uN) := Rules.Red.sort_eq hv1
  have hb1' : pwBit φ m₁.pw = 0 ↔ φ uN = 0 := by
    rw [← hz1, pwBit_zeronessOf]
    simp only [Level.eval]
    exact imax_eq_zero_iff _ _
  exact ⟨hb1', hb2'⟩

/-- **`AxiomBitsJ` for derivations**, at every environment. -/
theorem axiomBits_rulesJ (env : Env md) : AxiomBitsJ rulesJ env where
  propext_bits := fun hEq _ _ _ _ _ h φ => propext_bitsR hEq h φ
  choice_bits := fun h φ => choice_bitsR h φ

/-- At the fold's invariant the rules inputs hold (`RulesInputs.ofSem`). -/
theorem judgeSound_rulesJ_of {env : Env md} (mp : EnvModelM V μ env) :
    JudgeSound rulesJ mp.base2 :=
  judgeSound_rulesJ mp.base2 (fun φ => Rules.RulesInputs.ofSem mp φ)

/-- **The fold at the derivation package** (`foldJ` at `rulesJ`): what remains
is the inductive kind's step (the pinned axioms' bits are `axiomBits_rulesJ`). -/
theorem foldRules {Ind : Env md → List (ConstantInfo md) → Nat → Env md → Prop}
    (hind : ∀ {env : Env md} (mp : EnvModelM V μ env), ThmValOk mp → EtaFamiliesClosed env →
      ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
        Ind env block nP envI →
          EtaFamiliesClosed envI ∧ ∃ mp₂ : EnvModelM V μ envI, ModelExt mp mp₂)
    {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ Ind env ds env' → EnvModelT V μ env → EnvModelT V μ env' :=
  foldJ rulesJ_thmValue (fun mp _ => judgeSound_rulesJ_of mp) axiomBits_rulesJ hind

/-! ## The modeled inductive route over derivations -/

/-- **A modeled block, over derivations**: the restated record at `rulesJ` gives
the two facts `foldRules` asks of the inductive kind. -/
theorem modeledStep_rulesJ {env env₂ : Env md} {block : List (ConstantInfo md)}
    (mp : EnvModelM V μ env) (hE : EtaFamiliesClosed env)
    (h : DeclIndRunJ rulesJ env block env₂) :
    EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  declIndStepJ judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m) mp hE h

/-- **The fold at the derivation package, every inductive block modeled**:
`foldRules` with its inductive step discharged by `modeledStep_rulesJ`. -/
theorem foldRulesModeled {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ (fun e b _ e₂ => DeclIndRunJ rulesJ e b e₂)
      env ds env' →
    EnvModelT V μ env → EnvModelT V μ env' :=
  foldRules (fun {_} mp _ hE {_ _ _} h => modeledStep_rulesJ mp hE h)

/-! ## The native route's interface over derivations

The native install's model proofs read a package through `JudgeInv` and
`SortClaimJ` (`Model/Inductives/NativeJudge.lean`). Over derivations the
inversions are `Rules/Inversion.lean`'s (a sort or a `∀` reduces only to
itself, `Red.rigid`); the sort claim is the inference's and the reduction's
soundness; and an accepted annotation's projection slots are its inference's:
`Infer.proj` finds the slot's table. -/

/-- Instantiating a bound variable keeps the projection nodes. -/
theorem projSlotsOk_of_instantiate1 {env : Env md} {v : Expr md} :
    ∀ (e : Expr md) (k : Nat), Expr.ProjSlotsOk env (e.instantiate1 v k) →
      Expr.ProjSlotsOk env e := by
  intro e
  induction e with
  | bvar j => intro _ _; exact Expr.projSlotsOk_bvar
  | sort u => intro _ _; exact Expr.projSlotsOk_sort
  | const n us => intro _ _; exact Expr.projSlotsOk_const
  | lit l => intro _ _; exact Expr.projSlotsOk_lit
  | fvar idx ty _ => intro _ h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.projSlotsOk_app] at h
    exact Expr.projSlotsOk_app.mpr ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m ihty ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.projSlotsOk_lam] at h
    exact Expr.projSlotsOk_lam.mpr ⟨ihty k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.projSlotsOk_forallE] at h
    exact Expr.projSlotsOk_forallE.mpr ⟨ihty k h.1, ihb (k + 1) h.2⟩
  | letE t v' b _ iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.projSlotsOk_letE] at h
    exact Expr.projSlotsOk_letE.mpr ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s j e ihe =>
    intro k h
    simp only [Expr.instantiate1, Expr.projSlotsOk_proj] at h
    exact Expr.projSlotsOk_proj.mpr ⟨h.1, ihe k h.2⟩

mutual

/-- **An accepted subject's projection nodes name stored tables**, at the full
grade, given its free variables' annotations do. -/
theorem infer_projSlots {env : Env md} :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → g = .full →
      Expr.FvarTysOk env e → Expr.ProjSlotsOk env e
  | _, _, _, _, .sort, _, _ => Expr.projSlotsOk_sort
  | _, _, _, _, .fvar _, _, hf => Expr.projSlotsOk_fvar.mpr (Expr.fvarTysOk_fvar.mp hf)
  | _, _, _, _, .const _ _ _, _, _ => Expr.projSlotsOk_const
  | _, _, _, _, .natLit _, _, _ => Expr.projSlotsOk_lit
  | _, _, _, _, .strLit _, _, _ => Expr.projSlotsOk_lit
  | _, _, _, _, .forallE (ty := ty) (body := body) hs _ hbs _ _, hg, hf => by
    rw [Expr.fvarTysOk_forallE] at hf
    have hty := infer_projSlots hs hg hf.1
    have hb := infer_projSlots hbs hg
      (Expr.FvarTysOk.instantiate1 (Expr.fvarTysOk_fvar.mpr hty) body 0 hf.2)
    exact Expr.projSlotsOk_forallE.mpr ⟨hty, projSlotsOk_of_instantiate1 body 0 hb⟩
  | _, _, _, _, .lam (ty := ty) (body := body) hs _ hbt _ _ _ _, hg, hf => by
    rw [Expr.fvarTysOk_lam] at hf
    have hty := infer_projSlots (hs hg) rfl hf.1
    have hb := infer_projSlots hbt hg
      (Expr.FvarTysOk.instantiate1 (Expr.fvarTysOk_fvar.mpr hty) body 0 hf.2)
    exact Expr.projSlotsOk_lam.mpr ⟨hty, projSlotsOk_of_instantiate1 body 0 hb⟩
  | _, _, _, _, .app htf _ hta _, hg, hf => by
    rw [Expr.fvarTysOk_app] at hf
    exact Expr.projSlotsOk_app.mpr ⟨infer_projSlots htf hg hf.1, infer_projSlots hta hg hf.2⟩
  | _, _, _, _, .appSkip _ _ _, hg, _ => nomatch hg
  | _, _, _, _, .proj htpe _ _ hent _ _ _, hg, hf => by
    rw [Expr.fvarTysOk_proj] at hf
    exact Expr.projSlotsOk_proj.mpr ⟨⟨_, hent⟩, infer_projSlots htpe hg hf⟩

theorem infer_projSlots_red {env : Env md} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → True
  | _, _, _, _ => trivial

theorem infer_projSlots_defeq {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

theorem infer_projSlots_certs {env : Env md} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → True
  | _, _, _, _, _ => trivial

theorem infer_projSlots_defEqList {env : Env md} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem infer_projSlots_etaProjCerts {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-- **A constant-headed spine into a sort**, over derivations: every type the
head infers peels to a sort after the spine's length, so the spine infers that
sort (a `∀` reduces only to itself). -/
theorem infer_spine_sortR {env : Env md} {d : Nat} :
    ∀ (as : List (Expr md)) {f ty : Expr md} {bs : List (Expr md × Ix.Kernel.BinderMeta)}
      {s : Level} {t : Expr md},
      (∀ t', Infer env .full d f t' → t' = ty) →
      ty.stripPis as.length = some (bs, .sort s) →
      Infer env .full d (Expr.mkAppN f as) t → t = .sort s
  | [], f, ty, bs, s, t, huniq, hst, h => by
    obtain rfl := huniq t h
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    exact hst.2
  | a :: as, f, ty, bs, s, t, huniq, hst, h => by
    obtain ⟨dom, body, mb, rfl⟩ :
        ∃ dom body mb, ty = .forallE dom body mb := by
      cases ty <;> first
        | exact ⟨_, _, _, rfl⟩
        | simp [Expr.stripPis] at hst
    simp only [List.length_cons, Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    have hsome := Expr.stripPis_instantiate1_isSome (v := a) as.length
      (e := body) 0 (by rw [hst']; rfl)
    obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hb, -⟩ := Expr.stripPis_instantiate1_eq (v := a) as.length 0 hst' hst''
    rw [Expr.instantiate1_sort] at hb
    subst hb
    refine infer_spine_sortR as (f := .app f a) (ty := body.instantiate1 a) ?_ hst'' h
    intro t' h'
    obtain ⟨tf, ty', body', mt, ta, htf, hw, -, -, rfl⟩ := Rules.Infer.app_inv h'
    obtain rfl := huniq tf htf
    injection Rules.Red.rigid hw rfl with e1 e2 e3
    subst e2
    rfl

/-- **The derivation package has the shapes the native install reads.** -/
theorem judgeInv_rulesJ : JudgeInv (md := md) rulesJ where
  infer_sort := fun h => Rules.Infer.sort_inv h
  sort_sort := fun h => Rules.Red.sort_eq h
  infer_forallE := fun h => Rules.Infer.forallE_inv h
  infer_spine_sort := by
    intro env d n us as t ci bs s h hf hst
    refine infer_spine_sortR as (f := .const n us) ?_ hst h
    intro t' h'
    obtain ⟨ci', hf', -, -, rfl⟩ := Rules.Infer.const_inv h'
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    rfl
  annot_noProjAt := by
    intro env e e' T i hann hinf hnf hslot
    obtain ⟨t, ht⟩ := hinf
    have hnf' : e'.hasFvar = false :=
      Expr.not_hasFvar_of_fvarsBelow_zero
        ((annot_wscoped hann (Expr.WScoped.of_not_hasFvar hnf)).fvarsBelow)
    exact Expr.ProjSlotsOk.noProjAt hslot e'
      (infer_projSlots ht rfl (Expr.FvarTysOk.of_not_hasFvar e' hnf'))

/-- **The sort claim over derivations**, at a model whose rules inputs hold: the
inference's soundness puts the subject in its type's reading, and the
reduction's soundness reads that type as the universe. -/
theorem sortClaim_rulesJ {env : Env md} (m : EnvModel V env)
    (hin : ∀ φ, Rules.RulesInputs V m φ) (φ : LevelParam → Nat) :
    SortClaimJ rulesJ m φ := by
  intro d e t u Δa ea hi hs hws hb hL hC hea
  have hI : Rules.InferSemFull m φ d e t := Rules.infer_sound hin hi
  obtain ⟨hft, hsub, ta, hta, hgE, hgT, hmem⟩ :=
    hI (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e) hC hea
  have hR : Rules.RedSem m φ d t (.sort u) := Rules.red_sound hin hs
  obtain ⟨-, -, sa, hsa, -, heq⟩ := hR hft (hC.of_subset hsub) hta hgT
  rw [denoteMeta_sortQ] at hsa
  obtain rfl := Option.some.inj hsa
  intro ρ hρ
  refine ⟨hgE ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp_sort] at hm
  exact hm

/-- At the fold's invariant the sort claim holds (`RulesInputs.ofSem`). -/
theorem sortClaim_rulesJ_of {env : Env md} (mp : EnvModelM V μ env) (φ : LevelParam → Nat) :
    SortClaimJ rulesJ mp.base2 φ :=
  sortClaim_rulesJ mp.base2 (fun φ => Rules.RulesInputs.ofSem mp φ) φ

/-! ## The native route over derivations, and the fold over both routes -/

/-- **A native block, over derivations**: the restated native record at `rulesJ`
gives the two facts `foldRules` asks of the inductive kind, at a model whose stored
theorem values are read. -/
theorem nativeStep_rulesJ {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts md} (mp : EnvModelM V μ env) (hT : ThmValOk mp)
    (hE : EtaFamiliesClosed env) (hdp : Ix.Kernel.nativeParts? nP block = some p₀)
    (h : DeclNativeRunJ rulesJ env p₀ env₂) :
    EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  refine ⟨declNativeRunJ_etaClosed hE h, ?_⟩
  obtain ⟨mp₂, hext⟩ := declNativeJ judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m)
    judgeInv_rulesJ (fun m φ => sortClaim_rulesJ_of m φ) mp hE hdp h
  exact ⟨mp₂, hext hT⟩

/-- **A native block without its recursor record, over derivations**: the
recursor-less record at `rulesJ` gives the two facts `foldRules` asks of the
inductive kind, at a model whose stored theorem values are read. -/
theorem nativeNoRecStep_rulesJ {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts md} (mp : EnvModelM V μ env) (hT : ThmValOk mp)
    (hE : EtaFamiliesClosed env) (hdp : nativePartsNoRec? nP block = some p₀)
    (h : DeclNativeNoRecRunJ rulesJ env p₀ env₂) :
    EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  refine ⟨declNativeNoRecRunJ_etaClosed hE h, ?_⟩
  obtain ⟨mp₂, hext⟩ := declNativeNoRecJ judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m)
    judgeInv_rulesJ (fun m φ => sortClaim_rulesJ_of m φ) mp hE hdp h
  exact ⟨mp₂, hext hT⟩

/-- **The fold at the derivation package over the inductive routes** (`IndRoutesJ`):
every inductive block takes the native route at the parts the recogniser reads off
it (`nativeStep_rulesJ`), the modeled route (`modeledStep_rulesJ`), or the native
route without a recursor record (`nativeNoRecStep_rulesJ`). -/
theorem foldRulesRoutes {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env' →
    EnvModelT V μ env → EnvModelT V μ env' :=
  foldRules fun {_} mp hT hE {_ _ _} h => by
    rcases h with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
    · exact nativeStep_rulesJ mp hT hE hdp hN
    · exact modeledStep_rulesJ mp hE hM
    · exact nativeNoRecStep_rulesJ mp hT hE hdp hN

end Ix.Kernel.Model
