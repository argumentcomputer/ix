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
it when every inductive block takes the modeled route (`Model/DeclIndJ.lean`).
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

end Ix.Kernel.Model
