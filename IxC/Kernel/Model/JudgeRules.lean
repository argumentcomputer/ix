module

public import IxC.Kernel.Model.JudgeSound
public import IxC.Kernel.Model.FoldJ
public import IxC.Kernel.Rules.Annot
public import IxC.Kernel.Model.Rules.Sound
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Semantics.Frame
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Verify.Leaves

public section

/-!
# The derivation package (lane l5, obligation L5)

`rulesJ` is the judgement package of the rules tier: annotation is `Annot`
(`Rules/Annot.lean`), inference is `Infer` at the full grade, conversion is
`DefEq`, a sort check is a reduction to a sort, the proposition test is a level
that is zero under every assignment, and a theorem is stored with its annotated
value (decision D11). It is the package the records an IxVM refinement produces
are stated over.

`judgeSound_rulesJ` discharges `JudgeSound` at any model whose rules inputs hold,
from the derivations' soundness (`Rules.infer_sound`, `Rules.defeq_sound`) and
the readability of an accepted subject (`infer_reads`, by recursion on the
derivation). `foldRules` is `foldJ` at this package.
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

/-! ## An accepted subject reads

`acceptedReads_of`'s twin over derivations: what inference at the full grade
accepts, the reading reads. The recursion is on the derivation; the other five
relations of the mutual family need no statement and get a trivial one. -/

mutual

theorem infer_reads {env : Env md} (m : EnvModel V env) (φ : LevelParam → Nat) :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → g = .full →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      ∃ ea, denoteMeta m.acval env φ d e = some ea
  | _, _, _, _, .sort, _, _, _, _ => ⟨_, denoteMeta_sort _ _ _⟩
  | _, _, _, _, .fvar _, _, _, _, _ => ⟨_, denoteMeta_fvar _ _ _ _⟩
  | _, _, _, _, .const hf _ hus, _, _, _, _ => ⟨_, denoteMeta_const hf hus⟩
  | _, _, _, _, .natLit h, _, _, _, _ => ⟨_, denoteMeta_natLit h⟩
  | _, d, _, _, .strLit (s := s) h, _, _, _, _ => by
    rcases hd : denoteMeta m.acval env φ d (.lit (.strVal s)) with _ | ea
    · rw [denoteMeta, if_pos h] at hd
      exact nomatch hd
    · exact ⟨ea, rfl⟩
  | _, _, _, _, .forallE (ty := ty) (body := body) hs _ hbs _ _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded body := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwo, hbo, hLo⟩ := frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
    obtain ⟨ta, hta⟩ := infer_reads m φ hs hg hws.1 hb.1 hLty
    obtain ⟨ba, hba⟩ := infer_reads m φ hbs hg hwo hbo hLo
    exact ⟨_, by rw [denoteMeta_forallE, hta, hba]; rfl⟩
  | _, _, _, _, .lam (ty := ty) (body := body) hs _ hbt _ _ _ _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded body := fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwo, hbo, hLo⟩ := frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
    obtain ⟨ta, hta⟩ := infer_reads m φ (hs hg) rfl hws.1 hb.1 hLty
    obtain ⟨ba, hba⟩ := infer_reads m φ hbt hg hwo hbo hLo
    exact ⟨_, by rw [denoteMeta_lam, hta, hba]; rfl⟩
  | _, _, _, _, .app htf _ hta _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨fa, hfa⟩ := infer_reads m φ htf hg hws.1 hb.1 (fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl]))
    obtain ⟨aa, haa⟩ := infer_reads m φ hta hg hws.2 hb.2 (fun l hl =>
      hL l (by simp [Expr.fvarLeaves, hl]))
    exact ⟨_, by rw [denoteMeta_app, hfa, haa]; rfl⟩
  | _, _, _, _, .appSkip _ _ _, hg, _, _, _ => nomatch hg
  | _, _, _, _, .proj htpe _ _ hent _ _ _, hg, hws, hb, hL => by
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded] at hb
    obtain ⟨pa, hpa⟩ := infer_reads m φ htpe hg hws hb (fun l hl =>
      hL l (by simpa [Expr.fvarLeaves] using hl))
    exact ⟨_, denoteMeta_proj_tower hent hpa⟩

theorem infer_reads_red {env : Env md} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → True
  | _, _, _, _ => trivial

theorem infer_reads_defeq {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

theorem infer_reads_certs {env : Env md} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → True
  | _, _, _, _, _ => trivial

theorem infer_reads_defEqList {env : Env md} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem infer_reads_etaProjCerts {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → True
  | _, _, _, _, _, _, _, _ => trivial

end

/-! ## The package is sound at a model whose rules inputs hold -/

/-- **`JudgeSound` for derivations.** -/
theorem judgeSound_rulesJ {env : Env md} (m : EnvModel V env)
    (hin : ∀ φ, Rules.RulesInputs V m φ) : JudgeSound rulesJ m where
  toJudgeFrames := judgeFrames_rulesJ env
  accepted := fun φ _ _ _ h hws hb hL => infer_reads m φ h rfl hws hb hL
  infer := fun φ => by
    intro d e t Δa h hws hb hL ea ta hC hea hta
    have hs : Rules.InferSemFull m φ d e t := Rules.infer_sound (hin φ) h
    obtain ⟨-, -, ta', hta', hgE, hgT, hmem⟩ :=
      hs (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e) hC hea
    obtain rfl : ta' = ta := Option.some.inj (hta'.symm.trans hta)
    exact ⟨hgE, hgT, hmem⟩
  defeq := fun φ => by
    intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba' hCa hCb hra hrb hga hgb
    have hs : Rules.DefEqSem m φ d a b := Rules.defeq_sound (hin φ) h
    exact hs (⟨hwa, hba, hLa⟩ : Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a)
      (⟨hwb, hbb, hLb⟩ : Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded b) hCa hCb hra hrb hga hgb
  reads := fun φ => by
    intro d e t Δa ea h hws hb hL hC hea
    have hs : Rules.InferSemFull m φ d e t := Rules.infer_sound (hin φ) h
    obtain ⟨-, -, ta, hta, -⟩ :=
      hs (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e) hC hea
    exact ⟨ta, hta⟩
  frame := fun φ => by
    intro d e t Δa ea h hws hb hL hC hea
    have hs : Rules.InferSemFull m φ d e t := Rules.infer_sound (hin φ) h
    obtain ⟨⟨hwt, hbt, -⟩, hsub, -⟩ :=
      hs (⟨hws, hb, hL⟩ : Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e) hC hea
    exact ⟨hwt, hbt, hsub⟩

/-- At the fold's invariant the rules inputs hold (`RulesInputs.ofSem`). -/
theorem judgeSound_rulesJ_of {env : Env md} (mp : EnvModelM V μ env) :
    JudgeSound rulesJ mp.base2 :=
  judgeSound_rulesJ mp.base2 (fun φ => Rules.RulesInputs.ofSem mp φ)

/-- **The fold at the derivation package** (`foldJ` at `rulesJ`): what remains
is the pinned axioms' bits over derivations and the inductive kind's step. -/
theorem foldRules {Ind : Env md → List (ConstantInfo md) → Nat → Env md → Prop}
    (hbits : ∀ env : Env md, AxiomBitsJ rulesJ env)
    (hind : ∀ {env : Env md} (mp : EnvModelM V μ env), ThmValOk mp → EtaFamiliesClosed env →
      ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
        Ind env block nP envI →
          EtaFamiliesClosed envI ∧ ∃ mp₂ : EnvModelM V μ envI, ModelExt mp mp₂)
    {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ Ind env ds env' → EnvModelT V μ env → EnvModelT V μ env' :=
  foldJ rulesJ_thmValue (fun mp _ => judgeSound_rulesJ_of mp) hbits hind

end Ix.Kernel.Model
