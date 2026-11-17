import IxVMRefinement.RoleOps.Interface
import IxVMRefinement.Decl.VerifiedRunMap
import IxC.Kernel.Model.NatEqs

/-! # The interface holds of every operation the kernel installs

The converse of `structOp_run` and `wfOp_run`: the kernel's judgement-level record of a
definition at an operation's key, over derivations, gives the check facts (`StructOpCheck`,
`WfOpCheck`) and the prefix facts (`OpPrefix`, `WfPrefix`) the two theorems ask for
(`structOp_of_run`, `wfOp_of_run`). The interface is therefore exactly as strong as the record,
and it holds of every operation the kernel's verified checker installs
(`structOp_of_verifiedRun`, `wfOp_of_verifiedRun`): a run of the checker gives the record over
runs, and each of its judgements has a derivation (`verifiedRunMap`).

In the converse the declared terms `ty₀`, `val₀` are the declaration's own and `ty`, `val` their
annotations; a well-founded operation's proof terms are the evidence's, the operation replaced
by its value.
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey)
open IxVM.Refinement.Decl (JudgementsMap verifiedRunMap)
open Ix.Kernel (Env Expr ConstantInfo ConstantVal ReducibilityHint LevelParam
  natOpNames natDivModNames natOpDeps natOpGuard natOpStoredOk natOpTyPinned natOpCod
  natLitSupported natName natZeroName natSuccName boolName boolTrueName boolFalseName eqName
  natPredName natBeqName natBleName natOpEquations divModCertStmts divModCertGuard)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements DeclDefnRunJ DeclDefnRun ConstantValRunJ ValueFrontRunJ
  NatEqsRunJ DivModCertRunJ DivModCertsJ)
open Ix.Kernel.Model (rulesJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## A map of judgement packages carries a definition's record -/

theorem divModCertsJ_map {J K : Judgements .anon} (M : JudgementsMap J K) {env : Env .anon}
    {c : KKey} {v : KExpr} :
    ∀ {stmts : List (List KExpr × KExpr)} {proofs : List KExpr},
      DivModCertsJ J env c v stmts proofs → DivModCertsJ K env c v stmts proofs := by
  intro stmts proofs h
  induction h with
  | nil => exact .nil
  | cons hg hann hinf hde _ ih =>
    exact .cons hg (M.annot hann) (M.infer hinf) (M.defeq hde) ih

theorem declDefnRunJ_map {J K : Judgements .anon} (M : JudgementsMap J K) {env env₂ : Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : ReducibilityHint}
    (h : DeclDefnRunJ J env cv value hint env₂) : DeclDefnRunJ K env cv value hint env₂ := by
  obtain ⟨type', value', hcv, hvf, henv, hnat, hdm⟩ := h
  refine ⟨type', value', M.constantValRun hcv, M.valueFrontRun hvf, henv, fun hc => ?_,
    fun hc => ?_⟩
  · obtain ⟨hg, hd, heqs⟩ := hnat hc
    exact ⟨hg, hd, fun eq heq => M.defeq (heqs eq heq)⟩
  · obtain ⟨hg, proofs, hpg, hcerts⟩ := hdm hc
    exact ⟨hg, proofs, hpg, divModCertsJ_map M hcerts⟩

/-- **A verified run of the kernel's definition check gives the record over derivations.** -/
theorem declDefnRunJ_of_verifiedRun {F : Nat} {env env₂ : Env .anon} {cv : ConstantVal .anon}
    {value : KExpr} {hint : ReducibilityHint}
    (h : DeclDefnRun .verified F env cv value hint env₂) :
    DeclDefnRunJ rulesJ env cv value hint env₂ :=
  declDefnRunJ_map (verifiedRunMap F) (Ix.Kernel.Semantics.declDefnRun_runJ h)

/-! ## Reading the guards back -/

private theorem opNames_all_notBasis :
    opNames.all (fun c => c != natName && c != natZeroName && c != natSuccName &&
      c != boolName && c != boolTrueName && c != boolFalseName && c != eqName) = true := by
  decide

/-- An operation key is none of the keys its guards look up beside the operations. -/
theorem opNames_ne_basis {c : KKey} (hc : c ∈ opNames) :
    c ≠ natName ∧ c ≠ natZeroName ∧ c ≠ natSuccName ∧ c ≠ boolName ∧ c ≠ boolTrueName ∧
      c ≠ boolFalseName ∧ c ≠ eqName := by
  have h : (c != natName && c != natZeroName && c != natSuccName &&
      c != boolName && c != boolTrueName && c != boolFalseName && c != eqName) = true :=
    List.all_eq_true.mp opNames_all_notBasis c hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem natOpCod_congr {env₁ env₂ : Env .anon}
    (h : env₁.find? boolName = env₂.find? boolName) (c : KKey) (e : KExpr) :
    natOpCod env₁ c e = natOpCod env₂ c e := by
  unfold Ix.Kernel.natOpCod
  rw [h]

theorem natOpTyPinned_congr {env₁ env₂ : Env .anon}
    (h : env₁.find? boolName = env₂.find? boolName) (c : KKey) (ty : KExpr) :
    natOpTyPinned env₁ c ty = natOpTyPinned env₂ c ty := by
  unfold Ix.Kernel.natOpTyPinned
  simp only [natOpCod_congr h]

theorem natOpStoredOk_congr {env₁ env₂ : Env .anon} {n : KKey}
    (hn : env₁.find? n = env₂.find? n) (hb : env₁.find? boolName = env₂.find? boolName) :
    natOpStoredOk env₁ n = natOpStoredOk env₂ n := by
  unfold Ix.Kernel.natOpStoredOk
  rw [hn]
  simp only [natOpTyPinned_congr hb]

/-- The pinned type has the pinned shape. -/
theorem opTyShape_of_pinned {env : Env .anon} {c : KKey} {ty : KExpr}
    (h : natOpTyPinned env c ty = true) : OpTyShape c ty := by
  unfold OpTyShape
  by_cases hp : c = natPredName
  · rw [ite_eq_left hp]
    exact Ix.Kernel.Model.natOpTyPinned_shape_un hp h
  · rw [ite_eq_right hp]
    obtain ⟨mb₁, mb₂, cod, hty, hcmp, hncmp⟩ := Ix.Kernel.Model.natOpTyPinned_shape_bin hp h
    refine ⟨mb₁, mb₂, ?_⟩
    by_cases hc : c = natBeqName ∨ c = natBleName
    · rw [hty, (hcmp hc).1, show opCod c = boolName from ite_eq_left hc]
    · rw [hty, hncmp hc, show opCod c = natName from ite_eq_right hc]

/-- A comparison's pinned type reads the stored shape of `Bool`. -/
theorem boolPinned_of_pinned {env : Env .anon} {c : KKey} {ty : KExpr}
    (hc : c = natBeqName ∨ c = natBleName) (h : natOpTyPinned env c ty = true) :
    BoolPinned env := by
  have hnp : ¬ c = natPredName := by
    rcases hc with hc | hc <;> (rw [hc]; decide)
  have hcb : (c = natBeqName || c = natBleName) = true := by
    rcases hc with hc | hc <;> simp [hc]
  unfold Ix.Kernel.natOpTyPinned at h
  rw [ite_eq_right hnp] at h
  cases ty with
  | forallE dom b mb =>
    cases b with
    | forallE dom2 body mb2 =>
      have h' : (dom == .const natName [] && dom2 == .const natName [] &&
          natOpCod env c body) = true := h
      simp only [Bool.and_eq_true] at h'
      have hcod := h'.2
      unfold Ix.Kernel.natOpCod at hcod
      rw [ite_eq_left hcb] at hcod
      simp only [Bool.and_eq_true] at hcod
      have h2 := hcod.2
      cases hf : env.find? boolName with
      | none => rw [hf] at h2; exact nomatch h2
      | some ci =>
        rw [hf] at h2
        have h3 : (ci.toConstantVal.levelParams.isEmpty &&
            ci.toConstantVal.type == .sort (.succ .zero)) = true := h2
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h3
        exact ⟨ci, hf, h3.1, h3.2⟩
    | _ => exact nomatch h
  | _ => exact nomatch h

/-- The level parameters of a definition stored at the key of an operation its guard
accepts. -/
theorem head_levelParams_of_guard {env : Env .anon} {c : KKey} {lps : List LevelParam}
    {ty val : KExpr} {hint : ReducibilityHint} (hself : c ∈ natOpDeps c)
    (hg : natOpGuard (⟨.defnInfo ⟨c, lps, ty⟩ val hint :: env.consts⟩ : Env .anon) c = true) :
    lps = [] := by
  obtain ⟨-, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvn, vn, hn, hfn, hlpn⟩ := hdeps c hself
  have hhead : (⟨.defnInfo ⟨c, lps, ty⟩ val hint :: env.consts⟩ : Env .anon).find? c =
      some (.defnInfo ⟨c, lps, ty⟩ val hint) :=
    Ix.Kernel.Env.find?_cons_self (.defnInfo ⟨c, lps, ty⟩ val hint) env
  rw [hhead] at hfn
  injection hfn with hfn
  injection hfn with hcvn
  subst hcvn
  exact hlpn

/-- The stored operation's own type is pinned, off the dependency guard. -/
theorem head_pinned_of_deps {env : Env .anon} {c : KKey} {ty val : KExpr}
    {hint : ReducibilityHint} (hself : c ∈ natOpDeps c)
    (hd : (natOpDeps c).all (natOpStoredOk (installed env c ty val hint)) = true) :
    natOpTyPinned (installed env c ty val hint) c ty = true := by
  have hs : natOpStoredOk (installed env c ty val hint) c = true :=
    List.all_eq_true.mp hd c hself
  obtain ⟨cv', v', hint', hf', -, hp'⟩ := natOpStoredOk_inv hs
  rw [installed_find_self] at hf'
  injection hf' with hf'
  injection hf' with hcv'
  subst hcv'
  exact hp'

/-- **The prefix facts, from the guards of the record**: what `natOpGuard` and the dependencies'
pinned types say of the environment after the install holds, off the operation's own key, of
the environment before it. -/
theorem opPrefix_of_guards {env : Env .anon} {c : KKey} {ty val : KExpr}
    {hint : ReducibilityHint} (hc : c ∈ opNames) (hfresh : env.find? c = none)
    (hg : natOpGuard (installed env c ty val hint) c = true)
    (hd : (natOpDeps c).all (natOpStoredOk (installed env c ty val hint)) = true) :
    OpPrefix env c := by
  obtain ⟨hnN, hnZ, hnS, hnB, hnT, hnF, hnE⟩ := opNames_ne_basis hc
  have hfind : ∀ k : KKey, c ≠ k → (installed env c ty val hint).find? k = env.find? k :=
    fun k h => Ix.Kernel.EnvExt.find?_cons_ne (c := .defnInfo ⟨c, [], ty⟩ val hint) h
  obtain ⟨hs, hdeps, hbool⟩ := Ix.Kernel.natOpGuard_inv hg
  refine { fresh := hfresh, natLit := ?_, deps := ?_, boolCtors := ?_, bool := ?_ }
  · rw [← Ix.Kernel.natLitSupported_congr (hfind _ hnN) (hfind _ hnZ) (hfind _ hnS)]
    exact hs
  · intro n hn hne
    have h2 : natOpStoredOk (installed env c ty val hint) n = true :=
      List.all_eq_true.mp hd n hn
    rw [natOpStoredOk_congr (hfind n (Ne.symm hne)) (hfind _ hnB)] at h2
    exact h2
  · intro hcc
    obtain ⟨⟨ciT, hT, hlT⟩, ⟨ciF, hF, hlF⟩⟩ := hbool hcc
    rw [hfind _ hnT] at hT
    rw [hfind _ hnF] at hF
    exact ⟨⟨ciT, hT, hlT⟩, ⟨ciF, hF, hlF⟩⟩
  · intro hcc
    obtain ⟨ci, hf, hl, ht⟩ :=
      boolPinned_of_pinned hcc (head_pinned_of_deps (self_mem_natOpDeps hc) hd)
    rw [hfind _ hnB] at hf
    exact ⟨ci, hf, hl, ht⟩

/-! ## A structural operation -/

/-- **The kernel's record of a structural operation gives the interface**: the level parameters
are none, the environment is the prefix with the operation stored, and the prefix facts and the
check facts hold. -/
theorem structOp_of_run {env env₂ : Env .anon} {cv : ConstantVal .anon} {value : KExpr}
    {hint : ReducibilityHint} (hc : cv.name ∈ natOpNames)
    (hrun : DeclDefnRunJ rulesJ env cv value hint env₂) :
    ∃ ty val, cv.levelParams = [] ∧ env₂ = installed env cv.name ty val hint ∧
      OpPrefix env cv.name ∧ StructOpCheck env cv.name cv.type value ty val := by
  obtain ⟨name, lps, cty⟩ := cv
  have hc' : name ∈ natOpNames := hc
  have hco : name ∈ opNames := mem_opNames.mpr (Or.inl hc')
  have hself := self_mem_natOpDeps hco
  obtain ⟨type', value', hcv, hvf, henv, hnat, -⟩ := hrun
  obtain ⟨hg, hd, heqs⟩ := hnat (List.contains_iff_mem.mpr hc')
  subst henv
  have hlp : lps = [] := head_levelParams_of_guard hself hg
  subst hlp
  obtain ⟨hfr, -, -, -, htc, htf, hta, htl, -, hts⟩ := hcv
  obtain ⟨hvc, hvfv, hva, hvl, -, hvt⟩ := hvf
  have hfresh : env.find? name = none := Option.isNone_iff_eq_none.mp hfr
  refine ⟨type', value', rfl, rfl, opPrefix_of_guards hco hfresh hg hd,
    ⟨htc, htf, hta, htl, hts, hvc, hvfv, hva, hvl, hvt⟩,
    opTyShape_of_pinned (head_pinned_of_deps hself hd), ?_⟩
  intro eq hmem
  exact heqs _ (List.mem_map.mpr ⟨eq, hmem, rfl⟩)

/-! ## A well-founded operation -/

/-- The kernel's certificate rows are checked certificates, at the proofs with the operation
replaced by its value. -/
theorem certFacts_of_certsJ {env : Env .anon} {c : KKey} {val : KExpr} :
    ∀ {stmts : List (List KExpr × KExpr)} {proofs : List KExpr},
      DivModCertsJ rulesJ env c val stmts proofs →
      List.Forall₂ (CertFacts env c val) stmts (proofs.map (Expr.substConstAll c val)) := by
  intro stmts proofs h
  induction h with
  | nil => exact .nil
  | cons hg hann hinf hde _ ih =>
    unfold Ix.Kernel.divModCertGuard at hg
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := hg
    rw [List.map_cons]
    exact .cons ⟨h1, h2, h3, h4, ⟨_, _, hann, hinf, hde⟩⟩ ih

/-- **The kernel's record of a well-founded operation gives the interface.** -/
theorem wfOp_of_run {env env₂ : Env .anon} {cv : ConstantVal .anon} {value : KExpr}
    {hint : ReducibilityHint} (hc : cv.name ∈ natDivModNames)
    (hrun : DeclDefnRunJ rulesJ env cv value hint env₂) :
    ∃ ty val, cv.levelParams = [] ∧ env₂ = installed env cv.name ty val hint ∧
      WfPrefix env cv.name ∧ WfOpCheck env cv.name cv.type value ty val := by
  obtain ⟨name, lps, cty⟩ := cv
  have hc' : name ∈ natDivModNames := hc
  have hco : name ∈ opNames := mem_opNames.mpr (Or.inr hc')
  have hself := self_mem_natOpDeps hco
  obtain ⟨type', value', hcv, hvf, henv, -, hdm⟩ := hrun
  obtain ⟨hgE, proofs, -, hcerts⟩ := hdm (List.contains_iff_mem.mpr hc')
  subst henv
  obtain ⟨hg, hd, heq, hbT, hbF⟩ := Ix.Kernel.divModEnvGuard_inv hgE
  have hlp : lps = [] := head_levelParams_of_guard hself hg
  subst hlp
  obtain ⟨hfr, -, -, -, htc, htf, hta, htl, -, hts⟩ := hcv
  obtain ⟨hvc, hvfv, hva, hvl, -, hvt⟩ := hvf
  have hfresh : env.find? name = none := Option.isNone_iff_eq_none.mp hfr
  obtain ⟨hnN, hnZ, hnS, hnB, hnT, hnF, hnE⟩ := opNames_ne_basis hco
  have hfind : ∀ k : KKey, name ≠ k →
      (installed env name type' value' hint).find? k = env.find? k :=
    fun k h => Ix.Kernel.EnvExt.find?_cons_ne (c := .defnInfo ⟨name, [], type'⟩ value' hint) h
  have hprefix : WfPrefix env name := by
    refine ⟨opPrefix_of_guards hco hfresh hg hd, ?_, ?_⟩
    · rw [← hfind _ hnE]
      exact heq
    · obtain ⟨ciT, hT, htT⟩ := hbT
      obtain ⟨ciF, hF, htF⟩ := hbF
      have hT' : (installed env name type' value' hint).find? boolTrueName = some ciT := hT
      have hF' : (installed env name type' value' hint).find? boolFalseName = some ciF := hF
      rw [hfind _ hnT] at hT'
      rw [hfind _ hnF] at hF'
      exact ⟨⟨ciT, hT', htT⟩, ⟨ciF, hF', htF⟩⟩
  exact ⟨type', value', rfl, rfl, hprefix,
    ⟨htc, htf, hta, htl, hts, hvc, hvfv, hva, hvl, hvt⟩,
    opTyShape_of_pinned (head_pinned_of_deps hself hd), _, certFacts_of_certsJ hcerts⟩

/-! ## The kernel's verified checker -/

/-- **Every structural operation the kernel's verified checker installs satisfies the
interface.** -/
theorem structOp_of_verifiedRun {F : Nat} {env env₂ : Env .anon} {cv : ConstantVal .anon}
    {value : KExpr} {hint : ReducibilityHint} (hc : cv.name ∈ natOpNames)
    (h : DeclDefnRun .verified F env cv value hint env₂) :
    ∃ ty val, cv.levelParams = [] ∧ env₂ = installed env cv.name ty val hint ∧
      OpPrefix env cv.name ∧ StructOpCheck env cv.name cv.type value ty val :=
  structOp_of_run hc (declDefnRunJ_of_verifiedRun h)

/-- **Every well-founded operation the kernel's verified checker installs satisfies the
interface.** -/
theorem wfOp_of_verifiedRun {F : Nat} {env env₂ : Env .anon} {cv : ConstantVal .anon}
    {value : KExpr} {hint : ReducibilityHint} (hc : cv.name ∈ natDivModNames)
    (h : DeclDefnRun .verified F env cv value hint env₂) :
    ∃ ty val, cv.levelParams = [] ∧ env₂ = installed env cv.name ty val hint ∧
      WfPrefix env cv.name ∧ WfOpCheck env cv.name cv.type value ty val :=
  wfOp_of_run hc (declDefnRunJ_of_verifiedRun h)

end IxVM.Refinement.RoleOps
