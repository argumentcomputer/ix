import IxVMRefinement.FamilyAlias.ProjFacts
import IxVMRefinement.Assembly.FoldClause
import IxVMRefinement.Assembly.NativeAliasOpenTrace
import IxC.Kernel.Model.DeclIndRen
import IxC.Kernel.Model.IndRenJudge
import IxC.Kernel.Model.IndMembers
import IxC.Kernel.Model.IndEtaLaw
import IxC.Kernel.Model.IndUnitLaw
import IxC.Kernel.Model.JudgeRules
import IxC.Kernel.Rules.Inversion
import IxC.Kernel.SetModel.TreeUnpack

/-! # Coherence of modeled structure projections

Proves the set-model coherence theorem linking a checked modeled structure projection's
advice definition (`proj_i`) to its level- and parameter-independent graph chain (`bgraph`
at `nP = 0 ∧ bnl = 0`, or `.unpackGraph spec [n, fidx + 1]` at `nP > 0 ∨ bnl > 0`):

* `declIndRenJ_acval`: exposes `BlockAcvalInstalled` from `DeclIndRenRunJ`;
* `stripPisZetaSort_eq_of_openSortTrace`: equates a `StripPisZetaSort` / `stripPis` result
  level with a registered native family's `resSort` via `FormerOpenTraceAt`;
* positional level-parameter transport (`origVal`, `ψ_rec`) and `Infer.lam_inv`;
* `eqRefl_interp_pt`, `aux_fibre_disjoint`, and `auxRec_not_reserved`. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (substLevel)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam BinderMeta Key Env SetTheory)
open Ix.Kernel.Semantics (AnnotTerm interp WellDenoted SpineFit cons consList shiftE
  NativeFam NativeFamStored
  fixFamI fixStepI fixStepI_elim fixFamI_app_eq fixFamI_app_eq_sum
  fitsXI_slot_mem spineFit_real_of_XI idxValsAt idxValsAt_of_eqsXI
  sumMkAV sumMkAV_fold sumMkAV_zero nativeTyAVI nativeTyAVI_fold
  DeclIndRenRunJ IndMembersRunJ tupW)
open Ix.Kernel.Verify (BlockInstalledTT)
open Ix.Kernel.SetTheory
open Ix.Kernel.SetTheory.Tower
open Ix.Kernel.SetModel
open Ix.Kernel.Model

/-! ## Section 1: `declIndRenJ_acval` -/

set_option maxHeartbeats 1600000 in
/-- Sibling of `Ix.Kernel.Model.declIndRenJ` exposing `BlockAcvalInstalled` on the resulting
model so modeled structure projection installation can equate `acval T` with `acval (auxKey T .model)`. -/
theorem declIndRenJ_acval {V : Type u} [SetTheory V] {md : Ix.Kernel.Mode}
    {μ : Ix.Kernel.CheckMode} {J : Ix.Kernel.Semantics.Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJ J env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂,
      BlockAcvalInstalled (block.map (·.name)) env₂ mp₂.base2.acval ∧
      ModelExt mp mp₂ := by
  have hns := declIndRenRunJ_noModel h
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hbnNon : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => false | _ => true),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hbnRec : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hEC0 : Ix.Kernel.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  have hnostore : ∀ n, (block.map (·.name)).contains n = true →
      ∀ ci : ConstantInfo md, env.find? n = some ci → False := by
    intro n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [Ix.Kernel.Semantics.indMembersRun_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := Ix.Kernel.Semantics.indMembersRun_mono _ hmem _ _ hf
      rw [Ix.Kernel.Semantics.indRecsRun_fresh (Ix.Kernel.Semantics.indRecsRenRunJ_shape hrecs) ci₀ hci₀] at hup
      exact nomatch hup
  have hI0 : BlockInstalledTT (block.map (·.name)) env mp.base2.cvalE :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hIA0 : BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hBP0 : Ix.Kernel.BlockEtaPinned μ (block.map (·.name)) env :=
    fun n cvS capsS hnb hf _ => absurd (hnostore n hnb _ hf) (fun h => h)
  have hall : ∀ n, (block.map (·.name)).contains n = true →
      (envM.find? n).isSome = true ∨
      ∃ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false), ci.name = n := by
    intro n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (Ix.Kernel.Semantics.indMembersRun_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁, hext₁⟩ :=
    indMembersPM memberEtaLaw memberUnitLaw (fun e => judgeFrames_renameJ (hfr e)) _ mp
      hbnNon
      (fun cv caps₂ _ => ⟨Ix.Kernel.Semantics.etaPins_empty,
        ⟨fun h => absurd h (by (cases md <;> decide)),
          fun h => absurd h (by (cases md <;> decide))⟩⟩)
      hmem hI0 hIA0 hEC0 hBP0
  obtain ⟨mp₂, -, hIA₂, hext₂⟩ :=
    indRecsRen memberEtaLaw memberUnitLaw hfr hJ mp₁ hI₁ hIA₁ hbnRec hall hns hEC₁ hBP₁
      hrecs
  exact ⟨mp₂, hIA₂, hext₁.trans hext₂⟩

/-! ## Section 2: `StripPisZetaSort` vs `FormerOpenTraceAt` -/

/-- Structural equality of expressions ignoring the type annotations carried by `.fvar` nodes. -/
inductive FvarTypeIrrel : KExpr → KExpr → Prop where
  | bvar (i : Nat) : FvarTypeIrrel (.bvar i) (.bvar i)
  | fvar (i : Nat) (t₁ t₂ : KExpr) : FvarTypeIrrel (.fvar i t₁) (.fvar i t₂)
  | sort (l : KLevel) : FvarTypeIrrel (.sort l) (.sort l)
  | const (n : KKey) (us : List KLevel) : FvarTypeIrrel (.const n us) (.const n us)
  | app {f₁ f₂ a₁ a₂ : KExpr} :
      FvarTypeIrrel f₁ f₂ → FvarTypeIrrel a₁ a₂ → FvarTypeIrrel (.app f₁ a₁) (.app f₂ a₂)
  | lam {t₁ t₂ b₁ b₂ : KExpr} {m : BinderMeta} :
      FvarTypeIrrel t₁ t₂ → FvarTypeIrrel b₁ b₂ → FvarTypeIrrel (.lam t₁ b₁ m) (.lam t₂ b₂ m)
  | forallE {t₁ t₂ b₁ b₂ : KExpr} {m : BinderMeta} :
      FvarTypeIrrel t₁ t₂ → FvarTypeIrrel b₁ b₂ →
      FvarTypeIrrel (.forallE t₁ b₁ m) (.forallE t₂ b₂ m)
  | letE {t₁ t₂ v₁ v₂ b₁ b₂ : KExpr} {l : Ix.Kernel.LetMeta} :
      FvarTypeIrrel t₁ t₂ → FvarTypeIrrel v₁ v₂ → FvarTypeIrrel b₁ b₂ →
      FvarTypeIrrel (.letE t₁ v₁ b₁ l) (.letE t₂ v₂ b₂ l)
  | lit (l : Ix.Kernel.Literal) : FvarTypeIrrel (.lit l) (.lit l)
  | proj (s : KKey) (i : Nat) {e₁ e₂ : KExpr} :
      FvarTypeIrrel e₁ e₂ → FvarTypeIrrel (.proj s i e₁) (.proj s i e₂)

theorem FvarTypeIrrel.refl : ∀ e : KExpr, FvarTypeIrrel e e
  | .bvar i => .bvar i
  | .fvar i t => .fvar i t t
  | .sort l => .sort l
  | .const n us => .const n us
  | .app f a => .app (refl f) (refl a)
  | .lam t b _ => .lam (refl t) (refl b)
  | .forallE t b _ => .forallE (refl t) (refl b)
  | .letE t v b _ => .letE (refl t) (refl v) (refl b)
  | .lit l => .lit l
  | .proj s i e => .proj s i (refl e)

theorem FvarTypeIrrel.instantiate1 {e₁ e₂ v₁ v₂ : KExpr}
    (he : FvarTypeIrrel e₁ e₂) (hv : FvarTypeIrrel v₁ v₂) :
    ∀ c : Nat, FvarTypeIrrel (e₁.instantiate1 v₁ c) (e₂.instantiate1 v₂ c) := by
  induction he with
  | bvar i =>
    intro c
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> exact .bvar _
  | fvar i t₁ t₂ => intro c; exact .fvar i t₁ t₂
  | sort l => intro c; exact .sort l
  | const n us => intro c; exact .const n us
  | app _ _ ihf iha => intro c; exact .app (ihf c) (iha c)
  | lam _ _ iht ihb => intro c; exact .lam (iht c) (ihb (c + 1))
  | forallE _ _ iht ihb => intro c; exact .forallE (iht c) (ihb (c + 1))
  | letE _ _ _ iht ihv ihb => intro c; exact .letE (iht c) (ihv c) (ihb (c + 1))
  | lit l => intro c; exact .lit l
  | proj s i _ ihe => intro c; exact .proj s i (ihe c)

private theorem headDeltaBeta_trace_sort_inv {env : Env .anon} {l : KLevel} {r : KExpr}
    (h : Ix.Kernel.HeadDeltaBeta.Trace env (.sort l) r) : r = .sort l := by
  cases h with
  | refl => rfl
  | cons hs _ => cases hs

private theorem headDeltaBeta_trace_forallE_inv {env : Env .anon} {t b : KExpr} {m : BinderMeta}
    {r : KExpr} (h : Ix.Kernel.HeadDeltaBeta.Trace env (.forallE t b m) r) :
    r = .forallE t b m := by
  cases h with
  | refl => rfl
  | cons hs _ => cases hs

private theorem headDeltaBeta_trace_letE_inv {env : Env .anon} {t v b : KExpr}
    {l : Ix.Kernel.LetMeta} {r : KExpr}
    (h : Ix.Kernel.HeadDeltaBeta.Trace env (.letE t v b l) r) : r = .letE t v b l := by
  cases h with
  | refl => rfl
  | cons hs _ => cases hs

/-- If `e₁` has an `OpenSortTrace` of length `m` ending at `s` and `e₂` (agreeing with `e₁` up to
`.fvar` type annotations) has a `StripPisZetaSort` of length `n` ending at `l`, then `n = m` and
`l = s`. -/
theorem stripPisZetaSort_eq_of_openSortTrace {env : Env .anon} :
    ∀ {n m d : Nat} {e₁ e₂ : KExpr} {l s : KLevel},
      FvarTypeIrrel e₁ e₂ →
      Decl.OpenSortTrace env d m e₁ s →
      StripPisZetaSort n d e₂ l →
      n = m ∧ l = s := by
  intro n m d e₁ e₂ l s hirr hot hsz
  induction hsz generalizing m e₁ with
  | srt d l =>
    cases hirr with
    | sort =>
      cases hot with
      | done ht =>
        have heq := headDeltaBeta_trace_sort_inv ht
        exact ⟨rfl, (Expr.sort.inj heq).symm⟩
      | step ht _ =>
        have heq := headDeltaBeta_trace_sort_inv ht
        exact nomatch heq
  | forallE n d ty₂ b₂ m₂ l hsz' ih =>
    match e₁, hirr with
    | .forallE t₁ b₁ _, .forallE hty hb =>
      cases hot with
      | done ht =>
        have heq := headDeltaBeta_trace_forallE_inv ht
        exact nomatch heq
      | step ht hot' =>
        have heq := headDeltaBeta_trace_forallE_inv ht
        injection heq with hT hB _
        rw [hT, hB] at hot'
        have hirr' : FvarTypeIrrel (b₁.instantiate1 (.fvar d t₁) 0)
            (b₂.instantiate1 (.fvar d (.sort .zero)) 0) :=
          hb.instantiate1 (.fvar d t₁ (.sort .zero)) 0
        obtain ⟨hnm, hls⟩ := ih hirr' hot'
        exact ⟨congrArg Nat.succ hnm, hls⟩
  | letE n d ty₂ v₂ b₂ lM l _ _ =>
    cases hirr with
    | letE _ _ _ =>
      cases hot with
      | done ht =>
        have heq := headDeltaBeta_trace_letE_inv ht
        exact nomatch heq
      | step ht _ =>
        have heq := headDeltaBeta_trace_letE_inv ht
        exact nomatch heq

theorem stripPis_to_stripPisZetaSort :
    ∀ {n d : Nat} {e : KExpr} {bs : List (KExpr × BinderMeta)} {l : KLevel},
      e.stripPis n = some (bs, .sort l) → StripPisZetaSort n d e l
  | 0, d, e, _, l, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    exact .srt d l
  | n + 1, d, .forallE ty b m, bs, l, h => by
    simp only [Expr.stripPis] at h
    cases hsb : b.stripPis n with
    | none => simp [hsb] at h
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.2] at hsb
      obtain ⟨bs', hbs'⟩ := stripPis_instantiate1 (.fvar d (.sort .zero)) n 0 hsb
      simp only [Expr.instantiate1] at hbs'
      exact .forallE n d ty b m l (stripPis_to_stripPisZetaSort hbs')
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _ _, _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const _ _, _, _, h | _ + 1, _, .app _ _, _, _, h | _ + 1, _, .lam _ _ _, _, _, h
  | _ + 1, _, .letE _ _ _ _, _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .proj _ _ _, _, _, h => nomatch h

private theorem level_subst_go_range_self (k : Nat) (p : LevelParam)
    (hp : p ∈ List.range k) :
    Level.subst.go (List.range k) ((List.range k).map Level.param) p = .param p := by
  have hgo : ∀ (xs : List Nat), p ∈ xs →
      Level.subst.go xs (xs.map Level.param) p = .param p := by
    intro xs hm
    induction xs with
    | nil => cases hm
    | cons x xs ih =>
      simp only [List.map_cons, Level.subst.go]
      by_cases hxp : x = p
      · simp [hxp]
      · simp only [hxp, ↓reduceIte]
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact absurd rfl hxp
        · exact ih hm'
  exact hgo (List.range k) hp

private theorem level_subst_range_self (k : Nat) :
    ∀ l : KLevel, l.allParamsDefined (List.range k) = true →
      Level.subst (List.range k) ((List.range k).map Level.param) l = l
  | .zero, _ => rfl
  | .succ l, h => congrArg Level.succ (level_subst_range_self k l h)
  | .max a b, h => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp [Level.subst, level_subst_range_self k a h.1, level_subst_range_self k b h.2]
  | .imax a b, h => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp [Level.subst, level_subst_range_self k a h.1, level_subst_range_self k b h.2]
  | .param p, h =>
    level_subst_go_range_self k p (by simpa [Level.allParamsDefined, List.contains_eq_mem] using h)

private theorem propWhen_inst_range_self (k : Nat) (pw : Ix.Kernel.PropWhen)
    (h : pw.paramsDefined (List.range k) = true) :
    Level.substPW (List.range k) ((List.range k).map Level.param) pw = pw := by
  refine Ix.Kernel.PropWhen.eq_of_holds fun φ => ?_
  cases pw with
  | never =>
    simp [Level.substPW]
  | ifAllZero ps =>
    rw [Ix.Kernel.PropWhen.paramsDefined_ifAllZero] at h
    simp only [Level.substPW, Ix.Kernel.PropWhen.bindZ_ifAllZero,
      Ix.Kernel.PropWhen.holds_bindZ_go, Ix.Kernel.PropWhen.holds_ifAllZero]
    have hps := List.all_eq_true.mp h
    induction ps with
    | nil => rfl
    | cons p qs ih =>
      have hp : p ∈ List.range k := by
        simpa [List.contains_eq_mem] using hps p List.mem_cons_self
      have hgo := level_subst_go_range_self k p hp
      simp only [List.all_cons, hgo, Ix.Kernel.Level.zeronessOf,
        Ix.Kernel.PropWhen.holds_ifAllZero, List.all_nil, Bool.and_true]
      congr 1
      exact ih (List.all_eq_true.mpr fun q hq => hps q (List.mem_cons_of_mem _ hq))
        (fun q hq => hps q (List.mem_cons_of_mem _ hq))

/-- `Core.posOf (List.range k) e = e` whenever `e.allLevelParamsDefined (List.range k) = true`. -/
theorem posOf_range_eq (k : Nat) :
    ∀ e : KExpr, e.allLevelParamsDefined (List.range k) = true →
      Core.posOf (List.range k) e = e
  | .bvar _, _ => rfl
  | .fvar i t, h => by
    simp only [Core.posOf, Expr.instantiateLevelParams]
    exact congrArg (Expr.fvar i) (posOf_range_eq k t h)
  | .sort l, h => by
    have hpos : Core.posLevels (List.range k) = (List.range k).map Level.param := by
      simp [Core.posLevels]
    simp only [Core.posOf, hpos, Expr.instantiateLevelParams]
    exact congrArg Expr.sort (level_subst_range_self k l h)
  | .const n us, h => by
    have hpos : Core.posLevels (List.range k) = (List.range k).map Level.param := by
      simp [Core.posLevels]
    simp only [Core.posOf, hpos, Expr.instantiateLevelParams]
    congr 1
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    rw [List.map_congr_left (fun l hl => level_subst_range_self k l (h l hl)), List.map_id']
  | .app f a, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Core.posOf, Expr.instantiateLevelParams]
    exact congrArg₂ Expr.app (posOf_range_eq k f h.1) (posOf_range_eq k a h.2)
  | .lam t b m, h => by
    have hpos : Core.posLevels (List.range k) = (List.range k).map Level.param := by
      simp [Core.posLevels]
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Core.posOf, Expr.instantiateLevelParams]
    have ht := posOf_range_eq k t h.1.1
    have hb := posOf_range_eq k b h.1.2
    have hm := propWhen_inst_range_self k m.pw h.2
    simp only [Core.posOf] at ht hb
    rw [ht, hb, hpos, hm]
  | .forallE t b m, h => by
    have hpos : Core.posLevels (List.range k) = (List.range k).map Level.param := by
      simp [Core.posLevels]
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Core.posOf, Expr.instantiateLevelParams]
    have ht := posOf_range_eq k t h.1.1
    have hb := posOf_range_eq k b h.1.2
    have hm := propWhen_inst_range_self k m.pw h.2
    simp only [Core.posOf] at ht hb
    rw [ht, hb, hpos, hm]
  | .letE t v b l, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Core.posOf, Expr.instantiateLevelParams]
    have ht := posOf_range_eq k t h.1.1
    have hv := posOf_range_eq k v h.1.2
    have hb := posOf_range_eq k b h.2
    simp only [Core.posOf] at ht hv hb
    rw [ht, hv, hb]
  | .lit _, _ => rfl
  | .proj s i e, h => by
    simp only [Core.posOf, Expr.instantiateLevelParams]
    exact congrArg (Expr.proj s i) (posOf_range_eq k e h)

/-- Connect `StripPisZetaSort` on `Core.posOf fam.cvS.levelParams fam.cvS.type` to `fam.p.resSort`
via `FamRead FormerOpenTraceAt`. -/
theorem famRead_cvS_eq {L : Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} {k : KKey} {cv : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon}
    (hread : FamRead L t E env fam) (hname : fam.p.cvT.name = k)
    (hfind : env.find? k = some (.indInfo cv caps)) :
    fam.cvS = cv := by
  have hf1 := hread.stored.former
  rw [hname, hfind] at hf1
  exact (ConstantInfo.indInfo.inj (Option.some.inj hf1)).1.symm

theorem famRead_lps_range {L : Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} {bnl : Nat}
    (hread : FamRead L t E env fam) (hlen : fam.p.cvT.levelParams.length = bnl) :
    fam.p.cvT.levelParams = List.range bnl := by
  obtain ⟨_, _, _, _, _, ind, -, -, -, -, -, -, -, -, -, -, -, hlpsR⟩ := hread.record
  rw [hlpsR] at hlen ⊢
  have hnl : ind.lvls.toNat = bnl := by simpa using hlen
  rw [hnl]

theorem famRead_resSort_of_stripPisZetaSort {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Env .anon} {fam : NativeFam .anon} {n : Nat} {sortL : KLevel}
    (hwf : Ix.Kernel.EnvWF env)
    (hread : FamRead FormerOpenTraceAt t E env fam)
    (hsz : StripPisZetaSort n 0 (Core.posOf fam.cvS.levelParams fam.cvS.type) sortL) :
    n = fam.p.nP + fam.p.nIdx ∧ Core.LvEq sortL fam.p.resSort := by
  obtain ⟨-, -, -, -, -, ind, -, -, -, -, -, -, -, -, -, -, -, hlpsR⟩ := hread.record
  have hlpsS : fam.cvS.levelParams = List.range ind.lvls.toNat :=
    hread.lps.trans hlpsR
  have hc := hwf _ (Ix.Kernel.Semantics.Env.find?_mem hread.stored.former)
  have hdef : fam.cvS.type.allLevelParamsDefined (List.range ind.lvls.toNat) = true := by
    rw [← hlpsS]; exact hc.2.1
  have hpos : Core.posOf fam.cvS.levelParams fam.cvS.type = fam.cvS.type := by
    rw [hlpsS]; exact posOf_range_eq ind.lvls.toNat fam.cvS.type hdef
  rw [hpos] at hsz
  obtain ⟨s', hot, hlv⟩ := hread.link.result
  obtain ⟨hnm, rfl⟩ := stripPisZetaSort_eq_of_openSortTrace (.refl _) hot hsz
  exact ⟨hnm, hlv⟩

/-! ## Section 3: Positional level-parameter transport -/

/-- Original-parameter valuation corresponding to positional valuation `ψ`. -/
def origVal (ps : List LevelParam) (ψ : LevelParam → Nat) : LevelParam → Nat :=
  Level.substFn ψ ps (Core.posLevels ps)

/-- Valuation for a `(bnl + 1)`-level recursor or recursor model whose leading motive universe is
`pheadLvls.getD 0 .zero` and whose remaining `bnl` universes are positional `0 .. bnl - 1`. -/
def ψ_rec (pheadLvls : List KLevel) (bnl : Nat) (ψ : LevelParam → Nat) : LevelParam → Nat :=
  fun k =>
    if k = 0 then (pheadLvls.getD 0 .zero).eval ψ
    else if k < bnl + 1 then ψ (k - 1)
    else ψ k

theorem posOf_denoteMeta {V : Type u} [SetTheory V] {env : Env .anon}
    (m : EnvModel V env) (ps : List LevelParam) (ψ : LevelParam → Nat) (d : Nat) (e : KExpr) :
    denoteMeta m.acval env ψ d (Core.posOf ps e) =
      denoteMeta m.acval env (origVal ps ψ) d e := by
  unfold Core.posOf origVal
  exact denotePInstLevels m ψ ps (Core.posLevels ps) d e

theorem substFn_getElem {ψ : LevelParam → Nat} :
    ∀ (ks : List LevelParam) (us : List KLevel) (hnd : ks.Nodup) (hl : ks.length = us.length)
      (i : Nat) (hi : i < ks.length),
        Level.substFn ψ ks us ks[i] = (us[i]'(by omega)).eval ψ
  | [], _, _, _, _, hi => nomatch hi
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | k :: ks, u :: us, _, _, 0, _ => by
    simp [Level.substFn]
  | k :: ks, u :: us, hnd, hl, i + 1, hi => by
    have hnd' := List.nodup_cons.mp hnd
    have hlt : i < ks.length := by simpa using hi
    have hne : k ≠ ks[i] := fun heq => hnd'.1 (heq ▸ List.getElem_mem hlt)
    change (if k = ks[i] then u.eval ψ else Level.substFn ψ ks us ks[i]) = _
    simp only [hne, ↓reduceIte]
    exact substFn_getElem ks us hnd'.2 (by simpa using hl) i hlt

theorem lvEqList_getElem {us vs : List KLevel} (h : LvEqList us vs) :
    us.length = vs.length ∧
    ∀ (i : Nat) (hu : i < us.length) (hv : i < vs.length) (ψ : LevelParam → Nat),
      us[i].eval ψ = vs[i].eval ψ := by
  have hgo : ∀ (φ : LevelParam → Nat) (xs ys : List KLevel),
      Level.EvalEqList φ xs ys →
      xs.length = ys.length ∧
      ∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length),
        xs[i].eval φ = ys[i].eval φ := by
    intro φ xs
    induction xs with
    | nil =>
      intro ys heq
      cases ys with
      | nil => exact ⟨rfl, fun _ hx _ => nomatch hx⟩
      | cons _ _ => exact heq.elim
    | cons x xs ih =>
      intro ys heq
      cases ys with
      | nil => exact heq.elim
      | cons y ys =>
        obtain ⟨h1, hr⟩ := heq
        obtain ⟨hlen, hget⟩ := ih ys hr
        refine ⟨congrArg Nat.succ hlen, fun i hx hy => ?_⟩
        cases i with
        | zero => exact h1
        | succ j => exact hget j (by simpa using hx) (by simpa using hy)
  exact ⟨(hgo (fun _ => 0) us vs (h (fun _ => 0))).1,
    fun i hu hv ψ => (hgo ψ us vs (h ψ)).2 i hu hv⟩

theorem substFn_eq_origVal_rec {ps : List LevelParam} {pheadLvls : List KLevel} {bnl : Nat}
    (hlen : ps.length = bnl + 1) (hperm : ps.Perm (List.range (bnl + 1)))
    (hlvls_len : pheadLvls.length = bnl + 1)
    (hlvls_drop : LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param))
    (ψ : LevelParam → Nat) :
    ∀ p ∈ ps,
      Level.substFn ψ ps pheadLvls p = origVal ps (ψ_rec pheadLvls bnl ψ) p := by
  have hnodup : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hpos_len : (Core.posLevels ps).length = ps.length := by simp [Core.posLevels]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  rw [substFn_getElem ps pheadLvls hnodup (by omega) i hi]
  unfold origVal
  rw [substFn_getElem ps (Core.posLevels ps) hnodup hpos_len.symm i hi]
  have hpos_get : (Core.posLevels ps)[i]'(by omega) = .param i := by
    simp [Core.posLevels]
  rw [hpos_get]
  simp only [Level.eval]
  cases i with
  | zero =>
    simp [ψ_rec, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : 0 < pheadLvls.length)]
  | succ j =>
    have hj : j < bnl := by omega
    have hdrop_eq := (lvEqList_getElem hlvls_drop).2 j (by simp; omega) (by simp; omega) ψ
    have h1 : (pheadLvls.drop 1)[j]'(by simp; omega) = pheadLvls[j + 1]'(by omega) := by
      simp
    have h2 : ((List.range bnl).map Level.param)[j]'(by simp; omega) = .param j := by
      simp
    rw [h1, h2] at hdrop_eq
    simp only [Level.eval] at hdrop_eq
    simp only [ψ_rec, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      show j + 1 < bnl + 1 by omega, Nat.add_sub_cancel]
    exact hdrop_eq

theorem substFn_eq_of_lvEqList {ps : List LevelParam} {us vs : List KLevel}
    (h : LvEqList us vs) (ψ : LevelParam → Nat) :
    Level.substFn ψ ps us = Level.substFn ψ ps vs := by
  funext p
  have hφ := h ψ
  induction ps generalizing us vs with
  | nil => rfl
  | cons k ks ih =>
    cases us with
    | nil =>
      cases vs with
      | nil => rfl
      | cons _ _ => exact hφ.elim
    | cons u us =>
      cases vs with
      | nil => exact hφ.elim
      | cons v vs =>
        obtain ⟨h1, hrest⟩ := hφ
        simp only [Level.substFn]
        split
        · exact h1
        · exact ih (fun φ => (h φ).2) hrest

theorem substFn_range_param (n : Nat) (ψ : LevelParam → Nat) :
    Level.substFn ψ (List.range n) ((List.range n).map .param) = ψ := by
  funext p
  by_cases hp : p < n
  · have h := substFn_getElem (ψ := ψ) (List.range n) ((List.range n).map .param)
      List.nodup_range (by simp) p (by simp [hp])
    simpa [Level.eval] using h
  · have hgo : ∀ (ks : List LevelParam) (us : List KLevel),
        p ∉ ks → Level.substFn ψ ks us p = ψ p := by
      intro ks us hnot
      induction ks generalizing us with
      | nil => rfl
      | cons k ks ih =>
        cases us with
        | nil => rfl
        | cons u us =>
          have hne : k ≠ p := fun heq => hnot (heq ▸ List.mem_cons_self)
          change (if k = p then u.eval ψ else Level.substFn ψ ks us p) = ψ p
          simp only [hne, ↓reduceIte]
          exact ih us (fun hm => hnot (List.mem_cons_of_mem _ hm))
    exact hgo (List.range n) ((List.range n).map .param) (by simpa [List.mem_range] using hp)

/-! ## Section 4: `Rules.DefEq` inversion on `∀` and `Rules.Infer` on `λ` -/

theorem Infer.lam_inv {env : Env .anon} {g : Ix.Kernel.Rules.Grade} {d : Nat}
    {ty body t : KExpr} {mb : BinderMeta}
    (h : Ix.Kernel.Rules.Infer env g d (.lam ty body mb) t) :
    ∃ bt,
      Ix.Kernel.Rules.Infer env g (d + 1) (body.instantiate1 (.fvar d ty)) bt ∧
      t = .forallE ty (bt.abstract1 d) mb := by
  cases h with
  | lam _ _ hbt _ _ _ _ => exact ⟨_, hbt, rfl⟩

/-! ## Section 5: `Eq.refl` interpretation and `aux` fibre disjointness -/

/-- `Eq.refl` applied to any argument spine interprets to `pt` in any set model storing `eqA` and
`eqReflA`. -/
theorem eqRefl_interp_pt {V : Type u} [SetTheory V] {env : Env .anon}
    (mp : EnvModelM V .verified env)
    (hEq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hRefl : env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA)
    (ψ : LevelParam → Nat) (ρ : Nat → V) (args : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval Ix.Kernel.eqReflName ψ) args) = (pt : V) := by
  have hmemR : Ix.Kernel.eqReflA ∈ env.consts := Ix.Kernel.Semantics.Env.find?_mem hRefl
  obtain ⟨ta, hta⟩ := mp.type_reads Ix.Kernel.eqReflA hmemR ψ
  have hty : (Ix.Kernel.eqReflA (md := .anon)).toConstantVal.type =
      Expr.forallE (.sort (.param Ix.Kernel.uN))
        (Expr.forallE (.bvar 0)
          (.app (.app (.app (.const Ix.Kernel.eqName [.param Ix.Kernel.uN]) (.bvar 1))
            (.bvar 0)) (.bvar 0))
          { pw := .ifAllZero [] })
        { pw := .ifAllZero [] } := rfl
  rw [hty] at hta
  obtain ⟨Aa, Ba, -, -, htaEq⟩ := denoteMeta_forallE_inv hta
  have hmem := mp.mem_type Ix.Kernel.eqReflA hmemR ψ ta hta ρ
  rw [htaEq] at hmem
  have hbit : Ix.Kernel.Model.pwBit ψ ({ pw := .ifAllZero [] } : BinderMeta).pw = 0 := rfl
  rw [hbit] at hmem
  simp only [interp, piR_zero] at hmem
  have hpt : interp V ρ (mp.base2.acval Ix.Kernel.eqReflName ψ) = (pt : V) :=
    (mem_truthVal.mp hmem).2
  have hgo : ∀ (f : AnnotTerm) (as : List AnnotTerm),
      interp V ρ f = (pt : V) → interp V ρ (AnnotTerm.mkAppN f as) = (pt : V) := by
    intro f as
    induction as generalizing f with
    | nil => intro hf; exact hf
    | cons a rest ih =>
      intro hf
      simp only [AnnotTerm.mkAppN]
      exact ih (.app f a) (by simp [interp, hf, app_pt])
  exact hgo _ args hpt

/-- Any two index values `t₁, t₂` whose fibres in a non-Prop indexed native family (`nIdx = 1`)
share a common element `y` are equal. -/
theorem aux_fibre_disjoint {V : Type u} [SetTheory V] {u w : Nat} (hw : w ≠ 0)
    {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (hX : Ix.Kernel.Semantics.XChainsOk u w ρp Ids rss tlss Eiss Fss Ess)
    (hEs : ∀ j, j < Fss.length → (Ess.getD j []).length = Ids.length)
    (hIds : Ids.length = 1)
    {t₁ t₂ y : V}
    (ht₁ : SpineFit ρp Ids [t₁]) (ht₂ : SpineFit ρp Ids [t₂])
    (hy₁ : y ∈ˢ SetTheory.app (fixFamI u w ρp Ids 1 rss tlss Eiss Fss Ess) (tupW u [t₁]))
    (hy₂ : y ∈ˢ SetTheory.app (fixFamI u w ρp Ids 1 rss tlss Eiss Fss Ess) (tupW u [t₂])) :
    t₁ = t₂ := by
  have ht₁m : tupW u [t₁] ∈ˢ Ix.Kernel.Semantics.idxSet u ρp Ids :=
    Ix.Kernel.Semantics.tupW_mem ht₁
  have ht₂m : tupW u [t₂] ∈ˢ Ix.Kernel.Semantics.idxSet u ρp Ids :=
    Ix.Kernel.Semantics.tupW_mem ht₂
  rw [← hIds] at hy₁ hy₂
  rw [← fixFamI_app_eq hX ht₁m] at hy₁
  rw [← fixFamI_app_eq hX ht₂m] at hy₂
  obtain ⟨j₁, fs₁, hy1_eq, hj₁, hlen₁, -, hall₁⟩ := fixStepI_elim hw hy₁
  obtain ⟨j₂, fs₂, hy2_eq, hj₂, hlen₂, -, hall₂⟩ := fixStepI_elim hw hy₂
  have h12 : inj j₁ (mkTower (fs₁ ++ [pt])) = inj j₂ (mkTower (fs₂ ++ [pt])) :=
    hy1_eq.symm.trans hy2_eq
  have hj_eq : j₁ = j₂ := by
    have hfst := congrArg sfst h12
    simp only [inj, sfst_spair] at hfst
    exact vnat_inj hfst
  subst hj_eq
  have hmt : mkTower (fs₁ ++ [pt]) = mkTower (fs₂ ++ [pt]) := by
    have hsnd := congrArg ssnd h12
    simpa [inj, ssnd_spair] using hsnd
  have hfs_eq : fs₁ = fs₂ := by
    apply List.ext_getElem (by omega)
    intro k hk1 hk2
    have hp := congrArg (projS k) hmt
    rw [projS_mkTower k (fs₁ ++ [pt]) (by simp; omega),
      projS_mkTower k (fs₂ ++ [pt]) (by simp; omega)] at hp
    simpa [List.getElem_append_left hk1, List.getElem_append_left hk2] using hp
  subst hfs_eq
  have hEsj : (Ess.getD j₁ []).length = Ids.length := hEs j₁ hj₁
  have hv₁ := idxValsAt_of_eqsXI hX.hI ht₁ hEsj (hlen₁ ▸ hall₁)
  have hv₂ := idxValsAt_of_eqsXI hX.hI ht₂ hEsj (hlen₁ ▸ hall₂)
  have hlist : [t₁] = [t₂] := hv₁.symm.trans hv₂
  exact (List.cons.inj hlist).1

/-! ## Section 6: `auxRec_not_reserved` -/

private def basisRecMajReserved (bci : ConstantInfo .anon) : Bool :=
  match bci with
  | .recInfo cvB mIB _ _ =>
    match (Core.posOf cvB.levelParams cvB.type).stripPis mIB with
    | some (_, .forallE d _ _) =>
      match d.getAppFn with
      | .const hk _ => Ix.Kernel.reservedBasisNames.contains hk
      | _ => false
    | _ => false
  | _ => true

private theorem basisEnv_rec_maj_reserved :
    IxVM.Refinement.TableInhabit.basisEnv.consts.all basisRecMajReserved = true := by
  decide +kernel

/-- A recursor whose major-premise head is not in `reservedBasisNames` is itself not in
`reservedBasisNames`. -/
theorem auxRec_not_reserved {env : Env .anon} {auxRecKey auxKey : KKey}
    {cvAuxRec : ConstantVal .anon} {mI rP : Nat} {arules : List (RecRule .anon)}
    (hfind : env.find? auxRecKey = some (.recInfo cvAuxRec mI rP arules))
    (hnotResAux : Ix.Kernel.reservedBasisNames.contains auxKey = false)
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts,
      env.find? ci.name = some ci)
    {majBs : List (KExpr × BinderMeta)} {majDom majBody : KExpr} {majBm : BinderMeta}
    {majLvls : List KLevel} {majArgs : List KExpr}
    (hmaj : (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis mI =
      some (majBs, .forallE majDom majBody majBm))
    (hmajDom : majDom = Expr.mkAppN (.const auxKey majLvls) majArgs) :
    Ix.Kernel.reservedBasisNames.contains auxRecKey = false := by
  cases hres : Ix.Kernel.reservedBasisNames.contains auxRecKey with
  | false => rfl
  | true =>
    exfalso
    have hmem_res : auxRecKey ∈ Ix.Kernel.reservedBasisNames := by
      simpa [List.contains_eq_mem] using hres
    simp only [Ix.Kernel.reservedBasisNames, List.mem_cons, List.not_mem_nil, or_false] at hmem_res
    have check_basis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts,
        ci.name = auxRecKey → False := by
      intro ci hci hname
      have hf := hbasis ci hci
      rw [hname, hfind] at hf
      have heq := Option.some.inj hf
      cases ci with
      | recInfo cv' mI' rP' rls' =>
        injection heq with hcv hmI _ _
        subst hcv; subst hmI
        have hB := List.all_eq_true.mp basisEnv_rec_maj_reserved _ hci
        simp only [basisRecMajReserved, hmaj, hmajDom, Expr.getAppFn_mkAppN,
          Expr.getAppFn] at hB
        rw [hnotResAux] at hB
        cases hB
      | _ => cases heq
    rcases hmem_res with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      (first
        | exact check_basis Ix.Kernel.eqA (by decide) rfl
        | exact check_basis Ix.Kernel.eqReflA (by decide) rfl
        | exact check_basis Ix.Kernel.eqRecA (by decide) rfl
        | exact check_basis Ix.Kernel.natA (by decide) rfl
        | exact check_basis Ix.Kernel.natZeroA (by decide) rfl
        | exact check_basis Ix.Kernel.natSuccA (by decide) rfl
        | exact check_basis Ix.Kernel.natRecA (by decide) rfl
        | exact check_basis Ix.Kernel.punitA (by decide) rfl
        | exact check_basis Ix.Kernel.punitUnitA (by decide) rfl
        | exact check_basis Ix.Kernel.punitRecA (by decide) rfl
        | exact check_basis Ix.Kernel.emptyA (by decide) rfl
        | exact check_basis Ix.Kernel.emptyRecA (by decide) rfl
        | exact check_basis Ix.Kernel.falseA (by decide) rfl
        | exact check_basis Ix.Kernel.falseRecA (by decide) rfl
        | exact check_basis Ix.Kernel.quotA (by decide) rfl
        | exact check_basis Ix.Kernel.quotMkA (by decide) rfl
        | exact check_basis Ix.Kernel.quotLiftA (by decide) rfl
        | exact check_basis Ix.Kernel.quotIndA (by decide) rfl
        | exact check_basis Ix.Kernel.quotSoundA (by decide) rfl)

end IxVM.Refinement.Typing.FamilyAlias
