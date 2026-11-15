import IxVMRefinement.Decl.Value
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Model.DeclIndJ
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.Level

/-! # Positional level-parameter judgement package (`posRulesJ`) for modeled declarations

Modeled inductive blocks (and auxiliary model definitions generated with permuted level-parameter
lists such as `elim :: List.range n`) store terms whose `ConstantVal.levelParams` is a permutation
`ps.Perm (List.range ps.length)` rather than literally `List.range n`, while the VM heap represents
every loaded constant in positional space via `posOf ps`.

Raw syntactic `DefEq` is not unconditionally closed under arbitrary level-parameter substitution
(`DefEq.unitLikeTy` inspects an empty environment slot), whereas the semantic reading `denoteMeta`
crosses level instantiations unconditionally and exactly (`Ix.Kernel.Model.denotePInstLevels`).
We therefore package positional derivations into `posRulesJ : Judgements .anon`, prove
`JudgeSound posRulesJ mp.base2` directly from `judgeSound_rulesJ_of mp` via `denotePInstLevels`,
and lift both `DeclStoreInv` (across intermediate member/provisioned environments and full
`DeclIndRunJ posRulesJ` steps) and `DeclInv` across `posRulesJ` steps. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule IndCaps EnvExt)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ValueFrontRunJ DeclDefnRunJ DeclRunJ
  IndRoutesJ MemberValRunJ IndMembersRunJ ProvisionRecsRunJ IndRecsFoldRunJ IndRecsRunJ DeclIndRunJ)
open Ix.Kernel.Model (rulesJ EnvModel EnvModelM EnvModelT JudgeFrames JudgeSound NewSat)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Exact two-sided bijection between `posOf ps` and `invPosOf ps` -/

/-- Inverse of `posOf ps`, mapping positional parameters `0, …, ps.length - 1` back to `ps`. -/
def invPosOf (ps : List LevelParam) (e : KExpr) : KExpr :=
  e.instantiateLevelParams (List.range ps.length) (ps.map .param)

/-- Inverse of `Level.subst ps (posLevels ps)` on universe levels. -/
def invPosLevel (ps : List LevelParam) (u : KLevel) : KLevel :=
  Level.subst (List.range ps.length) (ps.map .param) u

/-- `invPosOf ps` is a left inverse to `posOf ps` when `ps.Perm (List.range ps.length)`. -/
theorem invPosOf_posOf {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (e : KExpr) : invPosOf ps (posOf ps e) = e :=
  posOf_perm_inv hperm e

/-- `posOf ps` is injective when `ps.Perm (List.range ps.length)`. -/
theorem posOf_inj {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {a b : KExpr} (h : posOf ps a = posOf ps b) : a = b := by
  rw [← invPosOf_posOf hperm a, ← invPosOf_posOf hperm b, h]

private theorem subst_go_getElem :
    ∀ (ks : List LevelParam) (vs : List KLevel) (i : Nat) (hnd : ks.Nodup)
      (hlen : vs.length = ks.length) (hi : i < ks.length),
      Level.subst.go ks vs ks[i] = vs[i]'(hlen ▸ hi)
  | [], _, _, _, _, hi => nomatch hi
  | k :: ks, [], _, _, hlen, _ => nomatch hlen
  | k :: ks, v :: vs, 0, _, _, _ => by
    show (if k = k then v else Level.subst.go ks vs k) = v
    exact ite_eq_left rfl
  | k :: ks, v :: vs, i + 1, hnd, hlen, hi => by
    obtain ⟨hk_not_mem, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hlen' : vs.length = ks.length := Nat.succ.inj hlen
    have hne : k ≠ ks[i] := fun heq => hk_not_mem (heq ▸ List.getElem_mem hi')
    show (if k = ks[i] then v else Level.subst.go ks vs ks[i]) = vs[i]'(hlen' ▸ hi')
    rw [ite_eq_right hne]
    exact subst_go_getElem ks vs i hnd' hlen' hi'

/-- `Level.subst ps (posLevels ps)` is a left inverse to `invPosLevel ps` when
`ps.Perm (List.range ps.length)`. -/
theorem subst_invPosLevel {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) :
    ∀ u : KLevel, Level.subst ps (posLevels ps) (invPosLevel ps u) = u
  | .zero => rfl
  | .succ u => congrArg Level.succ (subst_invPosLevel hperm u)
  | .max a b => by
    simp only [invPosLevel, Level.subst]
    exact congrArg₂ Level.max (subst_invPosLevel hperm a) (subst_invPosLevel hperm b)
  | .imax a b => by
    simp only [invPosLevel, Level.subst]
    exact congrArg₂ Level.imax (subst_invPosLevel hperm a) (subst_invPosLevel hperm b)
  | .param p => by
    have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
    show Level.subst ps (posLevels ps)
      (Level.subst.go (List.range ps.length) (ps.map .param) p) = .param p
    by_cases hp : p < ps.length
    · have hp_len : p < (ps.map Level.param).length := by rw [List.length_map]; exact hp
      have hget := InferAux.getElem?_eq_subst_go_range (us := ps.map Level.param) hp_len
      rw [List.length_map, List.getElem?_map, List.getElem?_eq_getElem hp] at hget
      have hgo : Level.subst.go (List.range ps.length) (ps.map .param) p = .param ps[p] :=
        (Option.some.inj hget).symm
      rw [hgo]
      show Level.subst.go ps (posLevels ps) ps[p] = .param p
      have hlen : (posLevels ps).length = ps.length := by
        simp [posLevels]
      rw [subst_go_getElem ps (posLevels ps) p hnd hlen hp]
      simp [posLevels]
    · have hp_range : p ∉ List.range ps.length := by
        rw [List.mem_range]; exact hp
      have hp_ps : p ∉ ps := fun hm => hp_range (hperm.mem_iff.mp hm)
      rw [InferAux.subst_go_of_not_mem hp_range]
      exact InferAux.subst_go_of_not_mem hp_ps

private theorem substPW_invPos {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (pw : Ix.Kernel.PropWhen) :
    Level.substPW ps (posLevels ps)
      (Level.substPW (List.range ps.length) (ps.map .param) pw) = pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Level.holds_substPW, Level.holds_substPW]
  congr 1
  funext p
  rw [← Level.eval_subst_go, ← Level.eval_subst]
  exact congrArg (Level.eval φ) (subst_invPosLevel hperm (.param p))

/-- `posOf ps` is a right inverse to `invPosOf ps` (unconditionally for every term `e`) when
`ps.Perm (List.range ps.length)`. -/
theorem posOf_invPosOf {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) :
    ∀ e : KExpr, posOf ps (invPosOf ps e) = e := by
  intro e
  unfold posOf invPosOf
  induction e with
  | bvar _ | lit _ => rfl
  | fvar idx ty ih => simp only [Expr.instantiateLevelParams, ih]
  | sort u =>
    simp only [Expr.instantiateLevelParams]
    exact congrArg Expr.sort (subst_invPosLevel hperm u)
  | const n us =>
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    have hmap : us.map (Level.subst ps (posLevels ps) ∘
        Level.subst (List.range ps.length) (ps.map .param)) = us.map id :=
      List.map_congr_left fun u _ => subst_invPosLevel hperm u
    simpa using hmap
  | app f a ihf iha => simp only [Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_invPos hperm m.pw]
  | forallE ty body m iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_invPos hperm m.pw]
  | letE ty val body l iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihv, ihb]
  | proj s i e ih => simp only [Expr.instantiateLevelParams, ih]

/-! ## Valuation crossing and scoping preservation under `posOf` -/

/-- Valuation transporting positional universe parameters back to `φ`. -/
def posVal (ps : List LevelParam) (φ : LevelParam → Nat) : LevelParam → Nat :=
  Level.substFn φ (List.range ps.length) (ps.map .param)

/-- Composing `posVal ps φ` with `(ps, posLevels ps)` recovers `φ` exactly. -/
theorem substFn_posVal {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (φ : LevelParam → Nat) :
    Level.substFn (posVal ps φ) ps (posLevels ps) = φ := by
  funext p
  have hinv : Level.subst (List.range ps.length) (ps.map .param)
      (Level.subst ps (posLevels ps) (.param p)) = .param p :=
    Expr.sort.inj (posOf_perm_inv hperm (.sort (.param p)))
  have hev := congrArg (Level.eval φ) hinv
  rw [Level.eval_subst, Level.eval_subst] at hev
  exact hev

/-- `denoteMeta` on `posOf ps e` at `posVal ps φ` equals `denoteMeta` on `e` at `φ`. -/
theorem denoteMeta_posOf {V : Type u} [Ix.Kernel.SetTheory V]
    {env : Ix.Kernel.Env .anon} (m : EnvModel V env)
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (φ : LevelParam → Nat) (d : Nat) (e : KExpr) :
    Ix.Kernel.Model.denoteMeta m.acval env (posVal ps φ) d (posOf ps e) =
      Ix.Kernel.Model.denoteMeta m.acval env φ d e := by
  unfold posOf
  rw [Ix.Kernel.Model.denotePInstLevels, substFn_posVal hperm]

theorem fvarsBelow_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (d : Nat),
      Expr.fvarsBelow d (e.instantiateLevelParams ks us) ↔ Expr.fvarsBelow d e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; simp [Expr.instantiateLevelParams, Expr.fvarsBelow]
  | fvar _ _ _ => intro _; simp [Expr.instantiateLevelParams, Expr.fvarsBelow]
  | app _ _ ihf iha =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, ihf d, iha d]
  | lam _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, iht d, ihb d]
  | forallE _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, iht d, ihb d]
  | letE _ _ _ _ iht ihv ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, iht d, ihv d, ihb d]
  | proj _ _ _ ih =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.fvarsBelow, ih d]

theorem wscoped_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (d : Nat),
      Expr.WScoped d (e.instantiateLevelParams ks us) ↔ Expr.WScoped d e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; simp [Expr.instantiateLevelParams, Expr.WScoped]
  | fvar idx _ ih =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, ih idx]
  | app _ _ ihf iha =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, ihf d, iha d]
  | lam _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, iht d, ihb d]
  | forallE _ _ _ iht ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, iht d, ihb d]
  | letE _ _ _ _ iht ihv ihb =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, iht d, ihv d, ihb d]
  | proj _ _ _ ih =>
    intro d; simp only [Expr.instantiateLevelParams, Expr.WScoped, ih d]

theorem fvarLeaves_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).fvarLeaves =
      e.fvarLeaves.map (fun l => (l.1, l.2.instantiateLevelParams ks us)) := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => simp [Expr.instantiateLevelParams, Expr.fvarLeaves]
  | fvar idx ty ih =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_cons, ih]
  | app _ _ ihf iha =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, ihf, iha]
  | lam _ _ _ iht ihb =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, iht, ihb]
  | forallE _ _ _ iht ihb =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, iht, ihb]
  | letE _ _ _ _ iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, List.map_append, iht, ihv, ihb]
  | proj _ _ _ ih =>
    simp only [Expr.instantiateLevelParams, Expr.fvarLeaves, ih]

theorem leavesBounded_instantiateLevelParams (ks : List LevelParam) (us : List KLevel)
    (e : KExpr) :
    Expr.LeavesBounded (e.instantiateLevelParams ks us) ↔ Expr.LeavesBounded e := by
  unfold Expr.LeavesBounded
  rw [fvarLeaves_instantiateLevelParams]
  constructor
  · intro h l hl
    have h' := h (l.1, l.2.instantiateLevelParams ks us) (List.mem_map_of_mem hl)
    rwa [Expr.looseBVarsBounded_instantiateLevelParams] at h'
  · intro h l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact h l hl

/-- `CtxOk` transports to positional space along `posVal ps φ`. -/
theorem ctxOk_posOf {V : Type u} [Ix.Kernel.SetTheory V]
    {env : Ix.Kernel.Env .anon} {m : EnvModel V env}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {φ : LevelParam → Nat} {d : Nat} {Δa : List Ix.Kernel.Semantics.AnnotTerm} {e : KExpr}
    (hctx : Ix.Kernel.Model.CtxOk m φ d Δa e) :
    Ix.Kernel.Model.CtxOk m (posVal ps φ) d Δa (posOf ps e) := by
  obtain ⟨hlen, hleaves⟩ := hctx
  refine ⟨hlen, fun l' hl' => ?_⟩
  unfold posOf at hl'
  rw [fvarLeaves_instantiateLevelParams] at hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  obtain ⟨hlt, hfb, tya, Aa, hden, hΔ, hint, hwd⟩ := hleaves l hl
  refine ⟨hlt, (fvarsBelow_instantiateLevelParams ps (posLevels ps) l.2 l.1).mpr hfb,
    tya, Aa, ?_, hΔ, hint, hwd⟩
  show Ix.Kernel.Model.denoteMeta m.acval env (posVal ps φ) d (posOf ps l.2) = some tya
  rw [denoteMeta_posOf m hperm φ d l.2]
  exact hden

/-! ## The positional derivation package `posRulesJ` and its soundness -/

/-- Derivation judgement package allowing a permutation `ps.Perm (List.range ps.length)` into
positional level-parameter space. -/
def posRulesJ : Judgements .anon where
  annot _ d e e' := Annot d e e'
  infer env d e t :=
    ∃ ps, ps.Perm (List.range ps.length) ∧ Infer env .full d (posOf ps e) (posOf ps t)
  defeq env d a b :=
    ∃ ps, ps.Perm (List.range ps.length) ∧ DefEq env d (posOf ps a) (posOf ps b)
  sort env d t u :=
    ∃ ps, ps.Perm (List.range ps.length) ∧
      Red env d (posOf ps t) (.sort (Level.subst ps (posLevels ps) u))
  isZero u := ∀ φ : LevelParam → Nat, Level.eval φ u = 0
  thmValue _ v' := v'

/-- Construct `posRulesJ.infer` from a positional `Rules.Infer` derivation by pulling back the
inferred type along `invPosOf ps`. -/
theorem posRulesJ_infer_of_pos {env : Ix.Kernel.Env .anon} {d : Nat}
    {ps : List LevelParam} {e t_pos : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hinf : Infer env .full d (posOf ps e) t_pos) :
    posRulesJ.infer env d e (invPosOf ps t_pos) :=
  ⟨ps, hperm, by rw [posOf_invPosOf hperm]; exact hinf⟩

/-- Construct `posRulesJ.defeq` directly from a positional `Rules.DefEq` derivation. -/
theorem posRulesJ_defeq_of_pos {env : Ix.Kernel.Env .anon} {d : Nat}
    {ps : List LevelParam} {a b : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hde : DefEq env d (posOf ps a) (posOf ps b)) :
    posRulesJ.defeq env d a b :=
  ⟨ps, hperm, hde⟩

/-- Construct `posRulesJ.sort` from a positional `Rules.Red` to `.sort u_pos`. -/
theorem posRulesJ_sort_of_pos {env : Ix.Kernel.Env .anon} {d : Nat}
    {ps : List LevelParam} {t_pos : KExpr} {u_pos : KLevel}
    (hperm : ps.Perm (List.range ps.length))
    (hred : Red env d t_pos (.sort u_pos)) :
    posRulesJ.sort env d (invPosOf ps t_pos) (invPosLevel ps u_pos) :=
  ⟨ps, hperm, by rw [posOf_invPosOf hperm, subst_invPosLevel hperm]; exact hred⟩

/-- Scoping frames for `posRulesJ` (`posRulesJ.annot` is `rulesJ.annot`). -/
theorem judgeFrames_posRulesJ (env : Ix.Kernel.Env .anon) : JudgeFrames posRulesJ env :=
  let h := Ix.Kernel.Model.judgeFrames_rulesJ env
  ⟨h.annot_syntax, h.annot_wscoped, h.annot_bounded, h.annot_leaves⟩

/-- **Model soundness of `posRulesJ`**, derived from `judgeSound_rulesJ_of` via `denoteMeta_posOf`. -/
theorem judgeSound_posRulesJ_of {V : Type u} [Ix.Kernel.SetTheory V]
    {μ : Ix.Kernel.CheckMode} {env : Ix.Kernel.Env .anon}
    (mp : EnvModelM V μ env) : JudgeSound posRulesJ mp.base2 where
  toJudgeFrames := judgeFrames_posRulesJ env
  accepted := by
    intro φ d e t ⟨ps, hperm, hpos⟩ hws hb hL
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    obtain ⟨ea, hea⟩ := hR.accepted (posVal ps φ) hpos hws' hb' hL'
    rw [denoteMeta_posOf mp.base2 hperm φ d e] at hea
    exact ⟨ea, hea⟩
  infer := by
    intro φ d e t Δa ⟨ps, hperm, hpos⟩ hws hb hL ea ta hctx hea hta
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    have hea' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (posVal ps φ) d (posOf ps e)
        = some ea := by
      rw [denoteMeta_posOf mp.base2 hperm φ d e]; exact hea
    have hta' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (posVal ps φ) d (posOf ps t)
        = some ta := by
      rw [denoteMeta_posOf mp.base2 hperm φ d t]; exact hta
    exact hR.infer (posVal ps φ) hpos hws' hb' hL' (ctxOk_posOf hperm hctx) hea' hta'
  defeq := by
    intro φ d a b Δa ⟨ps, hperm, hpos⟩ hwsa hba hLa hwsb hbb hLb aa ba hctxa hctxb haa hba_d hwda hwdb
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hwsa' : Expr.WScoped d (posOf ps a) :=
      (wscoped_instantiateLevelParams ps (posLevels ps) a d).mpr hwsa
    have hba' : (posOf ps a).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hba
    have hLa' : Expr.LeavesBounded (posOf ps a) :=
      (leavesBounded_instantiateLevelParams ps (posLevels ps) a).mpr hLa
    have hwsb' : Expr.WScoped d (posOf ps b) :=
      (wscoped_instantiateLevelParams ps (posLevels ps) b d).mpr hwsb
    have hbb' : (posOf ps b).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbb
    have hLb' : Expr.LeavesBounded (posOf ps b) :=
      (leavesBounded_instantiateLevelParams ps (posLevels ps) b).mpr hLb
    have haa' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (posVal ps φ) d (posOf ps a)
        = some aa := by
      rw [denoteMeta_posOf mp.base2 hperm φ d a]; exact haa
    have hba_d' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (posVal ps φ) d (posOf ps b)
        = some ba := by
      rw [denoteMeta_posOf mp.base2 hperm φ d b]; exact hba_d
    exact hR.defeq (posVal ps φ) hpos hwsa' hba' hLa' hwsb' hbb' hLb'
      (ctxOk_posOf hperm hctxa) (ctxOk_posOf hperm hctxb) haa' hba_d' hwda hwdb
  reads := by
    intro φ d e t Δa ea ⟨ps, hperm, hpos⟩ hws hb hL hctx hea
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    have hea' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (posVal ps φ) d (posOf ps e)
        = some ea := by
      rw [denoteMeta_posOf mp.base2 hperm φ d e]; exact hea
    obtain ⟨ta, hta'⟩ := hR.reads (posVal ps φ) hpos hws' hb' hL' (ctxOk_posOf hperm hctx) hea'
    rw [denoteMeta_posOf mp.base2 hperm φ d t] at hta'
    exact ⟨ta, hta'⟩
  frame := by
    intro φ d e t Δa ea ⟨ps, hperm, hpos⟩ hws hb hL hctx hea
    have hR := Ix.Kernel.Model.judgeSound_rulesJ_of mp
    have hws' : Expr.WScoped d (posOf ps e) :=
      (wscoped_instantiateLevelParams ps (posLevels ps) e d).mpr hws
    have hb' : (posOf ps e).looseBVarsBounded 0 = true := by
      unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb
    have hL' : Expr.LeavesBounded (posOf ps e) :=
      (leavesBounded_instantiateLevelParams ps (posLevels ps) e).mpr hL
    have hea' : Ix.Kernel.Model.denoteMeta mp.base2.acval env (posVal ps φ) d (posOf ps e)
        = some ea := by
      rw [denoteMeta_posOf mp.base2 hperm φ d e]; exact hea
    obtain ⟨hwst', hbt', hsub'⟩ :=
      hR.frame (posVal ps φ) hpos hws' hb' hL' (ctxOk_posOf hperm hctx) hea'
    refine ⟨(wscoped_instantiateLevelParams ps (posLevels ps) t d).mp hwst', ?_, ?_⟩
    · unfold posOf at hbt'
      rwa [Expr.looseBVarsBounded_instantiateLevelParams] at hbt'
    · intro l hl
      have hl_pos : (l.1, posOf ps l.2) ∈ (posOf ps t).fvarLeaves := by
        unfold posOf
        rw [fvarLeaves_instantiateLevelParams]
        exact List.mem_map_of_mem hl
      have hm_pos := hsub' _ hl_pos
      unfold posOf at hm_pos
      rw [fvarLeaves_instantiateLevelParams] at hm_pos
      obtain ⟨m, hm, heq⟩ := List.mem_map.mp hm_pos
      obtain ⟨hm1, hm2⟩ := Prod.mk.inj heq
      have hm2' : m.2 = l.2 := posOf_inj hperm hm2
      have hml : m = l := Prod.ext hm1 hm2'
      exact hml ▸ hm

/-! ## Shared front-end assembly at `posRulesJ` (any `Perm` of `List.range`) -/

private def zeroGhostPos : Nat → KExpr := fun _ => .sort .zero

/-- Assemble `ConstantValRunJ posRulesJ` from `validate_expr_well_scoped` + `k_ensure_sort` on an
exact closed type representation with `cv.levelParams.Perm (List.range cv.levelParams.length)`
(carried directly in `ValRepExact`). -/
theorem constantValRunJ_pos_of_front (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {type' : KExpr}
    {rc nl ty v55 v92 : SourceValue F} {h m56 m93 m124 : Heap F}
    {cs66 cs103 : List (Call F)}
    (hfresh : env.find? cv.name = none)
    (hres : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hnoprj : cv.name.isProjFnShape = false)
    (hcv_bvs : cv.type.looseBVarsBounded 0 = true)
    (hcv_nfv : cv.type.hasFvar = false)
    (hcenv : c.env = env)
    (hval : ValRepExact c.κ h nl ty ⟨cv.name, cv.levelParams, type'⟩)
    (hann : IxVM.Consistency.Annotates type' cv.type)
    (hrc : RCRep c.t c.lim h rc) (hef : EnvFacts c) (hlf : LoadFacts c)
    (hg66 : Good c cs66) (hg103 : Good c cs103)
    (ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v55 m56 cs66)
    (hm124 : m124 = m56 ++ [.construct kexprListEnum "Nil" []])
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort"
      [rc, ty, .ptr (.enum kexprListEnum) m56.length] m124 v92 m93 cs103) :
    ConstantValRunJ posRulesJ env cv type' := by
  obtain ⟨rfl, hnl, hperm, hty_rep⟩ := hval
  have hlvl_pos : (posOf cv.levelParams type').allLevelParamsDefined
      (List.range cv.levelParams.length) = true :=
    validate_expr_well_scoped_spec hnl (hty_rep 0 zeroGhostPos) ev_sc
  have hlvl_def : type'.allLevelParamsDefined cv.levelParams = true :=
    allLevelParamsDefined_of_posOf_perm hperm hlvl_pos
  have e_sc := ObsFn.heap_extends ev_sc
  have e_nil : Heap.Extends h m124 :=
    hm124 ▸ e_sc.trans (heap_extends_append m56 _)
  have htypes : TypesRep c.κ zeroGhostPos m124 0 (.ptr (.enum kexprListEnum) m56.length) :=
    hm124 ▸ typesRep_alloc_nil c.κ zeroGhostPos m56
  obtain ⟨stype_pos, u_pos, _, hinf0, hred0, _, _⟩ :=
    core_ensure_sort hCore (hrc.mono e_nil) htypes (ghostScoped_zero zeroGhostPos) hef hlf hg103
      ev_sort ((hty_rep 0 zeroGhostPos).toTm.mono e_nil)
  have hinf_pos : Infer env .full 0 (posOf cv.levelParams type') stype_pos := hcenv ▸ hinf0
  have hred_pos : Red env 0 stype_pos (.sort u_pos) := hcenv ▸ hred0
  have hpos_nfv : (posOf cv.levelParams type').hasFvar = false :=
    Tm.hasFvar_false (hty_rep 0 zeroGhostPos).toTm
  have hcr_pos : (posOf cv.levelParams type').constsResolve env = true :=
    infer_constsResolve hinf_pos (hcenv ▸ hef.store) hpos_nfv
  have hcr : type'.constsResolve env = true := by
    rw [constsResolve_posOf] at hcr_pos; exact hcr_pos
  exact ⟨by rw [hfresh]; rfl, hres, hnoprj, levelParam_nodup_of_perm_range hperm,
    hcv_bvs, hcv_nfv, annot_of_annotates hann hcv_nfv hcv_bvs 0, hlvl_def, hcr,
    invPosOf cv.levelParams stype_pos, invPosLevel cv.levelParams u_pos,
    posRulesJ_infer_of_pos hperm hinf_pos,
    posRulesJ_sort_of_pos hperm hred_pos⟩

/-- Assemble `ValueFrontRunJ posRulesJ` from `validate_expr_well_scoped` + `k_check` on exact closed
type and value representations in positional space (`posOf cv.levelParams`). -/
theorem valueFrontRunJ_pos_of_front (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {value type' value' : KExpr}
    {rc ty val v_sc r_chk : SourceValue F} {h₀ h_sc h_pre h_chk h_chk' h' : Heap F}
    {cs_sc cs_chk : List (Call F)}
    (hperm : cv.levelParams.Perm (List.range cv.levelParams.length))
    (hval_bvs : value.looseBVarsBounded 0 = true)
    (hval_nfv : value.hasFvar = false)
    (hcenv : c.env = env)
    (hnl : cv.levelParams.length < 4294967296)
    (hty_rep : TmCExact c.κ h₀ (posOf cv.levelParams type') ty)
    (hval_rep : TmCExact c.κ h₀ (posOf cv.levelParams value') val)
    (hann : IxVM.Consistency.Annotates value' value)
    (ext_sc : Heap.Extends h₀ h_sc)
    (ext_pre : Heap.Extends h₀ h_pre)
    (hrc : RCRep c.t c.lim h₀ rc) (hef : EnvFacts c) (hlf : LoadFacts c)
    (hg_sc : Good c cs_sc) (hg_chk : Good c cs_chk)
    (ev_sc : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [val, .field 0, .field (cv.levelParams.length : F)] h_sc v_sc h_chk cs_sc)
    (hm_chk : h_chk' = h_pre ++ [.construct kexprListEnum "Nil" []])
    (ev_chk : ObsFn W "KernelInfer::k_check"
      [rc, val, ty, .ptr (.enum kexprListEnum) h_pre.length] h_chk' r_chk h' cs_chk) :
    ValueFrontRunJ posRulesJ env cv value type' value' := by
  have hlvl_pos : (posOf cv.levelParams value').allLevelParamsDefined
      (List.range cv.levelParams.length) = true :=
    validate_expr_well_scoped_spec hnl ((hval_rep 0 zeroGhostPos).mono ext_sc) ev_sc
  have hlvl_def : value'.allLevelParamsDefined cv.levelParams = true :=
    allLevelParamsDefined_of_posOf_perm hperm hlvl_pos
  have e_chk : Heap.Extends h₀ h_chk' :=
    hm_chk ▸ ext_pre.trans (heap_extends_append h_pre _)
  have htypes : TypesRep c.κ zeroGhostPos h_chk' 0 (.ptr (.enum kexprListEnum) h_pre.length) :=
    hm_chk ▸ typesRep_alloc_nil c.κ zeroGhostPos h_pre
  obtain ⟨vt_pos, hinf0, hde0⟩ :=
    core_check hCore (hrc.mono e_chk) htypes (ghostScoped_zero zeroGhostPos) hef hlf hg_chk ev_chk
      ((hval_rep 0 zeroGhostPos).toTm.mono e_chk) ((hty_rep 0 zeroGhostPos).toTm.mono e_chk)
  have hinf_pos : Infer env .full 0 (posOf cv.levelParams value') vt_pos := hcenv ▸ hinf0
  have hde_pos : DefEq env 0 vt_pos (posOf cv.levelParams type') := hcenv ▸ hde0
  have hpos_nfv : (posOf cv.levelParams value').hasFvar = false :=
    Tm.hasFvar_false (hval_rep 0 zeroGhostPos).toTm
  have hcr_pos : (posOf cv.levelParams value').constsResolve env = true :=
    infer_constsResolve hinf_pos (hcenv ▸ hef.store) hpos_nfv
  have hcr : value'.constsResolve env = true := by
    rw [constsResolve_posOf] at hcr_pos; exact hcr_pos
  exact ⟨hval_bvs, hval_nfv, annot_of_annotates hann hval_nfv hval_bvs 0, hlvl_def, hcr,
    invPosOf cv.levelParams vt_pos,
    posRulesJ_infer_of_pos hperm hinf_pos,
    ⟨cv.levelParams, hperm, by rw [posOf_invPosOf hperm]; exact hde_pos⟩⟩

/-! ## Stepping `DeclStoreInv` and `DeclInv` across `posRulesJ` modeled and definition steps -/

/-- Provisioning recursors without rules extends the environment (`EnvExt`). -/
theorem provisionRecsRunJ_envExt {J : Judgements .anon} {blockNames : List KKey} :
    ∀ {envAcc : Ix.Kernel.Env .anon} {recs : List (ConstantInfo .anon)}
      {envSelf : Ix.Kernel.Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J blockNames envAcc recs envSelf checked →
      EnvExt envAcc envSelf
  | _, [], _, _, ⟨rfl, _⟩ => EnvExt.refl _
  | _, _ :: _, _, _, ⟨cvA, mI, rP, _, _, _, hmv, hrec, _⟩ =>
    (Ix.Kernel.Semantics.envExt_of_memberValRunJ (c := .recInfo cvA mI rP []) hmv rfl).trans
      (provisionRecsRunJ_envExt hrec)

/-- Provisioning recursors only adds rule-empty `.recInfo` entries. -/
theorem provisionRecsRunJ_newSat {J : Judgements .anon} {blockNames : List KKey}
    {Q : ConstantInfo .anon → Prop}
    (hQr : ∀ cv mI rP, Q (.recInfo cv mI rP [])) :
    ∀ {envAcc : Ix.Kernel.Env .anon} {recs : List (ConstantInfo .anon)}
      {envSelf : Ix.Kernel.Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J blockNames envAcc recs envSelf checked →
      NewSat envAcc envSelf Q
  | _, [], _, _, ⟨rfl, _⟩ => NewSat.refl _ Q
  | _, _ :: _, _, _, ⟨cvA, mI, rP, _, _, _, _, hrec, _⟩ =>
    (NewSat.cons (hQr cvA mI rP)).trans (provisionRecsRunJ_newSat hQr hrec)

/-- Installing non-recursor modeled block members preserves `DeclStoreInv` (allowing `Core` to run
at `envM` while checking recursor types). -/
theorem DeclStoreInv.indMembers_pos {blockNames : List KKey}
    {env envM : Ix.Kernel.Env .anon} {members : List (ConstantInfo .anon)}
    (h : DeclStoreInv env)
    (hmem : IndMembersRunJ posRulesJ blockNames {} env members envM) :
    DeclStoreInv envM := by
  have hext : EnvExt env envM := Ix.Kernel.Semantics.indMembersRunJ_envExt hmem
  refine
    { store := Ix.Kernel.Model.storeInv_indMembersRunJ judgeFrames_posRulesJ ⟨rfl, rfl⟩ members
        hmem h.store
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (Ix.Kernel.Model.indMembersRunJ_newSat (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ heq => nomatch heq) hmem)
      recK := Ix.Kernel.Model.recK_step_noRec h.store h.recK hext.find
        (Ix.Kernel.Model.indMembersRunJ_newSat (by intro; rintro _ _ _ _ ⟨⟩)
          (by intro _ _ _; rintro _ _ _ _ ⟨⟩) hmem)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (Ix.Kernel.Model.indMembersRunJ_newSat
          (fun _ _ _ heq he => by
            obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
            simp at he)
          (by intro _ _ _; rintro _ _ ⟨⟩) hmem)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (Ix.Kernel.Model.indMembersRunJ_newSat (by intro; rintro _ ⟨⟩)
          (by intro _ _ _; rintro _ ⟨⟩) hmem)
      recShape := Ix.Kernel.Model.recShape_step_noRec h.store h.recShape hext.find
        (Ix.Kernel.Model.indMembersRunJ_newSat (by intro; rintro _ _ _ _ ⟨⟩)
          (by intro _ _ _; rintro _ _ _ _ ⟨⟩) hmem) }

/-- Provisioning modeled recursors (with `rules = []`) preserves `DeclStoreInv` (allowing `Core` to
run at `envSelf` during `check_iota_rule`). -/
theorem DeclStoreInv.provisionRecs_pos {blockNames : List KKey}
    {envM envSelf : Ix.Kernel.Env .anon} {recs : List (ConstantInfo .anon)}
    {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
    (h : DeclStoreInv envM)
    (hprov : ProvisionRecsRunJ posRulesJ blockNames envM recs envSelf checked) :
    DeclStoreInv envSelf := by
  have hext : EnvExt envM envSelf := provisionRecsRunJ_envExt hprov
  have hnewNil : NewSat envM envSelf (fun x => ∃ cv a b, x = .recInfo cv a b []) :=
    provisionRecsRunJ_newSat (fun cv a b => ⟨cv, a, b, rfl⟩) hprov
  refine
    { store := Ix.Kernel.Model.storeInv_provisionRecsRunJ judgeFrames_posRulesJ recs hprov h.store
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (provisionRecsRunJ_newSat (by intro _ _ _; rintro _ _ ⟨⟩) hprov)
      recK := Ix.Kernel.Model.recK_step h.store h.recK hext.find (by
        intro n cv mI rP rules hf hn0
        rcases hnewNil n _ hf with hold | ⟨cv', a', b', heq⟩
        · rw [hold] at hn0; exact nomatch hn0
        · obtain ⟨_, _, _, hrls⟩ := ConstantInfo.recInfo.inj heq
          subst hrls
          exact ⟨fun _ hr => (nomatch hr), fun _ _ hr => (nomatch hr)⟩)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (provisionRecsRunJ_newSat (by intro _ _ _; rintro _ _ ⟨⟩) hprov)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (provisionRecsRunJ_newSat (by intro _ _ _; rintro _ ⟨⟩) hprov)
      recShape := Ix.Kernel.Model.recShape_step h.store h.recShape hext.find (by
        intro n cv mI rP rules hf hn0
        rcases hnewNil n _ hf with hold | ⟨cv', a', b', heq⟩
        · rw [hold] at hn0; exact nomatch hn0
        · obtain ⟨_, _, _, hrls⟩ := ConstantInfo.recInfo.inj heq
          subst hrls
          exact ⟨fun _ hr => (nomatch hr), fun _ _ hr => (nomatch hr),
            fun _ _ hr => (nomatch hr), fun _ _ heq' => (nomatch heq')⟩) }

/-- Full `DeclIndRunJ posRulesJ` step preserves `DeclStoreInv`. -/
theorem DeclStoreInv.declInd_pos {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)}
    (h : DeclStoreInv env)
    (hrun : DeclIndRunJ posRulesJ env block env₂) :
    DeclStoreInv env₂ := by
  have hext : EnvExt env env₂ := Ix.Kernel.Semantics.declIndRunJ_envExt hrun
  refine
    { store := Ix.Kernel.Model.storeInv_declIndRunJ judgeFrames_posRulesJ h.store hrun
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (Ix.Kernel.Model.modeled_newSat (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hrun)
      recK := Ix.Kernel.Model.recK_step h.store h.recK hext.find
        (Ix.Kernel.Model.modeled_recK_new hrun)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (Ix.Kernel.Model.modeled_newSat
          (fun _ _ _ heq he => by
            obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
            simp at he)
          (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hrun)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (Ix.Kernel.Model.modeled_newSat (fun _ _ heq => nomatch heq)
          (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hrun)
      recShape := Ix.Kernel.Model.recShape_step h.store h.recShape hext.find
        (Ix.Kernel.Model.modeled_recShape_new hrun) }

/-- **Full `DeclInv` preservation** across a modeled inductive block checked at `posRulesJ`. -/
theorem DeclInv.step_modeled_pos {V : Type u} [Ix.Kernel.SetTheory V]
    {env env₂ : Ix.Kernel.Env .anon} {block : List (ConstantInfo .anon)}
    (hrun : DeclIndRunJ posRulesJ env block env₂)
    (h : DeclInv V env) : DeclInv V env₂ := by
  obtain ⟨⟨⟨mp, hT⟩, hE⟩, hS⟩ := h
  obtain ⟨hE₂, mp₂, hext⟩ :=
    Ix.Kernel.Model.declIndStepJ judgeFrames_posRulesJ
      (fun m => judgeSound_posRulesJ_of m) mp hE hrun
  exact ⟨⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩, hS.declInd_pos hrun⟩

/-- Lift a `DeclStoreInv`-conditioned `DeclIndRunJ posRulesJ` witness to the full `Decls` step
obligation (`∃ env₂, InstallStep env (.indDecl block nP) env₂ ∧ ∀ V, DeclInv V env → DeclInv V env₂`). -/
theorem decls_step_of_modeled_pos {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hnodup : ((IxVM.Consistency.installs (.indDecl block nP)).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci₀.name = none)
    (hstep : DeclStoreInv env → ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      DeclIndRunJ posRulesJ env block env₂) :
    ∃ env₂, IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨env₂, hinst, hrun⟩ := hstep hS
    exact ⟨env₂, hinst, fun _ _ hInv => hInv.step_modeled_pos hrun⟩
  · obtain ⟨env₂, hinst⟩ := installStep_of_checked_fresh hchk hnodup hfresh
    exact ⟨env₂, hinst, fun _ _ hInv => absurd hInv.store hS⟩

/-- Definition step (`DeclDefnRunJ posRulesJ`, including auxiliary model definitions whose
`levelParams` are permutations of `List.range n`) preserves `DeclStoreInv`. -/
theorem DeclStoreInv.defn_pos {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (h : DeclStoreInv env)
    (hrun : DeclDefnRunJ posRulesJ env cv value hint env₂) :
    DeclStoreInv env₂ := by
  have hdecl : DeclRunJ posRulesJ (fun _ _ _ => False) env (.defnDecl cv value hint) env₂ := hrun
  have hext : EnvExt env env₂ :=
    Ix.Kernel.Semantics.declRunJ_envExt (fun hb => Ix.Kernel.Model.basisRun_envExt hb)
      (fun hf => hf.elim) hdecl
  obtain ⟨_, _, _, _, rfl, _, _⟩ := hrun
  refine
    { store := Ix.Kernel.Model.storeInv_declDefnRunJ (judgeFrames_posRulesJ env) h.store hdecl
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (NewSat.cons (fun _ _ heq => nomatch heq))
      recK := Ix.Kernel.Model.recK_step_noRec h.store h.recK hext.find
        (NewSat.cons (fun _ _ _ _ heq => nomatch heq))
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (NewSat.cons (fun _ _ heq => nomatch heq))
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find h.tableBodies
        (NewSat.cons (fun _ heq => nomatch heq))
      recShape := Ix.Kernel.Model.recShape_step_noRec h.store h.recShape hext.find
        (NewSat.cons (fun _ _ _ _ heq => nomatch heq)) }

/-- Definition step (`DeclDefnRunJ posRulesJ`) preserves `DeclInv`. -/
theorem DeclInv.step_defn_pos {V : Type u} [Ix.Kernel.SetTheory V]
    {env env₂ : Ix.Kernel.Env .anon}
    {cv : ConstantVal .anon} {value : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hrun : DeclDefnRunJ posRulesJ env cv value hint env₂)
    (h : DeclInv V env) : DeclInv V env₂ := by
  obtain ⟨⟨⟨mp, hT⟩, hE⟩, hS⟩ := h
  have hdecl : DeclRunJ posRulesJ (fun _ _ _ => False) env (.defnDecl cv value hint) env₂ := hrun
  have hE₂ : Ix.Kernel.EtaFamiliesClosed env₂ :=
    Ix.Kernel.Semantics.declEtaStepRunJ (fun hf => hf.elim) hE hdecl
  obtain ⟨mp₂, hext⟩ := Ix.Kernel.Model.harvestDefnJ mp (judgeSound_posRulesJ_of mp) hrun
  exact ⟨⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩, hS.defn_pos hrun⟩

end IxVM.Refinement.Decl
