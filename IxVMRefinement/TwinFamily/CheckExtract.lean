import IxVMRefinement.TwinFamily.WrapBridge
import IxVMRefinement.TwinFamily.Reload
import IxVMRefinement.Lib.Lists
import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.FamilyAlias.CallRecRefs
import IxVMRefinement.FamilyAlias.CallRekey
import IxVMRefinement.FamilyGraph.ProducersInnerRefs
import IxVMRefinement.FamilyGraph.ProducersRefs
import IxVMRefinement.Assembly.TypingRecLateMajorKey
import IxVMRefinement.Decl.FamilyMentions
import IxVMRefinement.Decl.Modeled
import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.Decl.ModeledTele
import IxVMRefinement.Decl.NativeCommon
import IxVMRefinement.Decl.NativeRecFieldRange
import IxVMRefinement.Core.Det
import IxVMRefinement.Core.Rekey
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled5
import IxVMRefinement.Obs.KernelCheck8
import IxVMRefinement.Claim.TopDefn
import IxVMRefinement.StatementRel.ClosedFacts
import IxVMRefinement.Assembly.TypingStore
import IxVMRefinement.Assembly.TypingFacts

/-! # Extraction of recursor readings, annotations, and front-door derivations from `check_family`

A `KernelModeled::check_family` call on a block `B` and a non-empty recursor block `A` checks every
recursor member `k` of `A` in `KernelModeled::check_recs`. This module extracts what the twin
recursor step needs from that call, without requiring any external stream wrapper:

* **Pure algebraic bridges**:
  - `posOf_canonAnn_eq_loadedAt`: `Core.posOf ps` maps the canonical annotation `canonAnn` under
    `ps` (a permutation of `0 .. ps.length - 1`) to the positional canonical reading `loadedAt`;
  - `letFree_of_canonAnn`: canonical annotations produced by `applyBinderTrace` contain no `let`;
  - `judgementsMap_rulesJ_twinPos`, `posSortLiftFor_twinPos`: judgement transport into
    `Decl.twinPosRulesJ`;
  - `recRulePlain_of_majorDom_eq`: `Expr.recRulePlain` agrees on two types whose `mI`-th domains
    share `getAppFn` and `getAppArgs`.
* **Reference safety and `InLogic` for inductive heads**:
  - `recRefs_of_familyCall`: `family_refs_ok` certifies `Claim.CoveredAt t lim x ∨ NeedOk E₀ x` at
    every used reference of `A`, for any limit `lim : Option Nat`;
  - `committedPrelude_inLogic`, `inLogic_of_covered_ind`: every covered inductive projection's
    block is `InLogic`, handling both `KeptIn` and `PinnedBasis` prelude rows.
* **Raw shape extraction**: `rec_to_parent_addr_rawTm_addr`, `last_binder_dom_rawTm`,
  `check_carriers_rawTm_familyKey`, and `check_rec_motive_not_forallE`.
* **Member extraction**: `ExtractedTwinMember` and `familyCall_extract_members` unpack `check_recs`
  at every member `k < rs'.size` of `A`, giving `RecReads`, `Reads`, `canonAnn`, `canonRules`,
  `ValStored`, `RuleStored`, `recNoSelf`, `motiveConcl`, `majorPins`, and a `ConstantValCheckJ`
  front-door factory at any environment storing the record's references. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core (KExpr KLevel KKey)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry loadedAt mutsRoot binderDomAfter peelForalls)
open Ix.Kernel (ConstantInfo ConstantVal RecRule Level LevelParam Expr)
open Ix.Kernel.Semantics (ConstantValCheckJ letFree)
open Ix.Cert.ReaderUnits (throw_ok)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

private theorem except_bind_ok_ce {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

private theorem heapExt_getElem? {h h' : Heap F} (ext : Heap.Extends h h') {i : Nat}
    {v : SourceValue F} (hget : h[i]? = some v) : h'[i]? = some v := by
  obtain ⟨s, rfl⟩ := ext
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hget).1]
  exact hget

/-! ## Pure algebraic bridges: `posOf`, `canonAnn`, `loadedAt`, `letFree`, `twinPosRulesJ` -/

private theorem subst_go_nodup_getElem_ce :
    ∀ {ks : List LevelParam} {vs : List KLevel},
      ks.Nodup → ∀ {i : Nat} (hi : i < ks.length) (hv : i < vs.length),
        Level.subst.go ks vs ks[i] = vs[i]
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, hv => absurd hv (Nat.not_lt_zero _)
  | _ :: _, _ :: _, _, 0, _, _ => by simp [Level.subst.go]
  | k :: ks, _ :: vs, hnd, i + 1, hi, hv => by
    obtain ⟨hk_not, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hv' : i < vs.length := Nat.lt_of_succ_lt_succ hv
    have hne : k ≠ ks[i] := fun h => hk_not (h ▸ List.getElem_mem hi')
    simp only [List.getElem_cons_succ, Level.subst.go, hne, ↓reduceIte]
    exact subst_go_nodup_getElem_ce hnd' hi' hv'

private theorem subst_go_not_mem_ce :
    ∀ (ks : List LevelParam) (vs : List KLevel) {q : LevelParam},
      q ∉ ks → Level.subst.go ks vs q = .param q
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, _ :: vs, q, hq => by
    have hne : k ≠ q := fun h => hq (by simp [h])
    simp only [Level.subst.go, hne, ↓reduceIte]
    exact subst_go_not_mem_ce ks vs fun hm => hq (List.mem_cons_of_mem _ hm)

/-- `Level.subst ps (Core.posLevels ps)` maps `Reader.convUniv (Reader.recParam ps) u` to
`Reader.convUniv id u` unconditionally for any permutation `ps` of `List.range ps.length`. -/
theorem convUniv_posOf_uncond {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) :
    ∀ (u : Ixon.Univ),
      Level.subst ps (Core.posLevels ps)
          (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u) =
        Ix.Kernel.Reader.convUniv id u
  | .zero => rfl
  | .succ u => congrArg Level.succ (convUniv_posOf_uncond hperm u)
  | .max a b => congrArg₂ Level.max (convUniv_posOf_uncond hperm a) (convUniv_posOf_uncond hperm b)
  | .imax a b =>
    congrArg₂ Level.imax (convUniv_posOf_uncond hperm a) (convUniv_posOf_uncond hperm b)
  | .var idx => by
    simp only [Ix.Kernel.Reader.convUniv, Level.subst]
    have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
    by_cases hlt : idx.toNat < ps.length
    · have hrec : Ix.Kernel.Reader.recParam ps idx.toNat = ps[idx.toNat] := by
        unfold Ix.Kernel.Reader.recParam List.getD
        rw [List.getElem?_eq_getElem hlt]; rfl
      have hplen : idx.toNat < (Core.posLevels ps).length := by simp [Core.posLevels, hlt]
      rw [hrec, subst_go_nodup_getElem_ce hnd hlt hplen]
      simp [Core.posLevels]
    · have hrec : Ix.Kernel.Reader.recParam ps idx.toNat = idx.toNat := by
        unfold Ix.Kernel.Reader.recParam List.getD
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)]; rfl
      have hnot : idx.toNat ∉ ps := fun hm =>
        hlt (List.mem_range.mp (hperm.mem_iff.mp hm))
      rw [hrec, subst_go_not_mem_ce ps (Core.posLevels ps) hnot]
      rfl

private theorem convExpr_posOf {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {tbl₁ tbl₂ : Array (Ix.Kernel.Reader.ReadM KExpr)}
    (htbl : ∀ (i : Nat) (v : KExpr), tbl₁[i]? = some (Except.ok v) →
      tbl₂[i]? = some (Except.ok (Core.posOf ps v))) :
    ∀ (e : Ixon.Expr) (v : KExpr),
      Ix.Kernel.Reader.convExpr (⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)), self⟩) tbl₁ e = .ok v →
      Ix.Kernel.Reader.convExpr (⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩) tbl₂ e =
        .ok (Core.posOf ps v) := by
  let ecx₁ : Ix.Kernel.Reader.ECx .anon :=
    ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)), self⟩
  let ecx₂ : Ix.Kernel.Reader.ECx .anon :=
    ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩
  have hlevel : ∀ (i : UInt64) (l : KLevel),
      ecx₁.level i = .ok l → ecx₂.level i = .ok (Level.subst ps (Core.posLevels ps) l) := by
    intro i l hl
    unfold Ix.Kernel.Reader.ECx.level at hl ⊢
    by_cases hi : i.toNat < src.univs.size
    · simp only [ecx₁, ecx₂, Array.getElem?_map, Array.getElem?_eq_getElem hi, Option.map_some,
        pure, Except.pure, Except.ok.injEq] at hl ⊢
      subst hl
      exact (convUniv_posOf_uncond hperm src.univs[i.toNat]).symm
    · simp only [ecx₁, ecx₂, Array.getElem?_map, Array.getElem?_eq_none (Nat.le_of_not_lt hi),
        Option.map_none] at hl
      exact (throw_ok hl).elim
  have hlevels : ∀ (us : List UInt64) (ls : List KLevel),
      us.mapM ecx₁.level = .ok ls →
      us.mapM ecx₂.level = .ok (ls.map (Level.subst ps (Core.posLevels ps))) := by
    intro us
    induction us with
    | nil =>
      intro ls h
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; rfl
    | cons u rest ih =>
      intro ls h
      simp only [List.mapM_cons] at h ⊢
      obtain ⟨l, hl, h⟩ := except_bind_ok_ce.mp h
      obtain ⟨ls', hls', h⟩ := except_bind_ok_ce.mp h
      rw [hlevel u l hl, ih ls' hls']
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; rfl
  intro e
  induction e with
  | sort i =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨l, hl, h⟩ := except_bind_ok_ce.mp h
    rw [hlevel i l hl]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | var i =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    simp [Ix.Kernel.Expr.mkBvar_eq, Core.posOf, Expr.instantiateLevelParams]
  | ref i us =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨k, hk, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨ls, hls, h⟩ := except_bind_ok_ce.mp h
    have hk' : ecx₂.keyAt i = .ok k := hk
    have hls' : ecx₂.levels us = .ok (ls.map (Level.subst ps (Core.posLevels ps))) :=
      hlevels us.toList ls hls
    rw [hk', hls']
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | recur i us =>
    intro v h
    cases hs : self i.toNat with
    | none =>
      simp only [Ix.Kernel.Reader.convExpr, hs] at h
      exact (throw_ok h).elim
    | some m =>
      simp only [Ix.Kernel.Reader.convExpr, hs] at h ⊢
      obtain ⟨k, hk, h⟩ := except_bind_ok_ce.mp h
      obtain ⟨ls, hls, h⟩ := except_bind_ok_ce.mp h
      have hls' : ecx₂.levels us = .ok (ls.map (Level.subst ps (Core.posLevels ps))) :=
        hlevels us.toList ls hls
      rw [hk, hls']
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; rfl
  | prj i field val ih =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨k, hk, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    have hk' : ecx₂.keyAt i = .ok k := hk
    rw [hk', ih x hx]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | str i =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨bs, hbs, h⟩ := except_bind_ok_ce.mp h
    have hbs' : ecx₂.blobAt i = .ok bs := hbs
    rw [hbs']
    simp only [bind, Except.bind] at h ⊢
    cases hutf : String.fromUTF8? bs with
    | none => simp only [hutf] at h; exact (throw_ok h).elim
    | some s =>
      simp only [hutf, pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; rfl
  | nat i =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨n, hn, h⟩ := except_bind_ok_ce.mp h
    have hn' : ecx₂.natAt i = .ok n := hn
    rw [hn']
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | app f a ihf iha =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    rw [ihf x hx, iha y hy]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | lam ty b iht ihb =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    rw [iht x hx, ihb y hy]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    simp [Core.posOf, Expr.instantiateLevelParams, Ix.Kernel.BinderMeta.leanNever, Level.substPW]
  | all ty b iht ihb =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    rw [iht x hx, ihb y hy]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    simp [Core.posOf, Expr.instantiateLevelParams, Ix.Kernel.BinderMeta.leanNever, Level.substPW]
  | letE nonDep mode ty val b iht ihv ihb =>
    intro v h
    simp only [Ix.Kernel.Reader.convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨z, hz, h⟩ := except_bind_ok_ce.mp h
    rw [iht x hx, ihv y hy, ihb z hz]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  | share i =>
    intro v h
    cases ht : tbl₁[i.toNat]? with
    | none =>
      simp only [Ix.Kernel.Reader.convExpr, ht] at h
      exact (throw_ok h).elim
    | some r =>
      simp only [Ix.Kernel.Reader.convExpr, ht] at h
      subst h
      simp only [Ix.Kernel.Reader.convExpr, htbl _ _ ht]

private theorem buildShareTblGo_posOf {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) :
    ∀ (es : List Ixon.Expr) (acc₁ acc₂ : Array (Ix.Kernel.Reader.ReadM KExpr)),
      acc₁.size = acc₂.size →
      (∀ (i : Nat) (v : KExpr), acc₁[i]? = some (Except.ok v) →
        acc₂[i]? = some (Except.ok (Core.posOf ps v))) →
      ∀ (i : Nat) (v : KExpr),
        (L1.buildShareTblGo ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)), self⟩
          acc₁ es)[i]? = some (Except.ok v) →
        (L1.buildShareTblGo ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩
          acc₂ es)[i]? = some (Except.ok (Core.posOf ps v))
  | [], _, _, _, hacc => hacc
  | e :: es, acc₁, acc₂, hsz, hacc => by
    simp only [L1.buildShareTblGo]
    apply buildShareTblGo_posOf hperm es _ _ (by simp [hsz])
    intro i v hi
    rw [Array.getElem?_push] at hi ⊢
    by_cases hsize : i = acc₁.size
    · rw [ite_eq_left hsize] at hi
      rw [ite_eq_left (hsize.trans hsz),
        convExpr_posOf hperm hacc e v (Option.some.inj hi)]
    · rw [ite_eq_right hsize] at hi
      rw [ite_eq_right (fun h => hsize (h.trans hsz.symm))]
      exact hacc i v hi

/-- **`Core.posOf ps` maps a reading under `recParam ps` to the positional reading under `id`.** -/
theorem exprReader_posOf {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {e : Ixon.Expr} {v : KExpr}
    (h : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok v) :
    (exprReader t blob src id self).read e = .ok (Core.posOf ps v) := by
  obtain ⟨hecx₁, htbl₁⟩ := L1.memberReader_mk'_eq (readCtx t blob) src (Ix.Kernel.Reader.recParam ps) self
  obtain ⟨hecx₂, htbl₂⟩ := L1.memberReader_mk'_eq (readCtx t blob) src id self
  unfold exprReader Ix.Kernel.Reader.MemberReader.read at h ⊢
  rw [hecx₁, htbl₁] at h
  rw [hecx₂, htbl₂]
  exact convExpr_posOf hperm
    (buildShareTblGo_posOf hperm src.sharing.toList #[] #[] rfl (fun _ _ hi => by simp at hi))
    e v h

private theorem applyBinderTrace_posOf {ps : List LevelParam}
    (hperm : ps.Perm (List.range ps.length)) :
    ∀ (E : KExpr) {plan rest : List KLevel} {E' : KExpr},
      L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) E plan = some (E', rest) →
      L1.applyBinderTrace (fun l => Core.bmeta l) (Core.posOf ps E) plan =
        some (Core.posOf ps E', rest) := by
  intro E
  induction E with
  | bvar i =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | fvar idx ty ih =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) ty plan with _ | ⟨ty1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hpos_fvar : Core.posOf ps (.fvar idx ty) = .fvar idx (Core.posOf ps ty) := rfl
      rw [hpos_fvar]
      simp only [L1.applyBinderTrace, bind, Option.bind]
      rw [ih h1]; rfl
  | sort u =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | const k us =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | lit l =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | app f a ihf iha =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) f plan with _ | ⟨f1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      rcases h2 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) a r1 with _ | ⟨a1, r2⟩
      · simp only [h2] at h; cases h
      · simp only [h2] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hpos_app : Core.posOf ps (.app f a) = .app (Core.posOf ps f) (Core.posOf ps a) := rfl
        rw [hpos_app]
        simp only [L1.applyBinderTrace, bind, Option.bind, ihf h1, iha h2]; rfl
  | lam d b m ihd ihb =>
    intro plan rest E' h
    cases plan with
    | nil => simp [L1.applyBinderTrace] at h
    | cons lv ls =>
      simp only [L1.applyBinderTrace, bind, Option.bind] at h
      rcases h1 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) d ls with _ | ⟨d1, r1⟩
      · simp only [h1] at h; cases h
      · simp only [h1] at h
        rcases h2 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) b r1 with _ | ⟨b1, r2⟩
        · simp only [h2] at h; cases h
        · simp only [h2] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hpos_lam : Core.posOf ps (.lam d b m) =
              .lam (Core.posOf ps d) (Core.posOf ps b)
                { m with pw := Level.substPW ps (Core.posLevels ps) m.pw } := rfl
          rw [hpos_lam]
          simp only [L1.applyBinderTrace, bind, Option.bind, ihd h1, ihb h2]
          simp only [pure, Option.some.injEq, Prod.mk.injEq, and_true]
          show Expr.lam (Core.posOf ps d1) (Core.posOf ps b1) (Core.bmeta lv) =
            Expr.lam (Core.posOf ps d1) (Core.posOf ps b1)
              { Core.bmeta (L1.invPosLevel ps lv) with
                  pw := Level.substPW ps (Core.posLevels ps) (Core.bmeta (L1.invPosLevel ps lv)).pw }
          congr 1
          exact (L1.substPW_posLevels_bmeta hperm lv).symm
  | forallE d b m ihd ihb =>
    intro plan rest E' h
    cases plan with
    | nil => simp [L1.applyBinderTrace] at h
    | cons lv ls =>
      simp only [L1.applyBinderTrace, bind, Option.bind] at h
      rcases h1 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) d ls with _ | ⟨d1, r1⟩
      · simp only [h1] at h; cases h
      · simp only [h1] at h
        rcases h2 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) b r1 with _ | ⟨b1, r2⟩
        · simp only [h2] at h; cases h
        · simp only [h2] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hpos_fa : Core.posOf ps (.forallE d b m) =
              .forallE (Core.posOf ps d) (Core.posOf ps b)
                { m with pw := Level.substPW ps (Core.posLevels ps) m.pw } := rfl
          rw [hpos_fa]
          simp only [L1.applyBinderTrace, bind, Option.bind, ihd h1, ihb h2]
          simp only [pure, Option.some.injEq, Prod.mk.injEq, and_true]
          show Expr.forallE (Core.posOf ps d1) (Core.posOf ps b1) (Core.bmeta lv) =
            Expr.forallE (Core.posOf ps d1) (Core.posOf ps b1)
              { Core.bmeta (L1.invPosLevel ps lv) with
                  pw := Level.substPW ps (Core.posLevels ps) (Core.bmeta (L1.invPosLevel ps lv)).pw }
          congr 1
          exact (L1.substPW_posLevels_bmeta hperm lv).symm
  | letE t v b l iht ihv ihb =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) t plan with _ | ⟨t1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      rcases h2 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) v r1 with _ | ⟨v1, r2⟩
      · simp only [h2] at h; cases h
      · simp only [h2] at h
        rcases h3 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) b r2 with _ | ⟨b1, r3⟩
        · simp only [h3] at h; cases h
        · simp only [h3] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hpos_let : Core.posOf ps (.letE t v b l) =
              .letE (Core.posOf ps t) (Core.posOf ps v) (Core.posOf ps b) l := rfl
          rw [hpos_let]
          simp only [L1.applyBinderTrace, bind, Option.bind, iht h1, ihv h2, ihb h3]
          simp only [pure, Option.some.injEq, Prod.mk.injEq, and_true]
          exact (Core.ProjBody.instantiate1Lift_instantiateLevelParams ps (Core.posLevels ps) v1 b1 0).symm
  | proj s i e ih =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace (fun l => Core.bmeta (L1.invPosLevel ps l)) e plan with _ | ⟨e1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hpos_proj : Core.posOf ps (.proj s i e) = .proj s i (Core.posOf ps e) := rfl
      rw [hpos_proj]
      simp only [L1.applyBinderTrace, bind, Option.bind]
      rw [ih h1]; rfl

/-- **Pure algebraic `posOf`/`canonAnn`/`loadedAt` bridge**: for any permutation `ps` of
`0 .. ps.length - 1`, `Core.posOf ps` takes `canonAnn src ps root e E_rd` directly to
`loadedAt t blob src self ps.length root e`. -/
theorem posOf_canonAnn_eq_loadedAt {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {root : F} {e : Ixon.Expr} {E_rd E' : KExpr}
    (hread : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok E_rd)
    (hcan : LoadedReads.canonAnn src ps root e E_rd = some E') :
    loadedAt t blob src self ps.length root e = some (Core.posOf ps E') := by
  unfold LoadedReads.canonAnn at hcan
  cases hp : L1.binderRootPlan (LoadedReads.canonTree src.binders.toList) src.sharing.toList root e with
  | none => rw [hp] at hcan; cases hcan
  | some plan =>
    rw [hp] at hcan
    simp only [Option.bind_some, Option.map_eq_some_iff] at hcan
    obtain ⟨⟨E1, rest⟩, hap, rfl⟩ := hcan
    have hpos := exprReader_posOf hperm hread
    have hap' := applyBinderTrace_posOf hperm E_rd hap
    unfold loadedAt
    rw [hpos]
    simp only [Except.toOption, LoadedReads.canonAnn, hp, Option.bind_some]
    have hinv : (fun l => Core.bmeta (L1.invPosLevel (List.range ps.length) l)) =
        (fun l => Core.bmeta l) := by
      funext l; rw [L1.invPosLevel_range]
    rw [hinv, hap']
    rfl

/-- Uniqueness corollary: if both `canonAnn` and `loadedAt` hold, then `Core.posOf ps E' = E_loaded`. -/
theorem posOf_eq_of_canonAnn_loadedAt {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {root : F} {e : Ixon.Expr} {E_rd E' E_loaded : KExpr}
    (hread : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok E_rd)
    (hcan : LoadedReads.canonAnn src ps root e E_rd = some E')
    (hld : loadedAt t blob src self ps.length root e = some E_loaded) :
    Core.posOf ps E' = E_loaded :=
  Option.some.inj ((posOf_canonAnn_eq_loadedAt hperm hread hcan).symm.trans hld)

private theorem letFree_instantiate1Lift {v : KExpr} (hv : letFree v = true) :
    ∀ (b : KExpr) (d : Nat), letFree b = true → letFree (b.instantiate1Lift v d) = true
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · exact Decl.letFree_liftLooseBVars d 0 hv
    · split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, d, h => by
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, letFree, Bool.and_eq_true]
    exact ⟨letFree_instantiate1Lift hv f d h.1, letFree_instantiate1Lift hv a d h.2⟩
  | .lam t b m, d, h => by
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, letFree, Bool.and_eq_true]
    exact ⟨letFree_instantiate1Lift hv t d h.1, letFree_instantiate1Lift hv b (d + 1) h.2⟩
  | .forallE t b m, d, h => by
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, letFree, Bool.and_eq_true]
    exact ⟨letFree_instantiate1Lift hv t d h.1, letFree_instantiate1Lift hv b (d + 1) h.2⟩
  | .letE _ _ _ _, _, h => by simp [letFree] at h
  | .proj _ _ e, d, h => by
    simp only [letFree] at h
    simp only [Expr.instantiate1Lift, letFree]
    exact letFree_instantiate1Lift hv e d h

/-- `L1.applyBinderTrace` eliminates every `let` node. -/
theorem letFree_of_applyBinderTrace {md : KLevel → Ix.Kernel.BinderMeta} :
    ∀ (E : KExpr) {plan rest : List KLevel} {E' : KExpr},
      L1.applyBinderTrace md E plan = some (E', rest) → letFree E' = true := by
  intro E
  induction E with
  | bvar _ | sort _ | const _ _ | lit _ =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | fvar _ ty _ =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace md ty plan with _ | ⟨ty1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); rfl
  | app f a ihf iha =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace md f plan with _ | ⟨f1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      rcases h2 : L1.applyBinderTrace md a r1 with _ | ⟨a1, r2⟩
      · simp only [h2] at h; cases h
      · simp only [h2] at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        simp only [letFree, Bool.and_eq_true]
        exact ⟨ihf h1, iha h2⟩
  | lam d b _ ihd ihb =>
    intro plan rest E' h
    cases plan with
    | nil => simp [L1.applyBinderTrace] at h
    | cons lv ls =>
      simp only [L1.applyBinderTrace, bind, Option.bind] at h
      rcases h1 : L1.applyBinderTrace md d ls with _ | ⟨d1, r1⟩
      · simp only [h1] at h; cases h
      · simp only [h1] at h
        rcases h2 : L1.applyBinderTrace md b r1 with _ | ⟨b1, r2⟩
        · simp only [h2] at h; cases h
        · simp only [h2] at h
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
          simp only [letFree, Bool.and_eq_true]
          exact ⟨ihd h1, ihb h2⟩
  | forallE d b _ ihd ihb =>
    intro plan rest E' h
    cases plan with
    | nil => simp [L1.applyBinderTrace] at h
    | cons lv ls =>
      simp only [L1.applyBinderTrace, bind, Option.bind] at h
      rcases h1 : L1.applyBinderTrace md d ls with _ | ⟨d1, r1⟩
      · simp only [h1] at h; cases h
      · simp only [h1] at h
        rcases h2 : L1.applyBinderTrace md b r1 with _ | ⟨b1, r2⟩
        · simp only [h2] at h; cases h
        · simp only [h2] at h
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
          simp only [letFree, Bool.and_eq_true]
          exact ⟨ihd h1, ihb h2⟩
  | letE t v b _ _ ihv ihb =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace md t plan with _ | ⟨t1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      rcases h2 : L1.applyBinderTrace md v r1 with _ | ⟨v1, r2⟩
      · simp only [h2] at h; cases h
      · simp only [h2] at h
        rcases h3 : L1.applyBinderTrace md b r2 with _ | ⟨b1, r3⟩
        · simp only [h3] at h; cases h
        · simp only [h3] at h
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
          exact letFree_instantiate1Lift (ihv h2) b1 0 (ihb h3)
  | proj _ _ e ih =>
    intro plan rest E' h
    simp only [L1.applyBinderTrace, bind, Option.bind] at h
    rcases h1 : L1.applyBinderTrace md e plan with _ | ⟨e1, r1⟩
    · simp only [h1] at h; cases h
    · simp only [h1] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [letFree]
      exact ih h1

/-- Every canonical annotation is `let`-free. -/
theorem letFree_of_canonAnn {src : Ixon.Constant} {ps : List LevelParam} {root : F}
    {e : Ixon.Expr} {E_rd E' : KExpr}
    (h : LoadedReads.canonAnn src ps root e E_rd = some E') : letFree E' = true := by
  unfold LoadedReads.canonAnn at h
  cases hp : L1.binderRootPlan (LoadedReads.canonTree src.binders.toList) src.sharing.toList root e with
  | none => rw [hp] at h; cases h
  | some plan =>
    rw [hp] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨⟨E1, rest⟩, hap, rfl⟩ := h
    exact letFree_of_applyBinderTrace E_rd hap

/-- Every `loadedAt` term is `let`-free. -/
theorem letFree_of_loadedAt {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {nl : Nat} {root : F} {e : Ixon.Expr} {E' : KExpr}
    (h : loadedAt t blob src self nl root e = some E') : letFree E' = true := by
  unfold loadedAt at h
  cases hr : ((exprReader t blob src id self).read e).toOption with
  | none => rw [hr] at h; cases h
  | some e₀ =>
    rw [hr] at h
    exact letFree_of_canonAnn h

private theorem convExpr_hasFvar_false {ecx : Ix.Kernel.Reader.ECx .anon}
    {tbl : Array (Ix.Kernel.Reader.ReadM KExpr)}
    (htbl : ∀ (i : Nat) (v : KExpr), tbl[i]? = some (Except.ok v) → v.hasFvar = false) :
    ∀ (e : Ixon.Expr) (v : KExpr),
      Ix.Kernel.Reader.convExpr ecx tbl e = .ok v → v.hasFvar = false := by
  intro e
  induction e with
  | sort _ =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | var _ =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [Ix.Kernel.Expr.mkBvar_eq, Expr.hasFvar]
  | ref _ _ =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | recur i _ =>
    intro v h
    cases hs : ecx.self i.toNat with
    | none => simp only [Ix.Kernel.Reader.convExpr, hs] at h; exact (throw_ok h).elim
    | some m =>
      simp only [Ix.Kernel.Reader.convExpr, hs] at h
      obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
      obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | prj _ _ _ ih =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ih x hx
  | str _ =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨bs, _, h⟩ := except_bind_ok_ce.mp h
    cases hu : String.fromUTF8? bs with
    | none => simp only [hu] at h; exact (throw_ok h).elim
    | some s =>
      simp only [hu, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | nat _ =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨_, _, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | app _ _ ihf iha =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    simp [Expr.hasFvar, ihf x hx, iha y hy]
  | lam _ _ iht ihb | all _ _ iht ihb =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    simp [Expr.hasFvar, iht x hx, ihb y hy]
  | letE _ _ _ _ _ iht ihv ihb =>
    intro v h; simp only [Ix.Kernel.Reader.convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok_ce.mp h
    obtain ⟨z, hz, h⟩ := except_bind_ok_ce.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    simp [Expr.hasFvar, iht x hx, ihv y hy, ihb z hz]
  | share i =>
    intro v h
    cases ht : tbl[i.toNat]? with
    | none => simp only [Ix.Kernel.Reader.convExpr, ht] at h; exact (throw_ok h).elim
    | some r => simp only [Ix.Kernel.Reader.convExpr, ht] at h; subst h; exact htbl _ _ ht

private theorem buildShareTblGo_hasFvar_false {ecx : Ix.Kernel.Reader.ECx .anon} :
    ∀ (es : List Ixon.Expr) (acc : Array (Ix.Kernel.Reader.ReadM KExpr)),
      (∀ (i : Nat) (v : KExpr), acc[i]? = some (Except.ok v) → v.hasFvar = false) →
      ∀ (i : Nat) (v : KExpr), (L1.buildShareTblGo ecx acc es)[i]? = some (Except.ok v) → v.hasFvar = false
  | [], _, hacc => hacc
  | e :: es, acc, hacc => by
    simp only [L1.buildShareTblGo]
    apply buildShareTblGo_hasFvar_false es
    intro i v hi
    rw [Array.getElem?_push] at hi
    by_cases hsize : i = acc.size
    · rw [ite_eq_left hsize] at hi
      exact convExpr_hasFvar_false hacc e v (Option.some.inj hi)
    · rw [ite_eq_right hsize] at hi
      exact hacc i v hi

/-- Every expression read by `exprReader` has no free variables. -/
theorem exprReader_hasFvar_false {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {param : Nat → LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {e : Ixon.Expr} {v : KExpr}
    (h : (exprReader t blob src param self).read e = .ok v) : v.hasFvar = false := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq (readCtx t blob) src param self
  unfold exprReader Ix.Kernel.Reader.MemberReader.read at h
  rw [hecx, htbl] at h
  exact convExpr_hasFvar_false
    (buildShareTblGo_hasFvar_false src.sharing.toList #[] fun _ _ hi => by simp at hi) e v h

/-- Judgement map lifting `Ix.Kernel.Model.rulesJ` into `Decl.twinPosRulesJ`. -/
theorem judgementsMap_rulesJ_twinPos :
    Decl.JudgementsMap (Ix.Kernel.Model.rulesJ (md := .anon)) twinPosRulesJ where
  annot h := h
  infer h := Decl.rulesJ_infer_to_twinPos h
  defeq h := Decl.rulesJ_defeq_to_twinPos h
  sort h := Decl.rulesJ_sort_to_twinPos h
  isZero h := h

/-- Positional sort-lifting into `Decl.twinPosRulesJ` for any permutation level-parameter list. -/
theorem posSortLiftFor_twinPos {env : Ix.Kernel.Env .anon} {cv' : ConstantVal .anon}
    (hperm : cv'.levelParams.Perm (List.range cv'.levelParams.length)) :
    Decl.PosSortLiftFor twinPosRulesJ env cv' :=
  fun sty₀ u₀ hinf hred =>
    ⟨Decl.TwinPos.invPosOf cv'.levelParams sty₀, Decl.TwinPos.invPosLevel cv'.levelParams u₀,
      Decl.twinPosRulesJ_infer_of_pos hperm hinf, Decl.twinPosRulesJ_sort_of_pos hperm hred⟩

/-- `Expr.recRulePlain` depends only on the `mI`-th binder domain's `getAppFn` and `getAppArgs`. -/
theorem recRulePlain_of_majorDom_eq {tyW tyC dW dC bW bC : KExpr}
    {preW preC : List (KExpr × Ix.Kernel.BinderMeta)} {mW mC : Ix.Kernel.BinderMeta}
    {mI rP cnP : Nat} {cjLps : List LevelParam}
    (hW : tyW.stripPis mI = some (preW, .forallE dW bW mW))
    (hC : tyC.stripPis mI = some (preC, .forallE dC bC mC))
    (hfn : dW.getAppFn = dC.getAppFn) (hargs : dW.getAppArgs = dC.getAppArgs) :
    Expr.recRulePlain tyW mI rP cnP cjLps = Expr.recRulePlain tyC mI rP cnP cjLps := by
  simp only [Expr.recRulePlain, hW, hC, hfn, hargs]

/-! ## Reference safety and `InLogic` for inductive heads -/

private def inLogicMutBool : Ixon.MutConst → Bool
  | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
  | .indc i => !i.isUnsafe && i.ctors.toList.all (fun ct => !ct.isUnsafe)
  | .recr r => !r.isUnsafe

private def inLogicBool (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
  | .recr r => !r.isUnsafe
  | .axio a => !a.isUnsafe
  | .muts ms => ms.toList.all inLogicMutBool
  | _ => true

private theorem inLogicMut_of_bool : ∀ {m : Ixon.MutConst}, inLogicMutBool m = true → InLogicMut m
  | .defn d, h => by simpa [inLogicMutBool, InLogicMut] using h
  | .indc i, h => by
    simp only [inLogicMutBool, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact ⟨h.1, fun ct hct => by simpa using h.2 ct hct⟩
  | .recr r, h => by simpa [inLogicMutBool, InLogicMut] using h

private theorem inLogic_of_bool {c : Ixon.Constant} (h : inLogicBool c = true) : InLogic c := by
  unfold inLogicBool at h
  unfold InLogic
  cases hc : c.info with
  | defn d => rw [hc] at h; simpa using h
  | recr r => rw [hc] at h; simpa using h
  | axio a => rw [hc] at h; simpa using h
  | quot _ => trivial
  | cPrj _ | rPrj _ | iPrj _ | dPrj _ => trivial
  | muts ms =>
    rw [hc] at h
    intro m hm
    exact inLogicMut_of_bool (List.all_eq_true.mp h m hm)

private theorem committedPrelude_inLogic_bool :
    RoleVal.committedPreludeList.all (fun e => inLogicBool e.2) = true := by
  decide +kernel

/-- Every committed prelude record is in Lean's logic. -/
theorem committedPrelude_inLogic :
    ∀ e ∈ RoleVal.committedPreludeList, InLogic e.2 :=
  fun e he => inLogic_of_bool (List.all_eq_true.mp committedPrelude_inLogic_bool e he)

private theorem pinnedBasis_role_mem_prelude_bool :
    ([Ix.Kernel.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK, .quotK] : List Ix.Kernel.BasisKind).all
      (fun kind => (kind.declsA : List (ConstantInfo .anon)).all fun ci =>
        match ci.name with
        | .role r => preludeRoles.contains r
        | _ => true) = true := by
  decide +kernel

private theorem pinnedBasis_role_mem_prelude {ci : ConstantInfo .anon} {r : Ix.Kernel.Role}
    (hp : PinnedBasis ci) (hn : ci.name = .role r) : r ∈ preludeRoles := by
  obtain ⟨kind, hmem⟩ := hp
  have hkind : kind ∈ ([Ix.Kernel.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK, .quotK] :
      List Ix.Kernel.BasisKind) := by
    cases kind <;> simp
  have hall := List.all_eq_true.mp pinnedBasis_role_mem_prelude_bool kind hkind
  have hci := List.all_eq_true.mp hall ci hmem
  rw [hn] at hci
  exact List.contains_iff_mem.mp hci

/-- **Every covered inductive projection's block is `InLogic`**: covers both `KeptIn` (from `R`'s
reading) and `PinnedBasis` (from `RecordsFor R E` + `committedPrelude_inLogic`). -/
theorem inLogic_of_covered_ind {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {G : Nat → Prop} {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {a Bm : _root_.Address} {c cBm : Ixon.Constant} {p : Ixon.InductiveProj}
    (ht : t.check = .ok ()) (hShape : TableShape.{u} t G R envT)
    (hRF : RecordsFor R E) (hSS : StepStore calls t E₀ E)
    (hLim : LimWithin G t lim)
    (hc : recordOf E₀ a = some c) (hinfo : c.info = .iPrj p) (hBm : p.block = Bm)
    (hcBm : recordOf E₀ Bm = some cBm)
    (hcov : Claim.CoveredAt t lim a) : InLogic cBm := by
  obtain ⟨r, hr_addr, hr_walk, hr_lt⟩ := hcov
  have hGr : G (Ix.SpecDigest.groupOf r) :=
    hLim r (by simp [hr_addr]) hr_lt
  have hkept : keptRole r := Or.inl (Or.inl hr_walk)
  obtain ⟨ci, hci_find, hpin | hkeptIn⟩ :=
    hShape.kept (Ix.SpecDigest.groupOf r) r a hGr (role_mem_roleGroup r) hkept hr_addr
  · have hname : ci.name = .role r := Core.WhnfAux.name_of_find hci_find
    have hprel : r ∈ preludeRoles := pinnedBasis_role_mem_prelude hpin hname
    obtain ⟨a', bytes, ha', hrow⟩ := ClosedFacts.preludePinned_rows hShape.prelude r hprel
    have haa : a' = a := Option.some.inj (ha'.symm.trans hr_addr)
    subst a'
    rw [StoreInhabit.committedRows_eq] at hrow
    obtain ⟨e, he, hpe⟩ := List.mem_map.mp hrow
    have he1 : e.1 = a := congrArg Prod.fst hpe
    have hrow_e : (e.1, Ixon.serConstant e.2) ∈ committedRows := by
      rw [StoreInhabit.committedRows_eq]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨lc, hlc, hraw⟩ := hRF.2.2.2 _ hrow_e
    obtain ⟨ce, hlce, hexe⟩ := hRF.1 e.1 lc hlc
    rw [hraw, (ClosedFacts.committedPrelude_rows e he).2] at hexe
    have hce_eq : ce = e.2 := (Except.ok.inj hexe).symm
    subst hce_eq
    have hrecE_e : Ix.Cert.recordAt E e.1 = some e.2 := by
      unfold Ix.Cert.recordAt
      rw [hlc]
      exact hlce
    have hrecE_a : Ix.Cert.recordAt E a = some c := hSS.runRecord a c hc
    rw [he1] at hrecE_e
    have hec : e.2 = c := Option.some.inj (hrecE_e.symm.trans hrecE_a)
    obtain ⟨q, hq, hq1⟩ := ClosedFacts.committedPrelude_owner e he
    have hown : Ix.Cert.ownerOf e.1 e.2 = Bm := by
      rw [he1, hec]; simp [Ix.Cert.ownerOf, hinfo, hBm]
    have hqBm : q.1 = Bm := hq1.trans hown
    have hrow_q : (q.1, Ixon.serConstant q.2) ∈ committedRows := by
      rw [StoreInhabit.committedRows_eq]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨lcq, hlcq, hrawq⟩ := hRF.2.2.2 _ hrow_q
    obtain ⟨cq, hlcq', hexq⟩ := hRF.1 q.1 lcq hlcq
    rw [hrawq, (ClosedFacts.committedPrelude_rows q hq).2] at hexq
    have hcq_eq : cq = q.2 := (Except.ok.inj hexq).symm
    subst hcq_eq
    have hrecE_q : Ix.Cert.recordAt E q.1 = some q.2 := by
      unfold Ix.Cert.recordAt
      rw [hlcq]
      exact hlcq'
    have hrecE_Bm : Ix.Cert.recordAt E Bm = some cBm := hSS.runRecord Bm cBm hcBm
    rw [hqBm] at hrecE_q
    have hqc : q.2 = cBm := Option.some.inj (hrecE_q.symm.trans hrecE_Bm)
    rw [← hqc]
    exact committedPrelude_inLogic q hq
  · obtain ⟨-, ci₀, hrd, -⟩ := hkeptIn
    obtain ⟨ca, hcaR, hca_rd⟩ := hrd
    have hcaE : Ix.Cert.recordAt E a = some ca := hRF.2.1 a ca hcaR
    have hca0 : Ix.Cert.recordAt E a = some c := hSS.runRecord a c hc
    have hca_eq : ca = c := Option.some.inj (hcaE.symm.trans hca0)
    subst hca_eq
    rw [hinfo] at hca_rd
    obtain ⟨cbR, msR, indR, hMA, -⟩ := hca_rd
    obtain ⟨hcbR, -, -, -, -, hlogR⟩ := hMA
    rw [hBm] at hcbR
    have hcbE : Ix.Cert.recordAt E Bm = some cbR := hRF.2.1 Bm cbR hcbR
    have hcb0 : Ix.Cert.recordAt E Bm = some cBm := hSS.runRecord Bm cBm hcBm
    have hcb_eq : cbR = cBm := Option.some.inj (hcbE.symm.trans hcb0)
    rwa [← hcb_eq]

private theorem refs_size_lt_of_exact_ce {bytes : ByteArray} {c : Ixon.Constant}
    (hsz : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by dsimp [Ixon.Constant.resourceSize]; omega
  omega

/-- **`KernelModeled::family_refs_ok` certifies `CoveredAt t lim x ∨ NeedOk E₀ x`** at every used
reference of the family record `A`, for ANY limit `lim : Option Nat`. -/
theorem recRefs_of_familyCall {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B A : _root_.Address} {c : Ixon.Constant}
    {lim : Option Nat} {cs : List (Call F)}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hc : recordOf E₀ A = some c)
    (hcall : FamilyCallAtLim calls bAddr t B A lim cs) :
    ∀ x, UsedRef E₀ A x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev_fam, -, hsub_fam⟩ := hcall
  match Obs.«KernelModeled::check_family».obs ev_fam with
  | .run (m105 := m105) (m_yarikpkl := m_fro) (cs1303 := cs_fro)
      (sg112 := sg112) (ev126 := e1) (ev148 := e2) (ev194 := e3) (ev_yqjbwijz := e4)
      (ev231 := e5) (ev266 := e6) (ev309 := e7) (ev344 := e8) (ev403 := e9) (ev435 := e10)
      (ev465 := e11) (ev513 := e12) (ev601 := e13) (ev634 := e14) (ev664 := e15) (ev686 := e16)
      (ev716 := e17) (ev759 := e18) (ev817 := e19) (ev796 := e20) (ev852 := e21)
      (ev_ursqbimm := e22) (ev_srfmazjk := e23) (ev874 := e24) (ev896 := e25) (ev960 := e26)
      (ev939 := e27) (ev1011 := e28) (ev990 := e29) (ev_edyzsqzv := e30) (ev_gkddqxhv := e31)
      (ev_ittpynob := e32) (ev_biaifgpd := e33) (ev1203 := e34) (ev_cwwgzxtj := e35)
      (ev1246 := e36) (ev_mitevvsv := e37) (ev_rqpeovbn := e38) (ev_xrhmaojz := e39)
      (ev_whimdwjd := e40) (ev1305 := ev_fro) (hc1474 := hcs) .. =>
    have hsg : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := e0) (he33 := hh) .. => rw [hh]; exact e0.heap_extends
      | .Node (heq97 := h01) .. => exact absurd (Value.field.inj h01).symm one_ne_zero
    have ext_fro : Heap.Extends h m_fro :=
      hsg.trans (e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
      (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
      (e7.heap_extends.trans (e8.heap_extends.trans (e9.heap_extends.trans
      (e10.heap_extends.trans (e11.heap_extends.trans (e12.heap_extends.trans
      (e13.heap_extends.trans (e14.heap_extends.trans (e15.heap_extends.trans
      (e16.heap_extends.trans (e17.heap_extends.trans (e18.heap_extends.trans
      (e19.heap_extends.trans (e20.heap_extends.trans (e21.heap_extends.trans
      (e22.heap_extends.trans (e23.heap_extends.trans (e24.heap_extends.trans
      (e25.heap_extends.trans (e26.heap_extends.trans (e27.heap_extends.trans
      (e28.heap_extends.trans (e29.heap_extends.trans (e30.heap_extends.trans
      (e31.heap_extends.trans (e32.heap_extends.trans (e33.heap_extends.trans
      (e34.heap_extends.trans (e35.heap_extends.trans (e36.heap_extends.trans
      (e37.heap_extends.trans (e38.heap_extends.trans (e39.heap_extends.trans
      e40.heap_extends)))))))))))))))))))))))))))))))))))))))
    have hsub_fro : ∀ cl ∈ cs_fro, cl ∈ calls :=
      fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
    match Obs.«KernelModeled::family_refs_ok».obs ev_fro with
    | .run (cs12 := cs12) (cs_zlhtmzlz := csSafe) (ev14 := ev14) (ev36 := ev36)
        (ev_ycrqbsja := ev_i1) (ev_nhomjxfq := ev_i2) (ev_kfwmaaqi := ev_go)
        (ev_ozxzdina := ev_i3) (ev_tnqzszcy := ev_safe) (hc222 := hcf) .. =>
      have hsub12 : ∀ cl ∈ cs12, cl ∈ calls :=
        fun cl hcl => hsub_fro cl (by rw [hcf]; simp [hcl])
      have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls :=
        fun cl hcl => hsub_fro cl (by rw [hcf]; simp [hcl])
      obtain ⟨ext14, rawBytes, c', hsz, hh, haddr, -, he, hcRep, -⟩ :=
        Claim.load_verified_constant_de (Core.S0.addr_mono ext_fro hxrb) ev14
      have hcc : c' = c :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub12 hh)
          haddr he
      subst c'
      have ext_after : Heap.Extends _ _ :=
        ev36.heap_extends.trans (ev_i1.heap_extends.trans (ev_i2.heap_extends.trans ev_go.heap_extends))
      have hcRep' := hcRep.mono ext_after
      obtain ⟨extIdx, hidx⟩ := Claim.const_idxs_of_spec hcRep' ev_i3
      obtain ⟨_, _, rp, _, _, heq, -, -, hrf, -, -⟩ := hcRep'
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at heq
      rcases heq with ⟨_, _, hrp, _, _⟩
      subst hrp
      have hrp := repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ extIdx hrf
      have hrc_safe := hrc.mono (ext_fro.trans (ext14.trans (ext_after.trans extIdx)))
      match Obs.«KernelModeled::assert_inner_refs_safe».obs ev_safe with
      | .run (cs_svbeyhut := csS) (cs_xuynpgdd := csNb)
          (ev_mxwoukvn := evS) (ev_hemnmxwe := evNb) (hc_sgljalbe := hcsS) .. =>
        have hsubS : ∀ cl ∈ csS, cl ∈ calls := fun cl hcl => hsubSafe cl (by rw [hcsS]; simp [hcl])
        have hsubNb : ∀ cl ∈ csNb, cl ∈ calls := fun cl hcl => hsubSafe cl (by rw [hcsS]; simp [hcl])
        have hsz_refs : 0 + c.refs.toList.length < 8589934592 := by
          simpa only [Nat.zero_add, Array.length_toList] using refs_size_lt_of_exact_ce hsz he
        have hfull := Claim.assert_safe_used_refs_full_spec hS c.refs.toList 0 hsz_refs
          hrc_safe hrp hidx evS hsubS
        have hnb := assert_used_not_block_spec hS hH c.refs.toList 0 hsz_refs
          (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ evS.heap_extends hrp)
          (repList_heapMono₂ _ Claim.repBoundedIdx_heapMono₂ evS.heap_extends hidx) evNb hsubNb
        intro x hu
        obtain ⟨c₀, i, hc₀, hi, hget⟩ := hu
        have heq0 : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
        subst c₀
        have hi' : 0 + i ∈ Core.S0.usedRefIdxs c := by
          simpa only [Nat.zero_add, Assembly.usedRefIdxs_eq] using hi
        have hgetL : c.refs.toList[i]? = some x := by simpa only [Array.getElem?_toList] using hget
        obtain ⟨hiLt, hval⟩ := List.getElem?_eq_some_iff.mp hgetL
        obtain ⟨-, hSafe⟩ := hfull i hiLt hi'
        rw [hval] at hSafe
        by_cases hcov : Claim.CoveredAt t lim x
        · exact Or.inl hcov
        · obtain ⟨cx, hcx, hnotb⟩ := by simpa only [hval] using hnb i hiLt hi'
          obtain ⟨hlog, hown⟩ := hSafe hcov cx hcx
          exact Or.inr ⟨cx, hcx, hnotb, hlog, hown⟩

/-! ## `level_is_not_zero` bit output and `block_nparams` -/

private theorem level_is_not_zero_bit_aux :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Core.W fname args h r h' cs → fname = "KernelLevels::level_is_not_zero" →
      r = .field 0 ∨ r = .field 1 :=
  ObsFn.strong_induction (world := Core.W)
    (fun fname _ _ r _ _ => fname = "KernelLevels::level_is_not_zero" → r = .field 0 ∨ r = .field 1)
    (fun fname args h r h' cs ev ih hfn => by
      subst hfn
      have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelLevels.level_is_not_zero.lookup
        (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl]) ev
      simp only [IxVM.KernelLevels.level_is_not_zero] at d0
      obtain ⟨_, _, _, _, _, _, _, sel, dArm, rfl⟩ := d0.matchValue_inv
      rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
      · obtain ⟨rfl, -, -⟩ := dArm.literal_inv; exact Or.inl rfl
      · rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
        · obtain ⟨rfl, -, -⟩ := dArm.literal_inv; exact Or.inl rfl
        · rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
          · obtain ⟨rfl, -, -⟩ := dArm.literal_inv; exact Or.inr rfl
          · rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
            · obtain ⟨_, _, _, _, _, _, _, sel2, dArm2, -⟩ := dArm.matchValue_inv
              rcases selectArm_cons_inv sel2 with ⟨_, rfl⟩ | ⟨_, sel2⟩
              · obtain ⟨rfl, -, -⟩ := dArm2.literal_inv; exact Or.inl rfl
              · rcases selectArm_cons_inv sel2 with ⟨_, rfl⟩ | ⟨_, sel2⟩
                · obtain ⟨rfl, -, -⟩ := dArm2.literal_inv; exact Or.inr rfl
                · exact (selectArm_nil_inv sel2).elim
            · rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
              · obtain ⟨_, _, _, cs', a', ev', hc'⟩ := dArm.call_inv
                rw [instanceName_plain_some] at ev'
                obtain ⟨_, _, _, _, _, rfl, dv, a'', hc_a⟩ := a'.cons_inv
                obtain ⟨_, rfl, hc_v⟩ := dv.var_inv
                obtain ⟨rfl, rfl, hc_n⟩ := a''.nil_inv
                subst hc_v hc_n hc_a hc'
                exact ih _ _ _ _ _ _ (by simp only [List.length_append, List.length_cons]; omega) ev' rfl
              · exact (selectArm_nil_inv sel).elim)

/-- `KernelLevels::level_is_not_zero` always returns `.field 0` or `.field 1`. -/
theorem level_is_not_zero_bit {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Core.W "KernelLevels::level_is_not_zero" [p] h r h' cs) :
    r = .field 0 ∨ r = .field 1 :=
  level_is_not_zero_bit_aux _ _ _ _ _ _ ev rfl

/-! ## Raw shape helpers: `rec_to_parent_addr`, `last_binder_dom`, `check_carriers`, `check_rec_motive` -/

private theorem getAppFn_mkAppN_ce : ∀ (As : List KExpr) (f : KExpr),
    (Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => getAppFn_mkAppN_ce As (.app f a)

private theorem rawTm_const_of_load_addr {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} {k : Nat} {R E : KExpr} {pe ap lsp : SourceValue F}
    (rep : Decl.RawTm κ d Γ h k R E pe)
    (ld : loadValue h pe = .ok (.construct Core.kexprEnum "Const" [ap, lsp])) :
    ∃ a us, R = .const (κ (Core.ixAddr a)) us ∧ Bytes.RepAddressRef Core.addrTy h a ap := by
  cases rep with
  | const cell ra rls eq =>
    obtain ⟨_, hxs⟩ := Core.load_cell cell ld
    injection hxs with h1 _
    subst h1
    exact ⟨_, _, rfl, ra⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (Core.load_cell_ne cell ld (by decide)).elim

/-- Companion to `rec_to_parent_addr_rawTm_major` that also returns `Bytes.RepAddressRef` for the
returned parent address pointer `r`. -/
theorem rec_to_parent_addr_rawTm_addr {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {R E : KExpr} {x_ty r : SourceValue F} {p m mi i : F}
    {h h' : Heap F} {calls : List (Call F)}
    (hR : Decl.RawTm κ d Γ h 0 R E x_ty)
    (ev : ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field p, .field m, .field mi, .field i] h r h' calls) :
    ∃ (rbs : List (KExpr × Ix.Kernel.BinderMeta)) (Rd Rb : KExpr)
      (mR : Ix.Kernel.BinderMeta) (a : Bytes.Address) (us : List KLevel),
      R.stripPis (ZMod.val (p + m + mi + i)) = some (rbs, .forallE Rd Rb mR) ∧
      Rd.getAppFn = .const (κ (Core.ixAddr a)) us ∧
      Bytes.RepAddressRef Core.addrTy h' a r := by
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, hr, hh, -⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  have hx17 : x17 = .field (p + m) := by simp only [evalBinOp, Except.ok.injEq] at op32; exact op32.symm
  subst hx17
  have hx9 : x9 = .field (p + m + mi) := by simp only [evalBinOp, Except.ok.injEq] at op24; exact op24.symm
  subst hx9
  have hv1 : v1 = .field (p + m + mi + i) := by simp only [evalBinOp, Except.ok.injEq] at op16; exact op16.symm
  subst hv1
  obtain ⟨hheap, rbs, rbody, ebody, hstrip, hbody⟩ :=
    peel_n_foralls_rawTm_val (ZMod.val (p + m + mi + i)) rfl hR ev50
  subst hheap
  obtain ⟨Rt, Rb, mR, T, B, ℓ, rfl, -, hRt, -, -⟩ := hbody.forallE_of_load ld78
  obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hRh, -, -, hRt_eq, -, -⟩ :=
    Decl.collect_spine_rawTm_spec hRt ev117
  injection htup with h1
  simp only [List.cons.injEq, and_true] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨a, us, rfl, ha⟩ := rawTm_const_of_load_addr hRh ld154
  subst hr hh
  exact ⟨rbs, Rt, Rb, mR, a, us, hstrip, by rw [hRt_eq, getAppFn_mkAppN_ce]; rfl, ha⟩

private theorem last_binder_dom_rawTm_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelModeled::last_binder_dom" →
      ∀ (x_e : SourceValue F) (k : Nat) (R E : KExpr),
        args = [x_e] → Decl.RawTm κ d Γ h k R E x_e →
        h' = h ∧ ∃ (k' : Nat) (Rd Ed : KExpr),
          lastBinderDom R = some Rd ∧ Decl.RawTm κ d Γ h k' Rd Ed r :=
  ObsFn.strong_induction (world := Obs.W)
    (fun fname args h r h' cs => fname = "KernelModeled::last_binder_dom" →
      ∀ (x_e : SourceValue F) (k : Nat) (R E : KExpr),
        args = [x_e] → Decl.RawTm κ d Γ h k R E x_e →
        h' = h ∧ ∃ (k' : Nat) (Rd Ed : KExpr),
          lastBinderDom R = some Rd ∧ Decl.RawTm κ d Γ h k' Rd Ed r)
    (fun fname args h r h' cs ev ih hfn x_e k R E hargs hR => by
      subst hfn hargs
      match Obs.«KernelModeled::last_binder_dom».obs ev with
      | .Forall (x_d := xd) (x_b := xb) (cs76 := cs76)
          (ld12 := ld12) (ld47 := ld47) (ev78 := ev78) (hc87 := hc87) .. =>
        subst hc87
        obtain ⟨Rd, Rb, mR, Ed, Eb, ℓ, rfl, -, -, hRb, -⟩ := hR.forallE_of_load ld12
        obtain ⟨Rd2, Rb2, mR2, -, -, -, hRb_fa, -, -, -, -⟩ := hRb.forallE_of_load ld47
        obtain ⟨hh, k', Rd_out, Ed_out, hlast, hRd_out⟩ :=
          ih _ _ _ _ _ _ (by simp) ev78 rfl xb (k + 1) Rb Eb rfl hRb
        refine ⟨hh, k', Rd_out, Ed_out, ?_, hRd_out⟩
        rw [hRb_fa] at hlast ⊢
        simpa [lastBinderDom] using hlast
      | .other (x_d := xd) (x_b := xb) (v36 := v36)
          (ld12 := ld12) (ld47 := ld47) (hne88 := hne88) (he93 := hr) (he94 := hh) .. =>
        subst hr hh
        obtain ⟨Rd, Rb, mR, Ed, Eb, ℓ, rfl, -, hRd, hRb, -⟩ := hR.forallE_of_load ld12
        have hnot_fa : ∀ d' b' m', Rb ≠ .forallE d' b' m' := by
          intro d' b' m' heq
          subst heq
          cases hRb with
          | forallE cell _ _ _ =>
            rw [Core.loadValue_enum_cell cell] at ld47
            exact hne88 _ rfl (Except.ok.inj ld47).symm
        refine ⟨rfl, k, Rd, Ed, ?_, hRd⟩
        cases Rb with
        | forallE d' b' m' => exact (hnot_fa d' b' m' rfl).elim
        | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
        | letE _ _ _ _ | lit _ | proj _ _ _ => rfl)

private theorem rawShape_lastBinderDom : ∀ {a b : KExpr}, RawShape a b →
    (lastBinderDom a = none ∧ lastBinderDom b = none) ∨
      ∃ d₁ d₂, lastBinderDom a = some d₁ ∧ lastBinderDom b = some d₂ ∧ RawShape d₁ d₂ := by
  intro a b h
  induction h with
  | @forallE t t' b₁ b₁' m m' ht hb _ ihb =>
    cases hb with
    | forallE _ _ =>
      rcases ihb with ⟨h1, h2⟩ | ⟨d₁, d₂, h1, h2, hd⟩
      · exact Or.inl ⟨by simpa [lastBinderDom] using h1, by simpa [lastBinderDom] using h2⟩
      · exact Or.inr ⟨d₁, d₂, by simpa [lastBinderDom] using h1, by simpa [lastBinderDom] using h2, hd⟩
    | bvar | fvar | sort | const | lit | app | lam | letE | proj =>
      exact Or.inr ⟨t, t', rfl, rfl, ht⟩
  | bvar | fvar | sort | const | lit | app | lam | letE | proj =>
    exact Or.inl ⟨rfl, rfl⟩

/-- Two terms of one raw shape have one `familyKey`. -/
theorem familyKey_eq_of_rawShape {rc : Ixon.Recursor} {a b : KExpr} (h : RawShape a b) :
    familyKey rc a = familyKey rc b := by
  unfold familyKey binderDom
  rcases rawShape_stripPis rc.params.toNat h with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    cases h3 with
    | forallE hd _ =>
      rcases rawShape_lastBinderDom hd with ⟨l1, l2⟩ | ⟨d₁, d₂, l1, l2, hds⟩
      · simp [l1, l2]
      · simp [l1, l2, headKey_eq_of_rawShape hds]
    | bvar | fvar | sort | const | lit | app | lam | letE | proj => rfl

/-- **`KernelModeled::check_carriers` extracts `familyKey rc R`** from the first element of
`x_type_addrs`. -/
theorem check_carriers_rawTm_familyKey {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {R E : KExpr} {rc : Ixon.Recursor}
    {x_ty x_type_addrs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    {t0 : Bytes.Address} {rest : List Bytes.Address}
    (hnp : rc.params.toNat < 72057594037927936)
    (hR : Decl.RawTm κ d Γ h 0 R E x_ty)
    (haddrs : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h (t0 :: rest) x_type_addrs)
    (ev : ObsFn Obs.W "KernelModeled::check_carriers"
      [x_ty, .field (rc.params.toNat : F), x_type_addrs] h r h' calls) :
    familyKey rc R = some (κ (Core.ixAddr t0)) := by
  match Obs.«KernelModeled::check_carriers».obs ev with
  | .run (v7 := v7) (m10 := m10) (ev20 := ev20) (ev6 := ev6) .. =>
    have hval : ZMod.val (rc.params.toNat : F) = rc.params.toNat :=
      ZMod.val_natCast_of_lt (Nat.lt_trans hnp (by decide))
    obtain ⟨hm10, rbs, rbody, ebody, hstrip, hbody⟩ :=
      peel_n_foralls_rawTm_val rc.params.toNat hval hR ev20
    subst hm10
    match Obs.«KernelModeled::check_carriers_go».obs ev6 with
    | .Nil (ld12 := ld12) .. => cases Lib.rep_nil_of_load haddrs ld12
    | .Cons (x_t := xt) (x_mdom := xmd) (v91 := v91) (m93 := m93) (x_head := xh) (m78 := m78)
        (x_c := xc) (ld12 := ld12) (ld53 := ld53) (ev103 := ev103) (ev90 := ev90)
        (ld137 := ld137) (ev180 := ev180) (heq203 := heq203) .. =>
      obtain ⟨_, _, hcons, ht0_rep, _⟩ := Lib.rep_cons_of_load haddrs ld12
      injection hcons with h1 _
      subst h1
      obtain ⟨Rmot, _, _, Emot, _, _, rfl, -, hRmot, -, -⟩ := hbody.forallE_of_load ld53
      obtain ⟨hm93, k', Rdom, Edom, hlast, hRdom⟩ :=
        last_binder_dom_rawTm_aux _ _ _ _ _ _ ev103 rfl xmd _ Rmot Emot rfl hRmot
      subst hm93
      obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hRh, -, -, hRdom_eq, -, -⟩ :=
        Decl.collect_spine_rawTm_spec hRdom ev90
      injection htup with h1
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨ac, us, rfl, hac⟩ := rawTm_const_of_load_addr hRh ld137
      have ht0_m78 : Bytes.RepAddressRef Core.addrTy m78 t0 xt :=
        Bytes.repAddressRef_heapMono₂ Core.addrTy ev90.heap_extends ht0_rep
      have hac_eq : ac = t0 := by
        obtain ⟨h1, _⟩ := Lib.address_eq_spec ev180 hac ht0_m78
        rw [heq203] at h1
        split at h1
        · assumption
        · exact absurd (Value.field.inj h1) one_ne_zero
      subst hac_eq
      unfold familyKey binderDom
      rw [hstrip]
      simp only [Option.bind_some, hlast, headKey, hRdom_eq, getAppFn_mkAppN_ce, Expr.getAppFn]

/-- **`KernelModeled::check_rec_motive` ensures the `mI + 1`-st conclusion is not a `∀`**, because
its spine head is a `.bvar`. -/
theorem check_rec_motive_not_forallE {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {E : KExpr} {x_ty r : SourceValue F} {depth mpos : Nat}
    {h h' : Heap F} {calls : List (Call F)}
    (hdepth : depth < Aiur.Library.U32.Goldilocks.modulus)
    (hE : Decl.TmExact κ 0 Γ h 0 E x_ty)
    (ev : ObsFn Obs.W "KernelModeled::check_rec_motive"
      [x_ty, .field (depth : F), .field (mpos : F)] h r h' calls) :
    ∃ bs concl, E.stripPis depth = some (bs, concl) ∧ ∀ d b m, concl ≠ .forallE d b m := by
  match Obs.«KernelModeled::check_rec_motive».obs ev with
  | .run (v1 := v1) (m2 := m2) (x_head := xh) (m32 := m32)
      (ev14 := ev14) (ev44 := ev44) (ld78 := ld78) .. =>
    have hval : ZMod.val (depth : F) = depth := ZMod.val_natCast_of_lt hdepth
    obtain ⟨bs, concl, hstrip, hconcl, rfl⟩ :=
      Decl.peel_n_foralls_exact depth hval ev14 hE
    obtain ⟨hd, sp, Eh, Eas, htup, hEh, -, hconcl_eq⟩ :=
      Decl.collect_spine_exact ev44 hconcl
    injection htup with h1
    simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨i_f, -, -, hbvar⟩ := hEh.toTm.bvar_of_load ld78
    rcases hbvar with ⟨_, rfl⟩ | ⟨_, hbad, _⟩
    · refine ⟨bs, concl, hstrip, fun d b m heq => ?_⟩
      have hfn : concl.getAppFn = .bvar i_f.val := by
        rw [hconcl_eq, getAppFn_mkAppN_ce]; rfl
      rw [heq] at hfn
      cases hfn
    · omega

/-! ## Extracting `check_rules` scoping and rule count -/

private theorem inv_var_find_ce {locals : Environment F Nat} {name : String}
    {v expected : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlkp : locals.find? (·.1 == name) = some (name, expected))
    (ev : ObsExpr Obs.W [] locals (.var name) h v h' cs) :
    expected = v ∧ h = h' ∧ cs = [] := by
  obtain ⟨l, hh, hc⟩ := ev.var_inv
  rw [hlkp] at l
  injection l with l; injection l with _ hv
  exact ⟨hv, hh.symm, hc⟩

private theorem check_iota_rule_validate_scoped
    {rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_iota_rule"
      [rc, rm, nl, ty_r, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t_addr, src, dst, aset]
      h r h' calls) :
    ∃ (h_plen : Heap F) (v_sc : SourceValue F) (h_sc : Heap F) (cs_sc : List (Call F)),
      Heap.Extends h h_plen ∧
      ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [rhs, .field 0, nl] h_plen v_sc h_sc cs_sc ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [rhs, .field 0, nl], h_plen⟩ : Call F) ∈ calls := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelModeled.check_iota_rule.lookup
    (by simp [IxVM.KernelModeled.check_iota_rule, ControlLower.hasControl]) ev
  simp only [IxVM.KernelModeled.check_iota_rule] at d0
  -- 1. `let mi = rp + ni`
  obtain ⟨mi, m1, _, c1a, c1b, d1, mt1, rest1, rfl⟩ := d0.letValue_inv
  obtain ⟨_, _, _, _, _, dl1, dr1, _, rfl⟩ := d1.binary_inv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) dl1
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) dr1
  obtain rfl := matchPattern_bind_inv mt1
  -- 2. `let d = rp + cnf`
  obtain ⟨d, m2, _, c2a, c2b, d2, mt2, rest2, rfl⟩ := rest1.letValue_inv
  obtain ⟨_, _, _, _, _, dl2, dr2, _, rfl⟩ := d2.binary_inv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) dl2
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) dr2
  obtain rfl := matchPattern_bind_inv mt2
  -- 3. `assert_eq!(Lists::length(pins), cnp)`
  obtain ⟨_, m3, _, c3a, c3b, d3, mt3, rest3, rfl⟩ := rest2.letValue_inv
  obtain ⟨_, a3, ap3⟩ := d3.builtin_inv
  obtain ⟨v3_l, vs3_r, h_plen, c3_l, c3_r, rfl, d3_l, a3_r, rfl⟩ := a3.cons_inv
  obtain ⟨v3_r, vs3_nil, m3_r, _, _, rfl, d3_r, a3_nil, rfl⟩ := a3_r.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := a3_nil.nil_inv
  obtain ⟨_, _, _, cs_plen, a3_la, ev_plen, rfl⟩ := d3_l.call_inv
  obtain ⟨_, _, _, _, _, rfl, d3_lv, a3_lnil, rfl⟩ := a3_la.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := a3_lnil.nil_inv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) d3_lv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) d3_r
  obtain ⟨_, rfl⟩ := Builtin.assertEq_inv ap3
  obtain rfl := matchPattern_wildcard_inv mt3
  -- 4. `KernelCheck::validate_expr_well_scoped(rhs, 0, nl)`
  obtain ⟨v_sc, h_sc, _, c4a, c4b, d4, mt4, rest4, rfl⟩ := rest3.letValue_inv
  obtain ⟨_, m4_3, _, cs_sc, a4, ev_sc, rfl⟩ := d4.call_inv
  rw [instanceName_plain_some] at ev_sc
  obtain ⟨v4_1, vs4_2, m4_1, c4_1, c4_23, rfl, d4_1, a4_2, rfl⟩ := a4.cons_inv
  obtain ⟨v4_2, vs4_3, m4_2, c4_2, c4_3, rfl, d4_2, a4_3, rfl⟩ := a4_2.cons_inv
  obtain ⟨v4_3, vs4_nil, m4_3', c4_3', c4_nil, rfl, d4_3, a4_nil, rfl⟩ := a4_3.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := a4_nil.nil_inv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) d4_1
  obtain ⟨rfl, rfl, rfl⟩ := d4_2.literal_inv
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find_ce (by rfl) d4_3
  refine ⟨_, v_sc, h_sc, cs_sc, ev_plen.heap_extends, ev_sc, ?_⟩
  simp [instanceName_plain_some]

private theorem check_rules_go_scoped {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {nlvls : Nat}
    (hbound : Bounded calls) (hnlvls : nlvls < 4294967296) :
    ∀ {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {x_rules : SourceValue F}
      {h₀ : Heap F}
      {x_rc x_rm x_ty x_rp x_ni x_ib x_ii x_inp x_il x_pins x_src x_dst x_aset x_s x_j r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h₀ j root rus x_rules →
      Heap.Extends h₀ h →
      ObsFn Obs.W "KernelModeled::check_rules_go"
        [x_rc, x_rm, .field (nlvls : F), x_ty, x_rp, x_ni, x_rules, x_ib, x_ii, x_inp, x_il,
          x_pins, x_src, x_dst, x_aset, x_s, x_j] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ ru ∈ rus, ∀ rhsP,
        (exprReader t blob src id self).read ru.rhs = .ok rhsP →
        rhsP.looseBVarsBounded 0 = true ∧ rhsP.allLevelParamsDefined (List.range nlvls) = true := by
  intro j root rus x_rules h₀ x_rc x_rm x_ty x_rp x_ni x_ib x_ii x_inp x_il x_pins x_src x_dst
    x_aset x_s x_j r h h' cs hrep
  induction hrep generalizing h h' cs x_s x_j with
  | nil cell =>
    intro _ _ _ ru hmem
    cases hmem
  | @cons j root addr rhsPtr rest ru rus plan cell hf raw planned levels rs ih =>
    intro hext ev hsub ru' hmem rhsP hread
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have := Core.loadValue_enum_cell (heapExt_getElem? hext cell)
      rw [this] at ld12
      exact absurd (Value.construct.inj (Except.ok.inj ld12)).2.1 (by decide)
    | .Cons (x_rest := xrest) (x_rhs := xrhs) (m42 := m42) (m117 := m117) (m155 := m155)
        (m77 := m77) (cs290 := cs290) (cs432 := cs432)
        (ld12 := ld12) (ev54 := ev54) (ev129 := ev129) (ev171 := ev171) (ev292 := ev292)
        (ev434 := ev434) (hc579 := hc) .. =>
      have hld := Core.loadValue_enum_cell (heapExt_getElem? hext cell)
      rw [hld] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      injection hargs with hhd htl
      injection htl with hrest_eq _
      injection hhd with _ _ hmk
      injection hmk with _ hmk2
      injection hmk2 with _ hmk3
      injection hmk3 with hrhs_eq _
      subst hrest_eq hrhs_eq
      rcases List.mem_cons.mp hmem with rfl | hmem_rest
      · obtain ⟨h_plen, v_sc, h_sc, cs_sc, ext_plen, ev_sc, hmem_sc⟩ :=
          check_iota_rule_validate_scoped ev292
        have ext_sc : Heap.Extends h₀ h_plen :=
          hext.trans (ev54.heap_extends.trans (ev129.heap_extends.trans
            (ev171.heap_extends.trans ext_plen)))
        have hcl_sc : (⟨"KernelCheck::validate_expr_well_scoped",
            [rhsPtr, .field 0, .field (nlvls : F)], h_plen⟩ : Call F) ∈ calls :=
          hsub _ (by rw [hc]; simp [hmem_sc])
        exact (Assembly.validate_expr_well_scoped_spec hbound hnlvls raw ext_sc hread ev_sc hcl_sc).2
      · have ext_next : Heap.Extends h₀ m77 :=
          hext.trans (ev54.heap_extends.trans (ev129.heap_extends.trans
            (ev171.heap_extends.trans ev292.heap_extends)))
        exact ih ext_next ev434 (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ru' hmem_rest rhsP hread

private theorem stored_rekey_ce (c : Core.Ctx) :
    ∀ x, c.stored.κ x ≠ Core.unresolvedKey → Core.keyOf c.t x = c.stored.κ x := by
  intro x hne
  change Core.resKey c.t (c.resolvesOver c.env) x ≠ Core.unresolvedKey at hne
  change Core.keyOf c.t x = Core.resKey c.t (c.resolvesOver c.env) x
  unfold Core.resKey at hne ⊢
  split at hne
  · next h => simp [h]
  · exact absurd rfl hne

private theorem rulesRep_det_ce {c : Core.Ctx} {h : Heap F} {ps₁ ps₂ : List LevelParam} :
    ∀ {j : Nat} {v : SourceValue F} {rls₁ rls₂ : List (RecRule .anon)},
      Core.RulesRep c.stored.κ h ps₁ j v rls₁ →
      Core.RulesRep (Core.keyOf c.t) h ps₂ j v rls₂ →
      List.Forall₂ (fun r₁ r₂ => r₁.nfields = r₂.nfields ∧
        Core.ExprLvEq (Core.posOf ps₁ r₁.rhs) (Core.posOf ps₂ r₂.rhs)) rls₁ rls₂
  | _, _, _, _, .nil _, .nil _ => .nil
  | _, _, _, _, .nil cell₁, .cons cell₂ _ _ => by
    have := Core.cell_eq cell₁ cell₂; simp at this
  | _, _, _, _, .cons cell₁ _ _, .nil cell₂ => by
    have := Core.cell_eq cell₁ cell₂; simp at this
  | _, _, r₁ :: _, r₂ :: _, .cons cell₁ ⟨rhs₁, hv₁, hlt₁, htm₁⟩ rs₁,
      .cons cell₂ ⟨rhs₂, hv₂, hlt₂, htm₂⟩ rs₂ => by
    have hce := Core.cell_eq cell₁ cell₂
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hce
    obtain ⟨rfl, rfl⟩ := hce
    rw [hv₁] at hv₂
    injection hv₂ with _ _ hargs
    injection hargs with _ hargs2
    injection hargs2 with hnf hargs3
    injection hargs3 with hrhs _
    subst hrhs
    have hnf_nat : r₁.nfields = r₂.nfields := by
      have h1 := congrArg ZMod.val (Value.field.inj hnf)
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
      exact h1
    refine .cons ⟨hnf_nat, Core.Tm.det
      ((htm₁ 0 (fun _ => .sort .zero)).rekey_mono (stored_rekey_ce c))
      (htm₂ 0 (fun _ => .sort .zero))⟩ (rulesRep_det_ce rs₁ rs₂)

private theorem check_rules_go_nfields {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {src : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    {bM : Bytes.Address} {iM : Nat} {x_ib : SourceValue F} {h_ib : Heap F}
    (hSS : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hiM : iM < 72057594037927936)
    (hbM : Bytes.RepAddressRef Core.addrTy h_ib bM x_ib) :
    ∀ {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {x_rules : SourceValue F}
      {h₀ : Heap F}
      {x_rc x_rm x_nl x_ty x_rp x_ni x_inp x_il x_pins x_src x_dst x_aset x_s r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rus.length < 72057594037927936 →
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h₀ j root rus x_rules →
      Heap.Extends h₀ h → Heap.Extends h_ib h →
      ObsFn Obs.W "KernelModeled::check_rules_go"
        [x_rc, x_rm, x_nl, x_ty, x_rp, x_ni, x_rules, x_ib, .field (iM : F), x_inp, x_il,
          x_pins, x_src, x_dst, x_aset, x_s, .field (j : F)] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ (c_idx : Nat) (ru : Ixon.RecursorRule), rus[c_idx]? = some ru →
        ∀ cvj cnP cnF,
          env.find? (keyOf t (Core.cprjAddr (Core.ixAddr bM) iM (j + c_idx))) =
            some (.ctorInfo cvj cnP cnF) →
          ru.fields.toNat = cnF := by
  intro j root rus x_rules h₀ x_rc x_rm x_nl x_ty x_rp x_ni x_inp x_il x_pins x_src x_dst x_aset
    x_s r h h' cs hbound_j hrep
  induction hrep generalizing h h' cs x_s with
  | nil cell =>
    intro _ _ _ _ c_idx ru hget
    simp at hget
  | @cons j root addr rhsPtr rest ru rus plan cell hf raw planned levels rs ih =>
    intro hext hext_ib ev hsub c_idx ru' hget cvj cnP cnF hfind
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have := Core.loadValue_enum_cell (heapExt_getElem? hext cell)
      rw [this] at ld12
      exact absurd (Value.construct.inj (Except.ok.inj ld12)).2.1 (by decide)
    | .Cons (x_rest := xrest) (x_rnf := xrnf) (v116 := v116) (m42 := m42) (m117 := m117)
        (m155 := m155) (p163 := p163) (x_cnf := xcnf) (m77 := m77) (v451 := v451)
        (cs127 := cs127) (cs169 := cs169) (cs432 := cs432)
        (ld12 := ld12) (ev54 := ev54) (ev129 := ev129) (ev171 := ev171) (ld165 := ld165)
        (heq286 := heq286) (ev292 := ev292) (op577 := op577) (ev434 := ev434) (hc579 := hc) .. =>
      have hld := Core.loadValue_enum_cell (heapExt_getElem? hext cell)
      rw [hld] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      injection hargs with hhd htl
      injection htl with hrest_eq _
      injection hhd with _ _ hmk
      injection hmk with _ hmk2
      injection hmk2 with hnf_eq _
      subst hrest_eq hnf_eq
      cases c_idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at hget hfind
        subst hget
        let c : Core.Ctx := ⟨E, env, t, lim⟩
        have hsub127 : ∀ cl ∈ cs127, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hsub169 : ∀ cl ∈ cs169, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hgood_all : Core.Good c calls := hSS.good env lim
        obtain ⟨bC, hbC_rep, hbC_addr⟩ := Decl.projection_addr_ctor_bounded (c := c)
          (by omega) (by omega)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy (hext_ib.trans ev54.heap_extends) hbM)
          (hgood_all.sub hsub127) ev129
        have hfind' : env.find? (Core.keyOf t (Core.ixAddr bC)) = some (.ctorInfo cvj cnP cnF) := by
          rw [hbC_addr, LoadedReads.keyOf_eq]; exact hfind
        have hκC : c.stored.κ (Core.ixAddr bC) = Core.keyOf t (Core.ixAddr bC) :=
          Core.Ctx.stored_key_of_find (c := c) hfind'
        have hneC : c.stored.κ (Core.ixAddr bC) ≠ Core.unresolvedKey := by
          rw [hκC]; exact Core.Resolved.ne
        have hg169 : Core.CoreGood c.stored cs169 :=
          Core.CoreGood.ofRaw (hgood_all.sub hsub169) (fun _ _ => trivial)
        obtain ⟨ci, hfind_ci, pv, hpv_ld, hci_rep⟩ :=
          hinv.loads.getCI v116 p163 m117 m155 cs169 bC ev171 trivial hneC hg169 hbC_rep
        change env.find? _ = some ci at hfind_ci
        rw [hκC, hfind'] at hfind_ci
        injection hfind_ci with hci_eq
        subst hci_eq
        rw [hpv_ld] at ld165
        injection ld165 with hv_eq
        rw [hv_eq] at hci_rep
        generalize hvg : Value.construct "KernelTypes::KConstantInfo" "Ctor" _ = vg at hci_rep
        cases hci_rep with
        | ctor _ _ hcnf_eq hcnts _ =>
          injection hvg with _ _ hvf
          injection hvf with _ hvf2
          injection hvf2 with _ hvf3
          injection hvf3 with _ hvf4
          injection hvf4 with _ hvf5
          injection hvf5 with _ hvf6
          injection hvf6 with _ hvf7
          injection hvf7 with hcnf_eq' _
          rw [hcnf_eq', hcnf_eq] at heq286
          have h1 := congrArg ZMod.val (Value.field.inj heq286)
          have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
          exact h1
        | quot _ _ => exact absurd (Value.construct.inj hvg).2.1 (by decide)
      | succ c' =>
        simp only [List.getElem?_cons_succ] at hget
        have hv451 : v451 = .field ((j + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at op577
          rw [← op577, Nat.cast_succ]
        rw [hv451] at ev434
        have ext_step : Heap.Extends h m77 :=
          ev54.heap_extends.trans (ev129.heap_extends.trans (ev171.heap_extends.trans ev292.heap_extends))
        have hfind' : env.find? (keyOf t (Core.cprjAddr (Core.ixAddr bM) iM ((j + 1) + c'))) =
            some (.ctorInfo cvj cnP cnF) := by
          have heq : j + 1 + c' = j + (c' + 1) := by omega
          rwa [heq]
        exact ih (by simp at hbound_j; omega) (hext.trans ext_step) (hext_ib.trans ext_step)
          ev434 (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) c' ru' hget cvj cnP cnF hfind'

private theorem check_rules_go_ctor_params {calls : List (Call F)} {E₀ : Ixon.Env}
    {src : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    {bM : Bytes.Address} {iM : Nat} {x_ib : SourceValue F} {h_ib : Heap F}
    {cbM : Ixon.Constant} {msM : Array Ixon.MutConst} {indM : Ixon.Inductive}
    (hRS : LoadedReads.RunStore calls E₀)
    (hbd : Bounded calls)
    (hiM : iM < 72057594037927936)
    (hbM : Bytes.RepAddressRef Core.addrTy h_ib bM x_ib)
    (hrec_cbM : recordOf E₀ (Core.ixAddr bM) = some cbM)
    (hcbM : cbM.info = .muts msM)
    (hmsM : msM.toList[iM]? = some (.indc indM))
    (hindM_np : indM.params.toNat < 72057594037927936) :
    ∀ {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {x_rules : SourceValue F}
      {h₀ : Heap F}
      {x_rc x_rm x_nl x_ty x_rp x_ni x_il x_pins x_src x_dst x_aset x_s r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      j + rus.length < 72057594037927936 →
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h₀ j root rus x_rules →
      Heap.Extends h₀ h → Heap.Extends h_ib h →
      ObsFn Obs.W "KernelModeled::check_rules_go"
        [x_rc, x_rm, x_nl, x_ty, x_rp, x_ni, x_rules, x_ib, .field (iM : F),
          .field (indM.params.toNat : F), x_il, x_pins, x_src, x_dst, x_aset, x_s,
          .field (j : F)] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ (c_idx : Nat), c_idx < rus.length →
        ∀ (ct : Ixon.Constructor), indM.ctors.toList[j + c_idx]? = some ct →
          ct.params.toNat = indM.params.toNat := by
  intro j root rus x_rules h₀ x_rc x_rm x_nl x_ty x_rp x_ni x_il x_pins x_src x_dst x_aset
    x_s r h h' cs hbound_j hrep
  induction hrep generalizing h h' cs x_s with
  | nil cell =>
    intro _ _ _ _ c_idx hc_lt
    simp at hc_lt
  | @cons j root addr rhsPtr rest ru rus plan cell hf raw planned levels rs ih =>
    intro hext hext_ib ev hsub c_idx hc_lt ct hct
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld12) .. =>
      have := Core.loadValue_enum_cell (heapExt_getElem? hext cell)
      rw [this] at ld12
      exact absurd (Value.construct.inj (Except.ok.inj ld12)).2.1 (by decide)
    | .Cons (x_rest := xrest) (v116 := v116) (m42 := m42) (m117 := m117)
        (m155 := m155) (p163 := p163) (x_cnp := xcnp) (m77 := m77) (v451 := v451)
        (cs127 := cs127) (cs169 := cs169) (cs432 := cs432)
        (ld12 := ld12) (ev54 := ev54) (ev129 := ev129) (ev171 := ev171) (ld165 := ld165)
        (heq258 := heq258) (ev292 := ev292) (op577 := op577) (ev434 := ev434) (hc579 := hc) .. =>
      have hld := Core.loadValue_enum_cell (heapExt_getElem? hext cell)
      rw [hld] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      injection hargs with _ htl
      injection htl with hrest_eq _
      subst hrest_eq
      cases c_idx with
      | zero =>
        simp only [Nat.add_zero] at hct
        have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
        have hsub127 : ∀ cl ∈ cs127, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hsub169 : ∀ cl ∈ cs169, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hbM_m42 := Bytes.repAddressRef_heapMono₂ Core.addrTy (hext_ib.trans ev54.heap_extends) hbM
        obtain ⟨bC, hbC_rep, hbC_addr⟩ := FamilyAlias.projection_addr_ctor_bounded ev129
          (Core.bounded_sub hsub127 hbd) hbM_m42
        have hiM_val : ZMod.val (iM : F) = iM := ZMod.val_natCast_of_lt (by omega)
        have hj_val : ZMod.val (j : F) = j := ZMod.val_natCast_of_lt (by simp at hbound_j; omega)
        rw [hiM_val, hj_val] at hbC_addr
        let c0 : Core.ScopedCtx := Core.ScopedCtx.unrestricted ⟨{}, .empty, default, none⟩
        have hhash_cprj := Core.hashed_mono hsub127 (Core.projection_addr_ctor_hashed c0 ev129 hbM_m42)
        rw [hiM_val, hj_val] at hhash_cprj
        obtain ⟨rawC, c_cp, hhC, haddrC, hexC, -, hresC⟩ :=
          L1.get_ci_block_trace_spec (Core.bounded_sub hsub169 hbd) hbC_rep ev171
        let c_exp : Ixon.Constant :=
          ⟨.cPrj ⟨iM.toUInt64, j.toUInt64, Core.ixAddr bM⟩, #[], #[], #[], #[]⟩
        have haddr_exp : Address.blake3Pure (Ixon.serConstant c_exp) = Core.ixAddr bC := by
          rw [hbC_addr]; rfl
        have hraw_eq : rawC = Ixon.serConstant c_exp :=
          Option.some.inj ((hRS.blobs rawC (Core.hashed_mono hsub169 hhC)).symm.trans
            (by rw [haddrC, ← haddr_exp]; exact hRS.blobs _ hhash_cprj))
        have hwfC := L1.projConstant_wireWF_cPrj iM.toUInt64 j.toUInt64 bM
        have hccp_eq : c_cp = c_exp :=
          Except.ok.inj (hexC.symm.trans
            (by rw [hraw_eq]; exact Ixon.Verify.deConstantExact_serConstant _ hwfC))
        subst c_cp
        unfold L1.GetCIBlockTraceResult at hresC
        dsimp only [c_exp] at hresC
        obtain ⟨-, -, blkC, cbC, msC, indC, ctC, blobsC, treeC, planC, vC, hhBC, haBC, hexBC,
          hcbC, hmsC, hctC, -, -, -, hldC, hrawC, -⟩ := hresC
        have hcbC_eq : cbC = cbM :=
          hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hrec_cbM)
            (Core.hashed_mono hsub169 hhBC) haBC hexBC
        subst cbC
        have hmsC_eq : msC = msM := Ixon.ConstantInfo.muts.inj (hcbC.symm.trans hcbM)
        subst msC
        have hiM64 : iM.toUInt64.toNat = iM := by
          change (UInt64.ofNat iM).toNat = iM
          rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        have hj64 : j.toUInt64.toNat = j := by
          change (UInt64.ofNat j).toNat = j
          rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by simp at hbound_j; omega)
        rw [hiM64] at hmsC
        have hindC_eq : indC = indM := Ixon.MutConst.indc.inj (Option.some.inj (hmsC.symm.trans hmsM))
        subst indC
        rw [hj64] at hctC
        have hctC_eq : ctC = ct := Option.some.inj (hctC.symm.trans hct)
        subst ctC
        obtain ⟨-, -, hct_np, -, -, tyPtrC, blkPtrC, bBC, -, -, hvC, -⟩ := hrawC
        rw [hvC] at hldC
        rw [hldC] at ld165
        injection ld165 with hv_eq
        injection hv_eq with _ _ hf
        injection hf with _ hf2
        injection hf2 with _ hf3
        injection hf3 with _ hf4
        injection hf4 with _ hf5
        injection hf5 with _ hf6
        injection hf6 with hcnp_eq _
        rw [← hcnp_eq] at heq258
        have h1 := congrArg ZMod.val (Value.field.inj heq258)
        rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
        exact h1
      | succ c' =>
        have hv451 : v451 = .field ((j + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at op577
          rw [← op577, Nat.cast_succ]
        rw [hv451] at ev434
        have ext_step : Heap.Extends h m77 :=
          ev54.heap_extends.trans (ev129.heap_extends.trans (ev171.heap_extends.trans ev292.heap_extends))
        have hct' : indM.ctors.toList[(j + 1) + c']? = some ct := by
          have heq : j + 1 + c' = j + (c' + 1) := by omega
          rwa [heq]
        exact ih (by simp at hbound_j; omega) (hext.trans ext_step) (hext_ib.trans ext_step)
          ev434 (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) c' (by simp at hc_lt; omega) ct hct'

/-! ## Pin bounds, address-mention exclusion, and block parameter counts -/

/-- Two consecutive `noLooseIn` checks (before and after `lowerBVars n lo`) imply
`hasBVarIn lo (lo + m + n) e = false`. -/
theorem hasBVarIn_false_of_noLooseIn_lower {m n : Nat} :
    ∀ (e : KExpr) (lo : Nat),
      Decl.noLooseIn lo n e = true →
      Decl.noLooseIn lo m (e.lowerBVars n lo) = true →
      Binding.FamilyFlat.hasBVarIn lo (lo + m + n) e = false
  | .bvar i, lo, h1, h2 => by
    simp only [Decl.noLooseIn, decide_eq_true_eq] at h1
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    rcases h1 with hlt | hge
    · exact Or.inl (by omega)
    · have hlow : (Expr.bvar i : KExpr).lowerBVars n lo = .bvar (i - n) := by
        show (if i ≥ lo + n then Expr.bvar (i - n) else Expr.bvar i) = .bvar (i - n)
        exact ite_eq_left hge
      rw [hlow] at h2
      simp only [Decl.noLooseIn, decide_eq_true_eq] at h2
      exact Or.inr (by omega)
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, lo, h1, h2 => by
    simp only [Decl.noLooseIn, Expr.lowerBVars, Bool.and_eq_true] at h1 h2
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_false_of_noLooseIn_lower f lo h1.1 h2.1,
      hasBVarIn_false_of_noLooseIn_lower a lo h1.2 h2.2⟩
  | .lam t b _, lo, h1, h2 => by
    simp only [Decl.noLooseIn, Expr.lowerBVars, Bool.and_eq_true] at h1 h2
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    refine ⟨hasBVarIn_false_of_noLooseIn_lower t lo h1.1 h2.1, ?_⟩
    have hb := hasBVarIn_false_of_noLooseIn_lower b (lo + 1) h1.2 h2.2
    have heq : lo + 1 + m + n = lo + m + n + 1 := by omega
    rwa [heq] at hb
  | .forallE t b _, lo, h1, h2 => by
    simp only [Decl.noLooseIn, Expr.lowerBVars, Bool.and_eq_true] at h1 h2
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    refine ⟨hasBVarIn_false_of_noLooseIn_lower t lo h1.1 h2.1, ?_⟩
    have hb := hasBVarIn_false_of_noLooseIn_lower b (lo + 1) h1.2 h2.2
    have heq : lo + 1 + m + n = lo + m + n + 1 := by omega
    rwa [heq] at hb
  | .letE t v b _, lo, h1, h2 => by
    simp only [Decl.noLooseIn, Expr.lowerBVars, Bool.and_eq_true] at h1 h2
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    refine ⟨⟨hasBVarIn_false_of_noLooseIn_lower t lo h1.1.1 h2.1.1,
      hasBVarIn_false_of_noLooseIn_lower v lo h1.1.2 h2.1.2⟩, ?_⟩
    have hb := hasBVarIn_false_of_noLooseIn_lower b (lo + 1) h1.2 h2.2
    have heq : lo + 1 + m + n = lo + m + n + 1 := by omega
    rwa [heq] at hb
  | .proj _ _ e, lo, h1, h2 =>
    hasBVarIn_false_of_noLooseIn_lower e lo h1 h2

private theorem addrIn_mono_ce {h h' : Heap F} (ext : Heap.Extends h h') {p : SourceValue F}
    {a : Bytes.Address} (hin : Core.AddrIn h p a) : Core.AddrIn h' p a := by
  induction hin with
  | const cell ra =>
    exact .const (heapExt_getElem? ext cell) (Bytes.repAddressRef_heapMono₂ Core.addrTy ext ra)
  | projHead cell ra =>
    exact .projHead (heapExt_getElem? ext cell) (Bytes.repAddressRef_heapMono₂ Core.addrTy ext ra)
  | projArg cell _ ih => exact .projArg (heapExt_getElem? ext cell) ih
  | appFn cell _ ih => exact .appFn (heapExt_getElem? ext cell) ih
  | appArg cell _ ih => exact .appArg (heapExt_getElem? ext cell) ih
  | lamTy cell _ ih => exact .lamTy (heapExt_getElem? ext cell) ih
  | lamBody cell _ ih => exact .lamBody (heapExt_getElem? ext cell) ih
  | forallTy cell _ ih => exact .forallTy (heapExt_getElem? ext cell) ih
  | forallBody cell _ ih => exact .forallBody (heapExt_getElem? ext cell) ih
  | letTy cell _ ih => exact .letTy (heapExt_getElem? ext cell) ih
  | letVal cell _ ih => exact .letVal (heapExt_getElem? ext cell) ih
  | letBody cell _ ih => exact .letBody (heapExt_getElem? ext cell) ih

private theorem zero_ne_one_ce : (.field (0 : F) : SourceValue F) ≠ .field 1 :=
  fun h => one_ne_zero (Value.field.inj h).symm

/-- **`KernelModeled::expr_mentions_addrs` answering `0` rules out every cell address of the heap
term** (`Core.AddrIn`, including inside `Let` types). -/
theorem expr_mentions_addrs_zero_addrIn {as : List Bytes.Address} {pe xs : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hxs : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as xs)
    (ev : ObsFn Obs.W "KernelModeled::expr_mentions_addrs" [pe, xs] h (.field 0) h' cs) :
    ∀ a, Core.AddrIn h pe a → ∀ b ∈ as, Core.ixAddr b ≠ Core.ixAddr a := by
  match Obs.«KernelModeled::expr_mentions_addrs».obs ev with
  | .Const (ld12 := ld) (ev36 := ev_in) .. =>
    intro a hin
    cases hin with
    | const cell ra =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with h1 _
      subst h1
      exact (Decl.addr_list_contains_zero_spec hxs ra ev_in).2
    | _ =>
      rename_i cell _
      rw [Core.loadValue_enum_cell cell] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | .App_n0 (ld12 := ld) (ev85 := ev1) (ev111 := ev2) (hc128 := hc) .. =>
    intro a hin
    cases hin with
    | appFn cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with h1 _
      subst h1
      exact expr_mentions_addrs_zero_addrIn hxs ev1 a sub
    | appArg cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with _ h2; injection h2 with h2 _
      subst h2
      exact expr_mentions_addrs_zero_addrIn
        (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ev1.heap_extends hxs)
        ev2 a (addrIn_mono_ce ev1.heap_extends sub)
    | _ =>
      rename_i cell _
      rw [Core.loadValue_enum_cell cell] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | .App_other (he133 := hr) .. => exact absurd hr zero_ne_one_ce
  | .Lam_n0 (ld12 := ld) (ev173 := ev1) (ev199 := ev2) (hc216 := hc) .. =>
    intro a hin
    cases hin with
    | lamTy cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with h1 _
      subst h1
      exact expr_mentions_addrs_zero_addrIn hxs ev1 a sub
    | lamBody cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with _ h2; injection h2 with h2 _
      subst h2
      exact expr_mentions_addrs_zero_addrIn
        (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ev1.heap_extends hxs)
        ev2 a (addrIn_mono_ce ev1.heap_extends sub)
    | _ =>
      rename_i cell _
      rw [Core.loadValue_enum_cell cell] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | .Lam_other (he221 := hr) .. => exact absurd hr zero_ne_one_ce
  | .Forall_n0 (ld12 := ld) (ev261 := ev1) (ev287 := ev2) (hc304 := hc) .. =>
    intro a hin
    cases hin with
    | forallTy cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with h1 _
      subst h1
      exact expr_mentions_addrs_zero_addrIn hxs ev1 a sub
    | forallBody cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with _ h2; injection h2 with h2 _
      subst h2
      exact expr_mentions_addrs_zero_addrIn
        (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ev1.heap_extends hxs)
        ev2 a (addrIn_mono_ce ev1.heap_extends sub)
    | _ =>
      rename_i cell _
      rw [Core.loadValue_enum_cell cell] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | .Forall_other (he309 := hr) .. => exact absurd hr zero_ne_one_ce
  | .Let_n0_n0 (ld12 := ld) (ev348 := ev1) (ev383 := ev2) (ev409 := ev3) (hc426 := hc) .. =>
    intro a hin
    cases hin with
    | letTy cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with h1 _
      subst h1
      exact expr_mentions_addrs_zero_addrIn hxs ev1 a sub
    | letVal cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with _ h2; injection h2 with h2 _
      subst h2
      exact expr_mentions_addrs_zero_addrIn
        (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ev1.heap_extends hxs)
        ev2 a (addrIn_mono_ce ev1.heap_extends sub)
    | letBody cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs
      injection hargs with _ h2; injection h2 with _ h3; injection h3 with h3 _
      subst h3
      have ext12 := ev1.heap_extends.trans ev2.heap_extends
      exact expr_mentions_addrs_zero_addrIn
        (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext12 hxs)
        ev3 a (addrIn_mono_ce ext12 sub)
    | _ =>
      rename_i cell _
      rw [Core.loadValue_enum_cell cell] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | .Let_n0_other (he431 := hr) .. => exact absurd hr zero_ne_one_ce
  | .Let_other (he438 := hr) .. => exact absurd hr zero_ne_one_ce
  | .Proj_n0 (ld12 := ld) (ev478 := ev1) (ev504 := ev2) (hc521 := hc) .. =>
    intro a hin
    cases hin with
    | projHead cell ra =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with h1 _
      subst h1
      exact (Decl.addr_list_contains_zero_spec hxs ra ev1).2
    | projArg cell sub =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hargs
      injection hargs with _ h2; injection h2 with _ h3; injection h3 with h3 _
      subst h3
      exact expr_mentions_addrs_zero_addrIn
        (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ev1.heap_extends hxs)
        ev2 a (addrIn_mono_ce ev1.heap_extends sub)
    | _ =>
      rename_i cell _
      rw [Core.loadValue_enum_cell cell] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | .Proj_other (he526 := hr) .. => exact absurd hr zero_ne_one_ce
  | .other (ld12 := ld) (hne54 := n1) (hne136 := n2) (hne224 := n3) (hne312 := n4)
      (hne441 := n5) (hne529 := n6) .. =>
    intro a hin
    cases hin with
    | const cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n1 [_, _] rfl)
    | projHead cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n6 [_, _, _] rfl)
    | projArg cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n6 [_, _, _] rfl)
    | appFn cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n2 [_, _] rfl)
    | appArg cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n2 [_, _] rfl)
    | lamTy cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n3 [_, _, _] rfl)
    | lamBody cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n3 [_, _, _] rfl)
    | forallTy cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n4 [_, _, _] rfl)
    | forallBody cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n4 [_, _, _] rfl)
    | letTy cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n5 [_, _, _] rfl)
    | letVal cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n5 [_, _, _] rfl)
    | letBody cell => rw [Core.loadValue_enum_cell cell] at ld; exact absurd (Except.ok.inj ld).symm (n5 [_, _, _] rfl)
termination_by cs.length
decreasing_by
  all_goals
    simp only [hc, List.length_cons, List.length_append]
    omega

/-- Level instantiation preserves `Expr.mentionsConst`. -/
theorem mentionsConst_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) (k : KKey) :
    ∀ e : KExpr, (e.instantiateLevelParams ps us).mentionsConst k = e.mentionsConst k
  | .bvar _ | .sort _ | .lit _ => rfl
  | .fvar _ t => mentionsConst_instantiateLevelParams ps us k t
  | .const _ _ => rfl
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ps us k f,
      mentionsConst_instantiateLevelParams ps us k a]
  | .lam t b _ => by
    simp only [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ps us k t,
      mentionsConst_instantiateLevelParams ps us k b]
  | .forallE t b _ => by
    simp only [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ps us k t,
      mentionsConst_instantiateLevelParams ps us k b]
  | .letE t v b _ => by
    simp only [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ps us k t,
      mentionsConst_instantiateLevelParams ps us k v,
      mentionsConst_instantiateLevelParams ps us k b]
  | .proj _ _ e => by
    simp only [Expr.instantiateLevelParams, Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ps us k e]

/-- `mentionsConst` is invariant under `Core.posOf`. -/
theorem mentionsConst_posOf (ps : List LevelParam) (k : KKey) (e : KExpr) :
    (Core.posOf ps e).mentionsConst k = e.mentionsConst k :=
  mentionsConst_instantiateLevelParams ps ((List.range ps.length).map .param) k e

/-- `KernelModeled::block_nparams` witnesses the first inductive member of the block and returns
its parameter count as a field element below `2^56`. -/
theorem block_nparams_spec {ms : List Ixon.MutConst} {x_members r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hms : RepList L1.mutConstListEnum L1.RepMutConst h ms x_members)
    (ev : ObsFn Obs.W "KernelModeled::block_nparams" [x_members] h r h' cs) :
    ∃ (ind₀ : Ixon.Inductive) (rest : List Ixon.MutConst),
      ms = .indc ind₀ :: rest ∧
      ind₀.params.toNat < 72057594037927936 ∧
      r = .field (ind₀.params.toNat : F) := by
  match Obs.«KernelModeled::block_nparams».obs ev with
  | .run (x_params := x_params) (ld12 := ld12) (ev115 := ev115) (he173 := hr) .. =>
    subst hr
    obtain ⟨m0, rest, hms_eq, hm0, -⟩ := Lib.rep_cons_of_load hms ld12
    subst hms_eq
    cases m0 with
    | indc ind₀ =>
      obtain ⟨iv, hval, hind⟩ := hm0
      obtain ⟨typPtr, ctorsPtr, hiv, -, -⟩ := hind
      rw [hiv] at hval
      injection hval with _ _ hargs
      injection hargs with hind_eq _
      injection hind_eq with _ _ hfields
      injection hfields with _ hf2
      injection hf2 with _ hf3
      injection hf3 with hpx _
      subst hpx
      obtain ⟨hlt, hret, -⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value h ind₀.params) ev115
      exact ⟨ind₀, rest, rfl, hlt, hret⟩
    | defn _ =>
      obtain ⟨_, hval, -⟩ := hm0
      exact absurd (Value.construct.inj hval).2.1 (by decide)
    | recr _ =>
      obtain ⟨_, hval, -⟩ := hm0
      exact absurd (Value.construct.inj hval).2.1 (by decide)

/-- `Ix.Kernel.Reader.recLps` at `List.range n` has length `n + (if large then 1 else 0)` and
is a permutation of `List.range` of its own length. -/
theorem recLps_length_perm (large : Bool) (n : Nat) :
    let ps := Ix.Kernel.Reader.recLps large (List.range n)
    ps.length = n + (if large then 1 else 0) ∧ ps.Perm (List.range ps.length) := by
  cases large with
  | false =>
    simp [Ix.Kernel.Reader.recLps]
  | true =>
    have hps : Ix.Kernel.Reader.recLps true (List.range n) = n :: List.range n := by
      simp [Ix.Kernel.Reader.recLps]
    rw [hps]
    refine ⟨by simp, ?_⟩
    rw [List.length_cons, List.length_range, List.range_succ]
    exact (List.perm_append_singleton n (List.range n)).symm

private theorem rmember_typ_used_ce {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {k : Nat}
    {rc : Ixon.Recursor} (hmuts : cb.info = .muts ms) (hmem : ms[k]? = some (.recr rc)) :
    ∀ i, i ∈ exprRefIdxs rc.typ → i ∈ usedRefIdxs cb := by
  have hmem' : Ixon.MutConst.recr rc ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  intro i hi
  unfold usedRefIdxs
  rw [hmuts]
  exact List.mem_append_right _
    (List.mem_flatMap.mpr ⟨.recr rc, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)

private theorem usedRef_of_rawConvExpr_rmember {E₀ : Ixon.Env} {A : _root_.Address}
    {c : Ixon.Constant} {rs' : Array Ixon.MutConst} {k : Nat} {rc : Ixon.Recursor}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {p : SourceValue F}
    {a : Bytes.Address}
    (hc : recordOf E₀ A = some c) (hmuts : c.info = .muts rs') (hmem : rs'[k]? = some (.recr rc))
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h 4294967295
      rc.typ p)
    (hin : Core.AddrIn h p a) :
    ∃ i ∈ usedRefIdxs c, c.refs.toList[i]? = some (Core.ixAddr a) := by
  rcases raw.addrIn_used a hin with hu | hr
  · obtain ⟨i, hi | ⟨s, hs, his⟩, href⟩ := hu
    · exact ⟨i, rmember_typ_used_ce hmuts hmem i hi, href⟩
    · refine ⟨i, ?_, href⟩
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
  · simp at hr

private theorem usedRef_of_idx {E₀ : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant}
    {i : Nat} {x : _root_.Address}
    (hc : recordOf E₀ A = some c) (hi : i ∈ usedRefIdxs c)
    (href : c.refs.toList[i]? = some x) : UsedRef E₀ A x :=
  ⟨c, i, hc, hi, by rwa [← Array.getElem?_toList]⟩

private theorem addrIn_of_rawTm_const_head {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {k : Nat} {R E : KExpr} {p : SourceValue F} {a : Bytes.Address} {us : List KLevel},
      Decl.RawTm κ d Γ h k R E p →
      (R.getAppFn = .const (κ (Core.ixAddr a)) us) →
      (∀ b : Bytes.Address, κ (Core.ixAddr b) = κ (Core.ixAddr a) → Core.ixAddr b = Core.ixAddr a) →
      ∃ b : Bytes.Address, Core.ixAddr b = Core.ixAddr a ∧ Core.AddrIn h p b := by
  intro k R E p a us hR
  induction hR with
  | @const k addr ap lsp b ls us _ cell ra rls _ =>
    intro hfn hinj
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    exact ⟨b, hinj b hfn.1, .const cell ra⟩
  | app cell hf ha ihf _ =>
    intro hfn hinj
    obtain ⟨b, hb, hin⟩ := ihf hfn hinj
    exact ⟨b, hb, .appFn cell hin⟩
  | bvarLocal | bvarFree | sort | lam | forallE | letE | litNat | litStr | proj =>
    intro hfn _
    simp [Expr.getAppFn] at hfn

private theorem addrIn_of_rawTm_stripPis {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {p : SourceValue F} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {rem : KExpr},
      Decl.RawTm κ d Γ h k R E p →
      R.stripPis n = some (bs, rem) →
      ∃ E' p_rem, Decl.RawTm κ d Γ h (k + n) rem E' p_rem ∧
        ∀ a, Core.AddrIn h p_rem a → Core.AddrIn h p a := by
  intro n
  induction n with
  | zero =>
    intro k R E p bs rem hR hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact ⟨E, p, by simpa using hR, fun _ h => h⟩
  | succ n ih =>
    intro k R E p bs rem hR hs
    obtain ⟨td, bd, md, bs0, rfl, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv hs
    cases hR with
    | forallE cell ht hb _ =>
      obtain ⟨E', p_rem, hrem, hin⟩ := ih hb hs0
      refine ⟨E', p_rem, ?_, fun a ha => .forallBody cell (hin a ha)⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 n] using hrem

private theorem addrIn_of_rawTm_lastBinderDom {κ : _root_.Address → KKey} {d : Nat}
    {Γ : Nat → KExpr} {h : Heap F} :
    ∀ {k : Nat} {R E : KExpr} {p : SourceValue F} {dom : KExpr},
      Decl.RawTm κ d Γ h k R E p →
      lastBinderDom R = some dom →
      ∃ k' E' p_dom, Decl.RawTm κ d Γ h k' dom E' p_dom ∧
        ∀ a, Core.AddrIn h p_dom a → Core.AddrIn h p a := by
  intro k R E p dom hR
  induction hR with
  | @forallE k addr Rt Rb T B ℓ mR tp bp lp cell ht hb _ _ ihb =>
    intro hlast
    cases Rb with
    | forallE _ _ _ =>
      simp only [lastBinderDom] at hlast
      obtain ⟨k', E', p_dom, hdom, hin⟩ := ihb hlast
      exact ⟨k', E', p_dom, hdom, fun a ha => .forallBody cell (hin a ha)⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ =>
      simp only [lastBinderDom, Option.some.injEq] at hlast
      subst hlast
      exact ⟨k, T, tp, ht, fun a ha => .forallTy cell ha⟩
  | bvarLocal | bvarFree | sort | const | app | lam | letE | litNat | litStr | proj =>
    intro hlast
    simp [lastBinderDom] at hlast

private theorem rule_list_length_eq {src : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData} {h₀ h h' : Heap F}
    {cs : List (Call F)} {r : SourceValue F} :
    ∀ {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {x_rules : SourceValue F},
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h₀ j root rus x_rules →
      Heap.Extends h₀ h →
      ObsFn Obs.W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [x_rules] h r h' cs →
      r = .field (rus.length : F) := by
  intro j root rus x_rules hrep
  induction hrep generalizing h h' cs r with
  | @nil _ _ addr cell =>
    intro hext ev
    have ev' : ObsFn Obs.W (Generic.Instance.mk "Lists::length" [.named "KernelTypes::KRecRule" []]).symbol
        [.ptr (.enum Core.krrListEnum) addr] h r h' cs := by
      rwa [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]
    rcases Obs.«Lists::length».obs ev' with ⟨ld, rfl, -, -⟩ | ⟨_, _, _, _, _, ld, -, -⟩
    · simp
    · rw [Core.loadValue_enum_cell (heapExt_getElem? hext cell)] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
  | @cons _ _ addr _ rest _ _ _ cell _ _ _ _ _ ih =>
    intro hext ev
    have ev' : ObsFn Obs.W (Generic.Instance.mk "Lists::length" [.named "KernelTypes::KRecRule" []]).symbol
        [.ptr (.enum Core.krrListEnum) addr] h r h' cs := by
      rwa [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]
    rcases Obs.«Lists::length».obs ev' with ⟨ld, -, -, -⟩ |
      ⟨w, rest', x, m, cs', ld, ev_rec, rfl, op, -⟩
    · rw [Core.loadValue_enum_cell (heapExt_getElem? hext cell)] at ld
      exact absurd (Value.construct.inj (Except.ok.inj ld)).2.1 (by decide)
    · rw [Core.loadValue_enum_cell (heapExt_getElem? hext cell)] at ld
      injection ld with hv; injection hv with _ _ hargs; injection hargs with _ htl
      injection htl with hrest _
      subst hrest
      have ev_rec' : ObsFn Obs.W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [rest] h x h' cs' := by
        rwa [← Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]
      have hsub := ih hext ev_rec'
      subst hsub
      simp only [evalBinOp, Except.ok.injEq] at op
      rw [← op, List.length_cons, Nat.cast_succ, add_comm]

private theorem length_le_sum_map_ce {α : Type} (f : α → Nat) (hf : ∀ a, 1 ≤ f a)
    (l : List α) : l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := hf a
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem mem_le_sum_map_ce {α : Type} (f : α → Nat) {a : α} (l : List α) (h : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'; omega

private theorem rules_size_le_ce {c : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {rc : Ixon.Recursor} (h : c.info = .muts ms) (hi : ms[i]? = some (.recr rc)) :
    rc.rules.size ≤ c.resourceSize := by
  have hi' : ms.toList[i]? = some (.recr rc) := by rw [Array.getElem?_toList]; exact hi
  have h1 := mem_le_sum_map_ce Ixon.MutConst.resourceSize ms.toList (List.mem_of_getElem? hi')
  have h2 := length_le_sum_map_ce Ixon.RecursorRule.resourceSize
    (fun ru => by dsimp only [Ixon.RecursorRule.resourceSize]; omega) rc.rules.toList
  have h3 : (rc.rules.toList.map Ixon.RecursorRule.resourceSize).sum ≤
      (Ixon.MutConst.recr rc).resourceSize := by
    dsimp only [Ixon.MutConst.resourceSize, Ixon.Recursor.resourceSize]
    omega
  have h4 : c.info.resourceSize ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  rw [h] at h4
  dsimp [Ixon.ConstantInfo.resourceSize] at h4
  rw [Array.length_toList] at h2
  omega

private theorem loadValue_snoc_self_ce (h : Heap F) (v : SourceValue F) :
    loadValue (h ++ [v]) (.ptr (Value.type v) h.length) = .ok v := by
  simp [loadValue]

private theorem convert_definition_ne_induct_ce {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_definition" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_definition».obs ev with
  | .Definition (he242 := he) .. | .Opaque (he329 := he) .. | .Theorem (he373 := he) .. =>
    rw [hr] at he; injection he with _ htag _; exact absurd htag (by decide)

private theorem convert_axiom_ne_induct_ce {a₁ a₂ a₃ a₄ a₅ a₆ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_axiom" [a₁, a₂, a₃, a₄, a₅, a₆] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_axiom».obs ev with
  | .run (he107 := he) .. =>
    rw [hr] at he; injection he with _ htag _; exact absurd htag (by decide)

private theorem convert_quotient_ne_induct_ce {a₁ a₂ a₃ a₄ a₅ a₆ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_quotient" [a₁, a₂, a₃, a₄, a₅, a₆] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_quotient».obs ev with
  | .run (he107 := he) .. =>
    rw [hr] at he; injection he with _ htag _; exact absurd htag (by decide)

private theorem convert_constructor_ne_induct_ce {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_constructor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_constructor».obs ev with
  | .run (he134 := he) .. =>
    rw [hr] at he; injection he with _ htag _; exact absurd htag (by decide)

private theorem convert_recursor_ne_induct_ce {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "Convert::convert_recursor" [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] h r h' cs)
    (vs : List (SourceValue F)) : r ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs := by
  intro hr
  match Obs.«Convert::convert_recursor».obs ev with
  | .run (he237 := he) .. =>
    rw [hr] at he; injection he with _ htag _; exact absurd htag (by decide)

private theorem get_ci_induct_at {a : Bytes.Address} {x_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls)
    {nl ty np ni nc u x_blk idx : SourceValue F}
    (hld : loadValue h' r = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [nl, ty, np, ni, nc, u, x_blk, idx])) :
    ∃ (raw : ByteArray) (c : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      raw.size < 4294967296 ∧ Hashed calls raw ∧
      Address.blake3Pure raw = Core.ixAddr a ∧
      Ixon.deConstantExact raw = .ok c ∧ L1.ConstantTablesValid c ∧
      c.info = .iPrj ip ∧
      Claim.BlockLoad calls ip.block cb ms ∧
      ms.toList[ip.idx.toNat]? = some (.indc ind) ∧
      nc = .field (ind.ctors.size : F) ∧
      ind.ctors.size < 8589934592 ∧
      (∃ b_blk, Core.ixAddr b_blk = ip.block ∧ Bytes.RepAddressRef Core.addrTy h' b_blk x_blk) ∧
      idx = .field (ip.idx.toNat : F) ∧
      ip.idx.toNat < 72057594037927936 := by
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (he219 := hr) (hm218 := hh) (ev225 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self_ce] at hld
    exact absurd (Except.ok.inj hld) (convert_definition_ne_induct_ce conv _)
  | .Defn_other (he340 := hr) (hm339 := hh) (ev346 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self_ce] at hld
    exact absurd (Except.ok.inj hld) (convert_definition_ne_induct_ce conv _)
  | .Axio (he441 := hr) (hm440 := hh) (ev447 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self_ce] at hld
    exact absurd (Except.ok.inj hld) (convert_axiom_ne_induct_ce conv _)
  | .Quot (he532 := hr) (hm531 := hh) (ev538 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self_ce] at hld
    exact absurd (Except.ok.inj hld) (convert_quotient_ne_induct_ce conv _)
  | .Recr (he981 := hr) (hm980 := hh) (ev987 := conv) .. =>
    rw [hr, hh, loadValue_snoc_self_ce] at hld
    exact absurd (Except.ok.inj hld) (convert_recursor_ne_induct_ce conv _)
  | .DPrj (ev650 := ev650) .. =>
    match Obs.«Ingress::get_ci_dprj».obs ev650 with
    | .run (he230 := hr) (hm229 := hh) (ev236 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self_ce] at hld
      exact absurd (Except.ok.inj hld) (convert_definition_ne_induct_ce conv _)
  | .CPrj (ev800 := ev800) .. =>
    match Obs.«Ingress::get_ci_cprj».obs ev800 with
    | .run (he251 := hr) (hm250 := hh) (ev257 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self_ce] at hld
      exact absurd (Except.ok.inj hld) (convert_constructor_ne_induct_ce conv _)
  | .RPrj (ev896 := ev896) .. =>
    match Obs.«Ingress::get_ci_rprj».obs ev896 with
    | .run (he170 := hr) (hm169 := hh) (ev176 := conv) .. =>
      rw [hr, hh, loadValue_snoc_self_ce] at hld
      exact absurd (Except.ok.inj hld) (convert_recursor_ne_induct_ce conv _)
  | .IPrj (m2 := m2) (x_idx := x_idx) (x_block_addr := x_blk') (cs718 := csi) (v722 := v722)
      (m731 := m731) (cs12 := cs12) (ev14 := ev14) (ev741 := ev741) (ev720 := ev720)
      (hc750 := hc) .. =>
    obtain ⟨-, bytes, c₀, hlen, hh, haddr, hex, -, -, -, -, -, htv, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨⟨idx', blk⟩, hci, hx_idx, hblk_ix⟩ := L1.repConstantInfo_iPrj_inv hinfo
    have hx_idx' : x_idx = TagN.u64Value idx'.toNat := hx_idx
    subst hx_idx'
    obtain ⟨hidx56, hv722, hm731⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 idx') ev741
    subst v722 m731
    obtain ⟨b, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    have hb_eq' : Core.ixAddr b = blk := hb_eq
    obtain ⟨cb, ms, ind, hbl, hmem, nl', ty', np', ni', hld'⟩ := Claim.get_ci_iprj_head hb_rep ev720
    rw [L1.val_cast_u56_ing hidx56] at hmem
    have hv := Except.ok.inj (hld.symm.trans hld')
    injection hv with _ _ hargs
    injection hargs with _ hargs2
    injection hargs2 with _ hargs3
    injection hargs3 with _ hargs4
    injection hargs4 with _ hargs5
    injection hargs5 with hnc_eq hargs6
    injection hargs6 with _ hargs7
    injection hargs7 with hxblk_eq hargs8
    injection hargs8 with hidx_eq _
    subst hxblk_eq hidx_eq
    have hsubi : ∀ x ∈ csi, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hsub12 : ∀ x ∈ cs12, x ∈ calls := by rw [hc]; intro x hx; simp [hx]
    have hbl' : Claim.BlockLoad calls (Core.ixAddr b) cb ms := hbl.mono hsubi
    obtain ⟨bytesB, hszB, -, -, hxB, hinfoB⟩ := hbl
    have hresB := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytesB cb hxB
    have hct_le := Claim.ctors_size_le hinfoB hmem
    refine ⟨⟨bytes.toArray⟩, c₀, ⟨idx', blk⟩, cb, ms, ind,
      by simpa only [ByteArray.size, List.size_toArray] using hlen,
      Core.hashed_mono hsub12 hh, haddr, hex, htv, hci,
      by rw [← hb_eq']; exact hbl', hmem,
      by simpa [Array.length_toList] using hnc_eq, by omega,
      ⟨b, hb_eq', Bytes.repAddressRef_heapMono₂ Core.addrTy ev720.heap_extends hb_rep⟩,
      rfl, hidx56⟩

private theorem rulesTrace_build_reads {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {h₀ : Heap F} {ps : List LevelParam} {Bm : _root_.Address}
    {im : Nat}
    (ht : t.check = .ok ())
    (hself : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (hperm : ps.Perm (List.range ps.length)) :
    ∀ {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {x_rules : SourceValue F},
      L1.RulesTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs tree
        h₀ j root rus x_rules →
      (∀ ru ∈ rus, ∀ rhsP, (exprReader t blob src id self).read ru.rhs = .ok rhsP →
        rhsP.looseBVarsBounded 0 = true ∧ rhsP.allLevelParamsDefined (List.range ps.length) = true) →
      ∃ rules₀ : List (RecRule .anon),
        List.Forall₂
          (RuleReads t (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self) Bm im)
          (rus.zipIdx j) rules₀ ∧
        List.Forall₂ (fun ru rl₀ =>
          rl₀.nfields = ru.fields.toNat ∧
          (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs = .ok rl₀.rhs ∧
          rl₀.rhs.looseBVarsBounded 0 = true ∧
          rl₀.rhs.allLevelParamsDefined ps = true ∧
          rl₀.rhs.hasFvar = false) rus rules₀ := by
  intro j root rus x_rules hrep
  induction hrep with
  | nil _ =>
    intro _
    exact ⟨[], .nil, .nil⟩
  | @cons j root addr rhsPtr rest ru rus plan cell hf raw planned levels rs ih =>
    intro hsc
    obtain ⟨rhsP, hrhsP⟩ := LoadedReads.exprReader_read_ok (t := t) (blob := blob) ht
      (param := id) (self := self) raw hself hblob
    obtain ⟨hlbbP, hdefP⟩ := hsc ru (List.mem_cons_self ..) rhsP hrhsP
    obtain ⟨rhs₀, hrhs₀⟩ := LoadedReads.exprReader_read_ok (t := t) (blob := blob) ht
      (param := Ix.Kernel.Reader.recParam ps) (self := self) raw hself hblob
    have hpos : Core.posOf ps rhs₀ = rhsP :=
      Except.ok.inj ((exprReader_posOf hperm hrhs₀).symm.trans hrhsP)
    have hlbb₀ : rhs₀.looseBVarsBounded 0 = true := by
      have : (Core.posOf ps rhs₀).looseBVarsBounded 0 = true := by rwa [hpos]
      simpa [Core.posOf, Ix.Kernel.Expr.looseBVarsBounded_instantiateLevelParams] using this
    have hdef₀ : rhs₀.allLevelParamsDefined ps = true :=
      Decl.allLevelParamsDefined_of_posOf_perm hperm (by rwa [hpos])
    have hfv₀ : rhs₀.hasFvar = false := exprReader_hasFvar_false hrhs₀
    obtain ⟨rest₀, hrr, hrf⟩ := ih (fun ru' hmem => hsc ru' (List.mem_cons_of_mem _ hmem))
    refine ⟨RecRule.mk (keyOf t (ctorAddr Bm im j)) ru.fields.toNat 0 .inert rhs₀ false false false :: rest₀,
      .cons ⟨rhs₀, hrhs₀, rfl⟩ hrr,
      .cons ⟨rfl, hrhs₀, hlbb₀, hdef₀, hfv₀⟩ hrf⟩

private theorem exprLvEq_stripPis_ce :
    ∀ (n : Nat) {e₁ e₂ : KExpr}, Core.ExprLvEq e₁ e₂ →
      ∀ {bs₁ bs₂ : List (KExpr × Ix.Kernel.BinderMeta)} {r₁ r₂ : KExpr},
        e₁.stripPis n = some (bs₁, r₁) → e₂.stripPis n = some (bs₂, r₂) →
        Core.ExprLvEq r₁ r₂
  | 0, _, _, h, _, _, _, _, h1, h2 => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    rw [← h1.2, ← h2.2]; exact h
  | n + 1, _, _, h, _, _, _, _, h1, h2 => by
    cases h with
    | @forallE d₁ d₂ b₁ b₂ m _ hb =>
      simp only [Expr.stripPis] at h1 h2
      cases hs1 : b₁.stripPis n with
      | none => rw [hs1] at h1; cases h1
      | some p1 =>
        cases hs2 : b₂.stripPis n with
        | none => rw [hs2] at h2; cases h2
        | some p2 =>
          rw [hs1] at h1; rw [hs2] at h2
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1 h2
          rw [← h1.2, ← h2.2]
          exact exprLvEq_stripPis_ce n hb hs1 hs2
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [Expr.stripPis] at h1 h2

private theorem exprLvEq_getAppArgs_length_ce {e₁ e₂ : KExpr} (h : Core.ExprLvEq e₁ e₂) :
    e₁.getAppArgs.length = e₂.getAppArgs.length := by
  induction h with
  | app _ _ ihf _ =>
    simp [Expr.getAppArgs, ihf]
  | bvar | fvar | sort | const | lam | forallE | letE | lit | proj =>
    simp [Expr.getAppArgs]

private theorem rec_major_pins_ni_eq {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {E : KExpr} {ty_ptr r : SourceValue F} {rp ni : F}
    {h h' : Heap F} {cs : List (Call F)}
    {a_maj : _root_.Address} {c_maj cbM : Ixon.Constant} {p_maj : Ixon.InductiveProj}
    {msM : Array Ixon.MutConst} {indM : Ixon.Inductive}
    (ht : t.check = .ok ())
    (hRS : LoadedReads.RunStore calls E₀)
    (hbd : Bounded calls)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hrp : ZMod.val rp < 288230376151711744)
    (hni : ZMod.val ni < 288230376151711744)
    (ev : ObsFn Obs.W "KernelModeled::rec_major_pins" [ty_ptr, .field rp, .field ni] h r h' cs)
    (hE : Decl.TmExact (Core.keyOf t) 0 (fun _ => .sort .zero) h 0 E ty_ptr)
    (hmaj : ∃ bs dom body m lvls,
      E.stripPis (ZMod.val rp + ZMod.val ni) = some (bs, .forallE dom body m) ∧
      dom.getAppFn = .const (Core.keyOf t a_maj) lvls)
    (hrec_M : recordOf E₀ a_maj = some c_maj)
    (hp_maj : c_maj.info = .iPrj p_maj)
    (hrec_cbM : recordOf E₀ p_maj.block = some cbM)
    (hcbM : cbM.info = .muts msM)
    (hmsM : msM.toList[p_maj.idx.toNat]? = some (Ixon.MutConst.indc indM)) :
    ZMod.val ni = indM.indices.toNat ∧
    indM.params.toNat < 72057594037927936 ∧
    ∀ bs' dom' body' m',
      E.stripPis (ZMod.val rp + ZMod.val ni) = some (bs', .forallE dom' body' m') →
      dom'.getAppArgs.length = indM.params.toNat + indM.indices.toNat := by
  match Obs.«KernelModeled::rec_major_pins».obs ev with
  | .run (x_args := x_args) (m141 := m141) (x_inp := x_inp) (cs155 := cs155)
      (op37 := op_mi) (ev14 := ev_peel) (ld51 := ld_fa)
      (ev89 := ev_sp) (ld122 := ld_c) (ev157 := ev_ci) (ld151 := ld_ind)
      (heq245 := heq_ini) (ev270 := ev_len) (op292 := op_add_inp)
      (heq295 := heq_len) (hc424 := hc) .. =>
    have hop_mi : evalBinOp .add (.field rp : SourceValue F) (.field ni) = .ok (.field (rp + ni)) := rfl
    have hv16 : _ = (.field (rp + ni) : SourceValue F) := Except.ok.inj (op_mi.symm.trans hop_mi)
    rw [hv16] at ev_peel
    have hmi_val : ZMod.val (rp + ni) = ZMod.val rp + ZMod.val ni := by
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      rw [ZMod.val_add]
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨bs, rem, hstrip, hrem, rfl⟩ :=
      Decl.peel_n_foralls_exact (ZMod.val rp + ZMod.val ni) hmi_val ev_peel hE
    rw [Nat.zero_add] at hrem
    obtain ⟨dom, body, ℓ_maj, rfl, hdom, _, _⟩ := hrem.forallE_of_load ld_fa
    obtain ⟨hd, sp, H, As, htup, hH, hAs, hdom_eq⟩ := Decl.collect_spine_exact ev_sp hdom
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_ind, lvls_pos, rfl, ra_ind, -⟩ := hH.const_of_load ld_c
    have ha_eq : Core.ixAddr a_ind = a_maj := by
      obtain ⟨bs', dom', body', m', lvls', hstrip', hfn'⟩ := hmaj
      have hrem_eq := Prod.mk.inj (Option.some.inj (hstrip.symm.trans hstrip'))
      injection hrem_eq.2 with hdom_eq' _ _
      have hfn1 : dom.getAppFn = .const (Core.keyOf t (Core.ixAddr a_ind)) lvls_pos := by
        rw [hdom_eq, Ix.Kernel.Expr.getAppFn_mkAppN]; rfl
      rw [hdom_eq', hfn'] at hfn1
      injection hfn1 with hk_eq _
      exact Assembly.keyOf_injective ht hk_eq.symm
    have hsub_ci : ∀ cl ∈ cs155, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨raw_u, c_u, hh_u, haddr_u, hex_u, -, hres_u⟩ :=
      L1.get_ci_block_trace_spec (Core.bounded_sub hsub_ci hbd) ra_ind ev_ci
    have hc_u_eq : c_u = c_maj := by
      rw [ha_eq] at haddr_u
      exact hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hrec_M)
        (Core.hashed_mono hsub_ci hh_u) haddr_u hex_u
    subst hc_u_eq
    unfold L1.GetCIBlockTraceResult at hres_u
    rw [hp_maj] at hres_u
    obtain ⟨-, blk', cb', ms', ind', blobs', tree', plan', v', hhB', haB', hexB', hcb', hms', -, -, -,
      hld', hraw', -⟩ := hres_u
    have hcb'_eq : cb' = cbM :=
      hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hrec_cbM)
        (Core.hashed_mono hsub_ci hhB') haB' hexB'
    subst hcb'_eq
    have hms'_eq : ms' = msM := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hcbM)
    subst hms'_eq
    have hind'_eq : ind' = indM :=
      Ixon.MutConst.indc.inj (Option.some.inj (hms'.symm.trans hmsM))
    subst ind'
    obtain ⟨-, hnp_M, hni_M, -, -, tyPtr', blkPtr', b', -, -, hv', -⟩ := hraw'
    rw [hv'] at hld'
    rw [hld'] at ld_ind
    injection ld_ind with hv_eq
    injection hv_eq with _ _ hf
    injection hf with _ hf2
    injection hf2 with _ hf3
    injection hf3 with hinp_eq hf4
    injection hf4 with hini_eq _
    rw [← hini_eq] at heq_ini
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hval := congrArg ZMod.val (Value.field.inj heq_ini)
    rw [ZMod.val_natCast_of_lt (by omega)] at hval
    have hAs1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ev_ci.heap_extends hAs
    have hAs_lt : As.length < 2 ^ 39 :=
      IxVM.Refinement.RomBound.bounded_length_lt (Core.bounded_sub hsub hbd)
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_args], m141⟩)
        (by rw [hc]; simp) (by simp) hAs1
    obtain ⟨hv257, -⟩ := Decl.tele_klength ev_len hAs1
    rw [← hinp_eq, ← hini_eq] at op_add_inp
    have hop_add : evalBinOp .add (.field (indM.params.toNat : F) : SourceValue F)
        (.field (indM.indices.toNat : F)) =
        .ok (.field ((indM.params.toNat + indM.indices.toNat : Nat) : F)) := by
      simp [evalBinOp, Nat.cast_add]
    have hsum_eq := Except.ok.inj (op_add_inp.symm.trans hop_add)
    rw [hv257, hsum_eq] at heq_len
    have hAs_len : As.length = indM.params.toNat + indM.indices.toNat := by
      have h1 := congrArg ZMod.val (Value.field.inj heq_len)
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
      exact h1
    refine ⟨hval.symm, hnp_M, fun bs' dom' body' m' hstrip' => ?_⟩
    have hrem_eq := Prod.mk.inj (Option.some.inj (hstrip.symm.trans hstrip'))
    injection hrem_eq.2 with hdom_eq' _ _
    rw [← hdom_eq', hdom_eq, Ix.Kernel.Expr.getAppArgs_mkAppN]
    exact hAs_len

/-! ## Extracted member data from `KernelModeled::check_family` -/

/-- **All data extracted from an accepted `KernelModeled::check_family` call for recursor member `k`
of the family record `A` of block `B`**: readings (`Reads`, `RecReads`), canonical annotations
(`canonAnn`, `canonRules`), `ValStored`/`RuleStored`, `letFree`, self-reference exclusion,
non-`forallE` motive conclusion, major-premise pins with `hasBVarIn` bounds, and a
`ConstantValCheckJ twinPosRulesJ` front-door factory at any environment storing `A`'s references. -/
structure ExtractedTwinMember (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (lim : Option Nat) (B A : _root_.Address) (cb c : Ixon.Constant)
    (ms rs' : Array Ixon.MutConst) (ind₀ : Ixon.Inductive) (k : Nat) where
  rc : Ixon.Recursor
  hmem : rs'[k]? = some (.recr rc)
  hk_false : rc.k = false
  huns_false : rc.isUnsafe = false
  hrnp : rc.params.toNat = ind₀.params.toNat
  hnmot : rc.motives.toNat = rs'.size
  off : Nat
  hoff : off = 0 ∨ off = 1
  hlvls_eq : rc.lvls.toNat = ind₀.lvls.toNat + off
  ps : List LevelParam
  hps_eq : ps = Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind₀.lvls.toNat + 1))
    (List.range ind₀.lvls.toNat)
  hps_len : ps.length = rc.lvls.toNat
  hps_perm : ps.Perm (List.range ps.length)
  a_maj : _root_.Address
  p_maj : Ixon.InductiveProj
  indM : Ixon.Inductive
  ty₀ : KExpr
  ty' : KExpr
  rules₀ : List (RecRule .anon)
  rls : List (RecRule .anon)
  ci₀ : ConstantInfo .anon
  hci₀ : ci₀ = .recInfo ⟨keyOf t (Core.rprjAddr A k), ps, ty₀⟩
    (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
    (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀
  hreads : Reads t E₀ (Core.rprjAddr A k) ci₀
  hrecReads : RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) c (blockSelf t A rs')
    (keyOf t (Core.rprjAddr A k)) rc ci₀
  hmajKey : majorKey rc (Core.posOf ps ty₀) = some (keyOf t a_maj)
  hindKey_M : IndKeyAt t (recordOf E₀) (keyOf t a_maj) p_maj.block p_maj.idx.toNat indM
  hni_eq : rc.indices.toNat = indM.indices.toNat
  hrules_size : rc.rules.size = indM.ctors.size
  hctor_params : ∀ (c_idx : Nat) (ct : Ixon.Constructor),
    indM.ctors[c_idx]? = some ct → ct.params.toNat = indM.params.toNat
  hmajor_np : ∀ bs dom body m,
    (Core.posOf ps ty').stripPis
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) =
        some (bs, .forallE dom body m) →
    dom.getAppArgs.length = indM.params.toNat + rc.indices.toNat
  hty_read : (exprReader t (fun x => E₀.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
    (blockSelf t A rs')).read rc.typ = .ok ty₀
  hty_lbb : ty₀.looseBVarsBounded 0 = true
  hty_def : ty₀.allLevelParamsDefined ps = true
  hty_fv : ty₀.hasFvar = false
  hcanonTy : LoadedReads.canonAnn c ps (mutsRoot rs' k) rc.typ ty₀ = some ty'
  hty'_letFree : letFree ty' = true
  hvalStored : ValStored ⟨keyOf t (Core.rprjAddr A k), ps, ty'⟩
    ⟨keyOf t (Core.rprjAddr A k), ps, ty₀⟩
  hrules_read : List.Forall₂ (fun ru rl₀ =>
    rl₀.nfields = ru.fields.toNat ∧
    (exprReader t (fun x => E₀.blobs.get? x) c (Ix.Kernel.Reader.recParam ps)
      (blockSelf t A rs')).read ru.rhs = .ok rl₀.rhs ∧
    rl₀.rhs.looseBVarsBounded 0 = true ∧
    rl₀.rhs.allLevelParamsDefined ps = true ∧
    rl₀.rhs.hasFvar = false) rc.rules.toList rules₀
  hcanonRules : LoadedReads.canonRules c ps rc.k rc.params.toNat (mutsRoot rs' k + 1)
    rc.rules.toList rules₀ = some rls
  hruleStored : List.Forall₂ RuleStored rls rules₀
  hrls_letFree : ∀ rl ∈ rls, letFree rl.rhs = true
  hnoSelf : ∀ j < rs'.size, ty'.mentionsConst (keyOf t (Core.rprjAddr A j)) = false
  hnoRole : ∀ ro : Ix.Kernel.Role, keyOf t (Core.rprjAddr A k) ≠ .role ro
  hmotiveConcl : ∃ bs concl,
    (Core.posOf ps ty').stripPis
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat + 1) =
        some (bs, concl) ∧
    ∀ d b m, concl ≠ .forallE d b m
  hmajorPins : ∃ (a_ind : _root_.Address) (inp : Nat)
    (bs : List (KExpr × Ix.Kernel.BinderMeta)) (dom body : KExpr)
    (m_maj : Ix.Kernel.BinderMeta) (lvls_pos : List KLevel) (As : List KExpr),
    (Core.posOf ps ty').stripPis
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) =
        some (bs, .forallE dom body m_maj) ∧
    dom.getAppFn = .const (keyOf t a_ind) lvls_pos ∧
    dom.getAppArgs = As ∧
    As.length = inp + rc.indices.toNat ∧
    As.drop inp = (List.range rc.indices.toNat).map (fun m => .bvar (rc.indices.toNat - 1 - m)) ∧
    (∀ P ∈ As.take inp,
      Binding.FamilyFlat.hasBVarIn 0
        (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) P = false)
  hfrontDoor : ∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon),
    StepStore calls t E₀ E →
    Decl.PrefixInv.{u} E t lim env →
    (∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x) →
    env.find? (keyOf t (Core.rprjAddr A k)) = none →
    Decl.KeyFree (keyOf t (Core.rprjAddr A k)) →
    ConstantValCheckJ twinPosRulesJ env
      ⟨keyOf t (Core.rprjAddr A k), ps, ty₀⟩
      ⟨keyOf t (Core.rprjAddr A k), ps, ty'⟩
  hrule_nfields : ∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon),
    StepStore calls t E₀ E →
    Decl.PrefixInv.{u} E t lim env →
    ∀ (c_idx : Nat) (ru : Ixon.RecursorRule), rc.rules[c_idx]? = some ru →
      ∀ cvj cnP cnF,
        env.find? (keyOf t (Core.cprjAddr p_maj.block p_maj.idx.toNat c_idx)) =
          some (.ctorInfo cvj cnP cnF) →
        ru.fields.toNat = cnF
  hloaded_at_env : ∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon),
    StepStore calls t E₀ E →
    Decl.PrefixInv.{u} E t lim env →
    ∀ cv mI' rP' rls',
      env.find? (keyOf t (Core.rprjAddr A k)) = some (.recInfo cv mI' rP' rls') →
      mI' = rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat ∧
      rP' = rc.params.toNat + rc.motives.toNat + rc.minors.toNat ∧
      cv.levelParams.length = rc.lvls.toNat ∧
      Core.ExprLvEq (Core.posOf cv.levelParams cv.type) (Core.posOf ps ty') ∧
      List.Forall₂ (fun rl_e rl_c =>
        rl_e.nfields = rl_c.nfields ∧
        Core.ExprLvEq (Core.posOf cv.levelParams rl_e.rhs) (Core.posOf ps rl_c.rhs)) rls' rls

private theorem canonRules_letFree {src : Ixon.Constant} {ps : List LevelParam}
    {kFlag : Bool} {cParams : Nat} :
    ∀ {root : F} {rus : List Ixon.RecursorRule} {rules₀ rls : List (RecRule .anon)},
      LoadedReads.canonRules src ps kFlag cParams root rus rules₀ = some rls →
      ∀ rl ∈ rls, letFree rl.rhs = true
  | _, [], [], _, h, rl, hmem => by
    simp [LoadedReads.canonRules] at h
    subst h; cases hmem
  | _, [], _ :: _, _, h, _, _ => by simp [LoadedReads.canonRules] at h
  | _, _ :: _, [], _, h, _, _ => by simp [LoadedReads.canonRules] at h
  | root, ru :: rus, rl₀ :: rules₀, rls, h, rl, hmem => by
    unfold LoadedReads.canonRules at h
    cases ha : LoadedReads.canonAnn src ps root ru.rhs rl₀.rhs with
    | none => rw [ha] at h; cases h
    | some rhs' =>
      rw [ha] at h
      simp only [Option.bind_some] at h
      cases hr : LoadedReads.canonRules src ps kFlag cParams (root + 1) rus rules₀ with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact letFree_of_canonAnn ha
        · exact canonRules_letFree hr rl hmem'

private theorem check_recs_extract {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ E_in : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {B A : _root_.Address} {cb c : Ixon.Constant} {ms rs' : Array Ixon.MutConst}
    {ind₀ : Ixon.Inductive} {off : Nat}
    {typeAs recAs : List Bytes.Address} {t0 : Bytes.Address} {typeRest : List Bytes.Address}
    {x_rc x_type_addrs x_fam x_src x_dst x_aset : SourceValue F} {h₀ : Heap F}
    (ht : t.check = .ok ())
    (hRS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hShape : TableShape.{u} t G R envT)
    (hRF : RecordsFor R E_in)
    (hSS_in : StepStore calls t E₀ E_in)
    (hLim : LimWithin G t lim)
    (hB : FamBlockRecord E₀ B cb ms) (hA : FamRecRecord E₀ A c rs')
    (hc_res : c.resourceSize < 8589934592)
    (hms0 : ms[0]? = some (.indc ind₀))
    (hind0_params : ind₀.params.toNat < 72057594037927936)
    (hind0_lvls : ind₀.lvls.toNat < 4294967296)
    (hoff : off = 0 ∨ off = 1)
    (hrefs_ok : ∀ x, UsedRef E₀ A x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x)
    (hrc_lim : Claim.RCLimRep t bAddr lim h₀ x_rc)
    (htypes_eq : typeAs = t0 :: typeRest) (ht0_addr : Core.ixAddr t0 = Core.iprjAddr B 0)
    (htype_rep : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h₀ typeAs x_type_addrs)
    (hfam_rep : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h₀ recAs x_fam)
    (hrecAs_map : recAs.map Core.ixAddr =
      rs'.toList.mapIdx (fun i m => memberAddr A i m))
    (hrecAs_len : recAs.length = rs'.size)
    (hnoRole_all : ∀ j < rs'.size, ∀ ro : Ix.Kernel.Role,
      keyOf t (Core.rprjAddr A j) ≠ .role ro) :
    ∀ {k : Nat} {remAs : List Bytes.Address} {x_recs x_models x_s x_form r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      remAs = recAs.drop k →
      Heap.Extends h₀ h →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h remAs x_recs →
      ObsFn Obs.W "KernelModeled::check_recs"
        [x_rc, x_type_addrs, x_recs, x_models, x_src, x_dst, x_aset, x_s,
          .field (rs'.size : F), .field (k : F), .field (ind₀.params.toNat : F),
          .field (off : F), .field (ind₀.lvls.toNat : F), x_fam, x_form] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, k ≤ j → j < rs'.size →
        Nonempty (ExtractedTwinMember.{u} calls t E₀ lim B A cb c ms rs' ind₀ j) := by
  intro k remAs
  induction remAs generalizing k with
  | nil =>
    intro _ _ _ _ _ _ _ _ hdrop _ _ _ _ j hkj hj
    have hlen : (recAs.drop k).length = 0 := by rw [← hdrop]; rfl
    simp only [List.length_drop, hrecAs_len] at hlen
    omega
  | cons a_k rest_as ih =>
    intro x_recs x_models x_s x_form r h h' cs hdrop hext hrep_recs ev hsub j hkj hj
    have hk_lt : k < rs'.size := by omega
    have ha_k_eq : recAs[k]? = some a_k := by
      have h1 : (recAs.drop k)[0]? = some a_k := by rw [← hdrop]; rfl
      simpa [List.getElem?_drop] using h1
    have hrest_eq : rest_as = recAs.drop (k + 1) := by
      have h1 := congrArg List.tail hdrop
      simpa [List.tail_drop] using h1
    match Obs.«KernelModeled::check_recs».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Lib.rep_nil_of_load hrep_recs ld12
    | .Cons (x_r := x_r) (x_rest := x_rest) (x_rm := x_rm) (x_mrest := x_mrest)
        (m67 := m67) (p74 := p74) (cs80 := cs80)
        (x_nl := x_nl) (x_ty := x_ty) (x_rnp := x_rnp) (x_ni := x_ni)
        (x_nmot := x_nmot) (x_nmin := x_nmin) (x_rules := x_rules)
        (x_kf := x_kf) (x_r_uns := x_r_uns) (w107 := w107) (w108 := w108)
        (m288 := m288) (m349 := m349) (m335 := m335) (m391 := m391) (m473 := m473)
        (m511 := m511) (m561 := m561) (m_oajaqiwd := m_oaj) (m_obmhbjvc := m_obm)
        (m_shkxqcak := m_shk) (m_raxeqbbt := m_rax) (m_yfwcpmwj := m_yfw)
        (m_cjjqtxxk := m_cjj) (m_tsdchhaz := m_tsd) (m_akkqvxxx := m_akk) (m627 := m627)
        (m596 := m596) (m640 := m640) (m669 := m669) (m698 := m698)
        (m_pipdqnib := m_pip) (m_pzqbkmwo := m_pzq) (m838 := m838) (m892 := m892)
        (v405 := v405) (v406 := v406) (v_czbmphqy := v_czb) (x_pins := x_pins)
        (v_lywxstel := v_lyw) (v697 := v697) (p_luqvxdfx := p_luq)
        (v_orhmbogm := v_orh) (v_lawpuqwl := v_law) (v891 := v891)
        (v909 := v909) (v1026 := v1026)
        (cs401 := cs401) (cs483 := cs483) (cs521 := cs521) (cs569 := cs569)
        (cs_hmmloamm := cs_hmm) (cs_fsttxebm := cs_fst) (cs_dsvkbvxt := cs_dsv)
        (cs_gbkzevef := cs_gbk) (cs_sblvzaks := cs_sbl) (cs_kxcowfqz := cs_kxc)
        (cs606 := cs606) (cs650 := cs650) (cs679 := cs679) (cs708 := cs708)
        (cs_vkeoeyff := cs_vke) (cs_fcqxjgjw := cs_fcq) (cs848 := cs848)
        (cs902 := cs902) (cs1014 := cs1014)
        (ld12 := ld12) (ev82 := ev82) (ld76 := ld76)
        (heq190 := heq190) (heq217 := heq217) (heq245 := heq245) (heq273 := heq273)
        (ev298 := ev298) (ev359 := ev359) (ev345 := ev345)
        (op451 := op451) (op443 := op443) (op435 := op435) (op427 := op427) (op469 := op469)
        (ev403 := ev403) (ev485 := ev485) (ev523 := ev523) (ev571 := ev571) (heq594 := heq594)
        (hm_odcsfbbr := hm_oaj) (ev_uprevpxl := ev_up) (ev_svgicqcr := ev_sv)
        (hm_owdmgqhw := hm_rax) (ev_oqkxxxxs := ev_oq) (ev_eejlfykm := ev_ee)
        (op_eindxttr := op_ein) (op_smkbhtsz := op_smk) (ev_uoyvrvop := ev_uoy)
        (op_dynlujbu := op_dyn) (ev_akrqpecc := ev_akr)
        (hm635 := hm635) (ev608 := ev608) (ev652 := ev652) (ev681 := ev681)
        (ev710 := ev710) (ev_uoummlhs := ev_uou) (ld_memczquv := ld_mem)
        (ev_tjosvhyt := ev_tjo) (ev850 := ev850)
        (op965 := op965) (op957 := op957) (ev904 := ev904)
        (op1107 := op1107) (ev1016 := ev1016) (hc1137 := hcs) .. =>
      obtain ⟨a_k', rest_as', hcons, ha_k_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrep_recs ld12
      injection hcons with h1 h2; subst h1 h2
      -- Heap extension chain across the loop body
      have ext_m67_m288 : Heap.Extends m67 m288 := ev298.heap_extends
      have ext_m67_m335 : Heap.Extends m67 m335 :=
        ext_m67_m288.trans (ev359.heap_extends.trans ev345.heap_extends)
      have ext_m67_m391 : Heap.Extends m67 m391 := ext_m67_m335.trans ev403.heap_extends
      have ext_m67_m473 : Heap.Extends m67 m473 := ext_m67_m391.trans ev485.heap_extends
      have ext_m67_m511 : Heap.Extends m67 m511 := ext_m67_m473.trans ev523.heap_extends
      have ext_m67_m561 : Heap.Extends m67 m561 := ext_m67_m511.trans ev571.heap_extends
      have ext_m561_m_oaj : Heap.Extends m561 m_oaj := by rw [hm_oaj]; exact ⟨_, rfl⟩
      have ext_m_shk_m_rax : Heap.Extends m_shk m_rax := by rw [hm_rax]; exact ⟨_, rfl⟩
      have ext_m67_m_cjj : Heap.Extends m67 m_cjj :=
        ext_m67_m561.trans (ext_m561_m_oaj.trans (ev_up.heap_extends.trans
          (ev_sv.heap_extends.trans (ext_m_shk_m_rax.trans (ev_oq.heap_extends.trans ev_ee.heap_extends)))))
      have ext_m67_m_tsd : Heap.Extends m67 m_tsd := ext_m67_m_cjj.trans ev_uoy.heap_extends
      have ext_m67_m_akk : Heap.Extends m67 m_akk := ext_m67_m_tsd.trans ev_akr.heap_extends
      have ext_m_akk_m627 : Heap.Extends m_akk m627 := by rw [hm635]; exact ⟨_, rfl⟩
      have ext_m67_m627 : Heap.Extends m67 m627 := ext_m67_m_akk.trans ext_m_akk_m627
      have ext_m67_m669 : Heap.Extends m67 m669 :=
        ext_m67_m627.trans (ev608.heap_extends.trans (ev652.heap_extends.trans ev681.heap_extends))
      have ext_m67_m698 : Heap.Extends m67 m698 := ext_m67_m669.trans ev710.heap_extends
      have ext_m67_m_pip : Heap.Extends m67 m_pip := ext_m67_m698.trans ev_uou.heap_extends
      have ext_m67_m838 : Heap.Extends m67 m838 :=
        ext_m67_m_pip.trans (ev_tjo.heap_extends.trans ev850.heap_extends)
      have ext_h_m892 : Heap.Extends h m892 :=
        ev82.heap_extends.trans (ext_m67_m838.trans ev904.heap_extends)
      by_cases hjk : j = k
      · subst j
        -- Member `k` is a recursor `rc` of `A`
        have hk_get : rs'[k]? = some (rs'[k]'hk_lt) := getElem?_pos rs' k hk_lt
        have hmem_list : rs'[k]'hk_lt ∈ rs'.toList :=
          List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk_get)
        obtain ⟨rc, hrc_eq⟩ := hA.recrs _ hmem_list
        have hmem_k : rs'[k]? = some (.recr rc) := by rwa [hrc_eq] at hk_get
        -- Address `a_k` equals `Core.rprjAddr A k`
        have ha_k_ix : Core.ixAddr a_k = Core.rprjAddr A k := by
          have h1 : (recAs.map Core.ixAddr)[k]? = some (Core.ixAddr a_k) := by
            rw [List.getElem?_map, ha_k_eq]; rfl
          rw [hrecAs_map, List.getElem?_mapIdx, Array.getElem?_toList, hmem_k] at h1
          exact Option.some.inj h1.symm
        have hproj_k : recordOf E₀ (Core.ixAddr a_k) = some (memberProjection A k (.recr rc)) := by
          rw [ha_k_ix]
          exact hA.members k (.recr rc) hmem_k
        have hgood_in : Core.Good ⟨E_in, default, t, lim⟩ calls := hSS_in.good default lim
        have hbound : Bounded calls := hgood_in.2
        have hsub80 : ∀ cl ∈ cs80, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        -- Unpack `ev82 : Ingress::get_ci [x_r]` via `L1.get_ci_block_trace_spec`
        obtain ⟨rawBytes, c_proj, hh_proj, haddr_proj, hex_proj, -, hres_proj⟩ :=
          L1.get_ci_block_trace_spec (hgood_in.sub hsub80).2 ha_k_rep ev82
        have hrec0_proj : Ix.Cert.recordAt E₀ (Core.ixAddr a_k) = some (memberProjection A k (.recr rc)) :=
          (hRS.recordOf_eq_recordAt _).symm.trans hproj_k
        have hc_proj_eq : c_proj = memberProjection A k (.recr rc) :=
          hRS.record_eq hrec0_proj (Core.hashed_mono hsub80 hh_proj) haddr_proj hex_proj
        subst hc_proj_eq
        unfold L1.GetCIBlockTraceResult at hres_proj
        have hproj_info : (memberProjection A k (.recr rc)).info = .rPrj ⟨k.toUInt64, A⟩ := rfl
        rw [hproj_info] at hres_proj
        obtain ⟨hk56, blkBytes, cb_a, rs_a, rc_a, blobs_a, tree_a, v_a,
          hh_blk, ha_blk, hex_blk, hcb_a, hrs_a, hhp_a, hbuilt_a, hld_a, htr_a⟩ := hres_proj
        have hk_lt_res : rs'.size ≤ c.resourceSize := by
          have h1 : rs'.toList.length ≤ (rs'.toList.map Ixon.MutConst.resourceSize).sum :=
            length_le_sum_map_ce Ixon.MutConst.resourceSize (fun m => by
              cases m <;> dsimp [Ixon.MutConst.resourceSize] <;> omega) rs'.toList
          have h2 : c.info.resourceSize = 1 + (rs'.toList.map Ixon.MutConst.resourceSize).sum := by
            rw [hA.muts]; rfl
          have h3 : c.info.resourceSize ≤ c.resourceSize := by
            dsimp [Ixon.Constant.resourceSize]; omega
          simp only [Array.length_toList] at h1
          omega
        have hk64 : k.toUInt64.toNat = k := by
          change (UInt64.ofNat k).toNat = k
          rw [UInt64.toNat_ofNat']
          exact Nat.mod_eq_of_lt (by omega)
        have hrec0_A : Ix.Cert.recordAt E₀ A = some c :=
          (hRS.recordOf_eq_recordAt A).symm.trans hA.record
        have hcb_a_eq : cb_a = c :=
          hRS.record_eq hrec0_A (Core.hashed_mono hsub80 hh_blk) ha_blk hex_blk
        subst cb_a
        have hrs_a_eq : rs_a = rs' := Ixon.ConstantInfo.muts.inj (hcb_a.symm.trans hA.muts)
        subst rs_a
        rw [hk64, Array.getElem?_toList] at hrs_a
        have hrc_a_eq : rc_a = rc :=
          Ixon.MutConst.recr.inj (Option.some.inj (hrs_a.symm.trans hmem_k))
        subst rc_a
        rw [hk64] at htr_a
        obtain ⟨hlvls_lt, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, b_a, planT,
          hb_a_eq, hb_a_rep, hv_a, rty, hplanT, hlevelsT, hrules_tr⟩ := htr_a
        rw [hv_a] at hld_a
        rw [hld_a] at ld76
        injection ld76 with hv_eq
        injection hv_eq with _ _ hfields
        simp only [List.cons.injEq, and_true] at hfields
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfields
        -- `rc.k = false`, `rc.isUnsafe = false`, `rc.params = ind₀.params`, `rc.motives = rs'.size`
        have hk_false : rc.k = false := by
          cases hk_b : rc.k with
          | false => rfl
          | true =>
            rw [hk_b] at heq190
            exact absurd heq190.symm zero_ne_one_ce
        have huns_false : rc.isUnsafe = false := by
          cases hu_b : rc.isUnsafe with
          | false => rfl
          | true =>
            rw [hu_b] at heq217
            exact absurd heq217.symm zero_ne_one_ce
        have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
        have hrnp : rc.params.toNat = ind₀.params.toNat := by
          have h1 := congrArg ZMod.val (Value.field.inj heq245)
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
          exact h1
        have hnmot : rc.motives.toNat = rs'.size := by
          have h1 := congrArg ZMod.val (Value.field.inj heq273)
          have hsz_le := Claim.muts_size_le hA.muts
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
          exact h1
        -- Blob agreement for `E₀`
        have hblob_a : ∀ x bs, (x, bs) ∈ blobs_a → E₀.blobs.get? x = some bs := by
          intro x bs hm
          obtain ⟨hhx, hxa⟩ := hhp_a (x, bs) hm
          have hrun := hRS.blobs bs (Core.hashed_mono hsub80 hhx)
          rwa [hxa] at hrun
        -- Read `rc.typ` at positional level parameters `id`
        obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
          (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := blockSelf t A rs')
          rty (fun i x hx => by simp at hx) hblob_a
        have hcl_ws : (⟨"KernelCheck::validate_expr_well_scoped",
            [tyPtr, .field 0, .field (rc.lvls.toNat : F)], m473⟩ : Call F) ∈ calls :=
          hsub _ (by rw [hcs]; simp)
        obtain ⟨-, htyP_lbb, htyP_def⟩ := Assembly.validate_expr_well_scoped_spec
          (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := blockSelf t A rs')
          hbound hlvls_lt rty ext_m67_m473 htyP ev523 hcl_ws
        have hrd_tyP : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
            (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
            (blockSelf t A rs')).read rc.typ = .ok tyP := by
          rw [Assembly.recParam_range]; exact htyP
        -- Raw syntax `R'` and positional canonical annotation `E_pos` of `rc.typ`
        obtain ⟨R', E_pos, hann_pos, hraw_ty, -, hrawTr_ty⟩ := rty.toRawTmCExactTrace (κ := Core.keyOf t)
          (ps := List.range rc.lvls.toNat) (by simp) (by simpa using hlvls_lt)
          (LoadedReads.readCtx_keyAt_inv ht _) (fun i x m k hx => by simp at hx) hblob_a
          hrd_tyP htyP_lbb htyP_def
        have hshape_ty : RawShape tyP R' := rawShape_of_rawTrace tyP (hrawTr_ty planT hlevelsT [])
        have hraw0 := hraw_ty 0 (fun _ => .sort .zero)
        simp only [Decl.posOf_range] at hraw0
        -- 1. `familyKey rc tyP = some (keyOf t (Core.iprjAddr B 0))` from `ev485 : check_carriers`
        have htype_m391 : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m391
            (t0 :: typeRest) x_type_addrs := by
          rw [← htypes_eq]
          exact repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
            (hext.trans (ev82.heap_extends.trans ext_m67_m391)) htype_rep
        have hfamKey_R : familyKey rc R' = some (Core.keyOf t (Core.ixAddr t0)) :=
          check_carriers_rawTm_familyKey hp56 (hraw0.toRawTm.mono ext_m67_m391) htype_m391 ev485
        have hfamKey_tyP : familyKey rc tyP = some (keyOf t (Core.iprjAddr B 0)) := by
          rw [familyKey_eq_of_rawShape hshape_ty, hfamKey_R, ht0_addr, LoadedReads.keyOf_eq]
        -- `IndKeyAt` for `B` member 0 (`ind₀`)
        have hind0_proj : recordOf E₀ (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind₀)) :=
          hB.members 0 (.indc ind₀) hms0
        have hindKey_F : IndKeyAt t (recordOf E₀) (keyOf t (Core.iprjAddr B 0)) B 0 ind₀ :=
          ⟨Core.iprjAddr B 0, memberProjection B 0 (.indc ind₀), ⟨(0 : Nat).toUInt64, B⟩, cb, ms,
            rfl, hind0_proj, rfl, rfl, rfl,
            ⟨hB.record, hB.muts, hms0, rfl, rfl, hB.logic⟩⟩
        -- 2. `majorKey rc tyP = some (keyOf t (Core.ixAddr a_maj))` from `ev710 : rec_to_parent_addr`
        obtain ⟨rbs_m, Rd_m, Rb_m, mR_m, a_maj, us_m, hstrip_m, hhead_m, ha_maj_rep⟩ :=
          rec_to_parent_addr_rawTm_addr (hraw0.toRawTm.mono ext_m67_m669) ev710
        have hsum_mI : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) +
            (rc.minors.toNat : F) + (rc.indices.toNat : F)) =
            rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
          rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
          exact ZMod.val_natCast_of_lt (by omega)
        rw [hsum_mI] at hstrip_m
        have hmajKey_R : majorKey rc R' = some (Core.keyOf t (Core.ixAddr a_maj)) := by
          unfold majorKey binderDom headKey
          rw [hstrip_m]
          simp only [Option.bind_some, hhead_m]
        have hmajKey_tyP : majorKey rc tyP = some (keyOf t (Core.ixAddr a_maj)) := by
          rw [majorKey_eq_of_rawShape hshape_ty, hmajKey_R, LoadedReads.keyOf_eq]
        -- 3. `ev_uou : Ingress::get_ci [v697]` and `ev904 : check_rules` give `IndKeyAt` for `a_maj`,
        --    rule out `check_recursor_canonical_at.other`, and give `rc.lvls = ind₀.lvls + off` & `rc.rules.size = indM.ctors.size`
        have hsub_uou : ∀ cl ∈ cs_vke, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        -- First inspect `ev904 : check_rules` to know `a_maj` is an inductive projection!
        have hsub_rules : ∀ cl ∈ cs902, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        -- Extract `a_ind_r`, `indM` from `ev904 : check_rules`
        match Obs.«KernelModeled::check_rules».obs ev904 with
        | .run (x_iaddr := x_iaddr) (x_inp := x_cr_inp) (x_inct := x_inct) (x_iblock := x_iblock)
            (x_iidx := x_iidx) (m2 := m_cr2) (m58 := m_cr58)
            (m147 := m_cr147) (cs12 := cs_cr12) (cs72 := cs_cr72) (cs177 := cs_cr177)
            (ev14 := ev_cr_pins) (ev74 := ev_cr_ci) (ld68 := ld_cr_ind)
            (ev157 := ev_cr_len) (heq173 := heq_cr_len) (ev179 := ev_cr_go) (hc315 := hcs_cr) .. =>
          -- `v909 = rc.params + rc.motives + rc.minors`
          have hv909_eq : v909 = .field ((rc.params.toNat + rc.motives.toNat + rc.minors.toNat : Nat) : F) := by
            simp only [evalBinOp, Except.ok.injEq] at op965
            rw [← op965] at op957
            simp only [evalBinOp, Except.ok.injEq] at op957
            rw [← op957, Nat.cast_add, Nat.cast_add]
          rw [hv909_eq] at ev_cr_pins
          have hrp_lt : ZMod.val ((rc.params.toNat + rc.motives.toNat + rc.minors.toNat : Nat) : F) <
              288230376151711744 := by
            rw [ZMod.val_natCast_of_lt (by omega)]; omega
          have hni_lt : ZMod.val (rc.indices.toNat : F) < 288230376151711744 := by
            rw [ZMod.val_natCast_of_lt (by omega)]; omega
          have hsub_cr12 : ∀ cl ∈ cs_cr12, cl ∈ calls :=
            fun cl hcl => hsub_rules cl (by rw [hcs_cr]; simp [hcl])
          have hsub_cr72 : ∀ cl ∈ cs_cr72, cl ∈ calls :=
            fun cl hcl => hsub_rules cl (by rw [hcs_cr]; simp [hcl])
          have hsub_cr177 : ∀ cl ∈ cs_cr177, cl ∈ calls :=
            fun cl hcl => hsub_rules cl (by rw [hcs_cr]; simp [hcl])
          obtain ⟨iaddr_r, ilvls_r, pins_r, a_ind_r, inp_r, bs_r, dom_r, body_r, mmaj_r,
            lvls_r, As_r, htup_r, ha_ind_r, -, hstrip_r, hfn_r, -, -, -, -, -, -, -⟩ :=
            Decl.rec_major_pins_spec_wide (hgood_in.sub hsub_cr12).2 hrp_lt hni_lt ev_cr_pins
              (hraw0.toTmExact.mono ext_m67_m838)
          injection htup_r with htup_r'
          injection htup_r' with hiaddr_eq _
          subst hiaddr_eq
          -- `a_ind_r` and `a_maj` have the same address!
          have hstrip_r' : E_pos.stripPis (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
              rc.indices.toNat) = some (bs_r, .forallE dom_r body_r mmaj_r) := by
            have h1 : ZMod.val ((rc.params.toNat + rc.motives.toNat + rc.minors.toNat : Nat) : F) +
                ZMod.val (rc.indices.toNat : F) =
                rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
              rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
            rwa [h1] at hstrip_r
          have hmaj_pos : majorKey rc E_pos = some (Core.keyOf t (Core.ixAddr a_ind_r)) := by
            unfold majorKey binderDom headKey
            rw [hstrip_r']
            simp only [Option.bind_some, hfn_r]
          have hmaj_ann : majorKey rc E_pos = majorKey rc tyP :=
            majorKey_of_annotates hmajKey_tyP hann_pos |>.trans hmajKey_tyP.symm
          have hkey_maj_eq : Core.keyOf t (Core.ixAddr a_ind_r) = Core.keyOf t (Core.ixAddr a_maj) := by
            have h1 := hmaj_pos.symm.trans (hmaj_ann.trans hmajKey_tyP)
            exact Option.some.inj (by simpa [LoadedReads.keyOf_eq] using h1)
          have ha_maj_eq : Core.ixAddr a_ind_r = Core.ixAddr a_maj :=
            Assembly.keyOf_injective ht hkey_maj_eq
          -- Unpack `ev_cr_ci : Ingress::get_ci [x_iaddr]` via `get_ci_induct_at`
          obtain ⟨rawM, c_maj, p_maj, cbM, msM, indM, hszM, hh_M, haddr_M, hex_M, htv_M, hp_maj,
            hblM, hmsM, hx_inct_eq, hindM_ctors_lt, ⟨bM_blk, hbM_blk_ix, hbM_blk_rep⟩,
            hx_iidx_eq, hp_maj_idx_lt⟩ := get_ci_induct_at ha_ind_r ev_cr_ci ld_cr_ind
          subst hx_inct_eq hx_iidx_eq
          have hrec_M : recordOf E₀ (Core.ixAddr a_ind_r) = some c_maj := by
            rw [← haddr_M]
            exact Claim.recordOf_of_hashed hH (Core.hashed_mono hsub_cr72 hh_M) hszM hex_M
          obtain ⟨hrec_cbM, hcbM⟩ := (hblM.mono hsub_cr72).stored hH
          have hx_cr_inp_eq : x_cr_inp = .field (indM.params.toNat : F) := by
            obtain ⟨rawM2, c_m2, hhM2, haM2, hexM2, -, hresM2⟩ :=
              L1.get_ci_block_trace_spec (hgood_in.sub hsub_cr72).2 ha_ind_r ev_cr_ci
            have hcm2_eq : c_m2 = c_maj :=
              hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hrec_M)
                (Core.hashed_mono hsub_cr72 hhM2) haM2 hexM2
            subst c_m2
            unfold L1.GetCIBlockTraceResult at hresM2
            rw [hp_maj] at hresM2
            obtain ⟨-, blk2, cb2, ms2, ind2, _, _, _, v2, hhB2, haB2, hexB2, hcb2, hms2, -, -, -,
              hld2, hraw2, -⟩ := hresM2
            have hcb2_eq : cb2 = cbM :=
              hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hrec_cbM)
                (Core.hashed_mono hsub_cr72 hhB2) haB2 hexB2
            subst cb2
            have hms2_eq : ms2 = msM := Ixon.ConstantInfo.muts.inj (hcb2.symm.trans hcbM)
            subst ms2
            have hind2_eq : ind2 = indM :=
              Ixon.MutConst.indc.inj (Option.some.inj (hms2.symm.trans hmsM))
            subst ind2
            obtain ⟨-, -, -, -, -, _, _, _, -, -, hv2, -⟩ := hraw2
            rw [hv2] at hld2
            rw [hld2] at ld_cr_ind
            injection ld_cr_ind with hv_eq
            injection hv_eq with _ _ hf
            injection hf with _ hf2
            injection hf2 with _ hf3
            injection hf3 with hinp2_eq _
            exact hinp2_eq.symm
          subst hx_cr_inp_eq
          obtain ⟨hni_eq', hindM_np, hdom_Epos_len⟩ :=
            rec_major_pins_ni_eq ht hRS hbound hsub_cr12 hrp_lt hni_lt ev_cr_pins
              (hraw0.toTmExact.mono ext_m67_m838)
              ⟨bs_r, dom_r, body_r, mmaj_r, lvls_r, hstrip_r, hfn_r⟩
              hrec_M hp_maj hrec_cbM hcbM hmsM
          have hni_eq : rc.indices.toNat = indM.indices.toNat := by
            rwa [ZMod.val_natCast_of_lt (by omega)] at hni_eq'
          -- `rc.rules.size = indM.ctors.size`
          have hlen_rules := rule_list_length_eq hrules_tr
            (ext_m67_m838.trans (ev_cr_pins.heap_extends.trans ev_cr_ci.heap_extends)) ev_cr_len
          rw [hlen_rules] at heq_cr_len
          have hrules_size_eq : rc.rules.size = indM.ctors.size := by
            have h1 := congrArg ZMod.val (Value.field.inj heq_cr_len)
            have hr_le := rules_size_le_ce hA.muts hmem_k
            rw [Array.length_toList] at h1
            rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
            exact h1
          -- Now unpack `ev_uou : Ingress::get_ci [v697]` to rule out `check_recursor_canonical_at.other`!
          obtain ⟨rawU, c_u, hh_U, haddr_U, hex_U, -, hres_U⟩ :=
            L1.get_ci_block_trace_spec (hgood_in.sub hsub_uou).2 ha_maj_rep ev_uou
          have hc_u_eq : c_u = c_maj := by
            have hrec0_M : Ix.Cert.recordAt E₀ (Core.ixAddr a_maj) = some c_maj := by
              rw [← ha_maj_eq]
              exact (hRS.recordOf_eq_recordAt _).symm.trans hrec_M
            exact hRS.record_eq hrec0_M (Core.hashed_mono hsub_uou hh_U) haddr_U hex_U
          subst c_u
          unfold L1.GetCIBlockTraceResult at hres_U
          rw [hp_maj] at hres_U
          obtain ⟨-, _, _, _, _, _, _, _, vU, -, -, -, -, -, -, -, -, hldU, hrawU, -⟩ := hres_U
          obtain ⟨-, -, -, -, -, _, _, _, -, -, hvU, -⟩ := hrawU
          rw [hvU] at hldU
          rw [hldU] at ld_mem
          injection ld_mem with hv_orh_eq
          subst hv_orh_eq
          -- `ev_tjo : check_recursor_canonical_at` CANNOT take `.other`!
          have hlvls_eq : rc.lvls.toNat = ind₀.lvls.toNat + off := by
            match Obs.«KernelCheck::check_recursor_canonical_at».obs ev_tjo with
            | .Induct_n1_bind (hv15 := hv15) (op162 := op162) (heq165 := heq165) .. =>
              injection hv15 with _ _ h15
              injection h15 with hxnl _
              subst hxnl
              simp only [evalBinOp, Except.ok.injEq] at op162
              rw [← op162] at heq165
              have h1 := congrArg ZMod.val (Value.field.inj heq165)
              rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by omega),
                ZMod.val_natCast_of_lt (by omega)] at h1
              exact h1
            | .Induct_other (hv15 := hv15) (op162 := op162) (heq165 := heq165) .. =>
              injection hv15 with _ _ h15
              injection h15 with hxnl _
              subst hxnl
              simp only [evalBinOp, Except.ok.injEq] at op162
              rw [← op162] at heq165
              have h1 := congrArg ZMod.val (Value.field.inj heq165)
              rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by omega),
                ZMod.val_natCast_of_lt (by omega)] at h1
              exact h1
            | .other (hne944 := hne944) .. =>
              exact absurd rfl (hne944 _ rfl)
          -- Construct `ps`
          let ps := Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind₀.lvls.toNat + 1))
            (List.range ind₀.lvls.toNat)
          have hps_props := recLps_length_perm (decide (rc.lvls.toNat = ind₀.lvls.toNat + 1))
            ind₀.lvls.toNat
          have hps_len : ps.length = rc.lvls.toNat := by
            have h1 : ps.length = ind₀.lvls.toNat +
                (if decide (rc.lvls.toNat = ind₀.lvls.toNat + 1) then 1 else 0) := hps_props.1
            rcases hoff with rfl | rfl <;> simp [hlvls_eq] at h1 ⊢ <;> omega
          have hps_perm : ps.Perm (List.range ps.length) := hps_props.2
          -- Build `ty₀` under `ps`
          obtain ⟨ty₀, hty₀_read⟩ := LoadedReads.exprReader_read_ok (t := t)
            (blob := fun x => E₀.blobs.get? x) ht (param := Ix.Kernel.Reader.recParam ps)
            (self := blockSelf t A rs') rty (fun _ _ hx => by simp at hx) hblob_a
          have hty₀_pos : Core.posOf ps ty₀ = tyP :=
            Except.ok.inj ((exprReader_posOf hps_perm hty₀_read).symm.trans htyP)
          have hty₀_lbb : ty₀.looseBVarsBounded 0 = true := by
            have : (Core.posOf ps ty₀).looseBVarsBounded 0 = true := by rwa [hty₀_pos]
            simpa [Core.posOf, Ix.Kernel.Expr.looseBVarsBounded_instantiateLevelParams] using this
          have hty₀_def : ty₀.allLevelParamsDefined ps = true :=
            Decl.allLevelParamsDefined_of_posOf_perm hps_perm (by rw [hty₀_pos, hps_len]; exact htyP_def)
          have hty₀_fv : ty₀.hasFvar = false := exprReader_hasFvar_false hty₀_read
          -- Build `rules₀` under `ps` using `check_rules_go_scoped`
          have hrules_sc : ∀ ru ∈ rc.rules.toList, ∀ rhsP,
              (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t A rs')).read ru.rhs = .ok rhsP →
              rhsP.looseBVarsBounded 0 = true ∧
                rhsP.allLevelParamsDefined (List.range ps.length) = true := by
            intro ru hru rhsP hrhsP
            rw [hps_len]
            exact check_rules_go_scoped hbound hlvls_lt hrules_tr
              (ext_m67_m838.trans (ev_cr_pins.heap_extends.trans
                (ev_cr_ci.heap_extends.trans ev_cr_len.heap_extends)))
              ev_cr_go hsub_cr177 ru hru rhsP hrhsP
          obtain ⟨rules₀, hrules_rr, hrules_rd⟩ := rulesTrace_build_reads (Bm := p_maj.block)
            (im := p_maj.idx.toNat) ht
            (fun i x hx => by
              obtain ⟨m₀, hm₀, -⟩ := LoadedReads.blockRecurAddrs_get hx
              exact ⟨.ok (keyOf t (memberAddr A i m₀)), keyOf t (memberAddr A i m₀),
                by simp [blockSelf, hm₀], rfl⟩)
            hblob_a hps_perm hrules_tr hrules_sc
          -- Build `IndKeyAt` for `a_maj` (`p_maj.block`, `p_maj.idx.toNat`, `indM`)
          have ha_maj_used : UsedRef E₀ A (Core.ixAddr a_maj) := by
            obtain ⟨_, p_rem, hrem, hin_rem⟩ := addrIn_of_rawTm_stripPis
              (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
              hraw0.toRawTm hstrip_m
            cases hrem with
            | forallE cell ht_dom _ _ =>
              obtain ⟨b', hb', hin_b'⟩ :=
                addrIn_of_rawTm_const_head ht_dom hhead_m (fun b hb => Assembly.keyOf_injective ht hb)
              obtain ⟨i, hi, href⟩ := usedRef_of_rawConvExpr_rmember hA.record hA.muts hmem_k rty
                (hin_rem b' (.forallTy cell hin_b'))
              rw [hb'] at href
              exact usedRef_of_idx hA.record hi href
          have hcbM_logic : InLogic cbM := by
            rcases hrefs_ok (Core.ixAddr a_maj) ha_maj_used with hcov | hneed
            · exact inLogic_of_covered_ind ht hShape hRF hSS_in hLim
                (by rwa [← ha_maj_eq]) hp_maj rfl hrec_cbM hcov
            · obtain ⟨c', hc', -, -, hown⟩ := hneed
              have hrec_maj' : recordOf E₀ (Core.ixAddr a_maj) = some c_maj := by
                rwa [← ha_maj_eq]
              have heq_c' : c' = c_maj := Option.some.inj (hc'.symm.trans hrec_maj')
              subst c'
              have hown_eq : Ix.Cert.ownerOf (Core.ixAddr a_maj) c_maj = p_maj.block := by
                simp [Ix.Cert.ownerOf, hp_maj]
              rw [hown_eq] at hown
              exact hown cbM hrec_cbM
          have hindKey_M : IndKeyAt t (recordOf E₀) (keyOf t (Core.ixAddr a_maj))
              p_maj.block p_maj.idx.toNat indM := by
            have hcan := LoadedReads.iprj_canonical indM hex_M htv_M hp_maj
            have hrec_maj' : recordOf E₀ (Core.ixAddr a_maj) = some c_maj := by
              rwa [← ha_maj_eq]
            refine ⟨Core.ixAddr a_maj, c_maj, p_maj, cbM, msM, rfl, hrec_maj', hp_maj, rfl, rfl,
              hrec_cbM, hcbM, ?_, ?_, ?_, hcbM_logic⟩
            · simpa [Array.getElem?_toList] using hmsM
            · exact hcan.1
            · rw [← ha_maj_eq, ← haddr_M]; exact hcan.2
          -- Build `RecReads` and `Reads`
          let mI := rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat
          let rP := rc.params.toNat + rc.motives.toNat + rc.minors.toNat
          let ci₀ : ConstantInfo .anon :=
            .recInfo ⟨keyOf t (Core.rprjAddr A k), ps, ty₀⟩ mI rP rules₀
          have hrecReads : RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) c (blockSelf t A rs')
              (keyOf t (Core.rprjAddr A k)) rc ci₀ :=
            ⟨tyP, ty₀, keyOf t (Core.iprjAddr B 0), keyOf t (Core.ixAddr a_maj),
              B, p_maj.block, 0, p_maj.idx.toNat, ind₀, indM, ps, rules₀,
              htyP, hfamKey_tyP, hindKey_F, hmajKey_tyP, hindKey_M, rfl, hty₀_read,
              hrules_size_eq, hrules_rr, rfl⟩
          have hreads : Reads t E₀ (Core.rprjAddr A k) ci₀ := by
            refine ⟨memberProjection A k (.recr rc),
              by simpa [memberAddr, memberProjection, Core.rprjAddr, Core.projAddr] using
                hA.members k (.recr rc) hmem_k, ?_⟩
            refine ⟨c, rs', rc, ⟨hA.record, hA.muts, ?_, ?_, ?_, hA.logic⟩, ?_⟩
            · simpa [hk64] using hmem_k
            · simp [memberProjection, hk64]
            · simp [memberAddr, memberProjection, Core.rprjAddr, Core.projAddr, hk64]
            · simpa [hk64] using hrecReads
          -- Canonical annotations `ty'` and `rls` via `LoadedReads.recr_value_canon`
          have hagree_a : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs_a :=
            fun a bs hm declared hd => Option.some.inj ((hblob_a a bs hm).symm.trans hd)
          have htr_repacked : L1.RecrTraceRep c.refs.toList (L1.blockRecurAddrs A rs'.toList)
              c.univs.toList c.sharing.toList blobs_a tree_a (mutsRoot rs' k) m67 rc A k v_a :=
            ⟨hlvls_lt, hp56, hi56, hm56, hmi56, by omega, tyPtr, rulesPtr, blkPtr, b_a, planT,
              hb_a_eq, hb_a_rep, hv_a, rty, hplanT, hlevelsT, hrules_tr⟩
          obtain ⟨ty', rls, hcanonTy, hcanonRules, hannTy', hruleStored, hci_canon⟩ :=
            LoadedReads.recr_value_canon ht hps_len hps_perm
              (LoadedReads.blockSelf_key t A rs') hagree_a hbuilt_a htr_repacked
              hty₀_read hty₀_lbb hty₀_def
              (List.Forall₂.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) hrules_rd)
              (fun hk => by rw [hk_false] at hk; cases hk)
              (Core.keyOf t) (Core.keyOf t (Core.rprjAddr A k)) (Or.inr rfl)
              (fun _ _ _ r => r) (fun _ _ _ _ _ r => r)
          -- Exact representation `TmCExact (Core.keyOf t) m67 (Core.posOf ps ty') tyPtr`
          obtain ⟨ty'_e, -, htm_ty'_e, happly_ty'_e⟩ := rty.toTmCExactTrace (κ := Core.keyOf t)
            (ps := ps) hps_perm (by rw [hps_len]; exact hlvls_lt)
            (LoadedReads.readCtx_keyAt_inv ht _) (fun i x m k hx => by simp at hx) hblob_a
            hty₀_read hty₀_lbb hty₀_def
          have hcanonTy_e : LoadedReads.canonAnn c ps (mutsRoot rs' k) rc.typ ty₀ = some ty'_e := by
            unfold LoadedReads.canonAnn mutsRoot
            rw [LoadedReads.canonTree_eq hbuilt_a, hplanT]
            simp only [Option.bind_some]
            have hap := happly_ty'_e planT hlevelsT []
            simp only [List.append_nil] at hap
            rw [hap]; rfl
          have hty'_eq : ty'_e = ty' := Option.some.inj (hcanonTy_e.symm.trans hcanonTy)
          subst ty'_e
          have htm_ty' : Decl.TmCExact (Core.keyOf t) m67 (Core.posOf ps ty') tyPtr := htm_ty'_e
          have hty'_letFree : letFree ty' = true := letFree_of_canonAnn hcanonTy
          have hrls_letFree : ∀ rl ∈ rls, letFree rl.rhs = true :=
            canonRules_letFree hcanonRules
          -- `noSelf` from `ev571 : expr_mentions_addrs [x_ty, x_fam] m511 (.field 0)`
          have hfam_m511 : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m511
              recAs x_fam :=
            repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
              (hext.trans (ev82.heap_extends.trans ext_m67_m511)) hfam_rep
          have hnoSelf : ∀ q < rs'.size, ty'.mentionsConst (keyOf t (Core.rprjAddr A q)) = false := by
            intro q hq
            have hT : ∀ a : Bytes.Address, Core.keyOf t (Core.ixAddr a) =
                Core.keyOf t (Core.rprjAddr A q) → ∃ b ∈ recAs, Core.ixAddr b = Core.ixAddr a := by
              intro a ha
              have hax : Core.ixAddr a = Core.rprjAddr A q := Assembly.keyOf_injective ht ha
              have hq_mem : rs'[q]? = some (rs'[q]'hq) := getElem?_pos rs' q hq
              obtain ⟨rcq, hrcq⟩ := hA.recrs _ (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hq_mem))
              have hq_rec : rs'[q]? = some (.recr rcq) := by rwa [hrcq] at hq_mem
              have hbq : (recAs.map Core.ixAddr)[q]? = some (Core.rprjAddr A q) := by
                rw [hrecAs_map, List.getElem?_mapIdx, Array.getElem?_toList, hq_rec]
                simp [memberAddr, memberProjection, Core.rprjAddr, Core.projAddr]
              rw [List.getElem?_map] at hbq
              cases hget : recAs[q]? with
              | none => rw [hget] at hbq; cases hbq
              | some b =>
                rw [hget] at hbq
                exact ⟨b, List.mem_of_getElem? hget, (Option.some.inj hbq).trans hax.symm⟩
            have h0 := Decl.expr_mentions_addrs_zero_spec hT
              ((htm_ty' 0 (fun _ => .sort .zero)).mono ext_m67_m511) hfam_m511
              (by rwa [heq594] at ev571)
            rw [mentionsConst_posOf, LoadedReads.keyOf_eq] at h0
            exact h0
          -- `motiveConcl` from `ev403 : check_rec_motive`
          have hv405_eq : v405 = .field ((mI + 1 : Nat) : F) := by
            simp only [evalBinOp, Except.ok.injEq] at op451
            rw [← op451] at op443
            simp only [evalBinOp, Except.ok.injEq] at op443
            rw [← op443] at op435
            simp only [evalBinOp, Except.ok.injEq] at op435
            rw [← op435] at op427
            simp only [evalBinOp, Except.ok.injEq] at op427
            rw [← op427]
            simp only [mI, Nat.cast_add, Nat.cast_one]
          have hv406_eq : v406 = .field ((rc.params.toNat + k : Nat) : F) := by
            simp only [evalBinOp, Except.ok.injEq] at op469
            rw [← op469, Nat.cast_add]
          have hmotiveConcl : ∃ bs concl,
              (Core.posOf ps ty').stripPis (mI + 1) = some (bs, concl) ∧
              ∀ d b m, concl ≠ .forallE d b m := by
            rw [hv405_eq, hv406_eq] at ev403
            exact check_rec_motive_not_forallE (by omega)
              ((htm_ty' 0 (fun _ => .sort .zero)).mono ext_m67_m335) ev403
          -- `majorPins` from `ev_uoy : rec_major_pins` + `ev_akr : lower_pins`
          have hv_czb_eq : v_czb = .field (rP : F) := by
            simp only [evalBinOp, Except.ok.injEq] at op_ein
            rw [← op_ein] at op_smk
            simp only [evalBinOp, Except.ok.injEq] at op_smk
            rw [← op_smk]
            simp only [rP, Nat.cast_add]
          have hv_lyw_eq : v_lyw = .field ((rc.motives.toNat + rc.minors.toNat : Nat) : F) := by
            simp only [evalBinOp, Except.ok.injEq] at op_dyn
            rw [← op_dyn, Nat.cast_add]
          have hsub_uoy : ∀ cl ∈ cs_sbl, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
          have hsub_akr : ∀ cl ∈ cs_kxc, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
          rw [hv_czb_eq] at ev_uoy
          rw [hv_lyw_eq] at ev_akr
          obtain ⟨iaddr_p, ilvls_p, pins_p, a_ind_p, inp_p, bs_p, dom_p, body_p, mmaj_p,
            lvls_p, As_p, htup_p, -, -, hstrip_p, hfn_p, hargs_p, -, -, hdrop_p, hno_ni,
            hpins_rep, hlen_p⟩ :=
            Decl.rec_major_pins_spec_wide (hgood_in.sub hsub_uoy).2
              (by rw [ZMod.val_natCast_of_lt (by omega)]; omega)
              (by rw [ZMod.val_natCast_of_lt (by omega)]; omega)
              ev_uoy ((htm_ty' 0 (fun _ => .sort .zero)).mono ext_m67_m_cjj)
          injection htup_p with htup_p'
          injection htup_p' with _ htup_p''
          injection htup_p'' with _ htup_p'''
          injection htup_p''' with hpins_eq _
          subst hpins_eq
          have hrp_val : ZMod.val (rP : F) = rP := ZMod.val_natCast_of_lt (by omega)
          have hni_val : ZMod.val (rc.indices.toNat : F) = rc.indices.toNat :=
            ZMod.val_natCast_of_lt (by omega)
          have hlyw_val : ZMod.val ((rc.motives.toNat + rc.minors.toNat : Nat) : F) =
              rc.motives.toNat + rc.minors.toNat := ZMod.val_natCast_of_lt (by omega)
          rw [hrp_val] at hstrip_p hpins_rep
          rw [hni_val] at hstrip_p hdrop_p hno_ni hpins_rep hlen_p
          have hrp_split : rP = rc.params.toNat + ZMod.val ((rc.motives.toNat + rc.minors.toNat : Nat) : F) := by
            rw [hlyw_val]; simp only [rP]; omega
          rw [hrp_split] at hpins_rep
          obtain ⟨hno_mm, -⟩ := Decl.lower_pins_spec (hgood_in.sub hsub_akr).2
            (by rw [hlyw_val]; omega) ev_akr hpins_rep
          have hmajorPins : ∃ (a_ind : _root_.Address) (inp : Nat)
              (bs : List (KExpr × Ix.Kernel.BinderMeta)) (dom body : KExpr)
              (m_maj : Ix.Kernel.BinderMeta) (lvls_pos : List KLevel) (As : List KExpr),
              (Core.posOf ps ty').stripPis mI = some (bs, .forallE dom body m_maj) ∧
              dom.getAppFn = .const (keyOf t a_ind) lvls_pos ∧
              dom.getAppArgs = As ∧
              As.length = inp + rc.indices.toNat ∧
              As.drop inp = (List.range rc.indices.toNat).map (fun m => .bvar (rc.indices.toNat - 1 - m)) ∧
              (∀ P ∈ As.take inp,
                Binding.FamilyFlat.hasBVarIn 0
                  (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) P = false) := by
            refine ⟨Core.ixAddr a_ind_p, ZMod.val inp_p, bs_p, dom_p, body_p, mmaj_p, lvls_p, As_p,
              hstrip_p, by rwa [LoadedReads.keyOf_eq] at hfn_p, hargs_p, hlen_p, hdrop_p, fun P hP => ?_⟩
            have h1 := hno_ni P hP
            have h2 := hno_mm (P.lowerBVars rc.indices.toNat 0) (List.mem_map.mpr ⟨P, hP, rfl⟩)
            rw [hlyw_val] at h2
            simpa using hasBVarIn_false_of_noLooseIn_lower P 0 h1 h2
          -- Front-door `ConstantValCheckJ twinPosRulesJ` factory
          have hcells_no_self : ∀ a, Core.AddrIn m67 tyPtr a → ∀ b ∈ recAs, Core.ixAddr b ≠ Core.ixAddr a :=
            fun a hin => expr_mentions_addrs_zero_addrIn hfam_m511 (by rwa [heq594] at ev571) a
              (addrIn_mono_ce ext_m67_m511 hin)
          have hfrontDoor : ∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon),
              StepStore calls t E₀ E →
              Decl.PrefixInv.{u} E t lim env →
              (∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
                (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x) →
              env.find? (keyOf t (Core.rprjAddr A k)) = none →
              Decl.KeyFree (keyOf t (Core.rprjAddr A k)) →
              ConstantValCheckJ twinPosRulesJ env
                ⟨keyOf t (Core.rprjAddr A k), ps, ty₀⟩
                ⟨keyOf t (Core.rprjAddr A k), ps, ty'⟩ := by
            intro E env hSS hinv hused hfresh hkey
            have hcells_stored : ∀ a, Core.AddrIn m67 tyPtr a →
                ∃ ci, env.find? (Core.keyOf t (Core.ixAddr a)) = some ci := by
              intro a hin
              obtain ⟨i, hi, href⟩ := usedRef_of_rawConvExpr_rmember hA.record hA.muts hmem_k rty hin
              rcases hused i hi (Core.ixAddr a) href with hst | hca
              · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hst
                exact ⟨ci, by rwa [LoadedReads.keyOf_eq]⟩
              · exfalso
                rcases hca with ⟨-, hs⟩ | ⟨ms_q, q, mq, hms_q, hmq, hxm⟩
                · exact standalone_not_block hs ⟨rs', hA.muts⟩
                have hrs_q : rs' = ms_q := Ixon.ConstantInfo.muts.inj (hA.muts.symm.trans hms_q)
                subst hrs_q
                obtain ⟨rcq, rfl⟩ := hA.recrs mq (List.mem_of_getElem? (by rwa [Array.getElem?_toList]))
                rcases hxm with ha_eq | ⟨ind_q, _, hind_q, -, -⟩
                · have hbq : (recAs.map Core.ixAddr)[q]? = some (Core.ixAddr a) := by
                    rw [hrecAs_map, List.getElem?_mapIdx, Array.getElem?_toList, hmq]
                    simp [ha_eq]
                  rw [List.getElem?_map] at hbq
                  cases hget : recAs[q]? with
                  | none => rw [hget] at hbq; cases hbq
                  | some b =>
                    rw [hget] at hbq
                    exact hcells_no_self a hin b (List.mem_of_getElem? hget) (Option.some.inj hbq)
                · cases hind_q
            have htm_stored : Decl.TmCExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ m67
                (Core.posOf ps ty') tyPtr :=
              fun k' Γ => FamilyAlias.tmExact_stored_of_cells (htm_ty' k' Γ) hcells_stored
            have hval_m473 : Decl.ValRepExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ m473
                (.field (rc.lvls.toNat : F)) tyPtr ⟨keyOf t (Core.rprjAddr A k), ps, ty'⟩ :=
              ⟨by rw [hps_len], by rw [hps_len]; exact hlvls_lt, hps_perm,
                fun k' Γ => (htm_stored k' Γ).mono ext_m67_m473⟩
            have hrc_m627 : Core.RCRep t lim m627 x_rc :=
              (hrc_lim.toRCRep).mono (hext.trans (ev82.heap_extends.trans ext_m67_m627))
            have hty_nil : Core.TypesRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ
                (fun _ => .sort .zero) m627 0
                (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m_akk.length) := by
              rw [hm635]
              exact Decl.typesRep_alloc_nil _ _ _
            have hsub606 : ∀ cl ∈ cs606, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
            have hsf := hinv.scopedCoreFacts
            exact (Decl.constantValCheckJ_of_scoped_mapped (c := Core.Ctx.stored ⟨E, env, t, lim⟩)
              (cv := ⟨keyOf t (Core.rprjAddr A k), ps, ty₀⟩)
              (cv' := ⟨keyOf t (Core.rprjAddr A k), ps, ty'⟩)
              judgementsMap_rulesJ_twinPos
              ⟨rfl, rfl, hannTy'⟩ hval_m473 hty₀_lbb hty₀_fv hfresh hkey.1
              (Decl.nat_keyOf_isProjFnShape_false t _) hinv.store.store
              (posSortLiftFor_twinPos hps_perm) ev523
              (ev523.heap_extends.trans (ev571.heap_extends.trans (ext_m561_m_oaj.trans
                (ev_up.heap_extends.trans (ev_sv.heap_extends.trans (ext_m_shk_m_rax.trans
                  (ev_oq.heap_extends.trans (ev_ee.heap_extends.trans
                    (ev_uoy.heap_extends.trans (ev_akr.heap_extends.trans ext_m_akk_m627))))))))))
              hrc_m627 hty_nil hsf.1 hsf.2
              (Core.CoreGood.ofRaw ((hSS.good env lim).sub hsub606) (fun _ _ => trivial)) ev608).1
          exact ⟨{
            rc := rc
            hmem := hmem_k
            hk_false := hk_false
            huns_false := huns_false
            hrnp := hrnp
            hnmot := hnmot
            off := off
            hoff := hoff
            hlvls_eq := hlvls_eq
            ps := ps
            hps_eq := rfl
            hps_len := hps_len
            hps_perm := hps_perm
            a_maj := Core.ixAddr a_maj
            p_maj := p_maj
            indM := indM
            ty₀ := ty₀
            ty' := ty'
            rules₀ := rules₀
            rls := rls
            ci₀ := ci₀
            hci₀ := rfl
            hreads := hreads
            hrecReads := hrecReads
            hmajKey := by rwa [hty₀_pos]
            hindKey_M := hindKey_M
            hni_eq := hni_eq
            hrules_size := hrules_size_eq
            hctor_params := fun c_idx ct hct => by
              have hr_le := rules_size_le_ce hA.muts hmem_k
              have hctL : indM.ctors.toList[0 + c_idx]? = some ct := by
                simpa [Nat.zero_add, Array.getElem?_toList] using hct
              have hc_lt : c_idx < rc.rules.toList.length := by
                have h1 : c_idx < indM.ctors.toList.length := by
                  rcases (List.getElem?_eq_some_iff.mp hctL) with ⟨h, -⟩
                  omega
                simp only [Array.length_toList] at h1 ⊢
                omega
              exact check_rules_go_ctor_params hRS hbound hp_maj_idx_lt hbM_blk_rep
                (by rwa [hbM_blk_ix]) hcbM hmsM hindM_np
                (by simp only [Array.length_toList]; omega) hrules_tr
                (ext_m67_m838.trans (ev_cr_pins.heap_extends.trans
                  (ev_cr_ci.heap_extends.trans ev_cr_len.heap_extends)))
                ev_cr_len.heap_extends
                (by simpa only [Nat.cast_zero] using ev_cr_go)
                hsub_cr177 c_idx hc_lt ct hctL
            hmajor_np := fun bs dom body m hstrip => by
              have hlv : Core.ExprLvEq E_pos (Core.posOf ps ty') :=
                Core.Tm.det hraw0.toTmExact.toTm (htm_ty' 0 (fun _ => .sort .zero)).toTm
              have hrem_lv := exprLvEq_stripPis_ce mI hlv hstrip_r' hstrip
              cases hrem_lv with
              | forallE hdom_lv _ =>
                rw [← exprLvEq_getAppArgs_length_ce hdom_lv, hni_eq]
                exact hdom_Epos_len bs_r dom_r body_r mmaj_r hstrip_r
            hty_read := hty₀_read
            hty_lbb := hty₀_lbb
            hty_def := hty₀_def
            hty_fv := hty₀_fv
            hcanonTy := hcanonTy
            hty'_letFree := hty'_letFree
            hvalStored := ⟨rfl, rfl, hannTy'⟩
            hrules_read := hrules_rd
            hcanonRules := hcanonRules
            hruleStored := hruleStored
            hrls_letFree := hrls_letFree
            hnoSelf := hnoSelf
            hnoRole := hnoRole_all k hk_lt
            hmotiveConcl := hmotiveConcl
            hmajorPins := hmajorPins
            hfrontDoor := hfrontDoor
            hrule_nfields := fun E env hSS hinv c_idx ru hru cvj cnP cnF hfind => by
              have hr_le := rules_size_le_ce hA.muts hmem_k
              have hruL : rc.rules.toList[c_idx]? = some ru := by
                rwa [Array.getElem?_toList]
              have hfind' : env.find? (keyOf t (Core.cprjAddr (Core.ixAddr bM_blk) p_maj.idx.toNat (0 + c_idx))) =
                  some (.ctorInfo cvj cnP cnF) := by
                simpa only [hbM_blk_ix, Nat.zero_add] using hfind
              exact check_rules_go_nfields hSS hinv hp_maj_idx_lt hbM_blk_rep
                (by simp only [Array.length_toList]; omega) hrules_tr
                (ext_m67_m838.trans (ev_cr_pins.heap_extends.trans
                  (ev_cr_ci.heap_extends.trans ev_cr_len.heap_extends)))
                ev_cr_len.heap_extends
                (by simpa only [Nat.cast_zero] using ev_cr_go)
                hsub_cr177 c_idx ru hruL cvj cnP cnF hfind'
            hloaded_at_env := fun E env hSS hinv cv mI' rP' rls' hfind => by
              let cctx : Core.Ctx := ⟨E, env, t, lim⟩
              have hfind' : env.find? (Core.keyOf t (Core.ixAddr a_k)) = some (.recInfo cv mI' rP' rls') := by
                rw [ha_k_ix, LoadedReads.keyOf_eq]; exact hfind
              have hκk : cctx.stored.κ (Core.ixAddr a_k) = Core.keyOf t (Core.ixAddr a_k) :=
                Core.Ctx.stored_key_of_find (c := cctx) hfind'
              have hnek : cctx.stored.κ (Core.ixAddr a_k) ≠ Core.unresolvedKey := by
                rw [hκk]; exact Core.Resolved.ne
              have hg80 : Core.CoreGood cctx.stored cs80 :=
                Core.CoreGood.ofRaw ((hSS.good env lim).sub hsub80) (fun _ _ => trivial)
              obtain ⟨ci_e, hfind_e, pv_e, hpv_e, hci_e⟩ :=
                hinv.loads.getCI x_r p74 h m67 cs80 a_k ev82 trivial hnek hg80 ha_k_rep
              change env.find? _ = some ci_e at hfind_e
              rw [hκk, hfind'] at hfind_e
              injection hfind_e with hci_eq
              subst hci_eq
              have hve_eq : pv_e = v_a := by
                rw [← hv_a] at hld_a
                rw [hld_a] at hpv_e
                exact Except.ok.inj hpv_e.symm
              rw [hve_eq] at hci_e
              generalize hvc_g : v_a = vc_g at hci_canon
              cases hci_e with
              | recr hv_e hnp_e hni_e hnm_e hnmi_e hrP_e hmI_e hcnts_e hrules_e _ _ =>
                cases hci_canon with
                | recr hv_c _ _ _ _ _ _ _ hrules_c _ _ =>
                  injection hvc_g with _ _ hvcf
                  injection hvcf with _ hvcf1
                  injection hvcf1 with hty_cg hvcf2
                  injection hvcf2 with _ hvcf3
                  injection hvcf3 with _ hvcf4
                  injection hvcf4 with _ hvcf5
                  injection hvcf5 with _ hvcf6
                  injection hvcf6 with hrl_cg _
                  subst hty_cg hrl_cg
                  injection hv_a with _ _ hvaf
                  injection hvaf with hnl_a hvaf1
                  injection hvaf1 with _ hvaf2
                  injection hvaf2 with hnp_a hvaf3
                  injection hvaf3 with hni_a hvaf4
                  injection hvaf4 with hnm_a hvaf5
                  injection hvaf5 with hnmi_a _
                  rw [hnl_a] at hv_e
                  rw [hnp_a] at hnp_e
                  rw [hni_a] at hni_e
                  rw [hnm_a] at hnm_e
                  rw [hnmi_a] at hnmi_e
                  have hp_e : _ = (rc.params.toNat : F) := Value.field.inj hnp_e.symm
                  have hi_e : _ = (rc.indices.toNat : F) := Value.field.inj hni_e.symm
                  have hm_e : _ = (rc.motives.toNat : F) := Value.field.inj hnm_e.symm
                  have hmi_e : _ = (rc.minors.toNat : F) := Value.field.inj hnmi_e.symm
                  rw [hp_e, hm_e, hmi_e] at hrP_e
                  rw [hp_e, hi_e, hm_e, hmi_e] at hmI_e
                  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
                  have hrP_eq : rP' = rc.params.toNat + rc.motives.toNat + rc.minors.toNat := by
                    have h1 := congrArg ZMod.val hrP_e
                    rw [← Nat.cast_add, ← Nat.cast_add,
                      ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
                    exact h1
                  have hmI_eq : mI' = rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
                    have h1 := congrArg ZMod.val hmI_e
                    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add,
                      ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
                    exact h1
                  have hlv_eq : cv.levelParams.length = rc.lvls.toNat := by
                    have hcv_lt := hv_e.2.1
                    have h1 := congrArg ZMod.val (Value.field.inj hv_e.1)
                    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
                    exact h1.symm
                  have hty_eq : Core.ExprLvEq (Core.posOf cv.levelParams cv.type) (Core.posOf ps ty') :=
                    Core.Tm.det ((hv_e.2.2.2 0 (fun _ => .sort .zero)).rekey_mono (stored_rekey_ce cctx))
                      (hv_c.2.2.2 0 (fun _ => .sort .zero))
                  exact ⟨hmI_eq, hrP_eq, hlv_eq, hty_eq, rulesRep_det_ce hrules_e hrules_c⟩
                | quot _ _ => exact absurd (Value.construct.inj hvc_g).2.1 (by decide)
              | quot _ _ => exact absurd (Value.construct.inj hv_a).2.1 (by decide)
          }⟩
      · have hnext_k : v1026 = .field ((k + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at op1107
          rw [← op1107, Nat.cast_succ]
        rw [hnext_k] at ev1016
        exact ih hrest_eq (hext.trans ext_h_m892)
          (repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
            ext_h_m892 hrest_rep)
          ev1016 (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) j (by omega) hj

private theorem family_recs_res_bound {calls : List (Call F)} {E₀ : Ixon.Env}
    (hRS : LoadedReads.RunStore calls E₀)
    {b : Bytes.Address} {x_rb v : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_rb)
    (ev : ObsFn Obs.W "KernelModeled::family_recs" [x_rb] h v h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {c : Ixon.Constant} {rs' : Array Ixon.MutConst}
    (hA : FamRecRecord E₀ (Core.ixAddr b) c rs') :
    c.resourceSize < 8589934592 := by
  match Obs.«KernelModeled::family_recs».obs ev with
  | .Muts (cs12 := cs12) (ev14 := ev14) (hc165 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨cb, ms, hbl, -⟩ := Claim.load_block_head hb ev14
    exact ((hbl.mono hsub12).record hRS hA.record).2
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc209 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨-, bytes, c', hsz, hh, haddr, hexact, -, -, -, -, -, -, -⟩ :=
      L1.load_verified_constant_decode_bounded hb ev14
    have hc_eq' : c' = c :=
      hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hA.record)
        (Core.hashed_mono hsub12 hh) haddr hexact
    subst hc_eq'
    have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound ⟨bytes.toArray⟩ c' hexact
    simp only [ByteArray.size, List.size_toArray] at hres
    omega

/-- **Extract all member data from an accepted `KernelModeled::check_family` call** on a block `B`
and a non-empty recursor block `A`. -/
theorem familyCall_extract_members {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ E_in : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {B A : _root_.Address} {cb c : Ixon.Constant} {ms rs' : Array Ixon.MutConst}
    {cs : List (Call F)}
    (ht : t.check = .ok ())
    (hRS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hShape : TableShape.{u} t G R envT)
    (hRF : RecordsFor R E_in)
    (hSS_in : StepStore calls t E₀ E_in)
    (hLim : LimWithin G t lim)
    (hB : FamBlockRecord E₀ B cb ms) (hA : FamRecRecord E₀ A c rs')
    (hcall : FamilyCallAtLim calls bAddr t B A lim cs) :
    ∃ (ind₀ : Ixon.Inductive), ms[0]? = some (.indc ind₀) ∧
      ∀ k < rs'.size, Nonempty (ExtractedTwinMember.{u} calls t E₀ lim B A cb c ms rs' ind₀ k) := by
  have hrefs_ok := recRefs_of_familyCall hRS hH hA.record hcall
  obtain ⟨h, h', x_rc, x_block, x_rec_block, r, hrc_lim, hxB, hxA, ev_fam, -, hsub_fam⟩ := hcall
  obtain ⟨bB, hB_rep, hB_ix⟩ := hxB
  obtain ⟨bA, hA_rep, hA_ix⟩ := hxA
  subst hB_ix hA_ix
  match Obs.«KernelModeled::check_family».obs ev_fam with
  | .run (m105 := m105) (x_members := x_members) (v651 := v651) (v673 := v673) (v839 := v839)
      (v861 := v861) (x_bnl := x_bnl) (x_univ_offset := x_uoff)
      (m501 := m501) (m624 := m624) (m652 := m652) (m674 := m674) (m784 := m784)
      (m840 := m840) (m_qvdvjtit := m_qvd) (m862 := m862) (m_lukcasbb := m_luk)
      (m1191 := m1191) (m1293 := m1293)
      (cs511 := cs511) (cs850 := cs850) (cs1201 := cs1201) (cs1341 := cs1341)
      (sg112 := sg112) (ev126 := e1) (ev148 := e2) (ev194 := e3) (ev_yqjbwijz := e4)
      (ev231 := e5) (ev266 := e6) (ev309 := e7) (ev344 := e8) (ev403 := e9) (ev435 := e10)
      (ev465 := e11) (ev513 := ev513) (ev601 := e13) (ev634 := e14) (ev664 := ev664)
      (ev686 := ev686) (ev716 := e17) (ev759 := e18) (ev817 := e19) (ev796 := e20)
      (ev852 := ev852) (ev_ursqbimm := e22) (ev_srfmazjk := e23) (ev874 := ev874)
      (ev896 := e25) (ev960 := e26) (ev939 := e27) (ev1011 := e28) (ev990 := e29)
      (ev_edyzsqzv := e30) (ev_gkddqxhv := e31) (ev_ittpynob := e32) (ev_biaifgpd := e33)
      (ev1203 := ev1203) (ev_cwwgzxtj := e35) (ev1246 := e36) (ev_mitevvsv := e37)
      (ev_rqpeovbn := e38) (ev_xrhmaojz := e39) (ev_whimdwjd := e40) (ev1305 := e41)
      (ev1343 := ev1343) (hc1474 := hcs) .. =>
    have hsg : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := e0) (he33 := hh) .. => rw [hh]; exact e0.heap_extends
      | .Node (heq97 := h01) .. => exact absurd (Value.field.inj h01).symm one_ne_zero
    have ext_h_453 : Heap.Extends h _ :=
      hsg.trans (e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
      (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
      (e7.heap_extends.trans (e8.heap_extends.trans (e9.heap_extends.trans
      (e10.heap_extends.trans e11.heap_extends))))))))))
    have ext_501_624 : Heap.Extends m501 m624 := e13.heap_extends.trans e14.heap_extends
    have ext_501_652 : Heap.Extends m501 m652 := ext_501_624.trans ev664.heap_extends
    have ext_674_784 : Heap.Extends m674 m784 :=
      e17.heap_extends.trans (e18.heap_extends.trans (e19.heap_extends.trans e20.heap_extends))
    have ext_840_qvd : Heap.Extends m840 m_qvd := e22.heap_extends.trans e23.heap_extends
    have ext_862_luk : Heap.Extends m862 m_luk :=
      e25.heap_extends.trans (e26.heap_extends.trans (e27.heap_extends.trans
      (e28.heap_extends.trans (e29.heap_extends.trans (e30.heap_extends.trans
      (e31.heap_extends.trans (e32.heap_extends.trans e33.heap_extends)))))))
    have ext_1191_1293 : Heap.Extends m1191 m1293 :=
      e35.heap_extends.trans (e36.heap_extends.trans (e37.heap_extends.trans
      (e38.heap_extends.trans (e39.heap_extends.trans (e40.heap_extends.trans e41.heap_extends)))))
    have ext_h_501 : Heap.Extends h m501 := ext_h_453.trans ev513.heap_extends
    have ext_h_674 : Heap.Extends h m674 := ext_h_501.trans (ext_501_652.trans ev686.heap_extends)
    have ext_h_784 : Heap.Extends h m784 := ext_h_674.trans ext_674_784
    have ext_h_840 : Heap.Extends h m840 := ext_h_784.trans ev852.heap_extends
    have ext_h_luk : Heap.Extends h m_luk :=
      ext_h_840.trans (ext_840_qvd.trans (ev874.heap_extends.trans ext_862_luk))
    have ext_h_1293 : Heap.Extends h m1293 := ext_h_luk.trans (ev1203.heap_extends.trans ext_1191_1293)
    have ext_674_luk : Heap.Extends m674 m_luk :=
      ext_674_784.trans (ev852.heap_extends.trans (ext_840_qvd.trans (ev874.heap_extends.trans ext_862_luk)))
    have ext_674_1293 : Heap.Extends m674 m1293 :=
      ext_674_luk.trans (ev1203.heap_extends.trans ext_1191_1293)
    have ext_840_1293 : Heap.Extends m840 m1293 :=
      ext_840_qvd.trans (ev874.heap_extends.trans (ext_862_luk.trans (ev1203.heap_extends.trans ext_1191_1293)))
    -- 1. `ev513 : load_verified_constant [x_block]` loads `cb` (`ms`)
    have hsub511 : ∀ cl ∈ cs511, cl ∈ calls := fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
    obtain ⟨cb', ms', hblB, hms_rep⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_h_453 hB_rep) ev513
    obtain ⟨hcb'_eq, hms'_eq⟩ := (hblB.mono hsub511).stored hH
    have heq_cb : cb' = cb := Option.some.inj (hcb'_eq.symm.trans hB.record)
    subst cb'
    have heq_ms : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'_eq.symm.trans hB.muts)
    subst ms'
    -- 2. `ev664 : block_nparams [x_members]` gives `ind₀` and `v651 = .field ind₀.params`
    obtain ⟨ind₀, rest_ms, hms_cons, hind0_params, hv651_eq⟩ :=
      block_nparams_spec (RepLinkedList.mono L1.repMutConst_heapMono₂ ext_501_624 hms_rep) ev664
    subst hv651_eq
    have hms0 : ms[0]? = some (.indc ind₀) := by
      rw [← Array.getElem?_toList, hms_cons]; rfl
    -- 3. `ev686 : build_recur_addrs [x_members, x_block]` gives `typeAs` with head `iprjAddr B 0`
    have hmem_m652 : Core.Specs.Callees.MembersRep m652 ms.toList x_members :=
      Route.membersRep_of_repMutConstList
        (RepLinkedList.mono L1.repMutConst_heapMono₂ ext_501_652 hms_rep)
    obtain ⟨-, typeAs, htype_m674, htype_map⟩ := L1.build_recur_addrs_spec hmem_m652
      (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_h_501.trans ext_501_652) hB_rep) ev686
    rw [hms_cons] at htype_map
    cases typeAs with
    | nil => simp at htype_map
    | cons t0 typeRest =>
      simp only [List.map_cons, List.mapIdx_cons, List.cons.injEq] at htype_map
      have ht0_addr : Core.ixAddr t0 = Core.iprjAddr (Core.ixAddr bB) 0 := by
        simpa [Core.projAddr, Core.Specs.Callees.memberProjInfo, Core.iprjAddr] using htype_map.1
      -- 4. `ev852 : family_recs [x_rec_block]` gives `recAs` + `c.resourceSize < 2^33`
      have hsub850 : ∀ cl ∈ cs850, cl ∈ calls := fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
      have hA_m784 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext_h_784 hA_rep
      have hc_res : c.resourceSize < 8589934592 :=
        family_recs_res_bound hRS hA_m784 ev852 hsub850 hA
      obtain ⟨recAs, hrec_m840, hrecAs_map'⟩ :=
        FamilyAlias.family_recs_list hH hA_m784 ev852 hsub850 hA
      have hrecAs_map : recAs.map Core.ixAddr =
          rs'.toList.mapIdx (fun i m => memberAddr (Core.ixAddr bA) i m) := by
        rw [hrecAs_map']
        refine List.ext_getElem? fun i => ?_
        rw [List.getElem?_mapIdx, List.getElem?_mapIdx]
        cases hget : rs'.toList[i]? with
        | none => rfl
        | some m =>
          cases m <;> rfl
      have hrecAs_len : recAs.length = rs'.size := by
        have := congrArg List.length hrecAs_map
        simpa [Array.length_toList] using this
      -- 4b. `e22 : assert_no_role [x_rc, v839]` gives `∀ j < rs'.size, ∀ ro, keyOf t (rprjAddr A j) ≠ .role ro`
      have hnoRole_recAs :=
        FamilyAlias.assert_no_role_spec recAs (hrc_lim.mono ext_h_840) hrec_m840 e22
      have hnoRole_all : ∀ j < rs'.size, ∀ ro : Ix.Kernel.Role,
          keyOf t (Core.rprjAddr (Core.ixAddr bA) j) ≠ .role ro := by
        intro j hj ro
        have hj' : j < recAs.length := by omega
        have ha_j : recAs[j]? = some recAs[j] := List.getElem?_eq_getElem hj'
        have hmem_aj : recAs[j] ∈ recAs := List.mem_of_getElem? ha_j
        have hmap_j := congrArg (fun l => l[j]?) hrecAs_map
        rw [List.getElem?_map, ha_j, Option.map_some, List.getElem?_mapIdx] at hmap_j
        have hrs_j : ∃ rc_j, rs'.toList[j]? = some (.recr rc_j) := by
          have hj_l : j < rs'.toList.length := by simpa [Array.length_toList] using hj
          have hm_j : rs'.toList[j]? = some rs'.toList[j] := List.getElem?_eq_getElem hj_l
          obtain ⟨rc_j, hrc_j_eq⟩ := hA.recrs rs'.toList[j] (List.mem_of_getElem? hm_j)
          exact ⟨rc_j, by rwa [hrc_j_eq] at hm_j⟩
        obtain ⟨rc_j, hrc_j⟩ := hrs_j
        rw [hrc_j, Option.map_some] at hmap_j
        have ha_eq : Core.ixAddr recAs[j] = Core.rprjAddr (Core.ixAddr bA) j := Option.some.inj hmap_j
        rw [← LoadedReads.keyOf_eq, ← ha_eq]
        exact hnoRole_recAs recAs[j] hmem_aj ro
      -- 5. `ev874 : Lists::length [v839]` gives `v861 = .field rs'.size`
      have hrec_qvd := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
        ext_840_qvd hrec_m840
      have hv861_eq : v861 = .field (recAs.length : F) :=
        (Decl.addrList_length_spec hrec_qvd ev874).1
      rw [hrecAs_len] at hv861_eq
      subst hv861_eq
      -- 6. `ev1203 : block_elim [x_rc, v673]` gives `x_bnl = .field ind₀.lvls`, `x_uoff = .field off`, `off ∈ {0, 1}`
      have hsub1201 : ∀ cl ∈ cs1201, cl ∈ calls := fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
      have htype_luk := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
        ext_674_luk htype_m674
      match Obs.«KernelModeled::block_elim».obs ev1203 with
      | .run (x_t0 := x_t0) (x_nl := x_nl_be) (v212 := v212) (cs41 := cs_be41)
          (ld11 := ld_be11) (ev43 := ev_be43) (ld37 := ld_be37)
          (ev232 := ev_be232) (he213 := he_be213) (hc242 := hcs_be) .. =>
        injection he_be213 with hbe_list
        injection hbe_list with hbnl_eq hbe_list2
        injection hbe_list2 with huoff_eq _
        obtain ⟨off, hoff, hv212_eq⟩ : ∃ off : Nat, (off = 0 ∨ off = 1) ∧ v212 = .field (off : F) := by
          rcases level_is_not_zero_bit ev_be232 with h | h
          · exact ⟨0, Or.inl rfl, by simpa using h⟩
          · exact ⟨1, Or.inr rfl, by simpa using h⟩
        rw [hv212_eq] at huoff_eq
        subst hbnl_eq huoff_eq
        obtain ⟨t0', _, ht0_cons, ht0_rep, -⟩ := Lib.rep_cons_of_load htype_luk ld_be11
        injection ht0_cons with ht0_eq _; subst ht0_eq
        have hsub_be41 : ∀ cl ∈ cs_be41, cl ∈ calls :=
          fun cl hcl => hsub1201 cl (by rw [hcs_be]; simp [hcl])
        have hgood_in := hSS_in.good default lim
        obtain ⟨raw0, c0, hh0, haddr0, hex0, -, hres0⟩ :=
          L1.get_ci_block_trace_spec (hgood_in.sub hsub_be41).2 ht0_rep ev_be43
        have hind0_proj : recordOf E₀ (Core.ixAddr t0) = some (memberProjection (Core.ixAddr bB) 0 (.indc ind₀)) := by
          rw [ht0_addr]
          exact hB.members 0 (.indc ind₀) hms0
        have hc0_eq : c0 = memberProjection (Core.ixAddr bB) 0 (.indc ind₀) :=
          hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hind0_proj)
            (Core.hashed_mono hsub_be41 hh0) haddr0 hex0
        subst hc0_eq
        unfold L1.GetCIBlockTraceResult at hres0
        have hinfo0 : (memberProjection (Core.ixAddr bB) 0 (.indc ind₀)).info =
            .iPrj ⟨(0 : Nat).toUInt64, Core.ixAddr bB⟩ := rfl
        rw [hinfo0] at hres0
        obtain ⟨-, blk0, cb0, ms0, ind0', blobs0, tree0, plan0, v0, hhB0, haB0, hexB0, hcb0, hms0', -, -, -,
          hld0, hraw0, -⟩ := hres0
        have hcb0_eq : cb0 = cb :=
          hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hB.record)
            (Core.hashed_mono hsub_be41 hhB0) haB0 hexB0
        subst cb0
        have hms0_eq : ms0 = ms := Ixon.ConstantInfo.muts.inj (hcb0.symm.trans hB.muts)
        subst ms0
        have hidx0 : ({ idx := (0 : Nat).toUInt64, block := Core.ixAddr bB } : Ixon.InductiveProj).idx.toNat = 0 := rfl
        rw [hidx0, Array.getElem?_toList] at hms0'
        have hind0_eq : ind0' = ind₀ :=
          Ixon.MutConst.indc.inj (Option.some.inj (hms0'.symm.trans hms0))
        subst ind0'
        obtain ⟨hind0_lvls, -, -, -, -, tyPtr0, blkPtr0, b0, -, -, hv0, -⟩ := hraw0
        rw [hv0] at hld0
        rw [hld0] at ld_be37
        injection ld_be37 with hv0_eq
        injection hv0_eq with _ _ h0_fields
        injection h0_fields with hxnl0_eq _
        subst hxnl0_eq
        -- 7. Invoke `check_recs_extract` at `k = 0`!
        have hsub1341 : ∀ cl ∈ cs1341, cl ∈ calls :=
          fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
        have htype_1293 := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ext_674_1293 htype_m674
        have hrec_1293 := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ext_840_1293 hrec_m840
        have hrc_1293 := hrc_lim.mono ext_h_1293
        refine ⟨ind₀, hms0, fun k hk => ?_⟩
        exact check_recs_extract ht hRS hH hShape hRF hSS_in hLim hB hA hc_res hms0 hind0_params
          hind0_lvls hoff hrefs_ok hrc_1293 rfl ht0_addr htype_1293 hrec_1293 hrecAs_map
          hrecAs_len hnoRole_all (k := 0) (by simp) (Heap.Extends.refl _) hrec_1293
          (by simpa only [Nat.cast_zero] using ev1343) hsub1341 k (Nat.zero_le k) hk

private theorem build_recur_addrs_head_hashed {m0 : Ixon.MutConst} {rest : List Ixon.MutConst}
    {b : Bytes.Address} {x_members x_block r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h (m0 :: rest) x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block)
    (ev : ObsFn Obs.W "Ingress::build_recur_addrs" [x_members, x_block] h r h' cs) :
    Hashed cs (Ixon.serConstant (memberProjection (Core.ixAddr b) 0 m0)) := by
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have ev6' : ObsFn Obs.W "Ingress::build_recur_addrs_walk"
      [x_members, x_block, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
    simpa using ev6
  rcases Obs.«Ingress::build_recur_addrs_walk».obs ev6' with
    ⟨ld12, _, _, _⟩ |
    ⟨w36, x_rest, v55, v56, m58, cs66, m94, cs102, v108,
      ld12, he51, hm50, ev68, op143, ev104, hc145⟩
  · cases Lib.rep_nil_of_load hms ld12
  · obtain ⟨-, -, -, mc, -, hget, -, -, hhash⟩ := L1.projection_addr_hashed_spec hms hb ev68
    have h0 : ((0 : Nat) : F).val = 0 := by simp
    rw [h0] at hget hhash
    have emc : mc = m0 := (by simpa using hget : m0 = mc).symm
    subst emc
    have hmemb : memberProjection (Core.ixAddr b) 0 mc =
        ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) 0 mc, #[], #[], #[], #[]⟩ := by
      cases mc <;> rfl
    rw [hmemb]
    exact Core.hashed_mono (fun cl hcl => by rw [hc38, hc145]; simp [hcl]) hhash

/-- **An accepted `KernelModeled::check_family` call on `(B, A)` with non-empty `A` witnesses
`B`'s block record, its first inductive member `ind₀`, its stored member-0 projection record, and
`UsedRef E₀ A (Core.iprjAddr B 0)`**: `load_verified_constant` loads `B`, `build_recur_addrs`
hashes `memberProjection B 0 (.indc ind₀)`, and `check_carriers` on member 0 of `A` finds
`iprjAddr B 0` as a `Const` cell in `rc₀.typ` (where `recurAddrs = []`). -/
theorem familyCall_usedRef_ind0 {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ E_in : Ixon.Env} {lim : Option Nat}
    {B A : _root_.Address} {c : Ixon.Constant} {rs' : Array Ixon.MutConst}
    {cs : List (Call F)}
    (ht : t.check = .ok ())
    (hRS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hSS_in : StepStore calls t E₀ E_in)
    (hA : FamRecRecord E₀ A c rs')
    (hsz : rs'.size ≠ 0)
    (hcall : FamilyCallAtLim calls bAddr t B A lim cs) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind₀ : Ixon.Inductive),
      recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧ ms[0]? = some (.indc ind₀) ∧
      recordOf E₀ (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind₀)) ∧
      UsedRef E₀ A (Core.iprjAddr B 0) := by
  obtain ⟨h, h', x_rc, x_block, x_rec_block, r, -, hxB, hxA, ev_fam, -, hsub_fam⟩ := hcall
  obtain ⟨bB, hB_rep, hB_ix⟩ := hxB
  obtain ⟨bA, hA_rep, hA_ix⟩ := hxA
  subst hB_ix hA_ix
  match Obs.«KernelModeled::check_family».obs ev_fam with
  | .run (m105 := m105) (x_members := x_members) (v673 := v673) (v839 := v839)
      (m501 := m501) (m624 := m624) (m652 := m652) (m674 := m674) (m784 := m784)
      (m840 := m840) (m_qvdvjtit := m_qvd) (m862 := m862) (m_lukcasbb := m_luk)
      (m1191 := m1191) (m1293 := m1293)
      (cs511 := cs511) (cs684 := cs684) (cs850 := cs850) (cs1341 := cs1341)
      (sg112 := sg112) (ev126 := e1) (ev148 := e2) (ev194 := e3) (ev_yqjbwijz := e4)
      (ev231 := e5) (ev266 := e6) (ev309 := e7) (ev344 := e8) (ev403 := e9) (ev435 := e10)
      (ev465 := e11) (ev513 := ev513) (ev601 := e13) (ev634 := e14) (ev664 := ev664)
      (ev686 := ev686) (ev716 := e17) (ev759 := e18) (ev817 := e19) (ev796 := e20)
      (ev852 := ev852) (ev_ursqbimm := e22) (ev_srfmazjk := e23) (ev874 := ev874)
      (ev896 := e25) (ev960 := e26) (ev939 := e27) (ev1011 := e28) (ev990 := e29)
      (ev_edyzsqzv := e30) (ev_gkddqxhv := e31) (ev_ittpynob := e32) (ev_biaifgpd := e33)
      (ev1203 := ev1203) (ev_cwwgzxtj := e35) (ev1246 := e36) (ev_mitevvsv := e37)
      (ev_rqpeovbn := e38) (ev_xrhmaojz := e39) (ev_whimdwjd := e40) (ev1305 := e41)
      (ev1343 := ev1343) (hc1474 := hcs) .. =>
    have hsg : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := e0) (he33 := hh) .. => rw [hh]; exact e0.heap_extends
      | .Node (heq97 := h01) .. => exact absurd (Value.field.inj h01).symm one_ne_zero
    have ext_h_453 : Heap.Extends h _ :=
      hsg.trans (e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
      (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
      (e7.heap_extends.trans (e8.heap_extends.trans (e9.heap_extends.trans
      (e10.heap_extends.trans e11.heap_extends))))))))))
    have ext_501_624 : Heap.Extends m501 m624 := e13.heap_extends.trans e14.heap_extends
    have ext_501_652 : Heap.Extends m501 m652 := ext_501_624.trans ev664.heap_extends
    have ext_674_784 : Heap.Extends m674 m784 :=
      e17.heap_extends.trans (e18.heap_extends.trans (e19.heap_extends.trans e20.heap_extends))
    have ext_840_qvd : Heap.Extends m840 m_qvd := e22.heap_extends.trans e23.heap_extends
    have ext_862_luk : Heap.Extends m862 m_luk :=
      e25.heap_extends.trans (e26.heap_extends.trans (e27.heap_extends.trans
      (e28.heap_extends.trans (e29.heap_extends.trans (e30.heap_extends.trans
      (e31.heap_extends.trans (e32.heap_extends.trans e33.heap_extends)))))))
    have ext_1191_1293 : Heap.Extends m1191 m1293 :=
      e35.heap_extends.trans (e36.heap_extends.trans (e37.heap_extends.trans
      (e38.heap_extends.trans (e39.heap_extends.trans (e40.heap_extends.trans e41.heap_extends)))))
    have ext_h_501 : Heap.Extends h m501 := ext_h_453.trans ev513.heap_extends
    have ext_h_674 : Heap.Extends h m674 := ext_h_501.trans (ext_501_652.trans ev686.heap_extends)
    have ext_h_784 : Heap.Extends h m784 := ext_h_674.trans ext_674_784
    have ext_674_1293 : Heap.Extends m674 m1293 :=
      ext_674_784.trans (ev852.heap_extends.trans (ext_840_qvd.trans
        (ev874.heap_extends.trans (ext_862_luk.trans (ev1203.heap_extends.trans ext_1191_1293)))))
    have ext_840_1293 : Heap.Extends m840 m1293 :=
      ext_840_qvd.trans (ev874.heap_extends.trans (ext_862_luk.trans
        (ev1203.heap_extends.trans ext_1191_1293)))
    have hsub511 : ∀ cl ∈ cs511, cl ∈ calls := fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
    have hsub684 : ∀ cl ∈ cs684, cl ∈ calls := fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
    obtain ⟨cb', ms', hblB, hms_rep⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_h_453 hB_rep) ev513
    obtain ⟨hcb'_eq, hms'_eq⟩ := (hblB.mono hsub511).stored hH
    obtain ⟨ind₀, rest_ms, hms_cons, -, -⟩ :=
      block_nparams_spec (RepLinkedList.mono L1.repMutConst_heapMono₂ ext_501_624 hms_rep) ev664
    have hms0 : ms'[0]? = some (.indc ind₀) := by
      rw [← Array.getElem?_toList, hms_cons]; rfl
    have hmem_m652 := Route.membersRep_of_repMutConstList
      (RepLinkedList.mono L1.repMutConst_heapMono₂ ext_501_652 hms_rep)
    have hmem_m652_cons : Core.Specs.Callees.MembersRep m652 (.indc ind₀ :: rest_ms) x_members := by
      rwa [hms_cons] at hmem_m652
    have hP0_hashed : Hashed calls (Ixon.serConstant (memberProjection (Core.ixAddr bB) 0 (.indc ind₀))) :=
      Core.hashed_mono hsub684 (build_recur_addrs_head_hashed hmem_m652_cons
        (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_h_501.trans ext_501_652) hB_rep) ev686)
    have hP0_rec : recordOf E₀ (Core.iprjAddr (Core.ixAddr bB) 0) =
        some (memberProjection (Core.ixAddr bB) 0 (.indc ind₀)) := by
      have hsz0 : (Ixon.serConstant ⟨.iPrj ⟨0, Core.ixAddr bB⟩, #[], #[], #[], #[]⟩).size <
          4294967296 := serConstant_iprj_size_lt 0 bB
      have hexact0 : Ixon.deConstantExact
          (Ixon.serConstant ⟨.iPrj ⟨0, Core.ixAddr bB⟩, #[], #[], #[], #[]⟩) =
          .ok ⟨.iPrj ⟨0, Core.ixAddr bB⟩, #[], #[], #[], #[]⟩ :=
        Ixon.Verify.deConstantExact_serConstant _ (L1.projConstant_wireWF_iPrj 0 bB)
      have hproj_rec := Claim.recordOf_of_hashed hH
        (by simpa [memberProjection] using hP0_hashed) hsz0 hexact0
      simpa [Core.iprjAddr, Core.projAddr, memberProjection] using hproj_rec
    obtain ⟨-, typeAs, htype_m674, htype_map⟩ := L1.build_recur_addrs_spec hmem_m652
      (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_h_501.trans ext_501_652) hB_rep) ev686
    rw [hms_cons] at htype_map
    cases typeAs with
    | nil => simp at htype_map
    | cons t0 typeRest =>
      simp only [List.map_cons, List.mapIdx_cons, List.cons.injEq] at htype_map
      have ht0_addr : Core.ixAddr t0 = Core.iprjAddr (Core.ixAddr bB) 0 := by
        simpa [Core.projAddr, Core.Specs.Callees.memberProjInfo, Core.iprjAddr] using htype_map.1
      have hsub850 : ∀ cl ∈ cs850, cl ∈ calls := fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
      obtain ⟨recAs, hrec_m840, hrecAs_map'⟩ :=
        FamilyAlias.family_recs_list hH (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_h_784 hA_rep)
          ev852 hsub850 hA
      have hrecAs_len : recAs.length = rs'.size := by
        have := congrArg List.length hrecAs_map'
        simpa [Array.length_toList] using this
      cases recAs with
      | nil => simp at hrecAs_len; exact absurd hrecAs_len.symm hsz
      | cons a0 recRest =>
        have h0_lt : 0 < rs'.size := Nat.pos_of_ne_zero hsz
        have h0_get : rs'[0]? = some (rs'[0]'h0_lt) := getElem?_pos rs' 0 h0_lt
        obtain ⟨rc0, hrc0⟩ := hA.recrs _ (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact h0_get))
        have hmem0 : rs'[0]? = some (.recr rc0) := by rwa [hrc0] at h0_get
        have ha0_ix : Core.ixAddr a0 = Core.rprjAddr (Core.ixAddr bA) 0 := by
          have h1 : (List.map Core.ixAddr (a0 :: recRest))[0]? = some (Core.ixAddr a0) := rfl
          rw [hrecAs_map', List.getElem?_mapIdx, Array.getElem?_toList, hmem0] at h1
          simpa [Core.projAddr, Core.Specs.Callees.memberProjInfo, Core.rprjAddr] using (Option.some.inj h1).symm
        have hrec_1293 := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ext_840_1293 hrec_m840
        have htype_1293 := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          ext_674_1293 htype_m674
        have hsub1341 : ∀ cl ∈ cs1341, cl ∈ calls :=
          fun cl hcl => hsub_fam cl (by rw [hcs]; simp [hcl])
        match Obs.«KernelModeled::check_recs».obs ev1343 with
        | .Nil (ld12 := ld12) .. =>
          cases Lib.rep_nil_of_load hrec_1293 ld12
        | .Cons (m67 := m67) (p74 := p74) (cs80 := cs80) (m391 := m391) (m473 := m473)
            (ld12 := ld12) (ev82 := ev82) (ld76 := ld76)
            (ev298 := ev298) (ev359 := ev359) (ev345 := ev345) (ev403 := ev403)
            (ev485 := ev485) (ev523 := ev523) (hc1137 := hcs_cr) .. =>
          obtain ⟨a0', _, hcons0, ha0_rep, -⟩ := Lib.rep_cons_of_load hrec_1293 ld12
          injection hcons0 with ha0_eq _; subst ha0_eq
          have hsub80 : ∀ cl ∈ cs80, cl ∈ calls :=
            fun cl hcl => hsub1341 cl (by rw [hcs_cr]; simp [hcl])
          have hgood_in := hSS_in.good default lim
          obtain ⟨raw0, c_p0, hh_p0, haddr_p0, hex_p0, -, hres_p0⟩ :=
            L1.get_ci_block_trace_spec (hgood_in.sub hsub80).2 ha0_rep ev82
          have hproj0 : recordOf E₀ (Core.ixAddr a0) =
              some (memberProjection (Core.ixAddr bA) 0 (.recr rc0)) := by
            rw [ha0_ix]; exact hA.members 0 (.recr rc0) hmem0
          have hcp0_eq : c_p0 = memberProjection (Core.ixAddr bA) 0 (.recr rc0) :=
            hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hproj0)
              (Core.hashed_mono hsub80 hh_p0) haddr_p0 hex_p0
          subst hcp0_eq
          unfold L1.GetCIBlockTraceResult at hres_p0
          have hinfo_p0 : (memberProjection (Core.ixAddr bA) 0 (.recr rc0)).info =
              .rPrj ⟨(0 : Nat).toUInt64, Core.ixAddr bA⟩ := rfl
          rw [hinfo_p0] at hres_p0
          obtain ⟨-, blk0, cb0, rs0, rc0', blobs0, tree0, v0, hhB0, haB0, hexB0, hcb0, hrs0,
            hhp0, -, hld0, htr0⟩ := hres_p0
          have hcb0_eq : cb0 = c :=
            hRS.record_eq ((hRS.recordOf_eq_recordAt _).symm.trans hA.record)
              (Core.hashed_mono hsub80 hhB0) haB0 hexB0
          subst cb0
          have hrs0_eq : rs0 = rs' := Ixon.ConstantInfo.muts.inj (hcb0.symm.trans hA.muts)
          subst rs0
          have hidx0 : ({ idx := (0 : Nat).toUInt64, block := Core.ixAddr bA } : Ixon.RecursorProj).idx.toNat = 0 := rfl
          rw [hidx0, Array.getElem?_toList] at hrs0
          have hrc0_eq : rc0' = rc0 :=
            Ixon.MutConst.recr.inj (Option.some.inj (hrs0.symm.trans hmem0))
          subst rc0'
          obtain ⟨hlvls0, hp56_0, -, -, -, -, tyPtr0, rulesPtr0, blkPtr0, b_a0, plan0, -, -, hv0,
            rty0, -, hlev0, -⟩ := htr0
          rw [hv0] at hld0; rw [hld0] at ld76
          injection ld76 with hv0_eq; injection hv0_eq with _ _ hf0
          simp only [List.cons.injEq, and_true] at hf0
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hf0
          have hblob0 : ∀ x bs, (x, bs) ∈ blobs0 → E₀.blobs.get? x = some bs := by
            intro x bs hm
            obtain ⟨hhx, hxa⟩ := hhp0 (x, bs) hm
            have hrun := hRS.blobs bs (Core.hashed_mono hsub80 hhx)
            rwa [hxa] at hrun
          obtain ⟨tyP0, htyP0⟩ := LoadedReads.exprReader_read_ok (t := t)
            (blob := fun x => E₀.blobs.get? x) ht (param := id)
            (self := blockSelf t (Core.ixAddr bA) rs')
            rty0 (fun i x hx => by simp at hx) hblob0
          have ext_m67_m391 : Heap.Extends m67 m391 :=
            ev298.heap_extends.trans (ev359.heap_extends.trans (ev345.heap_extends.trans ev403.heap_extends))
          have ext_m67_m473 : Heap.Extends m67 m473 := ext_m67_m391.trans ev485.heap_extends
          have hcl_ws : (⟨"KernelCheck::validate_expr_well_scoped",
              [tyPtr0, .field 0, .field (rc0.lvls.toNat : F)], m473⟩ : Call F) ∈ calls :=
            hsub1341 _ (by rw [hcs_cr]; simp)
          obtain ⟨-, htyP0_lbb, htyP0_def⟩ := Assembly.validate_expr_well_scoped_spec
            (cx := readCtx t (fun x => E₀.blobs.get? x))
            (self := blockSelf t (Core.ixAddr bA) rs')
            hgood_in.2 hlvls0 rty0 ext_m67_m473 htyP0 ev523 hcl_ws
          have hrd0 : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
              (Ix.Kernel.Reader.recParam (List.range rc0.lvls.toNat))
              (blockSelf t (Core.ixAddr bA) rs')).read rc0.typ = .ok tyP0 := by
            rw [Assembly.recParam_range]; exact htyP0
          obtain ⟨R0, _, -, hraw_ty0, -, -⟩ := rty0.toRawTmCExactTrace (κ := Core.keyOf t)
            (ps := List.range rc0.lvls.toNat) (by simp) (by simpa using hlvls0)
            (LoadedReads.readCtx_keyAt_inv ht _) (fun i x m k hx => by simp at hx) hblob0
            hrd0 htyP0_lbb htyP0_def
          have hraw0 := hraw_ty0 0 (fun _ => .sort .zero)
          simp only [Decl.posOf_range] at hraw0
          have htype_m391 := repList_heapMono₂ Core.addrListEnum
            (Bytes.repAddressRef_heapMono₂ Core.addrTy)
            (ev82.heap_extends.trans ext_m67_m391) htype_1293
          have hfk0 := check_carriers_rawTm_familyKey hp56_0 (hraw0.toRawTm.mono ext_m67_m391)
            htype_m391 ev485
          unfold familyKey binderDom at hfk0
          rcases hs : R0.stripPis rc0.params.toNat with _ | ⟨bs, body⟩
          · simp [hs] at hfk0
          · cases body with
            | forallE mot _ _ =>
              simp only [hs, Option.bind_some] at hfk0
              cases hl : lastBinderDom mot with
              | none => simp [hl] at hfk0
              | some dom =>
                rw [hl] at hfk0
                simp only [Option.bind_some] at hfk0
                unfold headKey at hfk0
                cases hfn : dom.getAppFn with
                | const k us =>
                  rw [hfn] at hfk0
                  have hk_eq : k = Core.keyOf t (Core.ixAddr t0) := Option.some.inj hfk0
                  subst hk_eq
                  obtain ⟨_, p_rem, hrem, hin_rem⟩ :=
                    addrIn_of_rawTm_stripPis rc0.params.toNat hraw0.toRawTm hs
                  cases hrem with
                  | forallE cell_m ht_m _ _ =>
                    obtain ⟨_, _, p_dom, hdom, hin_dom⟩ := addrIn_of_rawTm_lastBinderDom ht_m hl
                    obtain ⟨b_f, hb_f, hin_bf⟩ := addrIn_of_rawTm_const_head hdom hfn
                      (fun b hb => Assembly.keyOf_injective ht hb)
                    obtain ⟨i, hi, href⟩ := usedRef_of_rawConvExpr_rmember hA.record hA.muts hmem0
                      rty0 (hin_rem b_f (.forallTy cell_m (hin_dom b_f hin_bf)))
                    rw [hb_f, ht0_addr] at href
                    exact ⟨cb', ms', ind₀, hcb'_eq, hms'_eq, hms0, hP0_rec,
                      usedRef_of_idx hA.record hi href⟩
                | bvar _ | fvar _ _ | sort _ | app _ _ | lam _ _ _
                | forallE _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
                  rw [hfn] at hfk0; cases hfk0
            | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
            | letE _ _ _ _ | lit _ | proj _ _ _ =>
              simp [hs] at hfk0

end IxVM.Refinement.Typing.TwinFamily
