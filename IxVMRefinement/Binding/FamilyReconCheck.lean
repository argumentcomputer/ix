import IxVMRefinement.Binding.FamilyReconWrap
import IxVMRefinement.Binding.FamilyReconLevels
import IxVMRefinement.Binding.GroupStores
import IxVMRefinement.Binding.PayloadCoreSpecs
import IxVMRefinement.Binding.PayloadRefSpecs
import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.Callees.Modeled
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled5
import IxVMRefinement.Obs.KernelCheck4
import IxVMRefinement.Obs.KernelCheck5
import IxVMRefinement.Obs.KernelCheck8
import IxVMRefinement.Obs.KernelCheck9
import IxVMRefinement.Obs.KernelCheck11
import IxVMRefinement.Obs.KernelCheck12
import IxVMRefinement.Obs.KernelSubst0

/-! # Family-check reconstruction: flattened families, canonical forms, and group stores

Composes `FamilyFlatObs`, `FamilyReconBuilders`, `FamilyReconLevels`, and `FamilyReconWrap` across
`KernelModeled::check_family`, `KernelModeled::check_recs`,
`KernelCheck::check_recursor_canonical_at`, and `KernelCheck::canonical_rules_at_pos` to export:

* `RecordWrapConsObs`: observed wrapper-consumption record form (`RecordReconWith` over
  `WrapConsObs (wrapAt t E) (WrapperObserved calls t)`).
* `modeledAnswers_of_stepStore`: `ModeledAnswers` over `E₀` for every address directly from a
  `StepStore`.
* `addRecBlockStore`: extends a `UsedClosed` store agreeing with `E₀` by a recursor block `r` and
  its projections (so callers need not hold `r` before checking it).
* `familyFlat_of_call`: from an accepted `KernelModeled::check_family` call at any limit, extracts
  `FamilyOfBlock`, `RecordFlat`, `BlockDerivedFlat`, recursor level-count agreement
  `rc.lvls.toNat = ind₀.lvls.toNat + off`, and minor-count agreement
  `ctorsBefore (ReconView.ofStore t E₀) es es.length = some rc.minors.toNat`.
* `familyForm_of_call`: at any group-validating limit (`lim = some n`, `n < 77`), extracts
  unconditional `RFormS t E₀ B r`; at an arbitrary limit, extracts
  `RFormS t E₀ B r ∨ RecordWrapConsObs calls t E₀ B r`.
* `remainingFamilyClauses_of_run` and `groupStoresOfRun_closed : ∀ calls, GroupStoresOfRun calls`:
  closes the run's store sequence for every binding run.
-/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Core (W KExpr KLevel KKey ExprLvEq LvEq LvEqList bmeta
  kexprEnum kexprListEnum kciEnum krrEnum krrListEnum addrTy addrListEnum ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList klevelEnum klevelListEnum)
open IxVM.Refinement.Binding
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Typing (FamBlockRecord FamRecRecord StepStore)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem mem_of_eq {α : Type*} {x : α} {l₁ l₂ : List α} (heq : l₁ = l₂) (h : x ∈ l₂) :
    x ∈ l₁ :=
  heq ▸ h

local syntax "call_mem" : tactic
local macro_rules
  | `(tactic| call_mem) =>
    `(tactic| repeat first
      | assumption
      | exact List.mem_cons_self
      | exact List.mem_append_left _ (by assumption)
      | exact List.mem_append_left _ List.mem_cons_self
      | apply List.mem_cons_of_mem
      | apply List.mem_append_right)

/-! ## Section 1: Record form, `ModeledAnswers`, and recursor-block store extension -/

/-- **Observed wrapper-consumption record form**: every recursor of `rb` for block `B` in store `E`
relates its declared type to the block's reconstruction by `WrapConsObs` (with wrapper arities
witnessed in `calls`) and has every rule following the reconstructed body. -/
def RecordWrapConsObs (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (B rb : _root_.Address) : Prop :=
  RecordReconWith (fun ty R => WrapConsObs (wrapAt t E) (WrapperObserved calls t) R ty) t E B rb

/-- `flatTotalCtors V es` equals `ctorsBefore V es es.length`. -/
theorem flatTotalCtors_eq_ctorsBefore_length (V : ReconView) :
    ∀ es : List FlatEntry, flatTotalCtors V es = ctorsBefore V es es.length
  | [] => rfl
  | e :: rest => by
    simp only [flatTotalCtors, List.length_cons, ctorsBefore]
    cases hi : V.ind e.addr with
    | none => rfl
    | some opt =>
      cases opt with
      | none => rfl
      | some info =>
        rw [flatTotalCtors_eq_ctorsBefore_length V rest]
        cases hcb : ctorsBefore V rest rest.length <;> rfl

/-- `ModeledAnswers` is antitone in the address predicate `S`. -/
theorem modeledAnswers_mono_S {rootCalls : List (Call F)} {S S' : _root_.Address → Prop}
    {V : ReconView} (himpl : ∀ a, S' a → S a) (hM : ModeledAnswers rootCalls S V) :
    ModeledAnswers rootCalls S' V :=
  fun hsub hSa rba ev => hM hsub (himpl _ hSa) rba ev

/-- **`ModeledAnswers` over `E₀` for every address**, directly from a `StepStore`:
`block_is_modeled` reads only records the run hashed, all of which reside in `E₀`, and `E₀`
stripped of `roleBinding` has no hashed collision with `rootCalls`. -/
theorem modeledAnswers_of_stepStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ Ec : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hst : StepStore rootCalls t E₀ Ec) :
    ModeledAnswers rootCalls (fun _ => True) (ReconView.ofStore t E₀) := by
  let E₀' : Ixon.Env := { E₀ with roleBinding := none }
  have hpre : ∀ x bs, View.Preimage { env := E₀' } x bs →
      Hashed rootCalls bs ∧ Address.blake3Pure bs = x := by
    intro x bs hp
    rcases hp with ⟨lc, hget, rfl⟩ | hbl | ⟨_, hrb, -⟩ | ⟨_, ht, -⟩
    · exact hS.loaded.1 x lc hget
    · exact hS.loaded.2 x bs hbl
    · cases hrb
    · cases ht
  have hnc_root : ¬ View.HashedCollision { env := E₀' } [] rootCalls := by
    intro hcol
    apply (hst.good Ix.Kernel.Env.empty none).1
    rcases hcol with ⟨x, held, bytes, hp, hh, hne, hx⟩ |
      ⟨x, held, image, blk, cb, ms, hp, hb, hex, hms, himg, hne, hx⟩ | ⟨bytes, hp, hx⟩
    · refine .inl ⟨x, held, bytes, ?_, hh, hne, hx⟩
      rcases hp with h | h | h
      · exact .inr (.inr (hpre x held h))
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · refine .inr (.inl ⟨x, held, image, blk, cb, ms, ?_, hb, hex, hms, himg, hne, hx⟩)
      rcases hp with h | h | h
      · exact .inr (.inr (hpre x held h))
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · refine .inr (.inr ⟨bytes, ?_, hx⟩)
      rcases hp with h | h
      · exact .inr (hpre _ bytes h).1
      · exact .inr h
  have hbd_root : Bounded rootCalls := (hst.good Ix.Kernel.Env.empty none).2
  intro xblk r h m cs ba hsub _ rba ev
  have hnc_cs : ¬ View.HashedCollision { env := E₀' } [] cs :=
    fun hc => hnc_root (Core.collision_mono hsub hc)
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd_root hsub
  have hag := Route.block_is_modeled_agrees (E := E₀') hnc_cs hbd_cs rba ev
  have hcov : Ingress.CanonicalHashCoverage E₀' cs := by
    intro bytes val hh hsz hex
    obtain ⟨entry, stored, bytesEq, cached⟩ := hH bytes val (Core.hashed_mono hsub hh) hsz
      (Ingress.deConstant_of_deConstantExact hex) hex
    refine ⟨⟨entry, val, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]; exact hex
  obtain ⟨b, hbE₀'⟩ := hag.known hcov
  have hr_eq := hag.value b hbE₀'
  have hbE₀ : Route.blockRoute E₀ (ixAddr ba) = some b := hbE₀'
  refine ⟨b, hbE₀, hr_eq.trans ?_⟩
  cases b <;> rfl

/-- Insert records at `addrs` from `E₀` into `R`'s constant table. -/
private def insertFromEnv (E₀ : Ixon.Env) (addrs : List _root_.Address) (R : Ixon.Env) : Ixon.Env :=
  { R with
    consts := addrs.foldl (fun m a =>
      match E₀.consts.get? a with
      | some lc => m.insert a lc
      | none => m) R.consts }

private theorem hm_get?_insert_self {α : Type} (m : Std.HashMap _root_.Address α)
    (k : _root_.Address) (v : α) : (m.insert k v).get? k = some v := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]

private theorem hm_get?_insert_ne {α : Type} (m : Std.HashMap _root_.Address α)
    {k q : _root_.Address} (hne : k ≠ q) (v : α) : (m.insert k v).get? q = m.get? q := by
  have hbeq : (k == q) = false := by
    cases hb : (k == q)
    · rfl
    · exact absurd (beq_iff_eq.mp hb) hne
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbeq,
    ← Std.HashMap.get?_eq_getElem?]
  simp

private theorem foldl_insertFromEnv_get? (E₀ : Ixon.Env) :
    ∀ (addrs : List _root_.Address) (m : Std.HashMap _root_.Address Ixon.LazyConstant)
      (y : _root_.Address),
      (∀ a ∈ addrs, (E₀.consts.get? a).isSome = true) →
      (addrs.foldl (fun m a =>
        match E₀.consts.get? a with
        | some lc => m.insert a lc
        | none => m) m).get? y =
      if y ∈ addrs then E₀.consts.get? y else m.get? y
  | [], m, y, _ => by simp
  | a :: rest, m, y, hall => by
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (hall a List.mem_cons_self)
    simp only [List.foldl_cons, hlc]
    rw [foldl_insertFromEnv_get? E₀ rest (m.insert a lc) y
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))]
    by_cases hyr : y ∈ rest
    · simp only [hyr, ↓reduceIte, List.mem_cons_of_mem _ hyr]
    · by_cases hya : y = a
      · subst hya
        simp only [hyr, ↓reduceIte, List.mem_cons_self]
        rw [hm_get?_insert_self, hlc]
      · simp only [hyr, ↓reduceIte, List.mem_cons, hya, or_self]
        exact hm_get?_insert_ne m (Ne.symm hya) lc

private theorem insertFromEnv_recordOf {E₀ R : Ixon.Env} {addrs : List _root_.Address}
    (hall : ∀ a ∈ addrs, (E₀.consts.get? a).isSome = true) (y : _root_.Address) :
    recordOf (insertFromEnv E₀ addrs R) y =
      if y ∈ addrs then recordOf E₀ y else recordOf R y := by
  unfold recordOf insertFromEnv
  dsimp only
  rw [foldl_insertFromEnv_get? E₀ addrs R.consts y hall]
  split <;> rfl

/-- **Extend a `UsedClosed` store `R` (agreeing with `E₀`) by a recursor block `r` and its
projection records**, preserving `UsedClosed`, agreement with `E₀`, `StoreLevelsOk`, and
`StoreIndParamsOk`, without requiring `Held R r` beforehand. -/
theorem addRecBlockStore {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    {r : _root_.Address} {cr : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hcl : UsedClosed R)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hlv : StoreLevelsOk t E₀ (Held R))
    (hpar : StoreIndParamsOk E₀ (Held R))
    (hrec : FamRecRecord E₀ r cr rs)
    (hcr_refs : ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
      Held R a ∨ a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m)
    (hrec_lv : ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (.recr rc) →
      rc.lvls.toNat < 4294967296 ∧
      (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cr id
          (blockSelf t r rs)).read rc.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true) ∧
      (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, rc.rules[j]? = some ru →
        (exprReader t (fun x => E₀.blobs.get? x) cr id
          (blockSelf t r rs)).read ru.rhs = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true)) :
    ∃ R' : Ixon.Env,
      UsedClosed R' ∧
      (∀ y c, recordOf R y = some c → recordOf R' y = some c) ∧
      (∀ y c c', recordOf R' y = some c → recordOf E₀ y = some c' → c = c') ∧
      ((∀ y c, recordOf R y = some c → recordOf E₀ y = some c) →
        ∀ y c, recordOf R' y = some c → recordOf E₀ y = some c) ∧
      Held R' r ∧
      (∀ y, Held R' y ↔ Held R y ∨ y = r ∨ ∃ k m, rs[k]? = some m ∧ y = memberAddr r k m) ∧
      StoreLevelsOk t E₀ (Held R') ∧
      StoreIndParamsOk E₀ (Held R') := by
  let addrs : List _root_.Address :=
    r :: (List.range rs.size).filterMap (fun k => rs[k]?.map (memberAddr r k))
  have hmem_addrs : ∀ a, a ∈ addrs ↔
      a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m := by
    intro a
    simp only [addrs, List.mem_cons, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
    constructor
    · rintro (rfl | ⟨k, _, m, hk, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, m, hk, rfl⟩
    · rintro (rfl | ⟨k, m, hk, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, (Array.getElem?_eq_some_iff.mp hk).1, m, hk, rfl⟩
  have hall_E₀ : ∀ a ∈ addrs, (E₀.consts.get? a).isSome = true := by
    intro a ha
    have hrec_some : ∀ {x c}, recordOf E₀ x = some c → (E₀.consts.get? x).isSome = true := by
      intro x c hx
      cases hget : E₀.consts.get? x with
      | none => unfold recordOf at hx; rw [hget] at hx; cases hx
      | some lc => simp [hget]
    rcases (hmem_addrs a).mp ha with rfl | ⟨k, m, hk, rfl⟩
    · exact hrec_some hrec.record
    · exact hrec_some (hrec.members k m hk)
  let R' := insertFromEnv E₀ addrs R
  have hR'_eq : ∀ y, recordOf R' y = if y ∈ addrs then recordOf E₀ y else recordOf R y :=
    insertFromEnv_recordOf hall_E₀
  have hmono : ∀ y c, recordOf R y = some c → recordOf R' y = some c := by
    intro y c hy
    rw [hR'_eq y]
    split
    · rename_i hya
      obtain ⟨cE, hcE⟩ : ∃ cE, recordOf E₀ y = some cE := by
        rcases (hmem_addrs y).mp hya with rfl | ⟨k, m, hk, rfl⟩
        · exact ⟨cr, hrec.record⟩
        · exact ⟨_, hrec.members k m hk⟩
      rw [hRagree y c cE hy hcE]; exact hcE
    · exact hy
  have hheld_mono : ∀ y, Held R y → Held R' y := by
    intro y hy
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hy
    exact Option.isSome_iff_exists.mpr ⟨c, hmono y c hc⟩
  have hR'_agree : ∀ y c c', recordOf R' y = some c → recordOf E₀ y = some c' → c = c' := by
    intro y c c' h1 h2
    rw [hR'_eq y] at h1
    split at h1
    · exact Option.some.inj (h1.symm.trans h2)
    · exact hRagree y c c' h1 h2
  have hR'_sub : (∀ y c, recordOf R y = some c → recordOf E₀ y = some c) →
      ∀ y c, recordOf R' y = some c → recordOf E₀ y = some c := by
    intro hsub y c h1
    rw [hR'_eq y] at h1
    split at h1
    · exact h1
    · exact hsub y c h1
  have hR'_r : recordOf R' r = some cr := by
    rw [hR'_eq r, ite_eq_left ((hmem_addrs r).mpr (Or.inl rfl))]
    exact hrec.record
  have hR'_proj : ∀ k m, rs[k]? = some m →
      recordOf R' (memberAddr r k m) = some (memberProjection r k m) := by
    intro k m hk
    rw [hR'_eq _, ite_eq_left ((hmem_addrs _).mpr (Or.inr ⟨k, m, hk, rfl⟩))]
    exact hrec.members k m hk
  have hheld_iff : ∀ y, Held R' y ↔ Held R y ∨ y ∈ addrs := by
    intro y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hy
      rw [hR'_eq y] at hc
      split at hc
      · exact Or.inr ‹_›
      · exact Or.inl (Option.isSome_iff_exists.mpr ⟨c, hc⟩)
    · rintro (hy | hy)
      · exact hheld_mono y hy
      · rcases (hmem_addrs y).mp hy with rfl | ⟨k, m, hk, rfl⟩
        · exact Option.isSome_iff_exists.mpr ⟨cr, hR'_r⟩
        · exact Option.isSome_iff_exists.mpr ⟨_, hR'_proj k m hk⟩
  have hcl' : UsedClosed R' := by
    constructor
    · intro a c ha
      rw [hR'_eq a] at ha
      split at ha
      · rename_i ha_in
        rcases (hmem_addrs a).mp ha_in with rfl | ⟨k, m, hk, rfl⟩
        · have heq := Option.some.inj (ha.symm.trans hrec.record); subst c
          refine ⟨?_, fun i hi y hy => ?_⟩
          · simp only [Ix.Cert.ownerOf, hrec.muts]
            exact Option.isSome_iff_exists.mpr ⟨cr, hR'_r⟩
          · have hy' : cr.refs[i]? = some y := by simpa [Array.getElem?_toList] using hy
            rcases hcr_refs i hi y hy' with hRy | rfl | ⟨k', m', hk', rfl⟩
            · exact hheld_mono y hRy
            · exact Option.isSome_iff_exists.mpr ⟨cr, hR'_r⟩
            · exact Option.isSome_iff_exists.mpr ⟨_, hR'_proj k' m' hk'⟩
        · have heq := Option.some.inj (ha.symm.trans (hrec.members k m hk)); subst c
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          refine ⟨?_, fun i hi y hy => ?_⟩
          · simp only [Ix.Cert.ownerOf, memberProjection]
            exact Option.isSome_iff_exists.mpr ⟨cr, hR'_r⟩
          · simp [usedRefIdxs, memberProjection] at hi
      · obtain ⟨hown, hrefs⟩ := hcl.1 a c ha
        exact ⟨hheld_mono _ hown, fun i hi y hy => hheld_mono _ (hrefs i hi y hy)⟩
    · intro b cb ms hb hms i m hm
      rw [hR'_eq b] at hb
      split at hb
      · rename_i hb_in
        rcases (hmem_addrs b).mp hb_in with rfl | ⟨k, m', hk', rfl⟩
        · have heq := Option.some.inj (hb.symm.trans hrec.record); subst heq
          have hmeq := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrec.muts); subst hmeq
          refine ⟨hR'_proj i m hm, fun ind hmi _ _ => ?_⟩
          obtain ⟨rc, hrc⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
          rw [hmi] at hrc; cases hrc
        · have heq := Option.some.inj (hb.symm.trans (hrec.members k m' hk')); subst heq
          obtain ⟨rc, rfl⟩ := hrec.recrs m' (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk'))
          simp [memberProjection] at hms
      · obtain ⟨hmem, hct⟩ := hcl.2 b cb ms hb hms i m hm
        exact ⟨hmono _ _ hmem, fun ind hmi j hj => hmono _ _ (hct ind hmi j hj)⟩
  have hlv' : StoreLevelsOk t E₀ (Held R') := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a c d ha hc hci hdk
      rcases (hheld_iff a).mp ha with hR | ha_in
      · exact hlv.defnVal a c d hR hc hci hdk
      · rcases (hmem_addrs a).mp ha_in with rfl | ⟨k, m, hk, rfl⟩
        · have e := Option.some.inj (hc.symm.trans hrec.record); subst e
          rw [hrec.muts] at hci; cases hci
        · have e := Option.some.inj (hc.symm.trans (hrec.members k m hk)); subst e
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          simp [memberProjection] at hci
    · intro a c p cb ms d ha hc hci hcb hcbi hm hdk
      rcases (hheld_iff a).mp ha with hR | ha_in
      · exact hlv.dPrjVal a c p cb ms d hR hc hci hcb hcbi hm hdk
      · rcases (hmem_addrs a).mp ha_in with rfl | ⟨k, m, hk, rfl⟩
        · have e := Option.some.inj (hc.symm.trans hrec.record); subst e
          rw [hrec.muts] at hci; cases hci
        · have e := Option.some.inj (hc.symm.trans (hrec.members k m hk)); subst e
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          simp [memberProjection] at hci
    · intro a c p cb ms ind ha hc hci hcb hcbi hm
      rcases (hheld_iff a).mp ha with hR | ha_in
      · exact hlv.indTy a c p cb ms ind hR hc hci hcb hcbi hm
      · rcases (hmem_addrs a).mp ha_in with rfl | ⟨k, m, hk, rfl⟩
        · have e := Option.some.inj (hc.symm.trans hrec.record); subst e
          rw [hrec.muts] at hci; cases hci
        · have e := Option.some.inj (hc.symm.trans (hrec.members k m hk)); subst e
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          simp [memberProjection] at hci
    · intro b cb ms i ind j ct hb hcb hcbi hm hct
      rcases (hheld_iff b).mp hb with hR | hb_in
      · exact hlv.ctorTy b cb ms i ind j ct hR hcb hcbi hm hct
      · rcases (hmem_addrs b).mp hb_in with rfl | ⟨k, m, hk, rfl⟩
        · have e := Option.some.inj (hcb.symm.trans hrec.record); subst e
          have e2 := Ixon.ConstantInfo.muts.inj (hcbi.symm.trans hrec.muts); subst e2
          obtain ⟨rc, hrc⟩ := hrec.recrs (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
          cases hrc
        · have e := Option.some.inj (hcb.symm.trans (hrec.members k m hk)); subst e
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          simp [memberProjection] at hcbi
    · intro rb crb rs' k rc hrb hcrb hmuts hk
      rcases (hheld_iff rb).mp hrb with hR | hrb_in
      · exact hlv.recr rb crb rs' k rc hR hcrb hmuts hk
      · rcases (hmem_addrs rb).mp hrb_in with rfl | ⟨k', m', hk', rfl⟩
        · have e := Option.some.inj (hcrb.symm.trans hrec.record); subst e
          have e2 := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hrec.muts); subst e2
          exact hrec_lv k rc hk
        · have e := Option.some.inj (hcrb.symm.trans (hrec.members k' m' hk')); subst e
          obtain ⟨rc', rfl⟩ := hrec.recrs m' (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk'))
          simp [memberProjection] at hmuts
  have hpar' : StoreIndParamsOk E₀ (Held R') := by
    refine ⟨?_, ?_⟩
    · intro b cb ms i ind j ct hb hcb hcbi hm hct
      rcases (hheld_iff b).mp hb with hR | hb_in
      · exact hpar.ctorParams b cb ms i ind j ct hR hcb hcbi hm hct
      · rcases (hmem_addrs b).mp hb_in with rfl | ⟨k, m, hk, rfl⟩
        · have e := Option.some.inj (hcb.symm.trans hrec.record); subst e
          have e2 := Ixon.ConstantInfo.muts.inj (hcbi.symm.trans hrec.muts); subst e2
          obtain ⟨rc, hrc⟩ := hrec.recrs (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
          cases hrc
        · have e := Option.some.inj (hcb.symm.trans (hrec.members k m hk)); subst e
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          simp [memberProjection] at hcbi
    · intro b cb ms i₁ i₂ ind₁ ind₂ hb hcb hcbi h1 h2
      rcases (hheld_iff b).mp hb with hR | hb_in
      · exact hpar.blockParams b cb ms i₁ i₂ ind₁ ind₂ hR hcb hcbi h1 h2
      · rcases (hmem_addrs b).mp hb_in with rfl | ⟨k, m, hk, rfl⟩
        · have e := Option.some.inj (hcb.symm.trans hrec.record); subst e
          have e2 := Ixon.ConstantInfo.muts.inj (hcbi.symm.trans hrec.muts); subst e2
          obtain ⟨rc, hrc⟩ := hrec.recrs (.indc ind₁) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h1))
          cases hrc
        · have e := Option.some.inj (hcb.symm.trans (hrec.members k m hk)); subst e
          obtain ⟨rc, rfl⟩ := hrec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          simp [memberProjection] at hcbi
  exact ⟨R', hcl', hmono, hR'_agree, hR'_sub, Option.isSome_iff_exists.mpr ⟨cr, hR'_r⟩,
    fun y => (hheld_iff y).trans (or_congr_right (hmem_addrs y)), hlv', hpar'⟩

/-- Extending `R` by a recursor block `r` and its projections preserves `ModeledAnswers` over `E₀`:
at `r` (a block of recursors only) and at each `memberAddr r k m` (an `rPrj` projection),
`block_is_modeled` returns `0` and `Route.blockRoute E₀` returns `some false`. -/
theorem modeledAnswers_addRecBlock {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R R' : Ixon.Env} {r : _root_.Address} {cr : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hS : LoadedReads.RunStore rootCalls E₀)
    (hrec : FamRecRecord E₀ r cr rs)
    (hheld : ∀ y, Held R' y ↔ Held R y ∨ y = r ∨ ∃ k m, rs[k]? = some m ∧ y = memberAddr r k m)
    (hM : ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀)) :
    ModeledAnswers rootCalls (Held R') (ReconView.ofStore t E₀) := by
  intro xblk res h m cs ba hsub hSy rba ev
  rcases (hheld (ixAddr ba)).mp hSy with hR | hr_eq | ⟨k, mc, hk, hmem_eq⟩
  · exact hM hsub hR rba ev
  · have hno_ind : (rs.toList.filter Core.Specs.Callees.isIndc).length = 0 := by
      have hnil : rs.toList.filter Core.Specs.Callees.isIndc = [] :=
        List.filter_eq_nil_iff.mpr fun m hm => by
          obtain ⟨rc, rfl⟩ := hrec.recrs m hm
          simp [Core.Specs.Callees.isIndc, Core.isIndc]
      rw [hnil]; rfl
    have hbr : Route.blockRoute E₀ (ixAddr ba) = some false := by
      rw [hr_eq]
      simp [Route.blockRoute, Route.recordRoute, Route.mutsRoute, hrec.record, hrec.muts, hno_ind]
    have hres0 : res = .field 0 := by
      match Obs.«KernelModeled::block_is_modeled».obs ev with
      | .Muts_n0 (he116 := he) .. => exact he
      | .other (he253 := he) .. => exact he
      | .Muts_n1 (cs12 := cs12) (ev14 := ev14) (ev103 := ev103) (hc241 := hc) .. =>
        have hsub12 : ∀ cl ∈ cs12, cl ∈ rootCalls := fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))
        obtain ⟨cb, ms, hbl, hrep⟩ := Claim.load_block_head rba ev14
        obtain ⟨rfl, -⟩ := (hbl.mono hsub12).record hS (hr_eq ▸ hrec.record)
        have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hrec.muts)
        subst ms
        obtain ⟨hcnt, -⟩ := Core.ModeledAux.muts_indc_count_spec
          (Route.membersRep_of_repMutConstList hrep) ev103
        rw [hno_ind] at hcnt
        exact absurd (Value.field.inj hcnt) one_ne_zero
      | .Muts_other (cs12 := cs12) (ev14 := ev14) (ev103 := ev103) (hne119 := hne0)
          (hc248 := hc) .. =>
        have hsub12 : ∀ cl ∈ cs12, cl ∈ rootCalls := fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))
        obtain ⟨cb, ms, hbl, hrep⟩ := Claim.load_block_head rba ev14
        obtain ⟨rfl, -⟩ := (hbl.mono hsub12).record hS (hr_eq ▸ hrec.record)
        have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hrec.muts)
        subst ms
        obtain ⟨hcnt, -⟩ := Core.ModeledAux.muts_indc_count_spec
          (Route.membersRep_of_repMutConstList hrep) ev103
        rw [hno_ind] at hcnt
        exact absurd hcnt hne0
    exact ⟨false, hbr, hres0⟩
  · obtain ⟨rc, rfl⟩ := hrec.recrs mc (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
    have hrec_m : recordOf E₀ (ixAddr ba) = some (memberProjection r k (.recr rc)) := by
      rw [hmem_eq]; exact hrec.members k (.recr rc) hk
    have hbr : Route.blockRoute E₀ (ixAddr ba) = some false := by
      unfold Route.blockRoute
      simp only [Option.bind, hrec_m]
      exact Route.recordRoute_of_not_muts (fun _ h => by simp [memberProjection] at h)
    have hres0 : res = .field 0 := by
      match Obs.«KernelModeled::block_is_modeled».obs ev with
      | .Muts_n0 (he116 := he) .. | .other (he253 := he) .. => exact he
      | .Muts_n1 (cs12 := cs12) (ev14 := ev14) (hc241 := hc) ..
      | .Muts_other (cs12 := cs12) (ev14 := ev14) (hc248 := hc) .. =>
        have hsub12 : ∀ cl ∈ cs12, cl ∈ rootCalls := fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))
        obtain ⟨cb, ms, hbl, -⟩ := Claim.load_block_head rba ev14
        obtain ⟨rfl, -⟩ := (hbl.mono hsub12).record hS hrec_m
        have := hbl.info; simp [memberProjection] at this
    exact ⟨false, hbr, hres0⟩

/-! ## Section 2: Raw heap-shape analysis of `build_rec_type` -/

private theorem loadValue_store_snoc (h : Heap F) {name ctor : String}
    (args : List (SourceValue F)) :
    loadValue (h ++ [.construct name ctor args]) (.ptr (.enum name) h.length) =
      .ok (.construct name ctor args) := by
  simpa [Value.type] using Ingress.loadValue_snoc h (.construct name ctor args)

/-- Literal chain of heap `"App"` cells down to a `"BVar"` head with field value `idx`. -/
private inductive HeapAppBVar (h : Heap F) : SourceValue F → F → Prop
  | bvar {p : SourceValue F} {idx : F} :
      loadValue h p = .ok (.construct kexprEnum "BVar" [.field idx]) →
      HeapAppBVar h p idx
  | app {p f a : SourceValue F} {idx : F} :
      loadValue h p = .ok (.construct kexprEnum "App" [f, a]) →
      HeapAppBVar h f idx →
      HeapAppBVar h p idx

private theorem HeapAppBVar.mono {h h' : Heap F} {p : SourceValue F} {idx : F}
    (ext : Heap.Extends h h') (hb : HeapAppBVar h p idx) : HeapAppBVar h' p idx := by
  induction hb with
  | bvar ld => exact .bvar (loadValue_mono ext ld)
  | app ld _ ih => exact .app (loadValue_mono ext ld) ih

private theorem HeapAppBVar.not_forall {h : Heap F} {p : SourceValue F} {idx : F}
    (hb : HeapAppBVar h p idx) :
    ∃ v, loadValue h p = .ok v ∧ ∀ d b l, v ≠ .construct kexprEnum "Forall" [d, b, l] := by
  cases hb with
  | bvar ld => exact ⟨_, ld, fun _ _ _ he => by simp [kexprEnum] at he⟩
  | app ld _ => exact ⟨_, ld, fun _ _ _ he => by simp [kexprEnum] at he⟩

/-- Literal chain of ≥ 1 heap `"Forall"` cells ending in a `"Srt"` body, whose last `"Forall"`
domain satisfies `HeapAppConst h _ a`. -/
private inductive HeapMotiveCarrierSrt (h : Heap F) : SourceValue F → _root_.Address → Prop
  | last {p dp bp lp xl : SourceValue F} {a : _root_.Address} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) →
      loadValue h bp = .ok (.construct kexprEnum "Srt" [xl]) →
      HeapAppConst h dp a →
      HeapMotiveCarrierSrt h p a
  | step {p dp bp lp dp' bp' lp' : SourceValue F} {a : _root_.Address} :
      loadValue h p = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) →
      loadValue h bp = .ok (.construct kexprEnum "Forall" [dp', bp', lp']) →
      HeapMotiveCarrierSrt h bp a →
      HeapMotiveCarrierSrt h p a

private theorem HeapMotiveCarrierSrt.mono {h h' : Heap F} {p : SourceValue F} {a : _root_.Address}
    (ext : Heap.Extends h h') (hm : HeapMotiveCarrierSrt h p a) : HeapMotiveCarrierSrt h' p a := by
  induction hm with
  | last ld ldb hac =>
    exact .last (loadValue_mono ext ld) (loadValue_mono ext ldb) (hac.mono ext)
  | step ld ldb _ ih =>
    exact .step (loadValue_mono ext ld) (loadValue_mono ext ldb) ih

private theorem HeapMotiveCarrierSrt.toCarrier {h : Heap F} {p : SourceValue F}
    {a : _root_.Address} (hm : HeapMotiveCarrierSrt h p a) : HeapMotiveCarrier h p a := by
  induction hm with
  | last ld ldb hac =>
    exact .last ld ldb (fun _ _ _ he => by simp [kexprEnum] at he) hac
  | step ld ldb _ ih =>
    exact .step ld ldb ih

private theorem expr_lift_srt {p xsh xcut r xl : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (lds : loadValue h p = .ok (.construct kexprEnum "Srt" [xl]))
    (ev : ObsFn W "KernelSubst::expr_lift" [p, xsh, xcut] h r h' cs) :
    ∃ xl', loadValue h' r = .ok (.construct kexprEnum "Srt" [xl']) := by
  match Obs.«KernelSubst::expr_lift».obs ev with
  | .n0 (he16 := hr) (he17 := hh) .. =>
    subst hr hh; exact ⟨xl, lds⟩
  | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := hh) .. =>
    subst hr hh; exact ⟨xl, loadValue_mono (e1.heap_extends.trans e2.heap_extends) lds⟩
  | .other_n1_other (ev36 := e1) (ev59 := e2) (he_skulcowg := hr) (he_lgvghlmw := hh) .. =>
    subst hr hh; exact ⟨xl, loadValue_mono (e1.heap_extends.trans e2.heap_extends) lds⟩
  | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) ..
  | .other_n1_App (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) ..
  | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) ..
  | .other_n1_Forall (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) ..
  | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) ..
  | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ld) .. =>
    have lds2 := loadValue_mono (e1.heap_extends.trans e2.heap_extends) lds
    rw [lds2] at ld; simp [kexprEnum] at ld

private theorem expr_lift_heapAppConst_gen :
    ∀ {h : Heap F} {p : SourceValue F} {a : _root_.Address}, HeapAppConst h p a →
      ∀ {h1 h' : Heap F} {xsh xcut r : SourceValue F} {cs : List (Call F)},
        Heap.Extends h h1 →
        ObsFn W "KernelSubst::expr_lift" [p, xsh, xcut] h1 r h' cs →
        HeapAppConst h' r a := by
  intro h p a hac
  induction hac with
  | @const p xa xus da ld ra =>
    intro h1 h' xsh xcut r cs ext ev
    match Obs.«KernelSubst::expr_lift».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh; exact (HeapAppConst.const ld ra).mono ext
    | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := hh) .. =>
      subst hr hh
      exact (HeapAppConst.const ld ra).mono (ext.trans (e1.heap_extends.trans e2.heap_extends))
    | .other_n1_other (ev36 := e1) (ev59 := e2) (he_skulcowg := hr) (he_lgvghlmw := hh) .. =>
      subst hr hh
      exact (HeapAppConst.const ld ra).mono (ext.trans (e1.heap_extends.trans e2.heap_extends))
    | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_App (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Forall (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; simp [kexprEnum] at ldw
  | @app p fp ap a ld hf ih =>
    intro h1 h' xsh xcut r cs ext ev
    match Obs.«KernelSubst::expr_lift».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh; exact (HeapAppConst.app ld hf).mono ext
    | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := hh) .. =>
      subst hr hh
      exact (HeapAppConst.app ld hf).mono (ext.trans (e1.heap_extends.trans e2.heap_extends))
    | .other_n1_App (x_f := xf) (x_a := xa) (v_hatcdjee := vf') (v_sltmkgjd := va')
        (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) (he_lhthkmdy := hr) (hm_lkqgdqjj := hh)
        (ev_dldoddhd := evf) (ev_bretmskq := eva) .. =>
      subst hr hh
      have ext02 := ext.trans (e1.heap_extends.trans e2.heap_extends)
      have ld2 := loadValue_mono ext02 ld
      rw [ld2] at ldw
      injection ldw with hv; injection hv with _ _ hl; injection hl with h1 _; subst h1
      have hfp' := ih ext02 evf
      exact .app (loadValue_store_snoc _ _)
        (hfp'.mono (eva.heap_extends.trans (Heap.Extends.snoc _ _)))
    | .other_n1_other (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) (hne_hhkiegac := hne) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; injection ldw with hv; exact (hne _ rfl hv.symm).elim
    | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Forall (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; simp [kexprEnum] at ldw

private theorem expr_lift_heapMotiveCarrierSrt :
    ∀ {h : Heap F} {p : SourceValue F} {a : _root_.Address}, HeapMotiveCarrierSrt h p a →
      ∀ {h1 h' : Heap F} {xsh xcut r : SourceValue F} {cs : List (Call F)},
        Heap.Extends h h1 →
        ObsFn W "KernelSubst::expr_lift" [p, xsh, xcut] h1 r h' cs →
        HeapMotiveCarrierSrt h' r a := by
  intro h p a hm
  induction hm with
  | @last p dp bp lp xl a ld ldb hac =>
    intro h1 h' xsh xcut r cs ext ev
    match Obs.«KernelSubst::expr_lift».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh; exact (HeapMotiveCarrierSrt.last ld ldb hac).mono ext
    | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := hh) .. =>
      subst hr hh
      exact (HeapMotiveCarrierSrt.last ld ldb hac).mono
        (ext.trans (e1.heap_extends.trans e2.heap_extends))
    | .other_n1_Forall (x_ty := xty) (x_body := xb) (v_sogttdca := vd') (v_yvzvhdcj := vb')
        (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) (he_wljmpcwa := hr) (hm_lnuidxgg := hh)
        (ev_hgsapotx := evd) (ev_gssmelog := evb) .. =>
      subst hr hh
      have ext02 := ext.trans (e1.heap_extends.trans e2.heap_extends)
      have ld2 := loadValue_mono ext02 ld
      rw [ld2] at ldw
      injection ldw with hv; injection hv with _ _ hl
      injection hl with h1 hl; injection hl with h2 _; subst h1 h2
      have hd' := expr_lift_heapAppConst_gen hac ext02 evd
      obtain ⟨xl', hxl'⟩ := expr_lift_srt (loadValue_mono (ext02.trans evd.heap_extends) ldb) evb
      exact .last (loadValue_store_snoc _ _)
        (loadValue_mono (Heap.Extends.snoc _ _) hxl')
        (hd'.mono (evb.heap_extends.trans (Heap.Extends.snoc _ _)))
    | .other_n1_other (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) (hne_ttyzfnqz := hne) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; injection ldw with hv; exact (hne _ rfl hv.symm).elim
    | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_App (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; simp [kexprEnum] at ldw
  | @step p dp bp lp dp' bp' lp' a ld ldb hmb ih =>
    intro h1 h' xsh xcut r cs ext ev
    match Obs.«KernelSubst::expr_lift».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh; exact (HeapMotiveCarrierSrt.step ld ldb hmb).mono ext
    | .other_n0 (ev36 := e1) (ev59 := e2) (he81 := hr) (he82 := hh) .. =>
      subst hr hh
      exact (HeapMotiveCarrierSrt.step ld ldb hmb).mono
        (ext.trans (e1.heap_extends.trans e2.heap_extends))
    | .other_n1_Forall (x_ty := xty) (x_body := xb) (v_sogttdca := vd') (v_yvzvhdcj := vb')
        (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) (he_wljmpcwa := hr) (hm_lnuidxgg := hh)
        (ev_hgsapotx := evd) (ev_gssmelog := evb) .. =>
      subst hr hh
      have ext02 := ext.trans (e1.heap_extends.trans e2.heap_extends)
      have ld2 := loadValue_mono ext02 ld
      rw [ld2] at ldw
      injection ldw with hv; injection hv with _ _ hl
      injection hl with h1 hl; injection hl with h2 _; subst h1 h2
      have hb' := ih (ext02.trans evd.heap_extends) evb
      cases hb' with
      | last ld' ldb' hac' =>
        exact .step (loadValue_store_snoc _ _) (loadValue_mono (Heap.Extends.snoc _ _) ld')
          ((HeapMotiveCarrierSrt.last ld' ldb' hac').mono (Heap.Extends.snoc _ _))
      | step ld' ldb' hmb' =>
        exact .step (loadValue_store_snoc _ _) (loadValue_mono (Heap.Extends.snoc _ _) ld')
          ((HeapMotiveCarrierSrt.step ld' ldb' hmb').mono (Heap.Extends.snoc _ _))
    | .other_n1_other (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) (hne_ttyzfnqz := hne) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; injection ldw with hv; exact (hne _ rfl hv.symm).elim
    | .other_n1_BVar (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_App (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Lam (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Let (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) ..
    | .other_n1_Proj (ev36 := e1) (ev59 := e2) (ld_wtarinpb := ldw) .. =>
      have ld2 := loadValue_mono (ext.trans (e1.heap_extends.trans e2.heap_extends)) ld
      rw [ld2] at ldw; simp [kexprEnum] at ldw

private theorem apply_spec_params_lifted_heapAppConst {a : _root_.Address} :
    ∀ {sps : List (SourceValue F)} {xhd xsps xd r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList kexprListEnum (fun _ v p => v = p) h sps xsps →
      HeapAppConst h xhd a →
      ObsFn W "KernelCheck::apply_spec_params_lifted" [xhd, xsps, xd] h r h' cs →
      HeapAppConst h' r a := by
  intro sps
  induction sps with
  | nil =>
    intro xhd xsps xd r h h' cs hsps hac ev
    match Obs.«KernelCheck::apply_spec_params_lifted».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. => subst hr hh; exact hac
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hne, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsps ld
      cases hne
  | cons sp rest ih =>
    intro xhd xsps xd r h h' cs hsps hac ev
    match Obs.«KernelCheck::apply_spec_params_lifted».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hsps ld
    | .Cons (x_rest := xrest) (m42 := m_l) (m88 := m_app) (ev54 := evl) (hm96 := hm2) (ev83 := evrec) (ld12 := ld) .. =>
      obtain ⟨_, _, heq, -, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsps ld
      injection heq with _ hr; subst hr
      have ext_snoc : Heap.Extends m_l m_app := by rw [hm2]; exact Heap.Extends.snoc _ _
      have ext12 := evl.heap_extends.trans ext_snoc
      have hac1 : HeapAppConst m_app (.ptr (.enum kexprEnum) m_l.length) a :=
        .app (by rw [hm2]; exact loadValue_store_snoc m_l _) (hac.mono ext12)
      exact ih (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext12 hrest) hac1 evrec

private theorem build_apply_bvars_decreasing_heapAppConst {a : _root_.Address} (n : Nat)
    (hn : n < 9223372036854775808) :
    ∀ (rem j : Nat), j + rem = n →
      ∀ {xhd xst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        HeapAppConst h xhd a →
        ObsFn W "KernelCheck::build_apply_bvars_decreasing"
          [xhd, .field (n : F), xst, .field (j : F)] h r h' cs →
        HeapAppConst h' r a := by
  intro rem
  induction rem with
  | zero =>
    intro j hj xhd xst r h h' cs hac ev
    match Obs.«KernelCheck::build_apply_bvars_decreasing».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. => subst hr hh; exact hac
    | .other (op17 := op) (hne28 := hne) .. =>
      have : j = n := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro j hj xhd xst r h h' cs hac ev
    match Obs.«KernelCheck::build_apply_bvars_decreasing».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (hm43 := hm1) (hm83 := hm2) (op130 := op1) (ev69 := evrec) .. =>
      subst hm1 hm2
      obtain rfl := binop_add_one_nat op1
      exact ih (j + 1) (by omega)
        (.app (loadValue_store_snoc _ _)
          (hac.mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)))) evrec

private theorem build_major_params_heapAppConst_nat {a : _root_.Address} (n : Nat)
    (hn : n < 9223372036854775808) :
    ∀ (rem i : Nat), i + rem = n →
      ∀ {xhd xd r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        HeapAppConst h xhd a →
        ObsFn W "KernelCheck::build_major_params"
          [xhd, .field (n : F), xd, .field (i : F)] h r h' cs →
        HeapAppConst h' r a := by
  intro rem
  induction rem with
  | zero =>
    intro i hi xhd xd r h h' cs hac ev
    match Obs.«KernelCheck::build_major_params».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. => subst hr hh; exact hac
    | .other (op17 := op) (hne28 := hne) .. =>
      have : i = n := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro i hi xhd xd r h h' cs hac ev
    match Obs.«KernelCheck::build_major_params».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (hm43 := hm1) (hm100 := hm2) (op147 := op1) (ev86 := evrec) .. =>
      subst hm1 hm2
      obtain rfl := binop_add_one_nat op1
      exact ih (i + 1) (by omega)
        (.app (loadValue_store_snoc _ _)
          (hac.mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)))) evrec

private theorem build_major_indices_heapAppConst {a : _root_.Address} (n : Nat)
    (hn : n < 9223372036854775808) :
    ∀ (rem i : Nat), i + rem = n →
      ∀ {xhd r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        HeapAppConst h xhd a →
        ObsFn W "KernelCheck::build_major_indices"
          [xhd, .field (n : F), .field (i : F)] h r h' cs →
        HeapAppConst h' r a := by
  intro rem
  induction rem with
  | zero =>
    intro i hi xhd r h h' cs hac ev
    match Obs.«KernelCheck::build_major_indices».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. => subst hr hh; exact hac
    | .other (op17 := op) (hne28 := hne) .. =>
      have : i = n := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro i hi xhd r h h' cs hac ev
    match Obs.«KernelCheck::build_major_indices».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (hm43 := hm1) (hm90 := hm2) (op130 := op1) (ev77 := evrec) .. =>
      subst hm1 hm2
      obtain rfl := binop_add_one_nat op1
      exact ih (i + 1) (by omega)
        (.app (loadValue_store_snoc _ _)
          (hac.mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)))) evrec

private theorem apply_indices_in_conclusion_heapAppBVar {idx : F} (n : Nat)
    (hn : n < 9223372036854775808) :
    ∀ (rem i : Nat), i + rem = n →
      ∀ {xhd r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        HeapAppBVar h xhd idx →
        ObsFn W "KernelCheck::apply_indices_in_conclusion"
          [xhd, .field (n : F), .field (i : F)] h r h' cs →
        HeapAppBVar h' r idx := by
  intro rem
  induction rem with
  | zero =>
    intro i hi xhd r h h' cs hab ev
    match Obs.«KernelCheck::apply_indices_in_conclusion».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. => subst hr hh; exact hab
    | .other (op17 := op) (hne28 := hne) .. =>
      have : i = n := by omega
      subst this; simp only [evalBinOp, sub_self, Except.ok.injEq] at op
      exact (hne op.symm).elim
  | succ rem ih =>
    intro i hi xhd r h h' cs hab ev
    match Obs.«KernelCheck::apply_indices_in_conclusion».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (hm43 := hm1) (hm82 := hm2) (op122 := op1) (ev69 := evrec) .. =>
      subst hm1 hm2
      obtain rfl := binop_add_one_nat op1
      exact ih (i + 1) (by omega)
        (.app (loadValue_store_snoc _ _)
          (hab.mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)))) evrec

private theorem repList_to_rawKExprList {κ : _root_.Address → KKey} {h : Heap F} :
    ∀ {xs : List KExpr} {p : SourceValue F},
      RepList kexprListEnum (TmOExact κ) h xs p →
      ∃ ds : List (SourceValue F), ds.length = xs.length ∧
        RepList kexprListEnum (fun _ v q => v = q) h ds p
  | [], p, hr => by
    cases hr with
    | nil hld => exact ⟨[], rfl, .nil hld⟩
  | _ :: rest, p, hr => by
    cases hr with
    | cons hld _ hrest =>
      obtain ⟨ds, hlen, hds⟩ := repList_to_rawKExprList hrest
      exact ⟨_ :: ds, by simp [hlen], .cons hld rfl hds⟩

private theorem collect_n_doms_whnf_rawList :
    ∀ (n : Nat), n < 9223372036854775808 →
      ∀ {xrc xty xtypes xdoms xafter : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        ObsFn W "KernelCheck::collect_n_doms_whnf"
          [xrc, xty, .field (n : F), xtypes] h (.tuple [xdoms, xafter]) h' cs →
        ∃ ds : List (SourceValue F), ds.length ≤ n ∧
          RepList kexprListEnum (fun _ v q => v = q) h' ds xdoms := by
  intro n
  induction n with
  | zero =>
    intro _ xrc xty xtypes xdoms xafter h h' cs ev
    match Obs.«KernelCheck::collect_n_doms_whnf».obs ev with
    | .n0 (he19 := hr) (hm29 := hm) (he40 := hh) .. =>
      subst hm hh
      injection hr with hl; injection hl with h1 _; subst h1
      exact ⟨[], Nat.le_refl 0, Lib.rep_store_nil h⟩
    | .other_Forall (hne42 := hne) .. | .other_other_Forall (hne42 := hne) ..
    | .other_other_other (hne42 := hne) .. =>
      exact (hne rfl).elim
  | succ n ih =>
    intro hn xrc xty xtypes xdoms xafter h h' cs ev
    match Obs.«KernelCheck::collect_n_doms_whnf».obs ev with
    | .n0 (hv14 := hv) .. =>
      have : ((n + 1 : Nat) : F).val = (0 : F).val := congrArg ZMod.val (Value.field.inj hv)
      rw [fval_natCast (by omega)] at this; simp at this
    | .other_Forall (x_dom := xd) (x_rest := xrest) (op127 := op) (hm138 := hm1)
        (ev95 := evrec) (he178 := hr) (hm188 := hm2) (he215 := hh) .. =>
      subst hm1 hm2 hh
      injection hr with hl; injection hl with h1 _; subst h1
      obtain rfl := binop_sub_one_nat (a := n + 1) (by omega) op
      obtain ⟨ds, hle, hds⟩ := ih (by omega) (by simpa using evrec)
      exact ⟨xd :: ds, by simp; omega,
        Lib.rep_store_cons (fun _ _ _ _ _ h => h) rfl hds⟩
    | .other_other_Forall (x_dom := xd) (x_rest := xrest) (op332 := op) (hm343 := hm1)
        (ev300 := evrec) (he383 := hr) (hm393 := hm2) (he420 := hh) .. =>
      subst hm1 hm2 hh
      injection hr with hl; injection hl with h1 _; subst h1
      obtain rfl := binop_sub_one_nat (a := n + 1) (by omega) op
      obtain ⟨ds, hle, hds⟩ := ih (by omega) (by simpa using evrec)
      exact ⟨xd :: ds, by simp; omega,
        Lib.rep_store_cons (fun _ _ _ _ _ h => h) rfl hds⟩
    | .other_other_other (he431 := hr) (hm441 := hm) (he452 := hh) .. =>
      subst hm hh
      injection hr with hl; injection hl with h1 _; subst h1
      exact ⟨[], Nat.zero_le _, Lib.rep_store_nil _⟩

private theorem collect_index_doms_rawList :
    ∀ (n : Nat), n < 9223372036854775808 →
      ∀ {xrc xty xtypes r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        ObsFn W "KernelCheck::collect_index_doms"
          [xrc, xty, .field (n : F), xtypes] h r h' cs →
        ∃ ds : List (SourceValue F), ds.length ≤ n ∧
          RepList kexprListEnum (fun _ v q => v = q) h' ds r := by
  intro n
  induction n with
  | zero =>
    intro _ xrc xty xtypes r h h' cs ev
    match Obs.«KernelCheck::collect_index_doms».obs ev with
    | .n0 (he19 := hr) (hm18 := hm) .. =>
      subst hr hm
      exact ⟨[], Nat.le_refl 0, Lib.rep_store_nil h⟩
    | .other_Forall (hne24 := hne) .. | .other_other_Forall (hne24 := hne) ..
    | .other_other_other (hne24 := hne) .. =>
      exact (hne rfl).elim
  | succ n ih =>
    intro hn xrc xty xtypes r h h' cs ev
    match Obs.«KernelCheck::collect_index_doms».obs ev with
    | .n0 (hv14 := hv) .. =>
      have : ((n + 1 : Nat) : F).val = (0 : F).val := congrArg ZMod.val (Value.field.inj hv)
      rw [fval_natCast (by omega)] at this; simp at this
    | .other_Forall (x_dom := xd) (he67 := hr) (hm66 := hm2) (op123 := op) (hm134 := hm1)
        (ev91 := evrec) .. =>
      subst hr hm1 hm2
      obtain rfl := binop_sub_one_nat (a := n + 1) (by omega) op
      obtain ⟨ds, hle, hds⟩ := ih (by omega) (by simpa using evrec)
      exact ⟨xd :: ds, by simp; omega,
        Lib.rep_store_cons (fun _ _ _ _ _ h => h) rfl hds⟩
    | .other_other_Forall (x_dom := xd) (he227 := hr) (hm226 := hm2) (op283 := op) (hm294 := hm1)
        (ev251 := evrec) .. =>
      subst hr hm1 hm2
      obtain rfl := binop_sub_one_nat (a := n + 1) (by omega) op
      obtain ⟨ds, hle, hds⟩ := ih (by omega) (by simpa using evrec)
      exact ⟨xd :: ds, by simp; omega,
        Lib.rep_store_cons (fun _ _ _ _ _ h => h) rfl hds⟩
    | .other_other_other (he323 := hr) (hm322 := hm) .. =>
      subst hr hm
      exact ⟨[], Nat.zero_le _, Lib.rep_store_nil _⟩

private theorem list_lift_indices_rawList :
    ∀ (ds : List (SourceValue F)) {xdoms xsh xi r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList kexprListEnum (fun _ v q => v = q) h ds xdoms →
      ObsFn W "KernelCheck::list_lift_indices" [xdoms, xsh, xi] h r h' cs →
      ∃ ds' : List (SourceValue F), ds'.length = ds.length ∧
        RepList kexprListEnum (fun _ v q => v = q) h' ds' r := by
  intro ds
  induction ds with
  | nil =>
    intro xdoms xsh xi r h h' cs hds ev
    match Obs.«KernelCheck::list_lift_indices».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm; exact ⟨[], rfl, Lib.rep_store_nil h⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hne, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      cases hne
  | cons d rest ih =>
    intro xdoms xsh xi r h h' cs hds ev
    match Obs.«KernelCheck::list_lift_indices».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hds ld
    | .Cons (x_rest := xrest) (v54 := vd') (ld12 := ld) (he50 := hr) (hm49 := hm)
        (ev67 := evl) (ev103 := evrec) .. =>
      subst hr hm
      obtain ⟨_, _, heq, -, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      injection heq with _ hr; subst hr
      obtain ⟨ds', hlen, hds'⟩ := ih
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) evl.heap_extends hrest) evrec
      exact ⟨vd' :: ds', by simp [hlen], Lib.rep_store_cons (fun _ _ _ _ _ h => h) rfl hds'⟩

private theorem wrap_foralls_heapForalls :
    ∀ (ds : List (SourceValue F)) {xbody xdoms xdl r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList kexprListEnum (fun _ v q => v = q) h ds xdoms →
      ObsFn W "KernelCheck::wrap_foralls" [xbody, xdoms, xdl] h r h' cs →
      HeapForalls h' ds.length r xbody ∧
      ∀ (j : Nat) (d : SourceValue F), ds[j]? = some d →
        ∃ q bp lp, HeapForalls h' j r q ∧
          loadValue h' q = .ok (.construct kexprEnum "Forall" [d, bp, lp]) := by
  intro ds
  induction ds with
  | nil =>
    intro xbody xdoms xdl r h h' cs hds ev
    match Obs.«KernelCheck::wrap_foralls».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh; exact ⟨.zero r, fun _ _ h => by simp at h⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hne, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      cases hne
  | cons d rest ih =>
    intro xbody xdoms xdl r h h' cs hds ev
    match Obs.«KernelCheck::wrap_foralls».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hds ld
    | .Cons (x_dom := xd) (x_rest := xrest) (v50 := v50) (m60 := m_rec) (ld12 := ld) (he45 := hr)
        (hm44 := hm) (ev70 := evrec) .. =>
      subst hr hm
      obtain ⟨_, _, heq, hd_eq, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      injection heq with h1 h2; subst h1 h2; subst hd_eq
      obtain ⟨hf, hdoms⟩ := ih hrest evrec
      have hcell : loadValue (m_rec ++ [.construct kexprEnum "Forall" [d, v50, xdl]])
          (.ptr (.enum kexprEnum) m_rec.length) =
          .ok (.construct kexprEnum "Forall" [d, v50, xdl]) := loadValue_store_snoc m_rec _
      refine ⟨.succ hcell (hf.mono (Heap.Extends.snoc _ _)), fun j dj hj => ?_⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
        exact ⟨_, v50, xdl, .zero _, hcell⟩
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        obtain ⟨q, bp, lp, hfj, ldj⟩ := hdoms j' dj hj
        exact ⟨q, bp, lp, .succ hcell (hfj.mono (Heap.Extends.snoc _ _)),
          loadValue_mono (Heap.Extends.snoc _ _) ldj⟩

private theorem wrap_foralls_heapMotiveCarrierSrt {a : _root_.Address} :
    ∀ (ds : List (SourceValue F)) {xbody xdoms xdl r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList kexprListEnum (fun _ v q => v = q) h ds xdoms →
      HeapMotiveCarrierSrt h xbody a →
      ObsFn W "KernelCheck::wrap_foralls" [xbody, xdoms, xdl] h r h' cs →
      HeapMotiveCarrierSrt h' r a := by
  intro ds
  induction ds with
  | nil =>
    intro xbody xdoms xdl r h h' cs hds hm ev
    match Obs.«KernelCheck::wrap_foralls».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. => subst hr hh; exact hm
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hne, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      cases hne
  | cons d rest ih =>
    intro xbody xdoms xdl r h h' cs hds hm ev
    match Obs.«KernelCheck::wrap_foralls».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hds ld
    | .Cons (x_dom := xd) (x_rest := xrest) (v50 := v50) (ld12 := ld) (he45 := hr)
        (hm44 := hm_eq) (ev70 := evrec) .. =>
      subst hr hm_eq
      obtain ⟨_, _, heq, -, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      injection heq with _ h2; subst h2
      have hm' := ih hrest hm evrec
      cases hm' with
      | last ld' ldb' hac' =>
        exact .step (loadValue_store_snoc _ _) (loadValue_mono (Heap.Extends.snoc _ _) ld')
          ((HeapMotiveCarrierSrt.last ld' ldb' hac').mono (Heap.Extends.snoc _ _))
      | step ld' ldb' hmb' =>
        exact .step (loadValue_store_snoc _ _) (loadValue_mono (Heap.Extends.snoc _ _) ld')
          ((HeapMotiveCarrierSrt.step ld' ldb' hmb').mono (Heap.Extends.snoc _ _))

private theorem build_motive_type_flat_heapShape {κ : _root_.Address → KKey}
    {da : Bytes.Address} {nP nI : Nat} {isAux : Bool} {sps : List KExpr}
    {xrc xa xity xown xus xelim xsps xpt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 9223372036854775808) (hnI : nI < 9223372036854775808)
    (ra : Bytes.RepAddressRef addrTy h da xa)
    (hsps : RepList kexprListEnum (TmOExact κ) h sps xsps)
    (ev : ObsFn W "KernelCheck::build_motive_type_flat"
      [xrc, xa, xity, xown, .field (nI : F), xus, xelim, .field (nP : F),
        auxVal isAux, xsps, xpt] h r h' cs) :
    HeapMotiveCarrierSrt h' r (ixAddr da) := by
  match Obs.«KernelCheck::build_motive_type_flat».obs ev with
  | .run (m93 := m_3) (m139 := m_c) (v169 := v_4) (m170 := m_4) (v223 := v_5) (m224 := m_5)
      (m261 := m_s) (m284 := m_su) (m300 := m_z) (m313 := m_f)
      (ev14 := ev1) (ev44 := ev2) (ev105 := ev3) (hm149 := hm_c) (ev182 := ev4)
      (ev236 := ev5) (hm271 := hm_s) (hm294 := hm_su) (hm308 := hm_z) (hm323 := hm_f)
      (ev356 := ev6) .. =>
    obtain ⟨dsI, -, hdsI⟩ := collect_index_doms_rawList nI hnI ev3
    have ext03 := ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)
    have ext_c : Heap.Extends m_3 m_c := by rw [hm_c]; exact Heap.Extends.snoc _ _
    have hac0 : HeapAppConst m_c (.ptr (.enum kexprEnum) m_3.length) (ixAddr da) :=
      .const (by rw [hm_c]; exact loadValue_store_snoc m_3 _)
        (Bytes.repAddressRef_heapMono₂ addrTy (ext03.trans ext_c) ra)
    have hac4 : HeapAppConst m_4 v_4 (ixAddr da) := by
      match Obs.«KernelCheck::build_major_args_for_member».obs ev4 with
      | .n0 (ev20 := evmp) .. =>
        exact build_major_params_heapAppConst_nat nP hnP nP 0 (by omega) hac0 (by simpa using evmp)
      | .other (ev62 := evsp) .. =>
        obtain ⟨rawSp, -, hrawSp⟩ := repList_to_rawKExprList hsps
        exact apply_spec_params_lifted_heapAppConst
          (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) (ext03.trans ext_c) hrawSp) hac0 evsp
    have hac5 : HeapAppConst m_5 v_5 (ixAddr da) :=
      build_major_indices_heapAppConst nI hnI nI 0 (by omega) hac4 (by simpa using ev5)
    have ext_s : Heap.Extends m_5 m_s := by rw [hm_s]; exact Heap.Extends.snoc _ _
    have ext_z : Heap.Extends m_s m_z := by rw [hm_z]; exact Heap.Extends.snoc _ _
    have ext_su : Heap.Extends m_z m_su := by rw [hm_su]; exact Heap.Extends.snoc _ _
    have ext_f : Heap.Extends m_su m_f := by rw [hm_f]; exact Heap.Extends.snoc _ _
    have ext5_f : Heap.Extends m_5 m_f := ext_s.trans (ext_z.trans (ext_su.trans ext_f))
    have hlds : loadValue m_f (.ptr (.enum kexprEnum) m_5.length) =
        .ok (.construct kexprEnum "Srt" [xelim]) :=
      loadValue_mono (ext_z.trans (ext_su.trans ext_f))
        (by rw [hm_s]; exact loadValue_store_snoc m_5 [xelim])
    have hm0 : HeapMotiveCarrierSrt m_f (.ptr (.enum kexprEnum) m_su.length) (ixAddr da) :=
      .last (by rw [hm_f]; exact loadValue_store_snoc m_su _) hlds (hac5.mono ext5_f)
    have ext3_f := ext_c.trans (ev4.heap_extends.trans (ev5.heap_extends.trans ext5_f))
    exact wrap_foralls_heapMotiveCarrierSrt dsI
      (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext3_f hdsI) hm0 ev6

private theorem build_all_motives_walk_heapShape {rootCalls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    {nP : Nat} (hnP : nP < 9223372036854775808)
    {xrc xelim xpt : SourceValue F} :
    ∀ (es : List FlatEntry) (j : Nat) {xflat r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      (∀ cl ∈ cs, cl ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      (∀ e ∈ es, Held R e.addr ∧ ∃ info, indDataAt t E₀ e.addr = some (some info)) →
      ObsFn W "KernelCheck::build_all_motives_walk"
        [xrc, xflat, xelim, .field (nP : F), .field (j : F), xpt] h r h' cs →
      ∃ ds : List (SourceValue F),
        ds.length = es.length ∧
        RepList kexprListEnum (fun _ v q => v = q) h' ds r ∧
        ∀ (i : Nat) (d : SourceValue F) (e : FlatEntry),
          ds[i]? = some d → es[i]? = some e → HeapMotiveCarrierSrt h' d e.addr := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRagree hcl hlv
  intro es
  induction es with
  | nil =>
    intro j xflat r h h' cs _ hes _ ev
    match Obs.«KernelCheck::build_all_motives_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact ⟨[], rfl, Lib.rep_store_nil h, fun _ _ _ h1 _ => by simp at h1⟩
    | .Cons_Induct (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hne, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hne
  | cons e rest ih =>
    intro j xflat r h h' cs hsub hes hall ev
    match Obs.«KernelCheck::build_all_motives_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_other (x_member_addr := xa) (v82 := vci) (p90 := pci) (cs96 := cs1)
        (ld12 := ld) (ev98 := evci) (ld92 := ldci) (hne393 := hne) (hc451 := hc) .. =>
      obtain ⟨_, _, heq, he_rep, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection heq with h1 _; subst h1
      obtain ⟨_, _, _, da, htup, rda, hda, -, -⟩ := he_rep
      injection htup with hl; injection hl with h1 _; subst h1
      obtain ⟨hSe, info0, hinfo0⟩ := hall e List.mem_cons_self
      rw [← hda] at hSe hinfo0
      obtain ⟨-, hOther⟩ := hIA (fun cl hcl' => hsub cl (mem_of_eq hc (by call_mem)))
        hSe rda evci ldci
      have hnone := hOther hne
      change indDataAt t E₀ (ixAddr da) = some none at hnone
      rw [hinfo0] at hnone; cases hnone
    | .Cons_Induct (x_rest := xrest) (x_member_addr := xa) (x_is_aux := xaux)
        (x_spec_params := xsp) (x_occ_us := xou) (p90 := pci) (cs96 := cs1)
        (x_m_n_indices := xni) (v168 := vmot) (cs179 := cs2) (v270 := vmotL) (cs281 := cs3)
        (v316 := vrest) (cs333 := cs4) (ld12 := ld) (ev98 := evci) (ld92 := ldci)
        (ev181 := evmot) (ev283 := evlift) (he311 := hr) (hm310 := hm) (op383 := op1)
        (ev335 := evrec) (hc392 := hc) .. =>
      subst hr hm
      obtain ⟨_, _, heq, he_rep, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨_, _, _, da, htup, rda, hda, hsp_rep, -⟩ := he_rep
      injection htup with hl
      injection hl with h1 hl; injection hl with h2 hl; injection hl with h3 hl
      injection hl with h4 _; subst h1 h2 h3 h4
      obtain ⟨hSe, info0, hinfo0⟩ := hall e List.mem_cons_self
      rw [← hda] at hSe hinfo0
      obtain ⟨hInd, -⟩ := hIA (fun cl hcl' => hsub cl (mem_of_eq hc (by call_mem)))
        hSe rda evci ldci
      obtain ⟨info, _, hia, -, -, hni56, -, -, -, -, -, -, -, hniEq, -⟩ :=
        hInd _ _ _ _ _ _ _ _ rfl
      subst hniEq
      have hmot0 : HeapMotiveCarrierSrt _ vmot (ixAddr da) :=
        build_motive_type_flat_heapShape hnP (by omega)
          (Bytes.repAddressRef_heapMono₂ addrTy evci.heap_extends rda)
          (tmOExactList_mono evci.heap_extends hsp_rep) evmot
      have hmotL : HeapMotiveCarrierSrt _ vmotL (ixAddr da) :=
        expr_lift_heapMotiveCarrierSrt hmot0 (Heap.Extends.refl _) evlift
      obtain rfl := binop_add_one_nat op1
      have ext03 := evci.heap_extends.trans (evmot.heap_extends.trans evlift.heap_extends)
      obtain ⟨ds, hlen, hds, hds_shape⟩ := ih (j + 1)
        (fun cl hcl' => hsub cl (mem_of_eq hc (by call_mem)))
        (flatList_mono ext03 hrest)
        (fun x hx => hall x (List.mem_cons_of_mem _ hx)) evrec
      refine ⟨vmotL :: ds, by simp [hlen],
        Lib.rep_store_cons (fun _ _ _ _ _ h => h) rfl hds, fun i di ei hdi hei => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hdi hei
        subst hdi hei
        rw [← hda]
        exact hmotL.mono (evrec.heap_extends.trans (Heap.Extends.snoc _ _))
      | succ i' =>
        simp only [List.getElem?_cons_succ] at hdi hei
        exact (hds_shape i' di ei hdi hei).mono (Heap.Extends.snoc _ _)

private theorem rawKExprList_length_spec {ds : List (SourceValue F)} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum (fun _ v q => v = q) h ds l) :
    r = .field (ds.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := fun _ v q => v = q)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

private theorem repUnitList_to_rawKExprList {h : Heap F} :
    ∀ {xs : List Unit} {p : SourceValue F},
      RepList kexprListEnum (fun _ (_ : Unit) _ => True) h xs p →
      ∃ ds : List (SourceValue F), ds.length = xs.length ∧
        RepList kexprListEnum (fun _ v q => v = q) h ds p
  | [], p, hr => by
    cases hr with
    | nil hld => exact ⟨[], rfl, .nil hld⟩
  | () :: rest, p, hr => by
    cases hr with
    | cons hld _ hrest =>
      obtain ⟨ds, hlen, hds⟩ := repUnitList_to_rawKExprList hrest
      exact ⟨_ :: ds, by simp [hlen], .cons hld rfl hds⟩

/-- **Raw heap shape of `KernelCheck::build_rec_type`**, proved without `FlatEntryParamsOk` or
`prim = B`: produces `flatTotalCtors = some tot`, the exact leading `Forall` chain
(`lenP + es.length + tot + lenI + 1`), the terminal conclusion `HeapAppBVar`, `HeapMotiveCarrier`
at every motive `j < es.length`, and `HeapAppConst` at the major premise (`es[selfPos].addr`). -/
private theorem build_rec_type_heap_shape {rootCalls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    {es : List FlatEntry} {ek : FlatEntry} {nP nI selfPos : Nat}
    {xrc xity xindnl xelim xoff xflat xfop r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hnI : nI < 72057594037927936)
    (hes_lt : es.length < 72057594037927936)
    (hself_lt : selfPos < es.length) (hek : es[selfPos]? = some ek)
    (hsub : ∀ cl ∈ cs, cl ∈ rootCalls)
    (hes : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat)
    (hall : ∀ e ∈ es, Held R e.addr ∧ ∃ info, indDataAt t E₀ e.addr = some (some info))
    (ev : ObsFn W "KernelCheck::build_rec_type"
      [xrc, xity, xindnl, .field (nP : F), .field (nI : F),
        xelim, xoff, xflat, xfop, .field (selfPos : F)] h r h' cs) :
    ∃ (lenP lenI tot : Nat) (xconcl : SourceValue F),
      lenP ≤ nP ∧ lenI ≤ nI ∧ tot < 2 ^ 39 ∧
      flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧
      HeapForalls h' (lenP + es.length + tot + lenI + 1) r xconcl ∧
      HeapAppBVar h' xconcl (((es.length + tot + nI - selfPos : Nat) : F)) ∧
      (∀ (j : Nat) (ej : FlatEntry), es[j]? = some ej →
        ∃ q dp bp lp, HeapForalls h' (lenP + j) r q ∧
          loadValue h' q = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) ∧
          HeapMotiveCarrier h' dp ej.addr) ∧
      (∃ q dp bp lp, HeapForalls h' (lenP + es.length + tot + lenI) r q ∧
        loadValue h' q = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) ∧
        HeapAppConst h' dp ek.addr) := by
  have handle_from :
      ∀ {xpty xpnl : SourceValue F} {m0 : Heap F} {cs_f : List (Call F)},
        Heap.Extends h m0 →
        (∀ cl ∈ cs_f, cl ∈ rootCalls) →
        ObsFn W "KernelCheck::build_rec_type_from"
          [xrc, xpty, xpnl, xity, xindnl, .field (nP : F), .field (nI : F),
            xelim, xoff, xflat, xfop, .field (selfPos : F)] m0 r h' cs_f →
        ∃ (lenP lenI tot : Nat) (xconcl : SourceValue F),
          lenP ≤ nP ∧ lenI ≤ nI ∧ tot < 2 ^ 39 ∧
          flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧
          HeapForalls h' (lenP + es.length + tot + lenI + 1) r xconcl ∧
          HeapAppBVar h' xconcl (((es.length + tot + nI - selfPos : Nat) : F)) ∧
          (∀ (j : Nat) (ej : FlatEntry), es[j]? = some ej →
            ∃ q dp bp lp, HeapForalls h' (lenP + j) r q ∧
              loadValue h' q = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) ∧
              HeapMotiveCarrier h' dp ej.addr) ∧
          (∃ q dp bp lp, HeapForalls h' (lenP + es.length + tot + lenI) r q ∧
            loadValue h' q = .ok (.construct kexprEnum "Forall" [dp, bp, lp]) ∧
            HeapAppConst h' dp ek.addr) := by
    intro xpty xpnl m0 cs_f ext0 hsub_f evf
    have hes0 := flatList_mono ext0 hes
    match Obs.«KernelCheck::build_rec_type_from».obs evf with
    | .run (v1 := vnmot) (cs12 := cs1) (cs43 := cs2) (cs104 := cs3)
        (x_param_doms := xpdoms)
        (v159 := vmots) (m160 := m_mot) (cs170 := cs5)
        (v205 := vmins) (m206 := m_min) (cs216 := cs6)
        (v275 := vnmin) (cs286 := cs7) (cs308 := cs8)
        (x_self_addr := xsa) (x_self_is_aux := xsaux)
        (x_self_spec_params := xssp) (x_self_occ_us := xsou)
        (cs364 := cs9) (cs435 := cs10) (cs465 := cs11)
        (v515 := vids) (cs526 := cs13) (cs563 := cs12)
        (v574 := vlids) (m575 := m_li) (cs585 := cs14) (m621 := m_c)
        (v687 := vmaj1) (m688 := m_ms) (cs698 := cs15)
        (v775 := vmaj2) (m776 := m_mi) (cs786 := cs16)
        (v887 := vconcl0) (m888 := m_aic) (cs898 := cs17)
        (v1007 := vw1) (cs1018 := cs18)
        (v1045 := vw2) (cs1056 := cs19)
        (v1083 := vw3) (cs1094 := cs20) (cs1124 := cs21)
        (ev14 := evlen1) (ev45 := evbpr) (ev106 := evinst1) (hm139 := hm_nil)
        (ev83 := evcd) (ev172 := evmots) (ev218 := evmins) (ev288 := evlen2)
        (ev310 := evfma) (ev366 := evsci) (ev437 := evinst2) (ev467 := evpeel)
        (ev565 := evrev) (ev528 := evcid) (op611 := op_s1) (ev587 := evli)
        (hm631 := hm_c) (op682 := op_a1) (op674 := op_a2) (op666 := op_a3)
        (op734 := op_top) (op757 := op_l1) (op749 := op_l2)
        (ev700 := evms) (ev788 := evmi)
        (op827 := op_c1) (op852 := op_c2) (op861 := op_c3) (op844 := op_c4)
        (hm875 := hm_bv) (ev900 := evaic)
        (hm935 := hm_app) (hm957 := hm_bv0) (hm979 := hm_majf)
        (ev1020 := evw1) (ev1058 := evw2) (ev1096 := evw3) (ev1126 := evw4)
        (hc1151 := hcf) .. =>
      subst hm_nil hm_bv0 hm_app hm_majf
      obtain ⟨rfl, hm2⟩ := flat_length_spec evlen1 hes0
      subst hm2
      obtain ⟨dsP, hlenP, hdsP⟩ := collect_n_doms_whnf_rawList nP (by omega) evcd
      have ext_cd := evbpr.heap_extends.trans (evinst1.heap_extends.trans
        ((Heap.Extends.snoc _ _).trans evcd.heap_extends))
      -- motives
      obtain ⟨dsMot, hlenMot, hdsMot, hmot_shape⟩ :
          ∃ dsMot : List (SourceValue F), dsMot.length = es.length ∧
            RepList kexprListEnum (fun _ v q => v = q) m_mot dsMot vmots ∧
            ∀ (j : Nat) (d : SourceValue F) (ej : FlatEntry),
              dsMot[j]? = some d → es[j]? = some ej → HeapMotiveCarrierSrt m_mot d ej.addr := by
        match Obs.«KernelCheck::build_all_motives».obs evmots with
        | .run (cs4 := cs_mw) (ev58 := evctx) (ev6 := evwalk) (hc83 := hc_m) .. =>
          exact build_all_motives_walk_heapShape ht hwf hS hH hbd hRagree hcl hlv
            (nP := nP) (by omega) es 0
            (fun cl (hcl' : cl ∈ cs_mw) => hsub_f cl (mem_of_eq hcf (by
              have hm1 : cl ∈ cs5 := mem_of_eq hc_m (by call_mem)
              call_mem)))
            (flatList_mono (ext_cd.trans evctx.heap_extends) hes0) hall (by simpa using evwalk)
      -- minors via `build_all_minors_walk_rawLen`
      obtain ⟨tot, htot, hdsMin_u⟩ :
          ∃ tot : Nat, flatTotalCtors (ReconView.ofStore t E₀) es = some tot ∧
            RepList kexprListEnum (fun _ (_ : Unit) _ => True) m_min (List.replicate tot ()) vmins := by
        match Obs.«KernelCheck::build_all_minors».obs evmins with
        | .run (ev6 := evmw) (hc85 := hc_min) .. =>
          exact build_all_minors_walk_rawLen ht hwf hS hH hbd hRagree hcl hlv es
            (fun cl hcl' => hsub_f cl (mem_of_eq hcf (by
              have hm1 : cl ∈ cs6 := mem_of_eq hc_min (by call_mem)
              call_mem)))
            (flatList_mono (ext_cd.trans evmots.heap_extends) hes0) hall evmw
      obtain ⟨dsMin, hlenMin0, hdsMin⟩ := repUnitList_to_rawKExprList hdsMin_u
      have hlenMin : dsMin.length = tot := by simpa using hlenMin0
      have hmin_lt : tot < 2 ^ 39 := by
        have hmem_len : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [vmins], m_min⟩ :
            Call F) ∈ rootCalls := hsub_f _ (mem_of_eq hcf (by call_mem))
        have := RomBound.bounded_length_lt hbd hmem_len List.mem_cons_self hdsMin
        rwa [hlenMin] at this
      obtain ⟨hvnmin, hm276⟩ := rawKExprList_length_spec evlen2 hdsMin
      subst hvnmin hm276
      rw [hlenMin] at *
      -- flat_member_at selfPos
      have ext_fma := ext_cd.trans (evmots.heap_extends.trans evmins.heap_extends)
      obtain ⟨hm298, ek', hek', hrepk⟩ :=
        flat_member_at_spec es selfPos hself_lt (by omega) evfma (flatList_mono ext_fma hes0)
      subst hm298
      have hek_eq : ek' = ek := Option.some.inj (hek'.symm.trans hek); subst ek'
      obtain ⟨_, _, _, da, htup, rda, hda, hsp_rep, -⟩ := hrepk
      injection htup with hl
      injection hl with h1 hl; injection hl with h2 hl; injection hl with h3 hl
      injection hl with h4 _; subst h1 h2 h3 h4
      -- indices
      obtain ⟨dsI0, hlenI0, hdsI0⟩ := collect_index_doms_rawList nI (by omega) evcid
      obtain ⟨dsI, hlenI, hdsI⟩ := list_lift_indices_rawList dsI0 hdsI0 evli
      have hlenI_le : dsI.length ≤ nI := by omega
      -- major premise HeapAppConst
      have ext_mc : Heap.Extends m_li m_c := by rw [hm_c]; exact Heap.Extends.snoc _ _
      have ext_maj0 : Heap.Extends _ m_c := evsci.heap_extends.trans (evinst2.heap_extends.trans
        (evpeel.heap_extends.trans (evrev.heap_extends.trans
          (evcid.heap_extends.trans (evli.heap_extends.trans ext_mc)))))
      have hac0 : HeapAppConst m_c (.ptr (.enum kexprEnum) m_li.length) ek.addr := by
        rw [← hda]
        exact .const (by rw [hm_c]; exact loadValue_store_snoc m_li _)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_maj0 rda)
      have hac1 : HeapAppConst m_ms vmaj1 ek.addr := by
        match Obs.«KernelCheck::build_major_args_for_self».obs evms with
        | .n1 (ev20 := evsp) .. =>
          obtain ⟨rawSp, -, hrawSp⟩ := repList_to_rawKExprList hsp_rep
          exact apply_spec_params_lifted_heapAppConst
            (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext_maj0 hrawSp) hac0 evsp
        | .other (ev55 := evdec) .. =>
          exact build_apply_bvars_decreasing_heapAppConst nP (by omega) nP 0 (by omega)
            hac0 (by simpa using evdec)
      have hac2 : HeapAppConst m_mi vmaj2 ek.addr :=
        build_major_indices_heapAppConst nI (by omega) nI 0 (by omega) hac1 (by simpa using evmi)
      -- conclusion BVar index arithmetic
      obtain rfl := binop_add_nat op_a1
      obtain rfl := binop_add_nat op_a2
      obtain rfl := binop_add_nat op_a3
      obtain rfl := binop_add_one_nat op_c1
      obtain rfl := binop_sub_one_nat (a := nP + es.length + tot + nI + 1) (by omega) op_c2
      obtain rfl := binop_add_nat op_c3
      have hle_c4 : nP + selfPos ≤ nP + es.length + tot + nI + 1 - 1 := by omega
      obtain rfl := binop_sub_nat hle_c4 op_c4
      have hidx_eq : nP + es.length + tot + nI + 1 - 1 - (nP + selfPos) =
          es.length + tot + nI - selfPos := by omega
      rw [hidx_eq] at hm_bv
      subst hm_bv
      -- conclusion HeapAppBVar
      have hab0 : HeapAppBVar (m_mi ++ [Value.construct kexprEnum "BVar"
            [.field ((es.length + tot + nI - selfPos : Nat) : F)]])
          (.ptr (.enum kexprEnum) m_mi.length)
          (((es.length + tot + nI - selfPos : Nat) : F)) :=
        .bvar (loadValue_store_snoc m_mi _)
      let m_bv0 := m_aic ++ [Value.construct kexprEnum "BVar" [.field 0]]
      let m_app := m_bv0 ++ [Value.construct kexprEnum "App" [vconcl0, .ptr (.enum kexprEnum) m_aic.length]]
      let m_majf := m_app ++ [Value.construct kexprEnum "Forall" [vmaj2, .ptr (.enum kexprEnum) m_bv0.length, xelim]]
      have hab1 : HeapAppBVar m_aic vconcl0
          (((es.length + tot + nI - selfPos : Nat) : F)) :=
        apply_indices_in_conclusion_heapAppBVar nI (by omega) nI 0 (by omega) hab0 (by simpa using evaic)
      have ext_concl : Heap.Extends m_aic m_app :=
        (Heap.Extends.snoc m_aic _).trans (Heap.Extends.snoc m_bv0 _)
      have hab_concl : HeapAppBVar m_app (.ptr (.enum kexprEnum) m_bv0.length)
          (((es.length + tot + nI - selfPos : Nat) : F)) :=
        .app (loadValue_store_snoc m_bv0 _) (hab1.mono ext_concl)
      -- major Forall cell
      have ext_maj2_f : Heap.Extends m_mi m_majf :=
        (Heap.Extends.snoc m_mi _).trans (evaic.heap_extends.trans
          (ext_concl.trans (Heap.Extends.snoc m_app _)))
      have ld_maj : loadValue m_majf (.ptr (.enum kexprEnum) m_app.length) =
          .ok (.construct kexprEnum "Forall" [vmaj2, .ptr (.enum kexprEnum) m_bv0.length, xelim]) :=
        loadValue_store_snoc m_app _
      -- chain 4 wrap_foralls
      have ext_dsI : Heap.Extends m_li m_majf :=
        ext_mc.trans (evms.heap_extends.trans
          (evmi.heap_extends.trans ext_maj2_f))
      obtain ⟨hf1, -⟩ := wrap_foralls_heapForalls dsI
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext_dsI hdsI) evw1
      have ext_dsMin := evsci.heap_extends.trans (evinst2.heap_extends.trans
        (evpeel.heap_extends.trans (evrev.heap_extends.trans (evcid.heap_extends.trans
          (evli.heap_extends.trans (ext_dsI.trans evw1.heap_extends))))))
      obtain ⟨hf2, -⟩ := wrap_foralls_heapForalls dsMin
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext_dsMin hdsMin) evw2
      have ext_dsMot := evmins.heap_extends.trans (ext_dsMin.trans evw2.heap_extends)
      obtain ⟨hf3, hdoms3⟩ := wrap_foralls_heapForalls dsMot
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext_dsMot hdsMot) evw3
      have ext_dsP := evmots.heap_extends.trans (ext_dsMot.trans evw3.heap_extends)
      obtain ⟨hf4, -⟩ := wrap_foralls_heapForalls dsP
        (repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext_dsP hdsP) evw4
      have ext_w1_end := evw2.heap_extends.trans (evw3.heap_extends.trans evw4.heap_extends)
      have ext_w2_end := evw3.heap_extends.trans evw4.heap_extends
      have ext_w3_end := evw4.heap_extends
      have ext_maj_end := evw1.heap_extends.trans ext_w1_end
      have ext_mot_end := ext_dsMot.trans (evw3.heap_extends.trans evw4.heap_extends)
      have hf_all_maj : HeapForalls h' (dsP.length + es.length + tot + dsI.length) r
          (.ptr (.enum kexprEnum) m_app.length) := by
        have h12 := hf4.trans ((hf3.mono ext_w3_end).trans
          ((hf2.mono ext_w2_end).trans (hf1.mono ext_w1_end)))
        simpa [hlenMot, hlenMin0, m_app, m_bv0, Nat.add_assoc] using h12
      have hf_all : HeapForalls h' (dsP.length + es.length + tot + dsI.length + 1) r
          (.ptr (.enum kexprEnum) m_bv0.length) :=
        hf_all_maj.trans (.succ (loadValue_mono ext_maj_end ld_maj) (.zero _))
      refine ⟨dsP.length, dsI.length, tot, .ptr (.enum kexprEnum) m_bv0.length,
        hlenP, hlenI_le, hmin_lt, htot, hf_all,
        hab_concl.mono ((Heap.Extends.snoc m_app _).trans ext_maj_end), ?_, ?_⟩
      · intro j ej hej
        have hjlt : j < dsMot.length := by
          rw [hlenMot]; exact (List.getElem?_eq_some_iff.mp hej).1
        obtain ⟨dj, hdj⟩ : ∃ dj, dsMot[j]? = some dj := ⟨dsMot[j], List.getElem?_eq_getElem hjlt⟩
        obtain ⟨q, bp, lp, hfq, ldq⟩ := hdoms3 j dj hdj
        exact ⟨q, dj, bp, lp, hf4.trans (hfq.mono ext_w3_end), loadValue_mono ext_w3_end ldq,
          (hmot_shape j dj ej hdj hej).toCarrier.mono ext_mot_end⟩
      · exact ⟨.ptr (.enum kexprEnum) m_app.length, vmaj2, .ptr (.enum kexprEnum) m_bv0.length, xelim,
          hf_all_maj, loadValue_mono ext_maj_end ld_maj,
          hac2.mono (ext_maj2_f.trans ext_maj_end)⟩
  match Obs.«KernelCheck::build_rec_type».obs ev with
  | .Induct (ev15 := e1) (ev74 := e2) (ev140 := ef) (hc237 := hc) .. =>
    exact handle_from (e1.heap_extends.trans e2.heap_extends)
      (fun cl hcl' => hsub cl (mem_of_eq hc (by call_mem))) ef
  | .other (ev15 := e1) (ev74 := e2) (ev247 := ef) (hc344 := hc) .. =>
    exact handle_from (e1.heap_extends.trans e2.heap_extends)
      (fun cl hcl' => hsub cl (mem_of_eq hc (by call_mem))) ef

/-! ## Section 3: Comparing `HeapForalls` and `HeapAppBVar` through `HeapEqOrWrap` -/

private theorem peel_n_foralls_heapForalls :
    ∀ (n : Nat), n < 9223372036854775808 →
      ∀ {xe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        ObsFn W "KernelCheck::peel_n_foralls" [xe, .field (n : F)] h r h' cs →
        h' = h ∧ HeapForalls h n xe r := by
  intro n
  induction n with
  | zero =>
    intro _ xe r h h' cs ev
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. => subst hr hh; exact ⟨rfl, .zero r⟩
    | .other (hne19 := hne) .. => exact (hne rfl).elim
  | succ m ih =>
    intro hm xe r h h' cs ev
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. =>
      have : ((m + 1 : Nat) : F).val = (0 : F).val := congrArg ZMod.val (Value.field.inj hv)
      rw [fval_natCast (by omega)] at this; simp at this
    | .other (ld34 := ld) (op87 := op) (ev64 := evrec) .. =>
      obtain rfl := binop_sub_one_nat (a := m + 1) (by omega) op
      obtain ⟨hh', hf⟩ := ih (by omega) evrec
      exact ⟨hh', .succ ld hf⟩

private theorem heapForalls_eq_count {rootCalls : List (Call F)} :
    ∀ (n₁ : Nat) {n₂ : Nat} {xg q₁ xd yd : SourceValue F} {h : Heap F},
      HeapForalls h n₁ xg q₁ →
      (∃ v₁, loadValue h q₁ = .ok v₁ ∧ ∀ d b l, v₁ ≠ .construct kexprEnum "Forall" [d, b, l]) →
      HeapEqOrWrap rootCalls h xg xd →
      HeapForalls h n₂ xd yd →
      (∃ v₂, loadValue h yd = .ok v₂ ∧ ∀ d b l, v₂ ≠ .construct kexprEnum "Forall" [d, b, l]) →
      n₁ = n₂ ∧ ∃ h_end, Heap.Extends h h_end ∧ HeapEqOrWrap rootCalls h_end q₁ yd := by
  intro n₁
  induction n₁ with
  | zero =>
    intro n₂ xg q₁ xd yd h hf1 hnf1 hrel hf2 hnf2
    cases hf1
    cases hf2 with
    | zero => exact ⟨rfl, h, Heap.Extends.refl h, hrel⟩
    | succ ldf _ =>
      obtain ⟨v₁, ldv₁, hnev₁⟩ := hnf1
      obtain ⟨v₂, ldv₂, hnev₂⟩ := heapEqOrWrap_not_forall hrel ldv₁ hnev₁
      rw [ldf] at ldv₂; injection ldv₂ with heq
      exact (hnev₂ _ _ _ heq.symm).elim
  | succ m₁ ih =>
    intro n₂ xg q₁ xd yd h hf1 hnf1 hrel hf2 hnf2
    cases hf1 with
    | @succ _ _ dg bg lg _ ld_g hf1_rest =>
      obtain ⟨dd, bd, ld, _, h_b, _, ext_b, ld_d, -, hrel_b⟩ :=
        heapEqOrWrap_forall_step hrel ld_g
      cases hf2 with
      | zero =>
        obtain ⟨v₂, ldv₂, hnev₂⟩ := hnf2
        rw [ldv₂] at ld_d
        injection ld_d with heq
        exact (hnev₂ _ _ _ heq).elim
      | @succ m₂ _ dd' bd' ld' _ ldf hf2_rest =>
        have hld_eq := ldf.symm.trans ld_d
        simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq] at hld_eq
        obtain ⟨-, -, -, hbd_eq, -⟩ := hld_eq
        subst hbd_eq
        obtain ⟨v₁, ldv₁, hnev₁⟩ := hnf1
        obtain ⟨v₂, ldv₂, hnev₂⟩ := hnf2
        obtain ⟨hm_eq, h_end, ext_end, hrel_end⟩ := ih (hf1_rest.mono ext_b)
          ⟨v₁, loadValue_mono ext_b ldv₁, hnev₁⟩ hrel_b (hf2_rest.mono ext_b)
          ⟨v₂, loadValue_mono ext_b ldv₂, hnev₂⟩
        exact ⟨congrArg Nat.succ hm_eq, h_end, ext_b.trans ext_end, hrel_end⟩

private theorem collect_spine_head_valid :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ xe xhd xargs, args = [xe] → r = .tuple [xhd, xargs] →
        ∃ v, loadValue h xhd = .ok v ∧ ∀ f a, v ≠ .construct kexprEnum "App" [f, a] :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelTypes::collect_spine" →
      ∀ xe xhd xargs, args = [xe] → r = .tuple [xhd, xargs] →
        ∃ v, loadValue h xhd = .ok v ∧ ∀ f a, v ≠ .construct kexprEnum "App" [f, a])
    (fun fname args h r h' cs ev _ hnm xe xhd xargs hargs hr => by
      subst hnm hargs hr
      obtain ⟨_, hch, -, -⟩ := Core.collect_spine_chain_tup ev
      obtain ⟨v, ld, hne⟩ := hch.head_load
      exact ⟨v, ld, fun f a he => hne [f, a] rfl he⟩)

private theorem collect_spine_heapAppBVar :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ xe xhd xargs idx, args = [xe] → r = .tuple [xhd, xargs] →
        loadValue h' xhd = .ok (.construct kexprEnum "BVar" [.field idx]) →
        HeapAppBVar h xe idx :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelTypes::collect_spine" →
      ∀ xe xhd xargs idx, args = [xe] → r = .tuple [xhd, xargs] →
        loadValue h' xhd = .ok (.construct kexprEnum "BVar" [.field idx]) →
        HeapAppBVar h xe idx)
    (fun fname args h r h' cs ev _ hnm xe xhd xargs idx hargs hr ldb => by
      subst hnm hargs hr
      obtain ⟨ps, hch, -, -⟩ := Core.collect_spine_chain_tup ev
      have haux :
          ∀ {xe xhd' : SourceValue F} {ps : List (SourceValue F)},
            Core.SpineChain h xe xhd' ps →
            loadValue h' xhd' = .ok (.construct kexprEnum "BVar" [.field idx]) →
            HeapAppBVar h xe idx := by
        intro xe xhd' ps sc
        induction sc with
        | head ld _ =>
          intro ldb'
          have hld_m := loadValue_mono ev.heap_extends ld
          rw [hld_m] at ldb'; injection ldb' with hv; subst hv
          exact .bvar ld
        | app ld _ ih => intro ldb'; exact .app ld (ih ldb')
      exact haux hch ldb)

private theorem evalBinOp_sub_eq_zero_field {a b : F}
    (op : evalBinOp .sub (.field a : SourceValue F) (.field b) = .ok (.field 0)) : a = b := by
  simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
    Except.ok.injEq, Value.field.injEq] at op
  exact sub_eq_zero.mp op

private theorem heapAppBVar_eq_of_heapEqOrWrap {rootCalls : List (Call F)} {idx₁ idx₂ : F} :
    ∀ {h : Heap F} {xg : SourceValue F}, HeapAppBVar h xg idx₁ →
      ∀ {h1 : Heap F} {xd : SourceValue F},
        Heap.Extends h h1 →
        HeapAppBVar h1 xd idx₂ →
        HeapEqOrWrap rootCalls h1 xg xd →
        idx₁ = idx₂ := by
  intro h xg hab1
  induction hab1 with
  | @bvar p idx₁ ld_g =>
    intro h1 xd ext hab2 hrel
    have ld_g1 := loadValue_mono ext ld_g
    have from_kseq : ∀ {h2 cs2},
        ObsFn W "KernelCheck::kexpr_struct_eq" [p, xd] h1 (.field 1) h2 cs2 →
        loadValue h1 xd = .ok (.construct kexprEnum "BVar" [.field idx₁]) := by
      intro h2 cs2 evk
      match Obs.«KernelCheck::kexpr_struct_eq».obs evk with
      | .BVar_BVar_n0 (ld12 := l1) (ld36 := l2) (op65 := op) .. =>
        rw [ld_g1] at l1; injection l1 with hv; injection hv with _ _ hl; injection hl with h1 _
        subst h1
        cases hab2 with
        | bvar ldb =>
          rw [ldb] at l2; injection l2 with hv2; injection hv2 with _ _ hl2; injection hl2 with h2 _
          subst h2
          have hidx_eq := evalBinOp_sub_eq_zero_field op
          rw [hidx_eq]
          exact ldb
        | app lda _ =>
          rw [lda] at l2; simp [kexprEnum] at l2
      | .BVar_BVar_other (he79 := he) .. | .BVar_other (he86 := he) .. =>
        exact absurd (Value.field.inj he) (by decide)
      | .Srt_Srt (ld12 := l1) .. | .Srt_other (ld12 := l1) ..
      | .Const_Const_n1 (ld12 := l1) .. | .Const_Const_other (ld12 := l1) ..
      | .Const_other (ld12 := l1) ..
      | .App_App_n1 (ld12 := l1) .. | .App_App_other (ld12 := l1) .. | .App_other (ld12 := l1) ..
      | .Lam_Lam (ld12 := l1) .. | .Lam_other (ld12 := l1) ..
      | .Forall_Forall (ld12 := l1) .. | .Forall_other (ld12 := l1) ..
      | .Let_Let_n1_n1 (ld12 := l1) .. | .Let_Let_n1_other (ld12 := l1) ..
      | .Let_Let_other (ld12 := l1) .. | .Let_other (ld12 := l1) ..
      | .Lit_Lit (ld12 := l1) .. | .Lit_other (ld12 := l1) ..
      | .Proj_Proj_n1_n0 (ld12 := l1) .. | .Proj_Proj_n1_other (ld12 := l1) ..
      | .Proj_Proj_other (ld12 := l1) .. | .Proj_other (ld12 := l1) .. =>
        rw [ld_g1] at l1; simp [kexprEnum] at l1
    have ld_d : loadValue h1 xd = .ok (.construct kexprEnum "BVar" [.field idx₁]) := by
      rcases hrel with ⟨_, _, _, evk⟩ | ⟨_, _, _, _, evw⟩
      · exact from_kseq evk
      · match Obs.«KernelCheck::wrap_rel».obs evw with
        | .other_other_other (ev765 := evk) .. => exact from_kseq evk
        | .other_Let (he224 := he) .. => exact absurd (Value.field.inj he) (by decide)
        | .Let_Let_n1_n1 (ld12 := l1) .. | .Let_Let_n1_other (ld12 := l1) ..
        | .Let_Let_other (ld12 := l1) .. | .Let_other (ld12 := l1) ..
        | .other_other_App_App_n1 (ld242 := l1) .. | .other_other_App_App_other (ld242 := l1) ..
        | .other_other_App_other (ld242 := l1) .. | .other_other_Lam_Lam (ld242 := l1) ..
        | .other_other_Lam_other (ld242 := l1) .. | .other_other_Forall_Forall (ld242 := l1) ..
        | .other_other_Forall_other (ld242 := l1) .. | .other_other_Proj_Proj_n1 (ld242 := l1) ..
        | .other_other_Proj_Proj_other (ld242 := l1) .. | .other_other_Proj_other (ld242 := l1) .. =>
          rw [ld_g1] at l1; simp [kexprEnum] at l1
    cases hab2 with
    | bvar ldb =>
      rw [ld_d] at ldb; injection ldb with hv; injection hv with _ _ hl; injection hl with hi _
      exact Value.field.inj hi
    | app lda _ =>
      rw [ld_d] at lda; simp [kexprEnum] at lda
  | @app p fp ap idx₁ ld_g hfp ih =>
    intro h1 xd ext hab2 hrel
    have ld_g1 := loadValue_mono ext ld_g
    have hstep : ∃ fd ad, loadValue h1 xd = .ok (.construct kexprEnum "App" [fd, ad]) ∧
        HeapEqOrWrap rootCalls h1 fp fd := by
      rcases hrel with ⟨_, _, hsubk, evk⟩ | ⟨_, _, _, hsubw, evw⟩
      · match Obs.«KernelCheck::kexpr_struct_eq».obs evk with
        | .App_App_n1 (x_fa := xfa) (x_fb := xfb) (ld12 := l1) (ld301 := l2)
            (ev333 := evf) (hc376 := hc) .. =>
          rw [ld_g1] at l1; injection l1 with hv; injection hv with _ _ hl; injection hl with h1 _; subst h1
          exact ⟨xfb, _, l2, Or.inl ⟨_, _, fun cl hcl => hsubk cl (mem_of_eq hc (by call_mem)), evf⟩⟩
        | .App_App_other (he381 := he) .. | .App_other (he388 := he) .. =>
          exact absurd (Value.field.inj he) (by decide)
        | .BVar_BVar_n0 (ld12 := l1) .. | .BVar_BVar_other (ld12 := l1) .. | .BVar_other (ld12 := l1) ..
        | .Srt_Srt (ld12 := l1) .. | .Srt_other (ld12 := l1) ..
        | .Const_Const_n1 (ld12 := l1) .. | .Const_Const_other (ld12 := l1) .. | .Const_other (ld12 := l1) ..
        | .Lam_Lam (ld12 := l1) .. | .Lam_other (ld12 := l1) ..
        | .Forall_Forall (ld12 := l1) .. | .Forall_other (ld12 := l1) ..
        | .Let_Let_n1_n1 (ld12 := l1) .. | .Let_Let_n1_other (ld12 := l1) ..
        | .Let_Let_other (ld12 := l1) .. | .Let_other (ld12 := l1) ..
        | .Lit_Lit (ld12 := l1) .. | .Lit_other (ld12 := l1) ..
        | .Proj_Proj_n1_n0 (ld12 := l1) .. | .Proj_Proj_n1_other (ld12 := l1) ..
        | .Proj_Proj_other (ld12 := l1) .. | .Proj_other (ld12 := l1) .. =>
          rw [ld_g1] at l1; simp [kexprEnum] at l1
      · match Obs.«KernelCheck::wrap_rel».obs evw with
        | .other_other_App_App_n1 (x_f := xf) (x_f2 := xf2) (ld242 := l1) (ld271 := l2)
            (ev303 := evf) (hc346 := hc) .. =>
          rw [ld_g1] at l1; injection l1 with hv; injection hv with _ _ hl; injection hl with h1 _; subst h1
          exact ⟨xf2, _, l2, Or.inr ⟨_, _, _, fun cl hcl => hsubw cl (mem_of_eq hc (by call_mem)), evf⟩⟩
        | .other_other_App_App_other (he351 := he) ..
        | .other_other_App_other (he358 := he) ..
        | .other_Let (he224 := he) .. =>
          exact absurd (Value.field.inj he) (by decide)
        | .Let_Let_n1_n1 (ld12 := l1) .. | .Let_Let_n1_other (ld12 := l1) ..
        | .Let_Let_other (ld12 := l1) .. | .Let_other (ld12 := l1) ..
        | .other_other_Lam_Lam (ld242 := l1) .. | .other_other_Lam_other (ld242 := l1) ..
        | .other_other_Forall_Forall (ld242 := l1) .. | .other_other_Forall_other (ld242 := l1) ..
        | .other_other_Proj_Proj_n1 (ld242 := l1) .. | .other_other_Proj_Proj_other (ld242 := l1) ..
        | .other_other_Proj_other (ld242 := l1) .. =>
          rw [ld_g1] at l1; simp [kexprEnum] at l1
        | .other_other_other (ld242 := l1) (hne361 := hne) .. =>
          have hv := Except.ok.inj (ld_g1.symm.trans l1)
          exact (hne [_, _] rfl hv.symm).elim
    obtain ⟨fd, ad, ld_d, hrel_f⟩ := hstep
    cases hab2 with
    | bvar ldb => rw [ld_d] at ldb; simp [kexprEnum] at ldb
    | app lda hfd =>
      rw [ld_d] at lda; injection lda with hv; injection hv with _ _ hl; injection hl with h1 _; subst h1
      exact ih ext hfd hrel_f

/-! ## Section 4: `check_carriers`, `rec_major_pins`, `check_rec_motive`, `compare_rules`, `recTypeAt` -/

private theorem last_binder_dom_rawConvExpr {c : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelModeled::last_binder_dom" →
      ∀ xe, args = [xe] →
        h' = h ∧
        ∀ {bound : Nat} {e : Ixon.Expr},
          Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e xe →
          ∃ b' ed n_dom, FamilyOf.lastDom c n_dom e = some ed ∧
            Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' ed r :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelModeled::last_binder_dom" →
      ∀ xe, args = [xe] →
        h' = h ∧
        ∀ {bound : Nat} {e : Ixon.Expr},
          Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e xe →
          ∃ b' ed n_dom, FamilyOf.lastDom c n_dom e = some ed ∧
            Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' ed r)
    (fun fname args h r h' cs ev ih hnm xe hargs => by
      subst hnm hargs
      match Obs.«KernelModeled::last_binder_dom».obs ev with
      | .other (x_d := xd) (x_b := xb) (w20 := wl) (v36 := v36)
          (ld12 := ld1) (ld47 := ld2) (hne88 := hne) (he93 := hr) (he94 := hh) .. =>
        subst hr hh
        refine ⟨rfl, fun {bound e} raw => ?_⟩
        obtain ⟨b', ed, eb, hnd, raw_d, raw_b⟩ := rawConvExpr_forall_inv_wrap raw ld1
        have hnf := rawConvExpr_not_forall_of_nonForall raw_b ld2 (fun d b l he => hne [d, b, l] rfl he)
        refine ⟨b', ed, 1, ?_, raw_d⟩
        simp only [FamilyOf.lastDom, hnd]
      | .Forall (x_d := xd) (x_b := xb) (ld12 := ld1) (ld47 := ld2) (ev78 := evrec) (hc87 := hc) .. =>
        obtain ⟨hh', hih⟩ := ih _ _ _ _ _ _ (by rw [hc]; simp) evrec rfl xb rfl
        refine ⟨hh', fun {bound e} raw => ?_⟩
        obtain ⟨b', ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv_wrap raw ld1
        obtain ⟨b'', ed', eb', hnd_b, -, -⟩ := rawConvExpr_forall_inv_wrap raw_b ld2
        obtain ⟨b''', ed_out, n_dom, hlast, raw_out⟩ := hih raw_b
        refine ⟨b''', ed_out, n_dom + 1, ?_, raw_out⟩
        simp only [FamilyOf.lastDom, hnd, hnd_b, hlast])

private theorem collect_spine_rawConvExpr {c : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelTypes::collect_spine" →
      ∀ p xh xargs, args = [p] → r = .tuple [xh, xargs] →
        ∀ {h_fin : Heap F} {bound : Nat} {e : Ixon.Expr} {xc xus : SourceValue F},
          Heap.Extends h' h_fin →
          Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e p →
          loadValue h_fin xh = .ok (.construct kexprEnum "Const" [xc, xus]) →
          ∃ da : Bytes.Address, Bytes.RepAddressRef addrTy h_fin da xc ∧
            (ixAddr da ∉ recurAddrs → ∃ fuel, FamilyOf.refHeadAt c fuel e = some (ixAddr da)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelTypes::collect_spine" →
      ∀ p xh xargs, args = [p] → r = .tuple [xh, xargs] →
        ∀ {h_fin : Heap F} {bound : Nat} {e : Ixon.Expr} {xc xus : SourceValue F},
          Heap.Extends h' h_fin →
          Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e p →
          loadValue h_fin xh = .ok (.construct kexprEnum "Const" [xc, xus]) →
          ∃ da : Bytes.Address, Bytes.RepAddressRef addrTy h_fin da xc ∧
            (ixAddr da ∉ recurAddrs → ∃ fuel, FamilyOf.refHeadAt c fuel e = some (ixAddr da)))
    (fun fname args h r h' cs ev _ hnm p xh xargs hargs hr {h_fin bound e xc xus} ext_fin raw ldc => by
      subst hnm hargs hr
      obtain ⟨ps, hch, -, -⟩ := Core.collect_spine_chain_tup ev
      have ext_h := ev.heap_extends.trans ext_fin
      have haux :
          ∀ {p xh' : SourceValue F} {ps : List (SourceValue F)},
            Core.SpineChain h p xh' ps →
            loadValue h_fin xh' = .ok (.construct kexprEnum "Const" [xc, xus]) →
            ∀ {bound : Nat} {e : Ixon.Expr},
              Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e p →
              ∃ da : Bytes.Address, Bytes.RepAddressRef addrTy h_fin da xc ∧
                (ixAddr da ∉ recurAddrs → ∃ fuel, FamilyOf.refHeadAt c fuel e = some (ixAddr da)) := by
        intro p xh' ps sc
        induction sc with
        | head _ _ =>
          intro ldc' bound e raw
          rcases rawConvExpr_const_inv_any_wrap (raw.mono ext_h (fun _ hp => hp)) ldc' with
            ⟨rIdx, uIdxs, a', da, hnd, href, hda, rda⟩ |
            ⟨recIdx, uIdxs, a', da, hnd, hrec, hda, rda⟩
          · subst hda
            exact ⟨da, rda, fun _ => ⟨0, by simp [FamilyOf.refHeadAt, FamilyOf.spineHead, hnd, href]⟩⟩
          · subst hda
            exact ⟨da, rda, fun hnr => absurd (List.mem_of_getElem? hrec) hnr⟩
        | app ld12 _ ih =>
          intro ldc' bound e raw
          obtain ⟨b', ef, ea, hnd, raw_f, -⟩ := rawConvExpr_app_inv_wrap raw ld12
          obtain ⟨da, rda, href⟩ := ih ldc' raw_f
          refine ⟨da, rda, fun hnr => ?_⟩
          obtain ⟨fuel, hf⟩ := href hnr
          exact ⟨fuel + 1, by simp only [FamilyOf.refHeadAt, FamilyOf.spineHead, hnd]; exact hf⟩
      exact haux hch ldc raw)

private theorem rawConvExpr_peel_of_heapForalls {c : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)} {h : Heap F} :
    ∀ (n : Nat) {bound : Nat} {e : Ixon.Expr} {kp q : SourceValue F},
      HeapForalls h n kp q →
      Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp →
      ∃ b' e', FamilyOf.peel c n e = some e' ∧
        Ingress.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h b' e' q := by
  intro n
  induction n with
  | zero =>
    intro bound e kp q hf raw
    cases hf; exact ⟨bound, e, rfl, raw⟩
  | succ m ih =>
    intro bound e kp q hf raw
    cases hf with
    | succ ld hf_rest =>
      obtain ⟨b', ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv_wrap raw ld
      obtain ⟨b'', e', hpeel, raw'⟩ := ih hf_rest raw_b
      exact ⟨b'', e', by simp [FamilyOf.peel, hnd, hpeel], raw'⟩

/-- **`KernelModeled::check_carriers`** witnesses `FamilyOf.motiveCarrierAt crb rc 0 fuel = some (ixAddr t0)`
for the first type address `t0` in `x_type_addrs`. -/
private theorem check_carriers_motive0 {crb : Ixon.Constant} {rc : Ixon.Recursor}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {t0 : Bytes.Address} {trest : List Bytes.Address} {xty xta r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnp : rc.params.toNat < 9223372036854775808)
    (hnot_rec : ixAddr t0 ∉ recurAddrs)
    (hta : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (t0 :: trest) xta)
    (raw : Ingress.RawConvExpr crb.refs.toList recurAddrs crb.univs.toList crb.sharing.toList
      blobs h 4294967295 rc.typ xty)
    (ev : ObsFn W "KernelModeled::check_carriers"
      [xty, .field (rc.params.toNat : F), xta] h r h' cs) :
    ∃ fuel, FamilyOf.motiveCarrierAt crb rc 0 fuel = some (ixAddr t0) := by
  match Obs.«KernelModeled::check_carriers».obs ev with
  | .run (v7 := v7) (m10 := m10) (ev20 := evp) (ev6 := evgo) .. =>
    obtain ⟨hm10, hfp⟩ := peel_n_foralls_heapForalls rc.params.toNat hnp evp
    subst hm10
    match Obs.«KernelModeled::check_carriers_go».obs evgo with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hta ld
    | .Cons (x_t := xt) (x_mdom := xmdom) (v91 := v91) (m93 := m93) (m78 := m78)
        (x_head := xhd) (x_c := xc) (ld12 := ldt) (ld53 := ldall) (ev103 := evlbd)
        (ev90 := evsp) (ld137 := ldc) (ev180 := eveq) (heq203 := heq1) .. =>
      obtain ⟨_, _, heq_t, rt0, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hta ldt
      injection heq_t with h1 _; subst h1
      obtain ⟨b1, e1, hpeel, raw1⟩ := rawConvExpr_peel_of_heapForalls rc.params.toNat hfp raw
      obtain ⟨b2, ed, eb, hnd, raw_d, -⟩ := rawConvExpr_forall_inv_wrap raw1 ldall
      obtain ⟨hm93, hlbd⟩ := last_binder_dom_rawConvExpr _ _ _ _ _ _ evlbd rfl xmdom rfl
      subst m93
      obtain ⟨b3, ed_out, n_dom, hlast, raw_dp⟩ := hlbd raw_d
      obtain ⟨da, rda, href_fn⟩ := collect_spine_rawConvExpr _ _ _ _ _ _ evsp rfl v91 xhd _
        rfl rfl (Heap.Extends.refl m78) raw_dp ldc
      obtain ⟨heq_v, -⟩ := Lib.address_eq_spec (by rw [heq1] at eveq; exact eveq) rda
        (Bytes.repAddressRef_heapMono₂ addrTy evsp.heap_extends rt0)
      have hda_eq : da = t0 := by
        by_contra hne; rw [ite_eq_right hne] at heq_v
        exact absurd (Value.field.inj heq_v) one_ne_zero
      subst hda_eq
      obtain ⟨n_ref, href⟩ := href_fn hnot_rec
      refine ⟨max n_dom n_ref, ?_⟩
      unfold FamilyOf.motiveCarrierAt
      simp only [Nat.add_zero, Bind.bind, Option.bind, hpeel, FamilyOf.domOf, hnd]
      rw [FamilyOf.lastDom_mono crb ed_out n_dom (max n_dom n_ref) ed hlast (Nat.le_max_left _ _)]
      exact FamilyOf.refHeadAt_mono href (Nat.le_max_right _ _)

/-- **`KernelModeled::rec_major_pins`** links a recursor's index count `rni` to its major
inductive's index count `pni` and certifies `args.length = pnp + pni` (hence `pnp ≤ args.length`). -/
private theorem rec_major_pins_ni_eq {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    {ty : KExpr} {nP nMot nMin rni : Nat} {xty xr_pa r_mp : SourceValue F}
    {h₁ h₂ h₁' h₂' : Heap F} {cs₁ cs₂ : List (Call F)} {pa : Bytes.Address}
    (hsum : nP + nMot + nMin + rni < 9223372036854775808)
    (hsub₁ : ∀ cl ∈ cs₁, cl ∈ rootCalls)
    (hTy : TmOExact (Core.keyOf t) h₁ ty xty)
    (hTyIn : AddrIn (Held R) (Core.keyOf t) ty)
    (ext12 : Heap.Extends h₁ h₂)
    (ev_mp : ObsFn W "KernelModeled::rec_major_pins"
      [xty, .field ((nP + nMot + nMin : Nat) : F), .field (rni : F)] h₁ r_mp h₁' cs₁)
    (ev_pa : ObsFn W "KernelCheck::rec_to_parent_addr"
      [xty, .field (nP : F), .field (nMot : F), .field (nMin : F), .field (rni : F)]
      h₂ xr_pa h₂' cs₂)
    (rpa : Bytes.RepAddressRef addrTy h₂' pa xr_pa) :
    ∃ (pInfo : IndData) (d : KExpr) (us : List KLevel),
      indDataAt t E₀ (ixAddr pa) = some (some pInfo) ∧
      pInfo.ni = rni ∧
      binderDomAfter (nP + nMot + nMin + rni) ty = some d ∧
      d.getAppFn = .const (Core.keyOf t (ixAddr pa)) us ∧
      pInfo.np ≤ d.getAppArgs.length ∧
      Held R (ixAddr pa) := by
  obtain ⟨d, pa', us, hd, hfn, rpa', -⟩ :=
    rec_to_parent_addr_spec (κ := Core.keyOf t) hsum (hTy.mono ext12) ev_pa
  have hpa_eq : pa' = pa := Bytes.repAddressRef_inj U32.Goldilocks.compatible rpa' rpa
  subst pa'
  match Obs.«KernelModeled::rec_major_pins».obs ev_mp with
  | .run (v1 := v1) (m2 := m2) (v16 := v16) (x_dom := xdom) (m77 := m77) (x_h := xh)
      (x_args := xargs) (x_iaddr := xiaddr) (m141 := m141) (p149 := p149) (cs155 := cs_ci)
      (x_inp := xinp) (x_ini := xini) (v257 := vlen) (v258 := vsum) (m260 := m260)
      (op37 := op37) (ev14 := evp) (ld51 := ld51) (ev89 := evsp) (ld122 := ld122)
      (ev157 := evci) (ld151 := ldci) (heq245 := heq_ni) (ev270 := evlen)
      (op292 := op292) (heq295 := heq_len) (hc424 := hc) .. =>
    obtain rfl := binop_add_nat op37
    obtain ⟨rfl, E', hpeel, hE'⟩ :=
      peel_n_foralls_tmOExact (nP + nMot + nMin + rni) hsum evp hTy
    obtain ⟨D, B, ℓ, rfl, hD, -, -⟩ := TmOExact.forallE_of_load hE' ld51
    have hD_eq : D = d := by
      have h1 : binderDomAfter (nP + nMot + nMin + rni) ty = some D := by
        simp [binderDomAfter, hpeel]
      exact Option.some.inj (h1.symm.trans hd)
    subst D
    obtain ⟨xh', xargs', hdE, argsE, htup, hhd, hargs, hmk, -⟩ := collect_spine_tmOExact evsp hD
    injection htup with hl; injection hl with h1 hl; injection hl with h2 _; subst h1 h2
    obtain ⟨ia, ius, rfl, ria, -⟩ := TmOExact.const_of_load hhd ld122
    have hfn' : d.getAppFn = .const (Core.keyOf t (ixAddr ia)) ius := by
      rw [← hmk, getAppFn_mkAppN_const]
    have hkey_eq : Core.keyOf t (ixAddr ia) = Core.keyOf t (ixAddr pa) := by
      rw [hfn] at hfn'; injection hfn' with hk _; exact hk.symm
    have hia_eq : ixAddr ia = ixAddr pa := Core.keyOf_inj hwf hkey_eq
    have hSia : Held R (ixAddr ia) := by
      have hDIn := addrIn_binderDomAfter hTyIn hd
      have hfnIn := addrIn_getAppFn hDIn
      rw [hfn'] at hfnIn
      exact hfnIn (ixAddr ia) rfl
    obtain ⟨hInd, -⟩ := indAnswers_ofStore ht hwf hS hH hbd hRagree hcl hlv
      (fun cl hcl' => hsub₁ cl (mem_of_eq hc (by call_mem))) hSia ria evci ldci
    obtain ⟨info, _, hia_at, -, hnp56, hni56, -, -, -, -, -, -, hnpEq, hniEq, -⟩ :=
      hInd _ _ _ _ _ _ _ _ rfl
    rw [hia_eq] at hia_at hSia
    subst hnpEq hniEq
    have hni_eq : info.ni = rni := by
      have h1 : ((info.ni : Nat) : F).val = ((rni : Nat) : F).val :=
        congrArg ZMod.val (Value.field.inj heq_ni)
      rw [fval_natCast (by omega), fval_natCast (by omega)] at h1
      exact h1
    obtain ⟨hvlen, -⟩ := kexpr_length_spec evlen (tmOExactList_mono evci.heap_extends hargs)
    have hargs_lt : argsE.length < 2 ^ 39 := by
      have hmem_len : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xargs], m141⟩ :
          Call F) ∈ rootCalls := hsub₁ _ (mem_of_eq hc (by call_mem))
      exact RomBound.bounded_length_lt hbd hmem_len List.mem_cons_self
        (tmOExactList_mono evci.heap_extends hargs)
    obtain rfl := binop_add_nat op292
    rw [hvlen] at heq_len
    have hlen_eq : argsE.length = info.np + info.ni := by
      have h1 : ((argsE.length : Nat) : F).val = (((info.np + info.ni : Nat) : F)).val :=
        congrArg ZMod.val (Value.field.inj heq_len)
      rw [fval_natCast (by omega), fval_natCast (by omega)] at h1
      exact h1
    have hargs_eq : argsE = d.getAppArgs := by
      rw [← hmk, getAppArgs_mkAppN_const]
    exact ⟨info, d, us, hia_at, hni_eq, hd, hfn, by rw [← hargs_eq]; omega, hSia⟩

/-- **`KernelModeled::check_rec_motive`** produces a `HeapForalls` chain of length
`nP + nMot + nMin + rni + 1` ending in `HeapAppBVar _ _ (nMot + nMin + rni - k)`. -/
private theorem check_rec_motive_spec {nP nMot nMin rni k : Nat} {xty r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsum : nP + nMot + nMin + rni + 1 < 9223372036854775808) (hk : k ≤ nMot + nMin + rni)
    (ev : ObsFn W "KernelModeled::check_rec_motive"
      [xty, .field ((nP + nMot + nMin + rni + 1 : Nat) : F), .field ((nP + k : Nat) : F)]
      h r h' cs) :
    ∃ yd : SourceValue F,
      HeapForalls h (nP + nMot + nMin + rni + 1) xty yd ∧
      HeapAppBVar h yd (((nMot + nMin + rni - k : Nat) : F)) := by
  match Obs.«KernelModeled::check_rec_motive».obs ev with
  | .run (v1 := v1) (m2 := m2) (x_head := xh) (x_j := xj) (ev14 := evp) (ev44 := evsp)
      (ld78 := ldb) (op132 := op1) (op124 := op2) (heq135 := heqj) .. =>
    obtain ⟨hm2, hf⟩ := peel_n_foralls_heapForalls (nP + nMot + nMin + rni + 1) hsum evp
    subst hm2
    obtain rfl := binop_sub_one_nat (a := nP + nMot + nMin + rni + 1) (by omega) op1
    obtain rfl := binop_sub_nat (a := nP + nMot + nMin + rni + 1 - 1) (b := nP + k) (by omega) op2
    have hidx : nP + nMot + nMin + rni + 1 - 1 - (nP + k) = nMot + nMin + rni - k := by omega
    rw [hidx] at heqj; subst heqj
    exact ⟨v1, hf, collect_spine_heapAppBVar _ _ _ _ _ _ evsp rfl v1 xh _
      (((nMot + nMin + rni - k : Nat) : F)) rfl rfl ldb⟩

/-- **`KernelCheck::compare_rules` implies `pos + rus.length ≤ numCtors`** directly from
`x_cidx = x_pos`, `UInt32::less_than_fields [x_cidx, x_num_ctors] = 1`, and `pos + cbs.length = numCtors`. -/
private theorem compare_rules_len_le {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {S : _root_.Address → Prop} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {nl : Nat} {base : F}
    {xnp xnmot xnmin xblk xidx xelim xty xmoff : SourceValue F} {numCtors : Nat}
    (hnc : numCtors < 72057594037927936) :
    ∀ (rus : List Ixon.RecursorRule) (cbs : List KExpr) (pos : Nat)
      {xst xcan r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      pos + cbs.length = numCtors →
      RecRulesRep t E₀ S rb crb rs nl base h pos rus xst →
      RepList kexprListEnum (TmOExact (Core.keyOf t)) h cbs xcan →
      ObsFn W "KernelCheck::compare_rules"
        [xst, xcan, xnp, xnmot, xnmin, xblk, xidx, .field (numCtors : F), .field (pos : F),
          xelim, xty, xmoff] h r h' cs →
      pos + rus.length ≤ numCtors := by
  intro rus
  induction rus with
  | nil =>
    intro cbs pos _ _ _ _ _ _ hsum _ _ _; simp; omega
  | cons ru rest ih =>
    intro cbs pos xst xcan r h h' cs hsum hrrep hcbs ev
    have step_lt : ∀ {xcidx v112 m115 cs123},
        xcidx = .field (pos : F) →
        ObsFn W "UInt32::less_than_fields" [xcidx, .field (numCtors : F)] h v112 m115 cs123 →
        v112 = .field 1 → pos < numCtors := by
      intro xcidx v112 m115 cs123 hxc evlt hv1
      subst hxc hv1
      obtain ⟨-, -, hiff, -, -⟩ := Lib.less_than_fields_field evlt
      have h1 := hiff.mp rfl
      rw [fval_natCast (by omega), fval_natCast (by omega)] at h1
      exact h1
    match Obs.«KernelCheck::compare_rules».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases hrrep with
      | cons cell _ _ => exact absurd (Core.load_cell cell ld12).1 (by decide)
    | .Cons_Nil (heq100 := heq100) (ev125 := evlt) (heq148 := hv1) (ev165 := evci)
        (ld302 := ld302) .. =>
      have hlt := step_lt heq100 evlt hv1
      have hnil := IxVM.Refinement.Core.RepList.nil_of_load
        (tmOExactList_mono (evlt.heap_extends.trans evci.heap_extends) hcbs) ld302
      subst hnil; simp at hsum; omega
    | .Cons_Cons (ld12 := ld12) (heq100 := heq100) (ev125 := evlt) (heq148 := hv1)
        (ev165 := evci) (ld302 := ld302) (ev390 := ev390) (ev439 := ev439) (ev507 := ev507)
        (ev553 := ev553) (ev610 := ev610) (op721 := op1) (ev639 := evrec) .. =>
      have hlt := step_lt heq100 evlt hv1
      cases hrrep with
      | cons cell _ htail =>
        obtain ⟨_, hxs⟩ := Core.load_cell cell ld12
        injection hxs with _ hxs; injection hxs with hrest_eq _; subst hrest_eq
        have ext_ci := evlt.heap_extends.trans evci.heap_extends
        obtain ⟨cb, crest, rfl, -, hcrest⟩ :=
          IxVM.Refinement.Core.RepList.cons_of_load (tmOExactList_mono ext_ci hcbs) ld302
        obtain rfl := binop_add_one_nat op1
        have ext_rest : Heap.Extends _ _ :=
          ev390.heap_extends.trans <| ev439.heap_extends.trans <|
            ev507.heap_extends.trans <| ev553.heap_extends.trans ev610.heap_extends
        have hrec := ih crest (pos + 1) (by simp at hsum; omega)
          (RecRulesRep.mono (ext_ci.trans ext_rest) htail)
          (tmOExactList_mono ext_rest hcrest) evrec
        simp only [List.length_cons]; omega

private theorem motiveCarrierAt_mono {c : Ixon.Constant} {r : Ixon.Recursor} {j n m : Nat}
    {a : _root_.Address} (h : FamilyOf.motiveCarrierAt c r j n = some a) (hle : n ≤ m) :
    FamilyOf.motiveCarrierAt c r j m = some a := by
  unfold FamilyOf.motiveCarrierAt at h ⊢
  cases hp : FamilyOf.peel c (r.params.toNat + j) r.typ with
  | none => simp [hp] at h
  | some e =>
    cases hd : FamilyOf.domOf c e with
    | none => simp [hp, hd] at h
    | some dm =>
      cases hl : FamilyOf.lastDom c n dm with
      | none => simp [hp, hd, hl] at h
      | some ed =>
        simp only [Bind.bind, Option.bind, hp, hd, hl] at h ⊢
        rw [FamilyOf.lastDom_mono c ed n m dm hl hle]
        exact FamilyOf.refHeadAt_mono h hle

private theorem serConstant_cprj_size_lt (i j : UInt64) (b : Bytes.Address) :
    (Ixon.serConstant ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩).size < 4294967296 := by
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hb : AddressWireWF (Core.ixAddr b) := b.size_toArray
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hcwf : NonrecursiveConstantWireWF ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ :=
    { info := .cPrj hb
      sharingCount := by show (#[] : Array Ixon.Expr).size < UInt64.size; decide
      sharingEntries := by simp
      refsCount := by show (#[] : Array _root_.Address).size < UInt64.size; decide
      refsEntries := by simp
      univsCount := by show (#[] : Array Ixon.Univ).size < UInt64.size; decide
      univsEntries := by simp
      binders := by simp [Ixon.bindersWireWF] }
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hser : Ixon.serConstant ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      nonrecursiveConstantBytes ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ := by
    unfold Ixon.serConstant
    exact (putConstant_writes_nonrecursive _ hcwf).runPut
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hbytes : nonrecursiveConstantBytes ⟨.cPrj ⟨i, j, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ ++
        (tag0Bytes i ++ tag0Bytes j ++ (Core.ixAddr b).hash) ++
        tag0Bytes 0 ++ ByteArray.empty ++ tag0Bytes 0 ++ ByteArray.empty ++
        tag0Bytes 0 ++ ByteArray.empty ++ bindersBytes #[] := rfl
  rw [hser, hbytes]
  have h1 := tag0Bytes_size_le9 i
  have h2 := tag0Bytes_size_le9 j
  have ht4 : (Ixon.Verify.Codec.tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ).size = 1 := by
    decide
  have ht0 : (Ixon.Verify.Codec.tag0Bytes 0).size = 1 := by decide
  have hbd0 : (Ixon.Verify.Codec.ConstantTables.bindersBytes #[]).size = 1 := by decide
  have hh : (Core.ixAddr b).hash.size = 32 := hb
  simp only [ByteArray.size_append, ByteArray.size_empty]
  omega

private theorem stored_of_hashed_cprj {calls : List (Call F)} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {b : Bytes.Address} {i j : Nat}
    (hh : Hashed calls (Ixon.serConstant (constructorProjection (ixAddr b) i j))) :
    recordOf E₀ (ctorAddr (ixAddr b) i j) = some (constructorProjection (ixAddr b) i j) := by
  have hwf := Ingress.projConstant_wireWF_cPrj i.toUInt64 j.toUInt64 b
  have hsz := serConstant_cprj_size_lt i.toUInt64 j.toUInt64 b
  have hex := Ixon.Verify.deConstantExact_serConstant _ hwf
  obtain ⟨lc, hget, hbytes, -⟩ := hH _ _ hh hsz (Ingress.deConstant_of_deConstantExact hex) hex
  unfold recordOf
  change (E₀.consts.get? (Address.blake3Pure (Ixon.serConstant (constructorProjection (ixAddr b) i j)))).bind
    (fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) = _
  rw [hget, Option.bind_some, hbytes]
  have h1 : constructorProjection (ixAddr b) i j =
      ⟨.cPrj ⟨i.toUInt64, j.toUInt64, ixAddr b⟩, #[], #[], #[], #[]⟩ := rfl
  rw [h1, hex]; rfl

private theorem stored_of_hashed_iprj {calls : List (Call F)} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {b : Bytes.Address} {i : Nat} {ind : Ixon.Inductive}
    (hh : Hashed calls (Ixon.serConstant (memberProjection (ixAddr b) i (.indc ind)))) :
    recordOf E₀ (memberAddr (ixAddr b) i (.indc ind)) =
      some (memberProjection (ixAddr b) i (.indc ind)) := by
  have hwf := Ingress.projConstant_wireWF_iPrj i.toUInt64 b
  have hsz := serConstant_iprj_size_lt i.toUInt64 b
  have hex := Ixon.Verify.deConstantExact_serConstant _ hwf
  obtain ⟨lc, hget, hbytes, -⟩ := hH _ _ hh hsz (Ingress.deConstant_of_deConstantExact hex) hex
  unfold recordOf
  change (E₀.consts.get? (Address.blake3Pure (Ixon.serConstant (memberProjection (ixAddr b) i (.indc ind))))).bind
    (fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) = _
  rw [hget, Option.bind_some, hbytes]
  have h1 : memberProjection (ixAddr b) i (.indc ind) =
      ⟨.iPrj ⟨i.toUInt64, ixAddr b⟩, #[], #[], #[], #[]⟩ := rfl
  rw [h1, hex]; rfl

/-- **`KernelModeled::member_ctor_addrs`** hashes every constructor projection `(pos, j, b)`
for `cur ≤ j < n`. -/
private theorem member_ctor_addrs_hashed_spec {t : Ix.Kernel.RoleTable}
    {b : Bytes.Address} {pos n : Nat} (hpos : pos < 72057594037927936)
    (hn : n < 72057594037927936) :
    ∀ (rem cur : Nat), cur + rem = n →
      ∀ {xblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        Bytes.RepAddressRef addrTy h b xblk →
        ObsFn W "KernelModeled::member_ctor_addrs"
          [xblk, .field (pos : F), .field (n : F), .field (cur : F)] h r h' cs →
        ∀ j, cur ≤ j → j < n →
          Hashed cs (Ixon.serConstant (constructorProjection (ixAddr b) pos j)) := by
  intro rem
  induction rem with
  | zero =>
    intro cur hcur _ _ _ _ _ _ _ j h1 h2; omega
  | succ rem ih =>
    intro cur hcur xblk r h h' cs rb ev j hj1 hj2
    match Obs.«KernelModeled::member_ctor_addrs».obs ev with
    | .n0 (op17 := op) .. =>
      have heq := evalBinOp_sub_eq_zero_field op
      have h1 : (n : F).val = (cur : F).val := congrArg ZMod.val heq
      rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; omega
    | .other (ev58 := evp) (op133 := op1) (ev94 := evrec) (hc135 := hc) .. =>
      obtain rfl := binop_add_one_nat op1
      by_cases hjeq : j = cur
      · subst hjeq
        obtain ⟨_, c_proj, hcp, -, -, hh, -⟩ :=
          projection_addr_ctor_raw (t := t) rb evp
        rw [fval_natCast (by omega), fval_natCast (by omega)] at hcp
        rw [hcp] at hh
        exact Core.hashed_mono (fun cl hcl => mem_of_eq hc (by call_mem)) hh
      · have hrec := ih (cur + 1) (by omega)
          (Bytes.repAddressRef_heapMono₂ addrTy evp.heap_extends rb) evrec j (by omega) hj2
        exact Core.hashed_mono (fun cl hcl => mem_of_eq hc (by call_mem)) hrec

/-- **`KernelModeled::block_ctor_addrs`** hashes every constructor projection `(pos + i, j, b)`
for every inductive member `ms[i]` and `j < ind.ctors.size`. -/
private theorem block_ctor_addrs_hashed_spec {t : Ix.Kernel.RoleTable}
    {b : Bytes.Address} :
    ∀ (ms : List Ixon.MutConst) (pos : Nat),
      pos + ms.length < 72057594037927936 →
      (∀ m ∈ ms, ∀ ind, m = .indc ind → ind.ctors.size < 72057594037927936) →
      ∀ {xmem xblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        RepList (Obs.Names.«Lists::Node<Ixon::MutConst>») Ingress.RepMutConst h ms xmem →
        Bytes.RepAddressRef addrTy h b xblk →
        ObsFn W "KernelModeled::block_ctor_addrs" [xmem, xblk, .field (pos : F)] h r h' cs →
        ∀ i ind j, ms[i]? = some (.indc ind) → j < ind.ctors.size →
          Hashed cs (Ixon.serConstant (constructorProjection (ixAddr b) (pos + i) j)) := by
  intro ms
  induction ms with
  | nil => intro pos hpos hcsz xmem xblk r h h' cs hrep rb ev i ind j hi hj; simp at hi
  | cons m rest ih =>
    intro pos hpos hcsz xmem xblk r h h' cs hrep rb ev i ind j hi hj
    match Obs.«KernelModeled::block_ctor_addrs».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hrep ld
    | .Cons (x_ctors := xct) (v140 := vlen) (ld12 := ld) (ev167 := evlen)
        (ev137 := evmca) (op224 := op1) (ev193 := evrec) (hc226 := hc) .. =>
      obtain ⟨m', rest', hlist, hmrep, hrest_rep⟩ := IxVM.Refinement.Core.RepList.cons_of_load hrep ld
      injection hlist with h1 h2; subst h1 h2
      cases m with
      | defn _ | recr _ =>
        obtain ⟨_, hv, -⟩ := hmrep; simp at hv
      | indc ind0 =>
        obtain ⟨iv, hv_m, typPtr, xct', hiv, -, hct_rep⟩ := hmrep
        injection hv_m with _ _ hl; injection hl with hi_eq _
        rw [← hi_eq] at hiv
        injection hiv with _ _ hargs
        have hct_eq : xct' = xct := by
          simp only [List.cons.injEq] at hargs; exact hargs.2.2.2.2.2.1.symm
        subst xct'
        have hct_rep' : RepList
            (Instance.mk "Lists::Node" [.named "Ixon::Constructor" []]).symbol
            Ingress.RepConstructor h ind0.ctors.toList xct := by
          rw [Obs.Names.«Lists::Node<Ixon::Constructor>».symbol]; exact hct_rep
        obtain ⟨hvlen, -⟩ := Lib.Lists.length_spec
          (by rw [Obs.Names.«Lists::length<Ixon::Constructor>».symbol]; exact evlen) hct_rep'
        rw [Array.length_toList] at hvlen; subst hvlen
        obtain rfl := binop_add_one_nat op1
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Ixon.MutConst.indc.injEq] at hi
          subst ind0
          have hnc_lt := hcsz (.indc ind) List.mem_cons_self ind rfl
          have hh := member_ctor_addrs_hashed_spec (t := t) (pos := pos) (n := ind.ctors.size)
            (by omega) hnc_lt ind.ctors.size 0 (by omega)
            (Bytes.repAddressRef_heapMono₂ addrTy evlen.heap_extends rb)
            (by simpa using evmca) j (Nat.zero_le _) hj
          simpa [Nat.add_zero] using Core.hashed_mono (fun cl hcl => mem_of_eq hc (by call_mem)) hh
        | succ i' =>
          simp only [List.getElem?_cons_succ] at hi
          have ext_r := evlen.heap_extends.trans evmca.heap_extends
          have hrec := ih (pos + 1) (by simp at hpos; omega)
            (fun m' hm' => hcsz m' (List.mem_cons_of_mem _ hm'))
            (repList_heapMono₂ _ Ingress.repMutConst_heapMono₂ ext_r hrest_rep)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_r rb) evrec i' ind j hi hj
          rw [show pos + (i' + 1) = pos + 1 + i' by omega]
          exact Core.hashed_mono (fun cl hcl => mem_of_eq hc (by call_mem)) hrec

private theorem buildFlatAuxStep_length_le {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res →
      res.length ≤ acc.length + cur.length := by
  intro cur
  induction cur with
  | nil =>
    intro pos acc res h
    simp only [buildFlatAuxStep, Option.some.injEq] at h; subst h; simp
  | cons m rest ih =>
    intro pos acc res h
    cases m with
    | defn _ | indc _ =>
      simp only [buildFlatAuxStep] at h
      have := ih (pos + 1) acc res h
      simp only [List.length_cons]; omega
    | recr r =>
      simp only [buildFlatAuxStep] at h
      split at h; · cases h
      split at h; · cases h
      split at h; swap; · cases h
      split at h; · cases h
      split at h; · cases h
      · have := ih (pos + 1) acc res h
        simp only [List.length_cons]; omega
      · split at h
        · have := ih (pos + 1) acc res h
          simp only [List.length_cons]; omega
        · split at h
          · have := ih (pos + 1) acc res h
            simp only [List.length_cons]; omega
          · have := ih (pos + 1) _ res h
            simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
            omega

private theorem buildFlatAuxStep_skip_prefix {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} :
    ∀ (pre suf : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos (pre ++ suf) acc = some res →
      (∀ (j : Nat) (r : Ixon.Recursor), pre[j]? = some (.recr r) →
        ∃ ty d k us paddr info,
          loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
            (mutsRoot rs (pos + j)) r.typ = some ty ∧
          binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat)
            ty = some d ∧
          d.getAppFn = .const k us ∧
          keyAddr t k = some paddr ∧
          indInfoAt E₀ paddr = some (some info) ∧
          info.blk = prim) →
      buildFlatAuxStep t E₀ rb crb rs prim (pos + pre.length) suf acc = some res := by
  intro pre
  induction pre with
  | nil => intro suf pos acc res h _; simpa using h
  | cons m pre' ih =>
    intro suf pos acc res h hpre
    have hpre' : ∀ j r, pre'[j]? = some (.recr r) →
        ∃ ty d k us paddr info,
          loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
            (mutsRoot rs (pos + 1 + j)) r.typ = some ty ∧
          binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat)
            ty = some d ∧
          d.getAppFn = .const k us ∧
          keyAddr t k = some paddr ∧
          indInfoAt E₀ paddr = some (some info) ∧
          info.blk = prim := by
      intro j r hj
      have := hpre (j + 1) r (by simpa using hj)
      rwa [show pos + (j + 1) = pos + 1 + j by omega] at this
    rw [show pos + (m :: pre').length = pos + 1 + pre'.length by simp; omega]
    cases m with
    | defn _ | indc _ =>
      simp only [List.cons_append, buildFlatAuxStep] at h
      exact ih suf (pos + 1) acc res h hpre'
    | recr r =>
      obtain ⟨ty, d, k, us, paddr, info, hty, hd, hfn, hka, hinfo, hblk⟩ := hpre 0 r rfl
      simp only [Nat.add_zero] at hty
      simp only [List.cons_append, buildFlatAuxStep, hty, hd, hfn, hka, hinfo, hblk, beq_self_eq_true,
        ↓reduceIte] at h
      exact ih suf (pos + 1) acc res h hpre'

/-- Pigeonhole on `buildFlatAuxStep`: when the suffix appends one entry per member
(`res.length = acc.length + cur.length`), member `j` produces `res[acc.length + j]` exactly. -/
private theorem buildFlatAuxStep_strict_suffix {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res →
      res.length = acc.length + cur.length →
      ∀ (j : Nat) (r : Ixon.Recursor), cur[j]? = some (.recr r) →
        ∃ ty d k us paddr info,
          loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
            (mutsRoot rs (pos + j)) r.typ = some ty ∧
          binderDomAfter (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat)
            ty = some d ∧
          d.getAppFn = .const k us ∧
          keyAddr t k = some paddr ∧
          indInfoAt E₀ paddr = some (some info) ∧
          res[acc.length + j]? = some ⟨paddr, true,
            ((d.getAppArgs).take info.np).map
              (Ix.Kernel.Expr.lowerBVars (r.motives.toNat + r.minors.toNat + r.indices.toNat) 0),
            us⟩ := by
  intro cur
  induction cur with
  | nil => intro _ _ _ _ _ j _ hj; simp at hj
  | cons m rest ih =>
    intro pos acc res h hlen j r hj
    cases m with
    | defn _ | indc _ =>
      simp only [buildFlatAuxStep] at h
      have hle := buildFlatAuxStep_length_le rest (pos + 1) acc res h
      simp only [List.length_cons] at hlen; omega
    | recr r0 =>
      simp only [buildFlatAuxStep] at h
      cases hty : loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r0.lvls.toNat
          (mutsRoot rs pos) r0.typ with
      | none => simp only [hty] at h; cases h
      | some ty =>
        simp only [hty] at h
        cases hd : binderDomAfter
            (r0.params.toNat + r0.motives.toNat + r0.minors.toNat + r0.indices.toNat) ty with
        | none => simp only [hd] at h; cases h
        | some d =>
          simp only [hd] at h
          cases hfn : d.getAppFn with
          | const k us =>
            simp only [hfn] at h
            cases hka : keyAddr t k with
            | none => simp only [hka] at h; cases h
            | some paddr =>
              simp only [hka] at h
              cases hinfo : indInfoAt E₀ paddr with
              | none => simp only [hinfo] at h; cases h
              | some opt =>
                simp only [hinfo] at h
                cases opt with
                | none =>
                  have hle := buildFlatAuxStep_length_le rest (pos + 1) acc res h
                  simp only [List.length_cons] at hlen; omega
                | some info =>
                  by_cases hblk : (info.blk == prim) = true
                  · simp only [hblk, ↓reduceIte] at h
                    have hle := buildFlatAuxStep_length_le rest (pos + 1) acc res h
                    simp only [List.length_cons] at hlen; omega
                  · simp only [hblk, Bool.false_eq_true, ↓reduceIte] at h
                    let sp := ((d.getAppArgs).take info.np).map
                      (Ix.Kernel.Expr.lowerBVars
                        (r0.motives.toNat + r0.minors.toNat + r0.indices.toNat) 0)
                    by_cases hin : auxEntryIn acc paddr sp us = true
                    · simp only [sp] at hin
                      simp only [hin, ↓reduceIte] at h
                      have hle := buildFlatAuxStep_length_le rest (pos + 1) acc res h
                      simp only [List.length_cons] at hlen; omega
                    · simp only [sp] at hin
                      simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
                      let newE : FlatEntry := ⟨paddr, true, sp, us⟩
                      let acc' := acc ++ [newE]
                      have hlen' : res.length = acc'.length + rest.length := by
                        simp only [acc', List.length_append, List.length_cons, List.length_nil] at hlen ⊢
                        omega
                      cases j with
                      | zero =>
                        simp only [List.getElem?_cons_zero, Option.some.injEq,
                          Ixon.MutConst.recr.injEq] at hj
                        subst hj
                        obtain ⟨auxs, hres_eq, -⟩ :=
                          buildFlatAuxStep_append_aux rest (pos + 1) acc' res h
                        have hget : res[acc.length + 0]? = some newE := by
                          rw [Nat.add_zero, hres_eq, List.append_assoc, List.getElem?_append_right
                            (Nat.le_refl _), Nat.sub_self]; rfl
                        exact ⟨ty, d, k, us, paddr, info, by simpa using hty, hd, hfn, hka,
                          hinfo, hget⟩
                      | succ j' =>
                        simp only [List.getElem?_cons_succ] at hj
                        have hrec := ih (pos + 1) acc' res h hlen' j' r hj
                        have hpos_eq : pos + 1 + j' = pos + (j' + 1) := by omega
                        have hidx_eq : acc'.length + j' = acc.length + (j' + 1) := by
                          simp only [acc', List.length_append, List.length_singleton]; omega
                        rwa [hpos_eq, hidx_eq] at hrec
          | bvar _ | fvar _ _ | sort _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
          | lit _ | proj _ _ _ => simp only [hfn] at h; cases h

private theorem collectDoms_length_le {V : ReconView} {f : Nat} :
    ∀ (n : Nat) (e : KExpr) (ds : List KExpr) (rest : KExpr),
      collectDoms V f n e = some (ds, rest) → ds.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro e ds rest h
    simp only [collectDoms, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp
  | succ m ih =>
    intro e ds rest h
    simp only [collectDoms] at h
    cases hb : binderOf V f e with
    | none => rw [hb] at h; cases h
    | some opt =>
      rw [hb] at h
      cases opt with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; simp
      | some p =>
        cases hcd : collectDoms V f m p.2.1 with
        | none => simp [hcd] at h
        | some q =>
          simp only [hcd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]; simp only [List.length_cons]
          have := ih p.2.1 q.1 q.2 hcd; omega

private theorem allMotives_length {V : ReconView} {f : Nat} {elim : KLevel} {nrp : Nat} :
    ∀ (es : List FlatEntry) (j : Nat) (ms : List KExpr),
      allMotives V f elim nrp es j = some ms → ms.length = es.length := by
  intro es
  induction es with
  | nil => intro j ms h; simp [allMotives] at h; subst h; rfl
  | cons e rest ih =>
    intro j ms h
    simp only [allMotives] at h
    cases hi : V.ind e.addr with
    | none => simp only [hi] at h; cases h
    | some opt =>
      simp only [hi] at h
      cases opt with
      | none => cases h
      | some info =>
        cases hm : motiveType V f e.addr info.ty info.np info.ni e.levels elim nrp e.aux e.params with
        | none => simp only [hm] at h; cases h
        | some mt =>
          simp only [hm] at h
          cases hr : allMotives V f elim nrp rest (j + 1) with
          | none => simp [hr] at h
          | some ms' =>
            simp only [hr, Option.map_some, Option.some.injEq] at h
            subst h; simp [ih (j + 1) ms' hr]

private theorem minorDoms_length {V : ReconView} {f : Nat} {es : List FlatEntry} {fop : List Nat}
    {aux : Bool} {sp : List KExpr} {us : List KLevel} {nrp nMot motiveBase selfMemIdx : Nat}
    {blk : _root_.Address} {idx : Nat} {elim : KLevel} :
    ∀ (cs : List Nat) (prev : Nat) (ms : List KExpr),
      minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs = some ms →
      ms.length = cs.length := by
  intro cs
  induction cs with
  | nil => intro _ ms h; simp [minorDoms] at h; subst h; rfl
  | cons c rest ih =>
    intro prev ms h
    simp only [minorDoms] at h
    cases hc : V.ctor blk idx c with
    | none => simp only [hc] at h; cases h
    | some p =>
      simp only [hc] at h
      cases hm : minorAt V f es fop (V.key (V.ctorAddr blk idx c)) p.1 p.2 aux sp us nrp nMot
          prev motiveBase selfMemIdx elim with
      | none => simp only [hm] at h; cases h
      | some m =>
        simp only [hm] at h
        cases hr : minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim
            (prev + 1) rest with
        | none => simp [hr] at h
        | some ms' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h; simp [ih (prev + 1) ms' hr]

private theorem allMinors_length_eq_flatTotalCtors {V : ReconView} {f : Nat}
    {fullEs : List FlatEntry} {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel} :
    ∀ (es : List FlatEntry) (prev pos : Nat) (ms : List KExpr),
      allMinors V f fullEs fop nrp nMot motiveBase elim es prev pos = some ms →
      flatTotalCtors V es = some ms.length := by
  intro es
  induction es with
  | nil => intro _ _ ms h; simp [allMinors] at h; subst h; rfl
  | cons e rest ih =>
    intro prev pos ms h
    simp only [allMinors] at h
    cases hi : V.ind e.addr with
    | none => simp only [hi] at h; cases h
    | some opt =>
      simp only [hi] at h
      cases opt with
      | none => cases h
      | some info =>
        cases hm : minorDoms V f fullEs fop e.aux e.params e.levels nrp nMot motiveBase pos
            info.blk info.idx elim prev (List.range info.nctors) with
        | none => simp only [hm] at h; cases h
        | some m0 =>
          simp only [hm] at h
          cases hr : allMinors V f fullEs fop nrp nMot motiveBase elim rest
              (prev + m0.length) (pos + 1) with
          | none => simp [hr] at h
          | some mrest =>
            simp only [hr, Option.map_some, Option.some.injEq] at h
            subst h
            have hm0_len : m0.length = info.nctors := by
              rw [minorDoms_length _ _ _ hm, List.length_range]
            have htot_rest := ih (prev + m0.length) (pos + 1) mrest hr
            simp only [flatTotalCtors, hi, htot_rest, List.length_append, hm0_len]

private theorem peelForalls_wrapForalls (body : KExpr) (dl : KLevel) :
    ∀ (ds : List KExpr), peelForalls ds.length (wrapForalls body ds dl) = some body
  | [] => rfl
  | d :: ds => by
    simp only [List.length_cons, wrapForalls, List.foldr_cons, peelForalls]
    exact peelForalls_wrapForalls body dl ds

private theorem peelForalls_add :
    ∀ (m n : Nat) (e : KExpr),
      peelForalls (m + n) e = (peelForalls m e).bind (peelForalls n) := by
  intro m
  induction m with
  | zero => intro n e; simp [peelForalls]
  | succ m ih =>
    intro n e
    cases e with
    | forallE d b bm =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [peelForalls]
      exact ih n b
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp [peelForalls]

private theorem appSpine_getAppFn (h : KExpr) :
    ∀ (args : List KExpr), (appSpine h args).getAppFn = h.getAppFn
  | [] => rfl
  | a :: args => by
    simp only [appSpine, List.foldl_cons]
    exact (appSpine_getAppFn (.app h a) args).trans rfl

/-- Syntactic shape of `recTypeAt`: `lenP + es.length + tot + lenI` leading `forallE` binders
(with `lenP ≤ nP`, `lenI ≤ self.ni`, `flatTotalCtors V es = some tot`), followed by the major
premise `forallE dR concl _` where `dR.getAppFn = .const (V.key ek.addr) ek.levels` and `concl`
is an `app` (not a `forallE`). -/
private theorem recTypeAt_forall_shape {V : ReconView} {f : Nat} {es : List FlatEntry}
    {off nP k : Nat} {e0 ek : FlatEntry} {prim self : IndData} {Rty : KExpr}
    (he0 : es[0]? = some e0) (hek : es[k]? = some ek)
    (hprim : V.ind e0.addr = some (some prim)) (hself : V.ind ek.addr = some (some self))
    (hrec : recTypeAt V f es off nP k = some Rty) :
    ∃ (lenP lenI tot : Nat) (dR concl : KExpr) (bm : Ix.Kernel.BinderMeta),
      lenP ≤ nP ∧ lenI ≤ self.ni ∧
      flatTotalCtors V es = some tot ∧
      peelForalls (lenP + es.length + tot + lenI) Rty = some (.forallE dR concl bm) ∧
      dR.getAppFn = .const (V.key ek.addr) ek.levels ∧
      ∀ d' b' m', concl ≠ .forallE d' b' m' := by
  unfold recTypeAt at hrec
  simp only [he0, hek, hprim, hself] at hrec
  cases hcd1 : collectDoms V f nP
      (exprInstLevels ((List.range prim.nl).map fun i => Ix.Kernel.Level.param (off + i)) prim.ty) with
  | none => simp only [hcd1] at hrec; cases hrec
  | some p1 =>
    simp only [hcd1] at hrec
    cases ham : allMotives V f (elimLevel off) nP es 0 with
    | none => simp [ham] at hrec
    | some motDoms =>
      cases hfop : flatOwnParams V es with
      | none => simp [ham, hfop] at hrec
      | some fop =>
        simp only [ham, hfop] at hrec
        cases hmin : allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 with
        | none => simp only [hmin] at hrec; cases hrec
        | some minDoms =>
          simp only [hmin] at hrec
          cases hpmp : peelMotiveParams nP ek.aux ek.params self.np 0
              (exprInstLevels ek.levels self.ty) with
          | none => simp only [hpmp] at hrec; cases hrec
          | some selfAfter =>
            simp only [hpmp] at hrec
            cases hcd2 : collectDoms V f self.ni selfAfter with
            | none => simp only [hcd2] at hrec; cases hrec
            | some p2 =>
              simp only [hcd2, Option.some.injEq] at hrec
              subst hrec
              have hlenP := collectDoms_length_le _ _ _ _ hcd1
              have hlenI := collectDoms_length_le _ _ _ _ hcd2
              have hlenMot := allMotives_length _ _ _ ham
              have htot := allMinors_length_eq_flatTotalCtors _ _ _ _ hmin
              have hli_len : (liftIndices p2.1 (es.length + minDoms.length)).length = p2.1.length := by
                simp [liftIndices]
              let pre := nP + es.length + minDoms.length + self.ni
              let head : KExpr := .const (V.key ek.addr) ek.levels
              let withArgs := if ek.aux then specParamsLifted head ek.params
                  (es.length + minDoms.length + self.ni)
                else appBVarsDec head nP (pre - 1)
              let concl : KExpr := .app (conclIndices (.bvar (pre - (nP + k))) self.ni) (.bvar 0)
              refine ⟨p1.1.length, p2.1.length, minDoms.length,
                appBVarsDown withArgs self.ni, concl, bmeta (elimLevel off),
                hlenP, hlenI, htot, ?_, ?_, ?_⟩
              · rw [show p1.1.length + es.length + minDoms.length + p2.1.length =
                    p1.1.length + (motDoms.length + (minDoms.length +
                      (liftIndices p2.1 (es.length + minDoms.length)).length)) by
                    rw [hlenMot, hli_len]; omega]
                rw [peelForalls_add, peelForalls_wrapForalls, Option.bind_some,
                    peelForalls_add, peelForalls_wrapForalls, Option.bind_some,
                    peelForalls_add, peelForalls_wrapForalls, Option.bind_some,
                    peelForalls_wrapForalls]
              · simp only [withArgs, head, pre, appBVarsDown, appSpine_getAppFn]
                split <;> simp [specParamsLifted, appBVarsDec, appSpine_getAppFn,
                  Ix.Kernel.Expr.getAppFn]
              · intro _ _ _ h; simp [concl] at h

private theorem wrapConsEqObs_peelForalls {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} :
    ∀ (n : Nat) {g d g' : KExpr},
      WrapConsEqObs W ObsW g d →
      peelForalls n g = some g' →
      ∃ d', peelForalls n d = some d' ∧ WrapConsEqObs W ObsW g' d' := by
  intro n
  induction n with
  | zero => intro g d g' h hg; simp [peelForalls] at hg; subst hg; exact ⟨d, rfl, h⟩
  | succ m ih =>
    intro g d g' h hg
    cases g with
    | forallE dg bg mg =>
      simp only [peelForalls] at hg
      cases h with
      | forallE _ _ _ hb => exact ih hb hg
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => simp [peelForalls] at hg

private theorem wrapConsEqObs_not_forall {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {g d : KExpr}
    (h : WrapConsEqObs W ObsW g d) (hnf : ∀ d' b' m', g ≠ .forallE d' b' m') :
    ∀ d' b' m', d ≠ .forallE d' b' m' := by
  cases h with
  | forallE _ _ _ _ => exact (hnf _ _ _ rfl).elim
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ _ | letE _ _ _ | proj _ =>
    intro _ _ _ heq; cases heq

private theorem wrapConsEqObs_count_foralls {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} :
    ∀ (n₁ : Nat) {n₂ : Nat} {g d g' d' : KExpr},
      WrapConsEqObs W ObsW g d →
      peelForalls n₁ g = some g' → (∀ a b m, g' ≠ .forallE a b m) →
      peelForalls n₂ d = some d' → (∀ a b m, d' ≠ .forallE a b m) →
      n₁ = n₂ := by
  intro n₁
  induction n₁ with
  | zero =>
    intro n₂ g d g' d' h hg hng hd hnd
    simp only [peelForalls, Option.some.injEq] at hg; subst hg
    cases n₂ with
    | zero => rfl
    | succ m₂ =>
      cases d with
      | forallE _ _ _ => exact (wrapConsEqObs_not_forall h hng _ _ _ rfl).elim
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ => simp [peelForalls] at hd
  | succ m₁ ih =>
    intro n₂ g d g' d' h hg hng hd hnd
    cases g with
    | forallE dg bg mg =>
      simp only [peelForalls] at hg
      cases h with
      | forallE _ _ _ hb =>
        cases n₂ with
        | zero =>
          simp only [peelForalls, Option.some.injEq] at hd; subst hd
          exact (hnd _ _ _ rfl).elim
        | succ m₂ =>
          simp only [peelForalls] at hd
          exact congrArg Nat.succ (ih hb hg hng hd hnd)
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ => simp [peelForalls] at hg

private theorem wrapConsEqObs_getAppFn_const_eq {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {e₁ e₂ : KExpr} {k : KKey} {us : List KLevel}
    (h : WrapConsEqObs W ObsW e₁ e₂) (hfn : e₁.getAppFn = .const k us) :
    e₂.getAppFn = .const k us := by
  induction h with
  | const n ls => exact hfn
  | app hf _ ihf _ => exact ihf hfn
  | bvar _ | fvar _ _ | sort _ | lit _ | lam _ _ _ _ | forallE _ _ _ _ | letE _ _ _ | proj _ =>
    simp [Ix.Kernel.Expr.getAppFn] at hfn

/-- On a recursor type `ty` related to `recTypeAt ... = some Rty` by either `Rty = ty` or
`WrapConsEqObs (wrapAt t E₀) ObsW Rty ty`, the major premise domain `d` of `ty` has the exact
constant head and level list `.const (Core.keyOf t ek.addr) ek.levels`. -/
private theorem recTypeAt_majorDom_head_eq {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {ObsW : KKey → Nat → Prop} (hwf : t.wf = true)
    {f off nP k tot : Nat} {es : List FlatEntry} {e0 ek : FlatEntry} {prim self : IndData}
    {Rty ty d body : KExpr}
    (he0 : es[0]? = some e0) (hek : es[k]? = some ek)
    (hprim : indDataAt t E₀ e0.addr = some (some prim))
    (hself : indDataAt t E₀ ek.addr = some (some self))
    (hrec : recTypeAt (ReconView.ofStore t E₀) f es off nP k = some Rty)
    (htot : flatTotalCtors (ReconView.ofStore t E₀) es = some tot)
    (hd : binderDomAfter (nP + es.length + tot + self.ni) ty = some d)
    (hbody : peelForalls (nP + es.length + tot + self.ni + 1) ty = some body)
    (hnf : ∀ a b m, body ≠ .forallE a b m)
    (hrel : Rty = ty ∨ WrapConsEqObs (wrapAt t E₀) ObsW Rty ty) :
    d.getAppFn = .const (Core.keyOf t ek.addr) ek.levels := by
  obtain ⟨lenP, lenI, tot', dR, concl, bm, hlenP, hlenI, htot', hpeelR, hfnR, hnfR⟩ :=
    recTypeAt_forall_shape he0 hek hprim hself hrec
  have htot_eq : tot' = tot := Option.some.inj (htot'.symm.trans htot)
  subst tot'
  have hpeelR1 : peelForalls (lenP + es.length + tot + lenI + 1) Rty = some concl := by
    rw [peelForalls_add, hpeelR]; rfl
  rcases hrel with rfl | hwrap
  · have hcnt : lenP + es.length + tot + lenI + 1 = nP + es.length + tot + self.ni + 1 :=
      wrapConsEqObs_count_foralls (W := wrapAt t E₀) (ObsW := ObsW) _
        (WrapConsEqObs.refl Rty) hpeelR1 hnfR hbody hnf
    have hP : lenP = nP := by omega
    have hI : lenI = self.ni := by omega
    subst lenP lenI
    have hdR : binderDomAfter (nP + es.length + tot + self.ni) Rty = some dR := by
      simp [binderDomAfter, hpeelR]
    have hd_eq : dR = d := Option.some.inj (hdR.symm.trans hd)
    rw [← hd_eq]; exact hfnR
  · have hcnt := wrapConsEqObs_count_foralls _ hwrap hpeelR1 hnfR hbody hnf
    have hP : lenP = nP := by omega
    have hI : lenI = self.ni := by omega
    subst lenP lenI
    obtain ⟨d_all, hpeel_ty, hwrap_all⟩ := wrapConsEqObs_peelForalls _ hwrap hpeelR
    cases hwrap_all with
    | @forallE _ _ _ d_ty _ _ _ _ hcons hdom _ =>
      have hd_eq : d_ty = d := by
        have : binderDomAfter (nP + es.length + tot + self.ni) ty = some d_ty := by
          simp [binderDomAfter, hpeel_ty]
        exact Option.some.inj (this.symm.trans hd)
      subst hd_eq
      cases hcons with
      | refl _ => exact wrapConsEqObs_getAppFn_const_eq hdom hfnR
      | step _ hhd hW _ _ =>
        simp only [appHead, hfnR, Option.some.injEq] at hhd
        subst hhd
        have hnone := wrapAt_of_indDataAt_some hwf hself
        change wrapAt t E₀ (Core.keyOf t ek.addr) = _ at hW
        rw [hnone] at hW; cases hW

private theorem ruleBodies_length {V : ReconView} {f : Nat} {es : List FlatEntry} {fop : List Nat}
    {peers : List _root_.Address} {nP nMot nMin : Nat} {us recLvls : List KLevel} {aux : Bool}
    {sp : List KExpr} {elim : KLevel} {blk : _root_.Address} {idx off : Nat} :
    ∀ (cs : List Nat) (bs : List KExpr),
      ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off cs = some bs →
      bs.length = cs.length := by
  intro cs
  induction cs with
  | nil => intro bs h; simp [ruleBodies] at h; subst h; rfl
  | cons c rest ih =>
    intro bs h
    simp only [ruleBodies] at h
    cases hc : V.ctor blk idx c with
    | none => simp only [hc] at h; cases h
    | some p =>
      simp only [hc] at h
      cases hb : ruleBody V f es fop peers p.1 (off + c) nP nMot nMin p.2 us recLvls aux sp elim with
      | none => simp only [hb] at h; cases h
      | some b =>
        simp only [hb] at h
        cases hr : ruleBodies V f es fop peers nP nMot nMin us recLvls aux sp elim blk idx off rest with
        | none => simp [hr] at h
        | some bs' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h; simp [ih bs' hr]

private theorem ctorsBefore_succ_add (V : ReconView) :
    ∀ (es : List FlatEntry) (k cbk : Nat) (ek : FlatEntry) (info : IndData),
      es[k]? = some ek → V.ind ek.addr = some (some info) →
      ctorsBefore V es k = some cbk →
      ctorsBefore V es (k + 1) = some (cbk + info.nctors) := by
  intro es
  induction es with
  | nil => intro k _ _ _ hk; simp at hk
  | cons e rest ih =>
    intro k cbk ek info hk hi hcb
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
      simp only [ctorsBefore, Option.some.injEq] at hcb; subst hcb
      simp only [ctorsBefore, hi, Nat.zero_add, Nat.add_zero]
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [ctorsBefore] at hcb ⊢
      cases he : V.ind e.addr with
      | none => rw [he] at hcb; cases hcb
      | some opt =>
        rw [he] at hcb
        cases opt with
        | none => cases hcb
        | some i0 =>
          cases hcb' : ctorsBefore V rest k' with
          | none => simp [hcb'] at hcb
          | some n =>
            simp only [hcb', Option.some.injEq] at hcb; subst hcb
            rw [ih k' n ek info hk hi hcb']
            simp only [Option.some.injEq]; omega

private theorem eventually_forall_range (P : Nat → Nat → Prop) :
    ∀ n : Nat, (∀ k < n, Eventually (P k)) → Eventually (fun f => ∀ k < n, P k f) := by
  intro n
  induction n with
  | zero => intro _; exact Eventually.always (fun _ k hk => absurd hk (Nat.not_lt_zero k))
  | succ m ih =>
    intro h
    have hm := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hlast := h m (Nat.lt_succ_self m)
    exact (hm.and hlast).mono fun f ⟨h1, h2⟩ k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact h1 k hlt
      · exact h2

/-! ## Section 5: `check_recs` passes and `check_family` core -/

private theorem indInfoAt_of_indDataAt {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {d : IndData}
    (h : indDataAt t E₀ a = some (some d)) :
    indInfoAt E₀ a = some (some ⟨d.nl, d.np, d.nctors, d.blk, d.idx⟩) ∧
    ∃ ca p cb ms ind, recordOf E₀ a = some ca ∧ ca.info = .iPrj p ∧
      recordOf E₀ p.block = some cb ∧ cb.info = .muts ms ∧
      ms[p.idx.toNat]? = some (.indc ind) ∧
      d.nl = ind.lvls.toNat ∧ d.np = ind.params.toNat ∧ d.ni = ind.indices.toNat ∧
      d.nctors = ind.ctors.size ∧ d.blk = p.block ∧ d.idx = p.idx.toNat := by
  unfold indDataAt at h
  cases hca : recordOf E₀ a with
  | none => simp only [hca] at h; cases h
  | some ca =>
    simp only [hca] at h
    cases hi : ca.info with
    | iPrj p =>
      simp only [hi] at h
      cases hcb : recordOf E₀ p.block with
      | none => simp only [hcb] at h; cases h
      | some cb =>
        simp only [hcb] at h
        cases hms : cb.info with
        | muts ms =>
          simp only [hms] at h
          cases hm : ms[p.idx.toNat]? with
          | none => simp only [hm] at h; cases h
          | some m =>
            simp only [hm] at h
            cases m with
            | indc ind =>
              cases hld : loadedAt t (fun x => E₀.blobs.get? x) cb (blockSelf t p.block ms)
                  ind.lvls.toNat (mutsRoot ms p.idx.toNat) ind.typ with
              | none => simp only [hld] at h; cases h
              | some ty =>
                simp only [hld, Option.some.injEq] at h
                subst h
                refine ⟨?_, ca, p, cb, ms, ind, rfl, hi, hcb, hms, hm, rfl, rfl, rfl, rfl, rfl, rfl⟩
                unfold indInfoAt; simp only [hca, hi, hcb, hms, hm]
            | defn _ | recr _ => simp at h
        | defn _ | axio _ | quot _ | recr _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
          simp only [hms] at h; cases h
    | defn _ | axio _ | quot _ | recr _ | muts _ | dPrj _ | cPrj _ | rPrj _ =>
      simp only [hi] at h; cases h

private theorem indInfoAt_ne_indDataAt_none {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {info : IndInfo}
    (hi : indInfoAt E₀ a = some (some info)) (hd : indDataAt t E₀ a = some none) : False := by
  unfold indInfoAt at hi
  unfold indDataAt at hd
  cases hca : recordOf E₀ a with
  | none => simp only [hca] at hi; cases hi
  | some ca =>
    simp only [hca] at hi hd
    cases hci : ca.info with
    | iPrj p =>
      simp only [hci] at hd
      cases hcb : recordOf E₀ p.block with
      | none => simp only [hcb] at hd; cases hd
      | some cb =>
        simp only [hcb] at hd
        cases hms : cb.info with
        | muts ms =>
          simp only [hms] at hd
          cases hm : ms[p.idx.toNat]? with
          | none => simp only [hm] at hd; cases hd
          | some m =>
            simp only [hm] at hd
            cases m with
            | indc ind =>
              cases hld : loadedAt t (fun x => E₀.blobs.get? x) cb (blockSelf t p.block ms)
                  ind.lvls.toNat (mutsRoot ms p.idx.toNat) ind.typ <;> simp only [hld] at hd <;> cases hd
            | defn _ | recr _ => simp at hd
        | defn _ | axio _ | quot _ | recr _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
          simp only [hms] at hd; cases hd
    | defn _ | axio _ | quot _ | recr _ | muts _ | dPrj _ | cPrj _ | rPrj _ =>
      simp only [hci] at hi; cases hi

private theorem originals_all_indInfoAt {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {off : Nat} :
    ∀ (addrs : List _root_.Address) (os : List FlatEntry),
      originals (FlatView.ofStore t E₀) off addrs = some os →
      ∀ e ∈ os, ∃ info, indInfoAt E₀ e.addr = some (some info) := by
  intro addrs
  induction addrs with
  | nil => intro os h; simp [originals] at h; subst h; intro _ hm; cases hm
  | cons a rest ih =>
    intro os h
    simp only [originals] at h
    cases hi : (FlatView.ofStore t E₀).ci a with
    | none => rw [hi] at h; cases h
    | some opt =>
      rw [hi] at h
      cases opt with
      | none => cases h
      | some info =>
        cases hr : originals (FlatView.ofStore t E₀) off rest with
        | none => simp [hr] at h
        | some os' =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          intro e he
          rcases List.mem_cons.mp he with rfl | he'
          · exact ⟨info, hi⟩
          · exact ih os' hr e he'

private theorem buildFlatAuxStep_all_indInfoAt {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {prim : _root_.Address} :
    ∀ (cur : List Ixon.MutConst) (pos : Nat) (acc res : List FlatEntry),
      buildFlatAuxStep t E₀ rb crb rs prim pos cur acc = some res →
      (∀ e ∈ acc, ∃ info, indInfoAt E₀ e.addr = some (some info)) →
      ∀ e ∈ res, ∃ info, indInfoAt E₀ e.addr = some (some info) := by
  intro cur
  induction cur with
  | nil => intro _ acc res h hall; simp [buildFlatAuxStep] at h; subst h; exact hall
  | cons m rest ih =>
    intro pos acc res h hall
    cases m with
    | defn _ | indc _ =>
      simp only [buildFlatAuxStep] at h
      exact ih (pos + 1) acc res h hall
    | recr r =>
      simp only [buildFlatAuxStep] at h
      split at h; · cases h
      split at h; · cases h
      split at h; swap; · cases h
      split at h; · cases h
      split at h; · cases h
      · exact ih (pos + 1) acc res h hall
      · rename_i _ _ _ _ _ _ _ _ _ _ paddr info hinfo
        split at h
        · exact ih (pos + 1) acc res h hall
        · split at h
          · exact ih (pos + 1) acc res h hall
          · refine ih (pos + 1) _ res h (fun e he => ?_)
            rcases List.mem_append.mp he with he' | he'
            · exact hall e he'
            · simp only [List.mem_singleton] at he'; subst he'; exact ⟨info, hinfo⟩

/-- **`KernelCheck::build_flat_own_params`** lifts `indInfoAt` to `indDataAt` for every entry
of `es`. -/
private theorem flat_entries_indDataAt_of_build_flat_own_params {rootCalls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (es : List FlatEntry) {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ c ∈ cs, c ∈ rootCalls) →
      RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) h es xflat →
      (∀ e ∈ es, Held R e.addr ∧ ∃ info, indInfoAt E₀ e.addr = some (some info)) →
      ObsFn W "KernelCheck::build_flat_own_params" [xflat] h r h' cs →
      ∀ e ∈ es, Held R e.addr ∧ ∃ info, indDataAt t E₀ e.addr = some (some info) := by
  have hIA : IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_ofStore ht hwf hS hH hbd hRagree hcl hlv
  intro es
  induction es with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hm; cases hm
  | cons e rest ih =>
    intro xflat r h h' cs hsub hes hall ev
    match Obs.«KernelCheck::build_flat_own_params».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons (x_rest := xrest) (x_member_addr := xa) (m83 := m_ci) (cs96 := cs_ci)
        (m182 := m_sg) (cs184 := cs_sg) (cs216 := cs_rec)
        (ld12 := ld) (ev98 := evci) (ld92 := ldci) (sg189 := sg1) (ev218 := evrec) (hc227 := hc) .. =>
      obtain ⟨e', rest', h1, he', hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with h1e h1r; subst h1e h1r
      obtain ⟨_, _, _, ae, htup, rae, hae, -, -⟩ := he'
      injection htup with hl; injection hl with hxa _; subst hxa
      obtain ⟨hSe, info, hinfo⟩ := hall e List.mem_cons_self
      rw [← hae] at hSe hinfo
      obtain ⟨hInd, hOther⟩ := hIA (fun c (hc' : c ∈ cs_ci) => hsub c (mem_of_eq hc (by call_mem)))
        hSe rae evci ldci
      cases sg1 with
      | other hne _ _ _ =>
        exact (indInfoAt_ne_indDataAt_none hinfo (hOther hne)).elim
      | Induct _ _ _ _ _ _ _ _ hvi _ hh_sg _ =>
        obtain ⟨d, _, hd_at, -⟩ := hInd _ _ _ _ _ _ _ _ hvi
        rw [hae] at hd_at hSe
        have hrest_res := ih (fun c (hc' : c ∈ cs_rec) => hsub c (mem_of_eq hc (by call_mem)))
          (flatList_mono (hh_sg ▸ evci.heap_extends) hrest)
          (fun x hx => hall x (List.mem_cons_of_mem _ hx)) evrec
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨hSe, d, hd_at⟩
        · exact hrest_res x hx'

/-- Lightweight address-only extraction from `KernelCheck::flat_find_pos_kind` when it returns
`(1, xsp)`: recovers `es[i]? = some e`, `e.addr = ixAddr target`, and `xsp = pos + i` without
inspecting `spec_params` or `occ_us`. -/
private theorem flat_find_pos_kind_addr {κ : _root_.Address → KKey} {target : Bytes.Address}
    {xtarget xwaux xwsp xwus : SourceValue F} :
    ∀ (es : List FlatEntry) (pos : Nat) {xflat xsp : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h target xtarget →
      ObsFn W "KernelCheck::flat_find_pos_kind"
        [xflat, xtarget, xwaux, xwsp, xwus, .field (pos : F)] h (.tuple [.field 1, xsp]) h' cs →
      ∃ i e, es[i]? = some e ∧ e.addr = ixAddr target ∧ xsp = .field (((pos + i : Nat) : F)) := by
  intro es
  induction es with
  | nil =>
    intro pos xflat xsp h h' cs hflat _ ev
    match Obs.«KernelCheck::flat_find_pos_kind».obs ev with
    | .Nil (he24 := hr) .. =>
      injection hr with hl; injection hl with h1 _
      exact absurd (Value.field.inj h1) one_ne_zero
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hne, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hflat ld
      cases hne
  | cons e rest ih =>
    intro pos xflat xsp h h' cs hflat rtarget ev
    match Obs.«KernelCheck::flat_find_pos_kind».obs ev with
    | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hflat ld
    | .Cons_n1 (x_member_addr := xma) (v92 := v92) (v155 := v155) (v208 := v208) (x226 := x226)
        (ld12 := ld) (ev105 := ev105) (op241 := op241) (op233 := op233) (he253 := hr) .. =>
      injection hr with hl; injection hl with _ hl; injection hl with hxsp _
      obtain ⟨e', rest', h1, he', -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hflat ld
      injection h1 with h1e _; subst h1e
      obtain ⟨xa, _, _, a, htup, ra, ha_eq, -, -⟩ := he'
      injection htup with hts; injection hts with hxma _; subst hxma
      obtain ⟨hva, -⟩ := Lib.address_eq_spec ev105 ra rtarget
      have ha_t : a = target := by
        by_contra hne
        rw [ite_eq_right hne] at hva
        rw [hva] at op241
        cases v155 with
        | field fv155 =>
          simp only [evalBinOp, zero_mul, Except.ok.injEq] at op241
          rw [← op241] at op233
          cases v208 with
          | field fv208 =>
            simp only [evalBinOp, zero_mul, Except.ok.injEq, Value.field.injEq] at op233
            exact zero_ne_one op233
          | ptr _ _ | tuple _ | construct _ _ _ => simp [evalBinOp] at op233
        | ptr _ _ | tuple _ | construct _ _ _ => simp [evalBinOp] at op241
      subst ha_t
      exact ⟨0, e, rfl, ha_eq.symm, by simpa using hxsp⟩
    | .Cons_other (x_rest := xrest) (m93 := m93) (m156 := m156) (m209 := m209)
        (ld12 := ld) (ev105 := ev105) (sg163 := sg1) (sg216 := sg2)
        (op_epyjxidj := op1) (ev278 := evrec) .. =>
      obtain ⟨e', rest', h1, -, hrest⟩ := IxVM.Refinement.Core.RepList.cons_of_load hflat ld
      injection h1 with _ h1r; subst h1r
      have ext1 : Heap.Extends m93 m156 := by
        cases sg1 with
        | n0 _ _ hh _ => rw [hh]
        | other _ _ _ _ hh _ => rw [hh]
      have ext2 : Heap.Extends m156 m209 := by
        cases sg2 with
        | n1 _ _ _ _ _ _ ev_sp ev_us _ _ => exact ev_sp.heap_extends.trans ev_us.heap_extends
        | other _ _ hh _ => rw [hh]
      have ext_all := ev105.heap_extends.trans (ext1.trans ext2)
      obtain rfl := binop_add_one_nat op1
      obtain ⟨i, e₁, hi, ha₁, hxsp⟩ := ih (pos + 1)
        (flatList_mono ext_all hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_all rtarget) evrec
      exact ⟨i + 1, e₁, hi, ha₁, by rwa [show pos + 1 + i = pos + (i + 1) by omega] at hxsp⟩

private theorem flatTotalCtors_det {V : ReconView} {es : List FlatEntry} {t₁ t₂ : Nat}
    (h1 : flatTotalCtors V es = some t₁) (h2 : flatTotalCtors V es = some t₂) : t₁ = t₂ :=
  Option.some.inj (h1.symm.trans h2)

/-- Unpacked data from one `.Cons` step (at position `k`) of `KernelModeled::check_recs`,
`KernelCheck::check_recursor_canonical_at`, and `KernelCheck::canonical_rules_at_pos`. -/
private structure CheckRecsStep (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (E₀ R : Ixon.Env) (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (k np off bnl : Nat) (rc : Ixon.Recursor)
    (xrc xta xrest xmrest xsrc xdst xaset xfam xform r_out : SourceValue F)
    (h h' : Heap F) where
  ty : KExpr
  d : KExpr
  us : List KLevel
  pa : Bytes.Address
  pInfo : IndData
  prim : _root_.Address
  cprim : Ixon.Constant
  msp : Array Ixon.MutConst
  os : List FlatEntry
  flat : List FlatEntry
  tot : Nat
  ek : FlatEntry
  fop : List Nat
  -- Core recursor equalities and bounds
  rnp_eq : rc.params.toNat = np
  nmot_eq : rc.motives.toNat = rs.size
  nmin_eq : rc.minors.toNat = tot
  lvls_eq : rc.lvls.toNat = bnl + off
  flat_len : flat.length = rs.size
  tot_lt : tot < 2 ^ 39
  lvls_lt : rc.lvls.toNat < 4294967296
  ni_eq : pInfo.ni = rc.indices.toNat
  ni_lt : rc.indices.toNat < 72057594037927936
  pnp_le : pInfo.np ≤ d.getAppArgs.length
  pInfo_at : indDataAt t E₀ (ixAddr pa) = some (some pInfo)
  pInfo_nctors_lt : pInfo.nctors < 72057594037927936
  pInfo_idx_lt : pInfo.idx < 72057594037927936
  pInfo_blk_held : Held R pInfo.blk
  loaded_ty : loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
    (mutsRoot rs k) rc.typ = some ty
  major_dom : binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
    rc.indices.toNat) ty = some d
  major_fn : d.getAppFn = .const (Core.keyOf t (ixAddr pa)) us
  -- Flattened block at this step
  prim_frp : firstRecrParentBlock t E₀ rb crb rs pInfo.blk 0 rs.toList = some prim
  prim_held : Held R prim
  prim_rec : recordOf E₀ prim = some cprim
  prim_muts : cprim.info = .muts msp
  orig_eq : originals (FlatView.ofStore t E₀) off (indcAddrs prim 0 msp.toList) = some os
  aux_eq : buildFlatAuxStep t E₀ rb crb rs prim 0 rs.toList os = some flat
  filt_eq : flat.filter (fun e => !e.aux) = os
  os_props : ∀ e ∈ os, e.aux = false ∧ e.params = [] ∧ Held R e.addr ∧
    ∃ idx ind, msp[idx]? = some (.indc ind) ∧ e.addr = memberAddr prim idx (.indc ind)
  flat_held_ind : ∀ e ∈ flat, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
    (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)
  flat_tot : flatTotalCtors (ReconView.ofStore t E₀) flat = some tot
  flat_k : flat[k]? = some ek
  ek_addr : ek.addr = ixAddr pa
  fop_eq : flatOwnParams (ReconView.ofStore t E₀) flat = some fop
  fop_len : fop.length = flat.length
  fop_lt : ∀ n ∈ fop, n < 72057594037927936
  -- Motive carriers & major head (from `build_rec_type_heap_shape` + `heapEqOrWrap`)
  motive_carrier : ∀ (j : Nat) (ej : FlatEntry), flat[j]? = some ej →
    ∃ n, FamilyOf.motiveCarrierAt crb rc j n = some ej.addr
  major_head : ∃ n, FamilyOf.majorHeadAt crb rc n = some ek.addr
  -- Direct `check_carriers` witness (used at k = 0)
  m_car : Heap F
  x_ty : SourceValue F
  blobs : List (_root_.Address × ByteArray)
  ext_h_car : Heap.Extends h m_car
  raw_ty : Ingress.RawConvExpr crb.refs.toList [] crb.univs.toList
    crb.sharing.toList blobs m_car 4294967295 rc.typ x_ty
  ev_carriers : ∃ r_c m_c cs_c, ObsFn W "KernelModeled::check_carriers"
    [x_ty, .field (rc.params.toNat : F), xta] m_car r_c m_c cs_c
  -- `check_rec_motive` non-forall body for `recTypeAt_majorDom_head_eq`
  ty_body : KExpr
  ty_peel_body : peelForalls (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
    rc.indices.toNat + 1) ty = some ty_body
  ty_body_nf : ∀ a b m, ty_body ≠ .forallE a b m
  -- Canonical check subcalls for Pass 2 & Pass 3
  m_brt_in : Heap F
  m_brt_out : Heap F
  x_elim : SourceValue F
  x_flat : SourceValue F
  x_fop : SourceValue F
  x_cty : SourceValue F
  x_pty : SourceValue F
  x_pnl : SourceValue F
  x_rules : SourceValue F
  x_rba : SourceValue F
  x_pba : SourceValue F
  x_r : SourceValue F
  x_rlvls : SourceValue F
  x_peers : SourceValue F
  x_occ_us : SourceValue F
  x_sp : SourceValue F
  x_cbk : SourceValue F
  x_can : SourceValue F
  x_form2 : SourceValue F
  rba_b : Bytes.Address
  pba_b : Bytes.Address
  rba_addr : ixAddr rba_b = rb
  pba_addr : ixAddr pba_b = pInfo.blk
  m_elim : Heap F
  m_rlvls : Heap F
  m_bfb : Heap F
  m_peers : Heap F
  m_cbp_in : Heap F
  m_cbp_out : Heap F
  m_pop : Heap F
  m_cmp : Heap F
  m_next : Heap F
  x_s_next : SourceValue F
  ext_h_next : Heap.Extends h m_next
  ext_h_brt_out : Heap.Extends h m_brt_out
  ext_brt_out_cbp : Heap.Extends m_brt_out m_cbp_in
  helim_brt : RepKLevel m_brt_in (elimLevel off) x_elim
  hflat_brt : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m_brt_in flat x_flat
  hfop_brt : RepList fieldListEnum RepNatField m_brt_in fop x_fop
  hty_brt_out : TmOExact (Core.keyOf t) m_brt_out ty x_ty
  hrules_pop : RecRulesRep t E₀ (Held R) rb crb rs rc.lvls.toNat (mutsRoot rs k) m_pop 0
    rc.rules.toList x_rules
  hty_pop : TmOExact (Core.keyOf t) m_pop ty x_ty
  helim_pop : RepKLevel m_pop (elimLevel off) x_elim
  hflat_bfb : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m_bfb flat x_flat
  rrba_bfb : Bytes.RepAddressRef addrTy m_bfb rba_b x_rba
  rpba_cbp_out : Bytes.RepAddressRef addrTy m_cbp_out pba_b x_pba
  hocc_cbp_out : RepKLevelList m_cbp_out ek.levels x_occ_us
  hsp_cbp_out : RepList kexprListEnum (TmOExact (Core.keyOf t)) m_cbp_out ek.params x_sp
  hflat_cbp_in : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m_cbp_in flat x_flat
  hflat_cbp_out : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m_cbp_out flat x_flat
  hfop_cbp_out : RepList fieldListEnum RepNatField m_cbp_out fop x_fop
  helim_cbp_out : RepKLevel m_cbp_out (elimLevel off) x_elim
  ext_rlvls_cbp_out : Heap.Extends m_rlvls m_cbp_out
  ext_peers_cbp_out : Heap.Extends m_peers m_cbp_out
  ev_rlvls : ∃ cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelCheck::build_rec_lvls_list" [.field (rc.lvls.toNat : F), .field 0]
      m_elim x_rlvls m_rlvls cs
  ev_peers : ∃ cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rba, x_r] m_bfb x_peers m_peers cs
  ev_brt : ∃ cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelCheck::build_rec_type"
      [xrc, x_pty, x_pnl, .field (np : F), .field (pInfo.ni : F), x_elim, .field (off : F),
        x_flat, x_fop, .field (k : F)] m_brt_in x_cty m_brt_out cs
  sg_form : ∃ m_f cs_f, (∀ cl ∈ cs_f, cl ∈ calls) ∧
    Obs.«KernelCheck::canonical_rules_at_pos».Seg_dckjugtb x_cty (auxVal ek.aux) x_sp x_occ_us
      xrc x_flat (.field (k : F)) (.field (pInfo.nctors : F)) x_pba (.field (pInfo.idx : F))
      (.field (np : F)) (.field (rc.motives.toNat : F)) (.field (rc.minors.toNat : F))
      x_rlvls x_peers x_fop x_rules x_ty x_pty x_pnl (.field (pInfo.ni : F)) x_elim
      (.field (off : F)) xform m_brt_out x_form2 m_f cs_f
  ev_cbp : ∃ cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelCheck::ctors_before_pos" [x_flat, .field (k : F), .field 0]
      m_cbp_in x_cbk m_cbp_out cs
  ev_pop : ∃ cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelCheck::populate_rules"
      [xrc, .field (pInfo.nctors : F), x_cbk, x_pba, .field (pInfo.idx : F),
        .field (np : F), .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
        x_occ_us, x_rlvls, x_flat, x_peers, x_fop, auxVal ek.aux, x_sp, .field 0, x_elim]
      m_cbp_out x_can m_pop cs
  ev_cmp : ∃ r_c cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelCheck::compare_rules"
      [x_rules, x_can, .field (np : F), .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
        x_pba, .field (pInfo.idx : F), .field (pInfo.nctors : F), .field 0, x_elim, x_ty, x_cbk]
      m_pop r_c m_cmp cs
  ev_next : ∃ cs, (∀ cl ∈ cs, cl ∈ calls) ∧
    ObsFn W "KernelModeled::check_recs"
      [xrc, xta, xrest, xmrest, xsrc, xdst, xaset, x_s_next, .field (rs.size : F),
        .field ((k + 1 : Nat) : F), .field (np : F), .field (off : F), .field (bnl : F),
        xfam, x_form2] m_next r_out h' cs

private theorem peelForalls_of_heapForalls_tmOExact {κ : _root_.Address → KKey} :
    ∀ (n : Nat) {h : Heap F} {e : KExpr} {p q : SourceValue F},
      HeapForalls h n p q → TmOExact κ h e p →
      ∃ b, peelForalls n e = some b ∧ TmOExact κ h b q := by
  intro n
  induction n with
  | zero =>
    intro h e p q hf htm
    cases hf; exact ⟨e, rfl, htm⟩
  | succ m ih =>
    intro h e p q hf htm
    cases hf with
    | succ ld hf_rest =>
      obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load htm ld
      exact ih hf_rest hB

private theorem tmOExact_not_forall_of_heapAppBVar {κ : _root_.Address → KKey} {h : Heap F}
    {e : KExpr} {p : SourceValue F} {idx : F}
    (htm : TmOExact κ h e p) (hb : HeapAppBVar h p idx) :
    ∀ a b m, e ≠ .forallE a b m := by
  cases hb with
  | bvar ld =>
    obtain ⟨_, _, _, rfl⟩ := TmOExact.bvar_of_load htm ld
    intro _ _ _ he; cases he
  | app ld _ =>
    obtain ⟨_, _, rfl, -, -⟩ := TmOExact.app_of_load htm ld
    intro _ _ _ he; cases he

/-- Unpacks one `.Cons` step of `check_recs` completely (shared by Steps A, B, C1, C2). -/
private theorem check_recs_step_unpack {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {k np off bnl : Nat} {rc : Ixon.Recursor} {a_k : Bytes.Address} {rest : List Bytes.Address}
    {xrc xta xrecs xmodels xsrc xdst xaset xs xfam xform r_out : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    (hRec : FamRecRecord E₀ rb crb rs)
    (hSrb : Held R rb) (hrs_lt : rs.size < 2 ^ 39)
    (hnp_lt : np < 72057594037927936) (hoff : off ≤ 1) (hbnl_lt : bnl < 4294967296)
    (hk_lt : k < rs.size) (hk : rs[k]? = some (.recr rc))
    (ha_k : ixAddr a_k = memberAddr rb k (.recr rc))
    (hrecs : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (a_k :: rest) xrecs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (ev : ObsFn W "KernelModeled::check_recs"
      [xrc, xta, xrecs, xmodels, xsrc, xdst, xaset, xs, .field (rs.size : F), .field (k : F),
        .field (np : F), .field (off : F), .field (bnl : F), xfam, xform] h r_out h' cs) :
    ∃ (xrest xmrest : SourceValue F),
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h rest xrest ∧
      Nonempty (CheckRecsStep calls t E₀ R rb crb rs k np off bnl rc
        xrc xta xrest xmrest xsrc xdst xaset xfam xform r_out h h') := by
  have sub : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs) → ∀ cl ∈ cs', cl ∈ calls :=
    fun hs cl hcl' => hsub cl (hs cl hcl')
  match Obs.«KernelModeled::check_recs».obs ev with
  | .Nil (ld12 := ld) .. => cases IxVM.Refinement.Core.RepList.nil_of_load hrecs ld
  | .Cons (x_r := xr) (x_rest := xrest) (x_rm := xrm) (x_mrest := xmrest)
      (m67 := m_ci) (p74 := p_ci) (cs80 := cs_ci)
      (x_nl := xnl) (x_ty := xty) (x_rnp := xrnp) (x_ni := xni) (x_nmot := xnmot)
      (x_nmin := xnmin) (x_rules := xrules) (x_kf := xkf) (x_r_uns := xruns)
      (w107 := w107) (w108 := w108)
      (m288 := m288) (cs296 := cs296) (m335 := m335) (cs343 := cs343) (m349 := m349)
      (cs357 := cs357) (m391 := m391) (cs401 := cs401) (m473 := m473) (cs483 := cs483)
      (m511 := m511) (cs521 := cs521) (m561 := m561) (cs569 := cs569)
      (m_oajaqiwd := m_oa) (m_obmhbjvc := m_ob) (cs_hmmloamm := cs_pc1)
      (m_shkxqcak := m_sh) (cs_fsttxebm := cs_ren) (m_raxeqbbt := m_ra)
      (m_yfwcpmwj := m_yf) (cs_dsvkbvxt := cs_pc2)
      (m_cjjqtxxk := m_cj) (cs_gbkzevef := cs_spe)
      (m_tsdchhaz := m_ts) (cs_sblvzaks := cs_mp)
      (m_akkqvxxx := m_ak) (cs_kxcowfqz := cs_lp)
      (m627 := m627) (m596 := m596) (cs606 := cs606)
      (m640 := m640) (cs650 := cs650) (m669 := m669) (cs679 := cs679)
      (v697 := xr_pa) (m698 := m698) (cs708 := cs708)
      (v_lawpuqwl := xform2) (m_pzqbkmwo := m_can) (cs_fcqxjgjw := cs_can)
      (v_orhmbogm := vp_ci) (m_pipdqnib := m_pci) (p_luqvxdfx := pp_ci) (cs_vkeoeyff := cs_pci)
      (m838 := m838) (cs848 := cs848) (v891 := xs_next) (m892 := m_next) (cs902 := cs902)
      (cs1014 := cs_next)
      (ld12 := ld_recs) (ev82 := ev_ci) (ld76 := ld_ci)
      (heq245 := heq_rnp) (heq273 := heq_nmot)
      (ev298 := ev298) (ev359 := ev359) (ev345 := ev345)
      (op451 := op451) (op443 := op443) (op435 := op435) (op427 := op427) (op469 := op469)
      (ev403 := ev_mot) (ev485 := ev_car) (ev523 := ev523) (ev571 := ev571)
      (hm_odcsfbbr := hm_oa) (ev_uprevpxl := ev_pc1) (ev_svgicqcr := ev_ren)
      (hm_owdmgqhw := hm_ra) (ev_oqkxxxxs := ev_pc2) (ev_eejlfykm := ev_spe)
      (op_eindxttr := op_mp1) (op_smkbhtsz := op_mp2) (ev_uoyvrvop := ev_mp)
      (ev_akrqpecc := ev_lp) (hm635 := hm627) (ev608 := ev608) (ev652 := ev652)
      (ev681 := ev681) (ev710 := ev_pa) (ev_uoummlhs := ev_pci) (ld_memczquv := ld_pci)
      (ev_tjosvhyt := ev_can) (ev850 := ev850) (ev904 := ev904)
      (op1107 := op_k1) (ev1016 := ev_next) (hc1137 := hc_cr) .. =>
    obtain ⟨a_k', rest', hlist, ra_k, hrest_rep⟩ := IxVM.Refinement.Core.RepList.cons_of_load hrecs ld_recs
    injection hlist with h1 h2; subst h1 h2
    -- Heap extensions along check_recs body
    have ext_ci_335 : Heap.Extends m_ci m335 :=
      ev298.heap_extends.trans (ev359.heap_extends.trans ev345.heap_extends)
    have ext_335_391 : Heap.Extends m335 m391 := ev_mot.heap_extends
    have ext_391_cj : Heap.Extends m391 m_cj := by
      have e1 : Heap.Extends m561 m_oa := by rw [hm_oa]; exact Heap.Extends.snoc _ _
      have e2 : Heap.Extends m_sh m_ra := by rw [hm_ra]; exact Heap.Extends.snoc _ _
      exact ev_car.heap_extends.trans <| ev523.heap_extends.trans <| ev571.heap_extends.trans <|
        e1.trans <| ev_pc1.heap_extends.trans <| ev_ren.heap_extends.trans <|
        e2.trans <| ev_pc2.heap_extends.trans ev_spe.heap_extends
    have ext_cj_669 : Heap.Extends m_cj m669 := by
      have e3 : Heap.Extends m_ak m627 := by rw [hm627]; exact Heap.Extends.snoc _ _
      exact ev_mp.heap_extends.trans <| ev_lp.heap_extends.trans <| e3.trans <|
        ev608.heap_extends.trans <| ev652.heap_extends.trans ev681.heap_extends
    have ext_ci_cj : Heap.Extends m_ci m_cj :=
      ext_ci_335.trans (ext_335_391.trans ext_391_cj)
    have ext_ci_669 : Heap.Extends m_ci m669 := ext_ci_cj.trans ext_cj_669
    have ext_h_next : Heap.Extends h m_next :=
      ev_ci.heap_extends.trans <| ext_ci_669.trans <| ev_pa.heap_extends.trans <|
        ev_pci.heap_extends.trans <| ev_can.heap_extends.trans <|
        ev850.heap_extends.trans ev904.heap_extends
    -- Load recursor k via recrLoad_ofStore + recrLoad_rawConvExpr
    have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls := sub (fun cl hcl' => mem_of_eq hc_cr (by call_mem))
    obtain ⟨ty, tyPtr, rulesPtr, blkPtr, rba_b, hci_shape, hnl_lt, hrnp_lt, hni_lt, hnmot_lt,
      hnmin_lt, hk56, hloaded_ty, htm_ty, htyIn, hrba_addr, rrba, hrules_ci⟩ :=
      recrLoad_ofStore ht hwf hS hH hbd hRagree hcl hlv hsub_ci hSrb hRec.record hRec.muts hk
        ha_k ra_k ev_ci ld_ci
    obtain ⟨blobs, hraw_ty⟩ :=
      recrLoad_rawConvExpr hS hH hbd hRagree hcl hsub_ci hSrb hRec.record hRec.muts hk
        ha_k ra_k ev_ci ld_ci hci_shape
    simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hci_shape
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, hblk_eq, rfl⟩ := hci_shape
    subst w107
    have hrnp_eq : rc.params.toNat = np := by
      have h1 := congrArg ZMod.val (Value.field.inj heq_rnp)
      rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1
    have hnmot_eq : rc.motives.toNat = rs.size := by
      have h1 := congrArg ZMod.val (Value.field.inj heq_nmot)
      rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1
    -- rec_to_parent_addr + rec_major_pins_ni_eq
    have hsum_lt : rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat + 1 <
        9223372036854775808 := by omega
    obtain ⟨d_pa, pa_b, us_pa, hd_pa, hfn_pa, rpa_b, -⟩ :=
      rec_to_parent_addr_spec (κ := Core.keyOf t) (by omega) (htm_ty.mono ext_ci_669) ev_pa
    obtain rfl := binop_add_nat op_mp1
    obtain rfl := binop_add_nat op_mp2
    obtain ⟨pInfo, d, us, hpInfo_at, hni_eq, hd, hfn, hpnp_le, hSpa⟩ :=
      rec_major_pins_ni_eq ht hwf hS hH hbd hRagree hcl hlv (by omega)
        (sub fun cl hcl' => mem_of_eq hc_cr (by call_mem))
        (htm_ty.mono ext_ci_cj) htyIn ext_cj_669 ev_mp ev_pa rpa_b
    -- Load parent inductive via indAnswers_ofStore
    have hsub_pci : ∀ cl ∈ cs_pci, cl ∈ calls := sub (fun cl hcl' => mem_of_eq hc_cr (by call_mem))
    obtain ⟨hInd_p, hOther_p⟩ := indAnswers_ofStore ht hwf hS hH hbd hRagree hcl hlv
      hsub_pci hSpa rpa_b ev_pci ld_pci
    -- Check parent_ci is .Induct, then unpack check_recursor_canonical_at
    have hp_is_ind : ∃ (x_pnl x_pty x_pnp x_pni x_nct w_p x_pba x_pidx : SourceValue F),
        vp_ci = .construct kciEnum "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nct, w_p, x_pba, x_pidx] := by
      by_cases h1 : ∀ vs : List (SourceValue F), vs.length = 8 →
          vp_ci ≠ .construct kciEnum "Induct" vs
      · have hnone := hOther_p h1
        change indDataAt t E₀ (ixAddr pa_b) = some none at hnone
        rw [hpInfo_at] at hnone; cases hnone
      · push Not at h1
        obtain ⟨vs, hlen, hvs⟩ := h1
        rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | ⟨v6, _ | ⟨v7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
        all_goals try (simp at hlen)
        exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, hvs⟩
    obtain ⟨x_pnl, x_pty, x_pnp, x_pni, x_nct, w_p, x_pba, x_pidx, hvp_ind⟩ := hp_is_ind
    obtain ⟨pInfo', pba_b, hpInfo'_at, hpnl_lt, hpnp_lt, hpni_lt, hpnct_lt, hpidx_lt,
      hxpnl_eq, -, -, -, hx_pnp_eq, hx_pni_eq, hx_nct_eq, hpba_addr, rpba_pci, hx_pidx_eq⟩ :=
      hInd_p x_pnl x_pty x_pnp x_pni x_nct w_p x_pba x_pidx hvp_ind
    have hpInfo_eq : pInfo' = pInfo := Option.some.inj (Option.some.inj (hpInfo'_at.symm.trans hpInfo_at))
    subst pInfo'
    have hpInfo_blk_held : Held R pInfo.blk := by
      obtain ⟨-, ca_p, pr_p, _, _, _, hca_p, hci_p, -, -, -, -, -, -, -, hblk_p, -⟩ :=
        indInfoAt_of_indDataAt hpInfo_at
      have hca_R : recordOf R (ixAddr pa_b) = some ca_p := by
        obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp hSpa
        have := hRagree _ _ _ hcR hca_p; subst this; exact hcR
      have hown := (hcl.1 (ixAddr pa_b) ca_p hca_R).1
      simpa [Ix.Cert.ownerOf, hci_p, hblk_p] using hown
    have hpb_muts : ∃ cbP msP, recordOf E₀ pInfo.blk = some cbP ∧ cbP.info = .muts msP := by
      obtain ⟨-, _, pr_p, cbP, msP, _, -, -, hcbP, hmsP, -, -, -, -, -, hblk_p, -⟩ :=
        indInfoAt_of_indDataAt hpInfo_at
      rw [← hblk_p] at hcbP
      exact ⟨cbP, msP, hcbP, hmsP⟩
    obtain ⟨cbP, msP, hcbP, hmsP⟩ := hpb_muts
    -- Unify the two Induct arms of check_recursor_canonical_at
    have hcan_unify : ∃ (v_elim : SourceValue F) (m_elim : Heap F)
        (v_rlvls : SourceValue F) (m_rlvls : Heap F) (cs_rlvls : List (Call F))
        (v_flat : SourceValue F) (m_bfb : Heap F) (cs_bfb : List (Call F))
        (v_peers : SourceValue F) (m_peers : Heap F) (cs_peers : List (Call F))
        (v_fop : SourceValue F) (m_fop : Heap F) (cs_fop : List (Call F))
        (x_self_pos : SourceValue F) (m_c_in : Heap F) (cs_c_in : List (Call F)),
        rc.lvls.toNat = bnl + off ∧
        Heap.Extends m_pci m_elim ∧
        RepKLevel m_elim (elimLevel off) v_elim ∧
        (∀ cl ∈ cs_rlvls, cl ∈ calls) ∧
        ObsFn W "KernelCheck::build_rec_lvls_list" [.field (rc.lvls.toNat : F), .field 0]
          m_elim v_rlvls m_rlvls cs_rlvls ∧
        (∀ cl ∈ cs_bfb, cl ∈ calls) ∧
        ObsFn W "KernelCheck::build_flat_block" [blkPtr, x_pba, .field (off : F)]
          m_rlvls v_flat m_bfb cs_bfb ∧
        (∀ cl ∈ cs_peers, cl ∈ calls) ∧
        ObsFn W "KernelCheck::build_peer_recs" [v_flat, blkPtr, xr] m_bfb v_peers m_peers cs_peers ∧
        (∀ cl ∈ cs_fop, cl ∈ calls) ∧
        ObsFn W "KernelCheck::build_flat_own_params" [v_flat] m_peers v_fop m_fop cs_fop ∧
        Heap.Extends m_fop m_c_in ∧
        (∀ (es : List FlatEntry),
          RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m_bfb es v_flat →
          ∃ (sp : Nat) (e_s : FlatEntry), es[sp]? = some e_s ∧ e_s.addr = ixAddr pa_b ∧
            x_self_pos = .field (sp : F)) ∧
        (∀ cl ∈ cs_c_in, cl ∈ calls) ∧
        ObsFn W "KernelCheck::canonical_rules_at_pos"
          [xrc, v_flat, x_self_pos, x_nct, x_pba, x_pidx, .field (rc.params.toNat : F),
            .field (rc.motives.toNat : F), .field (rc.minors.toNat : F), v_rlvls, v_peers, v_fop,
            xrules, xty, x_pty, x_pnl, x_pni, v_elim, .field (off : F), xform]
          m_c_in xform2 m_can cs_c_in := by
      have extract_seg1 : ∀ {ve me cs_s},
          Obs.«KernelCheck::check_recursor_canonical_at».Seg1 x_pnl x_pty x_pnp x_pni x_nct x_pba
            x_pidx (.field (rc.lvls.toNat : F)) xty (.field (rc.params.toNat : F))
            (.field (rc.indices.toNat : F)) (.field (rc.motives.toNat : F))
            (.field (rc.minors.toNat : F)) xrules xkf xruns blkPtr (.field (k : F)) xrc
            (.construct kciEnum "Rec" [.field (rc.lvls.toNat : F), xty,
              .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
              .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
              xrules, xkf, xruns, blkPtr, .field (k : F)])
            xr vp_ci xr_pa (.field (off : F)) (.field (bnl : F)) xform m_pci ve me cs_s →
          Heap.Extends m_pci me ∧ RepKLevel me (elimLevel off) ve := by
        intro ve me cs_s sg1
        cases sg1 with
        | n1 hv179 he184 hm183 _ =>
          have hoff1 : off = 1 := by
            have := congrArg ZMod.val (Value.field.inj hv179)
            rw [fval_natCast (by omega)] at this; exact this
          subst hoff1 he184 hm183
          refine ⟨Heap.Extends.snoc _ _, ?_⟩
          exact RepKLevel.param (by decide) (by simp)
        | other hne196 he204 hm203 _ =>
          have hoff0 : off = 0 := by
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hoff with h0 | h1
            · exact h0
            · subst h1; exact (hne196 rfl).elim
          subst hoff0 he204 hm203
          refine ⟨Heap.Extends.snoc _ _, ?_⟩
          exact RepKLevel.zero (by simp)
      have extract_seg23 : ∀ {v345 v323 v285 v247 v218 v209 m346 v477 m478 cs480 vsou myr csjq},
          Obs.«KernelCheck::check_recursor_canonical_at».Seg2 v345 v323 v285 v247 v218 v209
            x_pnl x_pty x_pnp x_pni x_nct x_pba x_pidx (.field (rc.lvls.toNat : F)) xty
            (.field (rc.params.toNat : F)) (.field (rc.indices.toNat : F))
            (.field (rc.motives.toNat : F)) (.field (rc.minors.toNat : F))
            xrules xkf xruns blkPtr (.field (k : F)) xrc
            (.construct kciEnum "Rec" [.field (rc.lvls.toNat : F), xty,
              .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
              .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
              xrules, xkf, xruns, blkPtr, .field (k : F)])
            xr vp_ci xr_pa (.field (off : F)) (.field (bnl : F)) xform m346 v477 m478 cs480 →
          Obs.«KernelCheck::check_recursor_canonical_at».Seg_aowwkmcx v477 v345 v323 v285 v247
            v218 v209 x_pnl x_pty x_pnp x_pni x_nct x_pba x_pidx (.field (rc.lvls.toNat : F)) xty
            (.field (rc.params.toNat : F)) (.field (rc.indices.toNat : F))
            (.field (rc.motives.toNat : F)) (.field (rc.minors.toNat : F))
            xrules xkf xruns blkPtr (.field (k : F)) xrc
            (.construct kciEnum "Rec" [.field (rc.lvls.toNat : F), xty,
              .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
              .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
              xrules, xkf, xruns, blkPtr, .field (k : F)])
            xr vp_ci xr_pa (.field (off : F)) (.field (bnl : F)) xform m478 vsou myr csjq →
          Heap.Extends m346 myr := by
        intro _ _ _ _ _ _ m346 _ m478 _ _ myr _ sg2 sg3
        have e2 : Heap.Extends m346 m478 := by
          cases sg2 with
          | n1 _ _ ev446 _ => exact ev446.heap_extends
          | other _ _ hm _ => rw [hm]; exact Heap.Extends.snoc _ _
        have e3 : Heap.Extends m478 myr := by
          cases sg3 with
          | n1 _ _ evj _ => exact evj.heap_extends
          | other _ _ hm _ => rw [hm]; exact Heap.Extends.snoc _ _
        exact e2.trans e3
      match Obs.«KernelCheck::check_recursor_canonical_at».obs ev_can with
      | .other (hne944 := hne) .. => exact (hne _ rfl hvp_ind).elim
      | .Induct_n1_bind (hv15 := hv15) (hv86 := hv86) (op162 := op162) (heq165 := heq165)
          (sg217 := sg1) (ev231 := ev_rl) (ev260 := ev_bfb) (ev298 := ev_pr)
          (ev336 := ev_fop) (ev374 := ev_m1) (ev388 := ev_m2) (ev410 := ev_aeq)
          (sg485 := sg2) (sg_berdancy := sg3) (ev499 := ev_fpk) (ev572 := ev_cap)
          (hc725 := hc_can) .. =>
        simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv15
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv15
        rw [hvp_ind] at hv86
        simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv86
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv86
        obtain rfl := binop_add_nat op162
        have hlvls_eq : rc.lvls.toNat = bnl + off := by
          have h1 := congrArg ZMod.val (Value.field.inj heq165)
          rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1
        obtain ⟨ext_s1, helim⟩ := extract_seg1 sg1
        have ext_fop_yr : Heap.Extends _ _ :=
          ev_m1.heap_extends.trans <| ev_m2.heap_extends.trans <|
            ev_aeq.heap_extends.trans (extract_seg23 sg2 sg3)
        have ext_bfb_yr : Heap.Extends _ _ :=
          ev_pr.heap_extends.trans (ev_fop.heap_extends.trans ext_fop_yr)
        have hsub_can : ∀ cl ∈ cs_can, cl ∈ calls := sub (fun cl hcl' => mem_of_eq hc_cr (by call_mem))
        refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlvls_eq, ext_s1, helim,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_rl,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_bfb,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_pr,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_fop,
          ext_fop_yr.trans ev_fpk.heap_extends, ?_,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_cap⟩
        intro es hes_bfb
        have ext_pci_yr := ext_s1.trans <| ev_rl.heap_extends.trans <| ev_bfb.heap_extends.trans ext_bfb_yr
        obtain ⟨sp, e_s, hsp, ha_s, hxsp⟩ := flat_find_pos_kind_addr es 0
          (flatList_mono ext_bfb_yr hes_bfb)
          (Bytes.repAddressRef_heapMono₂ addrTy (ev_pci.heap_extends.trans ext_pci_yr) rpa_b)
          (by simpa using ev_fpk)
        exact ⟨sp, e_s, hsp, ha_s, by simpa using hxsp⟩
      | .Induct_other (hv15 := hv15) (hv86 := hv86) (op162 := op162) (heq165 := heq165)
          (sg217 := sg1) (ev231 := ev_rl) (ev260 := ev_bfb) (ev298 := ev_pr)
          (ev336 := ev_fop) (ev374 := ev_m1) (ev388 := ev_m2) (ev410 := ev_aeq)
          (sg485 := sg2) (sg_berdancy := sg3) (ev499 := ev_fpk) (ev743 := ev_fp)
          (ev790 := ev_cap) (hc943 := hc_can) .. =>
        simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv15
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv15
        rw [hvp_ind] at hv86
        simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv86
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv86
        obtain rfl := binop_add_nat op162
        have hlvls_eq : rc.lvls.toNat = bnl + off := by
          have h1 := congrArg ZMod.val (Value.field.inj heq165)
          rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1
        obtain ⟨ext_s1, helim⟩ := extract_seg1 sg1
        have ext_fop_yr : Heap.Extends _ _ :=
          ev_m1.heap_extends.trans <| ev_m2.heap_extends.trans <|
            ev_aeq.heap_extends.trans (extract_seg23 sg2 sg3)
        have ext_fop_487 : Heap.Extends _ _ := ext_fop_yr.trans ev_fpk.heap_extends
        have ext_bfb_487 : Heap.Extends _ _ :=
          ev_pr.heap_extends.trans (ev_fop.heap_extends.trans ext_fop_487)
        have hsub_can : ∀ cl ∈ cs_can, cl ∈ calls := sub (fun cl hcl' => mem_of_eq hc_cr (by call_mem))
        refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlvls_eq, ext_s1, helim,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_rl,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_bfb,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_pr,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_fop,
          ext_fop_487.trans ev_fp.heap_extends, ?_,
          fun cl hcl' => hsub_can cl (mem_of_eq hc_can (by call_mem)), ev_cap⟩
        intro es hes_bfb
        have ext_pci_487 := ext_s1.trans <| ev_rl.heap_extends.trans <| ev_bfb.heap_extends.trans ext_bfb_487
        obtain ⟨-, hfp⟩ := flat_find_pos_spec es 0 (flatList_mono ext_bfb_487 hes_bfb)
          (Bytes.repAddressRef_heapMono₂ addrTy (ev_pci.heap_extends.trans ext_pci_487) rpa_b)
          (by simpa using ev_fp)
        rcases hfp with ⟨sp, e_s, hsp, ha_s, htup⟩ | ⟨-, htup⟩
        · injection htup with hl; injection hl with _ hl; injection hl with hxsp _
          exact ⟨sp, e_s, hsp, ha_s, by simpa using hxsp⟩
        · injection htup with hl; injection hl with h1 _
          exact absurd (Value.field.inj h1) one_ne_zero
    obtain ⟨v_elim, m_elim, v_rlvls, m_rlvls, cs_rlvls, v_flat, m_bfb, cs_bfb,
      v_peers, m_peers, cs_peers, v_fop, m_fop, cs_fop, x_self_pos, m_c_in, cs_c_in,
      hlvls_eq, ext_pci_elim, helim, hsub_rlvls, ev_rlvls, hsub_bfb, ev_bfb,
      hsub_peers, ev_peers, hsub_fop, ev_fop, ext_fop_cin, hfind_sp, hsub_cap, ev_cap⟩ := hcan_unify
    -- Run build_flat_block_spec
    have ext_ci_rlvls : Heap.Extends m_ci m_rlvls :=
      ext_ci_669.trans <| ev_pa.heap_extends.trans <| ev_pci.heap_extends.trans <|
        ext_pci_elim.trans ev_rlvls.heap_extends
    have ext_pci_rlvls : Heap.Extends m_pci m_rlvls := ext_pci_elim.trans ev_rlvls.heap_extends
    obtain ⟨prim, cprim, msp, os, flat, hfrp, hSprim, hcprim, hmsp, horig, haux, hfilt,
      hos_props, hflat_bfb, hflat_held⟩ :=
      build_flat_block_spec ht hwf hS hH hbd hRagree hcl hlv hoff hsub_bfb
        (hrba_addr.symm ▸ hSrb) (hrba_addr.symm ▸ hRec.record) hRec.muts
        (hpba_addr.symm ▸ hpInfo_blk_held) (hpba_addr.symm ▸ hcbP) hmsP
        (Bytes.repAddressRef_heapMono₂ addrTy ext_ci_rlvls rrba)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_pci_rlvls rpba_pci) ev_bfb
    -- Lift flat entries from indInfoAt to indDataAt via build_flat_own_params
    have hflat_indInfo : ∀ e ∈ flat, Held R e.addr ∧ ∃ info, indInfoAt E₀ e.addr = some (some info) :=
      fun e he => ⟨(hflat_held e he).1,
        buildFlatAuxStep_all_indInfoAt rs.toList 0 os flat haux
          (originals_all_indInfoAt _ os horig) e he⟩
    have hflat_indData := flat_entries_indDataAt_of_build_flat_own_params ht hwf hS hH hbd hRagree
      hcl hlv flat hsub_fop (flatList_mono ev_peers.heap_extends hflat_bfb) hflat_indInfo ev_fop
    obtain ⟨fop, hfop_eq, hfop_len, hfop_lt, hfop_fop⟩ :=
      build_flat_own_params_spec ht hwf hS hH hbd hRagree hcl hlv flat hsub_fop
        (flatList_mono ev_peers.heap_extends hflat_bfb) hflat_indData ev_fop
    obtain ⟨sp, e_s, hsp_get, ha_s, hx_sp_eq⟩ := hfind_sp flat hflat_bfb
    subst hx_sp_eq
    have hsp_lt : sp < flat.length := (List.getElem?_eq_some_iff.mp hsp_get).1
    -- Unpack canonical_rules_at_pos
    match Obs.«KernelCheck::canonical_rules_at_pos».obs ev_cap with
    | .run (m2 := m_brt_in) (cs13 := cs_fma) (w38 := w38) (x_is_aux := xis_aux)
        (x_spec_params := x_sp_p) (x_occ_us := x_occ) (v59 := x_cty) (m60 := m_brt_out)
        (cs70 := cs_brt) (v_htewcxgp := xf2) (m_uszksxrg := m_f) (cs_vcbgkffy := cs_f)
        (v223 := v_nmot) (m224 := m224) (cs234 := cs234) (v245 := v_nmin) (m246 := m_cbp_in)
        (cs256 := cs256) (v259 := v_mins) (m261 := m261) (cs269 := cs269)
        (v384 := x_cbk) (m385 := m_cbp_out) (cs395 := cs_cbp)
        (v421 := x_can) (m422 := m_pop) (cs432 := cs_pop)
        (v_ubccbken := r_cmp) (m_xvqyrbqu := m_cmp) (cs_qxhjvbns := cs_cmp)
        (ev15 := ev_fma) (ev72 := ev_brt) (sg_xtajopni := sg_f) (ev236 := ev_flen)
        (ev271 := ev_mins) (ev258 := ev_mlen) (heq355 := heq_nmot2) (heq383 := heq_nmin2)
        (ev397 := ev_cbp) (ev434 := ev_pop) (ev_fswvniux := ev_cmp)
        (he_kcelgdaj := hr_cap) (he_uupfqxod := hh_cap) (hc671 := hc_cap) .. =>
      subst hr_cap hh_cap
      have ext_bfb_cin : Heap.Extends m_bfb m_c_in :=
        ev_peers.heap_extends.trans (ev_fop.heap_extends.trans ext_fop_cin)
      have ext_elim_cin : Heap.Extends m_elim m_c_in :=
        ev_rlvls.heap_extends.trans (ev_bfb.heap_extends.trans ext_bfb_cin)
      have ext_ci_cin : Heap.Extends m_ci m_c_in :=
        ext_ci_rlvls.trans (ev_bfb.heap_extends.trans ext_bfb_cin)
      have hsub_cap' : ∀ {cs' : List (Call F)}, (∀ cl ∈ cs', cl ∈ cs_c_in) → ∀ cl ∈ cs', cl ∈ calls :=
        fun hs cl hcl' => hsub_cap cl (hs cl hcl')
      -- flat_length = rs.size (from ev_flen + heq_nmot2)
      have ext_brt_f : Heap.Extends m_brt_out m_f := by
        cases sg_f with
        | n1_n1 _ _ evk _ _ hh _ => rw [hh]; exact evk.heap_extends
        | n1_other_n1 _ _ _ _ evk _ evw _ hh _ => rw [hh]; exact evk.heap_extends.trans evw.heap_extends
        | n1_other_other _ _ _ _ _ evk _ evw _ _ _ hh _ => rw [hh]; exact evk.heap_extends.trans evw.heap_extends
        | other _ _ _ _ _ _ _ _ _ _ _ _ _ evk _ evrg _ evw _ _ eviz _ _ hh _ =>
          rw [hh]; exact evk.heap_extends.trans (evrg.heap_extends.trans (evw.heap_extends.trans eviz.heap_extends))
      have ext_cin_f : Heap.Extends m_c_in m_f :=
        ev_fma.heap_extends.trans (ev_brt.heap_extends.trans ext_brt_f)
      obtain ⟨hv_nmot, hm224⟩ := flat_length_spec ev_flen
        (flatList_mono (ext_bfb_cin.trans ext_cin_f) hflat_bfb)
      subst hm224
      have hflat_lt : flat.length < 2 ^ 39 := by
        have hmem_len :
            (⟨Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>»,
              [v_flat], m224⟩ : Call F) ∈ calls :=
          hsub_cap _ (mem_of_eq hc_cap (by call_mem))
        exact RomBound.bounded_length_lt hbd hmem_len List.mem_cons_self
          (flatList_mono (ext_bfb_cin.trans ext_cin_f) hflat_bfb)
      rw [hv_nmot] at heq_nmot2
      have hflat_len : flat.length = rs.size := by
        have h1 := congrArg ZMod.val (Value.field.inj heq_nmot2)
        rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; omega
      -- flat_member_at gives xis_aux, x_sp_p, x_occ
      obtain ⟨hm_brt, e_s', he_s', hrep_es⟩ :=
        flat_member_at_spec flat sp hsp_lt (by omega) ev_fma (flatList_mono ext_bfb_cin hflat_bfb)
      subst hm_brt
      have he_s_eq : e_s' = e_s := Option.some.inj (he_s'.symm.trans hsp_get); subst e_s'
      obtain ⟨_, _, _, _, htup_es, -, -, hsp_rep, hocc_rep⟩ := hrep_es
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_es
      obtain ⟨-, haux_eq, hspp_eq, hocc_eq⟩ := htup_es
      subst haux_eq hspp_eq hocc_eq
      -- build_rec_type_heap_shape (at sp)
      have ev_brt' : ObsFn W "KernelCheck::build_rec_type"
          [xrc, x_pty, x_pnl, .field (rc.params.toNat : F), .field (pInfo.ni : F), v_elim,
            .field (off : F), v_flat, v_fop, .field (sp : F)] m_brt_in x_cty m_brt_out cs_brt := by
        rwa [hx_pni_eq] at ev_brt
      obtain ⟨lenP, lenI, tot, xconcl, hlenP_le, hlenI_le, htot_lt, htot_eq,
        hforalls_cty, hconcl_bv, hmots_car, hmaj_car⟩ :=
        build_rec_type_heap_shape ht hwf hS hH hbd hRagree hcl hlv
          (by omega) (by omega) (by omega) hsp_lt hsp_get
          (hsub_cap' fun cl hcl' => mem_of_eq hc_cap (by call_mem))
          (flatList_mono ext_bfb_cin hflat_bfb) hflat_indData ev_brt'
      -- tot = rc.minors.toNat from ev_mins + ev_mlen + heq_nmin2
      obtain ⟨tot', htot'_eq, hmins_u⟩ :
          ∃ tot' : Nat, flatTotalCtors (ReconView.ofStore t E₀) flat = some tot' ∧
            RepList kexprListEnum (fun _ (_ : Unit) _ => True) m261 (List.replicate tot' ()) v_mins := by
        match Obs.«KernelCheck::build_all_minors».obs ev_mins with
        | .run (ev6 := evmw) (hc85 := hc_m) .. =>
          exact build_all_minors_walk_rawLen ht hwf hS hH hbd hRagree hcl hlv flat
            (hsub_cap' fun cl hcl' => mem_of_eq hc_cap (by
              have hm1 : cl ∈ cs269 := mem_of_eq hc_m (by call_mem)
              call_mem))
            (flatList_mono (ext_bfb_cin.trans ext_cin_f) hflat_bfb) hflat_indData evmw
      have htot_eq' : tot' = tot := flatTotalCtors_det htot'_eq htot_eq; subst tot'
      obtain ⟨dsMin, hlenMin0, hdsMin⟩ := repUnitList_to_rawKExprList hmins_u
      have hlenMin : dsMin.length = tot := by simpa using hlenMin0
      obtain ⟨hv_nmin, hm_cbp_eq⟩ := rawKExprList_length_spec ev_mlen hdsMin
      subst hm_cbp_eq
      rw [hlenMin] at hv_nmin; rw [hv_nmin] at heq_nmin2
      have hnmin_eq : rc.minors.toNat = tot := by
        have h1 := congrArg ZMod.val (Value.field.inj heq_nmin2)
        rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1
      -- HeapEqOrWrap from sg_f (at m_eq extending m_brt_out)
      have hrel_cty : ∃ m_eq, Heap.Extends m_brt_out m_eq ∧ HeapEqOrWrap calls m_eq x_cty xty := by
        cases sg_f with
        | n1_n1 _ cs_k evk _ _ _ hcs =>
          exact ⟨m_brt_out, Heap.Extends.refl _,
            Or.inl ⟨_, cs_k, hsub_cap' (fun cl (hcl' : cl ∈ cs_k) => mem_of_eq hc_cap (by
              have : cl ∈ cs_f := mem_of_eq hcs (by call_mem); call_mem)), evk⟩⟩
        | n1_other_n1 _ cs_k _ _ evk _ _ _ _ hcs =>
          exact ⟨m_brt_out, Heap.Extends.refl _,
            Or.inl ⟨_, cs_k, hsub_cap' (fun cl (hcl' : cl ∈ cs_k) => mem_of_eq hc_cap (by
              have : cl ∈ cs_f := mem_of_eq hcs (by call_mem); call_mem)), evk⟩⟩
        | n1_other_other _ cs_k _ _ _ evk _ _ _ _ _ _ hcs =>
          exact ⟨m_brt_out, Heap.Extends.refl _,
            Or.inl ⟨_, cs_k, hsub_cap' (fun cl (hcl' : cl ∈ cs_k) => mem_of_eq hc_cap (by
              have : cl ∈ cs_f := mem_of_eq hcs (by call_mem); call_mem)), evk⟩⟩
        | other _ _ _ _ _ _ _ _ cs_w _ _ _ _ evk _ evrg _ evw heqw _ _ _ _ _ hcs =>
          subst heqw
          exact ⟨_, evk.heap_extends.trans evrg.heap_extends,
            Or.inr ⟨_, _, cs_w, hsub_cap' (fun cl (hcl' : cl ∈ cs_w) => mem_of_eq hc_cap (by
              have : cl ∈ cs_f := mem_of_eq hcs (by call_mem); call_mem)), evw⟩⟩
      obtain ⟨m_eq, ext_brt_eq, hrel_eq⟩ := hrel_cty
      -- check_rec_motive_spec + heapForalls_eq_count + heapAppBVar_eq_of_heapEqOrWrap => lenP = np, lenI = pni, sp = k!
      obtain rfl := binop_add_nat op451
      obtain rfl := binop_add_nat op443
      obtain rfl := binop_add_nat op435
      obtain rfl := binop_add_one_nat op427
      obtain rfl := binop_add_nat op469
      obtain ⟨yd, hforalls_ty, hab_ty⟩ := check_rec_motive_spec (by omega) (by omega) ev_mot
      have ext_335_eq : Heap.Extends m335 m_eq :=
        ext_335_391.trans <| ext_391_cj.trans <| ext_cj_669.trans <|
          ev_pa.heap_extends.trans <| ev_pci.heap_extends.trans <|
          ext_pci_elim.trans <| ext_elim_cin.trans <| ev_brt.heap_extends.trans ext_brt_eq
      have ext_ci_eq : Heap.Extends m_ci m_eq := ext_ci_335.trans ext_335_eq
      obtain ⟨hcnt_eq, h_end, ext_eq_end, hrel_end⟩ :=
        heapForalls_eq_count (lenP + flat.length + tot + lenI + 1)
          (hforalls_cty.mono ext_brt_eq) (hconcl_bv.mono ext_brt_eq).not_forall
          hrel_eq (hforalls_ty.mono ext_335_eq) (hab_ty.mono ext_335_eq).not_forall
      have hlenP_eq : lenP = rc.params.toNat := by omega
      have hlenI_eq : lenI = pInfo.ni := by omega
      subst hlenP_eq hlenI_eq
      have hbv_eq := heapAppBVar_eq_of_heapEqOrWrap (hconcl_bv.mono ext_brt_eq)
        ext_eq_end (hab_ty.mono (ext_335_eq.trans ext_eq_end)) hrel_end
      have hbv_nat : flat.length + tot + pInfo.ni - sp = rc.motives.toNat + rc.minors.toNat + rc.indices.toNat - k := by
        have h1 := congrArg ZMod.val hbv_eq
        rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1
      have hsp_eq : sp = k := by omega
      subst hsp_eq
      -- ty_peel_body + ty_body_nf (from hforalls_ty + hab_ty + htm_ty)
      obtain ⟨ty_body, hty_peel_body, hty_body_tm⟩ :=
        peelForalls_of_heapForalls_tmOExact _ hforalls_ty (htm_ty.mono ext_ci_335)
      have hty_body_nf := tmOExact_not_forall_of_heapAppBVar hty_body_tm hab_ty
      -- Motive carriers & major head via heapEqOrWrap_motiveCarrierAt / heapEqOrWrap_majorHeadAt
      have hmotive_carrier : ∀ (j : Nat) (ej : FlatEntry), flat[j]? = some ej →
          ∃ n, FamilyOf.motiveCarrierAt crb rc j n = some ej.addr := by
        intro j ej hej
        obtain ⟨q, dp, bp, lp, hfj, ldj, hmcj⟩ := hmots_car j ej hej
        obtain ⟨-, info_j, hind_j⟩ := hflat_indData ej (List.mem_of_getElem? hej)
        obtain ⟨-, ca_j, p_j, -, -, -, hca_j, hci_j, -⟩ := indInfoAt_of_indDataAt hind_j
        exact heapEqOrWrap_motiveCarrierAt hS hH hbd hca_j hci_j (by simp)
          (hfj.mono ext_brt_eq) (loadValue_mono ext_brt_eq ldj) (hmcj.mono ext_brt_eq)
          hrel_eq (hraw_ty.mono ext_ci_eq (fun _ hp => hp))
      have hmajor_head : ∃ n, FamilyOf.majorHeadAt crb rc n = some e_s.addr := by
        obtain ⟨q, dp, bp, lp, hfm, ldm, hacm⟩ := hmaj_car
        obtain ⟨-, info_k, hind_k⟩ := hflat_indData e_s (List.mem_of_getElem? hsp_get)
        obtain ⟨-, ca_k, p_k, -, -, -, hca_k, hci_k, -⟩ := indInfoAt_of_indDataAt hind_k
        have hfm' : HeapForalls m_eq (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) x_cty q := by
          rw [hnmot_eq, hnmin_eq, ← hflat_len, ← hni_eq]; exact hfm.mono ext_brt_eq
        exact heapEqOrWrap_majorHeadAt hS hH hbd hca_k hci_k (by simp)
          hfm' (loadValue_mono ext_brt_eq ldm) (hacm.mono ext_brt_eq)
          hrel_eq (hraw_ty.mono ext_ci_eq (fun _ hp => hp))
      -- Assemble heap extensions for Pass 2 & Pass 3
      have ext_brt_out_cbp : Heap.Extends m_brt_out m_cbp_in :=
        ext_brt_f.trans ev_mins.heap_extends
      have ext_cin_cbp_out : Heap.Extends m_brt_in m_cbp_out :=
        ev_brt.heap_extends.trans (ext_brt_out_cbp.trans ev_cbp.heap_extends)
      have ext_ci_pop : Heap.Extends m_ci m_pop :=
        ext_ci_cin.trans (ext_cin_cbp_out.trans ev_pop.heap_extends)
      have ext_elim_pop : Heap.Extends m_elim m_pop :=
        ext_elim_cin.trans (ext_cin_cbp_out.trans ev_pop.heap_extends)
      have ext_pci_cbp_out : Heap.Extends m_pci m_cbp_out :=
        ext_pci_elim.trans (ext_elim_cin.trans ext_cin_cbp_out)
      have ext_rlvls_cbp_out : Heap.Extends m_rlvls m_cbp_out :=
        ev_bfb.heap_extends.trans (ext_bfb_cin.trans ext_cin_cbp_out)
      have ext_peers_cbp_out : Heap.Extends m_peers m_cbp_out :=
        ev_fop.heap_extends.trans (ext_fop_cin.trans ext_cin_cbp_out)
      obtain rfl := binop_add_one_nat op_k1
      refine ⟨xrest, xmrest, hrest_rep, ⟨{
        ty := ty, d := d, us := us, pa := pa_b, pInfo := pInfo,
        prim := prim, cprim := cprim, msp := msp, os := os, flat := flat,
        tot := tot, ek := e_s, fop := fop,
        rnp_eq := hrnp_eq, nmot_eq := hnmot_eq, nmin_eq := hnmin_eq, lvls_eq := hlvls_eq,
        flat_len := hflat_len, tot_lt := htot_lt, lvls_lt := hnl_lt,
        ni_eq := hni_eq, ni_lt := hni_lt, pnp_le := hpnp_le,
        pInfo_at := hpInfo_at, pInfo_nctors_lt := hpnct_lt, pInfo_idx_lt := hpidx_lt,
        pInfo_blk_held := hpInfo_blk_held, loaded_ty := hloaded_ty,
        major_dom := hd, major_fn := hfn,
        prim_frp := by rw [← hrba_addr, ← hpba_addr]; exact hfrp,
        prim_held := hSprim, prim_rec := hcprim, prim_muts := hmsp,
        orig_eq := horig, aux_eq := by rw [← hrba_addr]; exact haux,
        filt_eq := hfilt, os_props := hos_props,
        flat_held_ind := fun e he => ⟨(hflat_held e he).1, (hflat_indData e he).2, (hflat_held e he).2⟩,
        flat_tot := htot_eq, flat_k := hsp_get, ek_addr := ha_s,
        fop_eq := hfop_eq, fop_len := hfop_len, fop_lt := hfop_lt,
        motive_carrier := hmotive_carrier, major_head := hmajor_head,
        m_car := m391, x_ty := xty, blobs := blobs,
        ext_h_car := ev_ci.heap_extends.trans (ext_ci_335.trans ext_335_391),
        raw_ty := hraw_ty.mono (ext_ci_335.trans ext_335_391) (fun _ hp => hp),
        ev_carriers := ⟨_, _, _, ev_car⟩,
        ty_body := ty_body, ty_peel_body := hty_peel_body, ty_body_nf := hty_body_nf,
        m_brt_in := m_brt_in, m_brt_out := m_brt_out,
        x_elim := v_elim, x_flat := v_flat, x_fop := v_fop, x_cty := x_cty,
        x_pty := x_pty, x_pnl := x_pnl, x_rules := xrules, x_rba := blkPtr, x_pba := x_pba,
        x_r := xr, x_rlvls := v_rlvls, x_peers := v_peers, x_occ_us := x_occ, x_sp := x_sp_p,
        x_cbk := x_cbk, x_can := x_can, x_form2 := xform2,
        rba_b := rba_b, pba_b := pba_b, rba_addr := hrba_addr, pba_addr := hpba_addr,
        m_elim := m_elim, m_rlvls := m_rlvls, m_bfb := m_bfb, m_peers := m_peers,
        m_cbp_in := m_cbp_in, m_cbp_out := m_cbp_out, m_pop := m_pop, m_cmp := m_can,
        m_next := m_next, x_s_next := xs_next,
        ext_h_next := ext_h_next,
        ext_h_brt_out := ev_ci.heap_extends.trans (ext_ci_cin.trans ev_brt.heap_extends),
        ext_brt_out_cbp := ext_brt_out_cbp,
        helim_brt := helim.mono ext_elim_cin,
        hflat_brt := flatList_mono ext_bfb_cin hflat_bfb,
        hfop_brt := repList_heapMono₂ _ (fun _ _ _ _ _ h => h) ext_fop_cin hfop_fop,
        hty_brt_out := htm_ty.mono (ext_ci_cin.trans ev_brt.heap_extends),
        hrules_pop := RecRulesRep.mono ext_ci_pop hrules_ci,
        hty_pop := htm_ty.mono ext_ci_pop,
        helim_pop := helim.mono ext_elim_pop,
        hflat_bfb := hflat_bfb,
        rrba_bfb := Bytes.repAddressRef_heapMono₂ addrTy (ext_ci_rlvls.trans ev_bfb.heap_extends) rrba,
        rpba_cbp_out := Bytes.repAddressRef_heapMono₂ addrTy ext_pci_cbp_out rpba_pci,
        hocc_cbp_out := hocc_rep.mono ext_cin_cbp_out,
        hsp_cbp_out := tmOExactList_mono ext_cin_cbp_out hsp_rep,
        hflat_cbp_in := flatList_mono (ext_bfb_cin.trans (ev_brt.heap_extends.trans ext_brt_out_cbp)) hflat_bfb,
        hflat_cbp_out := flatList_mono (ext_bfb_cin.trans ext_cin_cbp_out) hflat_bfb,
        hfop_cbp_out := repList_heapMono₂ _ (fun _ _ _ _ _ h => h) (ext_fop_cin.trans ext_cin_cbp_out) hfop_fop,
        helim_cbp_out := helim.mono (ext_elim_cin.trans ext_cin_cbp_out),
        ext_rlvls_cbp_out := ext_rlvls_cbp_out,
        ext_peers_cbp_out := ext_peers_cbp_out,
        ev_rlvls := ⟨cs_rlvls, hsub_rlvls, ev_rlvls⟩,
        ev_peers := ⟨cs_peers, hsub_peers, ev_peers⟩,
        ev_brt := ⟨cs_brt, hsub_cap' (fun cl hcl' => mem_of_eq hc_cap (by call_mem)),
          by rwa [hrnp_eq] at ev_brt'⟩,
        sg_form := ⟨m224, cs_f, hsub_cap' (fun cl hcl' => mem_of_eq hc_cap (by call_mem)),
          by simpa only [hrnp_eq, hx_nct_eq, hx_pidx_eq, hx_pni_eq] using sg_f⟩,
        ev_cbp := ⟨cs_cbp, hsub_cap' (fun cl hcl' => mem_of_eq hc_cap (by call_mem)), ev_cbp⟩,
        ev_pop := ⟨cs_pop, hsub_cap' (fun cl hcl' => mem_of_eq hc_cap (by call_mem)),
          by simpa only [hrnp_eq, hx_nct_eq, hx_pidx_eq] using ev_pop⟩,
        ev_cmp := ⟨r_cmp, cs_cmp, hsub_cap' (fun cl hcl' => mem_of_eq hc_cap (by call_mem)),
          by simpa only [hrnp_eq, hx_nct_eq, hx_pidx_eq] using ev_cmp⟩,
        ev_next := ⟨cs_next, sub (fun cl hcl' => mem_of_eq hc_cr (by call_mem)), ev_next⟩
      }⟩⟩

/-- **Step A (`k = 0`)**: comparing motive 0 from `build_rec_type_heap_shape` against
`check_carriers_motive0` pins `prim = B`, so every `build_flat_block` call in `check_recs`
deterministically produces `B`'s flattened family. -/
private theorem check_recs_head_prim_eq {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {msB rs : Array Ixon.MutConst} {np off bnl : Nat}
    {t0 : Bytes.Address} {trest : List Bytes.Address} {a0 : Bytes.Address} {rrest : List Bytes.Address}
    {ind₀ : Ixon.Inductive} {r₀ : Ixon.Recursor}
    {xrc xta xrecs xmodels xsrc xdst xaset xs xfam xform r_out : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    (hBlock : FamBlockRecord E₀ B cb msB) (hRec : FamRecRecord E₀ rb crb rs)
    (hSrb : Held R rb) (hrs_lt : rs.size < 2 ^ 39)
    (hnp_lt : np < 72057594037927936) (hoff : off ≤ 1) (hbnl_lt : bnl < 4294967296)
    (hms0 : msB[0]? = some (.indc ind₀)) (ht0 : ixAddr t0 = memberAddr B 0 (.indc ind₀))
    (hrs0 : rs[0]? = some (.recr r₀)) (ha0 : ixAddr a0 = memberAddr rb 0 (.recr r₀))
    (hta : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (t0 :: trest) xta)
    (hrecs : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (a0 :: rrest) xrecs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (ev : ObsFn W "KernelModeled::check_recs"
      [xrc, xta, xrecs, xmodels, xsrc, xdst, xaset, xs, .field (rs.size : F), .field ((0 : Nat) : F),
        .field (np : F), .field (off : F), .field (bnl : F), xfam, xform] h r_out h' cs) :
    ∀ fb : _root_.Address, firstRecrParentBlock t E₀ rb crb rs fb 0 rs.toList = some B := by
  have h0_lt : 0 < rs.size := (Array.getElem?_eq_some_iff.mp hrs0).1
  obtain ⟨_, _, -, ⟨st⟩⟩ := check_recs_step_unpack ht hwf hS hH hbd hRagree hcl hlv hRec hSrb
    hrs_lt hnp_lt hoff hbnl_lt h0_lt hrs0 ha0 hrecs hsub ev
  have hka : keyAddr t (Core.keyOf t (ixAddr st.pa)) = some (ixAddr st.pa) :=
    keyAddr_keyOf hwf (ixAddr st.pa)
  obtain ⟨hinfo_pa, -⟩ := indInfoAt_of_indDataAt st.pInfo_at
  have hfrp_all : ∀ fb, firstRecrParentBlock t E₀ rb crb rs fb 0 rs.toList = some st.pInfo.blk := by
    intro fb
    exact (firstRecrParentBlock_indep_fallback (fb₁ := fb) (fb₂ := st.pInfo.blk) (prim := st.pInfo.blk)
      hrs0 st.loaded_ty st.major_dom st.major_fn hka hinfo_pa).1
  have hprim_eq : st.prim = st.pInfo.blk :=
    Option.some.inj (st.prim_frp.symm.trans (hfrp_all st.pInfo.blk))
  -- st.os is nonempty because st.prim (= st.pInfo.blk) has inductive member st.pInfo.idx
  have hos_ne : st.os ≠ [] := by
    intro hnil
    obtain ⟨-, _, pr_p, cbP, msP, indP, -, -, hcbP, hmsP, hgetP, -, -, -, -, hblkP, hidxP⟩ :=
      indInfoAt_of_indDataAt st.pInfo_at
    rw [← hblkP, ← hprim_eq] at hcbP
    have hcbEq : cbP = st.cprim := Option.some.inj (hcbP.symm.trans st.prim_rec)
    subst hcbEq
    have hmsEq : msP = st.msp := Ixon.ConstantInfo.muts.inj (hmsP.symm.trans st.prim_muts)
    subst hmsEq
    have hmem_ind : memberAddr st.prim pr_p.idx.toNat (.indc indP) ∈
        indcAddrs st.prim 0 st.msp.toList := by
      have hsub_ind : ∀ (l : List Ixon.MutConst) (p idx : Nat) (ind : Ixon.Inductive),
          l[idx]? = some (.indc ind) → memberAddr st.prim (p + idx) (.indc ind) ∈ indcAddrs st.prim p l := by
        intro l
        induction l with
        | nil => intro _ _ _ h; simp at h
        | cons m rest ih =>
          intro p idx ind h
          cases idx with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h
            subst h; simp [indcAddrs]
          | succ idx' =>
            simp only [List.getElem?_cons_succ] at h
            have := ih (p + 1) idx' ind h
            rw [show p + 1 + idx' = p + (idx' + 1) by omega] at this
            cases m <;> simp [indcAddrs, this]
      simpa using hsub_ind st.msp.toList 0 pr_p.idx.toNat indP (by rw [Array.getElem?_toList]; exact hgetP)
    have hmap : st.os.map FlatEntry.addr = indcAddrs st.prim 0 st.msp.toList := by
      have hgo : ∀ (V : FlatView) (off : Nat) (addrs : List _root_.Address) (os : List FlatEntry),
          originals V off addrs = some os → os.map FlatEntry.addr = addrs := by
        intro V off addrs
        induction addrs with
        | nil => intro os h; simp [originals] at h; subst h; rfl
        | cons a rest ih =>
          intro os h
          simp only [originals] at h
          cases hc : V.ci a with
          | none => simp only [hc] at h; cases h
          | some opt =>
            simp only [hc] at h
            cases opt with
            | none => cases h
            | some info =>
              cases hr : originals V off rest with
              | none => simp [hr] at h
              | some os' =>
                simp only [hr, Option.map_some, Option.some.injEq] at h
                subst h; simp [ih os' hr]
      exact hgo (FlatView.ofStore t E₀) off _ st.os st.orig_eq
    rw [hnil] at hmap; simp only [List.map_nil] at hmap
    rw [← hmap] at hmem_ind; cases hmem_ind
  obtain ⟨e0, os_rest, hos_cons⟩ := List.exists_cons_of_ne_nil hos_ne
  obtain ⟨auxs, hflat_app, -⟩ := buildFlatAuxStep_append_aux rs.toList 0 st.os st.flat st.aux_eq
  have hflat0 : st.flat[0]? = some e0 := by rw [hflat_app, hos_cons]; rfl
  obtain ⟨n₁, hm1⟩ := st.motive_carrier 0 e0 hflat0
  obtain ⟨r_c, m_c, cs_c, ev_car⟩ := st.ev_carriers
  have hr0_np : r₀.params.toNat < 9223372036854775808 := by have := st.rnp_eq; omega
  obtain ⟨n₂, hm2⟩ := check_carriers_motive0 hr0_np (by simp)
    (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) st.ext_h_car hta)
    st.raw_ty ev_car
  have he0_addr : e0.addr = memberAddr B 0 (.indc ind₀) := by
    have h1 := motiveCarrierAt_mono hm1 (Nat.le_max_left n₁ n₂)
    have h2 := motiveCarrierAt_mono hm2 (Nat.le_max_right n₁ n₂)
    rw [ht0] at h2
    exact Option.some.inj (h1.symm.trans h2)
  obtain ⟨-, -, -, idx₀, ind', hget₀, he0_mem⟩ := st.os_props e0 (by rw [hos_cons]; exact List.mem_cons_self)
  have hcprimR : recordOf R st.prim = some st.cprim := by
    obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp st.prim_held
    have := hRagree _ _ _ hcR st.prim_rec; subst this; exact hcR
  have hprojR := (hcl.2 st.prim st.cprim st.msp hcprimR st.prim_muts idx₀ (.indc ind') hget₀).1
  rw [← he0_mem, he0_addr] at hprojR
  have hproj_eq := hRagree _ _ _ hprojR (hBlock.members 0 (.indc ind₀) hms0)
  have hinfo_eq := congrArg Ixon.Constant.info hproj_eq
  simp only [memberProjection, Ixon.ConstantInfo.iPrj.injEq, Ixon.InductiveProj.mk.injEq] at hinfo_eq
  have hB_eq : st.pInfo.blk = B := hprim_eq.symm.trans hinfo_eq.2
  rw [hB_eq] at hfrp_all
  exact hfrp_all

/-- **Step B (Pass 1)**: with `prim = B` known, every `k < rs.size` sees the exact same flattened
family `flat` and yields `FamilyOfBlock` fields, `rc.lvls.toNat = bnl + off`,
`flatTotalCtors = some rc.minors.toNat`, `pInfo.np ≤ d.getAppArgs.length`, and
`flat[k]?.addr = ixAddr pa`. -/
private theorem check_recs_pass1 {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {msB rs : Array Ixon.MutConst} {np off bnl : Nat} {os flat : List FlatEntry}
    {xrc xta xsrc xdst xaset xfam r_out : SourceValue F}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    (hBlock : FamBlockRecord E₀ B cb msB) (hRec : FamRecRecord E₀ rb crb rs)
    (hSrb : Held R rb) (hrs_lt : rs.size < 2 ^ 39)
    (hnp_lt : np < 72057594037927936) (hoff : off ≤ 1) (hbnl_lt : bnl < 4294967296)
    (hfrp_B : ∀ fb, firstRecrParentBlock t E₀ rb crb rs fb 0 rs.toList = some B)
    (horig_B : originals (FlatView.ofStore t E₀) off (indcAddrs B 0 msB.toList) = some os)
    (haux_B : buildFlatAuxStep t E₀ rb crb rs B 0 rs.toList os = some flat) :
    ∀ (as : List Bytes.Address) (pos : Nat),
      pos + as.length = rs.size →
      (∀ i a, as[i]? = some a → ∃ r, rs[pos + i]? = some (.recr r) ∧
        ixAddr a = memberAddr rb (pos + i) (.recr r)) →
      ∀ {xrecs xmodels xs xform : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xrecs →
        (∀ cl ∈ cs, cl ∈ calls) →
        ObsFn W "KernelModeled::check_recs"
          [xrc, xta, xrecs, xmodels, xsrc, xdst, xaset, xs, .field (rs.size : F), .field (pos : F),
            .field (np : F), .field (off : F), .field (bnl : F), xfam, xform] h r_out h' cs →
        ∀ (k : Nat) (rc : Ixon.Recursor), pos ≤ k → rs[k]? = some (.recr rc) →
          rc.params.toNat = np ∧
          rc.motives.toNat = flat.length ∧
          rc.lvls.toNat = bnl + off ∧
          flatTotalCtors (ReconView.ofStore t E₀) flat = some rc.minors.toNat ∧
          (∀ e ∈ flat, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
            (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p)) ∧
          (∀ j ej, flat[j]? = some ej → ∃ n, FamilyOf.motiveCarrierAt crb rc j n = some ej.addr) ∧
          (∀ ek, flat[k]? = some ek → ∃ n, FamilyOf.majorHeadAt crb rc n = some ek.addr) ∧
          ∃ (ty d : KExpr) (us : List KLevel) (pa : Bytes.Address) (pInfo : IndData),
            loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
            binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
              rc.indices.toNat) ty = some d ∧
            d.getAppFn = .const (Core.keyOf t (ixAddr pa)) us ∧
            indDataAt t E₀ (ixAddr pa) = some (some pInfo) ∧
            pInfo.ni = rc.indices.toNat ∧
            pInfo.np ≤ d.getAppArgs.length ∧
            flat[k]?.map FlatEntry.addr = some (ixAddr pa) := by
  intro as
  induction as with
  | nil =>
    intro pos hlen _ _ _ _ _ _ _ _ _ _ _ k rc hle hk
    have := (Array.getElem?_eq_some_iff.mp hk).1
    simp at hlen; omega
  | cons a_k rest ih =>
    intro pos hlen has xrecs xmodels xs xform h h' cs hrecs hsub ev k rc hle hk
    obtain ⟨r_pos, hr_pos, ha_pos⟩ := has 0 a_k rfl
    simp only [Nat.add_zero] at hr_pos ha_pos
    have hpos_lt : pos < rs.size := by simp at hlen; omega
    obtain ⟨xrest, xmrest, hrest_rep, ⟨st⟩⟩ := check_recs_step_unpack ht hwf hS hH hbd hRagree
      hcl hlv hRec hSrb hrs_lt hnp_lt hoff hbnl_lt hpos_lt hr_pos ha_pos hrecs hsub ev
    -- Deterministically pin st.prim = B, st.os = os, st.flat = flat
    have hprim_B : st.prim = B := Option.some.inj (st.prim_frp.symm.trans (hfrp_B st.pInfo.blk))
    have hcprim_B : st.cprim = cb := Option.some.inj ((hprim_B ▸ st.prim_rec).symm.trans hBlock.record)
    have hmsp_B : st.msp = msB := Ixon.ConstantInfo.muts.inj ((hcprim_B ▸ st.prim_muts).symm.trans hBlock.muts)
    have hos_eq : st.os = os := by
      have h1 := st.orig_eq; rw [hprim_B, hmsp_B] at h1
      exact Option.some.inj (h1.symm.trans horig_B)
    have hflat_eq : st.flat = flat := by
      have h1 := st.aux_eq; rw [hprim_B, hos_eq] at h1
      exact Option.some.inj (h1.symm.trans haux_B)
    by_cases hk_eq : k = pos
    · subst hk_eq
      have hrc_eq : rc = r_pos := Ixon.MutConst.recr.inj (Option.some.inj (hk.symm.trans hr_pos))
      subst hrc_eq
      refine ⟨st.rnp_eq, by rw [st.nmot_eq, ← st.flat_len, hflat_eq], st.lvls_eq,
        by rw [st.nmin_eq, ← hflat_eq]; exact st.flat_tot,
        fun e he => st.flat_held_ind e (hflat_eq.symm ▸ he),
        fun j ej hej => st.motive_carrier j ej (hflat_eq.symm ▸ hej),
        fun ek hek => ?_,
        st.ty, st.d, st.us, st.pa, st.pInfo, st.loaded_ty, st.major_dom, st.major_fn,
        st.pInfo_at, st.ni_eq, st.pnp_le, ?_⟩
      · have hek_eq : ek = st.ek := Option.some.inj ((hflat_eq ▸ st.flat_k).symm.trans hek).symm
        rw [hek_eq]; exact st.major_head
      · rw [← hflat_eq, st.flat_k]; simp [st.ek_addr]
    · obtain ⟨cs_n, hsub_n, ev_n⟩ := st.ev_next
      exact ih (pos + 1) (by simp at hlen; omega)
        (fun i a hi => by
          have := has (i + 1) a (by simpa using hi)
          rwa [show pos + (i + 1) = pos + 1 + i by omega] at this)
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) st.ext_h_next hrest_rep)
        hsub_n ev_n k rc (by omega) hk

/-- 3-state form invariant carried across `check_recs` (`Seg_dckjugtb`). -/
private def FormInv (lim : Option Nat) (xform : SourceValue F) (P1 P2 : Prop) : Prop :=
  (xform = .field 0 ∨ xform = .field 1 ∨ xform = .field 2) ∧
  (xform = .field 0 → P1 ∧ P2) ∧
  (xform = .field 1 → P1) ∧
  (xform = .field 2 → P2 ∧ ∀ n, lim = some n → n < 77 → False)

/-- **Step C1 (Pass 2)**: with `FlatEntryParamsOk` known, runs `build_rec_type_spec` and tracks
the 3-state `form` discipline across `check_recs`, yielding exact major-premise level lists
(completing `RecordFlatAux` on originals) and the global `ExprLvEq ∨ WrapConsObs` disjunction. -/
private theorem check_recs_pass2 {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {msB rs : Array Ixon.MutConst} {lim : Option Nat} {np off bnl tot : Nat}
    {os flat : List FlatEntry} {xrc xta xsrc xdst xaset xfam r_out : SourceValue F}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers calls (Held R) (ReconView.ofStore t E₀))
    (hBlock : FamBlockRecord E₀ B cb msB) (hRec : FamRecRecord E₀ rb crb rs)
    (hSrb : Held R rb) (hrs_lt : rs.size < 2 ^ 39)
    (hnp_lt : np < 72057594037927936) (hoff : off ≤ 1) (hbnl_lt : bnl < 4294967296)
    (hfrp_B : ∀ fb, firstRecrParentBlock t E₀ rb crb rs fb 0 rs.toList = some B)
    (horig_B : originals (FlatView.ofStore t E₀) off (indcAddrs B 0 msB.toList) = some os)
    (haux_B : buildFlatAuxStep t E₀ rb crb rs B 0 rs.toList os = some flat)
    (htot_flat : flatTotalCtors (ReconView.ofStore t E₀) flat = some tot)
    (hflat_ne : flat ≠ [])
    (hall_ok : ∀ e ∈ flat, Held R e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
      (∀ p ∈ e.params, AddrIn (Held R) (Core.keyOf t) p) ∧
      FlatEntryParamsOk (ReconView.ofStore t E₀) np e) :
    ∀ (as : List Bytes.Address) (pos : Nat),
      pos + as.length = rs.size →
      (∀ i a, as[i]? = some a → ∃ r, rs[pos + i]? = some (.recr r) ∧
        ixAddr a = memberAddr rb (pos + i) (.recr r)) →
      ∀ {xrecs xmodels xs xform : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        Claim.RCLimRep t bAddr lim h xrc →
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xrecs →
        (∀ cl ∈ cs, cl ∈ calls) →
        FormInv lim xform
          (∀ k < pos, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              ExprLvEq ty Rty)
          (∀ k < pos, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty ty) →
        ObsFn W "KernelModeled::check_recs"
          [xrc, xta, xrecs, xmodels, xsrc, xdst, xaset, xs, .field (rs.size : F), .field (pos : F),
            .field (np : F), .field (off : F), .field (bnl : F), xfam, xform] h r_out h' cs →
        (∀ k rc e, pos ≤ k → rs[k]? = some (.recr rc) → flat[k]? = some e →
          ∃ ty d info,
            loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
            binderDomAfter (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
              rc.indices.toNat) ty = some d ∧
            d.getAppFn = .const (Core.keyOf t e.addr) e.levels ∧
            indInfoAt E₀ e.addr = some (some info)) ∧
        ((∀ k < rs.size, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              ExprLvEq ty Rty) ∨
         ((∀ k < rs.size, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty ty) ∧
          ∀ n, lim = some n → n < 77 → False)) := by
  intro as
  induction as with
  | nil =>
    intro pos hlen _ xrecs xmodels xs xform h h' cs _ _ _ hfinv _
    have hpos_eq : pos = rs.size := by simp at hlen; omega
    subst hpos_eq
    refine ⟨fun k rc e hge hk _ => absurd (Array.getElem?_eq_some_iff.mp hk).1 (by omega), ?_⟩
    rcases hfinv.1 with rfl | rfl | rfl
    · exact Or.inl (hfinv.2.1 rfl).1
    · exact Or.inl (hfinv.2.2.1 rfl)
    · exact Or.inr (hfinv.2.2.2 rfl)
  | cons a_k rest ih =>
    intro pos hlen has xrecs xmodels xs xform h h' cs hrc hrecs hsub hfinv ev
    obtain ⟨r_pos, hr_pos, ha_pos⟩ := has 0 a_k rfl
    simp only [Nat.add_zero] at hr_pos ha_pos
    have hpos_lt : pos < rs.size := by simp at hlen; omega
    obtain ⟨xrest, xmrest, hrest_rep, ⟨st⟩⟩ := check_recs_step_unpack ht hwf hS hH hbd hRagree
      hcl hlv hRec hSrb hrs_lt hnp_lt hoff hbnl_lt hpos_lt hr_pos ha_pos hrecs hsub ev
    -- Pin st.flat = flat
    have hprim_B : st.prim = B := Option.some.inj (st.prim_frp.symm.trans (hfrp_B st.pInfo.blk))
    have hcprim_B : st.cprim = cb := Option.some.inj ((hprim_B ▸ st.prim_rec).symm.trans hBlock.record)
    have hmsp_B : st.msp = msB := Ixon.ConstantInfo.muts.inj ((hcprim_B ▸ st.prim_muts).symm.trans hBlock.muts)
    have hos_eq : st.os = os := by
      have h1 := st.orig_eq; rw [hprim_B, hmsp_B] at h1
      exact Option.some.inj (h1.symm.trans horig_B)
    have hflat_eq : st.flat = flat := by
      have h1 := st.aux_eq; rw [hprim_B, hos_eq] at h1
      exact Option.some.inj (h1.symm.trans haux_B)
    -- Run build_rec_type_spec on st.ev_brt
    obtain ⟨e0, flat_rest, hflat_cons⟩ := List.exists_cons_of_ne_nil hflat_ne
    have he0_get : flat[0]? = some e0 := by rw [hflat_cons]; rfl
    obtain ⟨prim0, hprim0⟩ := (hall_ok e0 (by rw [hflat_cons]; exact List.mem_cons_self)).2.1
    have hself_pos : indDataAt t E₀ st.ek.addr = some (some st.pInfo) := by
      rw [st.ek_addr]; exact st.pInfo_at
    obtain ⟨cs_brt, hsub_brt, ev_brt⟩ := st.ev_brt
    obtain ⟨Rty, tot', -, -, hev_Rty, hRty_tm, hRty_in⟩ :=
      build_rec_type_spec ht hwf hS hH hbd hRagree hcl hlv hM hoff hnp_lt (st.ni_eq ▸ st.ni_lt) rfl
        he0_get (hflat_eq ▸ st.flat_k) hprim0 hself_pos (hflat_eq ▸ st.fop_eq)
        (by rw [st.fop_len, hflat_eq]) st.fop_lt hsub_brt st.helim_brt
        (hflat_eq ▸ st.hflat_brt) st.hfop_brt hall_ok ev_brt
    -- Analyze sg_form to get (Rty = st.ty ∨ WrapConsEqObs ...) AND update FormInv
    obtain ⟨m_f, cs_f, hsub_f, sg_f⟩ := st.sg_form
    have hstep_form :
        (Rty = st.ty ∨ WrapConsEqObs (wrapAt t E₀) (WrapperObserved calls t) Rty st.ty) ∧
        FormInv lim st.x_form2
          (∀ k < pos + 1, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              ExprLvEq ty Rty)
          (∀ k < pos + 1, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty ty) := by
      have ext_P1 : ∀ (P1 : ∀ k < pos, ∀ rc, rs[k]? = some (.recr rc) →
          ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
            (mutsRoot rs k) rc.typ = some ty ∧
            Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
            ExprLvEq ty Rty),
          ExprLvEq st.ty Rty →
          ∀ k < pos + 1, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              ExprLvEq ty Rty := by
        intro hP1 hcur k hk rc hrc_k
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
        · exact hP1 k hlt rc hrc_k
        · have heq := Ixon.MutConst.recr.inj (Option.some.inj (hrc_k.symm.trans hr_pos)); subst heq
          exact ⟨st.ty, Rty, st.loaded_ty, by rwa [st.rnp_eq], hcur⟩
      have ext_P2 : ∀ (P2 : ∀ k < pos, ∀ rc, rs[k]? = some (.recr rc) →
          ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
            (mutsRoot rs k) rc.typ = some ty ∧
            Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
            WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty ty),
          WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty st.ty →
          ∀ k < pos + 1, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty ty := by
        intro hP2 hcur k hk rc hrc_k
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
        · exact hP2 k hlt rc hrc_k
        · have heq := Ixon.MutConst.recr.inj (Option.some.inj (hrc_k.symm.trans hr_pos)); subst heq
          exact ⟨st.ty, Rty, st.loaded_ty, by rwa [st.rnp_eq], hcur⟩
      cases sg_f with
      | n1_n1 _ _ evk hv_f hr_f _ _ =>
        have hEq : Rty = st.ty := kexpr_struct_eq_oexact hRty_tm st.hty_brt_out evk
        have hQ1 : ExprLvEq st.ty Rty := hEq ▸ ExprLvEq.refl st.ty
        refine ⟨Or.inl hEq, Or.inr (Or.inl hr_f), ?_, ?_, ?_⟩
        · intro h0; rw [hr_f] at h0; exact absurd (Value.field.inj h0) one_ne_zero
        · intro _; exact ext_P1 (hfinv.2.2.1 hv_f) hQ1
        · intro h2; rw [hr_f] at h2; exact absurd (Value.field.inj h2) (by decide)
      | n1_other_n1 _ _ _ cs_w evk hne_f evw hr_f _ hc_f =>
        have hEq : Rty = st.ty := kexpr_struct_eq_oexact hRty_tm st.hty_brt_out evk
        have hQ1 : ExprLvEq st.ty Rty := hEq ▸ ExprLvEq.refl st.ty
        have hsub_w : ∀ cl ∈ cs_w, cl ∈ calls := fun cl hcl' => hsub_f cl (mem_of_eq hc_f (by call_mem))
        have hQ2 : WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty st.ty :=
          wrap_rel_one_wrapConsObs ht hwf hS hH hbd hRagree hcl hlv hsub_w
            (hRty_tm.mono evk.heap_extends) (st.hty_brt_out.mono evk.heap_extends) hRty_in evw
        refine ⟨Or.inl hEq, ?_, ?_, ?_, ?_⟩
        · rw [hr_f]; exact hfinv.1
        · intro h0; rw [hr_f] at h0
          exact ⟨ext_P1 (hfinv.2.1 h0).1 hQ1, ext_P2 (hfinv.2.1 h0).2 hQ2⟩
        · intro h1; rw [hr_f] at h1; exact (hne_f h1).elim
        · intro h2; rw [hr_f] at h2
          exact ⟨ext_P2 (hfinv.2.2.2 h2).1 hQ2, (hfinv.2.2.2 h2).2⟩
      | n1_other_other _ _ _ _ _ evk _ _ _ heq_f hr_f _ _ =>
        have hEq : Rty = st.ty := kexpr_struct_eq_oexact hRty_tm st.hty_brt_out evk
        have hQ1 : ExprLvEq st.ty Rty := hEq ▸ ExprLvEq.refl st.ty
        refine ⟨Or.inl hEq, Or.inr (Or.inl hr_f), ?_, ?_, ?_⟩
        · intro h0; rw [hr_f] at h0; exact absurd (Value.field.inj h0) one_ne_zero
        · intro _; exact ext_P1 (hfinv.2.1 heq_f).1 hQ1
        · intro h2; rw [hr_f] at h2; exact absurd (Value.field.inj h2) (by decide)
      | other _ _ _ _ _ _ _ _ cs_w _ _ _ _ evk _ evrg heq_rg evw heq_w op_sub eviz heq_iz hr_f _ hc_f =>
        subst heq_rg heq_w heq_iz
        have hsub_w : ∀ cl ∈ cs_w, cl ∈ calls := fun cl hcl' => hsub_f cl (mem_of_eq hc_f (by call_mem))
        have hweq := wrap_rel_one_oexact ht hwf hS hH hbd hRagree hcl hlv hsub_w
          (hRty_tm.mono (evk.heap_extends.trans evrg.heap_extends))
          (st.hty_brt_out.mono (evk.heap_extends.trans evrg.heap_extends)) hRty_in evw
        have hQ2 := hweq.toWrapConsObs
        have hne1 : xform ≠ .field 1 := by
          intro h1; subst h1
          simp only [evalBinOp, sub_self, Except.ok.injEq] at op_sub
          rw [← op_sub] at eviz
          obtain ⟨hz, -⟩ := Lib.is_zero_spec eviz
          simp at hz
        have hP2_prev : ∀ k < pos, ∀ rc, rs[k]? = some (.recr rc) →
            ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
              Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
              WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) Rty ty := by
          rcases hfinv.1 with rfl | rfl | rfl
          · exact (hfinv.2.1 rfl).2
          · exact (hne1 rfl).elim
          · exact (hfinv.2.2.2 rfl).1
        have hnot_grp : ∀ n, lim = some n → n < 77 → False := by
          intro n hlim hn
          subst hlim
          have hrc_k := hrc.mono (st.ext_h_brt_out.trans evk.heap_extends)
          obtain ⟨h1, -⟩ := rc_validates_group_spec hn hrc_k evrg
          exact absurd (Value.field.inj h1) zero_ne_one
        refine ⟨Or.inr hweq, Or.inr (Or.inr hr_f), ?_, ?_, ?_⟩
        · intro h0; rw [hr_f] at h0; exact absurd (Value.field.inj h0) (by decide)
        · intro h1; rw [hr_f] at h1; exact absurd (Value.field.inj h1) (by decide)
        · intro _; exact ⟨ext_P2 hP2_prev hQ2, hnot_grp⟩
    obtain ⟨hrel_pos, hfinv_next⟩ := hstep_form
    -- Exact major premise head & levels at k = pos via recTypeAt_majorDom_head_eq
    obtain ⟨f0, hf0⟩ := hev_Rty
    have hrec_f0 := hf0 f0 (Nat.le_refl _)
    have hfn_exact : st.d.getAppFn = .const (Core.keyOf t st.ek.addr) st.ek.levels := by
      have htot_eq : st.tot = tot := flatTotalCtors_det (hflat_eq ▸ st.flat_tot) htot_flat
      have hsum_eq : np + flat.length + tot + st.pInfo.ni =
          r_pos.params.toNat + r_pos.motives.toNat + r_pos.minors.toNat + r_pos.indices.toNat := by
        have hfl : flat.length = rs.size := by rw [← hflat_eq]; exact st.flat_len
        have h1 := st.rnp_eq; have h2 := st.nmot_eq; have h3 := st.nmin_eq; have h4 := st.ni_eq
        omega
      have hd' : binderDomAfter (np + flat.length + tot + st.pInfo.ni) st.ty = some st.d :=
        hsum_eq.symm ▸ st.major_dom
      have hbody' : peelForalls (np + flat.length + tot + st.pInfo.ni + 1) st.ty = some st.ty_body :=
        (congrArg (· + 1) hsum_eq).symm ▸ st.ty_peel_body
      exact recTypeAt_majorDom_head_eq hwf he0_get (hflat_eq ▸ st.flat_k) hprim0 hself_pos
        hrec_f0 htot_flat hd' hbody' st.ty_body_nf hrel_pos
    obtain ⟨cs_n, hsub_n, ev_n⟩ := st.ev_next
    obtain ⟨hrest_rf, hform_final⟩ := ih (pos + 1) (by simp at hlen; omega)
      (fun i a hi => by
        have := has (i + 1) a (by simpa using hi)
        rwa [show pos + (i + 1) = pos + 1 + i by omega] at this)
      (hrc.mono st.ext_h_next)
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) st.ext_h_next hrest_rep)
      hsub_n hfinv_next ev_n
    refine ⟨fun k rc e hge hk he => ?_, hform_final⟩
    by_cases hk_eq : k = pos
    · subst k
      have hrc_eq := Ixon.MutConst.recr.inj (Option.some.inj (hk.symm.trans hr_pos)); subst hrc_eq
      have he_eq : e = st.ek := Option.some.inj (he.symm.trans (hflat_eq ▸ st.flat_k))
      subst he_eq
      obtain ⟨hinfo_ek, -⟩ := indInfoAt_of_indDataAt hself_pos
      exact ⟨st.ty, st.d, _, st.loaded_ty, st.major_dom, hfn_exact, hinfo_ek⟩
    · exact hrest_rf k rc e (by omega) hk he

/-- **Step C2 (Pass 3)**: with `RecordFlatAux` and `FlatPeerDistinct` known, resolves peer
recursors, `ctorsBefore`, `populate_rules` (`ruleBodiesAt`), and `compare_rules` (`RuleFollows`)
for every member `k < rs.size`. -/
private theorem check_recs_pass3 {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {msB rs : Array Ixon.MutConst} {np off bnl tot : Nat} {os flat : List FlatEntry}
    {xrc xta xsrc xdst xaset xfam r_out : SourceValue F}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hlv : StoreLevelsOk t E₀ (Held R))
    (hM : ModeledAnswers calls (Held R) (ReconView.ofStore t E₀))
    (hBlock : FamBlockRecord E₀ B cb msB) (hRec : FamRecRecord E₀ rb crb rs)
    (hSrb : Held R rb) (hrs_lt : rs.size < 2 ^ 39)
    (hnp_lt : np < 72057594037927936) (hoff : off ≤ 1) (hbnl_lt : bnl < 4294967296)
    (hfrp_B : ∀ fb, firstRecrParentBlock t E₀ rb crb rs fb 0 rs.toList = some B)
    (horig_B : originals (FlatView.ofStore t E₀) off (indcAddrs B 0 msB.toList) = some os)
    (haux_B : buildFlatAuxStep t E₀ rb crb rs B 0 rs.toList os = some flat)
    (htot_flat : flatTotalCtors (ReconView.ofStore t E₀) flat = some tot)
    (hRF : RecordFlatAux t E₀ rb crb rs flat)
    (hPD : FlatPeerDistinct flat) :
    ∀ (as : List Bytes.Address) (pos : Nat),
      pos + as.length = rs.size →
      (∀ i a, as[i]? = some a → ∃ r, rs[pos + i]? = some (.recr r) ∧
        ixAddr a = memberAddr rb (pos + i) (.recr r)) →
      ∀ {xrecs xmodels xs xform : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xrecs →
        (∀ cl ∈ cs, cl ∈ calls) →
        ObsFn W "KernelModeled::check_recs"
          [xrc, xta, xrecs, xmodels, xsrc, xdst, xaset, xs, .field (rs.size : F), .field (pos : F),
            .field (np : F), .field (off : F), .field (bnl : F), xfam, xform] h r_out h' cs →
        ∀ (k : Nat) (rc : Ixon.Recursor), pos ≤ k → rs[k]? = some (.recr rc) →
          ∃ (ty : KExpr) (bodies : List KExpr) (cbk : Nat),
            loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
              (mutsRoot rs k) rc.typ = some ty ∧
            Eventually (fun f => ruleBodiesAt (ReconView.ofStore t E₀) f flat off rc.params.toNat
              rc.motives.toNat rc.minors.toNat rc.lvls.toNat k (recAddrs rb rs) = some bodies) ∧
            ctorsBefore (ReconView.ofStore t E₀) flat k = some cbk ∧
            ∀ (c : Nat) (ru : Ixon.RecursorRule), rc.rules[c]? = some ru →
              ∃ rhs cb_r,
                loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
                  (mutsRoot rs k + 1 + ((c : Nat) : IxVM.F)) ru.rhs = some rhs ∧
                bodies[c]? = some cb_r ∧
                RuleFollows ty rc.params.toNat rc.motives.toNat rc.minors.toNat
                  (cbk + c) ru.fields.toNat (elimLevel off) rhs cb_r := by
  intro as
  induction as with
  | nil =>
    intro pos hlen has xrecs xmodels xs xform h h' cs hrecs hsub ev k rc hle hk
    have := (Array.getElem?_eq_some_iff.mp hk).1; simp at hlen; omega
  | cons a_k rest ih =>
    intro pos hlen has xrecs xmodels xs xform h h' cs hrecs hsub ev k rc hle hk
    obtain ⟨r_pos, hr_pos, ha_pos⟩ := has 0 a_k rfl
    simp only [Nat.add_zero] at hr_pos ha_pos
    have hpos_lt : pos < rs.size := by simp at hlen; omega
    obtain ⟨xrest, xmrest, hrest_rep, ⟨st⟩⟩ := check_recs_step_unpack ht hwf hS hH hbd hRagree
      hcl hlv hRec hSrb hrs_lt hnp_lt hoff hbnl_lt hpos_lt hr_pos ha_pos hrecs hsub ev
    have hprim_B : st.prim = B := Option.some.inj (st.prim_frp.symm.trans (hfrp_B st.pInfo.blk))
    have hcprim_B : st.cprim = cb := Option.some.inj ((hprim_B ▸ st.prim_rec).symm.trans hBlock.record)
    have hmsp_B : st.msp = msB := Ixon.ConstantInfo.muts.inj ((hcprim_B ▸ st.prim_muts).symm.trans hBlock.muts)
    have hos_eq : st.os = os := by
      have h1 := st.orig_eq; rw [hprim_B, hmsp_B] at h1
      exact Option.some.inj (h1.symm.trans horig_B)
    have hflat_eq : st.flat = flat := by
      have h1 := st.aux_eq; rw [hprim_B, hos_eq] at h1
      exact Option.some.inj (h1.symm.trans haux_B)
    by_cases hk_eq : k = pos
    · subst k
      have hrc_eq := Ixon.MutConst.recr.inj (Option.some.inj (hk.symm.trans hr_pos)); subst hrc_eq
      obtain ⟨cs_rl, -, ev_rl⟩ := st.ev_rlvls
      have hrlvls_rep := build_rec_lvls_list_spec rc.lvls.toNat st.lvls_lt rc.lvls.toNat 0
        (by omega) (by simpa using ev_rl)
      simp only [List.drop_zero] at hrlvls_rep
      obtain ⟨cs_pr, hsub_pr, ev_pr⟩ := st.ev_peers
      obtain ⟨peers, hpeers_rep, hpeers_map⟩ := build_peer_recs_spec ht hwf hS hH hbd hRagree
        hcl hlv hsub_pr (st.rba_addr.symm ▸ hSrb) (st.rba_addr.symm ▸ hRec.record) hRec.muts
        (st.rba_addr.symm ▸ hRF) hPD (hflat_eq ▸ st.hflat_bfb) st.rrba_bfb ev_pr
      have htot_eq : st.tot = tot := flatTotalCtors_det (hflat_eq ▸ st.flat_tot) htot_flat
      have htot_lt : tot < 2 ^ 39 := htot_eq ▸ st.tot_lt
      have hnmot_eq := st.nmot_eq
      have hnmin_eq := st.nmin_eq
      have hrnp_eq := st.rnp_eq
      obtain ⟨cs_cbp, hsub_cbp, ev_cbp⟩ := st.ev_cbp
      obtain ⟨cbk, hcbk_eq, hcbk_lt, hxcb_eq⟩ := ctors_before_pos_spec ht hwf hS hH hbd hRagree
        hcl hlv flat pos 0 tot (Nat.zero_le _) (by omega) (by omega) htot_flat hsub_cbp
        (hflat_eq ▸ st.hflat_cbp_in)
        (fun e he => (st.flat_held_ind e (hflat_eq.symm ▸ he)).1)
        (by simpa using ev_cbp)
      simp only [Nat.sub_zero] at hcbk_eq
      have hcbk_succ := ctorsBefore_succ_add (ReconView.ofStore t E₀) flat pos cbk st.ek st.pInfo
        (hflat_eq ▸ st.flat_k) (st.ek_addr.symm ▸ st.pInfo_at) hcbk_eq
      have hcbk_le : cbk + st.pInfo.nctors ≤ rc.minors.toNat := by
        rw [st.nmin_eq, htot_eq]
        exact ctorsBefore_le_flatTotalCtors (ReconView.ofStore t E₀) flat (pos + 1) _ _
          htot_flat hcbk_succ
      have hpeers_len : peers.length = st.fop.length := by
        have h1 : (peers.map ixAddr).length = (recAddrs rb rs).length :=
          congrArg List.length (by rwa [st.rba_addr] at hpeers_map)
        simp only [List.length_map, recAddrs, List.length_zipIdx, Array.length_toList] at h1
        rw [st.fop_len, st.flat_len]; exact h1
      obtain ⟨cs_pop, hsub_pop, ev_pop⟩ := st.ev_pop
      rw [hxcb_eq] at ev_pop
      obtain ⟨bodies, hev_bodies, hbodies_rep⟩ :=
        populate_rules_spec ht hwf hS hH hbd hRagree hcl hlv hM
          (nP := np) (nMot := rc.motives.toNat) (nMin := rc.minors.toNat)
          st.pInfo_nctors_lt st.pInfo_idx_lt
          hnp_lt (by omega) (by omega) hcbk_le (by rw [st.fop_len, hflat_eq])
          (by rw [st.fop_len, st.flat_len]; omega) hpeers_len st.fop_lt
          (st.pba_addr.symm ▸ st.pInfo_blk_held) st.pInfo.nctors 0 (by omega)
          hsub_pop st.rpba_cbp_out st.hocc_cbp_out (hrlvls_rep.mono st.ext_rlvls_cbp_out)
          (hflat_eq ▸ st.hflat_cbp_out)
          (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            st.ext_peers_cbp_out hpeers_rep)
          st.hfop_cbp_out st.hsp_cbp_out (st.flat_held_ind st.ek (List.mem_of_getElem? st.flat_k)).2.2
          st.helim_cbp_out (by simpa using ev_pop)
      simp only [List.drop_zero] at hev_bodies
      have hbodies_len : bodies.length = st.pInfo.nctors := by
        obtain ⟨f0, hf0⟩ := hev_bodies
        have h1 := ruleBodies_length _ _ (hf0 f0 (Nat.le_refl _))
        simpa using h1
      obtain ⟨r_cmp, cs_cmp, hsub_cmp, ev_cmp⟩ := st.ev_cmp
      rw [hxcb_eq] at ev_cmp
      have hrus_le : rc.rules.toList.length ≤ st.pInfo.nctors := by
        have h1 := compare_rules_len_le st.pInfo_nctors_lt rc.rules.toList bodies 0 (by omega)
          st.hrules_pop hbodies_rep (by simpa using ev_cmp)
        simpa using h1
      have hcmp := compare_rules_spec
        (nP := np) (nMot := rc.motives.toNat) (nMin := rc.minors.toNat) (minorOff := cbk)
        hbd (by omega) rc.rules.toList bodies 0
        (by omega) (by omega) hsub_cmp st.hrules_pop hbodies_rep st.hty_pop st.helim_pop
        (by simpa using ev_cmp)
      refine ⟨st.ty, bodies, cbk, st.loaded_ty, ?_, hcbk_eq, ?_⟩
      · refine hev_bodies.mono fun f hf => ?_
        unfold ruleBodiesAt
        have hind_k : (ReconView.ofStore t E₀).ind st.ek.addr = some (some st.pInfo) :=
          st.ek_addr.symm ▸ st.pInfo_at
        simp only [hflat_eq ▸ st.flat_k, hind_k, hflat_eq ▸ st.fop_eq, hcbk_eq]
        rw [st.rnp_eq]
        have hpm : peers.map ixAddr = recAddrs rb rs := by rwa [st.rba_addr] at hpeers_map
        rw [st.pba_addr, hpm] at hf
        exact hf
      · intro c ru hru
        have hruL : rc.rules.toList[c]? = some ru := by rw [Array.getElem?_toList]; exact hru
        rw [st.rnp_eq]
        simpa [Nat.zero_add] using hcmp c ru hruL
    · obtain ⟨cs_n, hsub_n, ev_n⟩ := st.ev_next
      exact ih (pos + 1) (by simp at hlen; omega)
        (fun i a hi => by
          have := has (i + 1) a (by simpa using hi)
          rwa [show pos + (i + 1) = pos + 1 + i by omega] at this)
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) st.ext_h_next hrest_rep)
        hsub_n ev_n k rc (by omega) hk

private theorem sub_drop {α : Type*} {l₁ l₂ root : List α} {c : α}
    (h : ∀ x ∈ l₁ ++ c :: l₂, x ∈ root) : ∀ x ∈ l₂, x ∈ root :=
  fun x hx => h x (List.mem_append_right l₁ (List.mem_cons_of_mem c hx))

private theorem sub_take {α : Type*} {l₁ l₂ root : List α} {c : α}
    (h : ∀ x ∈ l₁ ++ c :: l₂, x ∈ root) :
    (∀ x ∈ l₁, x ∈ root) ∧ c ∈ root ∧ (∀ x ∈ l₂, x ∈ root) :=
  ⟨fun x hx => h x (List.mem_append_left _ hx),
   h c (List.mem_append_right l₁ List.mem_cons_self),
   fun x hx => h x (List.mem_append_right l₁ (List.mem_cons_of_mem c hx))⟩

private structure CheckFamilyUnpack (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ R' : Ixon.Env) (B rb : _root_.Address)
    (cr : Ixon.Constant) (rs : Array Ixon.MutConst) (lim : Option Nat) where
  bB : Bytes.Address
  bR : Bytes.Address
  bB_eq : ixAddr bB = B
  bR_eq : ixAddr bR = rb
  cb : Ixon.Constant
  msB : Array Ixon.MutConst
  ind₀ : Ixon.Inductive
  np : Nat
  bnl : Nat
  off : Nat
  prim : _root_.Address
  cprim : Ixon.Constant
  msp : Array Ixon.MutConst
  os : List FlatEntry
  flat : List FlatEntry
  as_t : List Bytes.Address
  as_r : List Bytes.Address
  hBlock : FamBlockRecord E₀ B cb msB
  hms0 : msB[0]? = some (.indc ind₀)
  hmsB_lt : msB.size < 8589934592
  hnp_lt : np < 72057594037927936
  hnp_all : ∀ m ∈ msB.toList, ∀ ind, m = .indc ind → ind.params.toNat = np
  hrs_lt : rs.size < 2 ^ 39
  hflat_lt : flat.length < 2 ^ 39
  hflat_len : flat.length = rs.size
  hbnl_lt : bnl < 4294967296
  hoff : off ≤ 1
  hBlockElim : BlockElim t E₀ B off
  hbnl_d0 : ∀ a0 rest, as_t = a0 :: rest →
    ∃ d0, indDataAt t E₀ (ixAddr a0) = some (some d0) ∧ bnl = d0.nl
  has_t_len : as_t.length = msB.toList.length
  has_t_mem : ∀ i a, as_t[i]? = some a →
    ∃ m, msB.toList[i]? = some m ∧ ixAddr a = Core.projAddr (Core.Specs.Callees.memberProjInfo B i m)
  has_r_len : as_r.length = rs.size
  has_r_recr : ∀ i a, as_r[i]? = some a →
    ∃ r, rs[i]? = some (.recr r) ∧ ixAddr a = memberAddr rb i (.recr r)
  hfrp_cf : firstRecrParentBlock t E₀ rb cr rs B 0 rs.toList = some prim
  hSprim : Held R' prim
  hcprim : recordOf E₀ prim = some cprim
  hmsp : cprim.info = .muts msp
  horig_cf : originals (FlatView.ofStore t E₀) off (indcAddrs prim 0 msp.toList) = some os
  haux_cf : buildFlatAuxStep t E₀ rb cr rs prim 0 rs.toList os = some flat
  hfilt_cf : flat.filter (fun e => !e.aux) = os
  hos_props : ∀ e ∈ os, e.aux = false ∧ e.params = [] ∧ Held R' e.addr ∧
    ∃ idx ind, msp[idx]? = some (.indc ind) ∧ e.addr = memberAddr prim idx (.indc ind)
  hflat_held : ∀ e ∈ flat, Held R' e.addr ∧ ∀ p ∈ e.params, AddrIn (Held R') (Core.keyOf t) p
  m_flat : Heap F
  m_cna_out : Heap F
  xb_flat : SourceValue F
  v_flat : SourceValue F
  r_cna : SourceValue F
  cs_cna : List (Call F)
  hsub_cna : ∀ cl ∈ cs_cna, cl ∈ calls
  hbB_flat : Bytes.RepAddressRef addrTy m_flat bB xb_flat
  hflat_rep : RepList flatListEnum (FlatEntryRepExact (Core.keyOf t)) m_flat flat v_flat
  ev_cna : ObsFn W "KernelModeled::check_nested_aux" [xb_flat, v_flat] m_flat r_cna m_cna_out cs_cna
  m_cr : Heap F
  m_cr_out : Heap F
  xrc_cr : SourceValue F
  x_ta : SourceValue F
  x_recs : SourceValue F
  x_rm : SourceValue F
  x_v1 : SourceValue F
  x_v2 : SourceValue F
  x_v3 : SourceValue F
  x_s8 : SourceValue F
  r_cr : SourceValue F
  cs_cr : List (Call F)
  hsub_cr : ∀ cl ∈ cs_cr, cl ∈ calls
  hrc_cr : Claim.RCLimRep t bAddr lim m_cr xrc_cr
  has_t_cr : RepList addrListEnum (Bytes.RepAddressRef addrTy) m_cr as_t x_ta
  has_r_cr : RepList addrListEnum (Bytes.RepAddressRef addrTy) m_cr as_r x_recs
  ev_cr : ObsFn W "KernelModeled::check_recs"
    [xrc_cr, x_ta, x_recs, x_rm, x_v1, x_v2, x_v3, x_s8,
      .field (rs.size : F), .field 0, .field (np : F), .field (off : F), .field (bnl : F),
      x_recs, .field 0] m_cr r_cr m_cr_out cs_cr

private theorem check_family_unpack {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R' : Ixon.Env} {B rb : _root_.Address}
    {cr : Ixon.Constant} {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    {h h' : Heap F} {xrc xb xrb r_cf : SourceValue F} {bB bR : Bytes.Address}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hR'agree : ∀ y c c', recordOf R' y = some c → recordOf E₀ y = some c' → c = c')
    (hcl' : UsedClosed R') (hR'B : Held R' B) (hR'rb : Held R' rb)
    (hlv' : StoreLevelsOk t E₀ (Held R'))
    (hRec : FamRecRecord E₀ rb cr rs) (hrs_ne : rs.size ≠ 0)
    (hBLogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hrc : Claim.RCLimRep t bAddr lim h xrc)
    (hbB : Bytes.RepAddressRef addrTy h bB xb) (hBb : ixAddr bB = B)
    (hbR : Bytes.RepAddressRef addrTy h bR xrb) (hRb : ixAddr bR = rb)
    (ev_cf : ObsFn W "KernelModeled::check_family" [xrc, xb, xrb] h r_cf h' cs)
    (hsub_cf : ∀ cl ∈ cs, cl ∈ calls) :
    Nonempty (CheckFamilyUnpack calls bAddr t E₀ R' B rb cr rs lim) := by
  subst hBb hRb
  match Obs.«KernelModeled::check_family».obs ev_cf with
  | .run (m_vcemfqfp := m105) (v452 := x_v3) (m453 := m453) (m501 := m501) (cs511 := cs511) (x_members := x_members)
      (v588 := v588) (m589 := m589) (cs599 := cs599) (v621 := v621) (m624 := m624)
      (v651 := v651) (m652 := m652) (v673 := x_ta) (m674 := m674) (cs684 := cs684)
      (m704 := m704) (v746 := x_ca) (m747 := m747) (cs757 := cs757)
      (m784 := m784) (v839 := x_recs) (m840 := m840) (cs850 := cs850)
      (m_qvdvjtit := m_qv) (v861 := v_nrecs) (m862 := m862) (cs872 := cs872)
      (x_rec_models := x_rm) (x_s8 := x_s8) (v926 := x_v1) (v977 := x_v2)
      (m_lukcasbb := m_lu) (m1191 := m1191) (cs1201 := cs1201) (x_bnl := x_bnl)
      (x_univ_offset := x_uo) (v_qwfkpklj := v_flat) (m_ialrkdmk := m_flat) (cs_pblrtsmj := cs_flat)
      (v1233 := r_cna) (m1234 := m1234) (cs1244 := cs1244) (y_xxqgtlpp := v_flen) (m_soowcubw := m_so)
      (cs_owchsduj := cs_flen) (v_arypxepi := v_sub) (v_tabgyphp := v_comp)
      (m_gmcvdxbt := m_gm) (x_gwlxyjol := v_z0) (m_jbcuvwlm := m_jb)
      (y_svqhibng := v_vg) (m_yarikpkl := m_ya) (v_tpfunfpk := v_eok)
      (x_eezzidwb := v_add) (y_jggqqrgl := v_mul) (v_btzwyhmz := v_or)
      (m1293 := m1293) (v1330 := r_cr) (m1331 := m_cr_out) (cs1341 := cs1341)
      (sg_barfcuni := sg1) (ev126 := e1) (ev148 := e2) (ev194 := e3) (ev_yqjbwijz := e4)
      (ev231 := e5) (ev266 := e6) (ev309 := e7) (ev344 := e8) (ev403 := e9)
      (ev435 := e10) (ev465 := e11) (ev513 := ev_blk) (ev601 := ev_mlen)
      (ev634 := ev_icnt) (heq650 := heq_icnt) (ev664 := ev_bnp) (ev686 := ev_bra)
      (ev716 := e16) (ev759 := ev_bca) (ev817 := e18) (ev796 := e19) (ev852 := ev_fr)
      (ev_ursqbimm := f1) (ev_srfmazjk := f2) (ev874 := ev_rlen) (ev896 := f4)
      (ev960 := f5) (ev939 := f6) (ev1011 := f7) (ev990 := f8)
      (ev_edyzsqzv := f9) (ev_gkddqxhv := f10) (ev_ittpynob := f11) (ev_biaifgpd := f12)
      (ev1203 := ev_belim) (ev_cwwgzxtj := ev_bfb) (ev1246 := ev_cna) (ev_mitevvsv := ev_flen)
      (op_jmfoqaec := op_sub) (ev_rqpeovbn := ev_zcomp) (ev_xrhmaojz := ev_znr)
      (ev_whimdwjd := ev_vg) (op_qfbltjlu := op_1mvg) (op_cnutjuwu := op_eok)
      (op_ymhwloon := op_add) (op_mvhbzaru := op_mul) (op_zaucahqq := op_or)
      (heq_sujkqzii := heq_or) (ev1305 := ev_fro) (ev1343 := ev_cr) (hc1474 := hc) .. =>
    -- Peel all needed subcall proofs linearly from hc, then drop hc immediately
    have hrest : ∀ cl ∈ cs, cl ∈ calls := hsub_cf
    rw [hc] at hrest
    clear hc hsub_cf ev_cf
    have hrest := sub_drop (sub_drop (sub_drop (sub_drop (sub_drop (sub_drop
      (sub_drop (sub_drop (sub_drop (sub_drop (sub_drop (sub_drop hrest)))))))))))
    obtain ⟨hsub511, -, hrest⟩ := sub_take hrest
    have hrest := sub_drop (sub_drop (sub_drop hrest))
    obtain ⟨hsub684, -, hrest⟩ := sub_take hrest
    have hrest := sub_drop hrest
    obtain ⟨hsub757, -, hrest⟩ := sub_take hrest
    have hrest := sub_drop (sub_drop hrest)
    obtain ⟨hsub850, -, hrest⟩ := sub_take hrest
    have hrest := sub_drop hrest
    obtain ⟨-, hmem_rlen, hrest⟩ := sub_take hrest
    have hrest := sub_drop (sub_drop (sub_drop (sub_drop (sub_drop
      (sub_drop (sub_drop (sub_drop (sub_drop (sub_drop hrest)))))))))
    obtain ⟨hsub1201, -, hrest⟩ := sub_take hrest
    obtain ⟨hsub_flat, -, hrest⟩ := sub_take hrest
    obtain ⟨hsub1244, hmem_flen, hrest⟩ := sub_take hrest
    have hrest := sub_drop (sub_drop (sub_drop (sub_drop hrest)))
    obtain ⟨-, -, hsub1341⟩ := sub_take hrest
    have ext_sg1 : Heap.Extends h m105 := by
      cases sg1 with
      | Nil _ _ evax _ hh _ => rw [hh]; exact evax.heap_extends
      | Node _ _ _ _ _ _ _ _ evax ev_wo _ => exact evax.heap_extends.trans ev_wo.heap_extends
    have ext_h_453 : Heap.Extends h m453 :=
      ext_sg1.trans <| e1.heap_extends.trans <| e2.heap_extends.trans <| e3.heap_extends.trans <|
        e4.heap_extends.trans <| e5.heap_extends.trans <| e6.heap_extends.trans <|
        e7.heap_extends.trans <| e8.heap_extends.trans <| e9.heap_extends.trans <|
        e10.heap_extends.trans e11.heap_extends
    have ext_501_652 : Heap.Extends m501 m652 :=
      ev_mlen.heap_extends.trans (ev_icnt.heap_extends.trans ev_bnp.heap_extends)
    have ext_652_704 : Heap.Extends m652 m704 := ev_bra.heap_extends.trans e16.heap_extends
    have ext_704_784 : Heap.Extends m704 m784 :=
      ev_bca.heap_extends.trans (e18.heap_extends.trans e19.heap_extends)
    have ext_674_lu : Heap.Extends m674 m_lu :=
      e16.heap_extends.trans <| ext_704_784.trans <| ev_fr.heap_extends.trans <|
        f1.heap_extends.trans <| f2.heap_extends.trans <| ev_rlen.heap_extends.trans <|
        f4.heap_extends.trans <| f5.heap_extends.trans <| f6.heap_extends.trans <|
        f7.heap_extends.trans <| f8.heap_extends.trans <| f9.heap_extends.trans <|
        f10.heap_extends.trans <| f11.heap_extends.trans f12.heap_extends
    have ext_840_1293 : Heap.Extends m840 m1293 :=
      f1.heap_extends.trans <| f2.heap_extends.trans <| ev_rlen.heap_extends.trans <|
        f4.heap_extends.trans <| f5.heap_extends.trans <| f6.heap_extends.trans <|
        f7.heap_extends.trans <| f8.heap_extends.trans <| f9.heap_extends.trans <|
        f10.heap_extends.trans <| f11.heap_extends.trans <| f12.heap_extends.trans <|
        ev_belim.heap_extends.trans <| ev_bfb.heap_extends.trans <| ev_cna.heap_extends.trans <|
        ev_flen.heap_extends.trans <| ev_zcomp.heap_extends.trans <| ev_znr.heap_extends.trans <|
        ev_vg.heap_extends.trans ev_fro.heap_extends
    have ext_674_1293 : Heap.Extends m674 m1293 :=
      ext_674_lu.trans <| ev_belim.heap_extends.trans <| ev_bfb.heap_extends.trans <|
        ev_cna.heap_extends.trans <| ev_flen.heap_extends.trans <| ev_zcomp.heap_extends.trans <|
        ev_znr.heap_extends.trans <| ev_vg.heap_extends.trans ev_fro.heap_extends
    have ext_h_784 : Heap.Extends h m784 :=
      ext_h_453.trans <| ev_blk.heap_extends.trans <| ext_501_652.trans <|
        ext_652_704.trans ext_704_784
    have ext_h_1191 : Heap.Extends h m1191 :=
      ext_h_453.trans <| ev_blk.heap_extends.trans <| ext_501_652.trans <|
        ev_bra.heap_extends.trans <| ext_674_lu.trans ev_belim.heap_extends
    have ext_h_1293 : Heap.Extends h m1293 :=
      ext_h_784.trans (ev_fr.heap_extends.trans ext_840_1293)
    -- Block B: cb, msB, all inductive, nonempty, FamBlockRecord E₀ B cb msB
    obtain ⟨cb, msB, hblB, hrep_msB⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_h_453 hbB) ev_blk
    obtain ⟨hcbE, hmsB⟩ := (hblB.mono hsub511).stored hH
    obtain ⟨-, -, -, hmsB_lt⟩ :=
      Decl.load_block_info hS (Bytes.repAddressRef_heapMono₂ addrTy ext_h_453 hbB) ev_blk
        hsub511 hcbE hmsB
    have hmsB_len_v : v588 = .field (msB.toList.length : F) := by
      have ev' : ObsFn W (Instance.mk "Lists::length" [.named "Ixon::MutConst" []]).symbol
          [x_members] m501 v588 m589 cs599 := by
        rw [Obs.Names.«Lists::length<Ixon::MutConst>».symbol]; exact ev_mlen
      have hr' : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
          Ingress.RepMutConst m501 msB.toList x_members := by
        rw [Obs.Names.«Lists::Node<Ixon::MutConst>».symbol]; exact hrep_msB
      exact (Lib.Lists.length_spec ev' hr').1
    obtain ⟨hindV, -⟩ := Core.ModeledAux.muts_indc_count_spec
      (Route.membersRep_of_repMutConstList (RepLinkedList.mono Ingress.repMutConst_heapMono₂ ev_mlen.heap_extends hrep_msB))
      ev_icnt
    have hall_indc : ∀ m ∈ msB.toList, ∃ ind, m = .indc ind := by
      have hfilt_len : (msB.toList.filter Core.Specs.Callees.isIndc).length = msB.toList.length := by
        have he : ((msB.toList.filter Core.Specs.Callees.isIndc).length : F) = (msB.toList.length : F) :=
          Value.field.inj (hindV.symm.trans (heq_icnt.trans hmsB_len_v))
        have hle := List.length_filter_le Core.Specs.Callees.isIndc msB.toList
        have hlt : msB.toList.length < 8589934592 := by simpa only [Array.length_toList] using hmsB_lt
        exact Core.ModeledAux.natCast_inj_lt (by omega) (by omega) he
      intro m hm
      have hfl := List.filter_eq_self.mpr (by
        have := List.length_filter_eq_length_iff (p := Core.Specs.Callees.isIndc) (l := msB.toList)
        exact this.mp hfilt_len)
      have hm' : Core.Specs.Callees.isIndc m = true :=
        (List.mem_filter.mp (hfl ▸ hm)).2
      cases m with
      | indc ind => exact ⟨ind, rfl⟩
      | defn _ | recr _ => simp [Core.Specs.Callees.isIndc, Core.isIndc] at hm'
    have hmsB_ne : 0 < msB.size := by
      match Obs.«KernelModeled::block_nparams».obs ev_bnp with
      | .run (ld12 := ld12) .. =>
        obtain ⟨z, zs, hz, -, -⟩ := Lib.rep_cons_of_load
          (RepLinkedList.mono Ingress.repMutConst_heapMono₂
            (ev_mlen.heap_extends.trans ev_icnt.heap_extends) hrep_msB) ld12
        have hlen : msB.toList.length = zs.length + 1 := by rw [hz]; rfl
        rw [← Array.length_toList, hlen]; exact Nat.succ_pos _
    obtain ⟨ind₀, hms0⟩ : ∃ ind₀, msB[0]? = some (.indc ind₀) := by
      have h0 := Array.getElem?_eq_getElem hmsB_ne
      obtain ⟨ind₀, hind₀⟩ := hall_indc msB[0] (Array.mem_toList_iff.mpr (Array.getElem_mem hmsB_ne))
      rw [hind₀] at h0; exact ⟨ind₀, h0⟩
    -- block_nparams_spec
    obtain ⟨np, hnp_lt, hnp_v, hnp_all⟩ := block_nparams_spec
      (RepLinkedList.mono Ingress.repMutConst_heapMono₂
        (ev_mlen.heap_extends.trans ev_icnt.heap_extends) hrep_msB) ev_bnp
    subst hnp_v
    -- build_recur_addrs_hashed_spec => type_addrs + FamBlockRecord.members in E₀
    obtain ⟨-, as_t, has_t, has_t_len, has_t_mem⟩ := build_recur_addrs_hashed_spec
      (Route.membersRep_of_repMutConstList
        (RepLinkedList.mono Ingress.repMutConst_heapMono₂ ext_501_652 hrep_msB))
      (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_453.trans (ev_blk.heap_extends.trans ext_501_652)) hbB)
      ev_bra
    have hB_members : ∀ i m, msB[i]? = some m →
        recordOf E₀ (memberAddr (ixAddr bB) i m) = some (memberProjection (ixAddr bB) i m) := by
      intro i m hm
      have hi_lt : i < as_t.length := by rw [has_t_len, Array.length_toList]; exact (Array.getElem?_eq_some_iff.mp hm).1
      obtain ⟨m', hm', -, ha_i, hh_i⟩ := has_t_mem i as_t[i] (List.getElem?_eq_getElem hi_lt)
      rw [← Array.getElem?_toList] at hm
      have hm_eq : m' = m := Option.some.inj (hm'.symm.trans hm); subst m'
      obtain ⟨ind, rfl⟩ := hall_indc m (List.mem_of_getElem? hm)
      exact stored_of_hashed_iprj hH (Core.hashed_mono hsub684 hh_i)
    -- block_ctor_addrs_hashed_spec => FamBlockRecord.ctors in E₀
    have hct_sz : ∀ m ∈ msB.toList, ∀ ind, m = .indc ind → ind.ctors.size < 72057594037927936 := by
      intro m hm ind hmi; subst hmi
      obtain ⟨bytesB, hszB, -, -, hexB, -⟩ := hblB
      obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hm
      have hget : msB.toList[i]? = some (.indc ind) := by
        rw [List.getElem?_eq_getElem hi_lt, hi_eq]
      have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytesB cb hexB
      have hle := Claim.ctors_size_le hmsB hget
      omega
    have hB_ctors : ∀ i ind j, msB[i]? = some (.indc ind) → j < ind.ctors.size →
        recordOf E₀ (ctorAddr (ixAddr bB) i j) = some (constructorProjection (ixAddr bB) i j) := by
      intro i ind j hi hj
      have hh := block_ctor_addrs_hashed_spec (t := t) msB.toList 0
        (by rw [Nat.zero_add, Array.length_toList]; exact Nat.lt_trans hmsB_lt (by decide)) hct_sz
        (RepLinkedList.mono Ingress.repMutConst_heapMono₂ (ext_501_652.trans ext_652_704) hrep_msB)
        (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_453.trans (ev_blk.heap_extends.trans (ext_501_652.trans ext_652_704))) hbB)
        (by rw [Nat.cast_zero]; exact ev_bca) i ind j (by rw [Array.getElem?_toList]; exact hi) hj
      rw [Nat.zero_add] at hh
      exact stored_of_hashed_cprj hH (Core.hashed_mono hsub757 hh)
    have hBlock : FamBlockRecord E₀ (ixAddr bB) cb msB :=
      ⟨hcbE, hmsB, hall_indc, hBLogic cb hcbE, hB_members, hB_ctors⟩
    -- family_recs_muts_list => as_r
    obtain ⟨as_r, has_r, has_r_len, has_r_mem⟩ := family_recs_muts_list hS
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_784 hbR) ev_fr
      hsub850 hRec.record hRec.muts
    have has_r_recr : ∀ i a, as_r[i]? = some a →
        ∃ r, rs[i]? = some (.recr r) ∧ ixAddr a = memberAddr (ixAddr bR) i (.recr r) := by
      intro i a hi
      obtain ⟨m, hm, -, ha, -⟩ := has_r_mem i a hi
      obtain ⟨rc, rfl⟩ := hRec.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
      exact ⟨rc, hm, by rw [LoadedReads.memberAddr_eq_projAddr]; exact ha⟩
    have ev_rlen' : ObsFn W (Instance.mk "Lists::length" [(Generic.Ty.field.array 32).ptr]).symbol [x_recs] m_qv
        v_nrecs m862 cs872 := by
      rw [Obs.Names.«Lists::length<&[Field; 32]>».symbol]; exact ev_rlen
    have has_r_qv := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
      (f1.heap_extends.trans f2.heap_extends) has_r
    obtain ⟨hv_nrecs, -⟩ := Lib.Lists.length_spec ev_rlen'
      (by rw [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]; exact has_r_qv)
    rw [has_r_len] at hv_nrecs; subst hv_nrecs
    have hrs_lt : rs.size < 2 ^ 39 := by
      have := RomBound.bounded_length_lt hbd hmem_rlen List.mem_cons_self has_r_qv
      rwa [has_r_len] at this
    -- block_elim_spec => bnl, off, BlockElim
    have has_t_map : as_t.map ixAddr = indcAddrs (ixAddr bB) 0 msB.toList := by
      rw [← blockRecurAddrs_eq_indcAddrs_of_all_indc (ixAddr bB) 0 msB.toList hall_indc]
      simp only [Nat.zero_add]
      apply List.ext_getElem
      · simp [has_t_len]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_mapIdx]
        have hi_t : i < as_t.length := by simpa only [List.length_map] using h1
        obtain ⟨m, hm, -, ha, -⟩ := has_t_mem i as_t[i] (List.getElem?_eq_getElem hi_t)
        have hm_eq : m = msB.toList[i]'(by rw [← has_t_len]; exact hi_t) := by
          rw [List.getElem?_eq_getElem] at hm; exact (Option.some.inj hm).symm
        rw [← hm_eq]; exact ha
    have hmemAt_B : membersAt E₀ (ixAddr bB) = some (as_t.map ixAddr) := by
      rw [has_t_map]; unfold membersAt; simp only [hcbE, hmsB]
    have has_t_held : ∀ a ∈ as_t, Held R' (ixAddr a) := by
      intro a ha
      obtain ⟨i, hi_lt, rfl⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨m, hm, -, ha_i, -⟩ := has_t_mem i as_t[i] (List.getElem?_eq_getElem hi_lt)
      have hcbR' : recordOf R' (ixAddr bB) = some cb := by
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR'B
        have := hR'agree _ _ _ hc' hcbE; subst this; exact hc'
      have hm' : msB[i]? = some m := by rwa [Array.getElem?_toList] at hm
      have hprojR' := (hcl'.2 (ixAddr bB) cb msB hcbR' hmsB i m hm').1
      rw [← LoadedReads.memberAddr_eq_projAddr] at ha_i
      rw [ha_i]; exact Option.isSome_iff_exists.mpr ⟨_, hprojR'⟩
    obtain ⟨bnl, off, hbelim_r, hbnl_lt, hoff_01, hBlockElim, hbnl_d0⟩ :=
      block_elim_spec ht hwf hS hH hbd hR'agree hcl' hlv'
        hsub1201 hmemAt_B has_t_held
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext_674_lu has_t)
        ev_belim
    injection hbelim_r with hbl; injection hbl with hbnl_eq hbl; injection hbl with huo_eq _
    subst hbnl_eq huo_eq
    have hoff : off ≤ 1 := by rcases hoff_01 with rfl | rfl <;> omega
    -- build_flat_block_spec in check_family
    obtain ⟨prim, cprim, msp, os, flat, hfrp_cf, hSprim, hcprim, hmsp, horig_cf, haux_cf, hfilt_cf,
      hos_props, hflat_rep, hflat_held⟩ :=
      build_flat_block_spec ht hwf hS hH hbd hR'agree hcl' hlv' hoff
        hsub_flat hR'rb hRec.record hRec.muts
        hR'B hcbE hmsB
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1191 hbR)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_1191 hbB) ev_bfb
    -- flat.length = rs.size (from complete + empty_ok - complete*empty_ok = 1 and rs.size ≠ 0)
    obtain ⟨hv_flen, -⟩ := flat_length_spec ev_flen (flatList_mono ev_cna.heap_extends hflat_rep)
    subst hv_flen
    have hflat_lt : flat.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbd hmem_flen List.mem_cons_self
        (flatList_mono ev_cna.heap_extends hflat_rep)
    have hflat_len : flat.length = rs.size := by
      obtain ⟨hz_nr, -⟩ := Lib.is_zero_spec ev_znr
      have hrs_neF : (rs.size : F) ≠ 0 := by
        intro h0
        have := congrArg ZMod.val h0
        rw [fval_natCast (by omega)] at this; exact hrs_ne this
      have hrs_neV : (Value.field (rs.size : F) : SourceValue F) ≠ .field 0 :=
        fun h => hrs_neF (Value.field.inj h)
      rw [ite_eq_right hrs_neV] at hz_nr; subst hz_nr
      cases v_vg with
      | field fvg =>
        simp only [evalBinOp, Except.ok.injEq] at op_1mvg
        rw [← op_1mvg] at op_eok
        simp only [evalBinOp, zero_mul, Except.ok.injEq] at op_eok
        rw [← op_eok] at op_add op_mul
        obtain ⟨hz_c, -⟩ := Lib.is_zero_spec ev_zcomp
        rw [hz_c] at op_add op_mul
        simp only [evalBinOp, add_zero, mul_zero, Except.ok.injEq] at op_add op_mul
        rw [← op_add, ← op_mul] at op_or
        simp only [evalBinOp, sub_zero, Except.ok.injEq] at op_or
        rw [← op_or] at heq_or
        have hsub0 : v_sub = .field 0 := by
          cases v_sub with
          | field fv =>
            by_cases hfv : fv = 0
            · subst hfv; rfl
            · rw [ite_eq_right (fun (h : (Value.field fv : SourceValue F) = .field 0) => hfv (Value.field.inj h))] at heq_or
              exact absurd (Value.field.inj heq_or) zero_ne_one
          | ptr _ _ | tuple _ | construct _ _ _ => simp [evalBinOp] at op_sub
        rw [hsub0] at op_sub
        have hfeq := evalBinOp_sub_eq_zero_field op_sub
        have h1 := congrArg ZMod.val hfeq
        rw [fval_natCast (by omega), fval_natCast (by omega)] at h1; exact h1.symm
      | ptr _ _ | tuple _ | construct _ _ _ => simp [evalBinOp] at op_1mvg
    exact ⟨{
      bB := bB, bR := bR, bB_eq := rfl, bR_eq := rfl,
      cb := cb, msB := msB, ind₀ := ind₀, np := np, bnl := bnl, off := off,
      prim := prim, cprim := cprim, msp := msp, os := os, flat := flat,
      as_t := as_t, as_r := as_r,
      hBlock := hBlock, hms0 := hms0, hmsB_lt := hmsB_lt, hnp_lt := hnp_lt,
      hnp_all := fun m hm ind hmi => hnp_all ind (hmi ▸ hm),
      hrs_lt := hrs_lt, hflat_lt := hflat_lt, hflat_len := hflat_len,
      hbnl_lt := hbnl_lt, hoff := hoff, hBlockElim := hBlockElim, hbnl_d0 := hbnl_d0,
      has_t_len := has_t_len,
      has_t_mem := fun i a hi => by
        obtain ⟨m, hm, -, ha, -⟩ := has_t_mem i a hi; exact ⟨m, hm, ha⟩,
      has_r_len := has_r_len, has_r_recr := has_r_recr,
      hfrp_cf := hfrp_cf, hSprim := hSprim, hcprim := hcprim, hmsp := hmsp,
      horig_cf := horig_cf, haux_cf := haux_cf, hfilt_cf := hfilt_cf,
      hos_props := hos_props, hflat_held := hflat_held,
      m_flat := m_flat, m_cna_out := m1234, xb_flat := xb, v_flat := v_flat,
      r_cna := r_cna, cs_cna := cs1244, hsub_cna := hsub1244,
      hbB_flat := Bytes.repAddressRef_heapMono₂ addrTy (ext_h_1191.trans ev_bfb.heap_extends) hbB,
      hflat_rep := hflat_rep, ev_cna := ev_cna,
      m_cr := m1293, m_cr_out := m_cr_out, xrc_cr := xrc,
      x_ta := x_ta, x_recs := x_recs, x_rm := x_rm, x_v1 := x_v1, x_v2 := x_v2, x_v3 := x_v3,
      x_s8 := x_s8, r_cr := r_cr, cs_cr := cs1341,
      hsub_cr := fun cl hcl => hsub1341 cl (List.mem_append_left _ hcl),
      hrc_cr := hrc.mono ext_h_1293,
      has_t_cr := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext_674_1293 has_t,
      has_r_cr := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext_840_1293 has_r,
      ev_cr := ev_cr
    }⟩

private theorem originals_map_addr_cf {V : FlatView} {off : Nat} :
    ∀ (as : List _root_.Address) (os : List FlatEntry),
      originals V off as = some os → os.map (·.addr) = as := by
  intro as
  induction as with
  | nil =>
    intro os h; simp only [originals, Option.some.injEq] at h; subst h; rfl
  | cons a rest ih =>
    intro os h
    simp only [originals] at h
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some opt =>
      cases opt with
      | none => simp [hc] at h
      | some info =>
        cases ho : originals V off rest with
        | none => simp [hc, ho] at h
        | some os' =>
          simp only [hc, ho, Option.some.injEq] at h; subst h
          simp [ih os' ho]

/-- **Core family-check theorem** unifying `familyFlat_of_call` and `familyForm_of_call` in one
pass over `KernelModeled::check_family`. -/
private theorem check_family_core {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {B rb : _root_.Address}
    {cr : Ixon.Constant} {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hRB : Held R B)
    (hrecRefs : ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
      Held R a ∨ a = rb ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr rb k m)
    (hlv : StoreLevelsOk t E₀ (Held R)) (hpar : StoreIndParamsOk E₀ (Held R))
    (hM : ModeledAnswers calls (Held R) (ReconView.ofStore t E₀))
    (hRec : FamRecRecord E₀ rb cr rs) (hrs_ne : rs.size ≠ 0)
    (hBLogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hfc : FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
      FamilyOfBlock E₀ B cb ms rb cr rs (es.map FlatEntry.addr) ∧
      RecordFlat t E₀ rb cr rs es ∧
      BlockDerivedFlat t E₀ B off es ∧
      (∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
        ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
        rc.lvls.toNat = ind₀.lvls.toNat + off) ∧
      (∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (.recr rc) →
        ctorsBefore (ReconView.ofStore t E₀) es es.length = some rc.minors.toNat) ∧
      (RFormS t E₀ B rb ∨
        (RecordWrapConsObs calls t E₀ B rb ∧ ∀ n, lim = some n → n < 77 → False)) := by
  obtain ⟨h, h', xrc, xb, xrb, r_cf, hrc, ⟨bB, hbB, hBb⟩, ⟨bR, hbR, hRb⟩, ev_cf, -, hsub_cf⟩ := hfc
  -- 1. Extend R with rb + its projections
  have hrec_lv := check_family_recr_levelsOk (t := t) hS hbd (hRb ▸ hRec.record) hRec.muts hbR ev_cf hsub_cf
  obtain ⟨R', hcl', hRmono, hR'agree, -, hR'rb, hR'held_iff, hlv', hpar'⟩ :=
    addRecBlockStore hcl hRagree hlv hpar hRec hrecRefs (by rwa [hRb] at hrec_lv)
  have hR'B : Held R' B := by
    obtain ⟨cB, hcB⟩ := Option.isSome_iff_exists.mp hRB
    exact Option.isSome_iff_exists.mpr ⟨cB, hRmono _ _ hcB⟩
  have hM' : ModeledAnswers calls (Held R') (ReconView.ofStore t E₀) :=
    modeledAnswers_addRecBlock hS hRec hR'held_iff hM
  -- 2. Unpack check_family into a clean, compact record (dropping hc1474 and ~190 binders)
  obtain ⟨u⟩ := check_family_unpack ht hwf hS hH hbd hR'agree hcl' hR'B hR'rb hlv'
    hRec hrs_ne hBLogic hrc hbB hBb hbR hRb ev_cf hsub_cf
  clear hrec_lv h h' xrc xb xrb r_cf hrc bB hbB hBb bR hbR hRb ev_cf hsub_cf
  obtain ⟨bB, bR, rfl, rfl, cb, msB, ind₀, np, bnl, off, prim, cprim, msp, os, flat, as_t, as_r,
    hBlock, hms0, hmsB_lt, hnp_lt, hnp_all, hrs_lt, hflat_lt, hflat_len, hbnl_lt, hoff,
    hBlockElim, hbnl_d0, has_t_len, has_t_mem, has_r_len, has_r_recr,
    hfrp_cf, hSprim, hcprim, hmsp, horig_cf, haux_cf, hfilt_cf, hos_props, hflat_held,
    m_flat, m_cna_out, xb_flat, v_flat, r_cna, cs_cna, hsub_cna, hbB_flat, hflat_rep, ev_cna,
    m_cr, m_cr_out, xrc_cr, x_ta, x_recs, x_rm, x_v1, x_v2, x_v3, x_s8, r_cr, cs_cr,
    hsub_cr, hrc_cr, has_t_cr, has_r_cr, ev_cr⟩ := u
  have hcbE := hBlock.record
  have hmsB := hBlock.muts
  have hall_indc := hBlock.indcs
  have ev_cr0 : ObsFn W "KernelModeled::check_recs"
      [xrc_cr, x_ta, x_recs, x_rm, x_v1, x_v2, x_v3, x_s8,
        .field (rs.size : F), .field ((0 : Nat) : F), .field (np : F), .field (off : F),
        .field (bnl : F), x_recs, .field 0] m_cr r_cr m_cr_out cs_cr := by
    rw [Nat.cast_zero]; exact ev_cr
  -- Step A: k = 0 => prim = B, BlockDerivedFlat
  obtain ⟨t0, trest, has_t_cons⟩ := List.exists_cons_of_ne_nil (show as_t ≠ [] by
    intro h0; rw [h0] at has_t_len; simp at has_t_len
    have := (Array.getElem?_eq_some_iff.mp hms0).1; omega)
  obtain ⟨a0, rrest, has_r_cons⟩ := List.exists_cons_of_ne_nil (show as_r ≠ [] by
    intro h0; rw [h0] at has_r_len; simp at has_r_len; exact hrs_ne has_r_len.symm)
  have ht0_addr : ixAddr t0 = memberAddr (ixAddr bB) 0 (.indc ind₀) := by
    obtain ⟨m, hm, ha⟩ := has_t_mem 0 t0 (by rw [has_t_cons]; rfl)
    have hms0' : msB.toList[0]? = some (.indc ind₀) := by rw [Array.getElem?_toList]; exact hms0
    have := Option.some.inj (hm.symm.trans hms0'); subst this
    rw [LoadedReads.memberAddr_eq_projAddr]; exact ha
  obtain ⟨r₀, hrs0, ha0_addr⟩ := has_r_recr 0 a0 (by rw [has_r_cons]; rfl)
  have hfrp_B := check_recs_head_prim_eq ht hwf hS hH hbd hR'agree hcl' hlv' hBlock hRec hR'rb
    hrs_lt hnp_lt hoff hbnl_lt hms0 ht0_addr hrs0 ha0_addr
    (has_t_cons ▸ has_t_cr) (has_r_cons ▸ has_r_cr) hsub_cr ev_cr0
  have hprim_eq : prim = ixAddr bB := Option.some.inj (hfrp_cf.symm.trans (hfrp_B (ixAddr bB)))
  subst prim
  have hcprim_eq : cprim = cb := Option.some.inj (hcprim.symm.trans hcbE); subst cprim
  have hmsp_eq : msp = msB := Ixon.ConstantInfo.muts.inj (hmsp.symm.trans hmsB); subst msp
  -- BlockDerivedFlat from check_nested_aux_spec
  obtain ⟨n_der, hder⟩ := check_nested_aux_spec ht hwf hS hH hbd hR'agree hcl' hlv'
    hsub_cna (by unfold membersAt; simp only [hcbE, hmsB])
    horig_cf hfilt_cf hbB_flat hflat_rep hflat_held ev_cna
  have hBDF : BlockDerivedFlat t E₀ (ixAddr bB) off flat := ⟨hBlockElim, n_der, hder⟩
  -- bnl = ind₀.lvls.toNat
  have hbnl_ind0 : bnl = ind₀.lvls.toNat := by
    obtain ⟨d0, hd0, hbnl_d⟩ := hbnl_d0 t0 trest has_t_cons
    rw [ht0_addr] at hd0
    obtain ⟨-, ca0, p0, cb0, ms0, ind0', hca0, hci0, hcb0, hms0', hm0', hnl0, -, -, -, hblk0, hidx0⟩ :=
      indInfoAt_of_indDataAt hd0
    have hproj0 := hBlock.members 0 (.indc ind₀) hms0
    have hca_eq := Option.some.inj (hca0.symm.trans hproj0); subst hca_eq
    simp only [memberProjection, Ixon.ConstantInfo.iPrj.injEq] at hci0; subst hci0
    have hcb_eq := Option.some.inj (hcb0.symm.trans hcbE); subst hcb_eq
    have hms_eq := Ixon.ConstantInfo.muts.inj (hms0'.symm.trans hmsB); subst hms_eq
    have hm_eq := Ixon.MutConst.indc.inj (Option.some.inj (hm0'.symm.trans hms0)); subst hm_eq
    exact hbnl_d.trans hnl0
  -- Step B (Pass 1)
  have hP1 := check_recs_pass1 ht hwf hS hH hbd hR'agree hcl' hlv' hBlock hRec hR'rb hrs_lt
    hnp_lt hoff hbnl_lt hfrp_B horig_cf haux_cf as_r 0 (by simp [has_r_len])
    (fun i a hi => by simpa only [Nat.zero_add] using has_r_recr i a hi)
    has_r_cr hsub_cr ev_cr0
  -- FamilyOfBlock
  have hos_len : os.length = msB.size := by
    have hmap := originals_map_addr_cf _ os horig_cf
    have hlen1 := congrArg List.length hmap
    simp only [List.length_map] at hlen1
    rw [hlen1, ← blockRecurAddrs_eq_indcAddrs_of_all_indc (ixAddr bB) 0 msB.toList hall_indc]
    simp
  obtain ⟨auxs, hflat_app, hauxs_true⟩ := buildFlatAuxStep_append_aux rs.toList 0 os flat haux_cf
  have hFOB : FamilyOfBlock E₀ (ixAddr bB) cb msB (ixAddr bR) cr rs (flat.map FlatEntry.addr) := {
    block := hBlock
    record := hRec
    covers := by simp [hflat_len]
    originals := fun i m hm => by
      have hmap := originals_map_addr_cf _ os horig_cf
      have hi_lt : i < os.length := by rw [hos_len]; exact (Array.getElem?_eq_some_iff.mp hm).1
      rw [List.getElem?_map, hflat_app, List.getElem?_append_left hi_lt, ← List.getElem?_map, hmap]
      rw [← blockRecurAddrs_eq_indcAddrs_of_all_indc (ixAddr bB) 0 msB.toList hall_indc,
        List.getElem?_mapIdx, Array.getElem?_toList]
      simp only [Nat.zero_add, hm, Option.map_some, LoadedReads.memberAddr_eq_projAddr]
    motives := fun k rc hk => by
      have := (hP1 k rc (Nat.zero_le _) hk).2.1
      simpa using this
    carriers := fun k rc hk j a ha => by
      rw [List.getElem?_map] at ha
      cases hej : flat[j]? with
      | none => rw [hej] at ha; cases ha
      | some ej =>
        rw [hej] at ha; injection ha with hja; subst hja
        exact (hP1 k rc (Nat.zero_le _) hk).2.2.2.2.2.1 j ej hej
    major := fun k rc a hk ha => by
      rw [List.getElem?_map] at ha
      cases hek : flat[k]? with
      | none => rw [hek] at ha; cases ha
      | some ek =>
        rw [hek] at ha; injection ha with hka; subst hka
        exact (hP1 k rc (Nat.zero_le _) hk).2.2.2.2.2.2.1 ek hek
  }
  -- Pigeonhole on buildFlatAuxStep => exact auxiliary entries + FlatEntryParamsOk
  have hms_le_rs : msB.size ≤ rs.size := hFOB.types_le
  have hpre_skip : buildFlatAuxStep t E₀ (ixAddr bR) cr rs (ixAddr bB) msB.size
      (rs.toList.drop msB.size) os = some flat := by
    have hsplit : rs.toList = rs.toList.take msB.size ++ rs.toList.drop msB.size :=
      (List.take_append_drop msB.size rs.toList).symm
    have haux' : buildFlatAuxStep t E₀ (ixAddr bR) cr rs (ixAddr bB) 0
        (rs.toList.take msB.size ++ rs.toList.drop msB.size) os = some flat := by
      rwa [← hsplit]
    have htake_len : (rs.toList.take msB.size).length = msB.size := by
      rw [List.length_take, Array.length_toList]; exact Nat.min_eq_left hms_le_rs
    have hres := buildFlatAuxStep_skip_prefix (rs.toList.take msB.size) (rs.toList.drop msB.size)
      0 os flat haux' (fun j rc hj => by
        have hj_lt : j < msB.size := by
          have := (List.getElem?_eq_some_iff.mp hj).1; omega
        have hj_rs : rs[j]? = some (.recr rc) := by
          rw [List.getElem?_take_of_lt hj_lt, Array.getElem?_toList] at hj; exact hj
        obtain ⟨ty, d, us, pa, pInfo, hty, hd, hfn, hpInfo, -, -, hfk⟩ :=
          (hP1 j rc (Nat.zero_le _) hj_rs).2.2.2.2.2.2.2
        obtain ⟨hinfo, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := indInfoAt_of_indDataAt hpInfo
        have hm_j : msB[j]? = some msB[j] := Array.getElem?_eq_getElem hj_lt
        obtain ⟨ind_j, hind_j⟩ := hall_indc msB[j] (Array.mem_toList_iff.mpr (Array.getElem_mem hj_lt))
        rw [hind_j] at hm_j
        have hfk_orig := hFOB.originals j (.indc ind_j) hm_j
        rw [List.getElem?_map] at hfk_orig
        have hpa_eq : ixAddr pa = memberAddr (ixAddr bB) j (.indc ind_j) :=
          Option.some.inj (hfk.symm.trans hfk_orig)
        have hblk_eq : pInfo.blk = ixAddr bB := by
          obtain ⟨-, ca, pr, -, -, -, hca, hci, -, -, -, -, -, -, -, hblk, -⟩ :=
            indInfoAt_of_indDataAt hpInfo
          rw [hpa_eq] at hca
          have hca_eq := Option.some.inj (hca.symm.trans (hBlock.members j (.indc ind_j) hm_j))
          rw [hca_eq] at hci
          simp only [memberProjection, Ixon.ConstantInfo.iPrj.injEq] at hci
          rw [hblk, ← hci]
        exact ⟨ty, d, Core.keyOf t (ixAddr pa), us, ixAddr pa, _, by simpa using hty, hd, hfn,
          keyAddr_keyOf hwf _, hinfo, hblk_eq⟩)
    rwa [Nat.zero_add, htake_len] at hres
  have haux_exact := buildFlatAuxStep_strict_suffix (rs.toList.drop msB.size) msB.size os flat
    hpre_skip (by rw [hflat_len, hos_len, List.length_drop, Array.length_toList]; omega)
  have hflat_ind_all : ∀ e ∈ flat, Held R' e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
      (∀ p ∈ e.params, AddrIn (Held R') (Core.keyOf t) p) :=
    (hP1 0 r₀ (Nat.zero_le _) hrs0).2.2.2.2.1
  have hall_ok : ∀ e ∈ flat, Held R' e.addr ∧ (∃ info, indDataAt t E₀ e.addr = some (some info)) ∧
      (∀ p ∈ e.params, AddrIn (Held R') (Core.keyOf t) p) ∧
      FlatEntryParamsOk (ReconView.ofStore t E₀) np e := by
    intro e he
    refine ⟨(hflat_ind_all e he).1, (hflat_ind_all e he).2.1, (hflat_ind_all e he).2.2, ?_⟩
    intro d hd
    obtain ⟨-, ca_e, p_e, cb_e, ms_e, ind_e, hca_e, hci_e, hcb_e, hms_e, hm_e,
      -, hd_np, -, -, hd_blk, hd_idx⟩ := indInfoAt_of_indDataAt hd
    refine ⟨?_, ?_, ?_⟩
    · intro haux_f
      have he_os : e ∈ os := by
        rw [← hfilt_cf]; exact List.mem_filter.mpr ⟨he, by simp [haux_f]⟩
      obtain ⟨-, -, -, idx_e, ind_e', hget_e, he_mem⟩ := hos_props e he_os
      rw [he_mem] at hca_e
      have hca_eq := Option.some.inj (hca_e.symm.trans (hBlock.members idx_e (.indc ind_e') hget_e))
      rw [hca_eq] at hci_e
      simp only [memberProjection, Ixon.ConstantInfo.iPrj.injEq] at hci_e; subst p_e
      have hcb_eq := Option.some.inj (hcb_e.symm.trans hcbE); subst hcb_eq
      have hms_eq := Ixon.ConstantInfo.muts.inj (hms_e.symm.trans hmsB); subst hms_eq
      have hi64 : idx_e.toUInt64.toNat = idx_e := by
        have := (Array.getElem?_eq_some_iff.mp hget_e).1
        have h64 : UInt64.size = 18446744073709551616 := rfl
        change (UInt64.ofNat idx_e).toNat = idx_e
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      rw [hi64] at hm_e
      have hind_eq := Ixon.MutConst.indc.inj (Option.some.inj (hm_e.symm.trans hget_e)); subst hind_eq
      have hnp_e := hnp_all (.indc ind_e) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget_e)) ind_e rfl
      rw [hd_np, hnp_e]
    · intro haux_t
      obtain ⟨k, hk_lt, rfl⟩ := List.mem_iff_getElem.mp he
      have hk_ge : msB.size ≤ k := by
        by_contra hlt
        have hko : k < os.length := by omega
        have he_os : flat[k] ∈ os := by
          have hget : flat[k]? = os[k]? := by rw [hflat_app, List.getElem?_append_left hko]
          rw [List.getElem?_eq_getElem hk_lt, List.getElem?_eq_getElem hko] at hget
          rw [Option.some.inj hget]; exact List.getElem_mem hko
        have := (hos_props flat[k] he_os).1
        rw [this] at haux_t; cases haux_t
      have hk_rs_lt : k < rs.size := by omega
      obtain ⟨rc_k, hrc_k⟩ : ∃ rc_k, rs[k]? = some (.recr rc_k) := by
        have h1 := Array.getElem?_eq_getElem hk_rs_lt
        obtain ⟨rc_k, hrc⟩ := hRec.recrs rs[k] (Array.mem_toList_iff.mpr (Array.getElem_mem hk_rs_lt))
        rw [hrc] at h1; exact ⟨rc_k, h1⟩
      have hdrop_get : (rs.toList.drop msB.size)[k - msB.size]? = some (.recr rc_k) := by
        rw [List.getElem?_drop, Array.getElem?_toList, show msB.size + (k - msB.size) = k by omega]
        exact hrc_k
      obtain ⟨ty_a, d_a, k_a, us_a, paddr_a, info_a, hty_a, hd_a, hfn_a, hka_a, hinfo_a, hget_a⟩ :=
        haux_exact (k - msB.size) rc_k hdrop_get
      rw [show os.length + (k - msB.size) = k by omega, List.getElem?_eq_getElem hk_lt] at hget_a
      injection hget_a with hflat_k_eq
      obtain ⟨ty_1, d_1, us_1, pa_1, pInfo_1, hty_1, hd_1, -, hpInfo_1, -, hpnp_le_1, hfk_1⟩ :=
        (hP1 k rc_k (Nat.zero_le _) hrc_k).2.2.2.2.2.2.2
      rw [show msB.size + (k - msB.size) = k by omega] at hty_a
      have hty_eq : ty_a = ty_1 := Option.some.inj (hty_a.symm.trans hty_1); subst hty_eq
      have hd_eq : d_a = d_1 := Option.some.inj (hd_a.symm.trans hd_1); subst hd_eq
      have hpa_eq : paddr_a = ixAddr pa_1 := by
        rw [List.getElem?_eq_getElem hk_lt, hflat_k_eq] at hfk_1
        exact Option.some.inj hfk_1
      subst hpa_eq
      have hd_eq_p : d = pInfo_1 := by
        rw [hflat_k_eq] at hd
        exact Option.some.inj (Option.some.inj (hd.symm.trans hpInfo_1))
      subst hd_eq_p
      obtain ⟨hinfo_1, -⟩ := indInfoAt_of_indDataAt hpInfo_1
      have hinfo_eq := Option.some.inj (Option.some.inj (hinfo_a.symm.trans hinfo_1)); subst hinfo_eq
      rw [hflat_k_eq]
      simp only [List.length_map, List.length_take]
      exact Nat.le_min.mpr ⟨Nat.le_refl _, hpnp_le_1⟩
    · intro c cty cnp hctor
      unfold ReconView.ofStore ctorAt at hctor
      simp only [hd_blk, hd_idx, hcb_e, hms_e, hm_e] at hctor
      cases hct : ind_e.ctors[c]? with
      | none => simp only [hct] at hctor; cases hctor
      | some ct =>
        simp only [hct] at hctor
        cases hld : loadedAt t (fun x => E₀.blobs.get? x) cb_e (blockSelf t p_e.block ms_e)
            ct.lvls.toNat (mutsRoot ms_e p_e.idx.toNat + 1 + ((c : Nat) : F)) ct.typ with
        | none => simp only [hld] at hctor; cases hctor
        | some cty' =>
          simp only [hld, Option.some.injEq, Prod.mk.injEq] at hctor
          have hR'e : recordOf R' e.addr = some ca_e := by
            obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (hflat_ind_all e he).1
            have := hR'agree _ _ _ hc' hca_e; subst this; exact hc'
          have hR'blk : Held R' p_e.block := by
            simpa [Ix.Cert.ownerOf, hci_e] using (hcl'.1 e.addr ca_e hR'e).1
          have hpeq := hpar'.ctorParams p_e.block cb_e ms_e p_e.idx.toNat ind_e c ct
            hR'blk hcb_e hms_e hm_e hct
          rw [← hctor.2, hpeq, hd_np]
  -- Step C1 (Pass 2)
  obtain ⟨tot, htot_flat⟩ : ∃ tot, flatTotalCtors (ReconView.ofStore t E₀) flat = some tot :=
    ⟨r₀.minors.toNat, (hP1 0 r₀ (Nat.zero_le _) hrs0).2.2.2.1⟩
  have hflat_ne : flat ≠ [] := by intro h0; rw [h0] at hflat_len; exact hrs_ne hflat_len.symm
  obtain ⟨hRF_heads, hForm_disj⟩ := check_recs_pass2 ht hwf hS hH hbd hR'agree hcl' hlv' hM'
    hBlock hRec hR'rb hrs_lt hnp_lt hoff hbnl_lt hfrp_B horig_cf haux_cf htot_flat hflat_ne hall_ok
    as_r 0 (by simp [has_r_len]) (fun i a hi => by simpa only [Nat.zero_add] using has_r_recr i a hi)
    hrc_cr has_r_cr hsub_cr
    ⟨Or.inl rfl, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h => absurd (Value.field.inj h) zero_ne_one,
      fun h => absurd (Value.field.inj h) (by decide)⟩
    ev_cr0
  -- Assemble RecordFlatAux & FlatPeerDistinct
  have hRFAux : RecordFlatAux t E₀ (ixAddr bR) cr rs flat := by
    refine ⟨hflat_len, fun k hk => ?_, fun k rc e hk he => ?_⟩
    · have h1 := Array.getElem?_eq_getElem hk
      obtain ⟨rc, hrc⟩ := hRec.recrs rs[k] (Array.mem_toList_iff.mpr (Array.getElem_mem hk))
      rw [hrc] at h1; exact ⟨rc, h1⟩
    · obtain ⟨ty, d, info, hty, hd, hfn, hinfo⟩ := hRF_heads k rc e (Nat.zero_le _) hk he
      refine ⟨ty, d, info, hty, hd, hfn, hinfo, fun haux_t => ?_⟩
      have hk_ge : msB.size ≤ k := by
        by_contra hlt
        have hko : k < os.length := by omega
        have he_os : e ∈ os := by
          rw [hflat_app, List.getElem?_append_left hko] at he
          exact List.mem_of_getElem? he
        have := (hos_props e he_os).1; rw [this] at haux_t; cases haux_t
      have hdrop_get : (rs.toList.drop msB.size)[k - msB.size]? = some (.recr rc) := by
        rw [List.getElem?_drop, Array.getElem?_toList, show msB.size + (k - msB.size) = k by omega]
        exact hk
      obtain ⟨ty_a, d_a, k_a, us_a, paddr_a, info_a, hty_a, hd_a, -, -, hinfo_a, hget_a⟩ :=
        haux_exact (k - msB.size) rc hdrop_get
      rw [show msB.size + (k - msB.size) = k by omega] at hty_a
      rw [show os.length + (k - msB.size) = k by omega] at hget_a
      have he_eq := Option.some.inj (he.symm.trans hget_a); subst he_eq
      have hty_eq := Option.some.inj (hty_a.symm.trans hty); subst hty_eq
      have hd_eq := Option.some.inj (hd_a.symm.trans hd); subst hd_eq
      have hinfo_eq := Option.some.inj (Option.some.inj (hinfo_a.symm.trans hinfo)); subst hinfo_eq
      rfl
  have hPD : FlatPeerDistinct flat :=
    flatPeerDistinct_of_buildFlatAuxStep hR'agree hcl' hR'B hcbE hmsB (by omega)
      (fun idx ind hget => hBlock.members idx (.indc ind) hget)
      horig_cf (fun e he => ⟨(hos_props e he).1, (hos_props e he).2.2.2⟩) haux_cf
  -- Step C2 (Pass 3)
  have hP3 := check_recs_pass3 ht hwf hS hH hbd hR'agree hcl' hlv' hM' hBlock hRec hR'rb
    hrs_lt hnp_lt hoff hbnl_lt hfrp_B horig_cf haux_cf htot_flat hRFAux hPD
    as_r 0 (by simp [has_r_len]) (fun i a hi => by simpa only [Nat.zero_add] using has_r_recr i a hi)
    has_r_cr hsub_cr ev_cr0
  -- Merge common fuel over k < rs.size
  have hForm_out : RFormS t E₀ (ixAddr bB) (ixAddr bR) ∨
      (RecordWrapConsObs calls t E₀ (ixAddr bB) (ixAddr bR) ∧ ∀ n, lim = some n → n < 77 → False) := by
    have build_recon : ∀ (TyRel : KExpr → KExpr → Prop),
        (∀ k < rs.size, ∀ rc, rs[k]? = some (.recr rc) →
          ∃ ty Rty, loadedAt t (fun x => E₀.blobs.get? x) cr (blockSelf t (ixAddr bR) rs) rc.lvls.toNat
            (mutsRoot rs k) rc.typ = some ty ∧
            Eventually (fun f => recTypeAt (ReconView.ofStore t E₀) f flat off rc.params.toNat k = some Rty) ∧
            TyRel ty Rty) →
        RecordReconWith TyRel t E₀ (ixAddr bB) (ixAddr bR) := by
      intro TyRel hTy
      have hall_ev : ∀ k < rs.size, Eventually (fun f => ∀ rc, rs[k]? = some (.recr rc) →
          MemberRecon TyRel t E₀ (ixAddr bR) cr rs flat off f k rc) := by
        intro k hk_lt
        have h1 := Array.getElem?_eq_getElem hk_lt
        obtain ⟨rc, hrc_m⟩ := hRec.recrs rs[k] (Array.mem_toList_iff.mpr (Array.getElem_mem hk_lt))
        rw [hrc_m] at h1
        obtain ⟨ty1, Rty, hty1, hev1, hrel1⟩ := hTy k hk_lt rc h1
        obtain ⟨ty2, bodies, cbk, hty2, hev2, hcbk, hrules⟩ := hP3 k rc (Nat.zero_le _) h1
        have hty_eq : ty1 = ty2 := Option.some.inj (hty1.symm.trans hty2); subst hty_eq
        refine (hev1.and hev2).mono fun f ⟨hf1, hf2⟩ rc' hrc' => ?_
        have hrc_eq := Ixon.MutConst.recr.inj (Option.some.inj (hrc'.symm.trans h1)); subst hrc_eq
        exact ⟨ty1, Rty, bodies, cbk, hty1, hf1, hrel1, hf2, hcbk, hrules⟩
      obtain ⟨fuel, hfuel⟩ := eventually_forall_range _ rs.size hall_ev
      exact ⟨cr, rs, flat, off, fuel, hRec.record, hRec.muts, hRFAux.toRecordFlat, hBDF,
        fun k rc hk => hfuel fuel (Nat.le_refl _) k (Array.getElem?_eq_some_iff.mp hk).1 rc hk⟩
    rcases hForm_disj with h1 | ⟨h2, hnot⟩
    · exact Or.inl (build_recon ExprLvEq h1)
    · exact Or.inr ⟨build_recon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty) h2, hnot⟩
  refine ⟨cb, msB, flat, off, hFOB, hRFAux.toRecordFlat, hBDF, ?_, ?_, hForm_out⟩
  · intro ind₀' k rc hm0 hk
    have hind_eq := Ixon.MutConst.indc.inj (Option.some.inj (hm0.symm.trans hms0)); subst hind_eq
    rw [← hbnl_ind0]
    exact (hP1 k rc (Nat.zero_le _) hk).2.2.1
  · intro k rc hk
    rw [← flatTotalCtors_eq_ctorsBefore_length]
    exact (hP1 k rc (Nat.zero_le _) hk).2.2.2.1

/-! ## Section 6: Public exports (`familyFlat_of_call`, `familyForm_of_call`, `groupStoresOfRun_closed`) -/

/-- **Flattened family extraction from any observed `KernelModeled::check_family` call** (at any
limit, over any `UsedClosed R` agreeing with `E₀`, without requiring `R ⊆ E₀` or `Held R r`). -/
theorem familyFlat_of_call {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {B r : _root_.Address}
    {cr : Ixon.Constant} {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hRB : Held R B)
    (hrecRefs : ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
      Held R a ∨ a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m)
    (hlv : StoreLevelsOk t E₀ (Held R)) (hpar : StoreIndParamsOk E₀ (Held R))
    (hM : ModeledAnswers calls (Held R) (ReconView.ofStore t E₀))
    (hRec : FamRecRecord E₀ r cr rs) (hrs_ne : rs.size ≠ 0)
    (hBLogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hfc : FamilyCallAtLim calls bAddr t B r lim cs) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
      FamilyOfBlock E₀ B cb ms r cr rs (es.map FlatEntry.addr) ∧
      RecordFlat t E₀ r cr rs es ∧
      BlockDerivedFlat t E₀ B off es ∧
      (∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
        ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
        rc.lvls.toNat = ind₀.lvls.toNat + off) ∧
      (∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (.recr rc) →
        ctorsBefore (ReconView.ofStore t E₀) es es.length = some rc.minors.toNat) := by
  obtain ⟨cb, ms, es, off, hFOB, hRF, hBDF, hlv_eq, hct_eq, -⟩ :=
    check_family_core ht hwf hS hH hbd hRagree hcl hRB hrecRefs hlv hpar hM hRec hrs_ne hBLogic hfc
  exact ⟨cb, ms, es, off, hFOB, hRF, hBDF, hlv_eq, hct_eq⟩

/-- **Canonical record form at a group-validating limit** (`lim = some n`, `n < 77`): unconditional
`RFormS t E₀ B r`. -/
theorem familyForm_of_call_group {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {B r : _root_.Address}
    {cr : Ixon.Constant} {rs : Array Ixon.MutConst} {n : Nat} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hRB : Held R B)
    (hrecRefs : ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
      Held R a ∨ a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m)
    (hlv : StoreLevelsOk t E₀ (Held R)) (hpar : StoreIndParamsOk E₀ (Held R))
    (hM : ModeledAnswers calls (Held R) (ReconView.ofStore t E₀))
    (hRec : FamRecRecord E₀ r cr rs) (hrs_ne : rs.size ≠ 0)
    (hBLogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hn : n < 77)
    (hfc : FamilyCallAtLim calls bAddr t B r (some n) cs) :
    RFormS t E₀ B r := by
  obtain ⟨_, _, _, _, -, -, -, -, -, hform⟩ :=
    check_family_core ht hwf hS hH hbd hRagree hcl hRB hrecRefs hlv hpar hM hRec hrs_ne hBLogic hfc
  rcases hform with h1 | ⟨-, hbot⟩
  · exact h1
  · exact (hbot n rfl hn).elim

/-- **Canonical or wrapper-consumed record form at an arbitrary limit**:
`RFormS t E₀ B r ∨ RecordWrapConsObs calls t E₀ B r`. -/
theorem familyForm_of_call {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {B r : _root_.Address}
    {cr : Ixon.Constant} {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    (hRagree : ∀ y c c', recordOf R y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R) (hRB : Held R B)
    (hrecRefs : ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
      Held R a ∨ a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m)
    (hlv : StoreLevelsOk t E₀ (Held R)) (hpar : StoreIndParamsOk E₀ (Held R))
    (hM : ModeledAnswers calls (Held R) (ReconView.ofStore t E₀))
    (hRec : FamRecRecord E₀ r cr rs) (hrs_ne : rs.size ≠ 0)
    (hBLogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb)
    (hfc : FamilyCallAtLim calls bAddr t B r lim cs) :
    RFormS t E₀ B r ∨ RecordWrapConsObs calls t E₀ B r := by
  obtain ⟨_, _, _, _, -, -, -, -, -, hform⟩ :=
    check_family_core ht hwf hS hH hbd hRagree hcl hRB hrecRefs hlv hpar hM hRec hrs_ne hBLogic hfc
  rcases hform with h1 | ⟨h2, -⟩
  · exact Or.inl h1
  · exact Or.inr h2

/-- **Discharges `RemainingFamilyClauses`** for any collision-free, bounded binding run with
`RunStepStores`. -/
theorem remainingFamilyClauses_of_run {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀) (hbd : Bounded calls)
    (hb : BasisRowsLoaded E₀) (hbr : BasisRolesStored t)
    (hax : AxiomRolesDeclared t E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hroots : RootsSafe t E₀)
    (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    RemainingFamilyClauses calls bAddr t E₀ := by
  have hwf : t.wf = true := wf_of_check hcheck
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr; cases hr
  have hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs :=
    fun k => groupWalked_exists hC.hashedStored (hvalAll k)
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hcore : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
      ∃ (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
        FamilyOfBlock E₀ B cb ms rb crb rs (es.map FlatEntry.addr) ∧
        RecordFlat t E₀ rb crb rs es ∧ BlockDerivedFlat t E₀ B off es ∧
        (∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
          ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
          rc.lvls.toNat = ind₀.lvls.toNat + off) ∧
        RFormS t E₀ B rb := by
    intro g hg6 hg77 B rb hfam
    obtain ⟨hnew, hmod, cs, hfc⟩ := runFamOf_spec hfam
    have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
    obtain ⟨cr, rs, hcrE, hcrLog, hcrMuts, hrs_pos, hcrRecrs, hcrMems⟩ :=
      familyCall_isTwinShape hC.runStore hC.hashedStored hvl hfc
    have hRec : FamRecRecord E₀ rb cr rs := ⟨hcrE, hcrMuts, hcrRecrs, hcrLog, hcrMems⟩
    let Rg := groupStore t E₀ (runPayload calls bAddr t) (g + 1)
    have hcl_g : UsedClosed Rg :=
      groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6)
    have hRsub : ∀ y c, recordOf Rg y = some c → recordOf E₀ y = some c :=
      fun y cy hy => ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hy).2
    have hRagree : ∀ y c c', recordOf Rg y = some c → recordOf E₀ y = some c' → c = c' :=
      fun y c c' h1 h2 => Option.some.inj ((hRsub y c h1).symm.trans h2)
    have hRB : Held Rg B := hnew.1
    -- Held Rg rb via runFamOf_payload + new_groupStore
    have hRrb : Held Rg rb := by
      have hpay : runPayload calls bAddr t g B rb := runFamOf_payload hfam
      obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg6 hnew
      obtain ⟨cbB, msB, hcbB, hmsB, -, -⟩ :=
        familyCall_block_indc_nonempty hC.runStore hC.hashedStored hfc
      have hw := Classical.choose_spec (hws g)
      have hreach : PayReach t E₀ (runPayload calls bAddr t) g rb := by
        rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨-, -, -, -, p, hp, hproj, -⟩ |
            ⟨-, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpa
        · exact PayReach.payload hra hpay
        · have e := Option.some.inj (hp.symm.trans hcbB); rw [e] at hproj
          exact (Typing.proj_not_block hproj ⟨msB, hmsB⟩).elim
        · have e := Option.some.inj (hc₂.symm.trans hcbB); rw [e, hmsB] at hinfo; cases hinfo
        · rcases payAdds_cases hP hpa with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
          · exact PayReach.payloadOf hrB hpay
          · have e := Option.some.inj (hp.symm.trans hcbB); rw [e] at hproj
            exact (Typing.proj_not_block hproj ⟨msB, hmsB⟩).elim
      obtain ⟨c, hc⟩ := hP.record g rb hreach
      unfold Held
      rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
        ⟨storedBelow_of_adds hg6 (GroupAdds.payReach hreach), hc⟩]; rfl
    have hrecRefs : ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
        Held Rg a ∨ a = rb ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr rb k m := by
      intro i hi a ha
      have hcrR : recordOf Rg rb = some cr := by
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hRrb
        have := hRagree _ _ _ hc' hcrE; subst this; exact hc'
      exact Or.inl ((hcl_g.1 rb cr hcrR).2 i hi a ha)
    obtain ⟨hlv_g, hpar_g⟩ := storeLevelsOk_and_indParamsOk_of_groupStore hC hbd hb hbr hax
      hpin hcheck hroots hstep hval hvalAll hws (Nat.le_succ_of_le hg6) (Nat.succ_le_of_lt hg77)
    obtain ⟨Ec, -, hst⟩ := hstep Rg
      (groupStore_loaded hb (Nat.le_succ_of_le hg6))
      (groupStore_loadedBlobs (Nat.lt_succ_of_le hg6))
      (groupStore_committed hC hb (Nat.le_succ_of_le hg6))
      (groupStore_zeroFree hC hb (Nat.lt_succ_of_le hg6))
    have hM_g : ModeledAnswers calls (Held Rg) (ReconView.ofStore t E₀) :=
      modeledAnswers_mono_S (fun _ _ => trivial)
        (modeledAnswers_of_stepStore hC.runStore hC.hashedStored hst)
    have hBLogic : ∀ cb, recordOf E₀ B = some cb → InLogic cb := by
      intro cb hcb
      have hcbR : recordOf Rg B = some cb := by
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hRB
        have := hRagree _ _ _ hc' hcb; subst this; exact hc'
      exact logic_of_rootsSafe hC hb hP hval hroots g hg6 hg77 B cb hnew hcbR
    obtain ⟨cb, ms, es, off, hFOB, hRF, hBDF, hlv_eq, -, hform⟩ :=
      check_family_core hcheck hwf hC.runStore hC.hashedStored hbd hRagree hcl_g hRB hrecRefs
        hlv_g hpar_g hM_g hRec (by omega) hBLogic hfc
    rcases hform with hformS | ⟨-, hbot⟩
    · exact ⟨cb, cr, ms, rs, es, off, hFOB, hRF, hBDF, hlv_eq, hformS⟩
    · exact (hbot (valLimit g) rfl hvl).elim
  exact {
    familyFlat := fun g hg6 hg77 B rb hfam => by
      obtain ⟨cb, crb, ms, rs, es, off, hF, hR, hB, -, -⟩ := hcore g hg6 hg77 B rb hfam
      exact ⟨cb, crb, ms, rs, es, off, hF, hR, hB⟩
    familyForm := fun g hg6 hg77 B rb hfam => by
      obtain ⟨_, _, _, _, _, _, -, -, -, -, hformS⟩ := hcore g hg6 hg77 B rb hfam
      exact hformS
    familyRecLvls := fun g hg6 hg77 B rb cb crb ms rs hfam hcb hcrb hms hrs => by
      obtain ⟨cb', crb', ms', rs', es, off, hF, -, hB, hlv, -⟩ := hcore g hg6 hg77 B rb hfam
      have ecb : cb' = cb := Option.some.inj (hF.block.record.symm.trans hcb)
      have ecrb : crb' = crb := Option.some.inj (hF.record.record.symm.trans hcrb)
      subst cb' crb'
      have ems : ms' = ms := Ixon.ConstantInfo.muts.inj (hF.block.muts.symm.trans hms)
      have ers : rs' = rs := Ixon.ConstantInfo.muts.inj (hF.record.muts.symm.trans hrs)
      subst ms' rs'
      exact ⟨off, hB.1, hlv⟩
    levelsParams := fun g hg6 hg77 =>
      storeLevelsParams_of_groupStore hC hbd hb hbr hax hpin hcheck hroots hstep hval hvalAll hws
        (Nat.le_succ_of_le hg6) (Nat.succ_le_of_lt hg77)
  }

/-- **Closed `RemainingStoreClausesOfRunNC`**: discharges the remaining family clauses for any
bounded, collision-free binding run with `RunStepStores`. -/
theorem remainingStoreClausesOfRunNC_closed (calls : List (Call F)) :
    RemainingStoreClausesOfRunNC calls := by
  intro hbd a tb t htb hadm hall hpin hval hC hstep _
  have hb := basisRows_of_run hC hpin hval
  have hax := axiomRoles_of_run hC hval
  have hbr : BasisRolesStored t := basisRolesStored_of_pinned hpin
  have hcheck : t.check = .ok () :=
    ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
  have hroots : RootsSafe t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    RootsSafe.of_run hC hval (rootsAndTheoremsSafe_of_run hC hval)
  exact remainingFamilyClauses_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hval

/-- **Closed `GroupStoresOfRun`**: discharges the binding group-store hypothesis unconditionally
for every run (direct drop-in for `Endpoint/ComposedResidual.lean`). -/
theorem groupStoresOfRun_closed (calls : List (Call F)) : GroupStoresOfRun calls :=
  groupStoresOfRun_of_remainingNC (remainingStoreClausesOfRunNC_closed calls)

end IxVM.Refinement.Binding.FamilyRecon


