import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Binding.FamilyReconStore
import IxVMRefinement.StatementRel.LoadedReadsTrace
import IxVMRefinement.StatementRel.LoadedReadsBlockTrace
import IxVMRefinement.StatementRel.LoadedReadsCanonCtor
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Assembly.GuardRawExact
import IxVMRefinement.Binding.RunStepStores
import IxVMRefinement.Binding.RouteModeledRun
import IxVMRefinement.Obs.KernelGuard0
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelModeled3

/-! # Store-level bridge to `TmOExact` and `BlockElim`

This module discharges the five elementary single-call store-read predicates
(`AddrOf`, `DefnAnswers`, `IndAnswers`, `CtorOfAnswers`, `ModeledAnswers`) for
`ReconView.ofStore t E₀` over a used-closed sub-store `R` of the run's store `E₀`, together with
constructor loads (`Ingress::get_ci_cprj`), recursor loads (`Ingress::get_ci` on `RPrj`), block
member address lists (`Ingress::build_recur_addrs`), and the block elimination offset
(`KernelModeled::block_elim` refining `BlockElim t E₀ B off`).

Every expression read from a record at an address in `Held R` is converted directly to `TmOExact`
and `loadedAt` via `L1.RawConvExpr.toTmExactTrace` under `StoreLevelsOk t E₀ (Held R)` (every
record expression in `Held R` has its level parameters below the record's declared level count),
with zero `looseBVarsBounded 0`, `MatchStructFaithful`, `ProjAnswers`, `UnfoldAnswers`, or
`NoLetTele` premises. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum klevelListEnum
  kciEnum krrEnum krrListEnum addrTy addrListEnum ixAddr Resolved)
open IxVM.Refinement.Decl (TmExact RawTmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Typing (RecordsFor StepStore)
open IxVM (F)

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level-parameter well-scopedness of records in a store -/

/-- **Every expression of every record at an address in `S` has its level parameters within the
record's declared level count (below `2^32`)**, so `RawConvExpr` lifts directly to `TmOExact` and
`loadedAt`. -/
structure StoreLevelsOk (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (S : _root_.Address → Prop) : Prop where
  defnVal : ∀ a c d, S a → recordOf E a = some c → c.info = .defn d → d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  dPrjVal : ∀ a c p cb ms d, S a → recordOf E a = some c → c.info = .dPrj p →
    recordOf E p.block = some cb → cb.info = .muts ms → ms[p.idx.toNat]? = some (.defn d) →
    d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t p.block ms)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  indTy : ∀ a c p cb ms ind, S a → recordOf E a = some c → c.info = .iPrj p →
    recordOf E p.block = some cb → cb.info = .muts ms → ms[p.idx.toNat]? = some (.indc ind) →
    ind.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t p.block ms)).read ind.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true
  ctorTy : ∀ (b : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
    S b → recordOf E b = some cb → cb.info = .muts ms →
    ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
    ct.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t b ms)).read ct.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true
  recr : ∀ (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
      (k : Nat) (r : Ixon.Recursor),
    S rb → recordOf E rb = some crb → crb.info = .muts rs →
    rs[k]? = some (.recr r) →
    r.lvls.toNat < 4294967296 ∧
    (∀ E_rd, (exprReader t (fun x => E.blobs.get? x) crb id
        (blockSelf t rb rs)).read r.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, r.rules[j]? = some ru →
      (exprReader t (fun x => E.blobs.get? x) crb id
        (blockSelf t rb rs)).read ru.rhs = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true)

/-! ## Pure helpers: `posOf (List.range n)`, `looseBVarsBounded`, `AddrIn` -/

theorem invPosLevel_range (n : Nat) : ∀ ℓ : KLevel, L1.invPosLevel (List.range n) ℓ = ℓ
  | .zero => rfl
  | .succ l => congrArg Ix.Kernel.Level.succ (invPosLevel_range n l)
  | .max a b => congrArg₂ Ix.Kernel.Level.max (invPosLevel_range n a) (invPosLevel_range n b)
  | .imax a b => congrArg₂ Ix.Kernel.Level.imax (invPosLevel_range n a) (invPosLevel_range n b)
  | .param i => by
    simp only [L1.invPosLevel, List.length_range]
    split
    · simp [List.getElem_range]
    · rfl

theorem level_subst_posLevels_range (n : Nat) (ℓ : KLevel) :
    Ix.Kernel.Level.subst (List.range n) (Core.posLevels (List.range n)) ℓ = ℓ := by
  have h := L1.subst_posLevels_invPosLevel (ps := List.range n) (by simp) ℓ
  rwa [invPosLevel_range] at h

theorem posOf_range_eq (n : Nat) : ∀ E : KExpr, Core.posOf (List.range n) E = E
  | .bvar _ => rfl
  | .fvar _ t => congrArg (Ix.Kernel.Expr.fvar _) (posOf_range_eq n t)
  | .sort l => congrArg Ix.Kernel.Expr.sort (level_subst_posLevels_range n l)
  | .const k ls => by
    show Ix.Kernel.Expr.const k (ls.map (Ix.Kernel.Level.subst (List.range n)
      (Core.posLevels (List.range n)))) = .const k ls
    congr 1
    exact List.map_id'' (level_subst_posLevels_range n) ls
  | .app f a => congrArg₂ Ix.Kernel.Expr.app (posOf_range_eq n f) (posOf_range_eq n a)
  | .lam t b m => by
    show Ix.Kernel.Expr.lam (Core.posOf (List.range n) t) (Core.posOf (List.range n) b)
      { m with pw := Ix.Kernel.Level.substPW (List.range n) (Core.posLevels (List.range n)) m.pw } =
      .lam t b m
    rw [posOf_range_eq n t, posOf_range_eq n b]
    congr 1
    cases m with
    | mk pw =>
      congr 1
      apply Ix.Kernel.PropWhen.eq_of_holds
      intro φ
      rw [Ix.Kernel.Level.holds_substPW]
      have hpos : Core.posLevels (List.range n) = (List.range n).map .param := by
        simp [Core.posLevels]
      have hφ : Ix.Kernel.Level.substFn φ (List.range n) (Core.posLevels (List.range n)) = φ := by
        rw [hpos]; funext p; exact Ix.Kernel.Level.substFn_map_param
      rw [hφ]
  | .forallE t b m => by
    show Ix.Kernel.Expr.forallE (Core.posOf (List.range n) t) (Core.posOf (List.range n) b)
      { m with pw := Ix.Kernel.Level.substPW (List.range n) (Core.posLevels (List.range n)) m.pw } =
      .forallE t b m
    rw [posOf_range_eq n t, posOf_range_eq n b]
    congr 1
    cases m with
    | mk pw =>
      congr 1
      apply Ix.Kernel.PropWhen.eq_of_holds
      intro φ
      rw [Ix.Kernel.Level.holds_substPW]
      have hpos : Core.posLevels (List.range n) = (List.range n).map .param := by
        simp [Core.posLevels]
      have hφ : Ix.Kernel.Level.substFn φ (List.range n) (Core.posLevels (List.range n)) = φ := by
        rw [hpos]; funext p; exact Ix.Kernel.Level.substFn_map_param
      rw [hφ]
  | .letE t v b l => by
    show Ix.Kernel.Expr.letE (Core.posOf (List.range n) t) (Core.posOf (List.range n) v)
      (Core.posOf (List.range n) b) l = .letE t v b l
    rw [posOf_range_eq n t, posOf_range_eq n v, posOf_range_eq n b]
  | .lit _ => rfl
  | .proj k i e => congrArg (Ix.Kernel.Expr.proj k i) (posOf_range_eq n e)

private theorem looseBVarsBounded_mono : ∀ (E : KExpr) {k₁ k₂ : Nat},
    k₁ ≤ k₂ → E.looseBVarsBounded k₁ = true → E.looseBVarsBounded k₂ = true
  | .bvar i, k₁, k₂, hle, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢; omega
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, _, _, hle, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_mono f hle h.1, looseBVarsBounded_mono a hle h.2⟩
  | .lam t b _, _, _, hle, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_mono t hle h.1, looseBVarsBounded_mono b (by omega) h.2⟩
  | .forallE t b _, _, _, hle, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_mono t hle h.1, looseBVarsBounded_mono b (by omega) h.2⟩
  | .letE t v b _, _, _, hle, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨looseBVarsBounded_mono t hle h.1.1, looseBVarsBounded_mono v hle h.1.2⟩,
      looseBVarsBounded_mono b (by omega) h.2⟩
  | .proj _ _ e, _, _, hle, h => looseBVarsBounded_mono e hle h

theorem exists_looseBVarsBounded : ∀ (E : KExpr), ∃ k : Nat, E.looseBVarsBounded k = true
  | .bvar i => ⟨i + 1, by simp [Ix.Kernel.Expr.looseBVarsBounded]⟩
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => ⟨0, rfl⟩
  | .app f a => by
    obtain ⟨kf, hf⟩ := exists_looseBVarsBounded f
    obtain ⟨ka, ha⟩ := exists_looseBVarsBounded a
    exact ⟨max kf ka, by
      simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨looseBVarsBounded_mono f (Nat.le_max_left _ _) hf,
        looseBVarsBounded_mono a (Nat.le_max_right _ _) ha⟩⟩
  | .lam t b _ => by
    obtain ⟨kt, ht⟩ := exists_looseBVarsBounded t
    obtain ⟨kb, hb⟩ := exists_looseBVarsBounded b
    exact ⟨max kt kb, by
      simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨looseBVarsBounded_mono t (Nat.le_max_left _ _) ht,
        looseBVarsBounded_mono b (by omega) hb⟩⟩
  | .forallE t b _ => by
    obtain ⟨kt, ht⟩ := exists_looseBVarsBounded t
    obtain ⟨kb, hb⟩ := exists_looseBVarsBounded b
    exact ⟨max kt kb, by
      simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨looseBVarsBounded_mono t (Nat.le_max_left _ _) ht,
        looseBVarsBounded_mono b (by omega) hb⟩⟩
  | .letE t v b _ => by
    obtain ⟨kt, ht⟩ := exists_looseBVarsBounded t
    obtain ⟨kv, hv⟩ := exists_looseBVarsBounded v
    obtain ⟨kb, hb⟩ := exists_looseBVarsBounded b
    exact ⟨max (max kt kv) kb, by
      simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨⟨looseBVarsBounded_mono t (by omega) ht, looseBVarsBounded_mono v (by omega) hv⟩,
        looseBVarsBounded_mono b (by omega) hb⟩⟩
  | .proj _ _ e => exists_looseBVarsBounded e

theorem addrIn_of_rkeysAt {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {S : _root_.Address → Prop}
    (hwf : t.wf = true) :
    ∀ {E : KExpr}, RKeysAt (ReconView.ofStore t E₀) S E → AddrIn S (Core.keyOf t) E
  | .bvar _, _ | .sort _, _ | .lit _, _ => trivial
  | .fvar _ t1, hk =>
    addrIn_of_rkeysAt hwf (E := t1) (fun k hm => hk k (.fvarTy hm))
  | .const k us, hk => fun a ha => by
    subst ha
    exact hk (Core.keyOf t a) (.const us) a (keyAddr_keyOf hwf a)
  | .app f a, hk =>
    ⟨addrIn_of_rkeysAt hwf (E := f) (fun k hm => hk k (.appFn hm)),
      addrIn_of_rkeysAt hwf (E := a) (fun k hm => hk k (.appArg hm))⟩
  | .lam t1 b _, hk =>
    ⟨addrIn_of_rkeysAt hwf (E := t1) (fun k hm => hk k (.lamTy hm)),
      addrIn_of_rkeysAt hwf (E := b) (fun k hm => hk k (.lamBody hm))⟩
  | .forallE t1 b _, hk =>
    ⟨addrIn_of_rkeysAt hwf (E := t1) (fun k hm => hk k (.allTy hm)),
      addrIn_of_rkeysAt hwf (E := b) (fun k hm => hk k (.allBody hm))⟩
  | .letE t1 v b _, hk =>
    ⟨addrIn_of_rkeysAt hwf (E := t1) (fun k hm => hk k (.letTy hm)),
      addrIn_of_rkeysAt hwf (E := v) (fun k hm => hk k (.letVal hm)),
      addrIn_of_rkeysAt hwf (E := b) (fun k hm => hk k (.letBody hm))⟩
  | .proj k i e, hk =>
    ⟨fun a ha => by
        subst ha
        exact hk (Core.keyOf t a) (.proj i e) a (keyAddr_keyOf hwf a),
      addrIn_of_rkeysAt hwf (E := e) (fun k' hm => hk k' (.projBody hm))⟩

theorem addrIn_instantiateLevelParams {S : _root_.Address → Prop} {κ : _root_.Address → KKey}
    (ps : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ {E : KExpr}, AddrIn S κ E → AddrIn S κ (E.instantiateLevelParams ps us)
  | .bvar _, _ | .sort _, _ | .lit _, _ => trivial
  | .fvar _ t, h => addrIn_instantiateLevelParams ps us (E := t) h
  | .const _ _, h => h
  | .app f a, ⟨hf, ha⟩ =>
    ⟨addrIn_instantiateLevelParams ps us (E := f) hf,
      addrIn_instantiateLevelParams ps us (E := a) ha⟩
  | .lam t b _, ⟨ht, hb⟩ =>
    ⟨addrIn_instantiateLevelParams ps us (E := t) ht,
      addrIn_instantiateLevelParams ps us (E := b) hb⟩
  | .forallE t b _, ⟨ht, hb⟩ =>
    ⟨addrIn_instantiateLevelParams ps us (E := t) ht,
      addrIn_instantiateLevelParams ps us (E := b) hb⟩
  | .letE t v b _, ⟨ht, hv, hb⟩ =>
    ⟨addrIn_instantiateLevelParams ps us (E := t) ht,
      addrIn_instantiateLevelParams ps us (E := v) hv,
      addrIn_instantiateLevelParams ps us (E := b) hb⟩
  | .proj _ _ e, ⟨hk, he⟩ => ⟨hk, addrIn_instantiateLevelParams ps us (E := e) he⟩

/-! ## Core conversion bridge: `RawConvExpr` → `loadedAt` + `TmOExact` -/

/-- **From any traced `RawConvExpr` conversion to `loadedAt` and `TmOExact`**, without any
`looseBVarsBounded 0` assumption: only `allLevelParamsDefined (List.range nl)` on the reading. -/
theorem rawConvExpr_to_tmOExact_loadedAt {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {nl : Nat}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {root : F} {tree : L1.BinderTreeData} {plan : List KLevel}
    (hnl : nl < 4294967296)
    (hself_ok : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hself_key : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hdef : ∀ E_rd, (exprReader t blob src id self).read e = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range nl) = true) :
    ∃ E' : KExpr, loadedAt t blob src self nl root e = some E' ∧ TmOExact (Core.keyOf t) h E' kp := by
  obtain ⟨E_rd, hread⟩ := LoadedReads.exprReader_read_ok ht raw hself_ok hblob
  have hdefE := hdef E_rd hread
  obtain ⟨k, hlbb⟩ := exists_looseBVarsBounded E_rd
  have hread_rp : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range nl)) self).read e = .ok E_rd := by
    rw [Assembly.recParam_range]
    exact hread
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq (readCtx t blob) src
    (Ix.Kernel.Reader.recParam (List.range nl)) self
  unfold Ix.Kernel.Reader.MemberReader.read at hread_rp
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread_rp
  obtain ⟨E', -, htm, htrace⟩ := raw.toTmExactTrace (κ := Core.keyOf t) (ps := List.range nl)
    (by simp) (by simpa using hnl) rfl (by simp)
    (LoadedReads.readCtx_keyAt_inv ht blob) hself_key hblob
    (Nat.le_refl _) (Nat.min_le_right _ _) hread_rp hlbb hdefE
  have hap := htrace plan levels []
  rw [List.append_nil] at hap
  refine ⟨E', ?_, ⟨k, ?_⟩⟩
  · unfold loadedAt LoadedReads.canonAnn
    rw [hread]
    simp only [Except.toOption, LoadedReads.canonTree_eq built, planned, Option.bind_some]
    rw [hap]
    rfl
  · have h0 := htm 0 ghost0
    rwa [posOf_range_eq nl E'] at h0

/-! ## Store-read helpers from `RunStore` + `HashedRecordsStored` -/

private theorem blobs_of_hashedPairs {rootCalls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    {blobs : List (_root_.Address × ByteArray)} (hhp : L1.HashedPairs cs blobs) :
    ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
  intro x bs hm
  obtain ⟨hh, ha⟩ := hhp (x, bs) hm
  have h1 := hS.blobs bs (Core.hashed_mono hsub hh)
  rwa [ha] at h1

private theorem record_eq_of_hashed {rootCalls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    {a : _root_.Address} {c c' : Ixon.Constant} {bytes : ByteArray}
    (hrec : recordOf E₀ a = some c) (hh : Hashed cs bytes)
    (ha : Address.blake3Pure bytes = a) (hde : Ixon.deConstantExact bytes = .ok c') :
    c' = c := by
  rw [hS.recordOf_eq_recordAt] at hrec
  exact hS.record_eq hrec (Core.hashed_mono hsub hh) ha hde

private theorem get_ci_record_eq {rootCalls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    {a : Bytes.Address} {xa p : SourceValue F} {h m : Heap F}
    (ra : Bytes.RepAddressRef addrTy h a xa) (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs)
    {rawBytes : ByteArray} {c : Ixon.Constant}
    (hh : Hashed cs rawBytes) (ha : Address.blake3Pure rawBytes = ixAddr a)
    (hde : Ixon.deConstantExact rawBytes = .ok c) :
    recordOf E₀ (ixAddr a) = some c := by
  obtain ⟨c', hrec⟩ := LoadedReads.recordAt_of_get_ci hH ⟨a, ra, rfl⟩ ev hsub
  have hc := hS.record_eq hrec (Core.hashed_mono hsub hh) ha hde
  subst hc
  exact hS.recordOf_of_recordAt hrec

private theorem soloSelf_ok {t : Ix.Kernel.RoleTable} {a : _root_.Address} {d : Ixon.Definition} :
    ∀ i x, (L1.defnRecurAddrs d a)[i]? = some x →
      ∃ m k, soloSelf t a i = some m ∧ m = .ok k := by
  intro i x hx
  unfold L1.defnRecurAddrs at hx
  split at hx
  · cases i with
    | zero => exact ⟨.ok (keyOf t a), keyOf t a, rfl, rfl⟩
    | succ _ => simp at hx
  · simp at hx

private theorem soloSelf_key {t : Ix.Kernel.RoleTable} {a : _root_.Address} {d : Ixon.Definition} :
    ∀ i x m k, (L1.defnRecurAddrs d a)[i]? = some x → soloSelf t a i = some m → m = .ok k →
      k = Core.keyOf t x := by
  intro i x m k hx hs hm
  unfold L1.defnRecurAddrs at hx
  split at hx
  · cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp only [soloSelf] at hs
      injection hs with hs'
      rw [← hs'] at hm
      exact (Except.ok.inj hm).symm
    | succ _ => simp at hx
  · simp at hx

private theorem defnMember_self_ok {t : Ix.Kernel.RoleTable} {B : _root_.Address}
    {ms : Array Ixon.MutConst} {d : Ixon.Definition} :
    ∀ i x, (L1.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      ∃ m k, blockSelf t B ms i = some m ∧ m = .ok k := by
  intro i x hx
  unfold L1.defnMemberRecurAddrs at hx
  split at hx
  · exact LoadedReads.blockSelf_ok t B ms i x hx
  · simp at hx

private theorem defnMember_self_key {t : Ix.Kernel.RoleTable} {B : _root_.Address}
    {ms : Array Ixon.MutConst} {d : Ixon.Definition} :
    ∀ i x m k, (L1.defnMemberRecurAddrs d B ms.toList)[i]? = some x →
      blockSelf t B ms i = some m → m = .ok k → k = Core.keyOf t x := by
  intro i x m k hx hs hm
  unfold L1.defnMemberRecurAddrs at hx
  split at hx
  · exact LoadedReads.blockSelf_key t B ms i x m k hx hs hm
  · simp at hx

private theorem held_owner_of_proj {E₀ R : Ixon.Env}
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    (hcl : UsedClosed R) {a : _root_.Address} {c : Ixon.Constant}
    (hSa : Held R a) (hcE : recordOf E₀ a = some c) :
    Held R (Ix.Cert.ownerOf a c) :=
  (hcl.1 a c (held_of_sub hRsub hSa hcE)).1

private theorem defnValShape_ne_induct {d : Ixon.Definition} {tp vp hp : SourceValue F}
    {vs : List (SourceValue F)} :
    L1.defnValShape d tp vp hp ≠ .construct kciEnum "Induct" vs := by
  unfold L1.defnValShape
  cases d.kind <;> simp [kciEnum]

private theorem defnValShape_ne_ctor {d : Ixon.Definition} {tp vp hp : SourceValue F}
    {vs : List (SourceValue F)} :
    L1.defnValShape d tp vp hp ≠ .construct kciEnum "Ctor" vs := by
  unfold L1.defnValShape
  cases d.kind <;> simp [kciEnum]

private theorem defnValShape_defn_inv {d : Ixon.Definition} {tp vp hp : SourceValue F}
    {xnl xty xval xsf xh : SourceValue F}
    (h : L1.defnValShape d tp vp hp =
      .construct "KernelTypes::KConstantInfo" "Defn" [xnl, xty, xval, xsf, xh]) :
    d.kind = .defn ∧ xnl = .field (d.lvls.toNat : F) ∧ xval = vp := by
  unfold L1.defnValShape at h
  cases hk : d.kind with
  | defn =>
    simp only [hk, kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at h
    exact ⟨rfl, h.1.symm, h.2.2.1.symm⟩
  | thm => simp [hk, kciEnum] at h
  | opaq => simp [hk, kciEnum] at h

private theorem defnValShape_ne_defn_of_kind {d : Ixon.Definition} {tp vp hp : SourceValue F}
    (hne : ∀ vs : List (SourceValue F), vs.length = 5 →
      L1.defnValShape d tp vp hp ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) :
    d.kind ≠ .defn := by
  intro hk
  unfold L1.defnValShape at hne
  rw [hk] at hne
  exact hne _ rfl rfl

/-! ## Discharging the five single-call store-read predicates -/

/-- **`AddrOf` for `ReconView.ofStore t E₀`** whenever `t.wf = true`. -/
theorem addrOf_ofStore {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hwf : t.wf = true) :
    AddrOf (Core.keyOf t) (ReconView.ofStore t E₀) :=
  fun a => keyAddr_keyOf hwf a

private theorem defnValAt_of_defnAt {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {nl : Nat} {val : KExpr}
    (hd : defnAt t E₀ a = some (some (nl, val))) :
    defnValAt t E₀ a = some (nl, val) := by
  unfold defnValAt
  unfold defnAt at hd
  cases hrec : recordOf E₀ a with
  | none => rw [hrec] at hd; simp at hd
  | some c =>
    rw [hrec] at hd; simp only at hd ⊢
    cases hci : c.info with
    | defn d =>
      simp only [hci] at hd ⊢
      cases hdk : d.kind with
      | defn =>
        simp only [hdk] at hd ⊢
        cases hl : loadedAt t (fun x => E₀.blobs.get? x) c (soloSelf t a) d.lvls.toNat 1
            d.value with
        | none => rw [hl] at hd; simp at hd
        | some w =>
          rw [hl] at hd; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd ⊢
          exact hd
      | _ => simp [hdk] at hd
    | dPrj prj =>
      simp only [hci] at hd ⊢
      cases hcb : recordOf E₀ prj.block with
      | none => simp [hcb] at hd
      | some cb =>
        rw [hcb] at hd; simp only at hd ⊢
        cases hcbi : cb.info with
        | muts ms =>
          simp only [hcbi] at hd ⊢
          cases hm : ms[prj.idx.toNat]? with
          | none => simp [hm] at hd
          | some mc =>
            cases mc with
            | defn d =>
              simp only [hm] at hd ⊢
              cases hdk : d.kind with
              | defn =>
                simp only [hdk] at hd ⊢
                cases hl : loadedAt t (fun x => E₀.blobs.get? x) cb (blockSelf t prj.block ms)
                    d.lvls.toNat (mutsRoot ms prj.idx.toNat + 1) d.value with
                | none => rw [hl] at hd; simp at hd
                | some w =>
                  rw [hl] at hd
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd ⊢
                  exact hd
              | _ => simp [hdk] at hd
            | _ => simp [hm] at hd
        | _ => simp [hcbi] at hd
    | _ => simp [hci] at hd

/-- **`Ingress::get_ci` matches `defnAt t E₀`** (and `defnValAt t E₀`) on `TmOExact` and
`AddrIn (Held R)`. -/
theorem defnLoad_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hSa : Held R (ixAddr a))
    (ra : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (ldci : loadValue m p = .ok ci) :
    (∀ xnl xty xval xsf xh,
      ci = .construct "KernelTypes::KConstantInfo" "Defn" [xnl, xty, xval, xsf, xh] →
      ∃ (nl : Nat) (val : KExpr),
        xnl = .field (nl : F) ∧ nl < 4294967296 ∧ TmOExact (Core.keyOf t) m val xval ∧
        AddrIn (Held R) (Core.keyOf t) val ∧
        defnAt t E₀ (ixAddr a) = some (some (nl, val)) ∧
        defnValAt t E₀ (ixAddr a) = some (nl, val)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 5 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) →
      defnAt t E₀ (ixAddr a) = some none) := by
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd hsub
  obtain ⟨rawBytes, c, hh, ha, hex, htr⟩ := L1.get_ci_trace_spec ra ev
  have hcE : recordOf E₀ (ixAddr a) = some c := get_ci_record_eq hS hH hsub ra ev hh ha hex
  obtain ⟨-, rawBytes', c', blobs', hh', ha', hex', -, -, -, hrawRes⟩ :=
    L1.get_ci_spec hbd_cs ra ev
  have hc_eq : c' = c := record_eq_of_hashed hS hsub hcE hh' ha' hex'
  rcases hc_eq.symm with rfl
  cases hci : c.info with
  | defn d =>
    simp only [L1.GetCITraceResult, hci] at htr
    obtain ⟨blobs, tree, v, hhp, built, hld, hnl, tp, vp, hp, planT, planV, hv, rty, rval,
      hpT, hpV, hlT, hlV⟩ := htr
    rw [hld] at ldci; injection ldci with hv_eq; subst hv_eq; subst hv
    refine ⟨fun xnl xty xval xsf xh hshape => ?_, fun hne => ?_⟩
    · obtain ⟨hdk, rfl, rfl⟩ := defnValShape_defn_inv hshape
      obtain ⟨hnl', hdef⟩ := hlv.defnVal (ixAddr a) c d hSa hcE hci hdk
      obtain ⟨val, hloaded, htm⟩ := rawConvExpr_to_tmOExact_loadedAt ht hnl'
        (soloSelf_ok (t := t) (a := ixAddr a) (d := d))
        (soloSelf_key (t := t) (a := ixAddr a) (d := d))
        (blobs_of_hashedPairs hS hsub hhp) rval built hpV hlV hdef
      have hdefnAt : defnAt t E₀ (ixAddr a) = some (some (d.lvls.toNat, val)) := by
        unfold defnAt
        simp only [hcE, hci, hdk, hloaded]
        rfl
      have hvalIn : AddrIn (Held R) (Core.keyOf t) val := by
        have hcR := held_of_sub hRsub hSa hcE
        refine addrIn_of_rkeysAt (E₀ := E₀) hwf ?_
        refine keys_held_of_loaded ht hwf hcl hcR ?_ (fun j hj => ?_) hloaded
        · intro j k hs
          unfold soloSelf at hs
          split at hs
          · cases Except.ok.inj (Option.some.inj hs)
            exact ⟨ixAddr a, hSa, rfl⟩
          · cases hs
        · simp only [usedRefIdxs, hci]
          exact List.mem_append_right _ (List.mem_append_right _ hj)
      exact ⟨d.lvls.toNat, val, rfl, hnl', htm, hvalIn, hdefnAt, defnValAt_of_defnAt hdefnAt⟩
    · have hnd := defnValShape_ne_defn_of_kind hne
      cases hdk : d.kind with
      | defn => exact (hnd hdk).elim
      | thm => unfold defnAt; simp only [hcE, hci, hdk]
      | opaq => unfold defnAt; simp only [hcE, hci, hdk]
  | dPrj prj =>
    simp only [L1.GetCITraceResult, hci] at htr
    obtain ⟨_, blkBytes, cb, ms, d, blobs, tree, v, hhB, haB, hexB, hcb, hms, hhp, built, hld,
      hnl, tp, vp, hp, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
    rw [hld] at ldci; injection ldci with hv_eq; subst hv_eq; subst hv
    have hpb : Held R prj.block := by
      have h1 := held_owner_of_proj hRsub hcl hSa hcE
      simpa only [Ix.Cert.ownerOf, hci] using h1
    obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hpb
    have hcbE : recordOf E₀ prj.block = some cbR := hRsub prj.block cbR hcbR
    have hcbEq : cb = cbR := record_eq_of_hashed hS hsub hcbE hhB haB hexB
    subst hcbEq
    have hms' : ms[prj.idx.toNat]? = some (.defn d) := by
      rw [← Array.getElem?_toList]; exact hms
    refine ⟨fun xnl xty xval xsf xh hshape => ?_, fun hne => ?_⟩
    · obtain ⟨hdk, rfl, rfl⟩ := defnValShape_defn_inv hshape
      obtain ⟨hnl', hdef⟩ := hlv.dPrjVal (ixAddr a) c prj cb ms d hSa hcE hci hcbE hcb hms' hdk
      obtain ⟨val, hloaded, htm⟩ := rawConvExpr_to_tmOExact_loadedAt ht hnl'
        (defnMember_self_ok (t := t) (B := prj.block) (ms := ms) (d := d))
        (defnMember_self_key (t := t) (B := prj.block) (ms := ms) (d := d))
        (blobs_of_hashedPairs hS hsub hhp) rval built hpV hlV hdef
      have hdefnAt : defnAt t E₀ (ixAddr a) = some (some (d.lvls.toNat, val)) := by
        unfold defnAt
        simp only [hcE, hci, hcbE, hcb, hms', hdk, mutsRoot, hloaded]
        rfl
      have hvalIn : AddrIn (Held R) (Core.keyOf t) val :=
        addrIn_of_rkeysAt (E₀ := E₀) hwf
          (keys_held_of_loaded ht hwf hcl hcbR (blockSelf_held hcl hcbR hcb)
            (fun j hj => mem_used_of_member hcb hms' j (List.mem_append_right _ hj)) hloaded)
      exact ⟨d.lvls.toNat, val, rfl, hnl', htm, hvalIn, hdefnAt, defnValAt_of_defnAt hdefnAt⟩
    · have hnd := defnValShape_ne_defn_of_kind hne
      cases hdk : d.kind with
      | defn => exact (hnd hdk).elim
      | thm => unfold defnAt; simp only [hcE, hci, hcbE, hcb, hms', hdk]
      | opaq => unfold defnAt; simp only [hcE, hci, hcbE, hcb, hms', hdk]
  | axio ax =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [defnAt, hcE, hci]⟩
  | quot q =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [defnAt, hcE, hci]⟩
  | iPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, _, _, _, -, -, rfl, -⟩ :=
      hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [defnAt, hcE, hci]⟩
  | cPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, _, _, v, -, -, -, -, -, -, -, hld, -, -, -, -, -, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [defnAt, hcE, hci]⟩
  | recr rc =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [defnAt, hcE, hci]⟩
  | rPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨-, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [defnAt, hcE, hci]⟩
  | muts ms =>
    simp [L1.GetCIRawResult, hci] at hrawRes

/-- **`DefnAnswers` for `ReconView.ofStore t E₀`** over a used-closed sub-store `R` with
`StoreLevelsOk t E₀ (Held R)`. -/
theorem defnAnswers_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    DefnAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a hsub hSa ra ev ldci
  obtain ⟨hyes, hno⟩ := defnLoad_ofStore ht hwf hS hH hbd hRsub hcl hlv hsub hSa ra ev ldci
  have hka : keyAddr t (Core.keyOf t (ixAddr a)) = some (ixAddr a) := keyAddr_keyOf hwf (ixAddr a)
  refine ⟨fun xnl xty xval xsf xh hshape => ?_, fun hne us => ?_⟩
  · obtain ⟨nl, val, h1, h2, h3, h4, hdefnAt, -⟩ := hyes xnl xty xval xsf xh hshape
    refine ⟨nl, val, h1, h2, h3, h4, fun us => ?_⟩
    simp [ReconView.ofStore, unfoldAt, hka, hdefnAt]
  · simp [ReconView.ofStore, unfoldAt, hka, hno hne]

/-- **`IndAnswers` for `ReconView.ofStore t E₀`** over a used-closed sub-store `R` with
`StoreLevelsOk t E₀ (Held R)`. -/
theorem indAnswers_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    IndAnswers rootCalls (Held R) (Core.keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a hsub hSa ra ev ldci
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd hsub
  obtain ⟨rawBytes, c, hh, ha, hex, -, hblk⟩ := L1.get_ci_block_trace_spec hbd_cs ra ev
  have hcE : recordOf E₀ (ixAddr a) = some c := get_ci_record_eq hS hH hsub ra ev hh ha hex
  obtain ⟨-, rawBytes', c', blobs', hh', ha', hex', -, -, -, hrawRes⟩ :=
    L1.get_ci_spec hbd_cs ra ev
  have hc_eq : c' = c := record_eq_of_hashed hS hsub hcE hh' ha' hex'
  rcases hc_eq.symm with rfl
  cases hci : c.info with
  | iPrj prj =>
    simp only [L1.GetCIBlockTraceResult, hci] at hblk
    obtain ⟨_, blkBytes, cb, ms, ind, blobs, tree, plan, v, hhB, haB, hexB, hcb, hms, hhp, built,
      planned, hld, hrawInd, hcit⟩ := hblk
    rw [hld] at ldci; injection ldci with hv_eq; subst hv_eq
    obtain ⟨hnl, hnp, hni, hnc, hidx, tyPtr, blkPtr, ba, hba, rba, rfl, rty⟩ := hrawInd
    obtain ⟨_, tyPtr', _, hcit_eq, hlevels⟩ := hcit
    simp only [kciEnum, Value.construct.injEq, List.cons.injEq] at hcit_eq
    have hty_eq : tyPtr' = tyPtr := hcit_eq.2.2.2.1.symm
    subst hty_eq
    have hpb : Held R prj.block := by
      have h1 := held_owner_of_proj hRsub hcl hSa hcE
      simpa only [Ix.Cert.ownerOf, hci] using h1
    obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hpb
    have hcbE : recordOf E₀ prj.block = some cbR := hRsub prj.block cbR hcbR
    have hcbEq : cb = cbR := record_eq_of_hashed hS hsub hcbE hhB haB hexB
    subst hcbEq
    have hms' : ms[prj.idx.toNat]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]; exact hms
    refine ⟨fun xnl xty xnp xni xnc xrec xblk xidx hshape => ?_, fun hne => ?_⟩
    · simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hshape
      rcases hshape with ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩
      obtain ⟨hnl', hdef⟩ := hlv.indTy (ixAddr a) c prj cb ms ind hSa hcE hci hcbE hcb hms'
      obtain ⟨ty, hloaded, htm⟩ := rawConvExpr_to_tmOExact_loadedAt ht hnl'
        (LoadedReads.blockSelf_ok t prj.block ms) (LoadedReads.blockSelf_key t prj.block ms)
        (blobs_of_hashedPairs hS hsub hhp) rty built planned hlevels hdef
      have hindAt : indDataAt t E₀ (ixAddr a) =
          some (some ⟨ind.lvls.toNat, ty, ind.params.toNat, ind.indices.toNat, ind.ctors.size,
            prj.block, prj.idx.toNat⟩) := by
        unfold indDataAt
        simp only [hcE, hci, hcbE, hcb, hms', mutsRoot, hloaded]
      have htyIn : AddrIn (Held R) (Core.keyOf t) ty :=
        addrIn_of_rkeysAt (E₀ := E₀) hwf
          (keys_held_of_loaded ht hwf hcl hcbR (blockSelf_held hcl hcbR hcb)
            (fun j hj => mem_used_of_member hcb hms' j (List.mem_append_left _ hj)) hloaded)
      exact ⟨⟨ind.lvls.toNat, ty, ind.params.toNat, ind.indices.toNat, ind.ctors.size,
        prj.block, prj.idx.toNat⟩, ba, hindAt, hnl', hnp, hni, hnc, hidx, rfl, htm, htyIn, hpb,
        rfl, rfl, rfl, hba, rba, rfl⟩
    · exact (hne _ rfl rfl).elim
  | defn d =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, vp, hp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => (defnValShape_ne_induct h).elim,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | dPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, v, -, -, -, -, -, -, hld, -, tp, vp, hp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => (defnValShape_ne_induct h).elim,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | axio ax =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | quot q =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | cPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, _, _, v, -, -, -, -, -, -, -, hld, -, -, -, -, -, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | recr rc =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | rPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨-, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, indDataAt, hcE, hci]⟩
  | muts ms =>
    simp [L1.GetCIRawResult, hci] at hrawRes

/-- **`CtorOfAnswers` for `ReconView.ofStore t E₀`** over a used-closed sub-store `R`. -/
theorem ctorOfAnswers_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R) :
    CtorOfAnswers rootCalls (Held R) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a hsub hSa ra ev ldci
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd hsub
  obtain ⟨-, rawBytes, c, blobs, hh, ha, hex, -, -, -, hrawRes⟩ := L1.get_ci_spec hbd_cs ra ev
  have hcE : recordOf E₀ (ixAddr a) = some c := get_ci_record_eq hS hH hsub ra ev hh ha hex
  cases hci : c.info with
  | cPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, blkBytes, cb, ms, ind, ct, v, hhB, haB, hexB, -, hcb, hms, hct, hld,
      hnl, hcidx, hnp, hnf, hidx, tyPtr, blkPtr, ba, hba, rba, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    have hpb : Held R prj.block := by
      have h1 := held_owner_of_proj hRsub hcl hSa hcE
      simpa only [Ix.Cert.ownerOf, hci] using h1
    obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hpb
    have hcbE : recordOf E₀ prj.block = some cbR := hRsub prj.block cbR hcbR
    have hcbEq : cb = cbR := record_eq_of_hashed hS hsub hcbE hhB haB hexB
    subst hcbEq
    have hms' : ms[prj.idx.toNat]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]; exact hms
    have hct' : ind.ctors[prj.cidx.toNat]? = some ct := by
      rw [← Array.getElem?_toList]; exact hct
    refine ⟨fun xnl xty xblk xind xcidx xnp xnf xuns hshape => ?_, fun hne => ?_⟩
    · simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hshape
      rcases hshape with ⟨rfl, -, rfl, rfl, -, rfl, rfl, -⟩
      have hctAt : ctorOfAt E₀ (ixAddr a) =
          some (some ⟨ct.lvls.toNat, prj.block, prj.idx.toNat, ct.params.toNat,
            ct.fields.toNat⟩) := by
        simp [ctorOfAt, hcE, hci, hcbE, hcb, hms', hct']
      exact ⟨⟨ct.lvls.toNat, prj.block, prj.idx.toNat, ct.params.toNat, ct.fields.toNat⟩,
        ba, hctAt, hnl, hidx, hnp, hnf, rfl, hba, rba, rfl, rfl, rfl⟩
    · exact (hne _ rfl rfl).elim
  | defn d =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, vp, hp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => (defnValShape_ne_ctor h).elim,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | dPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, v, -, -, -, -, -, -, hld, -, tp, vp, hp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => (defnValShape_ne_ctor h).elim,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | axio ax =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | quot q =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | iPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, _, _, _, -, -, rfl, -⟩ :=
      hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | recr rc =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | rPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨-, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [ReconView.ofStore, ctorOfAt, hcE, hci]⟩
  | muts ms =>
    simp [L1.GetCIRawResult, hci] at hrawRes

/-- **`ModeledAnswers` for `ReconView.ofStore t E₀`** over a used-closed sub-store `R` backed by
a record store `Ec` (`RecordsFor R Ec` and `StepStore rootCalls t E₀ Ec`). -/
theorem modeledAnswers_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R Ec : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hRec : RecordsFor R Ec) (hst : StepStore rootCalls t E₀ Ec) :
    ModeledAnswers rootCalls (Held R) (ReconView.ofStore t E₀) := by
  intro xblk r h m cs ba hsub hSba rba ev
  have g := (hst.good Ix.Kernel.Env.empty none).sub hsub
  have hag := Route.block_is_modeled_agrees (E := Ec) g.1 g.2 rba ev
  have hcov : L1.CanonicalHashCoverage Ec cs := fun bytes val hh hsz hx =>
    (Binding.stepStore_canonicalHashCoverage hS hH hst) bytes val (Core.hashed_mono hsub hh) hsz hx
  obtain ⟨b, hbEc⟩ := hag.known hcov
  have hr_eq := hag.value b hbEc
  obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hSba
  have hbR : Route.blockRoute R (ixAddr ba) = some b := by
    rw [← Binding.blockRoute_of_recordsFor hcl hRec hcbR]
    exact hbEc
  have hbE₀ : Route.blockRoute E₀ (ixAddr ba) = some b :=
    blockRoute_grow hRsub b hbR
  refine ⟨b, hbE₀, hr_eq.trans ?_⟩
  cases b <;> rfl

/-! ## `IndInfo` loads, constructor loads (`get_ci_cprj`), recursor loads, and `build_recur_addrs` -/

/-- **`Ingress::get_ci` matches `indInfoAt E₀`** (`FlatView.ofStore t E₀ |>.ci`), with `Held R`
on the inductive's block address when `Held R (ixAddr a)`. -/
theorem indInfo_of_get_ci {rootCalls : List (Call F)} {E₀ R : Ixon.Env}
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hSa : Held R (ixAddr a))
    (ra : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (ldci : loadValue m p = .ok ci) :
    (∀ xnl xty xnp xni xnc xrec xblk xidx,
      ci = .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx] →
      ∃ (info : IndInfo) (ba : Bytes.Address),
        indInfoAt E₀ (ixAddr a) = some (some info) ∧
        info.nl < 4294967296 ∧ info.np < 72057594037927936 ∧
        info.nctors < 72057594037927936 ∧ info.idx < 72057594037927936 ∧
        Held R info.blk ∧
        xnl = .field (info.nl : F) ∧ xnp = .field (info.np : F) ∧
        xnc = .field (info.nctors : F) ∧ ixAddr ba = info.blk ∧
        Bytes.RepAddressRef addrTy m ba xblk ∧ xidx = .field (info.idx : F)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs) →
      indInfoAt E₀ (ixAddr a) = some none) := by
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd hsub
  obtain ⟨-, rawBytes, c, blobs, hh, ha, hex, -, -, -, hrawRes⟩ := L1.get_ci_spec hbd_cs ra ev
  have hcE : recordOf E₀ (ixAddr a) = some c := get_ci_record_eq hS hH hsub ra ev hh ha hex
  cases hci : c.info with
  | iPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, blkBytes, cb, ms, ind, v, hhB, haB, hexB, -, hcb, hms, hld,
      hnl, hnp, hni, hnc, hidx, tyPtr, blkPtr, ba, hba, rba, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    have hpb : Held R prj.block := by
      have h1 := held_owner_of_proj hRsub hcl hSa hcE
      simpa only [Ix.Cert.ownerOf, hci] using h1
    obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hpb
    have hcbE : recordOf E₀ prj.block = some cbR := hRsub prj.block cbR hcbR
    have hcbEq : cb = cbR := record_eq_of_hashed hS hsub hcbE hhB haB hexB
    subst hcbEq
    have hms' : ms[prj.idx.toNat]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]; exact hms
    refine ⟨fun xnl xty xnp xni xnc xrec xblk xidx hshape => ?_, fun hne => (hne _ rfl rfl).elim⟩
    simp only [kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hshape
    rcases hshape with ⟨rfl, -, rfl, -, rfl, -, rfl, rfl⟩
    refine ⟨⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, prj.block, prj.idx.toNat⟩,
      ba, ?_, hnl, hnp, hnc, hidx, hpb, rfl, rfl, rfl, hba, rba, rfl⟩
    simp [indInfoAt, hcE, hci, hcbE, hcb, hms']
  | defn d =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, vp, hp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => (defnValShape_ne_induct h).elim,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | dPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, v, -, -, -, -, -, -, hld, -, tp, vp, hp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => (defnValShape_ne_induct h).elim,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | axio ax =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | quot q =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, tp, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | cPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨_, _, _, _, _, _, _, v, -, -, -, -, -, -, -, hld, -, -, -, -, -, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | recr rc =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨v, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl, -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | rPrj prj =>
    simp only [L1.GetCIRawResult, hci] at hrawRes
    obtain ⟨-, _, _, _, _, v, -, -, -, -, -, -, hld, -, -, -, -, -, -, _, _, _, _, -, -, rfl,
      -⟩ := hrawRes
    rw [hld] at ldci; injection ldci with hv; subst hv
    exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [kciEnum] at h,
      fun _ => by simp [indInfoAt, hcE, hci]⟩
  | muts ms =>
    simp [L1.GetCIRawResult, hci] at hrawRes

/-- **`Ingress::get_ci_cprj` matches `ctorAt` and `ctorTypeAt`** on `TmOExact` and `AddrIn (Held R)`. -/
theorem ctorLoad_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {ba : Bytes.Address} {xblk p ci : SourceValue F} {i j : Nat}
    {h m : Heap F} {cs : List (Call F)}
    (hi : i < 18446744069414584321) (hj : j < 18446744069414584321)
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hSb : Held R (ixAddr ba))
    (rba : Bytes.RepAddressRef addrTy h ba xblk)
    (ev : ObsFn W "Ingress::get_ci_cprj" [xblk, .field (i : F), .field (j : F)] h p m cs)
    (ldci : loadValue m p = .ok ci) :
    ∃ (ty : KExpr) (nl np nf : Nat) (xty xblk' : SourceValue F) (ba' : Bytes.Address)
      (xcidx xuns : SourceValue F),
      ci = .construct kciEnum "Ctor"
        [.field (nl : F), xty, xblk', .field (i : F), xcidx, .field (np : F),
          .field (nf : F), xuns] ∧
      ctorAt t E₀ (ixAddr ba) i j = some (ty, np) ∧
      ctorTypeAt t E₀ (ixAddr ba) i j = some ty ∧
      nl < 4294967296 ∧ np < 72057594037927936 ∧ nf < 72057594037927936 ∧
      TmOExact (Core.keyOf t) m ty xty ∧ AddrIn (Held R) (Core.keyOf t) ty ∧
      ixAddr ba' = ixAddr ba ∧ Bytes.RepAddressRef addrTy m ba' xblk' := by
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd hsub
  obtain ⟨-, -, -, blkBytes, cb, ms, ind, ct, blobs, v, hhB, haB, hexB, -, hcb, hms, hct,
    hhp, hld, hrawC, tree, plan, built, planned, hcit⟩ :=
    L1.get_ci_cprj_origin_spec hbd_cs rba ev
  rw [hld] at ldci; injection ldci with hv; subst hv
  have hiv : ((i : F)).val = i := fval_natCast hi
  have hjv : ((j : F)).val = j := fval_natCast hj
  rw [hiv] at hms hrawC planned
  rw [hjv] at hct
  obtain ⟨hnl, hcidx, hnp, hnf, -, tyPtr, blkPtr, ba', hba', rba', rfl, rty⟩ := hrawC
  obtain ⟨_, tyPtr', _, hcit_eq, hlevels⟩ := hcit
  simp only [kciEnum, Value.construct.injEq, List.cons.injEq] at hcit_eq
  have hty_eq : tyPtr' = tyPtr := hcit_eq.2.2.2.1.symm
  rcases hty_eq.symm with rfl
  obtain ⟨cbR, hcbR⟩ := Option.isSome_iff_exists.mp hSb
  have hcbE : recordOf E₀ (ixAddr ba) = some cbR := hRsub (ixAddr ba) cbR hcbR
  have hcbEq : cb = cbR := record_eq_of_hashed hS hsub hcbE hhB haB hexB
  subst hcbEq
  have hms' : ms[i]? = some (.indc ind) := by rw [← Array.getElem?_toList]; exact hms
  have hct' : ind.ctors[j]? = some ct := by rw [← Array.getElem?_toList]; exact hct
  obtain ⟨hnl', hdef⟩ := hlv.ctorTy (ixAddr ba) cb ms i ind j ct hSb hcbE hcb hms' hct'
  obtain ⟨ty, hloaded, htm⟩ := rawConvExpr_to_tmOExact_loadedAt ht hnl'
    (LoadedReads.blockSelf_ok t (ixAddr ba) ms) (LoadedReads.blockSelf_key t (ixAddr ba) ms)
    (blobs_of_hashedPairs hS hsub hhp) rty built planned hlevels hdef
  have hcmem : ct ∈ ind.ctors.toList := List.mem_of_getElem? hct
  have htyIn : AddrIn (Held R) (Core.keyOf t) ty :=
    addrIn_of_rkeysAt (E₀ := E₀) hwf
      (keys_held_of_loaded ht hwf hcl hcbR (blockSelf_held hcl hcbR hcb)
        (fun l hl => mem_used_of_member hcb hms' l
          (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ct, hcmem, hl⟩))) hloaded)
  refine ⟨ty, ct.lvls.toNat, ct.params.toNat, ct.fields.toNat, tyPtr, blkPtr, ba',
    .field (ct.cidx.toNat : F), L1.repBoolField ct.isUnsafe, rfl, ?_, ?_, hnl', hnp, hnf,
    htm, htyIn, hba', rba'⟩
  · unfold ctorAt; simp only [hcbE, hcb, hms', hct', mutsRoot, hloaded]
  · unfold ctorTypeAt; simp only [hcbE, hcb, hms', hct', mutsRoot, hloaded]

/-- **Representation of a recursor rule list** matching `loadedAt` for each rule `j` of a recursor
member `r` at root `base`. -/
def RecRuleRep (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (S : _root_.Address → Prop)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (nl : Nat) (base : F) (h : Heap F) (j : Nat) (ru : Ixon.RecursorRule)
    (v : SourceValue F) : Prop :=
  ∃ (rhs : KExpr) (rhsPtr : SourceValue F),
    v = .construct krrEnum "Mk" [.field (j : F), .field (ru.fields.toNat : F), rhsPtr] ∧
    ru.fields.toNat < 72057594037927936 ∧
    loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) nl (base + 1 + ((j : Nat) : F))
      ru.rhs = some rhs ∧
    TmOExact (Core.keyOf t) h rhs rhsPtr ∧
    AddrIn S (Core.keyOf t) rhs

/-- Recursive witness for a list of rules from index `j`. -/
inductive RecRulesRep (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (S : _root_.Address → Prop)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (nl : Nat) (base : F) (h : Heap F) : Nat → List Ixon.RecursorRule → SourceValue F → Prop where
  | nil {j : Nat} {addr : Nat}
      (cell : h[addr]? = some (.construct krrListEnum "Nil" [])) :
      RecRulesRep t E₀ S rb crb rs nl base h j [] (.ptr (.enum krrListEnum) addr)
  | cons {j : Nat} {addr : Nat} {v rest : SourceValue F}
      {ru : Ixon.RecursorRule} {rus : List Ixon.RecursorRule}
      (cell : h[addr]? = some (.construct krrListEnum "Cons" [v, rest]))
      (head : RecRuleRep t E₀ S rb crb rs nl base h j ru v)
      (tail : RecRulesRep t E₀ S rb crb rs nl base h (j + 1) rus rest) :
      RecRulesRep t E₀ S rb crb rs nl base h j (ru :: rus) (.ptr (.enum krrListEnum) addr)

theorem RecRulesRep.mono {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {S : _root_.Address → Prop}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {nl : Nat} {base : F} {h₁ h₂ : Heap F} {j : Nat} {rus : List Ixon.RecursorRule}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (hr : RecRulesRep t E₀ S rb crb rs nl base h₁ j rus p) :
    RecRulesRep t E₀ S rb crb rs nl base h₂ j rus p := by
  induction hr with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell head _ ih =>
    obtain ⟨rhs, rhsPtr, hv, hf, hl, htm, hin⟩ := head
    exact .cons (ext.getElem?_eq cell) ⟨rhs, rhsPtr, hv, hf, hl, htm.mono ext, hin⟩ ih

private theorem rulesTraceRep_to_recRulesRep {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hcl : UsedClosed R) {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {k : Nat} {r : Ixon.Recursor} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {h : Heap F}
    (hcrbR : recordOf R rb = some crb) (hmuts : crb.info = .muts rs)
    (hk : rs[k]? = some (.recr r)) (hnl : r.lvls.toNat < 4294967296)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData crb.binders.toList) tree)
    (hdef : ∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, r.rules[j]? = some ru →
      (exprReader t (fun x => E₀.blobs.get? x) crb id (blockSelf t rb rs)).read ru.rhs =
        .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true) :
    ∀ {j : Nat} {rus : List Ixon.RecursorRule} {p : SourceValue F},
      (∀ i ru, rus[i]? = some ru → r.rules[j + i]? = some ru) →
      L1.RulesTraceRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList) crb.univs.toList
        crb.sharing.toList blobs tree h j (mutsRoot rs k + 1 + ((j : Nat) : F)) rus p →
      RecRulesRep t E₀ (Held R) rb crb rs r.lvls.toNat (mutsRoot rs k) h j rus p := by
  intro j rus p hidx htr
  induction rus generalizing j p with
  | nil =>
    cases htr with
    | nil cell => exact .nil cell
  | cons ru rus ih =>
    cases htr with
    | cons cell hf raw planned levels rest =>
      have hj : r.rules[j]? = some ru := by
        simpa using hidx 0 ru rfl
      obtain ⟨rhs, hloaded, htm⟩ := rawConvExpr_to_tmOExact_loadedAt ht hnl
        (LoadedReads.blockSelf_ok t rb rs) (LoadedReads.blockSelf_key t rb rs)
        hblob raw built planned levels (fun E_rd hr => hdef j ru E_rd hj hr)
      have hru_mem : ru ∈ r.rules.toList :=
        List.mem_of_getElem? (show r.rules.toList[j]? = some ru by rw [Array.getElem?_toList]; exact hj)
      have hrhsIn : AddrIn (Held R) (Core.keyOf t) rhs :=
        addrIn_of_rkeysAt (E₀ := E₀) hwf
          (keys_held_of_loaded ht hwf hcl hcrbR (blockSelf_held hcl hcrbR hmuts)
            (fun l hl => mem_used_of_member hmuts hk l
              (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ru, hru_mem, hl⟩))) hloaded)
      have hcast : mutsRoot rs k + 1 + ((j : Nat) : F) + 1 =
          mutsRoot rs k + 1 + (((j + 1 : Nat) : F)) := by
        push_cast; ring
      rw [hcast] at rest
      refine .cons cell ⟨rhs, _, rfl, hf, hloaded, htm, hrhsIn⟩ (ih (fun i ru' hi => ?_) rest)
      have h1 := hidx (i + 1) ru' (by simpa using hi)
      rwa [show j + (i + 1) = (j + 1) + i by omega] at h1

/-- **`Ingress::get_ci` on a recursor-projection record `rprjAddr rb k`** produces the canonical
recursor type and rules on `TmOExact` and `AddrIn (Held R)`. -/
theorem recrLoad_ofStore {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {a : Bytes.Address} {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {k : Nat}
    {r : Ixon.Recursor}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hSrb : Held R rb) (hcrbE : recordOf E₀ rb = some crb)
    (hmuts : crb.info = .muts rs) (hk : rs[k]? = some (.recr r))
    (ha_addr : ixAddr a = memberAddr rb k (.recr r))
    (ra : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (ldci : loadValue m p = .ok ci) :
    ∃ (ty : KExpr) (tyPtr rulesPtr blkPtr : SourceValue F) (ba : Bytes.Address),
      ci = .construct kciEnum "Rec"
        [.field (r.lvls.toNat : F), tyPtr,
          .field (r.params.toNat : F), .field (r.indices.toNat : F),
          .field (r.motives.toNat : F), .field (r.minors.toNat : F),
          rulesPtr, L1.repBoolField r.k, L1.repBoolField r.isUnsafe,
          blkPtr, .field (k : F)] ∧
      r.lvls.toNat < 4294967296 ∧ r.params.toNat < 72057594037927936 ∧
      r.indices.toNat < 72057594037927936 ∧ r.motives.toNat < 72057594037927936 ∧
      r.minors.toNat < 72057594037927936 ∧ k < 72057594037927936 ∧
      loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
        (mutsRoot rs k) r.typ = some ty ∧
      TmOExact (Core.keyOf t) m ty tyPtr ∧ AddrIn (Held R) (Core.keyOf t) ty ∧
      ixAddr ba = rb ∧ Bytes.RepAddressRef addrTy m ba blkPtr ∧
      RecRulesRep t E₀ (Held R) rb crb rs r.lvls.toNat (mutsRoot rs k) m 0 r.rules.toList
        rulesPtr := by
  have hbd_cs : Bounded cs := RomBound.bounded_mono hbd hsub
  obtain ⟨rawBytes, c, hh, ha, hex, -, hblk⟩ := L1.get_ci_block_trace_spec hbd_cs ra ev
  have hcE : recordOf E₀ (ixAddr a) = some c := get_ci_record_eq hS hH hsub ra ev hh ha hex
  have hcrbR : recordOf R rb = some crb := held_of_sub hRsub hSrb hcrbE
  have hprojR : recordOf R (memberAddr rb k (.recr r)) = some (memberProjection rb k (.recr r)) :=
    (hcl.2 rb crb rs hcrbR hmuts k (.recr r) hk).1
  have hprojE : recordOf E₀ (ixAddr a) = some (memberProjection rb k (.recr r)) := by
    rw [ha_addr]; exact hRsub _ _ hprojR
  have hcEq : c = memberProjection rb k (.recr r) := Option.some.inj (hcE.symm.trans hprojE)
  subst hcEq
  simp only [L1.GetCIBlockTraceResult, memberProjection] at hblk
  obtain ⟨hk56, blkBytes, cb, ms, rc, blobs, tree, v, hhB, haB, hexB, hcb, hms, hhp, built, hld,
    hrecr⟩ := hblk
  rw [hld] at ldci; injection ldci with hv; subst hv
  have hcbEq : cb = crb := record_eq_of_hashed hS hsub hcrbE hhB haB hexB
  rcases hcbEq with rfl
  have hmsEq : ms = rs := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts)
  rcases hmsEq with rfl
  have hk_lt : k < UInt64.size := by
    have hsz : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
    have hblk_lt : blkBytes.size < 2 ^ 39 := by
      obtain ⟨c0, hc0, -, inp, hargs, hrep⟩ := hhB
      have hlt := RomBound.bounded_length_lt hbd_cs hc0 (by rw [hargs]; simp) hrep
      change blkBytes.data.toList.length < 2 ^ 39 at hlt
      have hbl : blkBytes.size = blkBytes.data.toList.length := by
        simp only [ByteArray.size, Array.length_toList]
      omega
    have := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound blkBytes cb hexB
    have := Claim.muts_size_le hmuts
    have h64 : UInt64.size = 18446744073709551616 := rfl
    omega
  have hk_u64 : k.toUInt64.toNat = k := by
    change (UInt64.ofNat k).toNat = k
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hk_lt
  rw [hk_u64] at hms hrecr hk56
  have hms' : ms[k]? = some (.recr rc) := by rw [← Array.getElem?_toList]; exact hms
  have hrcEq : rc = r := Ixon.MutConst.recr.inj (Option.some.inj (hms'.symm.trans hk))
  rcases hrcEq with rfl
  obtain ⟨hnl, hnp, hni, hnm, hnmi, -, tyPtr, rulesPtr, blkPtr, ba, planT, hba, rba, rfl,
    rty, hpT, hlT, hrls⟩ := hrecr
  obtain ⟨hnl', hdefT, hdefR⟩ := hlv.recr rb cb ms k rc hSrb hcrbE hmuts hk
  obtain ⟨ty, hloadedT, htmT⟩ := rawConvExpr_to_tmOExact_loadedAt ht hnl'
    (fun _ _ hx => by simp at hx) (fun _ _ _ _ hx => by simp at hx)
    (blobs_of_hashedPairs hS hsub hhp) rty built hpT hlT hdefT
  have htyIn : AddrIn (Held R) (Core.keyOf t) ty :=
    addrIn_of_rkeysAt (E₀ := E₀) hwf
      (keys_held_of_loaded ht hwf hcl hcrbR (blockSelf_held hcl hcrbR hmuts)
        (fun l hl => mem_used_of_member hmuts hk l (List.mem_append_left _ hl)) hloadedT)
  have hrls' : L1.RulesTraceRep cb.refs.toList (L1.blockRecurAddrs rb ms.toList) cb.univs.toList
      cb.sharing.toList blobs tree m 0 (mutsRoot ms k + 1 + ((0 : Nat) : F)) rc.rules.toList
      rulesPtr := by
    simpa [mutsRoot] using hrls
  have hrulesRep := rulesTraceRep_to_recRulesRep ht hwf hcl hcrbR hmuts hk hnl'
    (blobs_of_hashedPairs hS hsub hhp) built hdefR
    (fun i ru hi => by rw [Nat.zero_add, ← Array.getElem?_toList]; exact hi) hrls'
  exact ⟨ty, tyPtr, rulesPtr, blkPtr, ba, rfl, hnl', hnp, hni, hnm, hnmi, hk56,
    hloadedT, htmT, htyIn, hba, rba, hrulesRep⟩

private theorem mapIdx_ext {α β : Type} {f g : Nat → α → β} :
    ∀ (l : List α), (∀ i x, f i x = g i x) → l.mapIdx f = l.mapIdx g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapIdx_cons, h 0 x]
    congr 1
    exact mapIdx_ext xs (fun i y => h (i + 1) y)

/-- On an all-inductive block (`muts_indc_count = length`), `L1.blockRecurAddrs B ms.toList` equals
`indcAddrs B 0 ms.toList`. -/
theorem blockRecurAddrs_eq_indcAddrs_of_all_indc (B : _root_.Address) :
    ∀ (i : Nat) (ms : List Ixon.MutConst),
      (∀ m ∈ ms, ∃ ind, m = .indc ind) →
      ms.mapIdx (fun j m => Core.projAddr (Core.Specs.Callees.memberProjInfo B (i + j) m)) =
        indcAddrs B i ms
  | _, [], _ => rfl
  | i, m :: ms, hall => by
    obtain ⟨ind, rfl⟩ := hall m List.mem_cons_self
    simp only [List.mapIdx_cons, Nat.add_zero, indcAddrs,
      ← LoadedReads.memberAddr_eq_projAddr]
    congr 1
    have ih := blockRecurAddrs_eq_indcAddrs_of_all_indc B (i + 1) ms
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    rw [← ih]
    exact mapIdx_ext ms (fun j x => by
      rw [show i + (j + 1) = i + 1 + j by omega, LoadedReads.memberAddr_eq_projAddr])

theorem membersAt_eq_blockRecurAddrs {E₀ : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst}
    (hB : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hall : ∀ m ∈ ms.toList, ∃ ind, m = .indc ind) :
    membersAt E₀ B = some (L1.blockRecurAddrs B ms.toList) := by
  simp only [membersAt, hB, hmuts, L1.blockRecurAddrs_eq_mapIdx]
  congr 1
  have h := blockRecurAddrs_eq_indcAddrs_of_all_indc B 0 ms.toList hall
  simp only [Nat.zero_add] at h
  exact h.symm

/-! ## `KernelGuard::expr_inst_raw`, `definition_value`, `head`, `get_result_sort_level`, `block_elim` -/

/-- Every `TmExact` term lifts to a `RawTmExact` term with the same semantic expression `E`. -/
theorem tmExact_to_rawTmExact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : TmExact κ d Γ h k E p) : ∃ R, RawTmExact κ d Γ h k R E p := by
  induction rep with
  | bvarLocal cell hi hl => exact ⟨_, .bvarLocal cell hi hl⟩
  | bvarFree cell hi hge hd => exact ⟨_, .bvarFree cell hi hge hd⟩
  | sort cell rl => exact ⟨_, .sort cell rl⟩
  | const cell ra rls => exact ⟨_, .const cell ra rls⟩
  | app cell _ _ ihf iha =>
    obtain ⟨Rf, hf⟩ := ihf; obtain ⟨Ra, ha⟩ := iha
    exact ⟨.app Rf Ra, .app cell hf ha⟩
  | lam cell _ _ rl iht ihb =>
    obtain ⟨Rt, ht⟩ := iht; obtain ⟨Rb, hb⟩ := ihb
    exact ⟨.lam Rt Rb _, .lam cell ht hb rl⟩
  | forallE cell _ _ rl iht ihb =>
    obtain ⟨Rt, ht⟩ := iht; obtain ⟨Rb, hb⟩ := ihb
    exact ⟨.forallE Rt Rb _, .forallE cell ht hb rl⟩
  | letE cell _ _ _ iht ihv ihb =>
    obtain ⟨Rt, ht⟩ := iht; obtain ⟨Rv, hv⟩ := ihv; obtain ⟨Rb, hb⟩ := ihb
    exact ⟨.letE Rt Rv Rb default, .letE cell ht hv hb⟩
  | litNat cell hr hv => exact ⟨_, .litNat cell hr hv⟩
  | litStr cell hr hs => exact ⟨_, .litStr cell hr hs⟩
  | proj cell ra _ ih =>
    obtain ⟨Ri, hi⟩ := ih
    exact ⟨.proj _ _ Ri, .proj cell ra hi⟩

/-- **`KernelGuard::expr_inst_raw` on `TmOExact`**: raw universe instantiation at positional
parameters `List.range us.length`. -/
theorem expr_inst_raw_tmOExact {κ : _root_.Address → KKey} {E : KExpr} {us : List KLevel}
    {p xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hE : TmOExact κ h E p) (hus : RepKLevelList h us xus)
    (ev : ObsFn W "KernelGuard::expr_inst_raw" [p, xus] h r h' cs) :
    TmOExact κ h' (E.instantiateLevelParams (List.range us.length) us) r := by
  obtain ⟨k, rE⟩ := hE
  obtain ⟨R, rR⟩ := tmExact_to_rawTmExact rE
  exact ⟨k, (Decl.expr_inst_raw_exact rR hus ev).toTmExact⟩

private theorem klevel_length_canon {us : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepKLevelList h us l) : r = .field (us.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by
      rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol,
        ← IxVM.Refinement.Levels.klevelList_names]
      exact hl)

/-- **`KernelGuard::definition_value`** refines `defnValAt t E₀` on `TmOExact` and `AddrIn (Held R)`. -/
theorem guard_definition_value_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {a : Bytes.Address} {us : List KLevel} {xa xus r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls) (hSa : Held R (ixAddr a))
    (ra : Bytes.RepAddressRef addrTy h a xa) (rus : RepKLevelList h us xus)
    (ev : ObsFn W "KernelGuard::definition_value" [xa, xus] h r h' cs) :
    ∃ (nl : Nat) (val : KExpr),
      defnValAt t E₀ (ixAddr a) = some (nl, val) ∧
      us.length = nl ∧
      TmOExact (Core.keyOf t) h' (val.instantiateLevelParams (List.range us.length) us) r ∧
      AddrIn (Held R) (Core.keyOf t) (val.instantiateLevelParams (List.range us.length) us) := by
  match Obs.«KernelGuard::definition_value».obs ev with
  | .run (m2 := m1) (p9 := pci) (cs15 := cs1) (x_nl := xnl) (x_value := xval) (v68 := vlen)
      (m71 := m2) (cs79 := cs2) (cs101 := cs3) (ev17 := evg) (ld11 := ldci) (ev81 := evl)
      (heq97 := hlen_eq) (ev103 := evi) (hc120 := hc) .. =>
    have hsub1 : ∀ c ∈ cs1, c ∈ rootCalls := fun c hm => hsub c (by rw [hc]; simp [hm])
    obtain ⟨hyes, -⟩ := defnLoad_ofStore ht hwf hS hH hbd hRsub hcl hlv hsub1 hSa ra evg ldci
    obtain ⟨nl, val, rfl, hnl, hval, hvalIn, -, hdv⟩ := hyes _ _ _ _ _ rfl
    have rus1 := rus.mono evg.heap_extends
    have hus_lt : us.length < 2 ^ 39 :=
      RomBound.bounded_length_lt (RomBound.bounded_mono hbd hsub)
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [xus], m1⟩)
        (by rw [hc]; simp) (by simp) rus1
    obtain ⟨rfl, rfl⟩ := klevel_length_canon evl rus1
    have hlen : us.length = nl := natCast_inj_small (by omega) (by omega) (Value.field.inj hlen_eq)
    exact ⟨nl, val, hdv, hlen, expr_inst_raw_tmOExact hval rus1 evi,
      addrIn_instantiateLevelParams (List.range us.length) us hvalIn⟩

/-- **`KernelGuard::head`** refines `GuardHead (defnValAt t E₀) (keyAddr t)` on `TmOExact` and
`AddrIn (Held R)`. -/
theorem guard_head_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (N : Nat) {E : KExpr} {p budget r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length < N →
      (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact (Core.keyOf t) h E p →
      AddrIn (Held R) (Core.keyOf t) E →
      ObsFn W "KernelGuard::head" [p, budget] h r h' cs →
      ∃ E' : KExpr, GuardHead (defnValAt t E₀) (keyAddr t) E E' ∧
        TmOExact (Core.keyOf t) h' E' r ∧ AddrIn (Held R) (Core.keyOf t) E' := by
  intro N
  induction N with
  | zero => intro _ _ _ _ _ _ _ hlen; exact absurd hlen (Nat.not_lt_zero _)
  | succ N ih =>
    intro E p budget r h h' cs hlen hsub hE hEin ev
    have rsub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
      fun hs c hc => hsub c (hs c hc)
    match Obs.«KernelGuard::head».obs ev with
    | .n0 (heq40 := he) .. | .other_other (heq453 := he) .. =>
      exact absurd (Value.field.inj he) (by decide)
    | .other_Srt (ld60 := ld) (he75 := hr) (he76 := hh) .. =>
      subst hr hh
      obtain ⟨l, rfl, -⟩ := TmOExact.sort_of_load hE ld
      exact ⟨.sort l, .sort l, hE, hEin⟩
    | .other_Forall (ld60 := ld) (he104 := hr) (he105 := hh) .. =>
      subst hr hh
      obtain ⟨D, B, ℓ, rfl, -⟩ := TmOExact.forallE_of_load hE ld
      exact ⟨.forallE D B (bmeta ℓ), .forallE D B (bmeta ℓ), hE, hEin⟩
    | .other_Lam (ld60 := ld) (he133 := hr) (he134 := hh) .. =>
      subst hr hh
      obtain ⟨D, B, ℓ, rfl, -⟩ := TmOExact.lam_of_load hE ld
      exact ⟨.lam D B (bmeta ℓ), .lam D B (bmeta ℓ), hE, hEin⟩
    | .other_Const (x_a := xa) (x_us := xus) (cs156 := cs2) (v159 := v1) (m162 := m1)
        (cs170 := cs1) (ld60 := ld) (ev172 := evdv) (ev158 := ev2) (hc204 := hc) .. =>
      obtain ⟨a, us, rfl, ra, rus⟩ := TmOExact.const_of_load hE ld
      have hSa : Held R (ixAddr a) := hEin (ixAddr a) rfl
      obtain ⟨nl, val, hdv, hlen_us, hval, hvalIn⟩ :=
        guard_definition_value_spec ht hwf hS hH hbd hRsub hcl hlv
          (rsub fun c hc' => by rw [hc]; simp [hc']) hSa ra rus evdv
      obtain ⟨E', hgh, hE', hE'in⟩ := ih
        (by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega)
        (rsub fun c hc' => by rw [hc]; simp [hc']) hval hvalIn ev2
      exact ⟨E', .const (keyAddr_keyOf hwf (ixAddr a)) hdv hlen_us hgh, hE', hE'in⟩
    | .other_App (x_f := xf) (x_a := xa) (m223 := m1) (p230 := pf) (cs236 := cs1)
        (x_body := xb) (cs286 := cs3) (v289 := vi) (m292 := m2) (cs300 := cs2)
        (ld60 := ld) (ev238 := evf) (ld232 := ldlam) (ev302 := evi) (ev288 := ev2)
        (hc341 := hc) .. =>
      obtain ⟨Ef, Ea, rfl, hEf, hEa⟩ := TmOExact.app_of_load hE ld
      obtain ⟨f', hghf, hf', hf'In⟩ := ih
        (by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega)
        (rsub fun c hc' => by rw [hc]; simp [hc']) hEf hEin.1 evf
      obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.lam_of_load hf' ldlam
      have hinst := expr_inst1_tmOExact
        (RomBound.bounded_mono hbd (rsub fun c hc' => by rw [hc]; simp [hc']))
        hB (hEa.mono evf.heap_extends) evi
      have hinstIn := addrIn_instantiate1Lift (d := 0) hEin.2 hf'In.2
      obtain ⟨E', hgh2, hE', hE'in⟩ := ih
        (by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega)
        (rsub fun c hc' => by rw [hc]; simp [hc']) hinst hinstIn ev2
      exact ⟨E', .app hghf hgh2, hE', hE'in⟩
    | .other_Let (x_value := xv) (x_body := xb) (cs368 := cs2) (v371 := vi) (m374 := m1)
        (cs382 := cs1) (ld60 := ld) (ev384 := evi) (ev370 := ev2) (hc423 := hc) .. =>
      obtain ⟨T, V0, B, rfl, -, hV, hB⟩ := TmOExact.letE_of_load hE ld
      have hinst := expr_inst1_tmOExact
        (RomBound.bounded_mono hbd (rsub fun c hc' => by rw [hc]; simp [hc']))
        hB hV evi
      exact ih
        (by rw [hc] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega)
        (rsub fun c hc' => by rw [hc]; simp [hc']) hinst hEin ev2

/-- **`KernelCheck::get_result_sort_level`** refines `ResultSort (defnValAt t E₀) (keyAddr t)` on
`TmOExact` and `AddrIn (Held R)`. -/
theorem get_result_sort_level_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R)) :
    ∀ (n : Nat) {E : KExpr} {xrc xty xtys r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact (Core.keyOf t) h E xty →
      AddrIn (Held R) (Core.keyOf t) E →
      ObsFn W "KernelCheck::get_result_sort_level" [xrc, xty, .field (n : F), xtys] h r h' cs →
      ∃ lvl : KLevel, ResultSort (defnValAt t E₀) (keyAddr t) n E lvl ∧ RepKLevel h' lvl r := by
  intro n
  induction n with
  | zero =>
    intro E xrc xty xtys r h h' cs _ hsub hE hEin ev
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (v1 := vw) (m2 := m1) (cs12 := cs1) (x_l := xl) (ev14 := evh) (ld55 := lds)
        (he69 := hr) (he70 := hh) (hc71 := hc) .. =>
      subst hr hh
      obtain ⟨W0, hgh, hW, -⟩ := guard_head_spec ht hwf hS hH hbd hRsub hcl hlv
        (cs1.length + 1) (Nat.lt_succ_self _)
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin evh
      obtain ⟨lvl, rfl, rl⟩ := TmOExact.sort_of_load hW lds
      exact ⟨lvl, .zero hgh, rl⟩
    | .other (hne73 := hne) .. => exact (hne (by simp)).elim
  | succ n ih =>
    intro E xrc xty xtys r h h' cs hn hsub hE hEin ev
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv43 := hv) .. =>
      exact absurd (field_natCast_eq_zero hn hv) (by omega)
    | .other (v1 := vw) (m2 := m1) (cs12 := cs1) (x_dom := xdom) (x_body := xbody)
        (cs115 := cs2) (v120 := vn) (m152 := m2) (ev14 := evh) (ld88 := ldf)
        (op149 := op) (hm160 := hm2) (ev117 := evrec) (hc180 := hc) .. =>
      subst hm2
      obtain rfl := evalBinOp_sub_succ n op
      obtain ⟨W0, hgh, hW, hWin⟩ := guard_head_spec ht hwf hS hH hbd hRsub hcl hlv
        (cs1.length + 1) (Nat.lt_succ_self _)
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin evh
      obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hW ldf
      have ext2 : Heap.Extends m1 (m1 ++ [.construct kexprListEnum "Cons" [xdom, xtys]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨lvl, hrs, rl⟩ := ih (by omega)
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (hB.mono ext2) hWin.2 evrec
      exact ⟨lvl, .succ hgh hrs, rl⟩

/-- **`KernelModeled::block_elim`** refines `BlockElim t E₀ B off` on an all-inductive block `B`
held in `R`, yielding `bnl < 2^32` and `off ∈ {0, 1}` with `r = (bnl, off)`. -/
theorem block_elim_spec {rootCalls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore rootCalls E₀) (hH : LoadedReads.HashedRecordsStored rootCalls E₀)
    (hbd : Bounded rootCalls)
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hlv : StoreLevelsOk t E₀ (Held R))
    {B : _root_.Address} {addrs : List Bytes.Address}
    {xrc xta r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hmemAt : membersAt E₀ B = some (addrs.map ixAddr))
    (hheld : ∀ a ∈ addrs, Held R (ixAddr a))
    (hta : RepList addrListEnum (fun h a p => Bytes.RepAddressRef addrTy h a p) h addrs xta)
    (ev : ObsFn W "KernelModeled::block_elim" [xrc, xta] h r h' cs) :
    ∃ (bnl off : Nat),
      r = .tuple [.field (bnl : F), .field (off : F)] ∧
      bnl < 4294967296 ∧ (off = 0 ∨ off = 1) ∧
      BlockElim t E₀ B off := by
  match Obs.«KernelModeled::block_elim».obs ev with
  | .run (x_t0 := xt0) (x_rest := xrest) (m27 := m1) (p35 := p1) (cs41 := cs1)
      (x_nl := xnl) (x_ty := xty) (x_np := xnp) (x_ni := xni) (v102 := vlvl) (m103 := m2)
      (cs113 := cs2) (v118 := vnpni) (m151 := m1b) (m164 := m3) (cs174 := cs3)
      (v212 := voff) (m222 := m4) (cs230 := cs4) (ld11 := ldt) (ev43 := evg) (ld37 := ldci)
      (op147 := op) (hm159 := hm1b) (ev115 := evrs) (ev176 := evp) (he213 := hr)
      (ev232 := evnz) (he241 := hh) (hc242 := hc) .. =>
    subst hm1b hr hh
    obtain ⟨t0, rest, rfl, rt0, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hta ldt
    have hSt0 : Held R (ixAddr t0) := hheld t0 List.mem_cons_self
    obtain ⟨hyes, -⟩ := indAnswers_ofStore ht hwf hS hH hbd hRsub hcl hlv
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hSt0 rt0 evg ldci
    obtain ⟨d, ba, hindAt, hnl, hnp, hni, -, -, rfl, hty, htyIn, -, rfl, rfl, -, -, -, -⟩ :=
      hyes _ _ _ _ _ _ _ _ rfl
    obtain rfl := binop_add_nat op
    have ext1 : Heap.Extends m1 (m1 ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
    obtain ⟨lvl, hrs, rl⟩ := get_result_sort_level_spec ht hwf hS hH hbd hRsub hcl hlv
      (d.np + d.ni) (by omega)
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) (hty.mono ext1) htyIn evrs
    obtain ⟨hoff, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step evnz vlvl rfl lvl
      (rl.mono evp.heap_extends)
    have hindTy : indTypeAt t E₀ (ixAddr t0) = some (d.nl, d.ty, d.np, d.ni) := by
      obtain ⟨c, p, cb, ms, ind, hcE, hci, hcbE, hcbi, hm, hld, -⟩ := indDataAt_inv hindAt
      have hd_eq : d = ⟨ind.lvls.toNat, d.ty, ind.params.toNat, ind.indices.toNat,
          ind.ctors.size, p.block, p.idx.toNat⟩ := by
        unfold ReconView.ofStore indDataAt at hindAt
        simp only [hcE, hci, hcbE, hcbi, hm, hld, Option.some.injEq] at hindAt
        exact hindAt.symm
      rw [hd_eq]
      unfold indTypeAt
      simp only [hcE, hci, hcbE, hcbi, hm, hld]
    refine ⟨d.nl, if lvl.isNeverZero then 1 else 0, ?_, hnl, ?_, ?_⟩
    · rw [hoff]
      cases lvl.isNeverZero <;> simp
    · cases lvl.isNeverZero <;> simp
    · exact ⟨ixAddr t0, rest.map ixAddr, d.nl, d.np, d.ni, d.ty, lvl,
        by simpa using hmemAt, hindTy, hrs, rfl⟩

end IxVM.Refinement.Binding.FamilyRecon

