import IxVMRefinement.Assembly.TypingRecLateRules
import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Decl.ModeledTele

/-! # The elimination restriction of the late recursor

The late relation asks, of a large eliminator, that the family's result sort be never zero or
that the family have fewer than two constructors. The circuit decides the eliminator's size in
`check_recursor_canonical_full`: `is_large_eliminator(rc, result_level, num_ctors, …)` with
`result_level = get_result_sort_level(rc, parent_type, n_p + n_i, [])`, and `nat_rec_check`
asserts that the record's level count is the parent's plus that verdict. This module reads the
restriction off those runs:

* `RecArmAt`, `rec_arm_of_arm`: `RecCanonAt` with the parent's load kept (the pointer the
  scoped `get_ci` answers at, so that its type is the stored former's under the prefix keying)
  and the parent's count bounds;
* `get_result_sort_level_any_spec`: `get_result_sort_level_scoped_bounded_spec` without the
  table-keyed instance, which its proof does not use (the prefix keying is not table-keyed);
* `Decl.ResultSortReads`, `FormerSortReads`: what the result-sort walk answers on a term, as a
  statement about every observed run; for a syntactic telescope it holds by reading
  (`ResultSortReads.of_strip`), and a registered family gives it from its recorded walk;
* `ciRep_induct_fields`, `eval_ne_zero_of_posOf`, `evalBinOp_add_inv`, `nat_rec_check_levels`;
* `canonical_full_elim`: from the canonical run, at a record with one level more than its
  parent, the level the result-sort walk answers on the parent's type is never zero or the
  parent has fewer than two constructors;
* `rec_elim_of_arm`: the restriction at the family read off the tied parent.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)

/-- **`get_result_sort_level` under any scoped context**: the returned level is the result sort
of the type's `n`-binder telescope, up to semantic equality. -/
theorem get_result_sort_level_any_spec {c : ScopedCtx} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      Tm c.κ d Γ h 0 E pe →
      ObsFn W "KernelCheck::get_result_sort_level" [rc, pe, .field (n : F), types] h r h' cs →
      ∃ ℓ : KLevel, RepKLevel h' ℓ r ∧
        ∀ bs s, E.stripPis n = some (bs, .sort s) → LvEq s ℓ
  | 0, d, Γ, E, rc, pe, types, r, h, h', cs, _, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (cs12 := cs12) (ev14 := ev_w) (ld55 := ld) (he69 := hr) (he70 := hh) (hc71 := hc) .. =>
      subst hc hr hh
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hrigid⟩ := Core.GuardData.head_rep ⟨hef, hlf⟩ hg1 hE ev_w
      obtain ⟨u, rfl, ℓ, hℓ, huℓ⟩ := hE'.sort_of_load ld
      refine ⟨ℓ, hℓ, fun bs s hst => ?_⟩
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      have hsort := hrigid rfl
      injection hsort with hsu
      subst hsu
      exact huℓ
    | .other (hne73 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, rc, pe, types, r, h, h', cs, hlt, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv43 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other (cs12 := cs12) (x_body := xbody) (cs115 := cs2) (m152 := m3) (ev14 := ev_w)
        (ld88 := ld) (op149 := op) (hm160 := hm3) (ev117 := ev_rec) (hc180 := hc) .. =>
      subst hc
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      have hg2 : CoreGood c cs2 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hrigid⟩ := Core.GuardData.head_rep ⟨hef, hlf⟩ hg1 hE ev_w
      obtain ⟨T, B, _, rfl, hT, hB, _⟩ := hE'.forallE_of_load ld
      have ext_w := ev_w.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm3] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m3 0 (B.instantiate1 (.fvar d T)) xbody :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ m op] at ev_rec
      obtain ⟨ℓ, hℓ, htele⟩ := get_result_sort_level_any_spec m (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hef hlf hg2 hB_open ev_rec
      refine ⟨ℓ, hℓ, fun bs s hst => ?_⟩
      cases E with
      | forallE dom₀ bo₀ m₀ =>
        obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (hrigid rfl)
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs₁, body₁⟩, hst₁, hst⟩ := hst
        simp only [Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        obtain ⟨bs₂, hst₂⟩ := stripPis_instantiate1_sort m (v := .fvar d T) (k := 0) hst₁
        exact htele bs₂ s hst₂
      | _ => simp [Expr.stripPis] at hst

/-- **The result-sort walk on `A` answers `s`**: every observed run of
`KernelCheck::get_result_sort_level` for `n` binders, at depth zero and with good calls, on a
pointer that represents `A`, returns a level semantically equal to `s`. For a term whose first
`n` nodes are `∀`s into `Sort s` it holds by reading (`ResultSortReads.of_strip`); for a type
that only head-reduces to such a telescope it is what the recorded walk of the type gives. -/
def ResultSortReads (c : ScopedCtx) (n : Nat) (A : KExpr) (s : KLevel) : Prop :=
  ∀ {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    RCRep c.t c.lim h rc → TypesRep c.κ (fun _ => default) h 0 types → CoreGood c cs →
    Tm c.κ 0 (fun _ => default) h 0 A pe →
    ObsFn W "KernelCheck::get_result_sort_level" [rc, pe, .field (n : F), types] h r h' cs →
    ∃ ℓ : KLevel, RepKLevel h' ℓ r ∧ LvEq s ℓ

/-- On a term whose first `n` nodes are `∀`s into `Sort s` the walk answers `s`. -/
theorem ResultSortReads.of_strip {c : ScopedCtx} (hc : ScopedCoreFacts c) {n : Nat}
    {A : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {s : KLevel}
    (hn : n < 18446744069414584321) (hs : A.stripPis n = some (bs, .sort s)) :
    ResultSortReads c n A s := by
  intro rc pe types r h h' cs hrc hty hgood hA ev
  obtain ⟨ℓ, hℓ, hlv⟩ := get_result_sort_level_any_spec n hn hrc hty (ghostScoped_zero _)
    hc.env hc.loads hgood hA ev
  exact ⟨ℓ, hℓ, hlv bs s hs⟩

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-! ## The arm with the parent's load -/

/-- **`RecCanonAt` with the parent's load kept**: the scan heap and the parent's address there,
the scoped load of the parent (`get_ci`) answering the pointer whose value is the parent's read
`Induct` value, and the parent's count bounds. -/
def RecArmAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (lim : Option Nat) (A : _root_.Address) (c : Ixon.Constant)
    (rc : Ixon.Recursor) (P : _root_.Address) (ip : Ixon.InductiveProj)
    (ind : Ixon.Inductive) : Prop :=
  ∃ (rcv apv parentV tyPtr rulesPtr blkPtr tyPtrP unsP blkPtrP kTarget result pointer :
      SourceValue F)
    (bA bR bT bP : Bytes.Address) (blobs : List (_root_.Address × ByteArray))
    (tree : Ingress.BinderTreeData) (scanHeap loadedHeap kHeap kAfter canonHeap final : Heap F)
    (loadCalls kCalls canonCalls : List (Call F)),
    Core.RCRep t lim loadedHeap rcv ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bA apv ∧ Core.ixAddr bA = A ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bR blkPtr ∧ Core.ixAddr bR = A ∧
    Bytes.RepAddressRef Core.addrTy scanHeap bT parentV ∧ Core.ixAddr bT = P ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bP blkPtrP ∧ Core.ixAddr bP = ip.block ∧
    (∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs) ∧
    Ingress.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs loadedHeap 4294967295
      rc.typ tyPtr ∧
    Ingress.RulesTraceRep c.refs.toList [A] c.univs.toList c.sharing.toList blobs tree loadedHeap 0
      (0 + 1) rc.rules.toList rulesPtr ∧
    rc.rules.size < 8589934592 ∧ ip.idx.toNat < 72057594037927936 ∧
    rc.lvls.toNat < 4294967296 ∧ ind.lvls.toNat < 4294967296 ∧
    ind.params.toNat < 72057594037927936 ∧ ind.indices.toNat < 72057594037927936 ∧
    ind.ctors.size < 72057594037927936 ∧
    Heap.Extends scanHeap loadedHeap ∧
    ObsFn Obs.W "Ingress::get_ci" [parentV] scanHeap pointer loadedHeap loadCalls ∧
    (∀ cl ∈ loadCalls, cl ∈ calls) ∧
    loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
        .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
        .field (ip.idx.toNat : F)]) ∧
    Heap.Extends loadedHeap kHeap ∧
    ObsFn Obs.W "KernelCheck::compute_k_target"
      [rcv, .construct "KernelTypes::KConstantInfo" "Induct"
        [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
          .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
          .field (ip.idx.toNat : F)], parentV] kHeap kTarget kAfter kCalls ∧
    (∀ cl ∈ kCalls, cl ∈ calls) ∧ Ingress.repBoolField rc.k = kTarget ∧
    Heap.Extends loadedHeap canonHeap ∧
    ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rcv, .construct "KernelTypes::KConstantInfo" "Rec"
        [.field (rc.lvls.toNat : F), tyPtr, .field (rc.params.toNat : F),
          .field (rc.indices.toNat : F), .field (rc.motives.toNat : F),
          .field (rc.minors.toNat : F), rulesPtr, Ingress.repBoolField rc.k,
          Ingress.repBoolField rc.isUnsafe, blkPtr, .field ((0 : Nat) : F)], apv,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
            .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
            .field (ip.idx.toNat : F)], parentV]
      canonHeap result final canonCalls ∧
    (∀ cl ∈ canonCalls, cl ∈ calls)

/-- **The arm at the tied parent, with the parent's load** (the derivation of
`rec_canon_of_arm`, keeping the load). -/
theorem rec_arm_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    RecArmAt calls t E₀ lim A c rc P ip ind := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, hrcM, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk, hfr⟩ := hnat
  obtain ⟨rawB, cB, hszB, hhB, hbaB, hexB⟩ := get_ci_bytes_bound ha_pre ev_ld
  have hcB : cB = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hhB) hbaB hexB
  subst cB
  have hrules_lt := recr_rules_size_lt hszB hexB hinfo
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    Ingress.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold Ingress.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, bR, planT, hbR, hblkR, hv,
    rty, -, -, hrulesTr⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfields
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk hfr
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  have hrd : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
      (soloSelf t (Core.ixAddr a'))).read rc.typ = .ok tyP := by
    rw [Assembly.recParam_range]
    exact htyP
  obtain ⟨E', hann, htm⟩ := rty.toTmC (κ := Core.keyOf t) (ps := List.range rc.lvls.toNat)
    (by simp) (by simpa using hlvls) (LoadedReads.readCtx_keyAt_inv ht _)
    (fun i x m k hx => by simp at hx) hblob hrd hlbb hdef
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := lim) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, canonResult, canonFinal, evScan, hsScan, evLoad, hsLoad, hldP, evRoute, hsRoute,
    hnp, hni, eLen, evLen, hsLen, hlenEq, eK, evK, hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    native_rec_member_full evM
  have hsScan' : ∀ x ∈ scanCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsScan x hx))
  have hsLoad' : ∀ x ∈ loadCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsLoad x hx))
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  have htmM := htmS.mono hextM
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := Decl.scopedCalleesSpec cS hcS .rec_to_parent_addr _ _ _
    _ _ evScan _ _ _ _ _ rfl (Core.CoreGood.ofRaw (hgood.sub hsScan') (fun _ _ => trivial)) E' htmM
  have hkr : Core.KeysResolved E' := (htmM 0 (fun _ => .sort .zero)).keysResolved
  have hne : cS.κ (Core.ixAddr a) ≠ Core.unresolvedKey :=
    keysResolved_getAppFn (keysResolved_piDomAt _ hkr hpi) hhead
  have hkey : cS.κ (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) := cS.key_eq hne
  have hhead' := hhead
  rw [hkey] at hhead'
  have hmajA : majorKey rc E' = some (keyOf t (Core.ixAddr a)) :=
    majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead'
  obtain ⟨tyP', E'', htyP', hann', hmajP⟩ := htie
  have htyEq : tyP' = tyP := Except.ok.inj (htyP'.symm.trans htyP)
  subst htyEq
  have hkeys : keyOf t P = keyOf t (Core.ixAddr a) :=
    Option.some.inj (hmajP.symm.trans ((majorKey_annotates_eq (rc := rc) hann' hann).trans hmajA))
  have hPa : P = Core.ixAddr a := keyOf_inj hroles hkeys
  subst hPa
  have hgL : Core.Good ⟨E, env, t, lim⟩ loadCalls := hgood.sub hsLoad'
  obtain ⟨rawP, cP, hhP, hbaP, hexP, -, hresP⟩ := Ingress.get_ci_block_trace_spec hgL.2 ha evLoad
  have hrecP : recordOf E (Core.ixAddr a) = some cm := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcm
  obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrecP
  have hbP : rawP = lc.rawBytes := Core.load_escape hget hgL.1 rawP hhP hbaP
  have hcP : cP = cm := by
    rw [hbP, hdec] at hexP
    exact (Except.ok.inj hexP).symm
  subst hcP
  unfold Ingress.GetCIBlockTraceResult at hresP
  rw [hcmi] at hresP
  obtain ⟨-, blkBytes, cb', ms', ind', blobs', tree', plan', v₀, hhB', haB', hexB', hcb', hms',
    -, -, -, hld₀, hraw, -⟩ := hresP
  have hrecB : recordOf E ip.block = some cb := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcb
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hrecB
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hgL.1 blkBytes hhB' haB'
  have hcbEq : cb' = cb := by
    rw [hbB, hdecB] at hexB'
    exact (Except.ok.inj hexB').symm
  subst hcbEq
  have hmsEq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hms)
  subst hmsEq
  have hlist : ms'.toList[ip.idx.toNat]? = ms'[ip.idx.toNat]? := by simp
  rw [hlist, hind] at hms'
  have hindEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj hms')
  subst hindEq
  obtain ⟨hlvlsP, hpP, hiP, hcP56, hidxP, tyPtrP, blkPtrP, bP, hbPa, hblkP, hvP, -⟩ := hraw
  subst hvP
  have hldP0 := hld₀
  rw [hld₀] at hldP
  injection hldP with hvP'
  injection hvP' with _ _ hpf
  simp only [List.cons.injEq, and_true] at hpf
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpf
  have extL : Heap.Extends m_chk loadedHeap :=
    hextM.trans (evScan.heap_extends.trans evLoad.heap_extends)
  have extA : Heap.Extends h_pre loadedHeap := ev_ld.heap_extends.trans extL
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, a', bR, a, bP, blobs, tree,
    scanHeap, loadedHeap, kHeap, kAfter, canonHeap, canonFinal, loadCalls, kCalls, canonCalls,
    hrcM.mono extL,
    Bytes.repAddressRef_heapMono₂ Core.addrTy extA ha'_ref, rfl,
    Bytes.repAddressRef_heapMono₂ Core.addrTy extL hblkR, hbR,
    ha, rfl,
    hblkP, hbPa, hblob, rty.mono extL (fun q hq => hq), hrulesTr.mono extL (fun q hq => hq),
    hrules_lt, hidxP, hlvls, hlvlsP, hpP, hiP, hcP56, evLoad.heap_extends, evLoad, hsLoad',
    hldP0, eK, evK, fun x hx => hsub_chk x (hsubM x (hsK x hx)), hkEq, eC, evCanon,
    fun x hx => hsub_chk x (hsubM x (hsCanon x hx))⟩

/-! ## Small facts -/

/-- A loaded `Induct` value represents an inductive type, its level count and type
represented. -/
theorem ciRep_induct_fields {κ : _root_.Address → Core.KKey} {h : Heap F}
    {nl ty np ni nc u blk idx : SourceValue F} {ci : ConstantInfo .anon}
    (r : Core.CIRep κ h (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) ci) :
    ∃ cv caps, ci = .indInfo cv caps ∧ Core.ValRep κ h nl ty cv := by
  generalize hv : (Value.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx] :
    SourceValue F) = v at r
  cases r
  case induct hvr hcounts hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, rfl, hvr⟩
  all_goals (injection hv with _ hc' _; exact absurd hc' (by decide))

/-- **A level renamed to positions is never zero only if the level is never zero.** -/
theorem eval_ne_zero_of_posOf {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) {s : Ix.Kernel.Level}
    (h : ∀ φ, Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst ps (Core.posLevels ps) s) ≠ 0) :
    ∀ ψ, Ix.Kernel.Level.eval ψ s ≠ 0 := by
  intro ψ
  have h' := h (Decl.posVal ps ψ)
  rwa [Ix.Kernel.Level.eval_subst, Decl.substFn_posVal hperm] at h'

/-- An addition of a field element that answers a field element added that element's
difference. -/
theorem evalBinOp_add_inv {a b : F} {x : SourceValue F}
    (h : evalBinOp .add (.field a) x = .ok (.field b)) : x = .field (b - a) := by
  cases x
  case field y =>
    have h' : a + y = b := by simpa [evalBinOp] using h
    rw [← h']
    simp
  all_goals simp [evalBinOp] at h

/-- **`nat_rec_check`'s level link**: the record's level count is the parent's plus the
eliminator's offset. -/
theorem nat_rec_check_levels
    {rc levels type parameters indices motives minors rules k unsafeFlag block position address
      parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock
      parentIndex parent univOffset result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::nat_rec_check"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
            parentBlock, parentIndex], parent, univOffset]
      heap result final calls) :
    evalBinOp .add parentLevels univOffset = .ok levels := by
  match Obs.«KernelCheck::nat_rec_check».obs observed with
  | .run (hv11 := recShape) (hv81 := parentShape) (op159 := hop) (heq162 := heq) .. =>
    injection recShape with _ _ recFields
    simp only [List.cons.injEq, and_true] at recFields
    injection parentShape with _ _ parentFields
    simp only [List.cons.injEq, and_true] at parentFields
    rw [parentFields.1, recFields.1, heq]
    exact hop

/-- A field image of a small count equal to `1` is `1`. -/
theorem field_nat_eq_one {a : Nat} (ha : a < 18446744069414584321)
    (h : ((.field (a : F)) : SourceValue F) = .field 1) : a = 1 := by
  have h' : ((.field (a : F)) : SourceValue F) = .field ((1 : Nat) : F) := by
    rw [Nat.cast_one]
    exact h
  exact field_nat_inj ha (by norm_num) h'

/-- A field image of a small count equal to `0` is `0`. -/
theorem field_nat_eq_zero {a : Nat} (ha : a < 18446744069414584321)
    (h : ((.field (a : F)) : SourceValue F) = .field 0) : a = 0 := by
  have h' : ((.field (a : F)) : SourceValue F) = .field ((0 : Nat) : F) := by
    rw [Nat.cast_zero]
    exact h
  exact field_nat_inj ha (by norm_num) h'

/-! ## The restriction from the canonical comparison -/

/-- **The elimination restriction from the canonical comparison**: at a record with one level
more than its parent, under a scoped context that allows every call, where the parent's type
pointer represents `E` and the result-sort walk on `E` over the parent's parameters and
indices answers `s`, the level `s` is never zero or the parent has fewer than two
constructors. -/
theorem canonical_full_elim {c : Core.ScopedCtx} (hc : Core.ScopedCoreFacts c)
    (hall : ∀ cl, c.allowed cl)
    {rcv type parameters indices motives minors rules k unsafeFlag block position address
      parentType parentUnsafe parentBlock parentIndex parent result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    {lvls plvls pnp pni nctors : Nat} {E : Core.KExpr}
    (hrc : Core.RCRep c.t c.lim heap rcv) (hgood : Core.Good c.toCtx calls)
    (hE : Core.TmC c.κ heap E parentType)
    (hnc : nctors < 18446744069414584321) {s : Core.KLevel}
    (hrd : Decl.ResultSortReads c (pnp + pni) E s)
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rcv, .construct "KernelTypes::KConstantInfo" "Rec"
        [.field (lvls : F), type, parameters, indices, motives, minors, rules, k, unsafeFlag,
          block, position], address,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [.field (plvls : F), parentType, .field (pnp : F), .field (pni : F),
            .field (nctors : F), parentUnsafe, parentBlock, parentIndex], parent]
      heap result final calls)
    (hlarge : lvls = plvls + 1) :
    (∀ φ, Ix.Kernel.Level.eval φ s ≠ 0) ∨ nctors < 2 := by
  match Obs.«KernelCheck::check_recursor_canonical_full».obs observed with
  | .other (hne568 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct (m272 := m272) (m329 := m329) (m281 := m281) (m389 := m389) (v280 := resLvl)
      (v296 := nsum) (v341 := univ) (cs291 := cs291) (sg279 := seg) (op325 := hsumOp)
      (hm337 := hm337) (ev293 := sortRun) (ev399 := soloRun) (ev354 := largeRun)
      (ev518 := natRun) (hc567 := children) (hv86 := parentShape) .. =>
    injection parentShape with _ _ parentFields
    simp only [List.cons.injEq, and_true] at parentFields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := parentFields
    have e1 : Heap.Extends heap m272 := by
      match seg with
      | .n1 (ev159 := e) (he201 := hh) .. =>
        rw [hh]
        exact e.heap_extends
      | .other (hm245 := e1) (hm259 := e2) (he269 := e3) .. =>
        rw [e3, e1, e2]
        exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have e2 : Heap.Extends heap m329 := e1.trans (ext_of_eq_snoc hm337)
    have hnsum : nsum = .field ((pnp + pni : Nat) : F) := Decl.evalBinOp_add_nat pnp pni hsumOp
    rw [hnsum] at sortRun
    have hgS : Core.CoreGood c cs291 :=
      Core.CoreGood.ofRaw (hgood.sub (fun x hx => by rw [children]; simp [hx]))
        (fun cl _ => hall cl)
    have htys : Core.TypesRep c.κ (fun _ => default) m329 0
        (.ptr (.enum Core.kexprListEnum) m272.length) := by
      rw [hm337]
      exact Decl.typesRep_alloc_nil _ _ _
    obtain ⟨ℓ, hℓ, hsℓ⟩ := hrd (hrc.mono e2) htys hgS ((hE.mono e2) 0 (fun _ => default)) sortRun
    have huniv : univ = .field 1 := by
      rw [evalBinOp_add_inv (nat_rec_check_levels natRun), hlarge]
      congr 1
      push_cast
      ring
    rw [huniv] at largeRun
    have hℓ' : IxVM.Refinement.KernelLevels.RepKLevel m389 ℓ resLvl :=
      IxVM.Refinement.KernelLevels.repKLevel_heapMono₂ soloRun.heap_extends hℓ
    match Obs.«KernelCheck::is_large_eliminator».obs largeRun with
    | .n1 (ev15 := e15) .. =>
      obtain ⟨hr1, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step e15 resLvl rfl ℓ hℓ'
      have hnz : ℓ.isNeverZero = true := by
        cases hz : ℓ.isNeverZero
        · rw [hz] at hr1
          exact absurd (Value.field.inj hr1) one_ne_zero
        · rfl
      exact Or.inl fun φ => by
        rw [hsℓ φ]
        exact Ix.Kernel.Level.isNeverZero_sound φ ℓ hnz
    | .other_n0 (he49 := he) .. => exact absurd (Value.field.inj he) one_ne_zero
    | .other_other_n0 (hv69 := hv) .. =>
      exact Or.inr (by have := field_nat_eq_zero hnc hv; omega)
    | .other_other_n1_n0 (hv77 := hv) .. =>
      exact Or.inr (by have := field_nat_eq_one hnc hv; omega)
    | .other_other_n1_other_Ctor_n0 (hv77 := hv) .. =>
      exact Or.inr (by have := field_nat_eq_one hnc hv; omega)
    | .other_other_n1_other_Ctor_other (hv77 := hv) .. =>
      exact Or.inr (by have := field_nat_eq_one hnc hv; omega)
    | .other_other_n1_other_other (hv77 := hv) .. =>
      exact Or.inr (by have := field_nat_eq_one hnc hv; omega)
    | .other_other_other (he272 := he) .. => exact absurd (Value.field.inj he) one_ne_zero

/-! ## The restriction at the family -/

/-- **The result-sort walk at a family's stored former answers the family's sort**, at the
step's context: on the stored former's type with its level parameters at positions, over
the family's parameters and indices, the walk answers the family's result sort at positions.
The canonical comparison, the K verdict and the large eliminator's field walk read the
family's sort through this walk only. -/
def FormerSortReads (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (lim : Option Nat)
    (env : Ix.Kernel.Env .anon) (fam : NativeFam .anon) : Prop :=
  Decl.ResultSortReads (Core.Ctx.stored ⟨E, env, t, lim⟩) (fam.p.nP + fam.p.nIdx)
    (Core.posOf fam.cvS.levelParams fam.cvS.type)
    (Ix.Kernel.Level.subst fam.cvS.levelParams (Core.posLevels fam.cvS.levelParams)
      fam.p.resSort)

/-- **The elimination restriction of the late relation** at the family read off the tied
parent: if the record has one level more than the parent's member (a large eliminator), the
family's result sort is never zero or the family has fewer than two constructors. -/
theorem rec_elim_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    {fam : NativeFam .anon} (hfam : NativeFamStored env fam)
    (hsr : FormerSortReads t E lim env fam) (hname : fam.p.cvT.name = keyOf t P)
    (hnP : fam.p.nP = ind.params.toNat) (hnI : fam.p.nIdx = ind.indices.toNat)
    (hctors : fam.ctorsA.length = ind.ctors.size) :
    decide (rc.lvls.toNat = ind.lvls.toNat + 1) = true →
      (∀ φ : Ix.Kernel.LevelParam → Nat, Ix.Kernel.Level.eval φ fam.p.resSort ≠ 0) ∨
        fam.ctorsA.length < 2 := by
  intro hlarge
  have hlarge' : rc.lvls.toNat = ind.lvls.toNat + 1 := of_decide_eq_true hlarge
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, kTarget, result,
    pointer, bA, bR, bT, bP, blobs, tree, scanHeap, loadedHeap, kHeap, kAfter, canonHeap, final,
    loadCalls, kCalls, canonCalls, hrc, hbA, hbA', hbR, hbR', hbT, hbT', hbP, hbP', hblob, rty,
    hrulesTr, hrules_lt, hidx56, hlvR, hlvP, hpP, hiP, hcP, eSL, evLoad, hsLoad, hldP, eK, evK,
    hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    rec_arm_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  -- the former the parent's key stores
  have hformer : env.find? (Core.keyOf t P) = some (.indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p)) := by
    rw [LoadedReads.keyOf_eq, ← hname]
    exact hfam.former
  have hκP : cS.κ P = Core.keyOf t P := Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hformer
  have hgL : Core.Good ⟨E, env, t, lim⟩ loadCalls := (hst.good env lim).sub hsLoad
  obtain ⟨ci, hfind, hptr⟩ := Core.get_ci_step cS hcS evLoad parentV bT rfl trivial
    (by rw [hbT', hκP]; exact Core.Resolved.ne)
    (Core.CoreGood.ofRaw hgL (fun _ _ => trivial)) hbT
  rw [hbT', hκP] at hfind
  have hci : ci = .indInfo fam.cvS (Ix.Kernel.nativeCaps fam.p) :=
    Option.some.inj (hfind.symm.trans hformer)
  subst hci
  obtain ⟨v, hv, hrep⟩ := hptr
  rw [hldP] at hv
  injection hv with hv
  subst hv
  obtain ⟨cv, caps, hcv, hval⟩ := ciRep_induct_fields hrep
  obtain ⟨hcvEq, -⟩ := Ix.Kernel.ConstantInfo.indInfo.inj hcv
  subst hcvEq
  obtain ⟨-, -, hperm, htm⟩ := hval
  -- the canonical comparison
  have hgC : Core.Good ⟨E, env, t, lim⟩ canonCalls := (hst.good env lim).sub hsCanon
  unfold FormerSortReads at hsr
  rw [hnP, hnI] at hsr
  rcases canonical_full_elim hcS (fun _ => trivial) (hrc.mono eC) hgC
    (htm.mono eC) (by omega) hsr evCanon hlarge' with h | h
  · exact Or.inl (eval_ne_zero_of_posOf hperm h)
  · exact Or.inr (by omega)

end IxVM.Refinement.Typing
