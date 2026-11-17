import IxVMRefinement.Assembly.TypingRecLatePins
import IxVMRefinement.Iota.RedIota

/-! # The recursor record's rules against its parent's constructors

The late relation pins rule `j` of the record at constructor `j` of the family, with that
constructor's field count. The circuit checks it in `nat_check_rules`: rule `j`'s constructor
index is `j`, and its field count is the field count of the constructor `get_ci_cprj(block, idx,
j)` loads, `block` and `idx` the parent's. Under the prefix keying that load is the constructor
the environment stores at the key of constructor projection `j` of the parent's member, which is
the family's constructor `j` (the registry's tie). This module reads the field counts off the
check:

* `RecCanonAt`, `rec_canon_of_arm`: the derivation behind `rec_counts_of_arm`, kept: at the tied
  parent, the member check's K verdict and canonical comparison, with the record's and the
  parent's loaded values read off their records (the record's rule list, the parent's block
  address and member index);
* `canonical_full_nat_rec`, `nat_rec_check_rules_run`: the canonical comparison at an inductive
  parent runs `nat_rec_check`, which runs `nat_check_rules` on the record's rule list from
  position `0`, with the parent's block and member index, at a heap after its own;
* `nat_check_rules_fields`: by induction on the converted rule list, rule `k`'s field count is
  the field count of the constructor stored at the key of constructor projection `j + k`;
* `rec_rule_fields_of_arm`: the record's rule `j` has the field count of the family's constructor
  `j`.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-! ## Heaps -/

/-- A heap with one cell pushed extends the heap. -/
theorem ext_of_eq_snoc {h h' : Heap F} {v : SourceValue F} (e : h' = h ++ [v]) :
    Heap.Extends h h' := by
  rw [e]
  exact Heap.Extends.snoc h v

/-! ## The member check's comparisons at the tied parent -/

/-- **The member check's K verdict and canonical comparison at the tied parent `P`, with the
records read**: the role context (represented at the parent's load), the record's address, its
loaded value read off the record (its type converted, its rule list converted with the plans of
the right-hand sides, its own address as block address), the parent's address `P`, the parent's
loaded value read off member `ind` of its block (block address `ip.block`, member index
`ip.idx`), the record's rule count below `2^33`; the K run and the canonical comparison, each at a
heap after the parent's load, within the calls. -/
def RecCanonAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (bAddr : _root_.Address) (n : Nat) (A : _root_.Address) (c : Ixon.Constant)
    (rc : Ixon.Recursor) (P : _root_.Address) (ip : Ixon.InductiveProj)
    (ind : Ixon.Inductive) : Prop :=
  ∃ (rcv apv parentV tyPtr rulesPtr blkPtr tyPtrP unsP blkPtrP kTarget result : SourceValue F)
    (bA bR bT bP : Bytes.Address) (blobs : List (_root_.Address × ByteArray))
    (tree : L1.BinderTreeData) (loadedHeap kHeap kAfter canonHeap final : Heap F)
    (kCalls canonCalls : List (Call F)),
    Claim.RCFullRep t bAddr n loadedHeap rcv ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bA apv ∧ Core.ixAddr bA = A ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bR blkPtr ∧ Core.ixAddr bR = A ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bT parentV ∧ Core.ixAddr bT = P ∧
    Bytes.RepAddressRef Core.addrTy loadedHeap bP blkPtrP ∧ Core.ixAddr bP = ip.block ∧
    (∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs) ∧
    L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs loadedHeap 4294967295
      rc.typ tyPtr ∧
    L1.RulesTraceRep c.refs.toList [A] c.univs.toList c.sharing.toList blobs tree loadedHeap 0
      (0 + 1) rc.rules.toList rulesPtr ∧
    rc.rules.size < 8589934592 ∧ ip.idx.toNat < 72057594037927936 ∧
    Heap.Extends loadedHeap kHeap ∧
    ObsFn Obs.W "KernelCheck::compute_k_target"
      [rcv, .construct "KernelTypes::KConstantInfo" "Induct"
        [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
          .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
          .field (ip.idx.toNat : F)], parentV] kHeap kTarget kAfter kCalls ∧
    (∀ cl ∈ kCalls, cl ∈ calls) ∧ L1.repBoolField rc.k = kTarget ∧
    Heap.Extends loadedHeap canonHeap ∧
    ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rcv, .construct "KernelTypes::KConstantInfo" "Rec"
        [.field (rc.lvls.toNat : F), tyPtr, .field (rc.params.toNat : F),
          .field (rc.indices.toNat : F), .field (rc.motives.toNat : F),
          .field (rc.minors.toNat : F), rulesPtr, L1.repBoolField rc.k,
          L1.repBoolField rc.isUnsafe, blkPtr, .field ((0 : Nat) : F)], apv,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [.field (ind.lvls.toNat : F), tyPtrP, .field (ind.params.toNat : F),
            .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsP, blkPtrP,
            .field (ip.idx.toNat : F)], parentV]
      canonHeap result final canonCalls ∧
    (∀ cl ∈ canonCalls, cl ∈ calls)

/-- **The member check's comparisons at the tied parent** (the derivation of
`rec_counts_of_arm`, kept). -/
theorem rec_canon_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    RecCanonAt calls t E₀ bAddr n A c rc P ip ind := by
  subst hlim
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, hrcM, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := hnat
  -- the record has few rules
  obtain ⟨rawB, cB, hszB, hhB, hbaB, hexB⟩ := get_ci_bytes_bound ha_pre ev_ld
  have hcB : cB = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hhB) hbaB hexB
  subst cB
  have hrules_lt := recr_rules_size_lt hszB hexB hinfo
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  -- the load of the record, traced
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
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
  -- the type reads, well scoped, represented under the prefix keying
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk
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
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := some n) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  -- the member check: route, K verdict, canonical comparison
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, evScan, hsScan, evLoad, hsLoad, hldP, evRoute, hsRoute,
    hnp, hni, eLen, evLen, hsLen, hlenEq, eK, evK, hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    native_rec_member_full evM
  have hsScan' : ∀ x ∈ scanCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsScan x hx))
  have hsLoad' : ∀ x ∈ loadCalls, x ∈ calls := fun x hx => hsub_chk x (hsubM x (hsLoad x hx))
  -- the route's parent is the tied one
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
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
  -- the parent's load, traced: the member `ind` of the block `cb`
  have hgL : Core.Good ⟨E, env, t, some n⟩ loadCalls := hgood.sub hsLoad'
  obtain ⟨rawP, cP, hhP, hbaP, hexP, -, hresP⟩ := L1.get_ci_block_trace_spec hgL.2 ha evLoad
  have hrecP : recordOf E (Core.ixAddr a) = some cm := by
    rw [recordOf_eq_recordAt_of_decoded hst.decoded]
    exact hcm
  obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrecP
  have hbP : rawP = lc.rawBytes := Core.load_escape hget hgL.1 rawP hhP hbaP
  have hcP : cP = cm := by
    rw [hbP, hdec] at hexP
    exact (Except.ok.inj hexP).symm
  subst hcP
  unfold L1.GetCIBlockTraceResult at hresP
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
  rw [hld₀] at hldP
  injection hldP with hvP'
  injection hvP' with _ _ hpf
  simp only [List.cons.injEq, and_true] at hpf
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpf
  -- the heaps
  have extL : Heap.Extends m_chk loadedHeap :=
    hextM.trans (evScan.heap_extends.trans evLoad.heap_extends)
  have extA : Heap.Extends h_pre loadedHeap := ev_ld.heap_extends.trans extL
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, a', bR, a, bP, blobs, tree,
    loadedHeap, kHeap, kAfter, canonHeap, h'_chk, kCalls, canonCalls,
    hrcM.mono extL,
    Bytes.repAddressRef_heapMono₂ Core.addrTy extA ha'_ref, rfl,
    Bytes.repAddressRef_heapMono₂ Core.addrTy extL hblkR, hbR,
    Bytes.repAddressRef_heapMono₂ Core.addrTy evLoad.heap_extends ha, rfl,
    hblkP, hbPa, hblob, rty.mono extL (fun q hq => hq), hrulesTr.mono extL (fun q hq => hq),
    hrules_lt, hidxP, eK, evK, fun x hx => hsub_chk x (hsubM x (hsK x hx)), hkEq, eC, evCanon,
    fun x hx => hsub_chk x (hsubM x (hsCanon x hx))⟩

/-! ## The canonical comparison runs `nat_rec_check`, which runs `nat_check_rules` -/

/-- **The canonical comparison at an inductive parent runs `nat_rec_check`**, at a heap after
its own, within its calls. -/
theorem canonical_full_nat_rec
    {rc levels type parameters indices motives minors rules k unsafeFlag block position address
      parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock
      parentIndex parent result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_canonical_full"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
            parentBlock, parentIndex], parent]
      heap result final calls) :
    ∃ (univOffset : SourceValue F) (natHeap : Heap F) (natCalls : List (Call F)),
      Heap.Extends heap natHeap ∧
      ObsFn Obs.W "KernelCheck::nat_rec_check"
        [rc, .construct "KernelTypes::KConstantInfo" "Rec"
          [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
            position], address,
          .construct "KernelTypes::KConstantInfo" "Induct"
            [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
              parentBlock, parentIndex], parent, univOffset]
        natHeap result final natCalls ∧
      (∀ cl ∈ natCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_canonical_full».obs observed with
  | .other (hne568 := hne) .. =>
    exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct (m272 := m272) (m329 := m329) (m281 := m281) (m389 := m389) (m342 := m342)
      (m417 := m417) (v341 := univOffset) (cs516 := natCalls)
      (sg279 := seg) (hm337 := hm337) (ev293 := sortRun) (ev399 := soloRun) (ev354 := largeRun)
      (ev429 := majorRun) (ev518 := natRun) (hc567 := children) .. =>
    have e1 : Heap.Extends heap m272 := by
      match seg with
      | .n1 (ev159 := e) (he201 := hh) .. =>
        rw [hh]
        exact e.heap_extends
      | .other (hm245 := e1) (hm259 := e2) (he269 := e3) .. =>
        rw [e3, e1, e2]
        exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have ext : Heap.Extends heap m417 :=
      e1.trans <| (ext_of_eq_snoc hm337).trans <| sortRun.heap_extends.trans <|
        soloRun.heap_extends.trans <| largeRun.heap_extends.trans majorRun.heap_extends
    refine ⟨univOffset, m417, natCalls, ext, natRun, ?_⟩
    intro call member
    rw [children]
    simp [member]

/-- **`nat_rec_check` runs `nat_check_rules`** on the record's rule list from position `0`, with
the parent's block and member index and the parent's address, at a heap after its own, within
its calls. -/
theorem nat_rec_check_rules_run
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
    ∃ (lps pw tty motiveTy recC rlvls : SourceValue F) (rulesHeap : Heap F)
      (rulesCalls : List (Call F)),
      Heap.Extends heap rulesHeap ∧
      ObsFn Obs.W "KernelCheck::nat_check_rules"
        [rules, parentBlock, parentIndex, parent, lps, parameters, indices, pw, constructors,
          univOffset, tty, motiveTy, recC, rlvls, .field 0] rulesHeap result final rulesCalls ∧
      (∀ cl ∈ rulesCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::nat_rec_check».obs observed with
  | .run (m219 := m219) (m299 := m299) (m308 := m308) (m324 := m324) (m382 := m382)
      (m1455 := m1455) (hv11 := recShape) (hv81 := parentShape) (ev231 := ev231) (sg306 := sg306)
      (hm318 := hm318) (hm332 := hm332) (sg389 := sg389) (hm447 := hm447) (ev403 := ev403)
      (ev464 := ev464) (hm492 := hm492) (ev560 := ev560) (ev588 := ev588) (ev546 := ev546)
      (ev525 := ev525) (hm653 := hm653) (hm676 := hm676) (ev617 := ev617) (ev749 := ev749)
      (ev794 := ev794) (ev735 := ev735) (ev714 := ev714) (hm835 := hm835) (ev889 := ev889)
      (hm914 := hm914) (ev875 := ev875) (ev823 := ev823) (ev969 := ev969) (hm1010 := hm1010)
      (ev938 := ev938) (ev1057 := ev1057) (hm1201 := hm1201) (ev1165 := ev1165)
      (ev1259 := ev1259) (hm1325 := hm1325) (ev1296 := ev1296) (ev1465 := ev1465)
      (ev1347 := ev1347) (hc1487 := children) .. =>
    injection recShape with _ _ recFields
    simp only [List.cons.injEq, and_true] at recFields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := recFields
    injection parentShape with _ _ parentFields
    simp only [List.cons.injEq, and_true] at parentFields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := parentFields
    have s1 : Heap.Extends m219 m299 := by
      match sg306 with
      | .n1 (hm272 := e) .. => exact ext_of_eq_snoc e
      | .other (hm292 := e) .. => exact ext_of_eq_snoc e
    have s2 : Heap.Extends m308 m382 := by
      match sg389 with
      | .n0 (he352 := e) .. => exact ⟨[], by rw [e, List.append_nil]⟩
      | .other (ev363 := e) .. => exact e.heap_extends
    have ext : Heap.Extends heap m1455 :=
      ev231.heap_extends.trans <| s1.trans <| (ext_of_eq_snoc hm332).trans <|
        (ext_of_eq_snoc hm318).trans <| s2.trans <| (ext_of_eq_snoc hm447).trans <|
        ev403.heap_extends.trans <| ev464.heap_extends.trans <| (ext_of_eq_snoc hm492).trans <|
        ev560.heap_extends.trans <| ev588.heap_extends.trans <| ev546.heap_extends.trans <|
        ev525.heap_extends.trans <| (ext_of_eq_snoc hm676).trans <|
        (ext_of_eq_snoc hm653).trans <| ev617.heap_extends.trans <|
        ev749.heap_extends.trans <| ev794.heap_extends.trans <| ev735.heap_extends.trans <|
        ev714.heap_extends.trans <| (ext_of_eq_snoc hm835).trans <|
        ev889.heap_extends.trans <| (ext_of_eq_snoc hm914).trans <|
        ev875.heap_extends.trans <| ev823.heap_extends.trans <| ev969.heap_extends.trans <|
        (ext_of_eq_snoc hm1010).trans <| ev938.heap_extends.trans <|
        ev1057.heap_extends.trans <| (ext_of_eq_snoc hm1201).trans <|
        ev1165.heap_extends.trans <| ev1259.heap_extends.trans <|
        (ext_of_eq_snoc hm1325).trans <| ev1296.heap_extends.trans ev1465.heap_extends
    refine ⟨_, _, _, _, _, _, _, _, ext, ev1347, ?_⟩
    intro call member
    rw [children]
    simp [member]

/-! ## The rules' field counts -/

/-- A converted rule cell loaded as a rule cell: its field count and its tail. -/
theorem ruleCell_load {h : Heap F} {addr : Nat} {a₁ a₂ a₃ rest x₁ x₂ x₃ xr : SourceValue F}
    (cell : h[addr]? = some (.construct Core.krrListEnum "Cons"
      [.construct Core.krrEnum "Mk" [a₁, a₂, a₃], rest]))
    (ld : loadValue h (.ptr (.enum Core.krrListEnum) addr) =
      .ok (.construct Obs.Names.«Lists::Node<KernelTypes::KRecRule>» "Cons"
        [.construct "KernelTypes::KRecRule" "Mk" [x₁, x₂, x₃], xr])) :
    a₂ = x₂ ∧ rest = xr := by
  have ld' : loadValue h (.ptr (.enum Core.krrListEnum) addr) =
      .ok (.construct Core.krrListEnum "Cons"
        [.construct Core.krrEnum "Mk" [x₁, x₂, x₃], xr]) := ld
  obtain ⟨-, hxs⟩ := load_cell cell ld'
  simp only [List.cons.injEq, and_true] at hxs
  obtain ⟨hmk, hrest⟩ := hxs
  injection hmk with _ _ hargs
  simp only [List.cons.injEq, and_true] at hargs
  exact ⟨hargs.2.1, hrest⟩

/-- A converted rule cell is no empty list. -/
theorem ruleCell_not_nil {h : Heap F} {addr : Nat} {xs : List (SourceValue F)}
    (cell : h[addr]? = some (.construct Core.krrListEnum "Cons" xs))
    (ld : loadValue h (.ptr (.enum Core.krrListEnum) addr) =
      .ok (.construct Obs.Names.«Lists::Node<KernelTypes::KRecRule>» "Nil" [])) : False := by
  have ld' : loadValue h (.ptr (.enum Core.krrListEnum) addr) =
      .ok (.construct Core.krrListEnum "Nil" []) := ld
  exact load_cell_ne cell ld' (by decide)

/-- **`nat_check_rules`, rule by rule**: on a converted rule list from position `j`, under a
scoped context that allows every call, rule `k`'s field count is the field count of any
constructor the environment stores at the key of constructor projection `j + k` of the block
and member index the check loads from. -/
theorem nat_check_rules_fields {c : Core.ScopedCtx} (hc : Core.ScopedCoreFacts c)
    (hall : ∀ cl, c.allowed cl)
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    {b : Bytes.Address} {bp : SourceValue F} {i : F}
    {x_t x_lps x_np x_ni x_pw x_n x_uo x_tty x_mty x_rec x_rlvls : SourceValue F} :
    ∀ (rus : List Ixon.RecursorRule) {j : Nat} {root : F} {p r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p →
      j + rus.length < 18446744069414584321 →
      ObsFn Obs.W "KernelCheck::nat_check_rules"
        [p, bp, .field i, x_t, x_lps, x_np, x_ni, x_pw, x_n, x_uo, x_tty, x_mty, x_rec, x_rlvls,
          .field (j : F)] h r h' cs →
      Core.Good c.toCtx cs → Bytes.RepAddressRef Core.addrTy h b bp →
      ∀ (k : Nat) (ru : Ixon.RecursorRule) (cv : ConstantVal .anon) (nP nF : Nat),
        rus[k]? = some ru →
        c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (j + k))) =
          some (.ctorInfo cv nP nF) →
        ru.fields.toNat = nF := by
  intro rus
  induction rus with
  | nil =>
    intro j root p r h h' cs _ _ _ _ _ k ru cv nP nF hk _
    simp at hk
  | cons ru₀ rus ih =>
    intro j root p r h h' cs htr hlen ev hgood hb k ru cv nP nF hk hfind
    cases htr with
    | cons cell hf raw planned levels rs =>
      match Obs.«KernelCheck::nat_check_rules».obs ev with
      | .Nil (ld12 := ld) .. => exact (ruleCell_not_nil cell ld).elim
      | .Cons (m98 := mC) (m230 := mR) (cs111 := csC) (cs384 := csRec) (v401 := vNext)
          (ld12 := ld) (ev113 := evC) (ld107 := ldC) (heq215 := hnfEq) (ev254 := evRhs)
          (ev240 := evWrap) (op513 := hjNext) (ev386 := evRec) (hc515 := hcalls) .. =>
        obtain ⟨hrnf, hrest⟩ := ruleCell_load cell ld
        have hjlt : j < 18446744069414584321 := by
          simp only [List.length_cons] at hlen
          omega
        cases k with
        | zero =>
          have hru : ru = ru₀ := by simpa using hk.symm
          subst hru
          have hval : ZMod.val (j : F) = j :=
            ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
          have hfind0 : c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) =
              some (.ctorInfo cv nP nF) := by
            simpa only [Nat.add_zero] using hfind
          have hfind' : c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i)
              (ZMod.val (j : F)))) = some (.ctorInfo cv nP nF) := by
            rw [hval]
            exact hfind0
          have hsubC : ∀ x ∈ csC, x ∈ cs := fun x hx => by rw [hcalls]; simp [hx]
          obtain ⟨-, hctor⟩ := Core.get_ci_cprj_step c hc evC bp i (j : F) b rfl (hall _)
            (Or.inr ⟨j, cv, nP, nF, hfind0⟩)
            (Core.CoreGood.ofRaw (hgood.sub hsubC) (fun cl _ => hall cl)) hb
          obtain ⟨v, hv, hrep⟩ := hctor cv nP nF hfind'
          rw [ldC] at hv
          injection hv with hv
          subst hv
          obtain ⟨cv', nP', nF', hci, -, -, hnf', ⟨-, hnF⟩, -⟩ := Core.CIRep.ctor_fields hrep
          obtain ⟨-, -, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj hci
          exact field_nat_inj (by omega) (by omega) (hrnf.trans (hnfEq.trans hnf'))
        | succ k =>
          have hk' : rus[k]? = some ru := by simpa using hk
          have hjv : vNext = .field (((j + 1 : Nat)) : F) := by
            simp only [evalBinOp] at hjNext
            injection hjNext with hv
            rw [← hv]
            simp [Nat.cast_add]
          subst hrest
          rw [hjv] at evRec
          have ext : Heap.Extends h mR :=
            evC.heap_extends.trans (evRhs.heap_extends.trans evWrap.heap_extends)
          have hsubR : ∀ x ∈ csRec, x ∈ cs := fun x hx => by rw [hcalls]; simp [hx]
          have hlen' : j + 1 + rus.length < 18446744069414584321 := by
            simp only [List.length_cons] at hlen
            omega
          have hfind'' : c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i)
              (j + 1 + k))) = some (.ctorInfo cv nP nF) := by
            rw [show j + 1 + k = j + (k + 1) by omega]
            exact hfind
          exact @ih (j + 1) (root + 1) _ _ _ _ _ (rs.mono ext (fun q hq => hq)) hlen' evRec
            (hgood.sub hsubR) (Bytes.repAddressRef_heapMono₂ Core.addrTy ext hb) k ru cv nP nF
            hk' hfind''

/-- **The record's rule `j` has the field count of the family's constructor `j`**, at a step's
environment, for the tied parent read off member `ind` of its block, where the family is stored
and its constructor `j` has the key of constructor projection `j` of the parent's member. -/
theorem rec_rule_fields_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    {fam : NativeFam .anon} (hfam : NativeFamStored env fam)
    (hnames : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
      cA.1.name = keyOf t (Core.cprjAddr ip.block ip.idx.toNat j)) :
    ∀ (j : Nat) (ru : Ixon.RecursorRule) (cA : ConstantVal .anon × Nat),
      rc.rules.toList[j]? = some ru → fam.ctorsA[j]? = some cA → ru.fields.toNat = cA.2 := by
  obtain ⟨rcv, apv, parentV, tyPtr, rulesPtr, blkPtr, tyPtrP, unsP, blkPtrP, kTarget, result,
    bA, bR, bT, bP, blobs, tree, loadedHeap, kHeap, kAfter, canonHeap, final, kCalls,
    canonCalls, hrc, hbA, hbA', hbR, hbR', hbT, hbT', hbP, hbP', hblob, rty, hrulesTr, hrules_lt,
    hidx56, eK, evK, hsK, hkEq, eC, evCanon, hsCanon⟩ :=
    rec_canon_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  subst hlim
  obtain ⟨univ, natHeap, natCalls, eN, evNat, hsNat⟩ := canonical_full_nat_rec evCanon
  obtain ⟨lps, pw, tty, mty, recC, rlvls, rulesHeap, rulesCalls, eR, evRules, hsRules⟩ :=
    nat_rec_check_rules_run evNat
  have ext : Heap.Extends loadedHeap rulesHeap := eC.trans (eN.trans eR)
  let cS : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
  have hcS : Core.ScopedCoreFacts cS := hstep.inv.scopedCoreFacts
  have hgood : Core.Good ⟨E, env, t, some n⟩ rulesCalls :=
    (hst.good env (some n)).sub (fun x hx => hsCanon x (hsNat x (hsRules x hx)))
  have hidx : ZMod.val ((ip.idx.toNat : Nat) : F) = ip.idx.toNat :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have evRules' : ObsFn Obs.W "KernelCheck::nat_check_rules"
      [rulesPtr, blkPtrP, .field ((ip.idx.toNat : Nat) : F), parentV, lps,
        .field (rc.params.toNat : F), .field (rc.indices.toNat : F), pw,
        .field (ind.ctors.size : F), univ, tty, mty, recC, rlvls, .field ((0 : Nat) : F)]
      rulesHeap result final rulesCalls := by
    rw [Nat.cast_zero]
    exact evRules
  intro j ru cA hru hcA
  have hfindN := (hfam.ctor j cA hcA).1
  rw [hnames j cA hcA, ← LoadedReads.keyOf_eq] at hfindN
  have hκ : cS.κ (Core.cprjAddr ip.block ip.idx.toNat j) =
      Core.keyOf t (Core.cprjAddr ip.block ip.idx.toNat j) :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hfindN
  have hfind : cS.env.find? (cS.κ (Core.cprjAddr (Core.ixAddr bP)
      (ZMod.val ((ip.idx.toNat : Nat) : F)) (0 + j))) =
      some (.ctorInfo cA.1 fam.p.nP cA.2) := by
    rw [hbP', hidx, Nat.zero_add, hκ]
    exact hfindN
  have hlen : 0 + rc.rules.toList.length < 18446744069414584321 := by
    rw [Array.length_toList]
    omega
  exact nat_check_rules_fields hcS (fun _ => trivial) rc.rules.toList
    (hrulesTr.mono ext (fun q hq => hq)) hlen evRules' hgood
    (Bytes.repAddressRef_heapMono₂ Core.addrTy ext hbP) j ru cA.1 fam.p.nP cA.2 hru hfind

/-! ## The pins -/

/-- **The rules as read**, position by position: rule `j` of a reading from index `k` names
constructor projection `k + j` of member `i` of the block at `B`, with the record's field
count. -/
theorem ruleReads_at {t : Ix.Kernel.RoleTable} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {B : _root_.Address} {i : Nat} :
    ∀ (rus : List Ixon.RecursorRule) (k : Nat) (rules : List (Ix.Kernel.RecRule .anon)),
      List.Forall₂ (RuleReads t mr B i) (rus.zipIdx k) rules →
      rules.length = rus.length ∧
      ∀ (j : Nat) (r : Ix.Kernel.RecRule .anon), rules[j]? = some r →
        ∃ ru, rus[j]? = some ru ∧ r.ctor = keyOf t (ctorAddr B i (k + j)) ∧
          r.nfields = ru.fields.toNat
  | [], k, rules, h => by
    have h' : List.Forall₂ (RuleReads t mr B i) [] rules := h
    cases h'
    exact ⟨rfl, fun j r hr => by simp at hr⟩
  | ru :: rus, k, rules, h => by
    rw [List.zipIdx_cons] at h
    cases h with
    | cons hhd htl =>
      obtain ⟨hlen, hrest⟩ := ruleReads_at rus (k + 1) _ htl
      obtain ⟨rhs, -, rfl⟩ := hhd
      refine ⟨by simp [hlen], ?_⟩
      intro j r hr
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
        subst hr
        exact ⟨ru, by simp, by simp, rfl⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hr
        obtain ⟨ru', hru', hc, hn⟩ := hrest j r hr
        refine ⟨ru', by simpa using hru', ?_, hn⟩
        rw [hc, show k + 1 + j = k + (j + 1) by omega]

/-- **The rules as read are pinned at the family's constructors**: one per constructor, rule `j`
at constructor `j` with its field count, where the reading names the constructor projections of
the parent's member, the family's constructor `j` has the key of projection `j`, and the
record's rule `j` has constructor `j`'s field count. -/
theorem ruleReads_pins {t : Ix.Kernel.RoleTable} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {B : _root_.Address} {i : Nat} {fam : NativeFam .anon} {rus : List Ixon.RecursorRule}
    {rules : List (Ix.Kernel.RecRule .anon)}
    (hr : List.Forall₂ (RuleReads t mr B i) rus.zipIdx rules)
    (hlen : rus.length = fam.ctorsA.length)
    (hnames : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
      cA.1.name = keyOf t (Core.cprjAddr B i j))
    (hfields : ∀ (j : Nat) (ru : Ixon.RecursorRule) (cA : ConstantVal .anon × Nat),
      rus[j]? = some ru → fam.ctorsA[j]? = some cA → ru.fields.toNat = cA.2) :
    rules.length = fam.ctorsA.length ∧
      ∀ (j : Nat) (r : Ix.Kernel.RecRule .anon) (cA : ConstantVal .anon × Nat),
        rules[j]? = some r → fam.ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2 := by
  obtain ⟨hl, hat⟩ := ruleReads_at rus 0 rules hr
  refine ⟨hl.trans hlen, fun j r cA hr hcA => ?_⟩
  obtain ⟨ru, hru, hc, hn⟩ := hat j r hr
  refine ⟨?_, hn.trans (hfields j ru cA hru hcA)⟩
  rw [hc, hnames j cA hcA, Nat.zero_add, LoadedReads.ctorAddr_eq_cprjAddr]

/-- **The pins of the late relation** from the record's counts against the parent's member and
the rules as read: the major index and rule prefix the record declares are the family's, and the
rules are one per constructor at its field count. -/
theorem late_pins_of {fam : NativeFam .anon} {cvR : ConstantVal .anon}
    {elim : Ix.Kernel.LevelParam} {large : Bool} {rc : Ixon.Recursor} {ind : Ixon.Inductive}
    {rules : List (Ix.Kernel.RecRule .anon)}
    (hlenA : fam.ctorsA.length = fam.p.ctors.length)
    (hnP : fam.p.nP = ind.params.toNat) (hnI : fam.p.nIdx = ind.indices.toNat)
    (hctors : fam.ctorsA.length = ind.ctors.size)
    (hp : rc.params.toNat = ind.params.toNat) (hi : rc.indices.toNat = ind.indices.toNat)
    (hm : rc.motives.toNat = 1) (hmi : rc.minors.toNat = ind.ctors.size)
    (hlen : rules.length = fam.ctorsA.length)
    (hrule : ∀ (j : Nat) (r : Ix.Kernel.RecRule .anon) (cA : ConstantVal .anon × Nat),
      rules[j]? = some r → fam.ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2) :
    rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat =
        (fam.recParts cvR elim large (rules.map (·.rhs))).majorIdx ∧
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat =
        (fam.recParts cvR elim large (rules.map (·.rhs))).rulePrefix ∧
      rules.length = fam.ctorsA.length ∧
      ∀ (j : Nat) (r : Ix.Kernel.RecRule .anon) (cA : ConstantVal .anon × Nat),
        rules[j]? = some r → fam.ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2 := by
  have hrP : (fam.recParts cvR elim large (rules.map (·.rhs))).rulePrefix =
      fam.p.nP + 1 + fam.p.ctors.length := rfl
  have hmI : (fam.recParts cvR elim large (rules.map (·.rhs))).majorIdx =
      fam.p.nP + 1 + fam.p.ctors.length + fam.p.nIdx := rfl
  refine ⟨?_, ?_, hlen, hrule⟩
  · rw [hmI]
    omega
  · rw [hrP]
    omega

end IxVM.Refinement.Typing
