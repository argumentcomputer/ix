import IxVMRefinement.Assembly.TypingRecParent
import IxVMRefinement.Assembly.RecursorSyntax
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.StatementRel.LoadedReadsCanonRec
import IxVMRefinement.Claim.FamilyRefusedStandalone

/-! # The parent family read at a recursor record, from the check of the record

`recParent_of_route` reads the parent family off the three runs of the native recursor route of
`check_recursor_member`, given the record's type represented under the prefix keying. This
module supplies those inputs from the walk's check of the record:

* `check_const_rec_route`: the `Rec` arm of `check_const` validates the type's scope at a heap
  after the check's own, and, the block of the family being native (a recursor of a modeled
  block is refused), runs `check_recursor_member` on the same value at a later heap;
* `native_rec_route_calls`: the three runs of the member check's route, each within the member
  check's calls;
* `NativeRecArm`: the walk loaded the recursor record and checked the loaded `Rec` value;
* `RecArmRun`: the same at any limit, the role context read as the core reads it;
* `RecMajorNotBasis`: the head key of the major premise's domain, in every annotation of the
  record's type as read, is no basis name (the record-scoped form of the basis hypothesis);
* `majorKey_of_piDomAt`: the head of the major premise's domain is the record's major key;
* `recParent_of_arm`: at every environment the skeleton hands the step, the parent the circuit
  read is a stored former whose record is an inductive projection of a native block. The type
  is the loaded one (traced conversion of the record, `RecrTraceRep`); its reading is well scoped
  by the arm's `validate_expr_well_scoped` run; it is represented under the table's keying
  (`RawConvExpr.toTmC`) and, its references being stored, under the prefix keying.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

/-! ## The `Rec` arm of `check_const` -/

/-- **The `Rec` arm of `check_const`**: the type's scope is validated at a heap after the
check's, and `check_recursor_member` runs on the same value at a later heap, its calls among the
check's. The other kinds' arms do not match a `Rec` value; the modeled route runs
`KernelModeled::check_family` at the value's block field, which `hfr` refuses (at a standalone
recursor record, `Claim.familyCheckRefused_of_recr`). -/
theorem check_const_rec_route
    {rc levels type parameters indices motives minors rules k unsafeFlag block position addr
      result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], addr] h result h' calls)
    (hfr : Claim.FamilyCheckRefused rc block h calls) :
    ∃ (scopeBefore scopeAfter memberHeap : Heap F) (scopeResult : SourceValue F)
      (scopeCalls memberCalls : List (Call F)),
      Heap.Extends h scopeBefore ∧
      ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [type, .field 0, levels]
        scopeBefore scopeResult scopeAfter scopeCalls ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [type, .field 0, levels], scopeBefore⟩ :
        Call F) ∈ calls ∧
      Heap.Extends h memberHeap ∧
      ObsFn Obs.W "KernelCheck::check_recursor_member"
        [rc, .construct "KernelTypes::KConstantInfo" "Rec"
          [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
            position], addr] memberHeap result h' memberCalls ∧
      (∀ cl ∈ memberCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_const».obs observed with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) ..
  | .Induct_n0 (hv1240 := shape) ..
  | .Induct_other_n0 (hv1240 := shape) ..
  | .Induct_other_other (hv1240 := shape) ..
  | .Ctor_n0_n0 (hv1989 := shape) ..
  | .Ctor_n0_other (hv1989 := shape) ..
  | .Ctor_other_n0 (hv1989 := shape) ..
  | .Ctor_other_other (hv1989 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Rec_other (m2789 := m2789) (m2857 := m2857) (ev14 := ev14) (hv2727 := shape)
      (ev2801 := ev2801) (hm2865 := hm2865) (ev2838 := ev2838) (ev2882 := ev2882)
      (ev2912 := ev2912) (ev2942 := ev2942) (ev2964 := ev2964) (ev2986 := ev2986)
      (ev3157 := evf) (hc3182 := hcs) .. =>
    -- the modeled route runs the family check at the value's block field, which is refused
    injection shape with _ _ entries
    simp only [List.cons.injEq] at entries
    obtain ⟨-, -, -, -, -, -, -, -, -, hblock, -⟩ := entries
    subst hblock
    have enil : Heap.Extends m2789 m2857 := by rw [hm2865]; exact Heap.Extends.snoc m2789 _
    exact (hfr _ _ _ _ _ (ev14.heap_extends.trans (ev2801.heap_extends.trans (enil.trans
      (ev2838.heap_extends.trans (ev2882.heap_extends.trans (ev2912.heap_extends.trans
      (ev2942.heap_extends.trans (ev2964.heap_extends.trans ev2986.heap_extends))))))))
      (fun cl hcl => by rw [hcs]; simp [hcl]) evf).elim
  | .Rec_n0 (m2 := scopeBefore) (m2789 := scopeAfter) (m2857 := sortBefore)
      (m2826 := sortAfter) (m2870 := safeAfter) (m2900 := rulesAfter) (m2930 := kindsAfter)
      (m2952 := familyAfter) (m2974 := memberHeap)
      (ev14 := unsafeRun) (hv2727 := shape) (ev2801 := scopeRun) (hm2865 := nilSort)
      (ev2838 := sortRun) (ev2882 := safeRun) (ev2912 := rulesRun) (ev2942 := kindsRun)
      (ev2964 := familyRun) (ev2986 := modeledRun) (ev3068 := memberRun)
      (hc3093 := allCalls) .. =>
    injection shape with _ _ entries
    injection entries with levelEq entries
    injection entries with typeEq entries
    subst levelEq typeEq
    have e1 : Heap.Extends scopeAfter sortBefore := by
      rw [nilSort]
      exact Heap.Extends.snoc _ _
    have hext : Heap.Extends h memberHeap :=
      unsafeRun.heap_extends.trans (scopeRun.heap_extends.trans (e1.trans
        (sortRun.heap_extends.trans (safeRun.heap_extends.trans (rulesRun.heap_extends.trans
          (kindsRun.heap_extends.trans (familyRun.heap_extends.trans
            modeledRun.heap_extends)))))))
    refine ⟨scopeBefore, scopeAfter, memberHeap, _, _, _, unsafeRun.heap_extends, scopeRun,
      ?_, hext, memberRun, ?_⟩
    · rw [allCalls]; simp
    · intro call member
      rw [allCalls]
      simp [member]

/-! ## The route of the member check, with its calls -/

/-- **The native route of `check_recursor_member`, each run within the member check's calls**:
the scan of the type for the major premise's parent, the load of the parent as an inductive, and
the test of its block, which answers `0`. -/
theorem native_rec_route_calls
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position
      result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address]
      heap result final calls) :
    ∃ (parent pointer : SourceValue F) (scanHeap loadedHeap routedHeap : Heap F)
      (scanCalls loadCalls routeCalls : List (Call F))
      (parentLevels parentType parentParams parentIndices constructors parentUnsafe parentBlock
        parentIndex : SourceValue F),
      ObsFn Obs.W "KernelCheck::rec_to_parent_addr" [type, parameters, motives, minors, indices]
        heap parent scanHeap scanCalls ∧
      (∀ cl ∈ scanCalls, cl ∈ calls) ∧
      ObsFn Obs.W "Ingress::get_ci" [parent] scanHeap pointer loadedHeap loadCalls ∧
      (∀ cl ∈ loadCalls, cl ∈ calls) ∧
      loadValue loadedHeap pointer = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
          parentBlock, parentIndex]) ∧
      ObsFn Obs.W "KernelModeled::block_is_modeled" [parentBlock]
        loadedHeap (.field 0) routedHeap routeCalls ∧
      (∀ cl ∈ routeCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (v72 := parent) (m73 := scanHeap) (p134 := pointer) (m127 := loadedHeap)
      (cs83 := scanCalls) (cs140 := loadCalls) (x__parent_nlvls := parentLevels)
      (w167 := parentType) (x_parent_np := parentParams) (x_parent_ni := parentIndices)
      (x_num_ctors := constructors) (w168 := parentUnsafe) (x_parent_block_addr := parentBlock)
      (x_parent_ind_idx := parentIndex) (m223 := routedHeap) (cs231 := routeCalls)
      (hv15 := input) (ev85 := scan) (ev142 := load) (ld136 := parentInfo)
      (ev233 := route) (heq248 := native)
      (hc898 := children) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    rw [native] at route
    refine ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
      parentLevels, parentType, parentParams, parentIndices, constructors, parentUnsafe,
      parentBlock, parentIndex, scan, ?_, load, ?_, parentInfo, route, ?_⟩
    · intro call member; rw [children]; simp [member]
    · intro call member; rw [children]; simp [member]
    · intro call member; rw [children]; simp [member]

/-! ## The evidence at the record, and the basis hypothesis -/

/-- **The check of the record took the recursor arm**: the walk loaded the record at `A` under
a role context at the limit `n` and ran `check_const` on the loaded `Rec` value, its calls among
the run's (`check_const_rec_route` then gives the member check). -/
def NativeRecArm (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (A : _root_.Address) (n : Nat) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr r_chk : SourceValue F)
    (levels type parameters indices motives minors rules k unsafeFlag block position : SourceValue F)
    (cs_load cs_chk : List (Call F)),
    Claim.RCFullRep t bAddr n h_pre rc ∧ Claim.RCFullRep t bAddr n m_chk rc ∧
    Core.BaseSeams.addr h_pre ap A ∧ Core.BaseSeams.addr m_chk ap A ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
      [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position]) ∧
    ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position],
        ap] m_chk r_chk h'_chk cs_chk ∧
    (∀ cl ∈ cs_chk, cl ∈ calls) ∧
    Claim.FamilyCheckRefused rc block m_chk cs_chk

/-- **The check of the record took the recursor arm, at the limit `lim`**: `NativeRecArm` with
the role context read as the core reads it (`Core.RCRep`), at a validating limit `some n` or
under an assumed binding (`none`). The check of a recursor record reads nothing else of the
role context, so one statement serves both validators. -/
def RecArmRun (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (A : _root_.Address)
    (lim : Option Nat) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr r_chk : SourceValue F)
    (levels type parameters indices motives minors rules k unsafeFlag block position : SourceValue F)
    (cs_load cs_chk : List (Call F)),
    Core.RCRep t lim h_pre rc ∧ Core.RCRep t lim m_chk rc ∧
    Core.BaseSeams.addr h_pre ap A ∧ Core.BaseSeams.addr m_chk ap A ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
      [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position]) ∧
    ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block, position],
        ap] m_chk r_chk h'_chk cs_chk ∧
    (∀ cl ∈ cs_chk, cl ∈ calls) ∧
    Claim.FamilyCheckRefused rc block m_chk cs_chk

/-- The arm of a validating run is the arm at its limit. -/
theorem NativeRecArm.run {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {A : _root_.Address} {n : Nat}
    (h : NativeRecArm calls bAddr t A n) : RecArmRun calls t A (some n) := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre, ha_m, ev_ld,
    hsub_ld, hld, ev_chk, hsub_chk, hfr⟩ := h
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, hrc_pre.toRCRep, hrc_m.toRCRep,
    ha_pre, ha_m, ev_ld, hsub_ld, hld, ev_chk, hsub_chk, hfr⟩

/-- **The head of the major premise's domain is no basis name**, record-scoped: in every
annotation of the record's type as read (positional level parameters, over the run's blobs),
the key heading the major premise's domain (`majorKey`) is no reserved basis name. The circuit's
basis-recursor guard is its producer. -/
def RecMajorNotBasis (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (A : _root_.Address)
    (c : Ixon.Constant) (rc : Ixon.Recursor) : Prop :=
  ∀ (tyP E' : Ix.Kernel.Expr .anon) (k : Ix.Kernel.Key .anon),
    (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t A)).read rc.typ = .ok tyP →
    Annotates E' tyP → majorKey rc E' = some k →
    Ix.Kernel.reservedBasisNames.contains k = false

/-- The head of the domain of binder `params + motives + minors + indices` is the major key. -/
theorem majorKey_of_piDomAt {rc : Ixon.Recursor} {e dom : Core.KExpr} {k : Core.KKey}
    {us : List Core.KLevel}
    (hpi : Core.piDomAt (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) e = some dom)
    (hhead : dom.getAppFn = .const k us) : majorKey rc e = some k := by
  obtain ⟨pre, body, bm, hst⟩ := (Decl.piDomAt_eq_some_iff _ _ _).mp hpi
  have hb : binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      e = some dom := by
    unfold binderDom
    rw [hst]
  unfold majorKey
  rw [hb]
  show headKey dom = some k
  unfold headKey
  rw [hhead]

/-- The references a recursor record's type uses are references the record uses. -/
theorem recr_typ_usedRefs {c : Ixon.Constant} {rc : Ixon.Recursor} (hinfo : c.info = .recr rc) :
    ∀ i, i ∈ exprRefIdxs rc.typ → i ∈ usedRefIdxs c := by
  intro i hi
  unfold usedRefIdxs
  rw [hinfo]
  exact List.mem_append_right _ (List.mem_append_left _ hi)

/-! ## The parent, from the check of the record -/

/-- **The parent family the circuit read at a recursor record, from the walk's check of the
record.** At every environment the skeleton hands the step, the parent is a stored former under
no basis name whose record is an inductive projection of a native block. Inputs: the run's
store and the step's store, the record, the check of the record at the walk's limit, the
record's used references stored (`hinert`, `hcover`), and the record-scoped basis hypothesis. -/
theorem recParent_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hres : RecMajorNotBasis t E₀ A c rc)
    (env : Ix.Kernel.Env .anon) (hstep : StepAt.{u} t envT E₀ E lim A c env) :
    ∃ P ip, RecParent t E env P ip := by
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk, hfr⟩ := hnat
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  -- the load of the record, traced
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    Ingress.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold Ingress.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, b, planT, -, -, hv, rty,
    -, -, -⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -, -⟩ := hfields
  -- the blobs the load hashed are the run's
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  -- the type reads, well scoped by the arm's scope check
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk hfr
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  -- represented under the table's keying, then under the prefix's
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
  -- the route of the member check
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, evScan, hsScan, evLoad, hsLoad, hldP, evRoute, hsRoute⟩ :=
    native_rec_route_calls evM
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  exact recParent_of_route hstep.inv hgood (htmS.mono hextM) evScan
    (fun x hx => hsub_chk x (hsubM x (hsScan x hx))) evLoad
    (fun x hx => hsub_chk x (hsubM x (hsLoad x hx))) hldP evRoute
    (fun x hx => hsub_chk x (hsubM x (hsRoute x hx)))
    (fun dom k us hpi hhead => hres tyP E' k htyP hann
      (majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead))

end IxVM.Refinement.Typing
