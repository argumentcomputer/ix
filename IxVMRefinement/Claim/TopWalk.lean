import IxVMRefinement.Claim.TopSeed
import IxVMRefinement.Claim.TopRefs
import IxVMRefinement.Claim.TopDecode
import IxVMRefinement.Claim.TopWalkCheck
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Assembly.TypingSkeleton
import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Obs.KernelRoles2
import IxVMRefinement.Obs.KernelRoleSpec0
import IxVMRefinement.Obs.KernelClaim1

/-! # The claim layer's walk export for the typing half

`TopWalkCore` is what a typing run's walk gives the assembly, read off the walk at the run's
top-level limit (`some 77` when the run validates its table, `none` when it assumes it):

* the run's store `E₀` (every canonical record and blob the run hashed) is a run store;
* the top-walked addresses `Top` hold the seeds and records; a reference a top-walked record
  uses is top-walked at a smaller rank or covered (`Typing.Covered`: bound to a role whose
  record a validation walks); a projection record's block is top-walked at a smaller rank;
* each top-walked record was checked at the limit (`CheckedLimAt`, `MemberCheckedLimAt`);
* no used reference is an inert axiom, and no uncovered used reference is a block record;
* the seeds are in Lean's logic and no inert axiom.

`topWalkCore_of_recs` builds it from a closed list of records walked at the limit (any walk
spec of this lane) and the seeds' refusals; `claimPhase_typing_check` gives it for a `check`
claim (`run_claim` arm 4) in both modes, and leaves a `checkEnv` claim's walk
(`walk_leaves_owned`, arm 5) as its observation (`EnvWalkRun`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-- **What the walk of a typing run exports** at the binding `bAddr` (module docstring). -/
structure TopWalkCore (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address) (E₀ : Ixon.Env)
    (lim : Option Nat) (Top : _root_.Address → Prop) (rank : _root_.Address → Nat) : Prop where
  topLim : lim = some 77 ∨ lim = none
  table : ∃ tb, Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨bAddr, tb⟩ = .ok t
  runStore : LoadedReads.RunStore calls E₀
  hashedStored : LoadedReads.HashedRecordsStored calls E₀
  seedsTop : ∀ a ∈ seeds, Top a
  record : ∀ a, Top a → ∃ c, recordOf E₀ a = some c
  closed : ∀ a x, Top a → Typing.UsedRef E₀ a x → (Top x ∧ rank x < rank a) ∨ Typing.Covered t x
  owner : ∀ a c, Top a → recordOf E₀ a = some c → Typing.IsProj c →
    Top (Ix.Cert.ownerOf a c) ∧ rank (Ix.Cert.ownerOf a c) < rank a
  seedLogic : ∀ a ∈ seeds, ∀ c, recordOf E₀ a = some c →
    InLogic c ∧ ∀ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb → InLogic cb
  seedNotInert : ∀ a ∈ seeds, ¬ InertAt t a
  checked : ∀ a, Top a → ∃ c, recordOf E₀ a = some c ∧
    ((∃ ms, c.info = .muts ms ∧ ∀ k, k < ms.size → MemberCheckedLimAt calls bAddr t a ms k lim) ∨
      CheckedLimAt calls bAddr t a lim)
  refsNotInert : ∀ a x, Top a → Typing.UsedRef E₀ a x → ¬ InertAt t x
  refsNotBlock : ∀ a x, Top a → Typing.UsedRef E₀ a x → ¬ Typing.Covered t x →
    ∀ c, recordOf E₀ x = some c → ¬ Typing.IsBlock c
  safeRefs : ∀ a x, Top a → SourceSafe E₀ a → Typing.UsedRef E₀ a x →
    ¬ Typing.Covered t x → SourceSafe E₀ x
  quotBound : ∀ x ro c, Top x → quotRole ro = true → t.addressOf? ro = some x →
    recordOf E₀ x = some c → Typing.Standalone c ∧ ∀ y, Typing.UsedRef E₀ x y →
      Typing.Covered t y ∨ ∃ ro', quotRole ro' = true ∧ t.addressOf? ro' = some y

/-! ## Quotient-bound records (`assert_quot_record_refs`) -/

private theorem quotRole_iff_sub_32 (ro : Ix.Kernel.Role) :
    quotRole ro = true ↔
      roleNum ro - (32 : F) = (0 : F) ∨ roleNum ro - (32 : F) = (1 : F) ∨
      roleNum ro - (32 : F) = (2 : F) ∨ roleNum ro - (32 : F) = (3 : F) ∨
      roleNum ro - (32 : F) = (4 : F) := by
  cases ro <;> decide

theorem addr_quot_bound_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::addr_quot_bound" [x_rc, x_a] h r h' calls) :
    h' = h ∧
      ((r = .field 0 ∧ ∀ ro, quotRole ro = true → t.addressOf? ro ≠ some a) ∨
       (r = .field 1 ∧ ∃ ro, quotRole ro = true ∧ t.addressOf? ro = some a)) := by
  match Obs.«KernelRoles::addr_quot_bound».obs ev with
  | .n0 (ev_rcqbqram := evr) (he_daqahcdl := hr) (he_bhektsom := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨-, hnone⟩ | ⟨ro, h0, -⟩
    · exact ⟨hh, .inl ⟨hr, fun ro _ => hnone ro⟩⟩
    · exact absurd (Value.field.inj h0).symm (RolesAux.roleNum_add_one_ne_zero ro)
  | .other_n0 (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_hvsdcsbp := op1)
      (ev_oakdyycl := evq) (op_bssudskp := op2) (he_qzstfxnn := hr) (he_lwvfeqiv := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op1; subst op1
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs evq
      simp only [evalBinOp, Except.ok.injEq] at op2
      exact ⟨hh, .inr ⟨hr, ro, (quotRole_iff_sub_32 ro).mpr (.inl (Value.field.inj op2)), hof⟩⟩
  | .other_n1 (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_hvsdcsbp := op1)
      (ev_oakdyycl := evq) (op_bssudskp := op2) (he_yyywwiyz := hr) (he_gzcylbfx := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op1; subst op1
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs evq
      simp only [evalBinOp, Except.ok.injEq] at op2
      exact ⟨hh, .inr ⟨hr, ro, (quotRole_iff_sub_32 ro).mpr (.inr (.inl (Value.field.inj op2))), hof⟩⟩
  | .other_n2 (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_hvsdcsbp := op1)
      (ev_oakdyycl := evq) (op_bssudskp := op2) (he_qadijrxe := hr) (he_yrhrpjvx := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op1; subst op1
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs evq
      simp only [evalBinOp, Except.ok.injEq] at op2
      exact ⟨hh, .inr ⟨hr, ro,
        (quotRole_iff_sub_32 ro).mpr (.inr (.inr (.inl (Value.field.inj op2)))), hof⟩⟩
  | .other_n3 (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_hvsdcsbp := op1)
      (ev_oakdyycl := evq) (op_bssudskp := op2) (he_hcborifo := hr) (he_msijpbpf := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op1; subst op1
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs evq
      simp only [evalBinOp, Except.ok.injEq] at op2
      exact ⟨hh, .inr ⟨hr, ro,
        (quotRole_iff_sub_32 ro).mpr (.inr (.inr (.inr (.inl (Value.field.inj op2))))), hof⟩⟩
  | .other_n4 (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_hvsdcsbp := op1)
      (ev_oakdyycl := evq) (op_bssudskp := op2) (he_tdbumkgo := hr) (he_lgppkpmn := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op1; subst op1
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs evq
      simp only [evalBinOp, Except.ok.injEq] at op2
      exact ⟨hh, .inr ⟨hr, ro,
        (quotRole_iff_sub_32 ro).mpr (.inr (.inr (.inr (.inr (Value.field.inj op2))))), hof⟩⟩
  | .other_other (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_hvsdcsbp := op1)
      (ev_oakdyycl := evq) (op_bssudskp := op2) (hne_trdykyhf := hn0) (hne_arcdkpuy := hn1)
      (hne_lowihoxb := hn2) (hne_teyjavyr := hn3) (hne_ezgksmjk := hn4)
      (he_lhxtzule := hr) (he_xhtrolce := hh) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op1; subst op1
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::role_quot».obs evq
      simp only [evalBinOp, Except.ok.injEq] at op2; subst op2
      refine ⟨hh, .inl ⟨hr, fun ro' hq' hof' => ?_⟩⟩
      obtain ⟨_, ⟨hwf, -⟩, -⟩ := hrc.cases
      have hro_eq : ro' = ro :=
        Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
      subst hro_eq
      rcases (quotRole_iff_sub_32 ro').mp hq' with h0 | h1 | h2 | h3 | h4
      · exact hn0 (congrArg Value.field h0)
      · exact hn1 (congrArg Value.field h1)
      · exact hn2 (congrArg Value.field h2)
      · exact hn3 (congrArg Value.field h3)
      · exact hn4 (congrArg Value.field h4)

theorem addr_walked_role_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::addr_walked_role" [x_rc, x_a] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ (r = .field 1 ∧ Typing.Covered t a)) := by
  match Obs.«KernelRoles::addr_walked_role».obs ev with
  | .n0 (ev_rcqbqram := evr) (he_daqahcdl := hr) (he_bhektsom := hh) .. =>
    obtain ⟨rfl, -⟩ := role_index_of_lim_spec hrc ha evr
    exact ⟨hh, .inl hr⟩
  | .other (ev_rcqbqram := evr) (hne_xjnibfzs := hne) (op_buvadoef := op)
      (ev_opsbypwq := eva) .. =>
    obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha evr
    rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
    · exact absurd h0 hne
    · subst hro
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op; subst op
      obtain ⟨rfl, hr⟩ := role_admission_checks_walks eva
      exact ⟨rfl, hr.imp id fun ⟨h1, hw⟩ => ⟨h1, ro, hof, hw⟩⟩

private theorem quot_refs_ok_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rc rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      RCLimRep t bAddr lim h rc →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs rp →
      RepSortedIdxFrom h idxs i used →
      ObsFn Obs.W "KernelClaim::quot_refs_ok" [rc, rp, used, .field (i : F)] h r h' cs →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs →
        Typing.Covered t refs[j] ∨ ∃ ro, quotRole ro = true ∧ t.addressOf? ro = some refs[j] := by
  induction refs with
  | nil => intro i idxs rc rp used r h h' cs hb hrc hr hi ev j hj; cases hj
  | cons a rest ih =>
    intro i idxs rc rp used r h h' cs hb hrc hr hi ev
    match Obs.«KernelClaim::quot_refs_ok».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (m_sszfdvej := mSeg) (ld_bolbylmd := ld) (ev_ahqcgauk := evPop)
        (sg_opqpxwys := seg) (op_gskedpnl := op) (ev_rajcapyd := evr) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      obtain ⟨rfl, hiff, hiNext⟩ := sorted_pop_spec idxs (by simp at hb; omega) hi evPop
      have hseg : Heap.Extends h mSeg ∧ (i ∈ idxs →
          Typing.Covered t a ∨ ∃ ro, quotRole ro = true ∧ t.addressOf? ro = some a) := by
        match seg with
        | .other (hne_yeueqpng := hn) (he_eemargwo := hh) .. =>
          exact ⟨hh ▸ Heap.Extends.refl _, fun hm => (hn (hiff.mpr hm)).elim⟩
        | .n1 (ev_akfsjgww := evw) (ev_ovoaytiw := evq)
            (op_veoctrkq := opAdd) (heq_cbhcrbea := heq1) (he_glsulvqd := hh) .. =>
          obtain ⟨rfl, hw⟩ := addr_walked_role_lim_spec hrc ha evw
          obtain ⟨rfl, hq⟩ := addr_quot_bound_lim_spec hrc ha evq
          refine ⟨by rw [hh], fun _ => ?_⟩
          rcases hw with rfl | ⟨-, hcov⟩
          · rcases hq with ⟨rfl, -⟩ | ⟨-, hqb⟩
            · simp only [evalBinOp, add_zero, Except.ok.injEq] at opAdd
              exact absurd (Value.field.inj (opAdd.trans heq1)) zero_ne_one
            · exact .inr hqb
          · exact .inl hcov
      obtain ⟨ext, hhead⟩ := hseg
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at evr
      have htail := ih (i + 1) (by simp at hb ⊢; omega) (hrc.mono ext)
        (repList_heapMono₂ _ repAddrElem_heapMono₂ ext hrest)
        (hiNext.mono ext) evr
      intro j hj hm
      cases j with
      | zero => exact hhead (by simpa only [Nat.add_zero] using hm)
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact htail j hj' (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)

theorem QuotRecordRefsIn.spec {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant} {ro : Ix.Kernel.Role}
    (hrefs : c.refs.size < 8589934592) (hq : QuotRecordRefsIn calls t bAddr lim a c)
    (hqr : quotRole ro = true) (hof : t.addressOf? ro = some a) :
    Typing.Standalone c ∧ ∀ i ∈ usedRefIdxs c, ∀ y, c.refs[i]? = some y →
      Typing.Covered t y ∨ ∃ ro', quotRole ro' = true ∧ t.addressOf? ro' = some y := by
  obtain ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hcp, ev, -⟩ := hq
  match Obs.«KernelClaim::assert_quot_record_refs».obs ev with
  | .n0 (ev_lhvvlvzx := evq) .. =>
    obtain ⟨-, ⟨-, hnone⟩ | ⟨h0, -⟩⟩ := addr_quot_bound_lim_spec hrc ha evq
    · exact (hnone ro hqr hof).elim
    · exact absurd (Value.field.inj h0) zero_ne_one
  | .other (m_jrmullwx := mSeg) (x_info := x_info) (x_refs := x_refs) (ev_lhvvlvzx := evq)
      (hv_cdpymqwc := hv) (sg_qqmcdzij := seg) (heq_zxortwso := h1)
      (ev_lfynsjgt := evIdx) (ev_oucfbbyu := evLoop) .. =>
    obtain ⟨hmQ, -⟩ := addr_quot_bound_lim_spec hrc ha evq
    rw [hmQ] at seg
    have hcp' := hcp
    obtain ⟨infoVal, _, rfPtr, _, _, hcp_eq, hinfo, _, hrf, _, _⟩ := hcp'
    have heq := hcp_eq.symm.trans hv
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at heq
    rcases heq with ⟨hinfo_eq, _, hrf_eq, _, _⟩
    rw [hinfo_eq] at hinfo
    rw [hrf_eq] at hrf
    have hstand : Typing.Standalone c ∧ mSeg = h := by
      match seg with
      | .Quot (hv_wlehqhre := hq_v) (he_danydyxy := hh) .. =>
        rw [hq_v] at hinfo
        cases hci : c.info <;> rw [hci] at hinfo
        case quot q => exact ⟨.inr (.inr (.inr ⟨q, hci⟩)), hh⟩
        all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
      | .Axio (hv_qcgdvgos := hax_v) (he_ebfeplnh := hh) .. =>
        rw [hax_v] at hinfo
        cases hci : c.info <;> rw [hci] at hinfo
        case axio ax => exact ⟨.inr (.inr (.inl ⟨ax, hci⟩)), hh⟩
        all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
      | .other (he_ccliwrit := h0) .. =>
        exact absurd (Value.field.inj (h0.symm.trans h1)) zero_ne_one
    obtain ⟨hs, hmSeg⟩ := hstand
    rw [hmSeg] at evIdx
    obtain ⟨extIdx, hidx⟩ := const_idxs_of_spec hcp evIdx
    have hloop := quot_refs_ok_spec c.refs.toList 0
      (by simpa only [Nat.zero_add, Array.length_toList] using hrefs)
      (hrc.mono extIdx) (repList_heapMono₂ _ repAddrElem_heapMono₂ extIdx hrf) hidx evLoop
    refine ⟨hs, fun i hi y hy => ?_⟩
    have hy' : c.refs.toList[i]? = some y := by simpa only [Array.getElem?_toList] using hy
    obtain ⟨hiLt, hget⟩ := List.getElem?_eq_some_iff.mp hy'
    have hi' : i ∈ S0.usedRefIdxs c := by rw [Assembly.usedRefIdxs_eq]; exact hi
    have hres := hloop i hiLt (by simpa only [Nat.zero_add] using hi')
    rwa [hget] at hres

/-- The store of the run's hashed records and blobs at the binding `b`. -/
noncomputable def runEnv (b : Ix.Kernel.Admission.Binding) {t : Ix.Kernel.RoleTable}
    (calls : List (Call F)) : Ixon.Env :=
  envOfRecs b calls ([] : List (WalkedRec calls b.address t))

/-- The rank of an address among a walk's records: the least depth of a record at it. -/
noncomputable def topRank {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} (recs : List (TopRec calls bAddr t lim))
    (a : _root_.Address) : Nat :=
  sInf {d | ∃ r ∈ recs, r.addr = a ∧ r.depth = d}

section Build

variable {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
  {lim : Option Nat}

theorem topRank_le {recs : List (TopRec calls b.address t lim)} {r : TopRec calls b.address t lim}
    (hr : r ∈ recs) : topRank recs r.addr ≤ r.depth :=
  Nat.sInf_le ⟨r, hr, rfl, rfl⟩

theorem exists_min_rec {recs : List (TopRec calls b.address t lim)} {a : _root_.Address}
    (ha : ∃ r ∈ recs, r.addr = a) :
    ∃ r ∈ recs, r.addr = a ∧ r.depth = topRank recs a := by
  obtain ⟨r, hr, hra⟩ := ha
  exact Nat.sInf_mem (s := {d | ∃ r ∈ recs, r.addr = a ∧ r.depth = d}) ⟨r.depth, r, hr, hra, rfl⟩

/-- **The walk export from a closed list of records walked at a top-level limit**, the seeds
among them and refused by `assert_claimable`, when the run hashed no collision. -/
theorem topWalkCore_of_recs
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hlim : lim = some 77 ∨ lim = none)
    (recs : List (TopRec calls b.address t lim)) (hcl : TopRecsClosed recs)
    {seeds : List _root_.Address} (hseeds : ∀ a ∈ seeds, a ∈ recs.map (·.addr))
    (hseedOk : ∀ a ∈ seeds, ClaimableSeed calls t a) :
    TopWalkCore calls b.address t seeds (runEnv b (t := t) calls) lim
      (fun a => ∃ r ∈ recs, r.addr = a) (topRank recs) := by
  have hw0 : WalkedL6 calls t (runEnv b (t := t) calls) [] :=
    walkedL6_envOfRecs (seeds := []) hnoColl [] hadm (by simp) (by intro r hr; cases hr)
  have hload : LoadedBy calls (runEnv b (t := t) calls) := envOfRecs_loadedBy b calls []
  have hS : LoadedReads.RunStore calls (runEnv b (t := t) calls) :=
    LoadedReads.RunStore.of_walkedL6 hload hw0
  have hH : LoadedReads.HashedRecordsStored calls (runEnv b (t := t) calls) :=
    LoadedReads.hashedRecordsStored_of_walkedL6 hw0
  have hrec : ∀ r ∈ recs, recordOf (runEnv b (t := t) calls) r.addr = some r.c := by
    intro r hr
    obtain ⟨lc, hget, hraw, -⟩ := hH r.rawBytes r.c r.hhashed r.hsz r.hde r.hdeExact
    rw [r.hblake] at hget
    unfold recordOf
    rw [hget]
    simp [hraw, r.hdeExact, Except.toOption]
  have huniq : ∀ r ∈ recs, ∀ c, recordOf (runEnv b (t := t) calls) r.addr = some c → c = r.c := by
    intro r hr c hc
    rw [hrec r hr] at hc
    exact (Option.some.inj hc).symm
  have hat : ∀ {a : _root_.Address} {c : Ixon.Constant},
      recordOf (runEnv b (t := t) calls) a = some c →
      Ix.Cert.recordAt (runEnv b (t := t) calls) a = some c :=
    fun {a c} h => (hS.recordOf_eq_recordAt a).symm.trans h
  -- the record at a top-walked address, with the least depth
  have hmin : ∀ a c, (∃ r ∈ recs, r.addr = a) → recordOf (runEnv b (t := t) calls) a = some c →
      ∃ r ∈ recs, r.addr = a ∧ r.depth = topRank recs a ∧ r.c = c := by
    intro a c hTa hc
    obtain ⟨r, hr, hra, hrd⟩ := exists_min_rec hTa
    refine ⟨r, hr, hra, hrd, ?_⟩
    subst hra
    exact (huniq r hr c hc).symm
  have huse : ∀ (c : Ixon.Constant) (i : Nat) (x : _root_.Address), i ∈ usedRefIdxs c →
      c.refs[i]? = some x → i ∈ S0.usedRefIdxs c := by
    intro c i x hi _
    rw [Assembly.usedRefIdxs_eq]
    exact hi
  refine
    { topLim := hlim
      table := ⟨b.bytes, by cases b; exact hadm⟩
      runStore := hS
      hashedStored := hH
      seedsTop := fun a ha => List.mem_map.mp (hseeds a ha) |>.imp fun r h => ⟨h.1, h.2⟩
      record := ?_
      closed := ?_
      owner := ?_
      seedLogic := ?_
      seedNotInert := fun a ha => (hseedOk a ha).notInert
      checked := ?_
      refsNotInert := ?_
      refsNotBlock := ?_
      safeRefs := ?_
      quotBound := ?_ }
  · rintro a ⟨r, hr, rfl⟩
    exact ⟨r.c, hrec r hr⟩
  · rintro a x hTa ⟨c, i, hc, hi, hx⟩
    obtain ⟨r, hr, rfl, hrd, rfl⟩ := hmin a c hTa hc
    obtain ⟨-, hrest⟩ := (hcl r hr).2 i (huse _ i x hi hx) x hx
    rcases hrest with ⟨-, r', hr', rfl, hlt⟩ | ⟨ro, hof, hw, -⟩
    · exact .inl ⟨⟨r', hr', rfl⟩, by have := topRank_le hr'; omega⟩
    · exact .inr ⟨ro, hof, hw⟩
  · intro a c hTa hc hp
    obtain ⟨r, hr, rfl, hrd, rfl⟩ := hmin a c hTa hc
    obtain ⟨r', hr', ha', hlt⟩ := (hcl r hr).1 hp
    rw [← ha']
    exact ⟨⟨r', hr', rfl⟩, by have := topRank_le hr'; omega⟩
  · intro a ha c hc
    have hout := claimableSeed_not_outsideLogicAt (b := b) hnoColl
      ([] : List (WalkedRec calls b.address t)) (hseedOk a ha)
    refine ⟨?_, fun cb hcb => ?_⟩
    · by_contra hn
      exact hout ⟨c, hat hc, Or.inl hn⟩
    · by_contra hn
      exact hout ⟨c, hat hc, Or.inr ⟨cb, hat hcb, hn⟩⟩
  · rintro a ⟨r, hr, rfl⟩
    exact ⟨r.c, hrec r hr, r.hchecked⟩
  · rintro a x hTa ⟨c, i, hc, hi, hx⟩
    obtain ⟨r, hr, rfl, -, rfl⟩ := hmin a c hTa hc
    obtain ⟨hal, -⟩ := (hcl r hr).2 i (huse _ i x hi hx) x hx
    exact refAllowed_not_inert_top hal hlim
  · rintro a x hTa ⟨c, i, hc, hi, hx⟩ hncov cx hcx ⟨ms, hms⟩
    obtain ⟨r, hr, rfl, -, rfl⟩ := hmin a c hTa hc
    obtain ⟨-, hrest⟩ := (hcl r hr).2 i (huse _ i x hi hx) x hx
    rcases hrest with ⟨⟨raw, c', hh, hb, hd, hn⟩, r', hr', rfl, -⟩ | ⟨ro, hof, hw, -⟩
    · have hraw : raw = r'.rawBytes := hnoColl raw r'.rawBytes hh r'.hhashed (hb.trans r'.hblake.symm)
      rw [hraw, r'.hde] at hd
      have hc' : r'.c = c' := Except.ok.inj hd
      have hcx' : cx = r'.c := huniq r' hr' cx hcx
      exact hn ms (hc' ▸ hcx' ▸ hms)
    · exact hncov ⟨ro, hof, hw⟩

  · rintro a x hTa hsafe ⟨c, i, hc, hi, hx⟩ hncov
    obtain ⟨r, hr, rfl, _, rfl⟩ := hmin a c hTa hc
    exact r.hguard.safe hS hH (hrec r hr) hsafe i hi x (by simpa using hx)
      (by rintro ⟨ro, hof, hw, _⟩; exact hncov ⟨ro, hof, hw⟩)
  · intro x ro c hTx hqr hof hc
    obtain ⟨r, hr, rfl, -, rfl⟩ := hmin x c hTx hc
    have hrefs : r.c.refs.size < 8589934592 := by
      have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound r.rawBytes r.c r.hdeExact
      have hsz := r.hsz
      have : r.c.refs.size ≤ r.c.resourceSize := by dsimp [Ixon.Constant.resourceSize]; omega
      omega
    obtain ⟨hstand, hrefsOk⟩ := r.hquot.spec hrefs hqr hof
    refine ⟨hstand, fun y ⟨c', i, hc', hi, hy⟩ => ?_⟩
    have hc_eq : c' = r.c := huniq r hr c' hc'
    subst hc_eq
    exact hrefsOk i hi y hy


end Build

/-- **Inhabitation test: the validating walk export gives `WalkedL6`'s walk data** on the
top-walked addresses: the seeds are walked, every walked address holds a record with the
check witnesses `WalkedL6` carries (`CheckedAtFull`, `MutsMemberCheckedAtFull`), and an edge
along a used reference decreases the rank unless it ends at a covered address (`WalkedL6`'s
closure without the covered branch, which an assumed run does not have). -/
theorem topWalkCore_walkedL6_data {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ (some 77) Top rank) :
    (∀ a ∈ seeds, Top a) ∧
    (∀ a, Top a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
      ((∃ ms, c.info = .muts ms ∧
        ∀ (k : Nat), k < ms.size → MutsMemberCheckedAtFull calls bAddr t a ms k) ∨
       CheckedAtFull calls bAddr t a)) ∧
    (∀ a x, Top a → Typing.UsedRef E₀ a x → ¬ Typing.Covered t x → Top x ∧ rank x < rank a) := by
  refine ⟨hW.seedsTop, fun a hTa => ?_, fun a x hTa hu hnc => ?_⟩
  · obtain ⟨c, hc, hchk⟩ := hW.checked a hTa
    refine ⟨c, (hW.runStore.recordOf_eq_recordAt a).symm.trans hc, ?_⟩
    rcases hchk with ⟨ms, hms, hk⟩ | hcl
    · exact .inl ⟨ms, hms, fun k hlt => ⟨77, hk k hlt⟩⟩
    · exact .inr ⟨77, hcl⟩
  · rcases hW.closed a x hTa hu with h | h
    · exact h
    · exact absurd h hnc

/-! ## Adapters to the step theorems' hypotheses -/

/-- A reference that is no inert axiom of an admitted table has a key that is no inert key. -/
theorem inertKey_keyOf_false {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {x : _root_.Address} (h : ¬ InertAt t x) : inertKey (IxVM.Consistency.keyOf t x) = false := by
  rcases IxVM.Consistency.keyOf_cases t x with ⟨hk, -⟩ | ⟨r, hr, hk⟩
  · rw [hk]
    rfl
  · rw [hk]
    show r.inert = false
    cases hi : r.inert
    · rfl
    · exact absurd ⟨r, hi, addressOf_eq_some_of_mem_bound ht hr⟩ h

theorem TopWalkCore.check_ok {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) : t.check = .ok () := by
  obtain ⟨tb, hadm⟩ := hW.table
  exact ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed

/-- **`InertClause` of every step** (`hinert`), from A2. -/
theorem TopWalkCore.inertClause {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {A : _root_.Address}
    {c : Ixon.Constant} (hT : Top A) (hc : recordOf E₀ A = some c) : Typing.InertClause t c := by
  intro i hi x hx
  exact inertKey_keyOf_false hW.check_ok (hW.refsNotInert A x hT (Typing.usedRef_of_idx hc hi hx))

/-- **A `checkEnv` claim's walk, as observed**: `walk_leaves_owned` over the claim's leaves under
the context at `lim`. Its specification at a limit turns it into `TopWalkCore`. -/
def EnvWalkRun (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (seeds : List _root_.Address) (lim : Option Nat) : Prop :=
  ∃ (as : List Bytes.Address) (h₁ h₂ : Heap F) (x_rc x_leaves v₁ : SourceValue F)
    (cs₁ : List (Call F)),
    seeds ≠ [] ∧ as.map ixAddr = seeds ∧ RCLimRep t bAddr lim h₁ x_rc ∧
    RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ as x_leaves ∧
    ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] h₁ v₁ h₂ cs₁ ∧
    (⟨"KernelClaim::walk_leaves_owned", [x_rc, x_leaves], h₁⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs₁, cl ∈ calls)

/-- **The claim layer for a typing run** (A0, A1 for `check`, A2, A3): an accepted claim in
scope under a table that admits at its context's address hashed a collision, or at its
top-level limit (`some 77` validating, `none` assumed) its walk exports `TopWalkCore` (a
`check` claim) or is a `checkEnv` claim's walk (`EnvWalkRun`). -/
theorem claimPhase_typing_check
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Ix.Claim} (hde : Ix.Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d)
    (hscope : InScopeTyping c)
    {V : View} {seeds : List _root_.Address} (hseeds : ClaimSeeds c V seeds)
    {ctx : Ix.ClaimContext} (hctx : c.context? = some ctx) {tb : ByteArray}
    {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t) :
    V.HashedCollision (bytes :: tb :: committedFootprint) calls ∨
    ∃ lim : Option Nat, (lim = some 77 ∨ lim = none) ∧
      ((∃ (E₀ : Ixon.Env) (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
          TopWalkCore calls ctx.binding t seeds E₀ lim Top rank) ∨
        EnvWalkRun calls t ctx.binding seeds lim) := by
  rcases verify_claim_decode_typing_spec ev hde hpack hscope hseeds hctx hadm with
    hcoll | ⟨lim, hlim, hbr⟩
  · exact .inl hcoll
  rcases noColl_or_hashedCollision V (bytes :: tb :: committedFootprint) calls with
    hcoll | hnoColl
  · exact .inl hcoll
  refine .inr ⟨lim, hlim, ?_⟩
  rcases hbr with
    ⟨a, h₁, h₂, h₃, x_rc, x_a, v₁, v₂, cs₁, cs₂, rfl, hrc, ha, ev_ac, ev_rct, -, -, hsub₁, hsub₂⟩ |
    henv
  · left
    obtain ⟨ext_ac, hseed⟩ := assert_claimable_lim_spec hrc ha ev_ac
    obtain ⟨-, recs, hmem, hcl, -⟩ :=
      run_check_transitive_lim_spec (hrc.mono ext_ac) (S0.addr_mono ext_ac ha) ev_rct
    refine ⟨_, _, _, topWalkCore_of_recs (b := ⟨ctx.binding, tb⟩) hnoColl hadm hlim
      (recs.map (TopRec.mono hsub₂)) (hcl.mono hsub₂) (seeds := [a]) ?_ ?_⟩
    · intro x hx
      rcases List.mem_singleton.mp hx with rfl
      simpa only [map_addr_topRec_mono] using hmem
    · intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact hseed.mono hsub₁
  · exact .inr henv

end IxVM.Refinement.Claim
