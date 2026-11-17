import IxVMRefinement.Claim.TopWalk
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.L1.Ingress
import IxVMRefinement.L1.Stream
import IxVMRefinement.Obs

/-! # What `check_const` gives of a top walk's records

`TopWalkCore` records that every top-walked record was loaded by `Ingress::get_ci` and checked
by `KernelCheck::check_const` (`checked`). This module reads three more facts off those checks,
or records why the circuit does not give them.

## Proved: a top-walked block has members of one kind (`TopWalkCore.uniform`)

Every check of a block member passes through `KernelCheck::check_block_member_kinds` on the
member's block: a definition member in `Ingress::get_ci_dprj`, an inductive member in
`check_const`'s `Induct` arm, a recursor member in its `Rec` arm. That function refuses a block
that mixes a definition with an inductive, a definition with a recursor, or an inductive with a
recursor (`KernelCheck.lean`, `check_block_member_kinds`). So a block's members are all
definitions, all inductives or all recursors (a block of recursors is accepted; the `Rec` arm
then refuses a recursor of a modeled family). A block record is never checked as a constant of
its own: `get_ci` has no arm for a `Muts` record. The proof uses the member at index `0` (an
empty block satisfies every kind) and holds at every limit, validating or assumed.

## Not a property of every accepted run: in-logic records use only in-logic records

The walk follows every reference index a record names as a constant, sharing table included
(`KernelClaim::const_idxs_of` starts from `const_idxs_exprs(sharing)`), and so does the
statement's `usedRefIdxs`. The safety check of a record in Lean's logic
(`KernelCheck::assert_safety` over `safe_refs_only`) reads only the converted type and value
(rules, constructor types), and the conversion enters a sharing entry only through a `Share`
node of a root (`Convert::convert_expr`, `Share` arm). Deserialization does not require every
sharing entry to be reached (`IxonDeserialize::get_constant`, `Ixon.getConstant`). The walk
checks the referenced record under the same context, and `check_const` of an unsafe record
skips `assert_safety` (and, for an axiom, `axiom_standing`). So the circuit accepts, as a
`check` seed, a safe definition whose sharing table holds an entry `Ref(i, [])` that no root
reaches, with `refs[i]` an unsafe definition or an unsafe axiom: a seam, under which the
used-reference facts `usedLogic` (a used, uncovered reference of an in-logic record is in
Lean's logic with its block) and `standing` (a top-walked axiom record stands at a standard
axiom's role) both fail. The assembly's statements of them are left unproved here.

Supporting specifications: `muts_has_kind_spec` (`KernelCheck::muts_has_kind`),
`check_block_member_kinds_uniform`. -/

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

variable {calls : List (Call F)}

/-! ## `KernelCheck::muts_has_kind` -/

/-- The kind number `KernelCheck::muts_has_kind` reads off a block member: `0` an inductive,
`1` a definition, `2` a recursor. -/
def mutConstKindF : Ixon.MutConst → F
  | .indc _ => 0
  | .defn _ => 1
  | .recr _ => 2

private theorem tc_field_one_ne_zero : (Value.field (1 : F) : SourceValue F) ≠ .field 0 := by
  intro h
  injection h with h10
  exact one_ne_zero h10

private theorem tc_kind_ne {kf k : F} (hk : (Value.field kf : SourceValue F) ≠ .field k) :
    k ≠ kf :=
  fun h0 => hk (by rw [h0])

/-- **`KernelCheck::muts_has_kind`**: `1` when a member has the kind, `0` otherwise. -/
theorem muts_has_kind_spec (kf : F) (ms : List Ixon.MutConst) :
    ∀ {h h' : Heap F} {x_ms r : SourceValue F} {cs : List (Call F)},
      Aiur.Library.List.RepList Obs.Names.«Lists::Node<Ixon::MutConst>» Claim.RepMutConst h ms
        x_ms →
      ObsFn Obs.W "KernelCheck::muts_has_kind" [x_ms, .field kf] h r h' cs →
      h' = h ∧ (((∃ m ∈ ms, mutConstKindF m = kf) ∧ r = .field 1) ∨
        ((∀ m ∈ ms, mutConstKindF m ≠ kf) ∧ r = .field 0)) := by
  induction ms with
  | nil =>
    intro h h' x_ms r cs rep ev
    match Obs.«KernelCheck::muts_has_kind».obs ev with
    | .Nil (he20 := he) (he21 := hh) .. =>
      exact ⟨hh, .inr ⟨fun m hm => by simp at hm, he⟩⟩
    | .Cons_n1 (ld12 := ld12) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
    | .Cons_other (ld12 := ld12) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons m rest ih =>
    intro h h' x_ms r cs rep ev
    match Obs.«KernelCheck::muts_has_kind».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Lib.rep_nil_of_load rep ld12
    | .Cons_n1 (m162 := m162) (ld12 := ld12) (sg169 := sg) (he184 := he) (he185 := hh) .. =>
      obtain ⟨m', rest', heq, hm, -⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      have key : m162 = h ∧ mutConstKindF m = kf := by
        match sg with
        | .Indc_n0 (hv54 := hv) (hv75 := hk) (he77 := hh') .. =>
          refine ⟨hh', ?_⟩
          cases m with
          | indc _ => exact (Value.field.inj hk).symm
          | defn _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
          | recr _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
        | .Indc_other (he83 := he') .. => exact absurd he' tc_field_one_ne_zero
        | .Defn_n1 (hv91 := hv) (hv112 := hk) (he114 := hh') .. =>
          refine ⟨hh', ?_⟩
          cases m with
          | defn _ => exact (Value.field.inj hk).symm
          | indc _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
          | recr _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
        | .Defn_other (he120 := he') .. => exact absurd he' tc_field_one_ne_zero
        | .Recr_n2 (hv128 := hv) (hv149 := hk) (he151 := hh') .. =>
          refine ⟨hh', ?_⟩
          cases m with
          | recr _ => exact (Value.field.inj hk).symm
          | indc _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
          | defn _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
        | .Recr_other (he157 := he') .. => exact absurd he' tc_field_one_ne_zero
      obtain ⟨hm162, hk⟩ := key
      exact ⟨hh.trans hm162, .inl ⟨⟨m, by simp, hk⟩, he⟩⟩
    | .Cons_other (m162 := m162) (ld12 := ld12) (sg169 := sg) (hne187 := hne) (ev196 := ev') .. =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      have key : m162 = h ∧ mutConstKindF m ≠ kf := by
        match sg with
        | .Indc_n0 (he76 := he') .. => exact absurd he' hne
        | .Indc_other (hv54 := hv) (hne79 := hk) (he84 := hh') .. =>
          refine ⟨hh', ?_⟩
          cases m with
          | indc _ => exact tc_kind_ne hk
          | defn _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
          | recr _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
        | .Defn_n1 (he113 := he') .. => exact absurd he' hne
        | .Defn_other (hv91 := hv) (hne116 := hk) (he121 := hh') .. =>
          refine ⟨hh', ?_⟩
          cases m with
          | defn _ => exact tc_kind_ne hk
          | indc _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
          | recr _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
        | .Recr_n2 (he150 := he') .. => exact absurd he' hne
        | .Recr_other (hv128 := hv) (hne153 := hk) (he158 := hh') .. =>
          refine ⟨hh', ?_⟩
          cases m with
          | recr _ => exact tc_kind_ne hk
          | indc _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
          | defn _ => obtain ⟨_, hv', _⟩ := hm; rw [hv] at hv'; simp at hv'
      obtain ⟨hm162, hmk⟩ := key
      subst hm162
      obtain ⟨hh', hr⟩ := ih hrest ev'
      refine ⟨hh', ?_⟩
      rcases hr with ⟨⟨m₀, hm₀, hk₀⟩, hr1⟩ | ⟨hall, hr0⟩
      · exact .inl ⟨⟨m₀, List.mem_cons_of_mem _ hm₀, hk₀⟩, hr1⟩
      · refine .inr ⟨fun m₁ hm₁ => ?_, hr0⟩
        rcases List.mem_cons.mp hm₁ with rfl | hm₁'
        · exact hmk
        · exact hall m₁ hm₁'

/-! ## `KernelCheck::check_block_member_kinds` -/

private theorem tc_mul_one_one {v : SourceValue F}
    (op : evalBinOp .mul (.field 1 : SourceValue F) (.field 1) = .ok v) (h0 : v = .field 0) :
    False := by
  simp only [evalBinOp, mul_one, Except.ok.injEq] at op
  subst op
  exact tc_field_one_ne_zero h0

/-- **`KernelCheck::check_block_member_kinds` on a block of the run's store**: its members are
all definitions, all inductives or all recursors. -/
theorem check_block_member_kinds_uniform {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {B : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hrec : Ix.Cert.recordAt E₀ B = some c) (hcm : c.info = .muts ms)
    {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : S0.addr h x B)
    (ev : ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    (∀ m ∈ ms.toList, ∃ d, m = .defn d) ∨ (∀ m ∈ ms.toList, ∃ i, m = .indc i) ∨
      (∀ m ∈ ms.toList, ∃ r, m = .recr r) := by
  match Obs.«KernelCheck::check_block_member_kinds».obs ev with
  | .other (ev14 := ev14) (hne405 := hne) (hc413 := hc) .. =>
    obtain ⟨_, raw, c_ld, _, hh, hbl, _, hex, hrep, _⟩ := load_verified_constant_de ha ev14
    have hceq : c_ld = c :=
      hS.record_eq hrec (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh) hbl hex
    subst c_ld
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcm] at hinfo
    obtain ⟨mv, hmv, _⟩ := hinfo
    exact absurd hmv (hne [mv] rfl)
  | .Muts (ev14 := ev14) (ev102 := ev102) (ev151 := ev151) (op144 := op144)
      (heq173 := heq173) (ev187 := ev187) (ev301 := ev301) (op294 := op294)
      (heq323 := heq323) (ev356 := ev356) (ev377 := ev377) (op350 := op350)
      (heq399 := heq399) (hc404 := hc) .. =>
    obtain ⟨_, raw, c_ld, _, hh, hbl, _, hex, hrep, _⟩ := load_verified_constant_de ha ev14
    have hceq : c_ld = c :=
      hS.record_eq hrec (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh) hbl hex
    subst c_ld
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcm] at hinfo
    obtain ⟨mv, hmv, hms_rep⟩ := hinfo
    injection hmv with _ _ hmv_args
    simp only [List.cons.injEq, and_true] at hmv_args
    subst hmv_args
    obtain ⟨rfl, hk1⟩ := muts_has_kind_spec 1 ms.toList hms_rep ev102
    obtain ⟨rfl, hk0⟩ := muts_has_kind_spec 0 ms.toList hms_rep ev151
    have hrep' := Aiur.Library.List.repList_heapMono₂ _ Claim.repMutConst_heapMono₂
      ev187.heap_extends hms_rep
    obtain ⟨rfl, hk2⟩ := muts_has_kind_spec 2 ms.toList hrep' ev301
    obtain ⟨rfl, hk0'⟩ := muts_has_kind_spec 0 ms.toList hrep' ev356
    obtain ⟨rfl, hk2'⟩ := muts_has_kind_spec 2 ms.toList hrep' ev377
    have noDI : ¬ ((∃ m ∈ ms.toList, mutConstKindF m = 1) ∧
        ∃ m ∈ ms.toList, mutConstKindF m = 0) := by
      rintro ⟨⟨m, hm, hmk⟩, ⟨m', hm', hmk'⟩⟩
      rcases hk1 with ⟨-, rfl⟩ | ⟨hn, -⟩
      · rcases hk0 with ⟨-, rfl⟩ | ⟨hn', -⟩
        · exact tc_mul_one_one op144 heq173
        · exact hn' m' hm' hmk'
      · exact hn m hm hmk
    have noDR : ¬ ((∃ m ∈ ms.toList, mutConstKindF m = 1) ∧
        ∃ m ∈ ms.toList, mutConstKindF m = 2) := by
      rintro ⟨⟨m, hm, hmk⟩, ⟨m', hm', hmk'⟩⟩
      rcases hk1 with ⟨-, rfl⟩ | ⟨hn, -⟩
      · rcases hk2 with ⟨-, rfl⟩ | ⟨hn', -⟩
        · exact tc_mul_one_one op294 heq323
        · exact hn' m' hm' hmk'
      · exact hn m hm hmk
    have noIR : ¬ ((∃ m ∈ ms.toList, mutConstKindF m = 0) ∧
        ∃ m ∈ ms.toList, mutConstKindF m = 2) := by
      rintro ⟨⟨m, hm, hmk⟩, ⟨m', hm', hmk'⟩⟩
      rcases hk0' with ⟨-, rfl⟩ | ⟨hn, -⟩
      · rcases hk2' with ⟨-, rfl⟩ | ⟨hn', -⟩
        · exact tc_mul_one_one op350 heq399
        · exact hn' m' hm' hmk'
      · exact hn m hm hmk
    by_cases hD : ∃ m ∈ ms.toList, mutConstKindF m = 1
    · refine .inl fun m hm => ?_
      cases m with
      | defn d => exact ⟨d, rfl⟩
      | indc i => exact (noDI ⟨hD, .indc i, hm, rfl⟩).elim
      | recr r => exact (noDR ⟨hD, .recr r, hm, rfl⟩).elim
    · by_cases hI : ∃ m ∈ ms.toList, mutConstKindF m = 0
      · refine .inr (.inl fun m hm => ?_)
        cases m with
        | defn d => exact (hD ⟨.defn d, hm, rfl⟩).elim
        | indc i => exact ⟨i, rfl⟩
        | recr r => exact (noIR ⟨hI, .recr r, hm, rfl⟩).elim
      · refine .inr (.inr fun m hm => ?_)
        cases m with
        | defn d => exact (hD ⟨.defn d, hm, rfl⟩).elim
        | indc i => exact (hI ⟨.indc i, hm, rfl⟩).elim
        | recr r => exact ⟨r, rfl⟩

/-! ## A projection record's load reaches its block's member-kind check -/

/-- The record a load reads at a projection record's address is the projection record. -/
private theorem tc_loaded_proj_eq {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {info : Ixon.ConstantInfo} (hwf : info.wireWF)
    (hhp : Hashed calls (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩))
    {raw : ByteArray} {c : Ixon.Constant} (hh : Hashed calls raw)
    (hb : Address.blake3Pure raw = Core.projAddr info)
    (hde : Ixon.deConstantExact raw = .ok c) :
    c = ⟨info, #[], #[], #[], #[]⟩ := by
  have hraw : raw = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ :=
    hS.hashed_inj hh hhp (hb.trans rfl)
  subst hraw
  have hrt := Ixon.Verify.deConstantExact_serConstant _ (L1.emptyTablesConstant_wireWF.mpr hwf)
  exact Except.ok.inj (hde.symm.trans hrt)

/-- **`get_ci` at a definition member's projection record** runs the member-kind check of the
block. -/
private theorem tc_get_ci_dprj_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {i : UInt64} {B : _root_.Address} (hB : B.hash.size = 32)
    (hhp : Hashed calls (Ixon.serConstant ⟨.dPrj ⟨i, B⟩, #[], #[], #[], #[]⟩))
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : S0.addr h ap (Core.projAddr (.dPrj ⟨i, B⟩)))
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      S0.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  have hid : ∀ (raw : ByteArray) (c' : Ixon.Constant), Hashed calls raw →
      Address.blake3Pure raw = Core.projAddr (.dPrj ⟨i, B⟩) →
      Ixon.deConstantExact raw = .ok c' → c' = ⟨.dPrj ⟨i, B⟩, #[], #[], #[], #[]⟩ :=
    fun raw c' hh hb hd =>
      tc_loaded_proj_eq hS (info := .dPrj ⟨i, B⟩) (show (Ixon.ConstantInfo.dPrj ⟨i, B⟩).wireWF from hB)
        hhp hh hb hd
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.dPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad
  | .DPrj (m2 := m2) (cs12 := cs12) (x_block_addr := x_block_addr) (cs648 := cs648)
      (ev14 := ev14) (ev650 := ev650) (hc675 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.dPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
    injection hpv with _ _ hpv_args
    simp only [List.cons.injEq, and_true] at hpv_args
    rw [← hpv_args] at hdp
    injection hdp with _ _ hdp_args
    simp only [List.cons.injEq, and_true] at hdp_args
    rcases hdp_args with ⟨_, hblk_eq⟩
    rw [← hblk_eq] at hblk_addr
    match Obs.«Ingress::get_ci_dprj».obs ev650 with
    | .run (v1 := v1) (m2 := m2') (cs12 := cs12') (ev14 := ev_mk) (hc348 := hc348) .. =>
      refine ⟨x_block_addr, v1, m2, m2', cs12', hblk_addr, ev_mk, fun cl hcl => ?_⟩
      have h1 : cl ∈ cs648 := by rw [hc348]; simp [hcl]
      exact hsub cl (by rw [hc]; simp [h1])

/-- **`get_ci` at an inductive member's projection record, then `check_const`**, runs the
member-kind check of the block (`check_const`'s `Induct` arm). -/
private theorem tc_get_ci_iprj_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {i : UInt64} {B : _root_.Address} (hB : B.hash.size = 32)
    (hhp : Hashed calls (Ixon.serConstant ⟨.iPrj ⟨i, B⟩, #[], #[], #[], #[]⟩))
    {ap ptr v rc r_chk : SourceValue F} {h h' h'' : Heap F} {cs cs_chk : List (Call F)}
    (ha : S0.addr h ap (Core.projAddr (.iPrj ⟨i, B⟩)))
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok v)
    (ev_chk : ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] h' r_chk h'' cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      S0.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  have hid : ∀ (raw : ByteArray) (c' : Ixon.Constant), Hashed calls raw →
      Address.blake3Pure raw = Core.projAddr (.iPrj ⟨i, B⟩) →
      Ixon.deConstantExact raw = .ok c' → c' = ⟨.iPrj ⟨i, B⟩, #[], #[], #[], #[]⟩ :=
    fun raw c' hh hb hd =>
      tc_loaded_proj_eq hS (info := .iPrj ⟨i, B⟩) (show (Ixon.ConstantInfo.iPrj ⟨i, B⟩).wireWF from hB)
        hhp hh hb hd
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.iPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad
  | .IPrj (m2 := m2) (cs12 := cs12) (x_block_addr := x_block_addr) (ev14 := ev14)
      (ev741 := ev741) (ev720 := ev720) (hc750 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.iPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
    injection hpv with _ _ hpv_args
    simp only [List.cons.injEq, and_true] at hpv_args
    rw [← hpv_args] at hdp
    injection hdp with _ _ hdp_args
    simp only [List.cons.injEq, and_true] at hdp_args
    rcases hdp_args with ⟨_, hblk_eq⟩
    rw [← hblk_eq] at hblk_addr
    have ext_m2 : Heap.Extends m2 h' := ev741.heap_extends.trans ev720.heap_extends
    match Obs.«Ingress::get_ci_iprj».obs ev720 with
    | .run (v166 := v166) (m167 := m167) (he170 := he170) (hm169 := hm169) (ev176 := ev176) .. =>
      match Obs.«Convert::convert_inductive».obs ev176 with
      | .run (he128 := he128) .. =>
        rw [he170, hm169, L1.loadValue_snoc] at hld
        have hv : v166 = v := Except.ok.inj hld
        subst hv
        subst he128
        match Obs.«KernelCheck::check_const».obs ev_chk with
        | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
        | .Axiom_other_other (hv37 := hv) ..
        | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
        | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
        | .Ctor_n0_n0 (hv1941 := hv) .. | .Ctor_n0_other (hv1941 := hv) ..
        | .Ctor_other_n0 (hv1941 := hv) ..
        | .Ctor_other_other (hv1941 := hv) ..
        | .Rec_n0 (hv2631 := hv) .. | .Rec_other (hv2631 := hv) .. =>
          injection hv with _ htag _
          exact absurd htag (by decide)
        | .Induct_n0 (x_ind_block := xblk) (m1283 := m1283) (m1333 := m1333)
            (m1354 := m1354) (m1376 := m1376)
            (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
            (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
            (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
            (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
            (ev1482 := ev_mk) (hc1634 := hc') ..
        | .Induct_other_n0 (x_ind_block := xblk) (m1283 := m1283) (m1333 := m1333)
            (m1354 := m1354) (m1376 := m1376)
            (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
            (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
            (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
            (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
            (ev1482 := ev_mk) (hc1926 := hc') ..
        | .Induct_other_other (x_ind_block := xblk) (m1283 := m1283) (m1333 := m1333)
            (m1354 := m1354) (m1376 := m1376)
            (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
            (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
            (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
            (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
            (ev1482 := ev_mk) (hc1935 := hc') .. =>
          injection hv_ind with _ _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with hblk _
          subst hblk
          have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc _ _
          have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc _ _
          have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc _ _
          have hext : Heap.Extends h' m1440 :=
            ev1.heap_extends.trans (ev2.heap_extends.trans
              (e_1376.trans (e_1354.trans (ev3.heap_extends.trans
                (e_1427.trans (ev4.heap_extends.trans ev5.heap_extends))))))
          exact ⟨_, r_mk, m1440, m_mk, cs_mk, S0.addr_mono (ext_m2.trans hext) hblk_addr, ev_mk,
            fun cl hcl => hsub_chk cl (by rw [hc']; simp [hcl])⟩

/-- **`get_ci` at a recursor member's projection record, then `check_const`**, runs the
member-kind check of the block (`check_const`'s `Rec` arm). -/
private theorem tc_get_ci_rprj_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {i : UInt64} {B : _root_.Address} (hB : B.hash.size = 32)
    (hhp : Hashed calls (Ixon.serConstant ⟨.rPrj ⟨i, B⟩, #[], #[], #[], #[]⟩))
    {ap ptr v rc r_chk : SourceValue F} {h h' h'' : Heap F} {cs cs_chk : List (Call F)}
    (ha : S0.addr h ap (Core.projAddr (.rPrj ⟨i, B⟩)))
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok v)
    (ev_chk : ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] h' r_chk h'' cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      S0.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  have hid : ∀ (raw : ByteArray) (c' : Ixon.Constant), Hashed calls raw →
      Address.blake3Pure raw = Core.projAddr (.rPrj ⟨i, B⟩) →
      Ixon.deConstantExact raw = .ok c' → c' = ⟨.rPrj ⟨i, B⟩, #[], #[], #[], #[]⟩ :=
    fun raw c' hh hb hd =>
      tc_loaded_proj_eq hS (info := .rPrj ⟨i, B⟩) (show (Ixon.ConstantInfo.rPrj ⟨i, B⟩).wireWF from hB)
        hhp hh hb hd
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hc) ..
  | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.rPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad
  | .RPrj (m2 := m2) (cs12 := cs12) (x_block_addr := x_block_addr) (ev14 := ev14)
      (ev917 := ev917) (ev896 := ev896) (hc926 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hcx := hid raw c_x
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst hcx
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo_r
    change Claim.RepConstantInfo _ (.rPrj ⟨i, B⟩) _ at hinfo_r
    obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
    injection hpv with _ _ hpv_args
    simp only [List.cons.injEq, and_true] at hpv_args
    rw [← hpv_args] at hdp
    injection hdp with _ _ hdp_args
    simp only [List.cons.injEq, and_true] at hdp_args
    rcases hdp_args with ⟨_, hblk_eq⟩
    rw [← hblk_eq] at hblk_addr
    have ext_m2 : Heap.Extends m2 h' := ev917.heap_extends.trans ev896.heap_extends
    match Obs.«Ingress::get_ci_rprj».obs ev896 with
    | .run (v166 := v166) (m167 := m167) (he170 := he170) (hm169 := hm169) (ev176 := ev176) .. =>
      match Obs.«Convert::convert_recursor».obs ev176 with
      | .run (he237 := he237) .. =>
        rw [he170, hm169, L1.loadValue_snoc] at hld
        have hv : v166 = v := Except.ok.inj hld
        subst hv
        subst he237
        match Obs.«KernelCheck::check_const».obs ev_chk with
        | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
        | .Axiom_other_other (hv37 := hv) ..
        | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
        | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
        | .Induct_n0 (hv1240 := hv) .. | .Induct_other_n0 (hv1240 := hv) ..
        | .Induct_other_other (hv1240 := hv) ..
        | .Ctor_n0_n0 (hv1941 := hv) .. | .Ctor_n0_other (hv1941 := hv) ..
        | .Ctor_other_n0 (hv1941 := hv) ..
        | .Ctor_other_other (hv1941 := hv) .. =>
          injection hv with _ htag _
          exact absurd htag (by decide)
        | .Rec_n0 (x_rec_block := xblk) (m2693 := m2637) (m2761 := m2705) (m2804 := m2718)
            (v2833 := r_mk) (m2834 := m_mk) (cs2844 := cs_mk)
            (ev14 := ev1) (hv2631 := hv_rec) (ev2705 := ev2)
            (hm2769 := hm2705) (ev2742 := ev3) (ev2786 := ev4) (ev2816 := ev_rules)
            (ev2846 := ev_mk) (hc2997 := hc') ..
        | .Rec_other (x_rec_block := xblk) (m2693 := m2637) (m2761 := m2705) (m2804 := m2718)
            (v2833 := r_mk) (m2834 := m_mk) (cs2844 := cs_mk)
            (ev14 := ev1) (hv2631 := hv_rec) (ev2705 := ev2)
            (hm2769 := hm2705) (ev2742 := ev3) (ev2786 := ev4) (ev2816 := ev_rules)
            (ev2846 := ev_mk) (hc3086 := hc') .. =>
          injection hv_rec with _ _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with _ hargs
          injection hargs with _ hargs; injection hargs with hblk _
          subst hblk
          have e_2705 : Heap.Extends m2637 m2705 := by rw [hm2705]; exact Heap.Extends.snoc _ _
          have hext : Heap.Extends h' m2718 :=
            ev1.heap_extends.trans (ev2.heap_extends.trans
              (e_2705.trans (ev3.heap_extends.trans (ev4.heap_extends.trans
                ev_rules.heap_extends))))
          exact ⟨_, r_mk, m2718, m_mk, cs_mk, S0.addr_mono (ext_m2.trans hext) hblk_addr, ev_mk,
            fun cl hcl => hsub_chk cl (by rw [hc']; simp [hcl])⟩

/-- **The check of member `0` of a block runs the block's member-kind check.** -/
private theorem tc_member_zero_kinds {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {bAddr B : _root_.Address} {t : Ix.Kernel.RoleTable} {ms : Array Ixon.MutConst}
    {lim : Option Nat} (hm : MemberCheckedLimAt calls bAddr t B ms 0 lim) :
    ∃ (x r : SourceValue F) (h₁ h₂ : Heap F) (cs₁ : List (Call F)),
      S0.addr h₁ x B ∧ ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x] h₁ r h₂ cs₁ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hm
  obtain ⟨b, hb, rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a, -, ra, hixa, hhp⟩ := L1.projection_addr_hashed_spec hmem hb ev_pa
  have hhp' := hashed_mono hsub_pa hhp
  have hB : (Core.ixAddr b).hash.size = 32 := b.size_toArray
  cases mc with
  | defn d =>
    exact tc_get_ci_dprj_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
  | indc ind =>
    exact tc_get_ci_iprj_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
      hld ev_chk hsub_chk
  | recr rcr =>
    exact tc_get_ci_rprj_kinds hS (B := Core.ixAddr b) hB hhp' ⟨a, ra, hixa⟩ ev_ld hsub_ld
      hld ev_chk hsub_chk

/-- **No block record is checked as a constant of its own**: `get_ci` has no `Muts` arm. -/
private theorem tc_get_ci_not_muts {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {B : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hrec : Ix.Cert.recordAt E₀ B = some c) (hcm : c.info = .muts ms)
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : S0.addr h ap B)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    False := by
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) ..
  | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hc) ..
  | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hc) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) ..
  | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hc) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
    obtain ⟨_, raw, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ := load_verified_constant_de ha ev14
    have hceq : c_x = c := hS.record_eq hrec
      (hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_x) hbl_x hex_x
    subst c_x
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcm] at hinfo_r
    obtain ⟨_, hv_bad, _⟩ := hinfo_r
    simp at hv_bad

/-! ## The walk export's blocks -/

/-- **A top-walked block has members of one kind**: all definitions, all inductives or all
recursors (`check_block_member_kinds`, run by the check of the block's first member). At every
limit. -/
theorem TopWalkCore.uniform {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) :
    ∀ B c ms, Top B → recordOf E₀ B = some c → c.info = .muts ms →
      (∀ m ∈ ms.toList, ∃ d, m = .defn d) ∨ (∀ m ∈ ms.toList, ∃ i, m = .indc i) ∨
        (∀ m ∈ ms.toList, ∃ r, m = .recr r) := by
  intro B c ms hT hc hcm
  have hrec : Ix.Cert.recordAt E₀ B = some c :=
    (hW.runStore.recordOf_eq_recordAt B).symm.trans hc
  obtain ⟨c', hc', hchk⟩ := hW.checked B hT
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  rcases hchk with ⟨ms', hms', hk⟩ | hcl
  · rw [hcm] at hms'
    injection hms' with hms_eq
    subst ms'
    by_cases hpos : 0 < ms.size
    · obtain ⟨x, r, h₁, h₂, cs₁, ha, ev, hsub⟩ := tc_member_zero_kinds hW.runStore (hk 0 hpos)
      exact check_block_member_kinds_uniform hW.runStore hrec hcm ha ev hsub
    · refine .inl fun m hm => ?_
      have hlen : 0 < ms.toList.length := List.length_pos_of_mem hm
      rw [Array.length_toList] at hlen
      exact absurd hlen hpos
  · exfalso
    obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
      -, -, ha_pre, -, ev_ld, -, hsub_ld, -, -, -, -⟩ := hcl
    exact tc_get_ci_not_muts hW.runStore hrec hcm ha_pre ev_ld hsub_ld

end IxVM.Refinement.Claim
