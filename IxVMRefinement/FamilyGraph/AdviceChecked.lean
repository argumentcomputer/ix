import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Assembly.FamilyAdviceWalk
import IxVMRefinement.Assembly.TypingSkeleton
import IxVMRefinement.L1.Decode
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled2

/-! # The checks a family check runs on its advice records

`check_family` runs `check_advice_records(rc, advice, Nil, wset)` under its own role context
`rc`: each listed record is checked by `check_advice_record`, which runs the record's own check
(`KernelClaim::run_check(rc, a)` for a definition, a theorem or a recursor record;
`check_muts_all` for a block) and then compares the record's used references with the earlier
advice and the witnessed references. This module reads that the record's own check ran, at the
limit of the family check's role context:

* `adviceRecord_checked`: an observed `check_advice_record` at a record that declares one
  constant is the check of that record (`Claim.CheckedLimAt`) at the limit of the role context it
  was called with. The record is the run store's: the arm of the loaded value is the arm of the
  stored record. A definition takes the arm of a safe definition or of a theorem, a recursor the
  recursor arm; an axiom or a quotient record has no arm, so the check does not return.
* `check_advice_records_obs`: every listed address had its `check_advice_record` observed, at
  an extension of the walk's heap, with its calls among the walk's.
* `adviceRecords_checked`: so every listed record that declares one constant was checked at the
  limit of the walk's role context.

This is the `checked` field of what a step reads of the run about a unit checked inside a family
check, for an advice definition, theorem or recursor. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Library.List Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **An observed advice-record check at a record that declares one constant ran the record's
own check**, at the limit of the role context it was called with (module docstring). -/
theorem adviceRecord_checked {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {ab : Bytes.Address}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (ha : Bytes.RepAddressRef addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c)
    (hst : Typing.Standalone c) :
    Claim.CheckedLimAt calls bAddr t (ixAddr ab) lim := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947) (ev14 := ev14)
      (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have hsub947 : ∀ cl ∈ cs947, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨ext1, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    have hrec₀ : Ix.Cert.recordAt E₀ (ixAddr ab) = some c :=
      (hS.recordOf_eq_recordAt _).symm.trans hc
    have hcc : c' = c := hS.record_eq hrec₀ (hashed_mono hsub12 hh) haddr hexact
    rw [hcc] at cRep
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq : x_info = infoVal := by
      have h1 := (Value.construct.inj hc_eq).2.2
      exact (List.cons.inj h1).1
    rw [← hinfo_eq] at hinfoRep
    -- the arm of the loaded value is the arm of the stored record
    have htagOf : ∀ (tag : String) (args : List (SourceValue F)),
        x_info = .construct "Ixon::ConstantInfo" tag args →
        tag = "Defn" ∨ tag = "Recr" ∨ tag = "Axio" ∨ tag = "Quot" := by
      intro tag args hx
      rcases hst with ⟨d, hd⟩ | ⟨rc, hr⟩ | ⟨ax, hax⟩ | ⟨q, hq⟩
      · rw [hd] at hinfoRep
        obtain ⟨dv, hv, -⟩ := hinfoRep
        rw [hx] at hv
        exact Or.inl (Value.construct.inj hv).2.1
      · rw [hr] at hinfoRep
        obtain ⟨rv, hv, -⟩ := hinfoRep
        rw [hx] at hv
        exact Or.inr (Or.inl (Value.construct.inj hv).2.1)
      · rw [hax] at hinfoRep
        obtain ⟨av, hv, -⟩ := hinfoRep
        rw [hx] at hv
        exact Or.inr (Or.inr (Or.inl (Value.construct.inj hv).2.1))
      · rw [hq] at hinfoRep
        obtain ⟨qv, hv, -⟩ := hinfoRep
        rw [hx] at hv
        exact Or.inr (Or.inr (Or.inr (Value.construct.inj hv).2.1))
    have hrc2 : Claim.RCLimRep t bAddr lim m2 x_rc := hrc.mono ext1
    have ha2 : S0.addr m2 x_a (ixAddr ab) :=
      ⟨ab, Bytes.repAddressRef_heapMono₂ addrTy ext1 ha, rfl⟩
    match sg952 with
    | .Defn_Definition_Safe (ev210 := evr) (hc227 := hcs) .. =>
      exact (Claim.run_check_lim_spec hrc2 ha2 evr).2.mono
        (fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl]))
    | .Defn_Definition_other (heq258 := heq) .. =>
      exact absurd (Value.field.inj heq) zero_ne_one
    | .Defn_Theorem (ev321 := evr) (hc338 := hcs) .. =>
      exact (Claim.run_check_lim_spec hrc2 ha2 evr).2.mono
        (fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl]))
    | .Defn_Opaque (heq372 := heq) .. =>
      exact absurd (Value.field.inj heq) zero_ne_one
    | .Recr (ev553 := evf) (ev540 := evm) (ev574 := evr) (hc591 := hcs) .. =>
      have ext : Heap.Extends m2 _ := evf.heap_extends.trans evm.heap_extends
      exact (Claim.run_check_lim_spec (hrc2.mono ext) (S0.addr_mono ext ha2) evr).2.mono
        (fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl]))
    | .Muts (hv598 := hv) .. =>
      rcases htagOf _ _ hv with e | e | e | e <;> exact absurd e (by decide)
    | .IPrj (hv790 := hv) .. =>
      rcases htagOf _ _ hv with e | e | e | e <;> exact absurd e (by decide)
    | .CPrj (hv869 := hv) .. =>
      rcases htagOf _ _ hv with e | e | e | e <;> exact absurd e (by decide)

/-- **An observed advice-record check is at no axiom and no quotient record**: the check's arms
are a definition's, a recursor's, a block's and an inductive or constructor projection's, and the
arm of the loaded value is the arm of the stored record. -/
theorem adviceRecord_kind {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {ab : Bytes.Address}
    (ha : Bytes.RepAddressRef addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c) :
    (∀ ax, c.info ≠ .axio ax) ∧ ∀ q, c.info ≠ .quot q := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947) (ev14 := ev14)
      (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨ext1, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded ha ev14
    have hrec₀ : Ix.Cert.recordAt E₀ (ixAddr ab) = some c :=
      (hS.recordOf_eq_recordAt _).symm.trans hc
    have hcc : c' = c := hS.record_eq hrec₀ (hashed_mono hsub12 hh) haddr hexact
    rw [hcc] at cRep
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq : x_info = infoVal := by
      have h1 := (Value.construct.inj hc_eq).2.2
      exact (List.cons.inj h1).1
    rw [← hinfo_eq] at hinfoRep
    -- the check's arm names the tag of the loaded value, which is neither `Axio` nor `Quot`
    have harm : ∀ (tag : String) (args : List (SourceValue F)),
        x_info = .construct "Ixon::ConstantInfo" tag args → tag ≠ "Axio" ∧ tag ≠ "Quot" := by
      intro tag args hx
      match sg952 with
      | .Defn_Definition_Safe (hv81 := hv) .. | .Defn_Definition_other (hv81 := hv) ..
      | .Defn_Theorem (hv81 := hv) .. | .Defn_Opaque (hv81 := hv) .. | .Recr (hv403 := hv) ..
      | .Muts (hv598 := hv) .. | .IPrj (hv790 := hv) .. | .CPrj (hv869 := hv) .. =>
        have e := (Value.construct.inj (hx.symm.trans hv)).2.1
        subst e
        exact ⟨by decide, by decide⟩
    refine ⟨fun ax hax => ?_, fun q hq => ?_⟩
    · rw [hax] at hinfoRep
      obtain ⟨av, hv, -⟩ := hinfoRep
      exact (harm _ _ hv).1 rfl
    · rw [hq] at hinfoRep
      obtain ⟨qv, hv, -⟩ := hinfoRep
      exact (harm _ _ hv).2 rfl

/-- **Every listed advice address had its advice-record check observed**, at an extension of
the walk's heap where the address is still read, with its calls among the walk's. -/
theorem check_advice_records_obs {rc wset : SourceValue F} :
    ∀ (advAs : List Bytes.Address) {x_advice x_seen r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs x_advice →
      ObsFn W "KernelModeled::check_advice_records" [rc, x_advice, x_seen, wset] h r h' cs →
      ∀ b ∈ advAs, ∃ (x_a seen r₁ : SourceValue F) (h₁ h₁' : Heap F) (cs₁ : List (Call F)),
        Heap.Extends h h₁ ∧ Bytes.RepAddressRef addrTy h₁ b x_a ∧
        ObsFn W "KernelModeled::check_advice_record" [rc, x_a, seen, wset] h₁ r₁ h₁' cs₁ ∧
        (∀ cl ∈ cs₁, cl ∈ cs)
  | [], _, _, _, _, _, _, _, _ => fun b hb => nomatch hb
  | a :: rest, x_advice, x_seen, r, h, h', cs, hadv_rep, ev => by
    cases Obs.«KernelModeled::check_advice_records».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hadv_rep ld12
    | Cons x_a x_rest v52 m55 cs63 v89 m90 cs100 cs138 v143 m160 cs168
        ld12 ev65 heq88 ev102 ev170 ev140 hc201 =>
      obtain ⟨a', rest', heq_cons, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hadv_rep ld12
      injection heq_cons with ha_eq hrest_eq
      subst ha_eq hrest_eq
      have ext_55 : Heap.Extends h m55 := ObsFn.heap_extends ev65
      have ext_160 : Heap.Extends h m160 :=
        ext_55.trans ((ObsFn.heap_extends ev102).trans (ObsFn.heap_extends ev170))
      have hrec := check_advice_records_obs rest
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_160 hrest_rep) ev140
      intro b hb
      rcases List.mem_cons.mp hb with hba | hrm
      · rw [hba]
        exact ⟨x_a, x_seen, v89, m55, m90, cs100, ext_55,
          Bytes.repAddressRef_heapMono₂ addrTy ext_55 ha_rep, ev102,
          fun cl hcl => by rw [hc201]; simp [hcl]⟩
      · obtain ⟨xa', seen', r₁, h₁, h₁', cs₁, e₁, hrep₁, ev₁, hsub₁⟩ := hrec b hrm
        exact ⟨xa', seen', r₁, h₁, h₁', cs₁, ext_160.trans e₁, hrep₁, ev₁,
          fun cl hcl => by rw [hc201]; simp [hsub₁ cl hcl]⟩

/-- **The advice walk checked every listed record that declares one constant**, at the limit of
the role context the walk was called with: the family check's. -/
theorem adviceRecords_checked {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {rc wset x_advice x_seen r : SourceValue F} {h h' : Heap F} {advAs : List Bytes.Address}
    (hrc : Claim.RCLimRep t bAddr lim h rc)
    (hadv : RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs x_advice)
    (ev : ObsFn W "KernelModeled::check_advice_records" [rc, x_advice, x_seen, wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ b ∈ advAs, ∀ c : Ixon.Constant, IxVM.Consistency.recordOf E₀ (ixAddr b) = some c →
      Typing.Standalone c → Claim.CheckedLimAt calls bAddr t (ixAddr b) lim := by
  intro b hb c hc hst
  obtain ⟨x_a, seen, r₁, h₁, h₁', cs₁, e₁, hrep₁, ev₁, hsub₁⟩ :=
    check_advice_records_obs advAs hadv ev b hb
  exact adviceRecord_checked hS (hrc.mono e₁) hrep₁ ev₁ (fun cl hcl => hsub cl (hsub₁ cl hcl))
    hc hst

end IxVM.Refinement.Decl
