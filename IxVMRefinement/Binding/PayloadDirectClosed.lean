import IxVMRefinement.Binding.PayloadDirectLoads
import IxVM.Obs.Convert
import IxVM.Obs.Ingress
import IxVM.Obs.KernelModeled

/-! # Closing the direct payload facts: advice projection members and container recursor logic

Two remaining fields of `PayloadDirectLeft`:

* **`adviceCheck_projMember`**: `KernelModeled::check_advice_record`'s `IPrj` and `CPrj` arms
  call `Ingress::get_ci` on the advice record, so `Claim.proj_member_of_load` gives the owner
  block and `ConstAddrOf`.
* **`containerRecIn_logic`**: `KernelModeled::check_container_rec` calls `Ingress::get_ci` on the
  container recursor, matches the loaded constant as `KConstantInfo::Rec`, and asserts its unsafe
  flag `0`. A standalone recursor is therefore safe (so `InLogic`); any projection record is
  `InLogic` by definition; definitions, axioms, quotients and blocks cannot load as `Rec`. -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

section DirectClosed

variable {calls : List (Call F)} {E₀ : Ixon.Env} {bAddr : _root_.Address}
  {t : Ix.Kernel.RoleTable}

private theorem rec_flag_eq_direct
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ u a₁₀ a₁₁ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ u' b₁₀ b₁₁ : SourceValue F}
    (h : (.construct "KernelTypes::KConstantInfo" "Rec"
        [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, u, a₁₀, a₁₁] : SourceValue F) =
      .construct "KernelTypes::KConstantInfo" "Rec"
        [b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, u', b₁₀, b₁₁]) :
    u = u' := by
  have e := (Value.construct.inj h).2.2
  have e1 := (List.cons.inj e).2
  have e2 := (List.cons.inj e1).2
  have e3 := (List.cons.inj e2).2
  have e4 := (List.cons.inj e3).2
  have e5 := (List.cons.inj e4).2
  have e6 := (List.cons.inj e5).2
  have e7 := (List.cons.inj e6).2
  have e8 := (List.cons.inj e7).2
  exact (List.cons.inj e8).1

/-- **`Convert::convert_definition` never returns a `KConstantInfo::Rec` value.** -/
private theorem convert_definition_not_rec {x_d x_sh x_rf x_ra x_un x_ht x_tb x_bs : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {args : List (SourceValue F)}
    (ev : ObsFn Obs.W "Convert::convert_definition"
      [x_d, x_sh, x_rf, x_ra, x_un, x_ht, x_tb, x_bs] h
      (.construct "KernelTypes::KConstantInfo" "Rec" args) h' cs) : False := by
  match Obs.«Convert::convert_definition».obs ev with
  | .Definition (he242 := he) .. =>
    exact absurd (Value.construct.inj he).2.1 (by decide)
  | .Opaque (he329 := he) .. =>
    exact absurd (Value.construct.inj he).2.1 (by decide)
  | .Theorem (he373 := he) .. =>
    exact absurd (Value.construct.inj he).2.1 (by decide)

/-- **A record whose `Ingress::get_ci` load reads as `KConstantInfo::Rec` is no standalone
definition.** -/
private theorem get_ci_rec_not_defn (hS : LoadedReads.RunStore calls E₀)
    {ab : Bytes.Address} {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hab : Bytes.RepAddressRef Core.addrTy h ab ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {args : List (SourceValue F)}
    (hld : loadValue h' ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec" args))
    {c : Ixon.Constant} {d : Ixon.Definition}
    (hc : recordOf E₀ (Core.ixAddr ab) = some c) (hinfo : c.info = .defn d) : False := by
  have htag : ∀ {tag : String} {iargs : List (SourceValue F)} {x_sh x_rf x_un x_bd : SourceValue F}
      {m : Heap F} {cs12 : List (Call F)},
      ObsFn Obs.W "Ingress::load_verified_constant" [ap] h
        (.construct "Ixon::Constant" "Mk"
          [.construct "Ixon::ConstantInfo" tag iargs, x_sh, x_rf, x_un, x_bd]) m cs12 →
      (∀ cl ∈ cs12, cl ∈ calls) → tag = "Defn" := by
    intro tag iargs x_sh x_rf x_un x_bd m cs12 ev14 hsub12
    obtain ⟨-, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      Ingress.load_verified_constant_decode_bounded hab ev14
    have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
      (Core.hashed_mono hsub12 hh) haddr hexact
    subst c'
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [hinfo] at hinfoRep
    obtain ⟨dv, hv, -⟩ := hinfoRep
    exact (Value.construct.inj (hinfo_eq.trans hv)).2.1
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (v215 := v215) (m216 := m216) (he219 := he) (hm218 := hm) (ev225 := evc) .. =>
    rw [he, hm, Claim.loadValue_snoc_self m216 v215] at hld
    have hv : v215 = .construct "KernelTypes::KConstantInfo" "Rec" args := Except.ok.inj hld
    subst hv
    exact convert_definition_not_rec evc
  | .Defn_other (v336 := v336) (m337 := m337) (he340 := he) (hm339 := hm) (ev346 := evc) .. =>
    rw [he, hm, Claim.loadValue_snoc_self m337 v336] at hld
    have hv : v336 = .construct "KernelTypes::KConstantInfo" "Rec" args := Except.ok.inj hld
    subst hv
    exact convert_definition_not_rec evc
  | .Axio (ev14 := ev14) (hc515 := hcs) .. | .Quot (ev14 := ev14) (hc606 := hcs) ..
  | .DPrj (ev14 := ev14) (hc675 := hcs) .. | .IPrj (ev14 := ev14) (hc750 := hcs) ..
  | .CPrj (ev14 := ev14) (hc851 := hcs) .. | .RPrj (ev14 := ev14) (hc926 := hcs) ..
  | .Recr (ev14 := ev14) (hc1071 := hcs) .. =>
    exact absurd (htag ev14 (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))) (by decide)

/-- **An advice record that is a projection record is at a member's or a constructor's address of
its block**, which the store holds: `KernelModeled::check_advice_record`'s `IPrj` and `CPrj` arms
call `Ingress::get_ci` at the record (`Claim.proj_member_of_load`). -/
theorem adviceCheck_projMember (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {a : _root_.Address}
    (hadv : AdviceCheckObs calls a) {c : Ixon.Constant} (hc : recordOf E₀ a = some c)
    (hp : IsProj c) :
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
  obtain ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs, ab, hab, rfl, ev, hsub⟩ := hadv
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947)
      (ev_yqjbwijz := ev_ord) (ev14 := ev14) (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have hsub947 : ∀ cl ∈ cs947, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have ext_m2 : Heap.Extends h m2 := ev_ord.heap_extends.trans ev14.heap_extends
    obtain ⟨-, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      Ingress.load_verified_constant_decode_bounded
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ord.heap_extends hab) ev14
    have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
      (Core.hashed_mono hsub12 hh) haddr hexact
    subst c'
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq : x_info = infoVal := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← hinfo_eq] at hinfoRep
    match sg952 with
    | .Defn_Definition_Safe (hv81 := hv) .. | .Defn_Definition_other (hv81 := hv) ..
    | .Defn_Theorem (hv81 := hv) .. | .Defn_Opaque (hv81 := hv) .. =>
      rw [hv] at hinfoRep
      obtain ⟨d, hd, -⟩ := Ingress.repConstantInfo_defn_inv hinfoRep
      exact (standalone_not_proj (Or.inl ⟨d, hd⟩) hp).elim
    | .Recr (hv403 := hv) .. =>
      rw [hv] at hinfoRep
      obtain ⟨rcr, hrc, -⟩ := Ingress.repConstantInfo_recr_inv hinfoRep
      exact (standalone_not_proj (Or.inr (Or.inl ⟨rcr, hrc⟩)) hp).elim
    | .Muts (hv598 := hv) .. =>
      rw [hv] at hinfoRep
      obtain ⟨ms, hms, -⟩ := Ingress.repConstantInfo_muts_inv hinfoRep
      exact (proj_not_block hp ⟨ms, hms⟩).elim
    | .IPrj (cs_sopfkvlz := cs_ci) (ev836 := ev836) (ev822 := ev822)
        (ev_gjbqzffr := ev_ci) (hc863 := hc863) .. =>
      have ext := ext_m2.trans (ev836.heap_extends.trans ev822.heap_extends)
      have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls :=
        fun cl hcl => hsub947 cl (by rw [hc863]; simp [hcl])
      exact Claim.proj_member_of_load hS hH
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext hab) ev_ci hsub_ci hc hp
    | .CPrj (cs_xamhzxrj := cs_ci) (ev915 := ev915) (ev901 := ev901)
        (ev_wwojrrlm := ev_ci) (hc942 := hc942) .. =>
      have ext := ext_m2.trans (ev915.heap_extends.trans ev901.heap_extends)
      have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls :=
        fun cl hcl => hsub947 cl (by rw [hc942]; simp [hcl])
      exact Claim.proj_member_of_load hS hH
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext hab) ev_ci hsub_ci hc hp

/-- **A container recursor of an observed family check is in Lean's logic**:
`KernelModeled::check_container_rec` loads it with `Ingress::get_ci`, matches the value as
`KConstantInfo::Rec`, and asserts its unsafe flag `0`. -/
theorem containerRecIn_logic (hS : LoadedReads.RunStore calls E₀) {B rb : _root_.Address}
    {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) {x : _root_.Address}
    (hx : ContainerRecIn cs x) {c : Ixon.Constant} (hc : recordOf E₀ x = some c) : InLogic c := by
  obtain ⟨h₀, h₀', rc₀, xb, xrb, r₀, -, -, -, ev, -, hsub⟩ := hfc
  obtain ⟨rc, xa, ib, h, hmem, ab, hab, rfl⟩ := hx
  obtain ⟨r₁, h₁', cs₁, ev₁, hcs₁⟩ := ev.calls_observed _ hmem
  match Obs.«KernelModeled::check_container_rec».obs ev₁ with
  | .run (cs_ymrayeri := cs_ci) (ev39 := ev39) (ev25 := ev25) (ev_nqhglzzq := ev_ci)
      (ld_hhcwtoqm := hld) (heq_defmyzfb := huns0) (hc96 := hc96) .. =>
    have ext : Heap.Extends h _ := ev39.heap_extends.trans ev25.heap_extends
    have hab' := Bytes.repAddressRef_heapMono₂ Core.addrTy ext hab
    have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls :=
      fun cl hcl => hsub cl (hcs₁ cl (by rw [hc96]; simp [hcl]))
    rw [huns0] at hld
    obtain ⟨raw, c', -, hh, hba, hde, -, hhead⟩ := Claim.get_ci_head hab' ev_ci
    have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
      (Core.hashed_mono hsub_ci hh) hba hde
    subst c'
    cases hinfo : c.info with
    | recr rcr =>
      obtain ⟨nl', ty', np', ni', nm', nmin', rules', k', x_a, hldv⟩ := hhead.recr rcr hinfo
      have hu := rec_flag_eq_direct (Except.ok.inj (hldv.symm.trans hld))
      simp only [InLogic, hinfo]
      exact Assembly.repBoolField_zero_false hu
    | defn d =>
      exact (get_ci_rec_not_defn hS hab' ev_ci hsub_ci hld hc hinfo).elim
    | axio ax =>
      obtain ⟨nl, ty, hl⟩ := hhead.axio ax hinfo
      rw [hld] at hl
      exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)
    | quot q =>
      simp only [InLogic, hinfo]
    | muts ms =>
      exact (hhead.notMuts ms hinfo).elim
    | dPrj _ => simp only [InLogic, hinfo]
    | iPrj _ => simp only [InLogic, hinfo]
    | cPrj _ => simp only [InLogic, hinfo]
    | rPrj _ => simp only [InLogic, hinfo]

end DirectClosed

end IxVM.Refinement.Binding
