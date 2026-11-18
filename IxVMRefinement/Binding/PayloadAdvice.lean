import IxVMRefinement.Binding.AdviceBlockReads
import IxVMRefinement.FamilyGraph.AdviceChecked
import IxVMRefinement.Binding.FamilyAdmits
import IxVMRefinement.Claim.TopProj

/-! # What an advice check and a container check give of their records

`KernelModeled::check_advice_record` loads the record at the advice address
(`Ingress::load_verified_constant`) and has no arm for an axiom or a quotient record. So an advice
record of an observed family check, nested or not, is a record of the run's store
(`adviceIn_record`) and is no axiom or quotient record (`adviceIn_notAxiomLike`).
`KernelModeled::check_container_rec` runs `rec_family_block`, which loads the recursor
(`Ingress::get_ci`) and reads the loaded constant as a `Rec` (`containerRecIn_load`); so a
container recursor is a record of the run's store (`containerRecIn_record`) and no axiom or
quotient record (`containerRecIn_notAxiomLike`). -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option linter.unusedVariables false

section Advice

variable {calls : List (Call F)} {E₀ : Ixon.Env} {bAddr : _root_.Address}
  {t : Ix.Kernel.RoleTable}

/-- **An advice record of an observed family check is a record of the run's store.** -/
theorem adviceIn_record (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {a : _root_.Address} (ha : AdviceIn cs a) : ∃ c, recordOf E₀ a = some c := by
  obtain ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs', ab, hab, rfl, ev, hsub⟩ :=
    adviceCheckObs_of_familyCall hfc ha
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (cs12 := cs12) (ev14 := ev14) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨-, bytes, c, hsz, hh, haddr, hex, hde, -, -, -, -, -, -⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    obtain ⟨lc, hget, -, hlc⟩ := hH ⟨bytes.toArray⟩ c (Core.hashed_mono hsub12 hh)
      (by simpa only [ByteArray.size, List.size_toArray] using hsz) hde hex
    have haddr' : Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr ab := haddr
    refine ⟨c, ?_⟩
    rw [hS.recordOf_eq_recordAt]
    unfold Ix.Cert.recordAt
    rw [← haddr', hget]
    exact hlc

/-- **An advice record of an observed family check is no axiom or quotient record.** -/
theorem adviceIn_notAxiomLike (hS : LoadedReads.RunStore calls E₀) {B rb : _root_.Address}
    {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) {a : _root_.Address}
    (ha : AdviceIn cs a) {c : Ixon.Constant} (hc : recordOf E₀ a = some c) : ¬ IsAxiomLike c := by
  obtain ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs', ab, hab, rfl, ev, hsub⟩ :=
    adviceCheckObs_of_familyCall hfc ha
  obtain ⟨hax, hq⟩ := Decl.adviceRecord_kind hS hab ev hsub hc
  rintro (⟨ax, hi⟩ | ⟨q, hi⟩)
  · exact hax ax hi
  · exact hq q hi

/-- **A container recursor of an observed family check is loaded as a recursor**:
`KernelModeled::check_container_rec` runs `rec_family_block`, whose first step is
`Ingress::get_ci` at the recursor, and which reads the loaded constant as a `Rec`. -/
theorem containerRecIn_load {B rb : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) {x : _root_.Address}
    (hx : ContainerRecIn cs x) :
    ∃ (h h' : Heap F) (ab : Bytes.Address) (ap ptr : SourceValue F) (cs' : List (Call F))
      (args : List (SourceValue F)),
      Bytes.RepAddressRef Core.addrTy h ab ap ∧ Core.ixAddr ab = x ∧
      ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs' ∧ (∀ cl ∈ cs', cl ∈ calls) ∧
      loadValue h' ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec" args) := by
  obtain ⟨h₀, h₀', rc₀, xb, xrb, r₀, -, -, -, ev, -, hsub⟩ := hfc
  obtain ⟨rc, xa, ib, h, hmem, ab, hab, rfl⟩ := hx
  obtain ⟨r₁, h₁', cs₁, ev₁, hcs₁⟩ := ev.calls_observed _ hmem
  match Obs.«KernelModeled::check_container_rec».obs ev₁ with
  | .run (cs37 := cs37) (ev39 := ev39) (hc96 := hc96) .. =>
    match Obs.«KernelModeled::rec_family_block».obs ev39 with
    | .run (cs16 := cs16) (ev18 := ev18) (ld12 := ld12) (hc333 := hc333) .. =>
      exact ⟨h, _, ab, xa, _, cs16, _, hab, rfl, ev18,
        fun cl hcl => hsub cl (hcs₁ cl (by rw [hc96, hc333]; simp [hcl])), ld12⟩

/-- **A container recursor of an observed family check is a record of the run's store.** -/
theorem containerRecIn_record (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {x : _root_.Address} (hx : ContainerRecIn cs x) : ∃ c, recordOf E₀ x = some c := by
  obtain ⟨h, h', ab, ap, ptr, cs', args, hab, rfl, ev, hsub, -⟩ := containerRecIn_load hfc hx
  obtain ⟨rawBytes, c, hsz, hh, hbl, hde, -, -⟩ := Claim.get_ci_head hab ev
  obtain ⟨lc, hget, -, hlc⟩ := hH rawBytes c (Core.hashed_mono hsub hh) hsz
    (L1.deConstant_of_deConstantExact hde) hde
  refine ⟨c, ?_⟩
  rw [hS.recordOf_eq_recordAt]
  unfold Ix.Cert.recordAt
  rw [← hbl, hget]
  exact hlc

/-- **A container recursor of an observed family check is no axiom or quotient record**: its load
reads as a `Rec`, where an axiom record's reads as an `Axiom` and a quotient record's as a
`Quot` (`Claim.GetCIHead`). -/
theorem containerRecIn_notAxiomLike (hS : LoadedReads.RunStore calls E₀) {B rb : _root_.Address}
    {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) {x : _root_.Address}
    (hx : ContainerRecIn cs x) {c : Ixon.Constant} (hc : recordOf E₀ x = some c) :
    ¬ IsAxiomLike c := by
  obtain ⟨h, h', ab, ap, ptr, cs', args, hab, rfl, ev, hsub, hld⟩ := containerRecIn_load hfc hx
  obtain ⟨rawBytes, c', -, hh, hbl, hde, -, hhead⟩ := Claim.get_ci_head hab ev
  have hrecA : Ix.Cert.recordAt E₀ (Core.ixAddr ab) = some c :=
    (hS.recordOf_eq_recordAt _).symm.trans hc
  have e : c' = c := hS.record_eq hrecA (Core.hashed_mono hsub hh) hbl hde
  subst e
  rintro (⟨ax, hi⟩ | ⟨q, hi⟩)
  · obtain ⟨nl, ty, hl⟩ := hhead.axio ax hi
    rw [hld] at hl
    exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)
  · obtain ⟨nl, ty, hl⟩ := hhead.quot q hi
    rw [hld] at hl
    exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)

end Advice

end IxVM.Refinement.Binding
