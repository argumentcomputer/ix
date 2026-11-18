import IxVMRefinement.Binding.AdviceBlockReads
import IxVMRefinement.FamilyGraph.AdviceChecked

/-! # What an advice check gives of its record

`KernelModeled::check_advice_record` loads the record at the advice address
(`Ingress::load_verified_constant`) and has no arm for an axiom or a quotient record. So an advice
record of an observed family check, nested or not, is a record of the run's store
(`adviceIn_record`) and is no axiom or quotient record (`adviceIn_notAxiomLike`). -/

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

end Advice

end IxVM.Refinement.Binding
