import Ix.Cert.Stream

/-! # Agreement of canonical decoding with coherent reader caches -/

namespace IxVM.Refinement.Assembly

/-- Canonical byte admission agrees with a cache-coherent store on the participating order.
The store, its closure graph, and its blob selection are unchanged. -/
theorem recordsRead_decodedOf_coherent
    (E : Ixon.Env) {limits : Ix.Kernel.Admission.Limits} :
    ∀ (order : List _root_.Address) {constants : List (_root_.Address × Ixon.Constant)},
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∀ c, Ixon.deConstantExact lc.rawBytes = .ok c → lc.get? = some c) →
      Ix.Kernel.Admission.RecordsRead limits (Ix.Cert.recordsOf E order) constants →
      constants = Ix.Cert.Stream.decodedOf E order
  | [], _, _, hread => by
    change Ix.Kernel.Admission.RecordsRead limits [] _ at hread
    cases hread
    rfl
  | a :: rest, _, hcoherent, hread => by
    rw [Ix.Cert.Stream.recordsOf_cons] at hread
    rw [Ix.Cert.Stream.decodedOf_cons]
    cases hget : E.consts.get? a with
    | none =>
      rw [hget] at hread
      dsimp only [Option.map, Option.toList, List.nil_append] at hread
      have hrec : Ix.Cert.recordAt E a = none := by
        simp only [Ix.Cert.recordAt, hget, Option.bind_none]
      rw [hrec]
      simpa using recordsRead_decodedOf_coherent E rest
        (fun x hx => hcoherent x (List.mem_cons_of_mem a hx)) hread
    | some lc =>
      rw [hget] at hread
      dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append] at hread
      cases hread with
      | cons reads tail =>
        rename_i c tail_constants
        have hdec : Ixon.deConstantExact lc.rawBytes = .ok c := by
          rw [← reads.encoded]
          exact Ixon.Verify.deConstantExact_serConstant c reads.wire
        have hrec : Ix.Cert.recordAt E a = some c := by
          simp only [Ix.Cert.recordAt, hget, Option.bind_some]
          exact hcoherent a List.mem_cons_self lc hget c hdec
        rw [hrec]
        dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append]
        exact congrArg ((a, c) :: ·) (recordsRead_decodedOf_coherent E rest
          (fun x hx => hcoherent x (List.mem_cons_of_mem a hx)) tail)

end IxVM.Refinement.Assembly
