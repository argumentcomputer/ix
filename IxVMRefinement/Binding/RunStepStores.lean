import IxVMRefinement.Assembly.TypingStore
import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Assembly.RawQueryCoverage

/-! # A record store the run's calls are good for, for every store within the run's

Every step of the binding fold reads the circuit's calls against a record store: a store whose
records decode exactly, that holds the witness store's records and blobs and the committed
prelude rows, and for which the run's calls are good (`Typing.StepStore`). The fold's witness
stores are arbitrary stores within the run's store, so the steps ask for such a record store at
each of them.

* `RunStepStores calls t E₀`: **every store within the run's store `E₀` that agrees with the
  committed rows and holds nothing at the zero address has a record store the run's calls are
  good for**, holding the run's records and blobs. The steps of the binding fold take this one
  proposition.
* `runStepStores_of_noCollision`: it holds under the statement's no-collision alternative, at
  any view and any extra byte strings that include the committed footprint: the record store is
  the merged store over the run's (`Typing.merged_exists`), and a collision with a store within
  the run's is a collision among byte strings the run hashed or computed.

* `stepStore_canonicalHashCoverage`: a record store of the run holds, with its exact decoding,
  every record the run hashed (the coverage a block's step asks beside the store), from the
  run store holding them.

It does not follow from a run store alone (`LoadedReads.RunStore`): a run store makes the hash
injective on what the run hashed, and says nothing of the projection images the run computes
without hashing, of the committed rows the run did not load, or of the zero address.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **Every store within the run's store has a record store the run's calls are good for**
(module docstring). -/
def RunStepStores (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop :=
  ∀ R : Ixon.Env,
    (∀ a lr, R.consts.get? a = some lr → E₀.consts.get? a = some lr) →
    (∀ a b, R.blobs.get? a = some b → E₀.blobs.get? a = some b) →
    AgreesCommitted R →
    (R.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      R.blobs.get? Ix.HostAdmission.Merkle.padding = none) →
    ∃ Ec : Ixon.Env, RecordsFor R Ec ∧ StepStore calls t E₀ Ec

/-- **The record stores exist under the no-collision alternative.** -/
theorem runStepStores_of_noCollision {V : View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} (t : Ix.Kernel.RoleTable)
    (hS : LoadedReads.RunStore calls E₀) (hb : Bounded calls)
    (hextra : ∀ x ∈ committedFootprint, x ∈ extra) (hnc : ¬ V.HashedCollision extra calls) :
    RunStepStores calls t E₀ := by
  intro R hcon hblob hcomm hzero
  obtain ⟨E, hM⟩ := merged_exists E₀ R
  -- what the store holds, the run hashed
  have hheld : ∀ (x : _root_.Address) (held : ByteArray),
      ((∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨ R.blobs.get? x = some held) →
        Hashed calls held ∧ Address.blake3Pure held = x := by
    intro x held h
    rcases h with ⟨lc, hl, hraw⟩ | hbl
    · have h1 := hS.loaded.1 x lc (hcon x lc hl)
      rw [hraw] at h1
      exact h1
    · exact hS.loaded.2 x held (hblob x held hbl)
  have hnc' : ¬ CollisionWith V extra R calls := by
    intro hc
    rcases hc with h | ⟨x, held, bytes, hh, hbytes, hne, hx⟩ | ⟨x, held, image, hh, himg, hne, hx⟩
    · exact hnc h
    · exact hnc (Or.inl ⟨x, held, bytes, Or.inr (Or.inr (hheld x held hh)), hbytes, hne, hx⟩)
    · obtain ⟨blk, cb, ms, hblk, hdec, hms, hform⟩ := himg
      exact hnc (Or.inr (Or.inl ⟨x, held, image, blk, cb, ms,
        Or.inr (Or.inr (hheld x held hh)), hblk, hdec, hms, hform, hne, hx⟩))
  have hdec : Ingress.EnvDecoded E₀ := fun a lc h => hS.decoded a lc h
  exact ⟨E, hM.recordsFor hS.loaded hdec hcomm hextra hnc',
    ⟨hM.decoded hdec, fun a c h => hM.run_record hS.loaded hdec hextra hnc' h,
      fun a b h => hM.run_blob hS.loaded hnc' h,
      fun env lim => hM.good hS.loaded hzero hextra hnc' hb env t lim⟩⟩

/-- **A record store of the run holds, with its exact decoding, every record the run hashed.** -/
theorem stepStore_canonicalHashCoverage {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ Ec : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ Ec) :
    Ingress.CanonicalHashCoverage Ec calls := by
  have hcanon₀ : Ingress.CanonicalHashCoverage E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hcov bytes value hashed size
      (Ingress.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  exact Assembly.canonicalHashCoverage_frame hcanon₀ hst.decoded
    (fun a v h => hst.runRecord a v ((hS.recordOf_eq_recordAt a).trans h))

end IxVM.Refinement.Binding
