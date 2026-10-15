import Ix.CompileCert.Interning
import Ix.Ixon.Authenticated.Theorems
import IxSharingVerify.BlockTables

/-! # The primary tables stay on the wire

The table interners keep the primary tables representable by the constant
wire format (`Ix.Sharing.Verify.BlockWireTablesWF`, the sharing builder's
table hypothesis), failing runs included. The count guards bound the
resulting table size; an interned address's width and an interned universe's
wire validity are the caller's (`width`, `valid`). An admission-hash address
is 32 bytes (`Ixon.Authenticated.admissionHash_width`). A full table refuses
a new entry with a resource-limit error and no state change. -/

namespace Ix.CompileCert.WireTables

open Ix.CompileM Ix.CompileCert Ix.CompileCert.Interning
open Ix.Sharing.Verify (BlockWireTablesWF)

theorem of_same {before after : BlockState} (wire : BlockWireTablesWF before)
    (refs : after.refs = before.refs) (univs : after.univs = before.univs) : BlockWireTablesWF after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [refs] using wire.refsCount
  · simpa only [refs] using wire.refs
  · simpa only [univs] using wire.univsCount
  · simpa only [univs] using wire.univs

theorem empty (state : BlockState) :
    BlockWireTablesWF { state with refs := #[], univs := #[] } := by
  exact ⟨by change 0 < UInt64.size; decide, by simp,
    by change 0 < UInt64.size; decide, by simp⟩

theorem internRef_preserves (context : CompileEnv × BlockEnv) (state : BlockState) (address : Address)
    (wire : BlockWireTablesWF state) (width : address.hash.size = 32) :
    BlockWireTablesWF (rawRun (internRef address) context state).2 := by
  cases found : state.refsIndex.get? address with
  | some index => rw [internRef_hit address context state found]; exact wire
  | none =>
    rw [internRef_miss address context state found]
    by_cases room : state.refs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      refine ⟨by simpa only [Array.size_push] using room, ?_, wire.univsCount, wire.univs⟩
      intro ref member
      simp only [Array.mem_push] at member
      rcases member with prior | rfl
      · exact wire.refs ref prior
      · exact width
    · simp only [room, ↓reduceIte, checkedTableCount_state]
      exact wire

theorem internUniv_preserves (context : CompileEnv × BlockEnv) (state : BlockState) (univ : Ixon.Univ)
    (wire : BlockWireTablesWF state) (valid : univ.wireWF) :
    BlockWireTablesWF (rawRun (internUniv univ) context state).2 := by
  cases found : state.univsIndex.get? univ with
  | some index => rw [internUniv_hit univ context state found]; exact wire
  | none =>
    rw [internUniv_miss univ context state found]
    by_cases room : state.univs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      refine ⟨wire.refsCount, wire.refs, by simpa only [Array.size_push] using room, ?_⟩
      intro entry member
      simp only [Array.mem_push] at member
      rcases member with prior | rfl
      · exact wire.univs entry prior
      · exact valid
    · simp only [room, ↓reduceIte, checkedTableCount_state]
      exact wire

/-- The extension of original spellings does not touch the primary tables. -/
theorem internMetaUniv_preserves (context : CompileEnv × BlockEnv) (state : BlockState) (univ : Ixon.Univ)
    (wire : BlockWireTablesWF state) :
    BlockWireTablesWF (rawRun (internMetaUniv univ) context state).2 :=
  have tables := internMetaUniv_tables univ context state
  of_same wire tables.1 tables.2.1

theorem internRef_count_failure (context : CompileEnv × BlockEnv) (state : BlockState) (address : Address)
    (missing : state.refsIndex.get? address = none) (full : UInt64.size ≤ state.refs.size + 1) :
    ∃ reason, rawRun (internRef address) context state = (.error (.resourceLimit reason), state) := by
  rw [internRef_miss address context state missing]
  have noRoom : ¬state.refs.size + 1 < UInt64.size := by omega
  simp only [noRoom, ↓reduceIte, checkedTableCount]
  exact ⟨_, rfl⟩

theorem internUniv_count_failure (context : CompileEnv × BlockEnv) (state : BlockState) (univ : Ixon.Univ)
    (missing : state.univsIndex.get? univ = none) (full : UInt64.size ≤ state.univs.size + 1) :
    ∃ reason, rawRun (internUniv univ) context state = (.error (.resourceLimit reason), state) := by
  rw [internUniv_miss univ context state missing]
  have noRoom : ¬state.univs.size + 1 < UInt64.size := by omega
  simp only [noRoom, ↓reduceIte, checkedTableCount]
  exact ⟨_, rfl⟩

/-- Interning a content address keeps the primary tables on the wire. -/
theorem internAdmission_preserves (context : CompileEnv × BlockEnv) (state : BlockState) (bytes : ByteArray)
    (wire : BlockWireTablesWF state) :
    BlockWireTablesWF (rawRun (internRef (Address.admissionHash bytes)) context state).2 :=
  internRef_preserves context state (Address.admissionHash bytes) wire (Ixon.Authenticated.admissionHash_width bytes)

end Ix.CompileCert.WireTables
