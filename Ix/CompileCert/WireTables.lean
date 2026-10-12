import Ix.CompileCert.UniversePipeline
import IxSharingVerify.Builder

/-! Primary table wire validity through actual compiler insertion, including
metadata mode and failures. Count guards concern the resulting table size;
incoming address widths and universe telescope bounds remain explicit. -/

namespace Ix.CompileCert.WireTables

open Ix.CompileM Ix.CompileCert.HeadWriterFrame Ix.CompileCert.Interning
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

theorem internRef_primary (context : CompileEnv × BlockEnv) (state : BlockState) (address : Address)
    (wire : BlockWireTablesWF state) (width : address.hash.size = 32) (ordinary : state.p3MetaMode = false) :
    BlockWireTablesWF (rawRun (internRef address) context state).2 := by
  cases found : state.refsIndex.get? address with
  | some index => rw [internRef_primary_hit address context state ordinary found]; exact wire
  | none =>
    rw [internRef_primary_miss address context state ordinary found]
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

theorem internRefMeta_tables (context : CompileEnv × BlockEnv) (state : BlockState) (address : Address) :
    (rawRun (internRefMeta address) context state).2.refs = state.refs ∧
      (rawRun (internRefMeta address) context state).2.univs = state.univs := by
  cases primary : state.refsIndex.get? address with
  | some index => rw [internRefMeta_primary_hit address context state primary]; exact ⟨rfl, rfl⟩
  | none =>
    cases metadata : state.p3MetaRefsIndex.get? address with
    | some index =>
      rw [internRefMeta_extension_hit address context state primary metadata, checkedTableIndex_state]
      exact ⟨rfl, rfl⟩
    | none =>
      rw [internRefMeta_miss address context state primary metadata]
      split <;> exact ⟨rfl, rfl⟩

theorem internRef_preserves (context : CompileEnv × BlockEnv) (state : BlockState) (address : Address)
    (wire : BlockWireTablesWF state) (width : address.hash.size = 32) :
    BlockWireTablesWF (rawRun (internRef address) context state).2 := by
  cases mode : state.p3MetaMode with
  | false => exact internRef_primary context state address wire width mode
  | true =>
    rw [internRef_meta_run address context state mode]
    have tables := internRefMeta_tables context state address
    exact of_same wire tables.1 tables.2

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

theorem internRef_count_failure (context : CompileEnv × BlockEnv) (state : BlockState) (address : Address)
    (ordinary : state.p3MetaMode = false) (missing : state.refsIndex.get? address = none)
    (full : UInt64.size ≤ state.refs.size + 1) :
    ∃ reason, rawRun (internRef address) context state = (.error (.resourceLimit reason), state) := by
  rw [internRef_primary_miss address context state ordinary missing]
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

theorem blake3_width (bytes : ByteArray) : (Address.blake3 bytes).hash.size = 32 := by
  exact (Blake3.Rust.Hasher.finalizeWithLength
    ((Blake3.Rust.Hasher.init ()).update bytes) 32 Address.digestLen_lt_wordBound).property

theorem internBlake3_preserves (context : CompileEnv × BlockEnv) (state : BlockState) (bytes : ByteArray)
    (wire : BlockWireTablesWF state) :
    BlockWireTablesWF (rawRun (internRef (Address.blake3 bytes)) context state).2 :=
  internRef_preserves context state (Address.blake3 bytes) wire (blake3_width bytes)

end Ix.CompileCert.WireTables
