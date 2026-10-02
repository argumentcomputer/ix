import Ix.Ixon.Verify.MutualConstant

namespace Ixon.Verify

theorem Codec.Reads.runGetExact {decoder : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (h : Codec.Reads decoder bytes value) : Ixon.runGetExact decoder bytes = .ok value := by
  have read := h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at read
  change decoder.run { bytes } = .ok value { idx := bytes.size, bytes } at read
  simp [Ixon.runGetExact, read]

/-- Success exposes the actual decoder result and its final cursor. -/
theorem runGetExact_complete {decoder : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (h : Ixon.runGetExact decoder bytes = .ok value) :
    ∃ state, decoder.run { bytes } = .ok value state ∧ state.idx = bytes.size := by
  unfold Ixon.runGetExact at h
  cases read : decoder.run { bytes } with
  | error reason state => simp [read] at h
  | ok output state =>
    by_cases consumed : state.idx = bytes.size
    · simp [read, consumed] at h
      subst output
      exact ⟨state, rfl, consumed⟩
    · simp [read, consumed] at h

/-- A proved prefix reading cannot absorb a nonempty suffix in exact mode. -/
theorem Codec.Reads.noTrailing {decoder : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (h : Codec.Reads decoder bytes value) (suffix : ByteArray) (nonempty : suffix.size ≠ 0) :
    (Ixon.runGetExact decoder (bytes ++ suffix)).isOk = false := by
  have read := h ByteArray.empty suffix
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at read
  change decoder.run { bytes := bytes ++ suffix } =
    .ok value { idx := bytes.size, bytes := bytes ++ suffix } at read
  have trailing : bytes.size ≠ (bytes ++ suffix).size := by
    simp only [ByteArray.size_append]
    omega
  simp only [Ixon.runGetExact, read, ite_eq_right trailing]
  rfl

/-- All constant variants and side tables retain the existing wire domain;
the strengthened entry point also checks whole-buffer consumption. -/
theorem deConstantExact_serConstant (constant : Ixon.Constant) (h : constant.wireWF) :
    Ixon.deConstantExact (Ixon.serConstant constant) = .ok constant := by
  have valid := Codec.MutualConstant.constantWireWF_of_catalog constant h
  unfold Ixon.deConstantExact Ixon.serConstant
  rw [(Codec.MutualConstant.putConstant_writes constant valid).runPut]
  exact (Codec.MutualConstant.getConstant_reads constant valid).runGetExact

theorem deConstantExact_noTrailing (constant : Ixon.Constant) (h : constant.wireWF)
    (suffix : ByteArray) (nonempty : suffix.size ≠ 0) :
    (Ixon.deConstantExact (Ixon.serConstant constant ++ suffix)).isOk = false := by
  have valid := Codec.MutualConstant.constantWireWF_of_catalog constant h
  unfold Ixon.deConstantExact Ixon.serConstant
  rw [(Codec.MutualConstant.putConstant_writes constant valid).runPut]
  exact (Codec.MutualConstant.getConstant_reads constant valid).noTrailing suffix nonempty

end Ixon.Verify
