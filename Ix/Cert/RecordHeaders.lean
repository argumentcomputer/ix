import Ix.Cert.Statement
import IxC.Ixon.Verify.Framing

/-! # What a record's first TagN says about its kind

A record's canonical bytes (`Ixon.serConstant`) open with the TagN header of its
`ConstantInfo` variant. Read through the production decoder
(`Ixon.Verify.deConstantExact_serConstant`), a block record (`muts`) opens with the
block flag (`blockHeader`), so the readability check of `compileReport`
(`unreadablePublished`, through `blockHeader`) rules out a block at every published
input name's address (`published_not_block`). -/

namespace Ix.Cert.RecordHeaders

open Ixon

/-- The decoder reads a block only under the block flag. -/
theorem info_muts {start finish : GetState} {ms : Array Ixon.MutConst}
    (h : getConstantInfo start = .ok (.muts ms) finish) :
    ∃ tag state, getTagN 4 start = .ok tag state ∧ tag.flag = Constant.FLAG_MUTS := by
  unfold getConstantInfo at h
  obtain ⟨tag, state, ht, h⟩ := ProjectionRead.bind_ok h
  refine ⟨tag, state, ht, ?_⟩
  split at h
  · rename_i flag
    exact beq_iff_eq.mp flag
  · split at h
    · by_cases v0 : tag.value = 0
      · simp only [v0, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v1 : tag.value = 1
      · simp only [v1, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v2 : tag.value = 2
      · simp only [v2, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v3 : tag.value = 3
      · simp only [v3, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v4 : tag.value = 4
      · simp only [v4, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v5 : tag.value = 5
      · simp only [v5, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v6 : tag.value = 6
      · simp only [v6, Functor.map, EStateM.map] at h
        split at h <;> cases h
      by_cases v7 : tag.value = 7
      · simp only [v7, Functor.map, EStateM.map] at h
        split at h <;> cases h
      · simp only at h
        cases h
    · cases h

/-- The canonical decoding of a well-formed record, from the first byte. -/
theorem serConstant_run {c : Constant} (wire : c.wireWF) :
    ∃ state, getConstant { bytes := serConstant c } = .ok c state := by
  obtain ⟨state, run, -⟩ := Ixon.Verify.runGetExact_complete (Ixon.Verify.deConstantExact_serConstant c wire)
  exact ⟨state, run⟩

/-- **A block record's canonical bytes open with the block header.** -/
theorem blockHeader_of_muts {c : Constant} (wire : c.wireWF) {ms : Array Ixon.MutConst}
    (h : c.info = .muts ms) : blockHeader (serConstant c) = true := by
  obtain ⟨state, run⟩ := serConstant_run wire
  obtain ⟨mid, hi⟩ := ProjectionRead.constant_info run
  rw [h] at hi
  obtain ⟨tag, s, ht, hf⟩ := info_muts hi
  unfold blockHeader
  simp only [EStateM.run, ht, hf, beq_self_eq_true]

/-- Bytes that do not open with the block header decode canonically to no block. -/
theorem not_muts_of_header {c : Constant} (wire : c.wireWF) {bytes : ByteArray}
    (encoded : serConstant c = bytes) (header : blockHeader bytes = false) :
    ∀ ms, c.info ≠ .muts ms := by
  intro ms h
  have := blockHeader_of_muts wire h
  rw [encoded, header] at this
  cases this

/-- **No published input name sits at a block**: when `compileReport` returns, the
record at a published input name's address is stored, and its canonical decoding,
if it has one, is no block. -/
theorem published_not_block {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) {n : Ix.Name} {named : Ixon.Named}
    (hn : (n, named) ∈ ixe.named.toList) (input : env.consts.contains n = true) :
    ∃ lc, ixe.consts.get? named.addr = some lc ∧
      ∀ c, c.wireWF → serConstant c = lc.rawBytes → ∀ ms, c.info ≠ .muts ms := by
  obtain ⟨lc, stored, header⟩ := publishedReadable h n named hn input
  exact ⟨lc, stored, fun c wire encoded => not_muts_of_header wire encoded header⟩

end Ix.Cert.RecordHeaders
