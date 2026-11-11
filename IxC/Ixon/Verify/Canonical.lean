import IxC.Ixon.Canonical
import IxC.Ixon.Verify.BoundedConstant
import IxC.Ixon.Verify.WireCheck

namespace Ixon.Verify.Canonical

open Ixon

/-- The per-record canonical contract: `bytes` is exactly the serialization of
a wire-well-formed constant whose binder data are in canonical form, within the
byte and aggregate universe-node limits. Canonicality here is byte spelling and
the binder data's spelling; it asserts nothing about mutual-block order,
typing, or address authentication. -/
structure Reads (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) (constant : Constant) : Prop where
  wire : constant.wireWF
  encoded : serConstant constant = bytes
  bytesFit : bytes.size ≤ maxBytes
  nodesFit : Bounded.univNodes constant.univs ≤ maxUnivNodes
  binders : constant.bindersCanonical = true

theorem deConstant_spec (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) (constant : Constant)
    (h : Canonical.deConstant maxBytes maxUnivNodes bytes = .ok constant) :
    Bounded.deConstant maxBytes maxUnivNodes bytes = .ok constant ∧
      constant.wireWF ∧ serConstant constant = bytes := by
  unfold Canonical.deConstant at h
  cases read : Bounded.deConstant maxBytes maxUnivNodes bytes with
  | error reason => simp [read, bind, Except.bind] at h
  | ok value =>
    simp only [read, bind, Except.bind] at h
    split at h
    next valid =>
      split at h
      next canonical =>
        split at h
        next =>
          cases h
          exact ⟨rfl, WireCheck.validConstant_iff _ |>.mp valid, canonical⟩
        next => cases h
      next => cases h
    next => cases h

/-- A canonical read has its binder data in canonical form. -/
theorem deConstant_bindersCanonical (maxBytes maxUnivNodes : Nat) (bytes : ByteArray)
    (constant : Constant)
    (h : Canonical.deConstant maxBytes maxUnivNodes bytes = .ok constant) :
    constant.bindersCanonical = true := by
  unfold Canonical.deConstant at h
  cases read : Bounded.deConstant maxBytes maxUnivNodes bytes with
  | error reason => simp [read, bind, Except.bind] at h
  | ok value =>
    simp only [read, bind, Except.bind] at h
    split at h
    next =>
      split at h
      next =>
        split at h
        next binders =>
          cases h
          exact binders
        next => cases h
      next => cases h
    next => cases h

theorem deConstant_serConstant (constant : Constant) (wf : constant.wireWF)
    (canonical : constant.bindersCanonical = true)
    (maxBytes maxUnivNodes : Nat) (bytesFit : (serConstant constant).size ≤ maxBytes)
    (nodesFit : Bounded.univNodes constant.univs ≤ maxUnivNodes) :
    Canonical.deConstant maxBytes maxUnivNodes (serConstant constant) = .ok constant := by
  have decoded := BoundedConstant.deConstant_serConstant constant wf _ _ bytesFit nodesFit
  have valid := WireCheck.validConstant_iff constant |>.mpr wf
  simp [Canonical.deConstant, decoded, valid, canonical, bind, Except.bind, pure, Except.pure]

/-- Exact canonical byte-decoding contract for all constant variants. The
right side describes the bytes and bounds without referring to a decoder. -/
theorem deConstant_ok_iff (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) (constant : Constant) :
    Canonical.deConstant maxBytes maxUnivNodes bytes = .ok constant ↔
      constant.wireWF ∧ serConstant constant = bytes ∧ bytes.size ≤ maxBytes ∧
        Bounded.univNodes constant.univs ≤ maxUnivNodes ∧ constant.bindersCanonical = true := by
  constructor
  · intro h
    obtain ⟨read, valid, canonical⟩ := deConstant_spec _ _ _ _ h
    obtain ⟨bytesFit, nodesFit, _⟩ := BoundedConstant.deConstant_spec _ _ _ _ read
    exact ⟨valid, canonical, bytesFit, nodesFit, deConstant_bindersCanonical _ _ _ _ h⟩
  · rintro ⟨valid, rfl, bytesFit, nodesFit, binders⟩
    exact deConstant_serConstant constant valid binders _ _ bytesFit nodesFit

/-- `deConstant_ok_iff` in terms of the named per-record contract. -/
theorem deConstant_reads_iff (maxBytes maxUnivNodes : Nat) (bytes : ByteArray)
    (constant : Constant) :
    Canonical.deConstant maxBytes maxUnivNodes bytes = .ok constant ↔
      Reads maxBytes maxUnivNodes bytes constant :=
  (deConstant_ok_iff _ _ _ _).trans
    ⟨fun ⟨wire, encoded, bytesFit, nodesFit, binders⟩ =>
      ⟨wire, encoded, bytesFit, nodesFit, binders⟩,
     fun ⟨wire, encoded, bytesFit, nodesFit, binders⟩ =>
      ⟨wire, encoded, bytesFit, nodesFit, binders⟩⟩

theorem deConstant_noTrailing (constant : Constant) (wf : constant.wireWF)
    (maxBytes maxUnivNodes : Nat) (suffix : ByteArray) (nonempty : suffix.size ≠ 0) :
    (Canonical.deConstant maxBytes maxUnivNodes (serConstant constant ++ suffix)).isOk = false := by
  cases read : Canonical.deConstant maxBytes maxUnivNodes (serConstant constant ++ suffix) with
  | error _ => rfl
  | ok value =>
    have bounded := (deConstant_spec _ _ _ _ read).1
    have rejected := BoundedConstant.deConstant_noTrailing constant wf maxBytes maxUnivNodes suffix nonempty
    rw [bounded] at rejected
    cases rejected

end Ixon.Verify.Canonical
