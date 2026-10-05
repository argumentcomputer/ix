import IxKernel.Ixon.Types

/-! # The decoded-record store of the Ixon ingress

Decoded records (`Constants`) and literal blobs (`Blobs`) as the host supplies
them, keyed by address and in order, with the lookups the certified entries
use: first-match `lookup`, the projection test, the empty-table test of a
projection record, and the little-endian value of a natural-number blob;
and `LawfulBEq Address`, for the proofs of the duplicate-key checks (first
match is then the only match: the entries reject a key used twice). -/

namespace Ix.Kernel.Ingress

abbrev Constants := List (Address × Ixon.Constant)
abbrev Blobs := List (Address × ByteArray)

def isProjection : Ixon.ConstantInfo → Bool
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => true
  | _ => false

/-- First lookup in the supplied finite store. -/
def lookup (store : List (Address × α)) (address : Address) : Option α :=
  match store with
  | [] => none
  | (key, value) :: rest => if key = address then some value else lookup rest address

/-- Little-endian natural-number payload, including the empty encoding of zero.
Canonical byte spelling is a separate condition (the canonical decoder). -/
def natural (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- A projection constant carries no expression tables. -/
def emptyTables (source : Ixon.Constant) : Bool :=
  source.sharing.isEmpty && source.refs.isEmpty && source.univs.isEmpty

/-! ## Key equality

`Address` derives `BEq` and `DecidableEq` separately (`IxKernel/Address/Core.lean`).
The derived `BEq` compares the key bytes with `ByteArray.beq`, whose
definition compares the underlying `Array UInt8`s (the `lean_sarray_dec_eq`
extern implements it, as it implements `ByteArray.decEq`). It is therefore
lawful, which the `Std.HashSet Address` lemmas behind the duplicate-key
checks need (`Ix.Kernel.Admission.uniqueKeys`, the reader's `readRecords`).
Proof only: these add no runtime code. -/

theorem _root_.Address.beq_eq (a b : Address) : (a == b) = (a.hash == b.hash) := rfl

theorem _root_.Address.beq_iff_eq {a b : Address} : (a == b) = true ↔ a = b := by
  rw [Address.beq_eq]
  constructor
  · intro h
    have data : (a.hash.data == b.hash.data) = true := h
    cases a; cases b
    simp only [Address.mk.injEq]
    exact ByteArray.ext (eq_of_beq data)
  · rintro rfl
    show (a.hash.data == a.hash.data) = true
    exact beq_self_eq_true _

instance : LawfulBEq Address where
  eq_of_beq h := Address.beq_iff_eq.mp h
  rfl := Address.beq_iff_eq.mpr rfl

end Ix.Kernel.Ingress
