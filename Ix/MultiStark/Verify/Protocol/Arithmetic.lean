module
public import Ix.MultiStark.Verify.Arithmetic

/-! Scalar conventions for the deterministic protocol: canonical modular
Goldilocks inversion, the X² = 7 extension basis, and powers of the pinned
primitive 2^32-th root. Cryptographic soundness is not an axiom of these
computational relations. In particular zero-denominator rejection is part
of the specified relation, not a successful inverse-zero convention. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def BaseInverse (value result : Field) : Prop :=
  value.val ≠ 0 ∧ value.inverse = result

def ExtensionInverse (value result : Ext) : Prop :=
  let norm := (value.c0.mul value.c0).sub ((Ix.Ixby.Goldilocks.mul 7 value.c1).mul value.c1)
  norm.val ≠ 0 ∧ value.inverse = result

def Division (left right result : Ext) : Prop :=
  ∃ reciprocal, ExtensionInverse right reciprocal ∧ left.mul reciprocal = result

/-- This scalar is pinned by the current native Goldilocks implementation.
All 33 table entries are checked against these powers by kernel reduction. -/
def generator (bits : Nat) : Field :=
  (Ix.Ixby.Goldilocks.reduce 0x185629dcda58878c).pow (2 ^ (32 - bits))

def TwoAdicGenerator (bits : Nat) (value : Field) : Prop := bits ≤ 32 ∧ generator bits = value

end MultiStark.Verify.Protocol
