module
public import Ix.Ixby.Basic
public import Ix.Ixby.Primitive
public import Ix.Ixby.Validate
public import Ix.Ixby.Eval
public import Ix.Ixby.Composition
public import Ix.Ixby.Profile
public import Ix.Ixby.Codec
public import Ix.Ixby.Commitment

/-! Functional IxBy semantics, experimental crypto codecs and commitments.
The first proving backend is a separate `Ix.Ixby.Aiur` import so this logical
surface stays independent of the proving FFI. This is not a production IxVM
claim implementation or a certified Compilatrix target. -/
