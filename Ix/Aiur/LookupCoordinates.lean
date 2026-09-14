/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Extension

/-! The two coordinates checked by native degree-two logUp. At an opening
point each coordinate is itself a challenge-field value. The two coordinates
must remain separate there; this quadratic algebra need not be a field. -/

namespace Aiur.NativeAIR.LogUp

structure Coordinates (W : Type u) where
  c0 : W
  c1 : W
  deriving DecidableEq, Repr

namespace Coordinates

def ofBase [OfNat W 0] (value : W) : Coordinates W := ⟨value, 0⟩

instance ofNat [OfNat W n] [OfNat W 0] : OfNat (Coordinates W) n :=
  ⟨ofBase (OfNat.ofNat n)⟩
instance add [Add W] : Add (Coordinates W) := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
instance sub [Sub W] : Sub (Coordinates W) := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1⟩⟩
instance neg [Neg W] : Neg (Coordinates W) := ⟨fun a => ⟨-a.c0, -a.c1⟩⟩

/-- The native `mul2` Karatsuba formula, with the pinned nonresidue 7. -/
instance mul [OfNat W 7] [Add W] [Sub W] [Mul W] : Mul (Coordinates W) := ⟨fun a b =>
  let v0 := a.c0 * b.c0
  let v1 := a.c1 * b.c1
  ⟨v0 + v1 * 7, (a.c0 + a.c1) * (b.c0 + b.c1) - v0 - v1⟩⟩

def scale [Mul W] (value : Coordinates W) (scalar : W) : Coordinates W :=
  ⟨value.c0 * scalar, value.c1 * scalar⟩

def map (f : W → V) (value : Coordinates W) : Coordinates V := ⟨f value.c0, f value.c1⟩

def read (values : Array W) (slot : Nat) : Option (Coordinates W) := do
  return ⟨← values[2 * slot]?, ← values[2 * slot + 1]?⟩

def flatten (values : List (Coordinates W)) : List W := values.flatMap fun value => [value.c0, value.c1]

/-- Only base-field coordinates have this identification with the native field. -/
def toExtension (value : Coordinates G) : ProofCodec.Extension := ⟨value.c0, value.c1⟩
def fromExtension (value : ProofCodec.Extension) : Coordinates G := ⟨value.c0, value.c1⟩

end Coordinates
end Aiur.NativeAIR.LogUp
