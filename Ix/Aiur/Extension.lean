/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofCodec

/-! Arithmetic on the two canonical coordinates carried by native proofs.
The pinned Goldilocks extension uses the basis `1, u` with `u² = 7`.
These definitions do not authenticate polynomial openings or a transcript.
-/

namespace Aiur.NativeAIR.ProofCodec.Extension

def ofBase (value : G) : Extension := ⟨value, 0⟩

instance ofNat : OfNat Extension n := ⟨ofBase (G.ofNat n)⟩
instance add : Add Extension := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
instance sub : Sub Extension := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1⟩⟩
instance neg : Neg Extension := ⟨fun a => ⟨0 - a.c0, 0 - a.c1⟩⟩
instance mul : Mul Extension := ⟨fun a b =>
  ⟨a.c0 * b.c0 + a.c1 * (b.c1 * 7), a.c0 * b.c1 + a.c1 * b.c0⟩⟩

def basis : Extension := ⟨0, 1⟩
def conjugate (value : Extension) : Extension := ⟨value.c0, 0 - value.c1⟩
def norm (value : Extension) : G := value.c0 * value.c0 - 7 * (value.c1 * value.c1)
def scale (value : Extension) (scalar : G) : Extension :=
  ⟨value.c0 * scalar, value.c1 * scalar⟩

def powBits (value : Extension) (exponent : Nat) : Nat → Extension
  | 0 => 1
  | fuel + 1 =>
    if exponent == 0 then 1
    else
      let half := powBits value (exponent / 2) fuel
      let square := half * half
      if exponent % 2 == 0 then square else square * value

def power (value : Extension) (exponent : Nat) : Extension :=
  powBits value exponent (exponent.log2 + 1)

def tryInverse (value : Extension) : Option Extension :=
  if value == 0 then none else some (value.conjugate.scale value.norm.inverse)

def evalOps : EvalOps Extension := ⟨ofBase, (· + ·), (· - ·), (· * ·), (-·)⟩

end Aiur.NativeAIR.ProofCodec.Extension
