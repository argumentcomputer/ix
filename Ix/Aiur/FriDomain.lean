/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Domain

/-! Query locations for the pinned two-adic FRI strategy. Indices use
bit-reversed order. `wordReverse` spells out the native word reversal and
overflowing right shift; correspondence requires a supported bit count and
an admitted domain index.
-/

namespace Aiur.NativeAIR.FriDomain

def reverseBits (bits index : Nat) : Nat := (BitVec.ofNat bits index).reverse.toNat

def wordReverse (wordBits bits index : Nat) : Nat :=
  ((BitVec.ofNat wordBits index).reverse >>> ((wordBits - bits) % wordBits)).toNat

def queryPoint (domain : Domain.Subgroup) (index : Nat) : G :=
  (Domain.generator domain).pow (reverseBits domain.val index)

def inputPoint (domain : Domain.Subgroup) (index : Nat) : G := 7 * queryPoint domain index

/-- The interpolation node at `slot` of the native folding row `index`. -/
def foldNode (parent arity : Domain.Subgroup) (index slot : Nat) : G :=
  (Domain.generator parent).pow (reverseBits (parent.val - arity.val) index) *
    (Domain.generator arity).pow (reverseBits arity.val slot)

end Aiur.NativeAIR.FriDomain
