/-
Adapted for Ix from the standard-library-shaped helpers in
`Ix/Theory/Named/Std/Basic.lean` (the named tree's Lean4Lean adaptation; its
Apache license is in `Ix/Theory/Named/LICENSE`).  Only the pieces the compiler
proofs rely on are kept.
SPDX-License-Identifier: Apache-2.0
-/

import Batteries.Data.Array.Lemmas
import Std.Data.HashMap.Basic

/-!
# Standard-library helpers for the compiler proofs

The compiler proofs unfold `Option`-monadic reference compilers with `simp`
and expect binds against `some` to become existentials; the hash-map caches
use product and list keys.  These attributes and instances used to arrive
through the retired named specification's import closure and are now stated
here directly.
-/

namespace Ix.Compile.Verify

attribute [simp] Option.bind_eq_some_iff List.filterMap_cons

instance [BEq α] [PartialEquivBEq α] [BEq β] [PartialEquivBEq β] :
    PartialEquivBEq (α × β) where
  symm := by simp [(· == ·)]; grind [BEq.symm]
  trans := by simp [(· == ·)]; grind [BEq.trans]

instance [BEq α] [EquivBEq α] [BEq β] [EquivBEq β] : EquivBEq (α × β) where
  rfl := by simp [(· == ·)]

instance [BEq α] [Hashable α] [LawfulHashable α] [BEq β] [Hashable β]
    [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq a b h := by
    simp [(· == ·)] at h
    simp [hash, LawfulHashable.hash_eq _ _ h.1, LawfulHashable.hash_eq _ _ h.2]

instance [BEq α] [PartialEquivBEq α] : PartialEquivBEq (List α) where
  symm := by
    simp [(· == ·)]; intro a b
    induction a generalizing b <;> cases b <;> simp [List.beq]; grind [BEq.symm]
  trans := by
    simp [(· == ·)]; intro a b c
    induction a generalizing b c <;> cases b <;> simp [List.beq]
    cases c <;> simp [List.beq]; grind [BEq.trans]

instance [BEq α] [EquivBEq α] : EquivBEq (List α) where
  rfl {a} := by simp [(· == ·)]; induction a <;> simp [List.beq, *]

end Ix.Compile.Verify
