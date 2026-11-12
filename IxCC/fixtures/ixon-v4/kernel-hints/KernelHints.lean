/-! The kernel-hints fixture (`fixtures/ixon-v4/kernel-hints`): proofs the certified kernel checks
in a millisecond with the artifact's reducibility hints and in time exponential in a literal's
bit length without them (`IxCC/plans/aiur-backend/KERNEL-NOTES.md`, section 10), a mutual
block of definitions (whose hints the compiler records under the members' projection
records), and a root `ixcc` compiles. -/

namespace KernelHints

/-- The root. -/
def root (n : Nat) : Nat := n + 1

/-- The minimal reproducer at width 16 (by `rfl`): over 20 s without hints at width 16, 92 ms
at width 12, growing four times per two bits. -/
theorem allOnesXor (y : BitVec 16) : (BitVec.allOnes 16 ^^^ y).toNat = Nat.xor 65535 y.toNat :=
  rfl

/-- The `complement` word equations as `ix compile --equations` states and proves them
(`Ix.Compile.WordEquations`, stage W1 of the data-types plan), at widths 16, 32 and 64. -/
theorem complement16 (x : Nat) : UInt16.complement (UInt16.ofNat x) =
    UInt16.ofNat (Nat.xor (nat_lit 65535) (Nat.mod x (nat_lit 65536))) :=
  UInt16.toNat_inj.mp (Nat.mod_eq_of_lt (UInt16.toNat_lt _)).symm

theorem complement32 (x : Nat) : UInt32.complement (UInt32.ofNat x) =
    UInt32.ofNat (Nat.xor (nat_lit 4294967295) (Nat.mod x (nat_lit 4294967296))) :=
  UInt32.toNat_inj.mp (Nat.mod_eq_of_lt (UInt32.toNat_lt _)).symm

theorem complement64 (x : Nat) : UInt64.complement (UInt64.ofNat x) =
    UInt64.ofNat (Nat.xor (nat_lit 18446744073709551615) (Nat.mod x (nat_lit 18446744073709551616))) :=
  UInt64.toNat_inj.mp (Nat.mod_eq_of_lt (UInt64.toNat_lt _)).symm

-- A mutual block of definitions: Lean's compiler writes the two `partial` definitions'
-- recursive bodies as one block of `unsafe` definitions, whose members' hints the artifact records
-- under their projection records. Not reached by the root.
mutual
partial def ping (n : Nat) : Nat := if n == 0 then 0 else pong (n - 1) + 1
partial def pong (n : Nat) : Nat := if n == 0 then 1 else ping (n - 1) + 2
end

end KernelHints
