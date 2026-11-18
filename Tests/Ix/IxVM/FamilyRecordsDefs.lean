/-! # Lean sources of the family records

Two small families, checked by Lean's kernel, that `ixvm-family-records`
(`Tests.Ix.IxVM.FamilyRecords`) reads from the test binary's environment and compiles with Ix's
compiler: a `List`-nested tree and a mutual pair of families indexed by `Nat`. -/

namespace Tests.Ix.IxVM.FamilyRecordsDefs

/-- A `List`-nested tree. -/
inductive T where
  | node : List T → T

mutual
  /-- The first of a mutual pair indexed by `Nat`. -/
  inductive EvT : Nat → Type where
    | zero : EvT Nat.zero
    | succ : (n : Nat) → OdT n → EvT (Nat.succ n)
  /-- The second of the pair. -/
  inductive OdT : Nat → Type where
    | succ : (n : Nat) → EvT n → OdT (Nat.succ n)
end

end Tests.Ix.IxVM.FamilyRecordsDefs
