/-! # Fixture: changed constants that S decides at the value level (M7 S+a)

A theorem clique given in both member orders (the shape of Init+Std's transported theorem
cliques, `List.MergeSort.Internal.mergeSortTR₂_run_eq_mergeSort` and
`Std.Tactic.BVDecide.BVExpr.bitblast.go_decl_eq`): one order is the canonical one, the other is
transported, so its members' Ix proofs differ from Lean's while their statements are Lean's
(W+'s `theorem` route). Each clique has users: theorems, and a definition whose value carries a
member as a proof argument. No changed inductive block is involved. -/

namespace Tests.Ix.CompileCert.ChangedValueDefs

/-- A definition taking a proof argument. -/
def withProof (n : Nat) (_ : True) : Nat := n + 1

namespace TC0
mutual
theorem ta : Nat → True
  | 0 => trivial
  | n + 1 => (tb n).1
theorem tb : Nat → True ∧ True
  | 0 => ⟨trivial, trivial⟩
  | n + 1 => ⟨ta n, ta n⟩
end
theorem use_ta : True := ta 3
def useInDef : Nat := withProof 2 (tb 1).2
theorem useInDef_eq : useInDef = 3 := rfl
end TC0

namespace TC1
mutual
theorem tb : Nat → True ∧ True
  | 0 => ⟨trivial, trivial⟩
  | n + 1 => ⟨ta n, ta n⟩
theorem ta : Nat → True
  | 0 => trivial
  | n + 1 => (tb n).1
end
theorem use_ta : True := ta 3
def useInDef : Nat := withProof 2 (tb 1).2
theorem useInDef_eq : useInDef = 3 := rfl
end TC1

end Tests.Ix.CompileCert.ChangedValueDefs
