/-
  Nested occurrences of the members of an external mutual group, and a split
  block with a recursive and a non-recursive member.

  Not part of any Lake library: the compiler's nested expansion registers
  only the head occurrence of an external group (design document §2.5,
  "[open] Deduplication of sibling occurrences"), so these declarations may
  not compile under Ix. `canon-pass1` elaborates this file at run time
  (`Ix.Meta.getFileEnvCore`) and compares Lean's `rec_N` with both
  deduplication rules of `Ix.Compile.Canon.Nested.expand`, and reads
  `InductiveVal.isRec` of the split block's members.
-/
namespace CanonSiblingNest

mutual
inductive Tree (α : Type) where
  | node : α → Forest α → Tree α
inductive Forest (α : Type) where
  | nil : Forest α
  | cons : Tree α → Forest α → Forest α
end

/-- The occurrence's head is the group's first member. -/
inductive T where
  | mk : Tree T → T

/-- The occurrence's head is the group's second member. -/
inductive F where
  | mk : Forest F → F

/-- Both members occur. -/
inductive B where
  | mk : Tree B → Forest B → B

-- A split block: `NR` mentions no member; `R` is recursive.
mutual
inductive NR where
  | a : Nat → NR
inductive R where
  | b : NR → R → R
end

end CanonSiblingNest
