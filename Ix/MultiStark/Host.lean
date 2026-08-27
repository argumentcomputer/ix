module
public import Ix.AssumptionTree
public import Ix.Claim
public import Std.Data.HashSet

/-!
# Host-side aggregate-first statement folding

The circuit rechecks all of this from serialized trees. These helpers give the
CLI one canonical implementation for constructing its claimed output and the
six tree preimages supplied to `join_two`.
-/

public section

namespace MultiStark

/-- A `CheckEnv` statement together with the canonical trees whose roots it
commits to. `assumptions = none` is represented by no tree, never by an empty
or padding-only serialization. -/
structure CheckEnvTrees where
  subjects : Ix.AssumptionTree
  assumptions : Option Ix.AssumptionTree
  deriving Repr

namespace CheckEnvTrees

def claim (statement : CheckEnvTrees) : Ix.Claim :=
  .checkEnv statement.subjects.root (statement.assumptions.map (·.root))

private def canonicalizeAt (label : String) (expected : Address)
    (tree : Ix.AssumptionTree) : Except String Ix.AssumptionTree := do
  let some canonical := Ix.AssumptionTree.canonical tree.leaves
    | throw s!"{label}: tree has no real leaves"
  if canonical.root != expected then
    throw s!"{label}: leaves do not reproduce claimed canonical root {expected}"
  pure canonical

/-- Recover and validate a host statement from a claim plus its content-
addressed tree map. This is used when turning persisted shard proofs into lift
slots: the wrapper's claim roots must match canonical trees reconstructed from
the `.ixe` environment. -/
def ofClaim (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree) : Except String CheckEnvTrees := do
  let .checkEnv subjectRoot assumptionRoot? := claim
    | throw "aggregate: expected a CheckEnv claim"
  let some subjectTree := trees.get? subjectRoot
    | throw s!"aggregate: missing subject tree {subjectRoot}"
  let subjects ← canonicalizeAt "aggregate subjects" subjectRoot subjectTree
  let assumptions ← match assumptionRoot? with
    | none => pure none
    | some assumptionRoot =>
      let some assumptionTree := trees.get? assumptionRoot
        | throw s!"aggregate: missing assumption tree {assumptionRoot}"
      pure (some (← canonicalizeAt "aggregate assumptions"
        assumptionRoot assumptionTree))
  pure { subjects, assumptions }

/-- Canonical mode-1 fold:

`subjects = subjectsL ∪ subjectsR`

`assumptions = (assumptionsL ∪ assumptionsR) ∖ subjects`.

The circuit independently verifies this relation with sorted linear merges;
the host implementation uses a hash set only to construct the witness. -/
def join (left right : CheckEnvTrees) : CheckEnvTrees :=
  let subjectLeaves := left.subjects.leaves ++ right.subjects.leaves
  let subjects := (Ix.AssumptionTree.canonical subjectLeaves).get!
  let subjectSet := subjects.leaves.foldl (fun set addr => set.insert addr)
    ({} : Std.HashSet Address)
  let leftAssumptions := left.assumptions.map (·.leaves) |>.getD #[]
  let rightAssumptions := right.assumptions.map (·.leaves) |>.getD #[]
  let remaining := (leftAssumptions ++ rightAssumptions).filter
    (fun addr => !subjectSet.contains addr)
  { subjects, assumptions := Ix.AssumptionTree.canonical remaining }

/-- The present trees in channel-5 order for one binary join. Optional empty
assumption sets contribute no advice entry. -/
def adviceTrees (left right output : CheckEnvTrees) : Array Ix.AssumptionTree :=
  #[left.subjects] ++ left.assumptions.toArray ++
  #[right.subjects] ++ right.assumptions.toArray ++
  #[output.subjects] ++ output.assumptions.toArray

end CheckEnvTrees

end MultiStark

end
