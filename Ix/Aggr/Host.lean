module
public import Ix.AssumptionTree
public import Ix.Claim
public import Std.Data.HashSet

/-!
# Host-side aggregate statement folding

The circuit rechecks all of this from serialized trees and Merkle paths.
These helpers give the CLI, tests, and benchmarks one implementation for
constructing flat and structural outputs plus their channel-5/channel-6
advice.
-/

public section

namespace Aggr

/-- A `CheckEnv` statement together with the trees whose roots it commits to.
Leaf and flat-pair subject trees are canonical; structural pairs use free-form
root-of-roots subject trees. Assumption trees always remain canonical.
`assumptions = none` is represented by no tree, never by an empty or
padding-only serialization. `ctx` is the claim's context; a fold joins only
statements under one context. -/
structure CheckEnvTrees where
  ctx : Ix.ClaimContext
  subjects : Ix.AssumptionTree
  assumptions : Option Ix.AssumptionTree
  deriving Repr

namespace CheckEnvTrees

def claim (statement : CheckEnvTrees) : Ix.Claim :=
  .checkEnv statement.ctx statement.subjects.root (statement.assumptions.map (·.root))

def subjectCount (statement : CheckEnvTrees) : Nat :=
  statement.subjects.leaves.size

private def canonicalizeAt (label : String) (expected : Address)
    (tree : Ix.AssumptionTree) : Except String Ix.AssumptionTree := do
  let some canonical := Ix.AssumptionTree.canonical tree.leaves
    | throw s!"{label}: tree has no real leaves"
  if canonical.root != expected then
    throw s!"{label}: leaves do not reproduce claimed canonical root {expected}"
  pure canonical

/-- Recover and validate a host statement from a claim plus its content-
addressed tree map. This is used when binding persisted shard proofs to
aggregation leaves: the wrapper's claim roots must match canonical trees
reconstructed from the `.ixe` environment. -/
def ofClaim (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree) : Except String CheckEnvTrees := do
  let .checkEnv ctx subjectRoot assumptionRoot? := claim
    | throw "aggr: expected a CheckEnv claim"
  let some subjectTree := trees.get? subjectRoot
    | throw s!"aggr: missing subject tree {subjectRoot}"
  let subjects ← canonicalizeAt "aggr subjects" subjectRoot subjectTree
  let assumptions ← match assumptionRoot? with
    | none => pure none
    | some assumptionRoot =>
      let some assumptionTree := trees.get? assumptionRoot
        | throw s!"aggr: missing assumption tree {assumptionRoot}"
      pure (some (← canonicalizeAt "aggr assumptions"
        assumptionRoot assumptionTree))
  pure { ctx, subjects, assumptions }

private def assumptionLeaves (statement : CheckEnvTrees) : Array Address :=
  statement.assumptions.map (·.leaves) |>.getD #[]

/-- The sorted, deduplicated candidate stream consumed by either discharge
mode: `assumptionsL ∪ assumptionsR`. -/
def assumptionCandidates (left right : CheckEnvTrees) : Array Address :=
  match Ix.AssumptionTree.canonical
      (assumptionLeaves left ++ assumptionLeaves right) with
  | none => #[]
  | some tree => tree.leaves

/-- Canonical pair fold:

`subjects = subjectsL ∪ subjectsR`

`assumptions = (assumptionsL ∪ assumptionsR) ∖ subjects`.

The circuit independently verifies this relation with sorted linear merges,
and that both children and the output share one context (the left child's
here); the host implementation uses a hash set only to construct the witness. -/
def join (left right : CheckEnvTrees) : CheckEnvTrees :=
  let subjectLeaves := left.subjects.leaves ++ right.subjects.leaves
  let subjects := (Ix.AssumptionTree.canonical subjectLeaves).get!
  let subjectSet := subjects.leaves.foldl (fun set addr => set.insert addr)
    ({} : Std.HashSet Address)
  let remaining := assumptionCandidates left right |>.filter
    (fun addr => !subjectSet.contains addr)
  { ctx := left.ctx, subjects, assumptions := Ix.AssumptionTree.canonical remaining }

/-- Structural fold. Subjects are committed in O(1) as a free-form node over
the two child roots. Assumptions retain canonical set semantics and drop
precisely those candidates for which the resulting subject forest can produce
a membership path. -/
def joinStructural (left right : CheckEnvTrees) : CheckEnvTrees :=
  let subjects := Ix.AssumptionTree.join left.subjects right.subjects
  let remaining := assumptionCandidates left right |>.filter
    (fun addr => !subjects.contains addr)
  { ctx := left.ctx, subjects, assumptions := Ix.AssumptionTree.canonical remaining }

/-- One channel-6 choice per structural-pair candidate. `some path` discharges
the candidate against the structural output root; `none` carries it into the
output assumption set. -/
def structuralPathAdvice (left right output : CheckEnvTrees) :
    Array (Address × Option Ix.Merkle.MerklePath) :=
  assumptionCandidates left right |>.map fun candidate =>
    (candidate, output.subjects.merkleProof candidate)

/-- The present trees in channel-5 order for one pair fold. Optional empty
assumption sets contribute no advice entry. -/
def adviceTrees (left right output : CheckEnvTrees) : Array Ix.AssumptionTree :=
  #[left.subjects] ++ left.assumptions.toArray ++
  #[right.subjects] ++ right.assumptions.toArray ++
  #[output.subjects] ++ output.assumptions.toArray

/-- Structural pairs never open subject trees. Only the canonical input/output
assumption trees are needed on channel 5. -/
def structuralAdviceTrees (left right output : CheckEnvTrees) :
    Array Ix.AssumptionTree :=
  left.assumptions.toArray ++ right.assumptions.toArray ++
    output.assumptions.toArray

/-- The cross-binding structural fold (`ix_aggr` shape 15): the structural
fold of two claims whose role bindings have the literal class `klass`, stated
under that class (validator `erased-lean-v2-class`). The circuit checks that
both children's classes are `klass`, reading each from its binding section when
the child validates its binding. Advice is that of `joinStructural`, plus the
binding sections of children that validate their binding. -/
def joinCrossBinding (klass : Address) (left right : CheckEnvTrees) : CheckEnvTrees :=
  let joined := joinStructural left right
  { joined with ctx := { left.ctx with binding := klass, bindingAssumed := false,
                                       literalClass := true } }

end CheckEnvTrees

/-- A `Catalog` statement with its members tree: the canonical tree over the
member claims' digests (`Ix.Claim.commit`). -/
structure CatalogTrees where
  members : Ix.AssumptionTree
  deriving Repr

namespace CatalogTrees

def claim (catalog : CatalogTrees) : Ix.Claim := .catalog catalog.members.root

/-- Whether a claim may be a catalog member: an unconditional `CheckEnv` claim
that validates its binding or names a literal class. -/
def isMember : Ix.Claim → Bool
  | .checkEnv ctx _ none => !ctx.bindingAssumed
  | _ => false

/-- The catalog of `members`, each of which must be a catalog member. -/
def ofMembers (members : Array Ix.Claim) : Except String CatalogTrees := do
  for m in members do
    unless isMember m do throw s!"aggr catalog: not a catalog member: {m}"
  let some tree := Ix.AssumptionTree.canonical (members.map Ix.Claim.commit)
    | throw "aggr catalog: a catalog has at least one member"
  return { members := tree }

/-- The member statements of one side of a catalog join (`ix_aggr` shape 16):
a member claim's own digest, or a catalog's members. -/
def part : Ix.Claim ⊕ CatalogTrees → Array Address
  | .inl claim => #[Ix.Claim.commit claim]
  | .inr catalog => catalog.members.leaves

/-- The catalog join: the union of both sides' member statements. -/
def join (left right : Ix.Claim ⊕ CatalogTrees) : CatalogTrees :=
  { members := (Ix.AssumptionTree.canonical (part left ++ part right)).get! }

end CatalogTrees

end Aggr

end
