module
public import Ix.Aggr.Host
public import Ix.Aggr.Protocol
public import Ix.ClaimContext
public import Ix.Merkle

/-!
# Aggregating a catalog over several role bindings

A `.ixc` catalog's members may come from different Lean toolchains, so their
aggregate roots state their typing under different role bindings. This plan
joins those roots into one statement, deterministically, so that `ix
aggregate --ixc` and `ix verify --aggregate --ixc` reach the same root:

1. the members are grouped by the literal class of their binding
   (`Ix.ClaimContext.literalClassOf`), the groups in the order of their first
   member in the manifest; incomplete bindings each remain a separate member;
2. a group of two or more members is folded left to right, in manifest order,
   with the cross-binding structural pair (`ix_aggr` shape 15), into one
   `CheckEnv` claim under the class;
3. the groups' claims are folded left to right with the catalog join (shape
   16) into a `Catalog` claim. A catalog of one class has that class's claim
   as its root.

Every member statement is the unconditional `CheckEnv` claim that validates
its binding, so a cross-binding join's subjects are `nodeHash(left, right)`
and it has no assumptions: the plan needs only claims, not subject trees, and
a member root folded structurally (an aggregate above `--structural-above`
leaves) joins like any other.
-/

public section

namespace Aggr

/-- One catalog member, as the plan sees it. -/
structure CatalogMember where
  label : String
  toolchain : String
  /-- The unconditional `CheckEnv` claim the member's aggregate root states,
  validating the member's binding. -/
  claim : Ix.Claim
  /-- The member's role binding section (`E8 03 …`), whose hash the claim's
  context names: a cross-binding join reads the literal class from it. -/
  bindingSection : ByteArray
  /-- The literal class of a complete binding. An incomplete binding stays
  under its own context and participates only in catalog joins. -/
  literalClass : Option Address
  deriving Inhabited

/-- One statement of the plan: a member's or a class's `CheckEnv` claim, or a
`Catalog` with its members tree. -/
inductive CatalogStatement where
  | checkEnv (claim : Ix.Claim)
  | catalog (trees : CatalogTrees)
  deriving Inhabited

def CatalogStatement.claim : CatalogStatement → Ix.Claim
  | .checkEnv claim => claim
  | .catalog trees => trees.claim

/-- A side of a catalog join (`CatalogTrees.join`). -/
def CatalogStatement.part : CatalogStatement → Ix.Claim ⊕ CatalogTrees
  | .checkEnv claim => .inl claim
  | .catalog trees => .inr trees

/-- A node of the plan: a member's root, or a join of two earlier nodes. -/
inductive CatalogNode where
  | member (index : Nat)
  /-- Shape 15: two nodes whose bindings have the literal class `klass`. -/
  | crossBinding (klass : Address) (left right : Nat)
  /-- Shape 16: two nodes of different classes, or catalogs. -/
  | catalogJoin (left right : Nat)
  deriving Inhabited

/-- The plan: its nodes in proving order, each node's statement, and the root
node (the last). -/
structure CatalogPlan where
  nodes : Array CatalogNode
  statements : Array CatalogStatement
  root : Nat

/-- The cross-binding join of two unconditional `CheckEnv` claims whose
bindings have the literal class `klass`: the structural fold under the
class. -/
def crossBindingClaim (klass : Address) (left right : Ix.Claim) :
    Except String Ix.Claim := do
  let .checkEnv lctx lroot none := left
    | throw s!"catalog plan: not an unconditional CheckEnv claim: {left}"
  let .checkEnv rctx rroot none := right
    | throw s!"catalog plan: not an unconditional CheckEnv claim: {right}"
  unless lctx.spec == rctx.spec && lctx.axioms == rctx.axioms do
    throw "catalog plan: members differ in specification digest or axioms"
  if lctx.bindingAssumed || rctx.bindingAssumed then
    throw "catalog plan: a member assumes its binding"
  let ctx := { lctx with binding := klass, bindingAssumed := false, literalClass := true }
  return .checkEnv ctx (Ix.Merkle.nodeHash lroot rroot) none

/-- Plan the joins of `members`, in manifest order. -/
def catalogPlan (members : Array CatalogMember) : Except String CatalogPlan := do
  if members.isEmpty then throw "catalog plan: a catalog has at least one member"
  let mut nodes : Array CatalogNode := #[]
  let mut statements : Array CatalogStatement := #[]
  let mut classes : Array (Option Address × Array Nat) := #[]
  for i in [0:members.size] do
    let m := members[i]!
    unless CatalogTrees.isMember m.claim do
      throw s!"catalog plan: member {m.label}'s claim is not an unconditional CheckEnv \
        claim that validates its binding: {m.claim}"
    nodes := nodes.push (.member i)
    statements := statements.push (.checkEnv m.claim)
    match m.literalClass.bind (fun klass => classes.findIdx? (·.1 == some klass)) with
    | some j => classes := classes.modify j fun (k, ixs) => (k, ixs.push i)
    | none => classes := classes.push (m.literalClass, #[i])
  let mut tops : Array Nat := #[]
  for (klass, indices) in classes do
    let mut acc := indices[0]!
    for i in indices[1:] do
      let some klass := klass
        | throw "catalog plan: an incomplete binding cannot use a cross-binding join"
      let claim ← crossBindingClaim klass statements[acc]!.claim statements[i]!.claim
      nodes := nodes.push (.crossBinding klass acc i)
      statements := statements.push (.checkEnv claim)
      acc := nodes.size - 1
    tops := tops.push acc
  let mut root := tops[0]!
  for t in tops[1:] do
    let joined := CatalogTrees.join statements[root]!.part statements[t]!.part
    nodes := nodes.push (.catalogJoin root t)
    statements := statements.push (.catalog joined)
    root := nodes.size - 1
  return { nodes, statements, root }

/-- What proving node `i` takes besides its children's proofs: the shape, the
channel-4 preimages (the children's claims, and the binding section of each
member child of a cross-binding join) and the channel-5 trees (the members
trees of catalog children and of the output). `none` for a member. -/
def CatalogPlan.advice (plan : CatalogPlan) (members : Array CatalogMember) (i : Nat) :
    Option (Nat × Array ByteArray × Array Ix.AssumptionTree) :=
  let claimBytes (j : Nat) := Ix.Claim.ser plan.statements[j]!.claim
  let bindingSection (j : Nat) : Array ByteArray :=
    match plan.nodes[j]! with
    | .member m => #[members[m]!.bindingSection]
    | _ => #[]
  let membersTree (j : Nat) : Array Ix.AssumptionTree :=
    match plan.statements[j]! with
    | .catalog trees => #[trees.members]
    | .checkEnv _ => #[]
  match plan.nodes[i]! with
  | .member _ => none
  | .crossBinding _ l r =>
    some (crossBindingShapeCode, #[claimBytes l, claimBytes r] ++ bindingSection l ++
      bindingSection r, #[])
  | .catalogJoin l r =>
    some (catalogShapeCode, #[claimBytes l, claimBytes r],
      membersTree l ++ membersTree r ++ membersTree i)

/-- The children of node `i`. -/
def CatalogNode.children : CatalogNode → Array Nat
  | .member _ => #[]
  | .crossBinding _ l r | .catalogJoin l r => #[l, r]

end Aggr

end
