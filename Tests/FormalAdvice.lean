import Ix.Cli.FormalAggregate
import Ix.Aggr.CatalogPlan

/-! A Lean advice builder over byte streams, kept as the reference the Rust
encoder (`aggregate_controller::streams`) is checked against:
`formal-aggregate-tests` writes these streams for the `streams_parity`
comparison. It covers every shape the controller proves: wraps and pairs,
binding discharge, and the joins of a catalog's plan. -/
namespace Ix.Cli.FormalAdvice
open Lean Aggr Ix.Cli.FormalAggregate

/-- Recursive advice as byte streams, in the order they are added. Adding a
key again replaces its payload in place, as `IOBuffer.extend` does. The
payloads stay bytes: child proofs, keys and claims are never expanded to
field elements, and Rust copies each once into compact advice. Channels and
keys follow `Ix.Aggr.Protocol`. -/
structure Streams where
  entries : Array (UInt64 × Array UInt64 × ByteArray) := #[]

namespace Streams

def extend (s : Streams) (channel : UInt64) (key : Array UInt64) (bytes : ByteArray) : Streams :=
  match s.entries.findIdx? (fun (c, k, _) => c == channel && k == key) with
  | some i => { entries := s.entries.set! i (channel, key, bytes) }
  | none => { entries := s.entries.push (channel, key, bytes) }

private def addressKey (a : Address) : Array UInt64 := a.hash.data.map (·.toUInt64)

/-- Channel 1: the verifying key of one child kind. -/
def vk (s : Streams) (kind : ChildKind) (bytes : ByteArray) : Streams :=
  s.extend 1 #[kind.code.toUInt64] bytes

/-- Channels 0 and 2 for one child slot: proof transport and claims. -/
def child (s : Streams) (slot : Nat) (proof claims : ByteArray) : Streams :=
  (s.extend 0 #[slot.toUInt64] proof).extend 2 #[slot.toUInt64] claims

/-- Channels 3 and 6: the identity blob and the shape byte. -/
def identity (s : Streams) (allowed : ByteArray) (shape : Nat) : Streams :=
  (s.extend 3 #[0] allowed).extend 6 #[0] (ByteArray.mk #[shape.toUInt8])

/-- Channel 2 key 2: a pair fold's output claim bytes. -/
def outputClaim (s : Streams) (bytes : ByteArray) : Streams :=
  s.extend 2 #[2] bytes

/-- Channel 4: a preimage keyed by its packed digest. -/
def preimage (s : Streams) (bytes : ByteArray) : Streams :=
  s.extend 4 ((MultiStark.digestGs bytes).map (·.val)) bytes

/-- Channel 5: a serialized canonical tree keyed by its root. -/
def tree (s : Streams) (t : Ix.AssumptionTree) : Streams :=
  s.extend 5 (addressKey t.root) (Ix.AssumptionTree.ser t)

/-- Channel 6: a structural carried/discharged choice keyed by its candidate. -/
def path (s : Streams) (candidate : Address) (path? : Option Ix.Merkle.MerklePath) : Streams :=
  s.extend 6 (addressKey candidate) (pathPayload path?)

/-- The same streams as an `IOBuffer`, for test fixtures. -/
def toIOBuffer (s : Streams) : Aiur.IOBuffer :=
  s.entries.foldl (init := default) fun io (channel, key, bytes) =>
    io.extend (.ofNat channel.toNat) (key.map (.ofNat ·.toNat)) (byteGs bytes)

end Streams

/-- A proven child: its statement, its kind and its proof wrapper. -/
structure Node where
  statement : CheckEnvTrees
  kind : ChildKind
  wrapper : Ixon.Proof

def streamsChild (ctx : Keys) (s : Streams) (slot : Nat) (node : Node) : IO Streams := do
  let s := s.vk node.kind (if node.kind == .ixvm then ctx.ixvm.key else ctx.aggr.key)
  return s.child slot (← rawProof node.kind node.wrapper.proof)
    (MultiStark.serializeClaims #[outerClaim ctx node.kind node.wrapper.claim])

/-- A wrap/pair witness as streams, with the manifest fold semantics the
independent verifier checks. -/
def streamsAdvice (ctx : Keys) (left : Node) (right : Option Node)
    (output : CheckEnvTrees) (structural : Bool) : IO Streams := do
  let shape := match right with
    | none => shapeCode (left.kind, none)
    | some r => if structural then structuralShapeCode left.kind r.kind
        else shapeCode (left.kind, some r.kind)
  let mut s ← streamsChild ctx (({} : Streams).identity ctx.allowed shape) 0 left
  if let some right := right then
    s ← streamsChild ctx s 1 right
    s := s.outputClaim (Ix.Claim.ser output.claim)
    for c in #[left.wrapper.claim, right.wrapper.claim] do
      s := s.preimage (Ix.Claim.ser c)
    let trees := if structural then left.statement.structuralAdviceTrees right.statement output
      else left.statement.adviceTrees right.statement output
    for t in trees do s := s.tree t
    if structural then
      for (addr, p) in left.statement.structuralPathAdvice right.statement output do
        s := s.path addr p
  return s

/-- The output of a binding discharge: the child's statement, validating
its role binding instead of assuming it. -/
def dischargedStatement (child : CheckEnvTrees) : CheckEnvTrees :=
  { child with ctx := { child.ctx with bindingAssumed := false } }

/-- A binding discharge (`ix_aggr` shapes 13 and 14) as streams: the child
that assumes its binding in slot 0, the IxVM proof of the `binding` claim in
slot 1, the output claim, and the preimages of both children's claims. -/
def streamsDischarge (ctx : Keys) (child : Node) (bindingWrapper : Ixon.Proof)
    (output : CheckEnvTrees) : IO Streams := do
  let mut s ← streamsChild ctx
    (({} : Streams).identity ctx.allowed (dischargeShapeCode child.kind)) 0 child
  s := s.vk .ixvm ctx.ixvm.key
  s := s.child 1 (← rawProof .ixvm bindingWrapper.proof)
    (MultiStark.serializeClaims #[outerClaim ctx .ixvm bindingWrapper.claim])
  s := s.outputClaim (Ix.Claim.ser output.claim)
  for c in #[child.wrapper.claim, bindingWrapper.claim] do
    s := s.preimage (Ix.Claim.ser c)
  return s

/-- Node `i` of a catalog's plan (`Aggr.catalogPlan`) as streams, with the
plan's advice for it (`CatalogPlan.advice`): both children, each an
`ix_aggr` proof wrapper from `proofs`, the output claim, the preimages and
the trees. `none` for a member. -/
def streamsCatalog (ctx : Keys) (plan : CatalogPlan) (members : Array CatalogMember)
    (proofs : Array (Option Ixon.Proof)) (i : Nat) : IO (Option (Nat × Streams)) := do
  let some (shape, preimages, trees) := plan.advice members i | return none
  let mut s := ({} : Streams).identity ctx.allowed shape
  for (c, slot) in plan.nodes[i]!.children.zipIdx do
    let some child := proofs[c]! | throw (IO.userError s!"catalog node {c} has no proof")
    s := s.vk .aggr ctx.aggr.key
    s := s.child slot (← rawProof .aggr child.proof)
      (MultiStark.serializeClaims #[outerClaim ctx .aggr child.claim])
  s := s.outputClaim (Ix.Claim.ser plan.statements[i]!.claim)
  for pre in preimages do s := s.preimage pre
  for t in trees do s := s.tree t
  return some (shape, s)

end Ix.Cli.FormalAdvice
