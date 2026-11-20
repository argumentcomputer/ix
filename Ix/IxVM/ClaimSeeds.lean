module
public import Ix.Claim
public import Ix.ClaimContext
public import IxC.Kernel.Ixon.RoleTable
public import IxC.Kernel.Ixon.Prelude

public section

/-!
# The seeds a typing claim may name

The references a record uses as constants (`constIdxsOf`), the claim walk's
edges (`walkEdges`), and the constants that use an inert axiom (`inertUsers`),
which no typing claim names. Kept apart from `Ix.IxVM.ClaimHarness`, which
imports this module, so that consumers of the seed lists (the aggregate audit)
need not import the harness.
-/
namespace IxVM.ClaimHarness

/-- Accumulate constant references, including the structure named by a projection.
Shared expressions have their own entry in the record's sharing table. -/
private partial def collectIdxs (out : Std.HashSet UInt64) : Ixon.Expr → Std.HashSet UInt64
  | .ref i _ => out.insert i
  | .prj i _ inner => collectIdxs (out.insert i) inner
  | .app a b | .lam a b | .all a b => collectIdxs (collectIdxs out a) b
  | .letE _ _ t v b => collectIdxs (collectIdxs (collectIdxs out t) v) b
  | _ => out

def constIdxsExpr (e : Ixon.Expr) : Std.HashSet UInt64 := collectIdxs {} e

/-- The constant references used by every root and sharing entry of a record. -/
def constIdxsOf (c : Ixon.Constant) : Std.HashSet UInt64 :=
  let out := c.sharing.foldl collectIdxs {}
  let ofDefn (acc : Std.HashSet UInt64) (d : Ixon.Definition) := collectIdxs (collectIdxs acc d.typ) d.value
  let ofRecr (acc : Std.HashSet UInt64) (r : Ixon.Recursor) :=
    r.rules.foldl (fun s rule => collectIdxs s rule.rhs) (collectIdxs acc r.typ)
  let ofIndc (acc : Std.HashSet UInt64) (i : Ixon.Inductive) :=
    i.ctors.foldl (fun s ctor => collectIdxs s ctor.typ) (collectIdxs acc i.typ)
  match c.info with
  | .defn d => ofDefn out d
  | .recr r => ofRecr out r
  | .axio a => collectIdxs out a.typ
  | .quot q => collectIdxs out q.typ
  | .muts members => members.foldl (fun acc m => match m with
      | .defn d => ofDefn acc d
      | .indc i => ofIndc acc i
      | .recr r => ofRecr acc r) out
  | _ => out

/-! ## Seeds that use an inert axiom

An inert axiom (`Ix.Kernel.Role.inert`: `sorryAx` and Lean's compiler-trust
axioms) installs nothing and may have no model, so no typing claim certifies
one: IxVM refuses a seed its binding binds to an inert role
(`KernelClaim::assert_claimable`), and refuses any constant whose walk meets a
use of one (`KernelRoles::assert_ref_allowed`). The claim builders therefore
leave out every constant that uses an inert axiom, the axioms themselves
included, as they leave out the constants outside Lean's logic. A constant
left in uses none, and so references none of those left out: an owned set
stays closed under the claim walk. -/

/-- The addresses `env`'s role binding binds to an inert role, under the default
    table when `env` carries no binding (as `withDefaultRoleBinding` binds it); none
    when the binding does not decode. -/
def inertRoleAddrs (env : Ixon.Env) : Std.HashSet Address :=
  let bytes := match env.roleBinding with
    | some b => some b.bytes
    | none => Ix.Kernel.Reader.defaultTableBytes.toOption
  match bytes.bind Ix.Kernel.RoleTable.ofBytes with
  | none => {}
  | some t => t.bound.foldl (fun s (r, a) => if r.inert then s.insert a else s) {}

/-- The walk edges of the record `c`: the references it uses as constants
    (`constIdxsOf`) and, for a projection, its block. These are the edges the
    claim walk follows (`KernelClaim::walk_refs_transitive`; `walk_edges` in
    `crates/ixon/src/shard_claim.rs`). -/
def walkEdges (c : Ixon.Constant) : Array Address := Id.run do
  let used := constIdxsOf c
  let mut out : Array Address := #[]
  for (r, i) in c.refs.zipIdx do
    if used.contains i.toUInt64 then out := out.push r
  match c.info with
  | .iPrj p | .cPrj p => out := out.push p.block
  | .rPrj p | .dPrj p => out := out.push p.block
  | _ => pure ()
  return out

/-- Follow the same edges as `inertUsers` from a single requested seed. Only
stored inert roots count, including when the seed itself is an inert axiom. -/
def reachesInert (env : Ixon.Env) (seed : Address) : Bool := Id.run do
  let roots := (inertRoleAddrs env).filter env.consts.contains
  if roots.isEmpty then return false
  let mut seen : Std.HashSet Address := {}
  let mut todo := #[seed]
  while let some a := todo.back? do
    todo := todo.pop
    if roots.contains a then return true
    if seen.contains a then continue
    seen := seen.insert a
    if let some c := env.getConst? a then todo := todo ++ walkEdges c
  return false

/-- **The constants of `env` that use an inert axiom**: the axioms its binding
    binds to inert roles (`inertRoleAddrs`), Lean 4's native-evaluation
    auxiliary compiler-trust axioms (`Ix.ClaimContext.nativeEvalAxiomAddrs`),
    and every constant whose walk edges reach one, transitively. Empty, without
    a reverse-edge pass over `env`, when it stores none of these axioms. -/
def inertUsers (env : Ixon.Env) : Std.HashSet Address := Id.run do
  let mut rootSet : Std.HashSet Address := Ix.ClaimContext.nativeEvalAxiomAddrs env
  for a in inertRoleAddrs env do
    if env.consts.contains a then
      rootSet := rootSet.insert a
  let roots := rootSet.toArray
  if roots.isEmpty then return {}
  let mut users : Std.HashMap Address (Array Address) := {}
  for (a, lc) in env.consts do
    let some c := lc.get? | continue
    for e in walkEdges c do
      users := users.alter e (fun xs => some ((xs.getD #[]).push a))
  let mut seen : Std.HashSet Address := roots.foldl (·.insert ·) {}
  let mut stack := roots
  repeat
    match stack.back? with
    | none => break
    | some a =>
      stack := stack.pop
      for u in users.getD a #[] do
        unless seen.contains u do
          seen := seen.insert u
          stack := stack.push u
  return seen

/-- `addrs` without the seeds no typing claim may name, in order: those outside
    Lean's logic (`Ixon.Env.dropOutsideLogic`) and those that use an inert axiom
    (`inertUsers`). -/
def dropUnclaimable (env : Ixon.Env) (addrs : Array Address) : Array Address :=
  let inert := inertUsers env
  (env.dropOutsideLogic addrs).filter (!inert.contains ·)

/-- The constants of `env` a typing claim may name, in `env.consts` order: those
    in Lean's logic (`Ixon.Env.inLogicConsts`) that use no inert axiom. -/
def claimableConsts (env : Ixon.Env) : Array Address :=
  let inert := inertUsers env
  env.inLogicConsts.filter (!inert.contains ·)

end IxVM.ClaimHarness
