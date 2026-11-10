module
public import Ix.Claim
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

/-- The `refs` indices `e` uses as a CONSTANT: `Ref i` and the type index
    of `Prj i`. -/
partial def constIdxsExpr : Ixon.Expr → Std.HashSet UInt64
  | .ref i _ => {i}
  | .prj i _ inner => (constIdxsExpr inner).insert i
  | .app a b | .lam _ a b | .all _ _ a b =>
    (constIdxsExpr a).union (constIdxsExpr b)
  | .letE _ t v b =>
    ((constIdxsExpr t).union (constIdxsExpr v)).union (constIdxsExpr b)
  | _ => {}

/-- The `refs` indices `c` uses as constants, over its `sharing` table and
    every Expr its `ConstantInfo` carries. -/
def constIdxsOf (c : Ixon.Constant) : Std.HashSet UInt64 := Id.run do
  let mut out : Std.HashSet UInt64 := {}
  for e in c.sharing do
    out := out.union (constIdxsExpr e)
  let ofDefn (d : Ixon.Definition) := (constIdxsExpr d.typ).union (constIdxsExpr d.value)
  let ofRecr (r : Ixon.Recursor) := r.rules.foldl
    (fun acc rule => acc.union (constIdxsExpr rule.rhs)) (constIdxsExpr r.typ)
  let ofIndc (i : Ixon.Inductive) := i.ctors.foldl
    (fun acc ctor => acc.union (constIdxsExpr ctor.typ)) (constIdxsExpr i.typ)
  match c.info with
  | .defn d => out := out.union (ofDefn d)
  | .recr r => out := out.union (ofRecr r)
  | .axio a => out := out.union (constIdxsExpr a.typ)
  | .quot q => out := out.union (constIdxsExpr q.typ)
  | .muts members =>
    for m in members do
      out := out.union <| match m with
        | .defn d => ofDefn d
        | .indc i => ofIndc i
        | .recr r => ofRecr r
  | _ => pure ()
  return out

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

/-- **The constants of `env` that use an inert axiom**: the axioms its binding
    binds to inert roles, and every constant whose walk edges reach one,
    transitively. Empty, without a pass over `env`, when it stores none of the
    inert axioms. -/
def inertUsers (env : Ixon.Env) : Std.HashSet Address := Id.run do
  let roots := (inertRoleAddrs env).toArray.filter env.consts.contains
  if roots.isEmpty then return {}
  let mut users : Std.HashMap Address (Array Address) := {}
  for (a, lc) in env.consts do
    let some c := lc.get? | continue
    for e in walkEdges c do
      users := if users.contains e then users.modify e (·.push a) else users.insert e #[a]
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
