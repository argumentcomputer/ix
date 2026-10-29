module

public import Ix.IxVM.ClaimHarness
public import Ix.Aiur.Compiler

/-! Type-only binding anchors defer body checking to consumers. These fixtures
leave every original operation and proof record untouched, while an Int.negSucc
alias uses a helper with either a valid or an ill-typed erased argument. Native
negative results must check the synthesized constructor reference, including
when the consuming claim assumes its binding. -/

@[expose] public section

namespace Tests.Ix.IxVM.BindingAnchors

open Ix.Kernel (Role RoleTable)

def need (label : String) (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error label

def address (table : RoleTable) (role : Role) : Except String Address :=
  match table.bound.find? (·.1 == role) with
  | some (_, value) => pure value
  | none => throw s!"missing role {role.leanName}"

def putConstant (env : Ixon.Env) (constant : Ixon.Constant) : Ixon.Env × Address :=
  let key := Address.blake3 (Ixon.ser constant)
  let env := env.storeConst key constant
  ({ env with anonHints := env.anonHints.insert key .opaque }, key)

def definition (typ value : Ixon.Expr) (refs : Array Address) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, typ, value⟩, #[], refs, #[]⟩

structure Fixture where
  env : Ixon.Env
  helper : Address
  anchor : Address

def fixture (base : Ixon.Env) (table : RoleTable) (illTyped : Bool) : Except String Fixture := do
  let nat ← address table .nat
  let int ← address table .int
  let original ← address table .intNegSucc
  let discarded ← address table (if illTyped then .trueIntro else .natZero)
  let typ : Ixon.Expr := .all default default (.ref 0 #[]) (.ref 1 #[])
  let value : Ixon.Expr := .lam default (.ref 0 #[])
    (.app (.lam default (.ref 0 #[]) (.app (.ref 2 #[]) (.var 1))) (.ref 3 #[]))
  let (env, helper) := putConstant base (definition typ value #[nat, int, original, discarded])
  let (env, anchor) := putConstant env (definition typ (.ref 2 #[]) #[nat, int, helper])
  let replaced : RoleTable := { table with bound := table.bound.map fun (role, key) =>
    (role, if role == Role.intNegSucc then anchor else key) }
  need "proof evidence changed" (replaced.evidence == table.evidence)
  need "role count changed" (replaced.bound.size == Role.all.length)
  replaced.check
  let bytes := replaced.toBytes
  let env := { env with roleBinding := some ⟨Address.blake3 bytes, bytes⟩ }
  let mut roots := table.bound.filterMap fun (role, key) =>
    match role.spec (md := .anon) with
    | .ops .. | .eqns .. => some key
    | _ => none
  for (_, evidence) in table.evidence do
    for entry in evidence do
      if let .proof key := entry then roots := roots.push key
  let closure := IxVM.ClaimHarness.closureFromRoots env roots
  need "the new anchor occurs in an original operation/proof closure" (!closure.contains anchor)
  need "the new helper occurs in an original operation/proof closure" (!closure.contains helper)
  return { env, helper, anchor }

def bindingClaim (env : Ixon.Env) : Except String Ix.Claim := do
  let context ← Ix.ClaimContext.ofEnv env
  return .binding context.spec context.binding

def helperClaim (fixture : Fixture) : Except String Ix.Claim := do
  return .check (← Ix.ClaimContext.ofEnv fixture.env) fixture.helper none

/-- A valid original theorem whose native reduction synthesizes the rebound
constructor. The helper/alias are absent from its original reference closure. -/
def consumer (table : RoleTable) (fixture : Fixture) (assumed : Bool) :
    Except String (Ixon.Env × Ix.Claim) := do
  let refs ← #[Role.eq, .int, .intNeg, .intOfNat, .natSucc, .natZero,
    .intNegSucc, .eqRefl].mapM (address table)
  let one : Ixon.Expr := .app (.ref 4 #[]) (.ref 5 #[])
  let lhs : Ixon.Expr := .app (.ref 2 #[]) (.app (.ref 3 #[]) one)
  let rhs : Ixon.Expr := .app (.ref 6 #[]) (.ref 5 #[])
  let typ : Ixon.Expr := .app (.app (.app (.ref 0 #[0]) (.ref 1 #[])) lhs) rhs
  let value : Ixon.Expr := .app (.app (.ref 7 #[0]) (.ref 1 #[])) rhs
  let proofRecord : Ixon.Constant := ⟨.defn ⟨.thm, .safe, 0, typ, value⟩,
    #[], refs, #[.succ .zero]⟩
  let (env, target) := putConstant fixture.env proofRecord
  let closure := IxVM.ClaimHarness.closureFromRoots env #[target]
  need "consumer directly references the new anchor" (!closure.contains fixture.anchor)
  need "consumer directly references the new helper" (!closure.contains fixture.helper)
  let context ← Ix.ClaimContext.ofEnv env
  return (env, .check { context with bindingAssumed := assumed } target none)

structure Case where
  name : String
  env : Ixon.Env
  claim : Ix.Claim
  expectAccept : Bool
  requireNativeInt : Bool := false

def cases (base : Ixon.Env) : Except String (Array Case) := do
  let some binding := base.roleBinding | throw "fixture environment has no binding"
  let some table := RoleTable.ofBytes binding.bytes | throw "malformed fixture binding"
  table.check
  need "consumer fixtures require a complete binding" (table.bound.size == Role.all.length)
  let good ← fixture base table false
  let bad ← fixture base table true
  let goodHelper ← helperClaim good
  let badHelper ← helperClaim bad
  let mut result := #[
    { name := "binding-anchor-valid-helper", env := good.env,
      claim := goodHelper, expectAccept := true : Case },
    { name := "binding-anchor-invalid-helper", env := bad.env,
      claim := badHelper, expectAccept := false : Case }]
  for assumed in [false, true] do
    for (label, value, accept) in [("valid", good, true), ("invalid", bad, false)] do
      let (env, claim) ← consumer table value assumed
      let entry : Case := {
        name := s!"binding-anchor-{label}-consumer-assumed-{assumed}"
        env := env
        claim := claim
        expectAccept := accept
        requireNativeInt := accept }
      result := result.push entry
  return result

/-- Focused consumer checks with exact backend parity. Successful native
controls must reach the constructor builder; failures must be the planted
type error, not missing witness data or another setup error. -/
def checks (compiled : Aiur.CompiledToplevel) (base : Ixon.Env) : IO (Array (String × Bool)) := do
  let some entry := compiled.getFuncIdx `verify_claim | throw (IO.userError "missing verify_claim")
  let some nativeInt := compiled.getFuncIdx `mk_int_prim | throw (IO.userError "missing mk_int_prim")
  let mut result := #[]
  for c in ← IO.ofExcept (cases base) do
    let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness c.env c.claim)
    let interpreted ← IO.lazyPure fun _ =>
      compiled.bytecode.execute entry witness.input witness.inputIOBuffer
    let generated ← IO.lazyPure fun _ =>
      compiled.bytecode.executeIxVM entry witness.input witness.inputIOBuffer
    let parity := match interpreted, generated with
      | .error a, .error b => a == b
      | .ok (a, ai, aq), .ok (b, bi, bq) =>
        a == b && ai == bi && aq.size == bq.size &&
          (aq.zip bq).all fun (a, b) => a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits
      | _, _ => false
    result := result.push (s!"{c.name}: interpreter/generated parity", parity)
    match interpreted with
    | .ok (_, _, counts) =>
      result := result.push (s!"{c.name}: accepted", c.expectAccept)
      if c.requireNativeInt then
        result := result.push (s!"{c.name}: native constructor path exercised",
          (counts[nativeInt]?.map fun count => decide (count.uniqueRows > 0)).getD false)
    | .error error =>
      let isTypeError := (error.splitOn "inferred type is not def-eq to the expected type").length > 1
      result := result.push (s!"{c.name}: rejected ({error})", !c.expectAccept && isTypeError)
  return result

def defaultChecks (compiled : Aiur.CompiledToplevel) : IO (Array (String × Bool)) := do
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let base ← IO.ofExcept (IxVM.ClaimHarness.withRoleTable {} table.toBytes)
  checks compiled base

end Tests.Ix.IxVM.BindingAnchors
