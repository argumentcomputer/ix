module

public import Tests.Ix.IxVM.BindingAnchors
public import Ix.IxVM.RoleSpecGen

/-! Production claims must validate earlier native operations lazily and check
the bodies of anchors synthesized by native reduction. The original operation
and evidence records remain unchanged in the anchor fixtures. Their new helper
is absent from the consumer's stored reference closure. -/

@[expose] public section

namespace Tests.Ix.IxVM.BindingFrontier

open Ix.Kernel (Role RoleTable)
open BindingAnchors (need address putConstant definition)

private def rebind (env : Ixon.Env) (table : RoleTable) : Except String Ixon.Env := do
  table.check
  let bytes := table.toBytes
  return { env with roleBinding := some ⟨Address.blake3 bytes, bytes⟩ }

structure AnchorFixture where
  env : Ixon.Env
  helper : Address
  anchor : Address

/-- A valid alias and an alias with an ill-typed erased argument reduce to the
same original constructor. Type-only admission cannot distinguish their bodies. -/
def anchorFixture (base : Ixon.Env) (table : RoleTable) (role : Role)
    (illTyped : Bool) : Except String AnchorFixture := do
  let isChar := role == .charOfNat
  need "unsupported native-result anchor" (isChar || role == .boolTrue || role == .boolFalse)
  let refs ← #[Role.nat, if isChar then .char else .bool, role,
    if illTyped then .trueIntro else .natZero].mapM (address table)
  let typ : Ixon.Expr := if isChar then
    .all default default (.ref 0 #[]) (.ref 1 #[]) else .ref 1 #[]
  let original : Ixon.Expr := if isChar then .app (.ref 2 #[]) (.var 1) else .ref 2 #[]
  let erased : Ixon.Expr := .app (.lam default (.ref 0 #[]) original) (.ref 3 #[])
  let value := if isChar then .lam default (.ref 0 #[]) erased else erased
  let (env, helper) := putConstant base (definition typ value refs)
  let (env, anchor) := putConstant env (definition typ (.ref 2 #[]) #[refs[0]!, refs[1]!, helper])
  let replaced : RoleTable := { table with bound := table.bound.map fun (r, key) =>
    (r, if r == role then anchor else key) }
  need "anchor fixture changed evidence" (replaced.evidence == table.evidence)
  need "anchor fixture changed the role count" (replaced.bound.size == Role.all.length)
  return { env := ← rebind env replaced, helper, anchor }

private def theoremClaim (env : Ixon.Env) (refs : Array Address)
    (lhs rhs : Ixon.Expr) (assumed : Bool := false) : Except String (Ixon.Env × Ix.Claim) := do
  -- refs[0..2] are Eq, the carrier and Eq.refl, respectively.
  let typ : Ixon.Expr := .app (.app (.app (.ref 0 #[0]) (.ref 1 #[])) lhs) rhs
  let value : Ixon.Expr := .app (.app (.ref 2 #[0]) (.ref 1 #[])) rhs
  let (env, target) := putConstant env
    ⟨.defn ⟨.thm, .safe, 0, typ, value⟩, #[], refs, #[.succ .zero]⟩
  let context ← Ix.ClaimContext.ofEnv env
  return (env, .check { context with bindingAssumed := assumed } target none)

/-- The stored theorem mentions the original Bool constructor; native Nat.beq
introduces the rebound constructor, whose helper is not a stored dependency. -/
def boolConsumer (env : Ixon.Env) (table : RoleTable) (truth assumed : Bool) :
    Except String (Ixon.Env × Ix.Claim) := do
  let refs ← #[Role.eq, .bool, .eqRefl, .natBeq, .natZero, .natSucc,
    if truth then .boolTrue else .boolFalse].mapM (address table)
  let zero : Ixon.Expr := .ref 4 #[]
  let other : Ixon.Expr := if truth then zero else .app (.ref 5 #[]) zero
  theoremClaim env refs (.app (.app (.ref 3 #[]) zero) other) (.ref 6 #[]) assumed

/-- A multibyte string selects a non-ASCII native Char result. -/
def charConsumer (env : Ixon.Env) (table : RoleTable) (assumed : Bool := false) :
    Except String (Ixon.Env × Ix.Claim) := do
  let text := "aλ".toUTF8
  let codepoint : ByteArray := ⟨#[0xBB, 0x03]⟩
  let textKey := Address.blake3 text
  let codepointKey := Address.blake3 codepoint
  let env := { env with blobs := (env.blobs.insert textKey text).insert codepointKey codepoint }
  let refs ← #[Role.eq, .char, .eqRefl, .stringBack, .charOfNat].mapM (address table)
  theoremClaim env (refs ++ #[textKey, codepointKey])
    (.app (.ref 3 #[]) (.str 5)) (.app (.ref 4 #[]) (.nat 6)) assumed

private def absentFromConsumer (fixture : AnchorFixture) (env : Ixon.Env)
    (claim : Ix.Claim) : Except String Unit := do
  let .check _ target _ := claim | throw "expected a typing claim"
  let closure := IxVM.ClaimHarness.closureFromRoots env #[target]
  need "consumer references the rebound anchor" (!closure.contains fixture.anchor)
  need "consumer references the erased helper" (!closure.contains fixture.helper)

def invalidWfEvidence (base : Ixon.Env) (table : RoleTable) : Except String Ixon.Env := do
  let refs ← #[Role.false, .trueIntro].mapM (address table)
  let (env, proof) := putConstant base
    ⟨.defn ⟨.thm, .safe, 0, .ref 0 #[], .ref 1 #[]⟩, #[], refs, #[]⟩
  let wfRole (role : Role) := (IxVM.RoleSpecGen.equations role).any (!·.1.isEmpty)
  need "fixture has no well-founded evidence" (table.evidence.any fun (role, _) => wfRole role)
  rebind env { table with evidence := table.evidence.map fun (role, entries) =>
    (role, if wfRole role then entries.map (fun _ => .proof proof) else entries) }

structure Case where
  name : String
  env : Ixon.Env
  claim : Ix.Claim
  expectedError : Option String := none
  requiredQuery : Option Lean.Name := none

def cases (base : Ixon.Env) : Except String (Array Case) := do
  let some binding := base.roleBinding | throw "frontier fixture has no role binding"
  let some table := RoleTable.ofBytes binding.bytes | throw "frontier fixture has a malformed table"
  table.check
  need "frontier controls require every role" (table.bound.size == Role.all.length)
  let typeError := "inferred type is not def-eq to the expected type"
  let mut result := #[]
  for role in [Role.boolFalse, .boolTrue, .charOfNat] do
    for illTyped in [false, true] do
      let fixture ← anchorFixture base table role illTyped
      for assumed in [false, true] do
        let (env, claim) ← if role == .charOfNat then charConsumer fixture.env table assumed
          else boolConsumer fixture.env table (role == .boolTrue) assumed
        absentFromConsumer fixture env claim
        result := result.push {
          name := s!"native-{role.leanName}-erased-helper-{illTyped}-assumed-{assumed}"
          env, claim
          expectedError := if illTyped then some typeError else none
          requiredQuery := if illTyped then none else
            some (if role == .charOfNat then `try_str_back else `mk_bool) }
  let (valid, validClaim) ← charConsumer base table
  result := result.push { name := "late-equation-valid-earlier-evidence"
    env := valid, claim := validClaim, requiredQuery := some `try_str_back }
  let invalid ← invalidWfEvidence base table
  let (invalid, invalidClaim) ← charConsumer invalid table
  result := result.push { name := "late-equation-refuses-invalid-earlier-evidence"
    env := invalid, claim := invalidClaim, expectedError := some typeError }
  return result

/-- Every call starts a fresh interpreter and generated executor. Compare the
complete outputs, IO and query counts; negative controls must hit their planted
error, and positive consumers must reach the relevant native constructor. -/
def checks (compiled : Aiur.CompiledToplevel) (base : Ixon.Env)
    (selection : String := "") : IO (Array (String × Bool)) := do
  let some entry := compiled.getFuncIdx `verify_claim | throw (IO.userError "missing verify_claim")
  let mut results := #[]
  for c in ← IO.ofExcept (cases base) do
    if !selection.isEmpty && (c.name.splitOn selection).length == 1 then continue
    IO.println s!"[binding-frontier] checking {c.name}"
    (← IO.getStdout).flush
    let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness c.env c.claim)
    let interpreted ← IO.lazyPure fun _ => compiled.bytecode.execute entry witness.input witness.inputIOBuffer
    let generated ← IO.lazyPure fun _ => compiled.bytecode.executeIxVM entry witness.input witness.inputIOBuffer
    let parity := match interpreted, generated with
      | .error a, .error b => a == b
      | .ok (a, ai, aq), .ok (b, bi, bq) =>
        a == b && ai == bi && aq.size == bq.size &&
          (aq.zip bq).all fun (a, b) => a.uniqueRows == b.uniqueRows && a.totalHits == b.totalHits
      | _, _ => false
    results := results.push (s!"{c.name}: interpreter/generated parity", parity)
    match interpreted with
    | .ok (_, _, counts) =>
      results := results.push (s!"{c.name}: accepted", c.expectedError.isNone)
      if let some name := c.requiredQuery then
        let some query := compiled.getFuncIdx name | throw (IO.userError s!"missing {name}")
        results := results.push (s!"{c.name}: native result exercised",
          (counts[query]?.map fun count => decide (count.uniqueRows > 0)).getD false)
    | .error error =>
      let expected := c.expectedError.any fun fragment => (error.splitOn fragment).length > 1
      results := results.push (s!"{c.name}: rejected ({error})", expected)
  if results.isEmpty then throw (IO.userError s!"no frontier controls selected by '{selection}'")
  return results

def defaultChecks (compiled : Aiur.CompiledToplevel) : IO (Array (String × Bool)) := do
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let base ← IO.ofExcept (IxVM.ClaimHarness.withRoleTable {} table.toBytes)
  checks compiled base

end Tests.Ix.IxVM.BindingFrontier
