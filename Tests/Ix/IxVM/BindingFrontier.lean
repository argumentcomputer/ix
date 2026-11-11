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

def rebind (env : Ixon.Env) (table : RoleTable) : Except String Ixon.Env := do
  table.check
  let bytes := table.toBytes
  return { env with roleBinding := some ⟨Address.blake3 bytes, bytes⟩ }

structure AnchorFixture where
  env : Ixon.Env
  helper : Address
  anchor : Address

/-- A valid alias and an alias with an ill-typed erased argument reduce to the
same original constructor. Type-only admission cannot distinguish their bodies. -/
def anchorFixture (base : Ixon.Env) (table : RoleTable)
    (illTyped : Bool) : Except String AnchorFixture := do
  let refs ← #[Role.nat, .char, .charOfNat,
    if illTyped then .trueIntro else .natZero].mapM (address table)
  let typ : Ixon.Expr := .all default default (.ref 0 #[]) (.ref 1 #[])
  let original : Ixon.Expr := .app (.ref 2 #[]) (.var 1)
  let erased : Ixon.Expr := .app (.lam default (.ref 0 #[]) original) (.ref 3 #[])
  let value := .lam default (.ref 0 #[]) erased
  let (env, helper) := putConstant base (definition typ value refs)
  let (env, anchor) := putConstant env (definition typ (.ref 2 #[]) #[refs[0]!, refs[1]!, helper])
  let replaced : RoleTable := { table with bound := table.bound.map fun (r, key) =>
    (r, if r == .charOfNat then anchor else key) }
  need "anchor fixture changed evidence" (replaced.evidence == table.evidence)
  need "anchor fixture changed the role count" (replaced.bound.size == Role.all.length)
  return { env := ← rebind env replaced, helper, anchor }

def theoremClaim (env : Ixon.Env) (refs : Array Address)
    (lhs rhs : Ixon.Expr) (assumed : Bool := false) : Except String (Ixon.Env × Ix.Claim) := do
  -- refs[0..2] are Eq, the carrier and Eq.refl, respectively.
  let typ : Ixon.Expr := .app (.app (.app (.ref 0 #[0]) (.ref 1 #[])) lhs) rhs
  let value : Ixon.Expr := .app (.app (.ref 2 #[0]) (.ref 1 #[])) rhs
  let (env, target) := putConstant env
    ⟨.defn ⟨.thm, .safe, 0, typ, value⟩, #[], refs, #[.succ .zero]⟩
  let context ← Ix.ClaimContext.ofEnv env
  return (env, .check { context with bindingAssumed := assumed } target none)

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

def absentFromConsumer (fixture : AnchorFixture) (env : Ixon.Env)
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
  let mut result : Array Case := #[]
  for illTyped in [false, true] do
    let fixture ← anchorFixture base table illTyped
    for assumed in [false, true] do
      let (env, claim) ← charConsumer fixture.env table assumed
      absentFromConsumer fixture env claim
      result := result.push {
        name := s!"native-Char.ofNat-erased-helper-{illTyped}-assumed-{assumed}"
        env, claim
        expectedError := if illTyped then some typeError else none
        -- `String.back` (B3) is no longer native (REMOVED-MOVES.md): the verdicts are the test.
        requiredQuery := none }
  let (valid, validClaim) ← charConsumer base table
  result := result.push {
    name := "late-equation-valid-earlier-evidence"
    env := valid, claim := validClaim }
  let invalid ← invalidWfEvidence base table
  let (invalid, invalidClaim) ← charConsumer invalid table
  result := result.push {
    name := "late-equation-refuses-invalid-earlier-evidence"
    env := invalid, claim := invalidClaim, expectedError := some typeError }
  return result

/-- The cases as claims to the IxVM program: negative controls must hit their
planted error, and positive consumers must reach the native constructor. -/
def claimCases (base : Ixon.Env) : Except String (Array Tests.Ix.IxVM.Builder) := do
  return (← cases base).map fun c _ => do
    let case ← Tests.Ix.IxVM.Case.ofClaim s!"binding frontier {c.name}" c.env c.claim {}
      c.expectedError.isNone c.expectedError
    return { case with exercises := c.requiredQuery.map fun n => s!"KernelNatPrim::{n}" }

def run : IO UInt32 := do
  let table ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let base ← IO.ofExcept (IxVM.ClaimHarness.withRoleTable {} table.toBytes)
  Tests.Ix.IxVM.runCases "ixvm-binding-frontier" (← IO.ofExcept (claimCases base))

end Tests.Ix.IxVM.BindingFrontier
