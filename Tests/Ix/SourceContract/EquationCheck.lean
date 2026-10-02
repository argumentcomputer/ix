import Tests.Ix.SourceContract.EquationFixture
import Ix.Compile.Equations
import Ix.Compile.SourceContract.Transport

/-! Unfolding equations carry their definition's header input contracts (R1
amendment): the realized `f.eq_def` statement binder at each annotated
position, and the proof's matching lambda, transport with the definition's
input contract; contracts written inside the body reach the statement as
before; definitions without header contracts are unchanged. -/

open Lean Ix.Compile

namespace Tests.Ix.SourceContract.EquationCheck

/-- The semantic contract codes attached along a telescope of `kind`
(`1` for foralls, `0` for lambdas): `(position, code)` per decorated binder. -/
partial def telescopeCodes (kind : Nat) (expr : Expr) (position : Nat := 0) :
    List (Nat × Nat) :=
  match expr with
  | .mdata data inner =>
    let here := if (Ix.SemanticContract.leanFields data).isEmpty then [] else
      match data.getNat `ix.contract.kind 99, data.getNat `ix.contract.code 999 with
      | k, code => if k == kind then [(position, code)] else []
    here ++ telescopeCodes kind inner position
  | .forallE _ _ body _ => if kind == 1 then telescopeCodes kind body (position + 1) else []
  | .lam _ _ body _ => if kind == 0 then telescopeCodes kind body (position + 1) else []
  | _ => []

def hasLetContract (expr : Expr) : Bool :=
  (expr.find? fun
    | .mdata data (.letE ..) => data.getNat `ix.contract.kind 99 == 2
    | _ => false).isSome

end Tests.Ix.SourceContract.EquationCheck

open Tests.Ix.SourceContract.EquationCheck in
run_cmd do
  let root := `Tests.Ix.SourceContract.EquationFixture
  let definitions := #[root ++ `revAccU, root ++ `countdownWF, root ++ `withLet,
    `List.length]
  let found ← Lean.Elab.Command.liftTermElabM do
    definitions.filterMapM fun definition => do
      let some equation ← Meta.getUnfoldEqnFor? definition | return none
      return some ({ definition, equation } : Ix.Compile.Equations.Association)
  unless found.size == 4 do throwError "expected four unfolding equations, got {found.size}"
  let (env, carried, failed) := Ix.Compile.Equations.carryContracts (← getEnv) found
  unless failed.isEmpty do throwError "contracts were not carried: {failed}"
  let unique : Ixon.ValueContract := .unique
  let expected : List (Name × List (Nat × Ixon.Uses × Ixon.ValueContract)) := [
    (root ++ `revAccU, [(1, .many, unique)]),
    (root ++ `countdownWF, [(1, .erased, .shared)]),
    (root ++ `withLet, [(1, .many, unique)]),
    (`List.length, [])]
  for (definition, contracts) in expected do
    let some a := carried.find? (·.definition == definition)
      | throwError "no association for {definition}"
    let actual := a.contracts.toList.map fun c => (c.position, c.uses, c.value)
    unless actual == contracts do
      throwError "{definition}: carried {repr actual}, expected {repr contracts}"
    let some info := env.find? a.equation | throwError "missing {a.equation}"
    let input ← match compileInputFromEnv env [(a.equation, info)] with
      | .ok input => pure input
      | .error error => throwError "{a.equation} does not export: {error}"
    let prepared ← match input.prepare with
      | .ok prepared => pure prepared
      | .error error => throwError "{a.equation} does not transport: {error}"
    let some (_, decorated) := prepared.head? | throwError "nothing transported"
    -- Statement binders carry the input contract with a shared result.
    let statement := telescopeCodes 1 decorated.type
    let want := contracts.map fun (p, uses, value) =>
      (p, (Ixon.packAllContract ⟨uses, value⟩ .shared).toNat)
    unless statement == want do
      throwError "{a.equation}: statement contracts {statement}, expected {want}"
    -- The proof's matching lambdas carry the same input contract.
    let some proof := sourceBody? decorated | throwError "{a.equation} has no proof"
    let lambdas := (telescopeCodes 0 proof).filter fun (p, _) => contracts.any (·.1 == p)
    let wantLambdas := contracts.map fun (p, uses, value) =>
      (p, (Ixon.BinderContract.toBits ⟨uses, value⟩).toNat)
    unless lambdas == wantLambdas do
      throwError "{a.equation}: proof contracts {lambdas}, expected {wantLambdas}"
    -- A contract written inside the body reaches the statement.
    if definition == root ++ `withLet && !hasLetContract decorated.type then
      throwError "the body's linear let did not reach {a.equation}'s statement"
  pure ()
