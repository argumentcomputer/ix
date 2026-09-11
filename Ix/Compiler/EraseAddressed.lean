import Ix.Compiler.Erase
import Ix.Compiler.IxIR0.Readdress

/-!
# Artifact-facing addressed erasure

The proof-facing eraser still emits transient mutual-member keys.  This module
preserves that exact intermediate result, records constant boundaries, and
then applies the certified whole-IxIR₀ block readdresser.  It is the migration
seam for later evaluator transport and pipeline adoption; no existing erasure
theorem is weakened or silently retargeted.
-/

namespace Ix.Compiler.EraseAddressed

open Ix.Compiler.Ixon (Address Constant ConstantInfo)

inductive Error where
  | erase (error : Erase.EraseErr)
  | readdress (message : String)
  deriving Repr

/-- Erase each source constant while retaining whether its output is one
stable group or one mutual block. -/
def eraseGroups (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant))
    (fuel : Nat := Erase.defaultFuel) :
    Except Error (List IxIR0.Readdress.Group) := do
  let mut groups := []
  for (address, constant) in consts do
    let entries ←
      match Erase.eraseConstant ctx address constant fuel with
      | .ok entries => pure entries
      | .error error => throw (.erase error)
    let group :=
      match constant.info with
      | .muts _ => IxIR0.Readdress.Group.mutual entries
      | _ => IxIR0.Readdress.Group.stable entries
    groups := groups ++ [group]
  return groups

/-- Complete artifact-facing erasure result. `raw` is exactly the old eraser
output; `addressed` is its collision-checked block-address image. -/
structure Result where
  raw : List (Address × IxIR0.Decl)
  groups : List IxIR0.Readdress.Group
  addressed : IxIR0.Readdress.Result

namespace Result

def addressMap (result : Result) : IxIR0.MutualBlock.Renaming :=
  result.addressed.addressMap

def declarations (result : Result) : List (Address × IxIR0.Decl) :=
  result.addressed.declarations

def main (result : Result) : IxIR0.Expr :=
  result.addressed.main

/-- Executable bridge pinning both seams: group flattening equals the existing
eraser's exact output, and the addressed result is the certified image of
that grouping. -/
def semanticAudit (result : Result) (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr)
    (fuel : Nat) : Bool :=
  result.raw == IxIR0.Readdress.rawDeclarations result.groups &&
    (match Erase.eraseProgram ctx consts fuel with
    | .ok raw => raw == result.raw
    | .error _ => false) &&
    result.addressed.semanticAudit (consts.map (·.1)) result.groups main

end Result

abbrev CertifiedResult (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr) (fuel : Nat) :=
  { result : Result // result.semanticAudit ctx consts main fuel = true }

private def certify (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr) (fuel : Nat)
    (result : Result) : Except Error (CertifiedResult ctx consts main fuel) :=
  if haudit : result.semanticAudit ctx consts main fuel then
    .ok ⟨result, haudit⟩
  else
    .error (.readdress
      "internal: addressed erasure failed its exact-output audit")

/-- Run the existing eraser, then readdress every `.muts` output as a
cycle-safe block. Every source constant address is protected, including the
Ixon identity of each mutual block. -/
def runCertified (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr)
    (fuel : Nat := Erase.defaultFuel) :
    Except Error (CertifiedResult ctx consts main fuel) := do
  let groups ← eraseGroups ctx consts fuel
  let raw := IxIR0.Readdress.rawDeclarations groups
  let addressed ←
    match IxIR0.Readdress.run (consts.map (·.1)) groups main with
    | .ok result => pure result
    | .error message => throw (.readdress message)
  certify ctx consts main fuel { raw, groups, addressed }

/-- Artifact-facing projection of `runCertified`. -/
def run (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr)
    (fuel : Nat := Erase.defaultFuel) : Except Error Result := do
  return (← runCertified ctx consts main fuel).1

/-- Proof-facing execution record for addressed erasure.  The ordinary API
returns the same `Result`; this companion retains the exact successful run
equation needed to compose the validator and lowering simulations. -/
structure RunTrace (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr)
    (fuel : Nat) where
  result : Result
  runEq : run ctx consts main fuel = .ok result

/-- Execute addressed erasure once and retain its successful equation. -/
def runWithTrace (ctx : Erase.EraseCtx)
    (consts : List (Address × Constant)) (main : IxIR0.Expr)
    (fuel : Nat := Erase.defaultFuel) :
    Except Error (RunTrace ctx consts main fuel) :=
  match hrun : run ctx consts main fuel with
  | .error error => .error error
  | .ok result => .ok { result, runEq := hrun }

/-- Successful addressed erasure retains the exact-output/address-image
audit. -/
theorem semanticAudit_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {fuel : Nat} {result : Result}
    (hrun : run ctx consts main fuel = .ok result) :
    result.semanticAudit ctx consts main fuel = true := by
  unfold run at hrun
  cases hcertified : runCertified ctx consts main fuel with
  | error error =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2

end Ix.Compiler.EraseAddressed
