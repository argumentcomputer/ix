import Ix.IxVM.RoleSpecGen

open Ix.Kernel IxVM.RoleSpecGen

private def need (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Reordered fixtures still satisfy the coverage, dependency order, and
tail conditions that precede the validation-frontier check. -/
private def priorOrderValid (ordered : List (List Role)) : Bool := Id.run do
  let flat := ordered.flatten
  unless flat.length == Role.all.length && Role.all.all flat.contains do return false
  let index (role : Role) := (ordered.findIdx? (·.contains role)).getD ordered.length
  let some first := ordered.findIdx? tailOnly | return false
  return ordered.zipIdx.all fun (group, i) =>
    group.all (fun role => Role.block role == group) &&
    (groupNeeds group).all (fun role => decide (index role < i)) &&
    ((tailOnly group || (groupNeeds group).any (fun role => decide (first ≤ index role))) ==
      decide (first ≤ i))

def main : IO UInt32 := do
  need "current role groups and generated references agree" checkGroups.isOk
  let firstWf ← IO.ofExcept firstWellFoundedGroup
  let firstEquation ← IO.ofExcept firstEquationGroup
  need "current order meets the original coverage and tail conditions" (priorOrderValid groups)
  let equationGroup := groups[firstEquation]!
  let withoutEquation := groups.filter (· != equationGroup)
  let equationBeforeWf := withoutEquation.take firstWf ++ [equationGroup] ++
    withoutEquation.drop firstWf
  let lastWf := groups[firstEquation - 1]!
  let withoutLastWf := groups.filter (· != lastWf)
  let wfAfterEquation := withoutLastWf.take firstEquation ++ [lastWf] ++
    withoutLastWf.drop firstEquation
  for (label, mutant) in [("equation before the WF block", equationBeforeWf),
      ("WF group after the first equation", wfAfterEquation)] do
    need s!"{label}: original ordering conditions still hold" (priorOrderValid mutant)
    need s!"{label}: the validation-frontier invariant refuses it"
      (!(firstEquationGroup mutant).isOk)
  let group := Role.block .intNegOfNat
  let needs := groupNeeds group
  let terms := closedSpecTerms .intNegOfNat
  need "complete dependencies pass" (checkReferenceGroups group needs terms).isOk
  need "removing Eq is detected through the generated statement"
    (!(checkReferenceGroups group (needs.filter (· != .eq)) terms).isOk)
  need "removing the Int group is detected"
    (!(checkReferenceGroups group (needs.filter (· != .int)) terms).isOk)
  let reference : Expr .anon := .const (.role .intNegSucc) []
  need "a dependency member covers its complete group"
    (checkReferenceGroups group [.intOfNat] [reference]).isOk
  need "same-group references are allowed"
    (checkReferenceGroups (Role.block .int) [] [reference]).isOk
  let projection : Expr .anon := .proj (.role .intNegSucc) 0 (.sort .zero)
  need "projection-head dependencies cannot be omitted"
    (!(checkReferenceGroups group [] [projection]).isOk)
  need "declared projection-head dependency passes"
    (checkReferenceGroups group [.int] [projection]).isOk
  IO.println "generated specification dependency and validation-frontier mutants passed"
  return 0
