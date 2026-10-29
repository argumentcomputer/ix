import Ix.IxVM.RoleSpecGen

open Ix.Kernel IxVM.RoleSpecGen

private def need (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

def main : IO UInt32 := do
  need "current role groups and generated references agree" checkGroups.isOk
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
  IO.println "generated specification dependency checks and omission mutants passed"
  return 0
