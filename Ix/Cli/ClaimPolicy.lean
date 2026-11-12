module
public import Cli
public import Ix.ClaimContext

/-! # The conditional claims `ix verify` and `ix compress` accept by default

A verified proof establishes its claim, and a claim can be conditional. The
IxVM consistency theorem (`IxVM.consistent`'s `InScope`) covers `check` and
`checkEnv` claims that validate their binding, with no user axioms and no
assumed leaves. By default these commands refuse a claim

- that depends on axioms beyond the standard three (`--allow-axioms`);
- that assumes its role binding meets the specifications instead of validating
  it, where no binding proof discharges that (`--allow-assumed-binding`);
- that is conditional on typing assumptions, the assumed leaves another proof
  must discharge (`--allow-assumptions`).

Claims that state no typing (`reveal`, `contains`, `resource`, `binding`) are not
restricted. A catalog is admitted when each of its members is. -/

public section

namespace Ix.Cli.ClaimPolicy

/-- Which conditional claims a command accepts. -/
structure Policy where
  axioms : Bool := false
  assumedBinding : Bool := false
  assumptions : Bool := false
  deriving Repr, Inhabited

/-- The policy the command line selects. -/
def ofParsed (p : Cli.Parsed) : Policy where
  axioms := p.hasFlag "allow-axioms"
  assumedBinding := p.hasFlag "allow-assumed-binding"
  assumptions := p.hasFlag "allow-assumptions"

/-- A typing claim's assumptions (assumed leaves). -/
def assumptionsOf : Ix.Claim → Option Address
  | .eval _ _ _ a | .check _ _ a | .checkEnv _ _ a => a
  | _ => none

/-- Why `pol` refuses `claim`, if it does. `bindingDischarged`: a verified binding
proof discharges the claim's assumed binding; `assumptionsDischarged`: the proofs
verified with it own every assumed leaf (a whole shard partition). -/
def refusal (pol : Policy) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) : Except String (Option String) := do
  let some ctx := Ix.Claim.context? claim | return none
  if !pol.axioms then
    if let some ax := ctx.axioms then
      return some s!"the claim depends on the user axioms {ax}; pass --allow-axioms to accept it"
  if !pol.assumedBinding && ctx.bindingAssumed && !bindingDischarged then
    return some s!"the claim assumes its role binding {ctx.binding} meets the specifications; \
      verify a binding proof with it, or pass --allow-assumed-binding to accept it"
  if !pol.assumptions && !assumptionsDischarged then
    if let some root := assumptionsOf claim then
      return some s!"the claim is conditional on the typing assumptions {root}; \
        pass --allow-assumptions to accept it"
  return none

/-- Refuse `claim` (an error) unless the command line's policy admits it. -/
def admit (p : Cli.Parsed) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) : IO Unit := do
  if let some why ← IO.ofExcept
      (refusal (ofParsed p) claim bindingDischarged assumptionsDischarged) then
    throw (IO.userError s!"refused: {why}")

end Ix.Cli.ClaimPolicy

end
