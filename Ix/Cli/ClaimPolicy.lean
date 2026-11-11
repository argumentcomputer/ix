module
public import Cli
public import Ix.ClaimContext
public import Ix.Cli.TableAdmission

/-! # The conditional claims `ix verify` and `ix compress` accept by default

A verified proof establishes its claim, and a claim can be conditional. The
IxVM consistency theorem (`IxVM.consistent`'s `InScope`) covers `check` and
`checkEnv` claims that validate their binding, with no user axioms and no
assumed leaves, under the default role table or a role table the kernel admits.
By default these commands refuse a claim

- relative to a role binding other than the default role table that the kernel
  does not admit here (`Ix.Cli.TableAdmission`), or to a literal class
  (`--allow-custom-binding`);
- that depends on axioms beyond the standard three (`--allow-axioms`);
- that assumes its role binding meets the specifications instead of validating
  it, where no binding proof discharges that (`--allow-assumed-binding`);
- that is conditional on typing assumptions, the assumed leaves another proof
  must discharge (`--allow-assumptions`).

Claims that state no typing (`reveal`, `contains`, `resource`, `binding`) are not
restricted. A catalog is admitted when each of its members is.

The consistency theorem covers a claim under the default role table or under a
role table the kernel admits. The circuit does not establish the second, so
`admit` runs the kernel's admission of a claim's table (`Ix.Cli.TableAdmission`)
and relaxes the `customBinding` test of `refusal` only when it succeeds. -/

public section

namespace Ix.Cli.ClaimPolicy

/-- Which conditional claims a command accepts. -/
structure Policy where
  customBinding : Bool := false
  axioms : Bool := false
  assumedBinding : Bool := false
  assumptions : Bool := false
  deriving Repr, Inhabited

/-- The policy the command line selects. -/
def ofParsed (p : Cli.Parsed) : Policy where
  customBinding := p.hasFlag "allow-custom-binding"
  axioms := p.hasFlag "allow-axioms"
  assumedBinding := p.hasFlag "allow-assumed-binding"
  assumptions := p.hasFlag "allow-assumptions"

/-- A typing claim's assumptions (assumed leaves). -/
def assumptionsOf : Ix.Claim → Option Address
  | .eval _ _ _ a | .check _ _ a | .checkEnv _ _ a => a
  | _ => none

/-- Why `pol` refuses `claim`, if it does. `bindingDischarged`: a verified binding
proof discharges the claim's assumed binding; `assumptionsDischarged`: the proofs
verified with it own every assumed leaf (a whole shard partition);
`tableAdmitted`: the kernel admits the claim's role table
(`Ix.Cli.TableAdmission.standing`), which a literal class never is. -/
def refusal (pol : Policy) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (tableAdmitted : Bool := false) :
    Except String (Option String) := do
  let some ctx := Ix.Claim.context? claim | return none
  let default ← Ix.Kernel.Reader.defaultTableAddress
  if !pol.customBinding && !(tableAdmitted && !ctx.literalClass) &&
      (ctx.literalClass || ctx.binding != default) then
    let what := if ctx.literalClass then s!"the literal class {ctx.binding}"
      else s!"the role binding {ctx.binding}"
    return some s!"the claim is relative to {what}, not the default role table {default}; \
      pass --allow-custom-binding to accept it"
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

/-- Refuse `claim` (an error) unless the command line's policy admits it. A claim
under a role table other than the default one is admitted without
`--allow-custom-binding` when the kernel admits the table
(`Ix.Cli.TableAdmission.standing`) over `envs` or the environment
`--binding-env` names; the environments are read only if the table needs them. -/
def admit (p : Cli.Parsed) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (envs : IO (List Ixon.Env) := pure []) :
    IO Unit := do
  let pol := ofParsed p
  let mut tableAdmitted := false
  let mut unestablished : Option String := none
  if let some ctx := Ix.Claim.context? claim then
    unless pol.customBinding do
      match ← TableAdmission.standing ctx (TableAdmission.withSupplied p envs) with
      | .default => pure ()
      | .admitted recorded =>
        tableAdmitted := true
        IO.eprintln s!"role table {ctx.binding}: admitted by the kernel\
          {if recorded then " (recorded by an earlier run)" else ""}"
      | .unestablished why => unestablished := some why
  if let some why ← IO.ofExcept
      (refusal pol claim bindingDischarged assumptionsDischarged tableAdmitted) then
    let detail := match unestablished with
      | some reason => s!" (the kernel's admission of the table is not established: {reason})"
      | none => ""
    throw (IO.userError s!"refused: {why}{detail}")

end Ix.Cli.ClaimPolicy

end
