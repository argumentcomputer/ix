module
public import Cli
public import Ix.ClaimContext
public import Ix.Cli.TableAdmission

/-! # The claims `ix verify` and `ix compress` accept by default

A verified proof establishes its claim, and a claim can be conditional or state
something other than typing. The IxVM consistency theorem (`IxVM.consistent`'s
`InScope`) covers `check` and `checkEnv` claims that validate their binding, with
no user axioms and no assumed leaves, under the default role table or a role table
the kernel admits. These commands accept the typing claims (`eval`, `check`,
`checkEnv`), and by default refuse one

- that names another specification set than this build's. No flag accepts it:
  the circuit pins the digest, so a mismatch means that this build and the
  artifact the proof was made with disagree;
- relative to a role binding other than the default role table that the kernel
  does not admit here (`Ix.Cli.TableAdmission`), or to a literal class
  (`--allow-custom-binding`);
- that depends on axioms beyond the standard three (`--allow-axioms`);
- that assumes its role binding meets the specifications instead of validating
  it, where no binding proof discharges that (`--allow-assumed-binding`);
- that is conditional on typing assumptions, the assumed leaves another proof
  must discharge (`--allow-assumptions`).

Every other kind of claim is refused unless its own flag accepts it:
`--allow-reveal-claim`, `--allow-contains-claim`, `--allow-resource-claim` and
`--allow-binding-claim` (a binding claim names a specification set too, which
must be this build's). A command given a binding proof for the purpose
(`ix verify --binding-proof`) checks that proof's claim itself and needs no flag.

A `catalog` claim is refused on every path but one, as a conjunction of member
claims whose conditions it does not show: `ix verify --aggregate --ixc`
recomputes the claim from the catalog's manifest and pieces and admits each
member under the rules above (`Ix.Cli.CatalogAggregate.verifyCatalog`).

The consistency theorem covers a claim under the default role table or under a
role table the kernel admits. The circuit does not establish the second, so
`admit` runs the kernel's admission of a claim's table (`Ix.Cli.TableAdmission`)
and relaxes the `customBinding` test of `refusal` only when it succeeds.

`statement` says what an admitted claim states, for the verifier's report: its
kind, its subject and its conditions, each with what discharges it or the flag
that accepted it open. -/

public section

namespace Ix.Cli.ClaimPolicy

/-- Which claims a command accepts beyond the unconditional typing claims under
the default role table or a table the kernel admits. -/
structure Policy where
  customBinding : Bool := false
  axioms : Bool := false
  assumedBinding : Bool := false
  assumptions : Bool := false
  reveal : Bool := false
  contains : Bool := false
  resource : Bool := false
  binding : Bool := false
  deriving Repr, Inhabited

/-- The policy the command line selects. -/
def ofParsed (p : Cli.Parsed) : Policy where
  customBinding := p.hasFlag "allow-custom-binding"
  axioms := p.hasFlag "allow-axioms"
  assumedBinding := p.hasFlag "allow-assumed-binding"
  assumptions := p.hasFlag "allow-assumptions"
  reveal := p.hasFlag "allow-reveal-claim"
  contains := p.hasFlag "allow-contains-claim"
  resource := p.hasFlag "allow-resource-claim"
  binding := p.hasFlag "allow-binding-claim"

/-- A typing claim's assumptions (assumed leaves). -/
def assumptionsOf : Ix.Claim → Option Address
  | .eval _ _ _ a | .check _ _ a | .checkEnv _ _ a => a
  | _ => none

/-- The claim's kind, as `ix claim` names it. -/
def kind : Ix.Claim → String
  | .eval .. => "eval"
  | .check .. => "check"
  | .checkEnv .. => "check-env"
  | .reveal .. => "reveal"
  | .contains .. => "contains"
  | .catalog .. => "catalog"
  | .resource .. => "resource"
  | .binding .. => "binding"

/-- The specification set a claim names: a typing claim's context's, or a binding
claim's. -/
def specOf? : Ix.Claim → Option Address
  | .binding spec _ => some spec
  | c => c.context?.map (·.spec)

/-- The refusal of a claim kind that `allowed` does not accept, naming its flag. -/
def kindFlagged (allowed : Bool) (what flag : String) : Option String :=
  if allowed then none else some s!"the claim is {what}; pass --{flag} to accept it"

/-- Why `pol` refuses a claim for its kind, if it does: typing claims never, a
catalog always, any other kind unless its flag accepts it. -/
def kindRefusal (pol : Policy) : Ix.Claim → Option String
  | .eval .. | .check .. | .checkEnv .. => none
  | .catalog members => some s!"the claim is a catalog (members {members}), a conjunction \
      of member claims whose conditions it does not show; verify it with --aggregate --ixc \
      CATALOG, which recomputes it from the catalog's manifest and admits each member"
  | .reveal .. =>
    kindFlagged pol.reveal "a reveal claim, which states no typing" "allow-reveal-claim"
  | .contains .. =>
    kindFlagged pol.contains "a contains claim, which states no typing" "allow-contains-claim"
  | .resource .. => kindFlagged pol.resource
      "a resource claim, which the IxVM consistency theorem does not cover" "allow-resource-claim"
  | .binding .. =>
    kindFlagged pol.binding "a binding claim, which states no typing" "allow-binding-claim"

/-- Why `pol` refuses `claim`, if it does. `bindingDischarged`: a verified binding
proof discharges the claim's assumed binding; `assumptionsDischarged`: the proofs
verified with it own every assumed leaf (a whole shard partition);
`tableAdmitted`: the kernel admits the claim's role table
(`Ix.Cli.TableAdmission.standing`), which a literal class never is. -/
def refusal (pol : Policy) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (tableAdmitted : Bool := false) :
    Except String (Option String) := do
  let spec ← Ix.SpecDigest.specDigest
  if let some named := specOf? claim then
    if named != spec then
      return some s!"the claim names the specification set {named}, not this build's {spec}; \
        this build and the artifact the proof was made with disagree"
  let some ctx := Ix.Claim.context? claim | return kindRefusal pol claim
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

/-- The specification-set condition: `named`, against this build's `spec`. -/
def specLine (spec named : Address) : String :=
  s!"specification set: {named}{if named == spec then ", this build's" else ", not this build's"}"

/-- A typing claim's conditions under `ctx`, each with what discharges it where
the claim is verified, or the flag that accepts it open. `spec` is this build's
specification digest, `default` the default role table's address; the rest as
`refusal`'s arguments. -/
def typingConditions (spec default : Address) (ctx : Ix.ClaimContext)
    (assumptions : Option Address) (bindingDischarged assumptionsDischarged tableAdmitted : Bool) :
    List String :=
  let table :=
    if ctx.literalClass then
      s!"role table: any with the literal class {ctx.binding} (open; accepted under \
        --allow-custom-binding)"
    else if ctx.binding == default then s!"role table: {ctx.binding}, the default role table"
    else if tableAdmitted then s!"role table: {ctx.binding}, admitted by the kernel"
    else s!"role table: {ctx.binding}, not admitted here (open; accepted under \
      --allow-custom-binding)"
  let axioms := match ctx.axioms with
    | none => "axioms: the standard three only (propext, Classical.choice, Quot.sound)"
    | some ax => s!"axioms: the standard three and the user axioms {ax} (open; accepted under \
        --allow-axioms)"
  let binding :=
    if !ctx.bindingAssumed then "role binding: validated in the proof"
    else if bindingDischarged then
      "role binding: assumed to meet the specifications, discharged by the verified binding proof"
    else "role binding: assumed to meet the specifications (open; accepted under \
      --allow-assumed-binding)"
  let leaves := match assumptions with
    | none => "typing assumptions: none"
    | some root =>
      if assumptionsDischarged then
        s!"typing assumptions: the leaves under {root}, owned by the partition verified with it"
      else s!"typing assumptions: the leaves under {root} (open; accepted under \
        --allow-assumptions)"
  [specLine spec ctx.spec, table, axioms, binding, leaves]

/-- What `claim` states, for the verifier's report: its kind, its subject and its
conditions, as indented lines. The arguments are `refusal`'s. -/
def statement (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (tableAdmitted : Bool := false) :
    Except String String := do
  let spec ← Ix.SpecDigest.specDigest
  let default ← Ix.Kernel.Reader.defaultTableAddress
  let typing (ctx : Ix.ClaimContext) (asm : Option Address) : List String :=
    typingConditions spec default ctx asm bindingDischarged assumptionsDischarged tableAdmitted
  let parts : String × String × List String := match claim with
    | .eval ctx i o asm =>
      ("a constant is well-typed and evaluates to another",
        s!"the constant {i}, evaluating to the constant {o}", typing ctx asm)
    | .check ctx c asm => ("a constant is well-typed", s!"the constant {c}", typing ctx asm)
    | .checkEnv ctx r asm =>
      ("every constant of an environment is well-typed",
        s!"the constants of the canonical tree with root {r}", typing ctx asm)
    | .reveal comm info =>
      ("fields of a committed constant", s!"the constant committed as {comm}: {repr info}",
        ["none; the claim states no typing"])
    | .contains tree c =>
      ("membership in a merkle tree", s!"the leaf {c} of the tree with root {tree}",
        ["none; the claim states no typing"])
    | .catalog members =>
      ("every member claim holds",
        s!"the member claims of the canonical tree with root {members}",
        ["each member's own, which the claim does not show"])
    | .resource root profile =>
      ("erased typing and resource admission of an environment",
        s!"the environment with root {root}, under the resource profile {profile}",
        ["the resource validator's own; the IxVM consistency theorem does not cover it"])
    | .binding named table =>
      ("a role table binds every role, each bound constant meeting its specification",
        s!"the role table {table}", [specLine spec named])
  let (what, subject, conditions) := parts
  let head := [s!"kind: {kind claim} ({what})", s!"subject: {subject}", "conditions:"]
  return "\n".intercalate (head.map ("  " ++ ·) ++ conditions.map ("    " ++ ·))

/-- Refuse `claim` (an error) unless the command line's policy admits it, and
return what it states (`statement`), to print once its proof verifies. A claim
under a role table other than the default one is admitted without
`--allow-custom-binding` when the kernel admits the table
(`Ix.Cli.TableAdmission.standing`) over `envs` or the environment
`--binding-env` names; the environments are read only if the table needs them. -/
def admit (p : Cli.Parsed) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (envs : IO (List Ixon.Env) := pure []) :
    IO String := do
  let pol := ofParsed p
  let mut tableAdmitted := false
  let mut unestablished : Option String := none
  if let some ctx := Ix.Claim.context? claim then
    unless pol.customBinding do
      match ← TableAdmission.standing ctx (TableAdmission.withSupplied p envs)
          (← TableAdmission.checkerRef.get) with
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
  IO.ofExcept (statement claim bindingDischarged assumptionsDischarged tableAdmitted)

end Ix.Cli.ClaimPolicy

end
