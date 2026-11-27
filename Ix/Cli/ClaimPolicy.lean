module
public import Cli
public import Ix.AssumptionTree
public import Ix.ClaimContext
public import Ix.Cli.TableAdmission
public import Ix.DynamicLink.Codec

/-! # The claims `ix verify` and `ix compress` accept by default

A verified proof establishes its claim only as far as a theorem states it, and a
claim can be conditional or state something other than typing. The proved
theorem, `IxVM.Refinement.Endpoint.circuitComposed`, states `check` and
`checkEnv` claims with no user axioms, no assumed leaves and no literal class,
each only together with an accepted `binding` claim for the same role table
(`statement` prints what it gives). These commands accept the typing claims
`check` and `checkEnv`, and by default refuse one

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
`--allow-eval-claim` (no theorem states an `eval` claim), `--allow-reveal-claim`,
`--allow-contains-claim` and
`--allow-binding-claim` (a binding claim names a specification set too, which
must be this build's). A command given a binding proof for the purpose
(`ix verify --binding-proof`) checks that proof's claim itself and needs no flag.

A `catalog` claim is refused on every path but one, as a conjunction of member
claims whose conditions it does not show: `ix verify --aggregate --ixc`
recomputes the claim from the catalog's manifest and pieces and admits each
member under the rules above (`Ix.Cli.CatalogAggregate.verifyCatalog`).

A claim under a role table other than the default one is accepted without
`--allow-custom-binding` when the kernel's executable admission admits the table:
`admit` runs it (`Ix.Cli.TableAdmission`) and relaxes the `customBinding` test of
`refusal` only when it succeeds. No theorem connects that admission to the table
validity `circuitComposed` takes from a `binding` claim (`IxVM.consistent`, which
takes it as a premise, is an unproved reduction), and the report says so.

`statement` says what an admitted claim states, for the verifier's report: its
kind, its subject, the theorem that covers it or that none does, and its
conditions, each with what discharges it or the flag that accepted it open. -/

public section

namespace Ix.Cli.ClaimPolicy

/-- Explicit allowlist entry for a Tier-1 standalone `DynamicLinkStatement` (`0xE8 0x0D`).
VK-wide wildcards and unpinned I/O arities are forbidden: `vkDigest`, exact `entryIdx`,
`numInputs` (`nin`), and `numOutputs` (`nout`) must all be pinned. -/
structure AllowedDynamicCircuit where
  vkDigest : Address
  entryIdx : UInt64
  numInputs : UInt32
  numOutputs : UInt32
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Explicit allowlist entry for a Mode-3a (`LinkedClaim`, validators `12`/`13`) equality-bridge
accelerator circuit. Separate from Tier-1 `AllowedDynamicCircuit`: Mode 3a requires
`codec = ixonAddrPair` and pins the full `(vkDigest, entryIdx, codec, targetConst, certConst, evalType)`
tuple so a non-equality Tier-1 circuit or mismatched bridge/type can never discharge an `EvalAssumption`. -/
structure AllowedLinkedCircuit where
  vkDigest : Address
  entryIdx : UInt64
  codec : Ix.DynamicLink.CodecTag := .ixonAddrPair
  targetConst : Address
  certConst : Address
  evalType : Address
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Which claims a command accepts beyond the unconditional typing claims under
the default role table or a table the kernel admits. -/
structure Policy where
  /-- `--allow-eval-claim`: accept an `eval` claim, which no theorem states. -/
  eval : Bool := false
  customBinding : Bool := false
  axioms : Bool := false
  assumedBinding : Bool := false
  assumptions : Bool := false
  reveal : Bool := false
  contains : Bool := false
  binding : Bool := false
  /-- Allowlisted Tier-1 external circuits (`<vkDigest>:<entryIdx>:<nin>:<nout>`; no VK wildcard
  or unpinned I/O arity). Authorizes standalone `DynamicLinkStatement` (`0xE8 0x0D`) claims ONLY —
  NEVER Mode-3a `LinkedClaim` (validators `12`/`13`). -/
  allowedDynamicCircuits : Array AllowedDynamicCircuit := #[]
  /-- Allowlisted Mode-3a equality-bridge circuits pinning
  `(vkDigest, entryIdx, codec = ixonAddrPair, targetConst, certConst, evalType)`.
  Empty by default: every validator `12`/`13` (`LinkedClaim`) proof or non-empty
  `linkedCircuits` root is refused unless explicitly allowlisted via
  `--allow-linked-circuit`. -/
  allowedLinkedCircuits : Array AllowedLinkedCircuit := #[]
  deriving Repr, Inhabited

/-- Parse one `--allow-dynamic-circuit` allowlist specifier for Tier-1 `DynamicLinkStatement`:
strictly `<64-hex-vk-digest>:<entry-idx>:<nin>:<nout>`. VK-wide `<vk-hex>` wildcards and
unpinned I/O arities (`<vk-hex>:<entry-idx>`) are rejected. -/
def parseAllowedDynamicCircuit (spec : String) : Except String AllowedDynamicCircuit := do
  let parts := spec.splitOn ":"
  match parts with
  | [_vkHex] =>
    throw s!"--allow-dynamic-circuit: VK-wide wildcard is forbidden; expected <vk-hex>:<entry-idx>:<nin>:<nout>, got '{spec}'"
  | [_vkHex, _idxStr] =>
    throw s!"--allow-dynamic-circuit: unpinned I/O arity is forbidden; expected <vk-hex>:<entry-idx>:<nin>:<nout>, got '{spec}'"
  | [vkHex, idxStr, ninStr, noutStr] =>
    let some vkDigest := Address.fromString vkHex
      | throw s!"--allow-dynamic-circuit: invalid 64-hex VK digest '{vkHex}'"
    let some idx := idxStr.toNat?
      | throw s!"--allow-dynamic-circuit: invalid entry index '{idxStr}'"
    if idx ≥ UInt64.size then
      throw s!"--allow-dynamic-circuit: entry index '{idxStr}' exceeds u64"
    let some nin := ninStr.toNat?
      | throw s!"--allow-dynamic-circuit: invalid input arity '{ninStr}'"
    if nin ≥ UInt32.size then
      throw s!"--allow-dynamic-circuit: input arity '{ninStr}' exceeds u32"
    let some nout := noutStr.toNat?
      | throw s!"--allow-dynamic-circuit: invalid output arity '{noutStr}'"
    if nout ≥ UInt32.size then
      throw s!"--allow-dynamic-circuit: output arity '{noutStr}' exceeds u32"
    pure {
      vkDigest
      entryIdx := UInt64.ofNat idx
      numInputs := UInt32.ofNat nin
      numOutputs := UInt32.ofNat nout
    }
  | _ =>
    throw s!"--allow-dynamic-circuit: expected <vk-hex>:<entry-idx>:<nin>:<nout>, got '{spec}'"

/-- Parse all `--allow-dynamic-circuit` flag values, failing closed on any malformed entry. -/
def parseAllowedDynamicCircuits (specs : Array String) :
    Except String (Array AllowedDynamicCircuit) :=
  specs.mapM parseAllowedDynamicCircuit

/-- Parse one `--allow-linked-circuit` allowlist specifier for Mode-3a `LinkedClaim` (validators `12`/`13`).
Accepts `<vk-hex>:<entry-idx>:<target-hex>:<cert-hex>:<eval-type-hex>` (pinning `codec = ixonAddrPair`)
or `<vk-hex>:<entry-idx>:<codec>:<target-hex>:<cert-hex>:<eval-type-hex>` where `<codec>` must be
`1` or `ixonAddrPair`. Rejects VK wildcards, unpinned `(vk, entry)` pairs, and non-`ixonAddrPair` codecs. -/
def parseAllowedLinkedCircuit (spec : String) : Except String AllowedLinkedCircuit := do
  let parts := spec.splitOn ":"
  let (vkHex, idxStr, targetHex, certHex, evalTypeHex) ← match parts with
    | [vkHex, idxStr, targetHex, certHex, evalTypeHex] =>
      pure (vkHex, idxStr, targetHex, certHex, evalTypeHex)
    | [vkHex, idxStr, codecStr, targetHex, certHex, evalTypeHex] =>
      if codecStr == "1" || codecStr == "ixonAddrPair" then
        pure (vkHex, idxStr, targetHex, certHex, evalTypeHex)
      else
        throw s!"--allow-linked-circuit: Mode 3a requires codec '1' or 'ixonAddrPair', got '{codecStr}'"
    | _ =>
      throw s!"--allow-linked-circuit: expected <vk-hex>:<entry-idx>:<target-hex>:<cert-hex>:<eval-type-hex> \
        (or with explicit :ixonAddrPair: codec), got '{spec}'"
  let some vkDigest := Address.fromString vkHex
    | throw s!"--allow-linked-circuit: invalid 64-hex VK digest '{vkHex}'"
  let some idx := idxStr.toNat?
    | throw s!"--allow-linked-circuit: invalid entry index '{idxStr}'"
  if idx ≥ UInt64.size then
    throw s!"--allow-linked-circuit: entry index '{idxStr}' exceeds u64"
  let some targetConst := Address.fromString targetHex
    | throw s!"--allow-linked-circuit: invalid 64-hex targetConst '{targetHex}'"
  let some certConst := Address.fromString certHex
    | throw s!"--allow-linked-circuit: invalid 64-hex certConst '{certHex}'"
  let some evalType := Address.fromString evalTypeHex
    | throw s!"--allow-linked-circuit: invalid 64-hex evalType '{evalTypeHex}'"
  pure {
    vkDigest
    entryIdx := UInt64.ofNat idx
    codec := .ixonAddrPair
    targetConst
    certConst
    evalType
  }

/-- Parse all `--allow-linked-circuit` flag values, failing closed on any malformed entry. -/
def parseAllowedLinkedCircuits (specs : Array String) :
    Except String (Array AllowedLinkedCircuit) :=
  specs.mapM parseAllowedLinkedCircuit

/-- Whether `pol` explicitly allowlists `(vkDigest, entryIdx, numInputs, numOutputs)` for Tier-1
`DynamicLinkStatement`, pinning the input/output arity split. -/
def Policy.allowsDynamicCircuit (pol : Policy) (vkDigest : Address) (entryIdx : UInt64)
    (numInputs numOutputs : Nat) : Bool :=
  pol.allowedDynamicCircuits.any fun a =>
    a.vkDigest == vkDigest && a.entryIdx == entryIdx &&
    a.numInputs.toNat == numInputs && a.numOutputs.toNat == numOutputs

/-- Whether `pol` explicitly allowlists a Mode-3a `LinkedCircuitEntry`, pinning the full
`(vkDigest, entryIdx, codec = ixonAddrPair, targetConst, certConst, evalType)` tuple. -/
def Policy.allowsLinkedEntry (pol : Policy) (entry : Ix.DynamicLink.LinkedCircuitEntry) : Bool :=
  entry.codec == .ixonAddrPair &&
  pol.allowedLinkedCircuits.any fun a =>
    a.vkDigest == entry.vkDigest &&
    a.entryIdx == entry.entryIdx &&
    a.codec == .ixonAddrPair &&
    a.targetConst == entry.targetConst &&
    a.certConst == entry.certConst &&
    a.evalType == entry.evalType

/-- Checked policy parsing from CLI flags (fails closed on invalid `--allow-dynamic-circuit`
or `--allow-linked-circuit`). -/
def ofParsedChecked (p : Cli.Parsed) : Except String Policy := do
  let rawDyn := (p.flag? "allow-dynamic-circuit").map (·.as! (Array String)) |>.getD #[]
  let allowedDynamicCircuits ← parseAllowedDynamicCircuits rawDyn
  let rawLinked := (p.flag? "allow-linked-circuit").map (·.as! (Array String)) |>.getD #[]
  let allowedLinkedCircuits ← parseAllowedLinkedCircuits rawLinked
  pure {
    eval := p.hasFlag "allow-eval-claim"
    customBinding := p.hasFlag "allow-custom-binding"
    axioms := p.hasFlag "allow-axioms"
    assumedBinding := p.hasFlag "allow-assumed-binding"
    assumptions := p.hasFlag "allow-assumptions"
    reveal := p.hasFlag "allow-reveal-claim"
    contains := p.hasFlag "allow-contains-claim"
    binding := p.hasFlag "allow-binding-claim"
    allowedDynamicCircuits
    allowedLinkedCircuits
  }

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
  | .binding .. => "binding"
  | .compile .. => "compile"

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
  | .binding .. =>
    kindFlagged pol.binding "a binding claim, which states no typing" "allow-binding-claim"
  | .compile .. => some "the claim is a compile claim (IxCC), which states no typing; verify it \
      with the IxCC certificate checker"

/-- Why `pol` refuses `claim`, if it does. `bindingDischarged`: a binding proof
for the claim's own role table was verified with it, which discharges an assumed
binding; `assumptionsDischarged`: the proofs verified with it own every assumed
leaf (a whole shard partition); `tableAdmitted`: the kernel admits the claim's
role table (`Ix.Cli.TableAdmission.standing`), which a literal class never is. -/
def refusal (pol : Policy) (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (tableAdmitted : Bool := false) :
    Except String (Option String) := do
  let spec ← Ix.SpecDigest.specDigest
  if let some named := specOf? claim then
    if named != spec then
      return some s!"the claim names the specification set {named}, not this build's {spec}; \
        this build and the artifact the proof was made with disagree"
  if let .eval .. := claim then
    if !pol.eval then
      return some "the claim is an eval claim, which no theorem states (that its output is its \
        input's normal form is proved by no theorem); pass --allow-eval-claim to accept it"
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
  if !pol.assumedBinding && ctx.bindingAssumed && !(bindingDischarged && !ctx.literalClass) then
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

/-- How a verified proof reaches its claim, for the report's `theorem` line: an
IxVM proof of the claim itself (`IxVM::verify_claim`), an aggregation root
(`MultiStark::ix_aggr`), or a compressed or shrunk proof of an aggregation root. -/
inductive Route where
  | direct
  | aggregate
  | compressed
  deriving BEq, Repr, Inhabited

/-- A typing claim's conditions under `ctx`, each with what discharges it where
the claim is verified, or the flag that accepts it open. `spec` is this build's
specification digest, `default` the default role table's address; the rest as
`refusal`'s arguments. -/
def typingConditions (spec default : Address) (ctx : Ix.ClaimContext)
    (assumptions : Option Address) (bindingDischarged assumptionsDischarged tableAdmitted : Bool)
    (route : Route := .direct) : List String :=
  let table :=
    if ctx.literalClass then
      s!"role table: any with the literal class {ctx.binding} (open; accepted under \
        --allow-custom-binding)"
    else if ctx.binding == default then s!"role table: {ctx.binding}, the default role table"
    else if tableAdmitted then s!"role table: {ctx.binding}, admitted by the kernel's executable \
      admission here (no theorem connects that admission to the table's validity under IxVM)"
    else s!"role table: {ctx.binding}, not admitted here (open; accepted under \
      --allow-custom-binding)"
  let axioms := match ctx.axioms with
    | none => "axioms: the standard three only (propext, Classical.choice, Quot.sound)"
    | some ax => s!"axioms: the standard three and the user axioms {ax} (open; accepted under \
        --allow-axioms)"
  let binding :=
    if !ctx.bindingAssumed then
      if route != .direct then "role binding: not assumed by the root claim; validated by the \
        proofs under it (lazily, as far as each check uses the table, or by a binding proof the \
        aggregation verified)"
      else if bindingDischarged then "role binding: validated lazily by this proof (only the roles \
        its check uses); the table's validity is established by the binding proof verified with it"
      else "role binding: validated lazily by this proof (only the roles its check uses); the \
        table's validity is established only by a binding proof for it, which this run did not verify"
    else if bindingDischarged then
      "role binding: assumed to meet the specifications, discharged by the verified binding proof \
        for this table"
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

/-- What the theorem covering a typing claim gives, or that none covers it, for
the report. `bindingDischarged`: a binding
proof for the claim's own table was verified with it; `route`: how the proof
reaches the claim. The proved statement is `IxVM.Refinement.Endpoint.circuitComposed`
(`IxVM.Consistency.ComposedSpec`, `TableValid.lean`): of an accepted `binding`
run and an accepted in-scope typing run under the same table, a BLAKE3 collision,
or the table is valid and the claimed constants' environment has a model in every
set theory. It is a statement about circuit runs, and about models, not typing by
Lean's kernel; no theorem states an `eval` claim, a claim with user axioms,
assumed leaves or a literal class, an aggregation root or a compressed proof. -/
def theoremLine (claim : Ix.Claim) (bindingDischarged tableAdmitted : Bool) (route : Route) :
    Option String :=
  let typingScope (ctx : Ix.ClaimContext) (asm : Option Address) : String :=
    if route != .direct then
      "theorem: none states an aggregation root: no theorem connects an accepted aggregation \
        proof to its root claim" ++
      (if route == .compressed then ", nor a compressed proof to the aggregation proof" else "") ++
      ", and IxVM.Refinement.Endpoint.circuitComposed states single IxVM runs, each with an \
        accepted binding run (Shape 18 Mode 2 equality-reflection roots use distinct validators \
        14/15 and cannot produce a standard validator 3/4/5 root)"
    else if ctx.axioms.isSome || asm.isSome || ctx.literalClass then
      "theorem: none; IxVM.Refinement.Endpoint.circuitComposed states only check and check-env \
        claims with no user axioms, no typing assumptions and no literal class, and no theorem \
        states the composition of a shard partition"
    else if bindingDischarged then
      s!"theorem: IxVM.Refinement.Endpoint.circuitComposed, with the binding proof for role \
        table {ctx.binding} verified in this run, states of IxVM circuit runs accepting the two \
        claims: a BLAKE3 collision, or the table is valid and the claimed constants' environment, \
        each constant as its record declares it, has a model in every set theory. It states no \
        typing by Lean's kernel, and that this verifier's acceptance implies such circuit runs \
        is not proved"
    else
      s!"theorem: IxVM.Refinement.Endpoint.circuitComposed covers this claim only together with \
        an accepted binding claim for role table {ctx.binding}, which this run did not verify \
        (ix verify --binding-proof)" ++
      (if tableAdmitted then "; the kernel's admission of the table is not such a proof" else "") ++
      ". With one, it states of the two IxVM circuit runs: a BLAKE3 collision, or the table is \
        valid and the claimed constants' environment has a model in every set theory; it states \
        no typing by Lean's kernel"
  match claim with
  | .eval .. => some "theorem: none; no theorem states an eval claim (that its output is its \
      input's normal form is proved by no theorem); accepted only under --allow-eval-claim"
  | .check ctx _ asm | .checkEnv ctx _ asm => some (typingScope ctx asm)
  | _ => none

/-- What `claim` states, for the verifier's report: its kind, its subject, the
theorem that covers it (`theoremLine`) and its conditions, as indented lines.
The arguments are `refusal`'s, and `route` how the proof reaches the claim. -/
def statement (claim : Ix.Claim) (bindingDischarged : Bool := false)
    (assumptionsDischarged : Bool := false) (tableAdmitted : Bool := false)
    (route : Route := .direct) : Except String String := do
  let spec ← Ix.SpecDigest.specDigest
  let default ← Ix.Kernel.Reader.defaultTableAddress
  let typing (ctx : Ix.ClaimContext) (asm : Option Address) : List String :=
    typingConditions spec default ctx asm bindingDischarged assumptionsDischarged tableAdmitted route
  -- A typing claim states typing under Ix's kernel rules, not Lean's kernel.
  let ixRules := "under Ix's kernel rules, which include equality reflection (a proved \
    equation is a conversion), not Lean's kernel"
  let parts : String × String × List String := match claim with
    | .eval ctx i o asm =>
      (s!"the input and output constants type-check {ixRules}, and the output is the input's \
          normal form as IxVM's evaluator computes it",
        s!"the constant {i}, evaluating to the constant {o}", typing ctx asm)
    | .check ctx c asm => (s!"a constant type-checks {ixRules}", s!"the constant {c}", typing ctx asm)
    | .checkEnv ctx r asm =>
      (s!"every constant of an environment type-checks {ixRules}",
        s!"the constants of the canonical tree with root {r}", typing ctx asm)
    | .reveal comm info binders =>
      ("fields of a committed constant",
        s!"the constant committed as {comm}: {repr info}, binders {binders}",
        ["none; the claim states no typing"])
    | .contains tree c =>
      ("membership in a merkle tree", s!"the leaf {c} of the tree with root {tree}",
        ["none; the claim states no typing"])
    | .catalog members =>
      ("every member claim holds",
        s!"the member claims of the canonical tree with root {members}",
        ["each member's own, which the claim does not show"])
    | .binding named table =>
      ("a role table binds every role, each bound constant meeting its specification",
        s!"the role table {table}", [specLine spec named])
    | .compile cc =>
      ("a constant compiles to an x86-64 ELF64 object",
        s!"{cc.target} in env {cc.env} (role table {cc.roleTable}, policy {cc.policy}, \
          arity {cc.abiArity}) -> ELF {cc.elfHash}",
        ["none; the claim states no typing"])
  let (what, subject, conditions) := parts
  let scope := (theoremLine claim bindingDischarged tableAdmitted route).toList
  let head := [s!"kind: {kind claim} ({what})", s!"subject: {subject}"] ++ scope ++ ["conditions:"]
  return "\n".intercalate (head.map ("  " ++ ·) ++ conditions.map ("    " ++ ·))

/-- Refuse `claim` (an error) unless the command line's policy admits it, and
return what it states (`statement`), to print once its proof verifies. A claim
under a role table other than the default one is admitted without
`--allow-custom-binding` when the kernel admits the table
(`Ix.Cli.TableAdmission.standing`) over `envs` or the environment
`--binding-env` names; the environments are read only if the table needs them.
`bindingProof`: the role table of a `binding` claim whose proof was verified with
this one; it discharges the claim's binding only when it is the claim's own table.
`route`: how the proof reaches the claim. -/
def admit (p : Cli.Parsed) (claim : Ix.Claim) (bindingProof : Option Address := none)
    (assumptionsDischarged : Bool := false) (envs : IO (List Ixon.Env) := pure [])
    (route : Route := .direct) : IO String := do
  let bindingDischarged := match Ix.Claim.context? claim, bindingProof with
    | some ctx, some table => !ctx.literalClass && ctx.binding == table
    | _, _ => false
  let pol ← IO.ofExcept (ofParsedChecked p)
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
  IO.ofExcept (statement claim bindingDischarged assumptionsDischarged tableAdmitted route)

/-! ## Dynamic Circuit Linking (`EvalAssumedClaim` / `LinkedClaim` / `DynamicLinkStatement`) Policy -/

/-- Always refuse a Tier-2 `EvalAssumedClaim` (validators `10`/`11`): undischarged
`evalAssumptions` must be discharged before verification. -/
def refusalEvalAssumedClaim (claim : Ix.DynamicLink.EvalAssumedClaim) : String :=
  s!"the claim retains undischarged eval assumptions {claim.evalAssumptions} \
    (validator {claim.validator}); discharge all eval assumptions before verification"

/-- Why `pol` refuses a Shape 18 Mode 2 `EvalDischargedClaim` (validators `14`/`15`), if it does.
Mode 2 roots use equality reflection (rewriting along proved `@Eq` equations) and carry distinct
validators `14`/`15` so they can never alias direct `InScopeTyping` claims (`3`/`4`). They are
refused by default unless `--allow-eval-claim` is passed AND the underlying `(ctx, assumptions)`
passes standard `ClaimPolicy` checks. -/
def refusalEvalDischargedClaim (pol : Policy) (claim : Ix.DynamicLink.EvalDischargedClaim)
    (bindingDischarged : Bool := false) (assumptionsDischarged : Bool := false)
    (tableAdmitted : Bool := false) : Except String (Option String) := do
  let spec ← Ix.SpecDigest.specDigest
  if claim.ctx.spec != spec then
    return some s!"the claim names the specification set {claim.ctx.spec}, not this build's {spec}; \
      this build and the artifact the proof was made with disagree"
  if !pol.eval then
    return some s!"the claim is a Shape 18 Mode 2 equality-reflection root (validator {claim.validator}), \
      which no theorem covers (distinct from direct typing validators 3/4); pass --allow-eval-claim to accept it"
  let stdClaim : Ix.Claim := match claim.kind with
    | .check const => .check claim.ctx const claim.assumptions
    | .checkEnv root => .checkEnv claim.ctx root claim.assumptions
  refusal pol stdClaim bindingDischarged assumptionsDischarged tableAdmitted

/-- Why `pol` refuses a validator `12`/`13` `LinkedClaim` (`linkedCircuits ≠ none`), if it does.
Refused by default (`pol.allowedLinkedCircuits.isEmpty`) — even when `--allow-dynamic-circuit` is
set for Tier-1 `DynamicLinkStatement`s — unless:
1. `claim.evalAssumptions = none` (all eval assumptions discharged),
2. `entries = some es` supplies the exact canonical `LinkedCircuitEntry` preimages whose
   sorted canonical Merkle root equals `claim.linkedCircuits`,
3. every entry `e ∈ es` binds `(e.spec, e.binding) == (claim.ctx.spec, claim.ctx.binding)`,
   uses `e.codec = .ixonAddrPair`, AND matches a Mode-3a `--allow-linked-circuit` entry pinning
   the full `(vkDigest, entryIdx, codec = ixonAddrPair, targetConst, certConst, evalType)` tuple,
   and
4. the underlying `(claim.ctx, claim.assumptions)` passes standard `ClaimPolicy` checks. -/
def refusalLinkedClaim (pol : Policy) (claim : Ix.DynamicLink.LinkedClaim)
    (entries : Option (Array Ix.DynamicLink.LinkedCircuitEntry) := none)
    (bindingDischarged : Bool := false) (assumptionsDischarged : Bool := false)
    (tableAdmitted : Bool := false) : Except String (Option String) := do
  let spec ← Ix.SpecDigest.specDigest
  if claim.ctx.spec != spec then
    return some s!"the claim names the specification set {claim.ctx.spec}, not this build's {spec}; \
      this build and the artifact the proof was made with disagree"
  if let some evRoot := claim.evalAssumptions then
    return some s!"the linked claim retains undischarged eval assumptions {evRoot} \
      (validator {claim.validator}); discharge all eval assumptions before verification"
  if pol.allowedLinkedCircuits.isEmpty then
    return some s!"the claim depends on dynamically linked external circuits \
      (linkedCircuits root {claim.linkedCircuits}, validator {claim.validator}); \
      pass --allow-linked-circuit <vk>:<entry>:<target>:<cert>:<eval-type> to explicitly allowlist every linked circuit"
  let some es := entries
    | return some s!"the claim depends on dynamically linked external circuits \
        (linkedCircuits root {claim.linkedCircuits}, validator {claim.validator}), \
        but no LinkedCircuitEntry preimages were supplied to audit against the allowlist"
  let some canonTree := Ix.AssumptionTree.canonical (es.map (·.address))
    | return some s!"the linked claim {claim.linkedCircuits} has an empty linked-circuit entry list"
  if canonTree.root != claim.linkedCircuits then
    return some s!"supplied LinkedCircuitEntry preimages hash to canonical root {canonTree.root}, \
      not the claim's committed linkedCircuits root {claim.linkedCircuits}"
  for entry in es do
    if entry.spec != claim.ctx.spec || entry.binding != claim.ctx.binding then
      return some s!"linked circuit ({entry.vkDigest}:{entry.entryIdx}, cert {entry.certConst}) \
        binds (spec={entry.spec}, binding={entry.binding}), which differs from the claim's \
        (spec={claim.ctx.spec}, binding={claim.ctx.binding})"
    if entry.codec != .ixonAddrPair then
      return some s!"linked circuit ({entry.vkDigest}:{entry.entryIdx}, cert {entry.certConst}) \
        uses codec {repr entry.codec}, but Mode 3a requires ixonAddrPair (1)"
    unless pol.allowsLinkedEntry entry do
      return some s!"linked circuit ({entry.vkDigest}:{entry.entryIdx}, target {entry.targetConst}, \
        cert {entry.certConst}, evalType {entry.evalType}) is not allowlisted; pass \
        --allow-linked-circuit {entry.vkDigest}:{entry.entryIdx}:{entry.targetConst}:{entry.certConst}:{entry.evalType} to accept it"
  let stdClaim : Ix.Claim := match claim.kind with
    | .check const => .check claim.ctx const claim.assumptions
    | .checkEnv root => .checkEnv claim.ctx root claim.assumptions
  refusal pol stdClaim bindingDischarged assumptionsDischarged tableAdmitted

/-- Why `pol` refuses a standalone Tier 1 `DynamicLinkStatement` (`0xE8 0x0D`), if it does.
Refused by default unless exact `(stmt.circuit.vkDigest, stmt.circuit.entryIdx, stmt.pubInputs.size, stmt.pubOutputs.size)`
is allowlisted via `--allow-dynamic-circuit`, and when bridged:
- `bridge.spec` equals this build's spec,
- `bridge.binding` is the default role table, kernel-admitted (`tableAdmitted`), or accepted via
  `--allow-custom-binding`, and
- codec-specific public I/O arities hold (`ixonAddrPair`: `8 + 8`, `ixonAddrSingle`: `8 + 0`). -/
def refusalDynamicLinkStatement (pol : Policy) (stmt : Ix.DynamicLink.DynamicLinkStatement)
    (tableAdmitted : Bool := false) :
    Except String (Option String) := do
  if let some b := stmt.bridge? then
    let spec ← Ix.SpecDigest.specDigest
    if b.spec != spec then
      return some s!"the dynamic-link bridge names specification set {b.spec}, not this build's {spec}"
    let default ← Ix.Kernel.Reader.defaultTableAddress
    if !pol.customBinding && !tableAdmitted && b.binding != default then
      return some s!"the dynamic-link bridge is relative to role binding {b.binding}, \
        not the default role table {default}; pass --allow-custom-binding to accept it"
    match b.codec with
    | .ixonAddrPair =>
      if stmt.pubInputs.size != 8 || stmt.pubOutputs.size != 8 then
        return some s!"the dynamic-link bridge uses codec ixonAddrPair (1), which requires \
          8 pubInputs and 8 pubOutputs (got {stmt.pubInputs.size} and {stmt.pubOutputs.size})"
    | .ixonAddrSingle =>
      if stmt.pubInputs.size != 8 || stmt.pubOutputs.size != 0 then
        return some s!"the dynamic-link bridge uses codec ixonAddrSingle (2), which requires \
          8 pubInputs and 0 pubOutputs (got {stmt.pubInputs.size} and {stmt.pubOutputs.size})"
    | _ => pure ()
  unless pol.allowsDynamicCircuit stmt.circuit.vkDigest stmt.circuit.entryIdx
      stmt.pubInputs.size stmt.pubOutputs.size do
    return some s!"the dynamic-link statement uses external circuit \
      ({stmt.circuit.vkDigest}:{stmt.circuit.entryIdx} with {stmt.pubInputs.size} inputs, \
      {stmt.pubOutputs.size} outputs) which is not allowlisted; \
      pass --allow-dynamic-circuit {stmt.circuit.vkDigest}:{stmt.circuit.entryIdx}:{stmt.pubInputs.size}:{stmt.pubOutputs.size} to accept it"
  return none

/-- Uniform policy check over raw claim bytes covering standard `Ix.Claim` (validators `0, 3, 4, 5`),
`EvalDischargedClaim` (validators `14`/`15`), `LinkedClaim` (validators `12`/`13`),
`EvalAssumedClaim` (validators `10`/`11`), and Tier 1 `DynamicLinkStatement` (`0xE8 0x0D`).
Refuses validator `14`/`15` Mode-2 equality-reflection roots unless `--allow-eval-claim` is set,
and refuses any non-empty `linkedCircuits` / validator `12`/`13` claim by default unless explicitly
allowlisted via `--allow-linked-circuit`. -/
def refusalDynamicBytes (pol : Policy) (bytes : ByteArray)
    (linkedEntries : Option (Array Ix.DynamicLink.LinkedCircuitEntry) := none)
    (bindingDischarged : Bool := false) (assumptionsDischarged : Bool := false)
    (tableAdmitted : Bool := false) : Except String (Option String) := do
  match Ix.Claim.de bytes with
  | .ok c => refusal pol c bindingDischarged assumptionsDischarged tableAdmitted
  | .error claimErr =>
    match Ix.DynamicLink.deEvalDischargedClaim bytes with
    | .ok dc =>
      refusalEvalDischargedClaim pol dc bindingDischarged assumptionsDischarged tableAdmitted
    | .error _ =>
      match Ix.DynamicLink.deLinkedClaim bytes with
      | .ok lc =>
        refusalLinkedClaim pol lc linkedEntries bindingDischarged assumptionsDischarged tableAdmitted
      | .error _ =>
        match Ix.DynamicLink.deEvalAssumedClaim bytes with
        | .ok ec => pure (some (refusalEvalAssumedClaim ec))
        | .error _ =>
          match Ix.DynamicLink.deDynamicLink bytes with
          | .ok dl => refusalDynamicLinkStatement pol dl tableAdmitted
          | .error _ => throw claimErr

/-- CLI-facing admission over raw claim bytes covering standard `Ix.Claim`, Mode-2
`EvalDischargedClaim` (validators `14`/`15`), Mode-3a `LinkedClaim` (validators `12`/`13`),
`EvalAssumedClaim` (validators `10`/`11`), and Tier-1 `DynamicLinkStatement` (`0xE8 0x0D`).
Enforces `ofParsedChecked`, kernel `TableAdmission.standing` for custom role tables, and
`refusalDynamicBytes`, returning a human-readable statement on admission or throwing
`IO.userError "refused: ..."` on refusal. -/
def admitDynamicBytes (p : Cli.Parsed) (bytes : ByteArray)
    (linkedEntries : Option (Array Ix.DynamicLink.LinkedCircuitEntry) := none)
    (bindingDischarged : Bool := false) (assumptionsDischarged : Bool := false)
    (envs : IO (List Ixon.Env) := pure []) : IO String := do
  let pol ← IO.ofExcept (ofParsedChecked p)
  let ctx? : Option Ix.ClaimContext :=
    match Ix.Claim.de bytes with
    | .ok c => Ix.Claim.context? c
    | .error _ =>
      match Ix.DynamicLink.deEvalDischargedClaim bytes with
      | .ok dc => some dc.ctx
      | .error _ =>
        match Ix.DynamicLink.deLinkedClaim bytes with
        | .ok lc => some lc.ctx
        | .error _ =>
          match Ix.DynamicLink.deDynamicLink bytes with
          | .ok dl => dl.bridge?.map fun b =>
              { spec := b.spec, binding := b.binding, axioms := none, bindingAssumed := false }
          | .error _ => none
  let mut tableAdmitted := false
  let mut unestablished : Option String := none
  if let some ctx := ctx? then
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
      (refusalDynamicBytes pol bytes linkedEntries bindingDischarged assumptionsDischarged tableAdmitted) then
    let detail := match unestablished with
      | some reason => s!" (the kernel's admission of the table is not established: {reason})"
      | none => ""
    throw (IO.userError s!"refused: {why}{detail}")
  match Ix.Claim.de bytes with
  | .ok c => IO.ofExcept (statement c bindingDischarged assumptionsDischarged tableAdmitted .aggregate)
  | .error _ =>
    match Ix.DynamicLink.deEvalDischargedClaim bytes with
    | .ok dc =>
      let stdClaim : Ix.Claim := match dc.kind with
        | .check const => .check dc.ctx const dc.assumptions
        | .checkEnv root => .checkEnv dc.ctx root dc.assumptions
      let base ← IO.ofExcept (statement stdClaim bindingDischarged assumptionsDischarged tableAdmitted .aggregate)
      pure s!"{base}\n    eval discharge: Shape 18 Mode 2 equality reflection (validator {dc.validator}; accepted under --allow-eval-claim)"
    | .error _ =>
      match Ix.DynamicLink.deLinkedClaim bytes with
      | .ok lc =>
        let stdClaim : Ix.Claim := match lc.kind with
          | .check const => .check lc.ctx const lc.assumptions
          | .checkEnv root => .checkEnv lc.ctx root lc.assumptions
        let base ← IO.ofExcept (statement stdClaim bindingDischarged assumptionsDischarged tableAdmitted .aggregate)
        pure s!"{base}\n    linked circuits: {lc.linkedCircuits} (validator {lc.validator}; explicitly allowlisted)"
      | .error _ =>
        match Ix.DynamicLink.deDynamicLink bytes with
        | .ok dl =>
          let bridgeDesc := match dl.bridge? with
            | none => "none"
            | some b => s!"spec={b.spec}, binding={b.binding}, target={b.targetConst}, codec={repr b.codec}, cert={b.certConst}"
          pure s!"  kind: dynamic-link (external Multi-STARK circuit execution)\n  subject: {dl.circuit.vkDigest}:{dl.circuit.entryIdx} ({dl.pubInputs.size} inputs, {dl.pubOutputs.size} outputs)\n  conditions:\n    bridge: {bridgeDesc}\n    allowlist: explicitly allowlisted"
        | .error err => throw (IO.userError s!"unrecognized dynamic claim bytes: {err}")

end Ix.Cli.ClaimPolicy

end
