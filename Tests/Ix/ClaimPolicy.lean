module

public import LSpec
public import Ix.Cli.ClaimPolicy
public import IxC.Kernel.Ixon.Prelude

/-! # The claims `ix verify` and `ix compress` refuse by default

`Ix.Cli.ClaimPolicy.refusal` over hand-made claims: an unconditional typing claim
is admitted; one under a role binding other than the default role table that the
kernel does not admit, or with user axioms, an assumed binding or assumed leaves,
is refused unless its flag allows it, or a binding proof or a whole partition
discharges the condition. A claim naming another specification set than this
build's is refused under every flag. A claim of another kind than `eval`, `check`
and `checkEnv` is refused unless its own flag accepts it, and a catalog under
every flag.

`Ix.Cli.ClaimPolicy.statement`: each kind's report names the kind, the subject
and the conditions, each with what discharges it or the flag that accepted it.

`Ix.Cli.TableAdmission.standing` over a temporary cache: the default table
needs no admission and reads no environment; a literal class, another
specification set, a missing environment, a build with no admission run and a
table the run refuses are not admitted; a table the run admits is recorded, and
the record answers the next claim without reading an environment or running
the admission again. -/

public section

namespace Tests.ClaimPolicy

open LSpec Ix.Cli.ClaimPolicy Ix.Cli.TableAdmission

set_option compiler.extract_closed false

private def addr (s : String) : Address := Address.blake3 s.toUTF8

/-- This build's specification digest. -/
private def mkSpec (_ : Unit) : Address := Ix.SpecDigest.specDigest.toOption.getD default

private def mkCtx (_ : Unit) : Ix.ClaimContext :=
  { spec := mkSpec (), binding := Ix.Kernel.Reader.defaultTableAddress.toOption.getD default,
    axioms := none }

/-- Whether `pol` admits `claim`. -/
def admits (pol : Policy) (claim : Ix.Claim) (bindingDischarged assumptionsDischarged : Bool := false)
    (tableAdmitted : Bool := false) : Bool :=
  match refusal pol claim bindingDischarged assumptionsDischarged tableAdmitted with
  | .ok none => true
  | _ => false

/-- Whether `pol` refuses `claim` saying `text`. -/
def refusesSaying (pol : Policy) (claim : Ix.Claim) (text : String)
    (tableAdmitted : Bool := false) : Bool :=
  match refusal pol claim (tableAdmitted := tableAdmitted) with
  | .ok (some why) => (why.splitOn text).length > 1
  | _ => false

/-- Every flag. -/
private def everyFlag : Policy :=
  { customBinding := true, axioms := true, assumedBinding := true, assumptions := true,
    reveal := true, contains := true, binding := true }

/-- `everyFlag` without `except`'s kind flag. -/
private def allBut (except : String) : Policy :=
  { everyFlag with
    reveal := except != "reveal", contains := except != "contains",
    binding := except != "binding" }

/-- A claim of each kind that states no typing, with its kind and its flag. -/
private def mkUntyped (_ : Unit) : List (String × (Unit → Ix.Claim) × Policy) := [
  ("reveal", fun () => .reveal (addr "comm") (.axio none none none) none, { reveal := true }),
  ("contains", fun () => .contains (addr "tree") (addr "const"), { contains := true }),
  ("binding", fun () => .binding (mkSpec ()) (addr "binding"), { binding := true })]

/-- Refusals by kind and by specification set. -/
def kindTests : LSpec.Spec := do
  let mkCatalog (_ : Unit) : Ix.Claim := .catalog (addr "members")
  let mkOtherSpec := fun () => addr "another specification set"
  for (kind, mkClaim, flag) in mkUntyped () do
    itBool s!"a {kind} claim is refused by default, naming --allow-{kind}-claim"
      (refusesSaying {} (mkClaim ()) s!"--allow-{kind}-claim")
    itBool s!"  accepted under --allow-{kind}-claim" (admits flag (mkClaim ()))
    itBool s!"  and refused under every other flag" (!admits (allBut kind) (mkClaim ()))
  itBool "a catalog is refused by default, naming --ixc" (refusesSaying {} (mkCatalog ()) "--ixc")
  itBool "  and under every flag" (!admits everyFlag (mkCatalog ()))
  itBool "a typing claim under another specification set is refused"
    (refusesSaying {} (.checkEnv { mkCtx () with spec := mkOtherSpec () } (addr "root") none)
      "specification set")
  itBool "  under every flag" (!admits everyFlag (.check { mkCtx () with spec := mkOtherSpec () } (addr "c") none))
  itBool "  and under a table the kernel admits"
    (!admits everyFlag (.checkEnv { mkCtx () with spec := mkOtherSpec (), binding := addr "table" }
      (addr "root") none) (tableAdmitted := true))
  itBool "  and as an evaluation" (!admits everyFlag (.eval { mkCtx () with spec := mkOtherSpec () }
    (addr "in") (addr "out") none))
  itBool "a binding claim under another specification set is refused under its flag"
    (!admits { binding := true } (.binding (mkOtherSpec ()) (addr "binding")))
  itBool "the kind flags accept no conditional typing claim"
    (!admits { reveal := true, contains := true, binding := true }
      (.checkEnv { mkCtx () with axioms := some (addr "axioms") } (addr "root") none))

/-- Whether `claim`'s statement says every one of `texts`. -/
private def statementSays (claim : Ix.Claim) (texts : List String)
    (bindingDischarged assumptionsDischarged tableAdmitted : Bool := false) : Bool :=
  match statement claim bindingDischarged assumptionsDischarged tableAdmitted with
  | .ok s => texts.all fun t => (s.splitOn t).length > 1
  | .error _ => false

/-- The verifier's report of each kind. -/
def statementTests : LSpec.Spec := do
  it "an unconditional check-env names its kind, subject and conditions" do
    let ctx := mkCtx ()
    let spec := mkSpec ()
    let defaultTable := ctx.binding
    expect (statementSays (.checkEnv ctx (addr "root") none)
      ["kind: check-env", s!"subject: the constants of the canonical tree with root {addr "root"}",
       "conditions:", s!"specification set: {spec}, this build's",
       s!"role table: {defaultTable}, the default role table", "axioms: the standard three only",
       "role binding: validated in the proof", "typing assumptions: none"])
  itBool "a check names its constant" (statementSays (.check (mkCtx ()) (addr "c") none)
    ["kind: check", s!"subject: the constant {addr "c"}"])
  itBool "an eval names its input and output"
    (statementSays (.eval (mkCtx ()) (addr "in") (addr "out") none)
      ["kind: eval", s!"the constant {addr "in"}, evaluating to the constant {addr "out"}"])
  itBool "an eval says what it asserts and that the consistency theorem does not state it"
    (statementSays (.eval (mkCtx ()) (addr "in") (addr "out") none)
      ["the output is the input's normal form as IxVM's evaluator computes it",
       "scope: not covered by the IxVM consistency theorem"])
  itBool "no other kind carries the eval scope line"
    (!statementSays (.check (mkCtx ()) (addr "c") none) ["scope: not covered"])
  itBool "each open condition names the flag that accepted it"
    (statementSays (.checkEnv
        { mkCtx () with binding := addr "table", axioms := some (addr "ax"), bindingAssumed := true }
        (addr "root") (some (addr "leaves")))
      ["not admitted here (open; accepted under --allow-custom-binding)",
       s!"user axioms {addr "ax"} (open; accepted under --allow-axioms)",
       "(open; accepted under --allow-assumed-binding)",
       s!"the leaves under {addr "leaves"} (open; accepted under --allow-assumptions)"])
  itBool "  and each discharged one what discharges it"
    (statementSays (.checkEnv { mkCtx () with binding := addr "table", bindingAssumed := true }
        (addr "root") (some (addr "leaves"))) (bindingDischarged := true)
        (assumptionsDischarged := true) (tableAdmitted := true)
      [s!"role table: {addr "table"}, admitted by the kernel",
       "discharged by the verified binding proof", "owned by the partition verified with it"])
  itBool "a literal class is open" (statementSays (.checkEnv { mkCtx () with literalClass := true }
    (addr "root") none) ["any with the literal class", "--allow-custom-binding"])
  itBool "a claim that states no typing says so"
    (statementSays (.contains (addr "tree") (addr "const"))
        ["kind: contains", s!"the leaf {addr "const"} of the tree with root {addr "tree"}",
         "none; the claim states no typing"]
      && statementSays (.reveal (addr "comm") (.axio none none none) none)
        ["kind: reveal", s!"the constant committed as {addr "comm"}"])
  itBool "a binding claim names its table and specification set"
    (statementSays (.binding (mkSpec ()) (addr "binding"))
      ["kind: binding", s!"the role table {addr "binding"}", s!"specification set: {mkSpec ()}, this build's"])
  itBool "a catalog names its subjects"
    (statementSays (.catalog (addr "members"))
      ["kind: catalog", s!"root {addr "members"}", "each member's own"])

def unitTests : LSpec.Spec := do
  let mkUnconditional (_ : Unit) : Ix.Claim := .checkEnv (mkCtx ()) (addr "root") none
  let mkAssumed (_ : Unit) : Ix.Claim := .check (mkCtx ()) (addr "const") (some (addr "leaves"))
  let mkAxioms (_ : Unit) : Ix.Claim := .checkEnv { mkCtx () with axioms := some (addr "axioms") } (addr "root") none
  let mkBound (_ : Unit) : Ix.Claim := .checkEnv { mkCtx () with bindingAssumed := true } (addr "root") none
  let mkOther (_ : Unit) : Ix.Claim := .checkEnv { mkCtx () with binding := addr "table" } (addr "root") none
  let mkLiteral (_ : Unit) : Ix.Claim := .checkEnv { mkCtx () with literalClass := true } (addr "root") none
  itBool "an unconditional typing claim is admitted" (admits {} (mkUnconditional ()))
  itBool "a claim with assumed leaves is refused" (!admits {} (mkAssumed ()))
  itBool "  unless --allow-assumptions" (admits { assumptions := true } (mkAssumed ()))
  itBool "  or a whole partition discharges them" (admits {} (mkAssumed ()) false true)
  itBool "an evaluation with assumed leaves is refused"
    (!admits {} (.eval (mkCtx ()) (addr "in") (addr "out") (some (addr "leaves"))))
  itBool "a claim with user axioms is refused" (!admits {} (mkAxioms ()))
  itBool "  even when its assumptions are discharged" (!admits {} (mkAxioms ()) true true)
  itBool "  unless --allow-axioms" (admits { axioms := true } (mkAxioms ()))
  itBool "a claim that assumes its binding is refused" (!admits {} (mkBound ()))
  itBool "  unless a binding proof discharges it" (admits {} (mkBound ()) true)
  itBool "  or --allow-assumed-binding" (admits { assumedBinding := true } (mkBound ()))
  itBool "a claim under another role table is refused" (!admits {} (mkOther ()))
  itBool "  and one under a literal class" (!admits {} (mkLiteral ()))
  itBool "  unless --allow-custom-binding" (admits { customBinding := true } (mkOther ()))
  itBool "  or the kernel admits the table" (admits {} (mkOther ()) (tableAdmitted := true))
  itBool "  which a literal class never is" (!admits {} (mkLiteral ()) (tableAdmitted := true))
  itBool "  and the admission relaxes no other condition"
    (!admits {} (.checkEnv { mkCtx () with binding := addr "table", axioms := some (addr "axioms") }
      (addr "root") none) (tableAdmitted := true))

/-- A standing's shape, for the tests. -/
private def shape : Standing → String
  | .default => "default"
  | .admitted recorded => s!"admitted {recorded}"
  | .unestablished _ => "unestablished"

/-- Whether a standing that is not established says `text`. -/
private def says (s : Standing) (text : String) : Bool :=
  match s with
  | .unestablished why => (why.splitOn text).length > 1
  | _ => false

/-- `standing`'s cases over a temporary cache root. -/
def standingTests : IO Spec := do
  let spec ← IO.ofExcept Ix.SpecDigest.specDigest
  let defaultTable ← IO.ofExcept Ix.Kernel.Reader.defaultTableAddress
  let table := addr "a custom table"
  let here : Ix.ClaimContext := { spec, binding := table, axioms := none }
  let carrying (a : Address) : Ixon.Env := { roleBinding := some { address := a, bytes := "table".toUTF8 } }
  let unread : IO (List Ixon.Env) := throw (IO.userError "an environment was read")
  let reads ← IO.mkRef 0
  let counted (envs : List Ixon.Env) : IO (List Ixon.Env) := reads.modify (· + 1) *> pure envs
  let checker (answer : Bool) : Option Checker :=
    some { check := fun b _ => (b.address == table) && answer
           explain := fun _ _ => "the test checker refuses" }
  let dir ← IO.FS.createTempDir
  try
    let s0 ← standing { here with binding := defaultTable } unread none (root? := dir)
    let s1 ← standing { here with literalClass := true } unread none (root? := dir)
    let s2 ← standing { here with spec := addr "another specification set" } unread none
      (root? := dir)
    let s3 ← standing here (counted []) (checker true) (root? := dir)
    let s4 ← standing here (counted [carrying (addr "another table")]) (checker true) (root? := dir)
    let s5 ← standing here (counted [carrying table]) none (root? := dir)
    let s6 ← standing here (counted [carrying table]) (checker false) (root? := dir)
    let recordedEarly ← cached dir spec table
    let s7 ← standing here (counted [carrying table]) (checker true) (root? := dir)
    let recorded ← cached dir spec table
    let s8 ← standing here unread (checker false) (root? := dir)
    let otherSpec ← cached dir (addr "another specification set") table
    -- an entry written by another checker version is a miss
    IO.FS.writeFile (dir / toString spec / toString table) "table-admission/0\n"
    let stale ← cached dir spec table
    let readCount ← reads.get
    return do
      itBool "the default table needs no admission and reads no environment" (shape s0 == "default")
      itBool "a literal class is not admitted" (shape s1 == "unestablished")
      itBool "a claim under another specification set is not admitted" (shape s2 == "unestablished")
      itBool "a table no supplied environment carries is not admitted" (shape s3 == "unestablished")
      itBool "  nor one only another table's environment carries" (shape s4 == "unestablished")
      itBool "a build with no admission run admits no table" (shape s5 == "unestablished")
      itBool "a table the kernel refuses is not admitted, nor recorded"
        (shape s6 == "unestablished" && !recordedEarly)
      itBool "  and the refusal gives the refusing stage" (says s6 "the test checker refuses")
      itBool "a table the kernel admits is admitted and recorded"
        (shape s7 == "admitted false" && recorded)
      itBool "  and the record answers the next claim without an environment or a run"
        (shape s8 == "admitted true")
      itBool "  under its specification set only" (!otherSpec)
      itBool "  and this checker version only" (!stale)
      itBool "the environments were read only where the table needed them" (readCount == 5)
  finally
    IO.FS.removeDirAll dir

def suite : IO Spec := do
  let standing ← standingTests
  return do
    unitTests
    kindTests
    statementTests
    standing

end Tests.ClaimPolicy

end
