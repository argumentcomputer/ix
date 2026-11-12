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

private def addr (s : String) : Address := Address.blake3 s.toUTF8

/-- This build's specification digest. -/
private def spec : Address := Ix.SpecDigest.specDigest.toOption.getD default

private def ctx : Ix.ClaimContext :=
  { spec, binding := Ix.Kernel.Reader.defaultTableAddress.toOption.getD default,
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
    reveal := true, contains := true, resource := true, binding := true }

/-- `everyFlag` without `except`'s kind flag. -/
private def allBut (except : String) : Policy :=
  { everyFlag with
    reveal := except != "reveal", contains := except != "contains",
    resource := except != "resource", binding := except != "binding" }

/-- A claim of each kind that states no typing, with its kind and its flag. -/
private def untyped : List (String × Ix.Claim × Policy) := [
  ("reveal", .reveal (addr "comm") (.axio none none none), { reveal := true }),
  ("contains", .contains (addr "tree") (addr "const"), { contains := true }),
  ("resource", .resource (addr "root") (addr "profile"), { resource := true }),
  ("binding", .binding spec (addr "binding"), { binding := true })]

/-- Refusals by kind and by specification set. -/
def kindTests : TestSeq :=
  let catalog : Ix.Claim := .catalog (addr "members")
  let otherSpec := addr "another specification set"
  untyped.foldl (init := TestSeq.done) (fun acc (kind, claim, flag) =>
    acc ++ test s!"a {kind} claim is refused by default, naming --allow-{kind}-claim"
        (refusesSaying {} claim s!"--allow-{kind}-claim")
      ++ test s!"  accepted under --allow-{kind}-claim" (admits flag claim)
      ++ test s!"  and refused under every other flag" (!admits (allBut kind) claim))
  ++ test "a catalog is refused by default, naming --ixc" (refusesSaying {} catalog "--ixc")
  ++ test "  and under every flag" (!admits everyFlag catalog)
  ++ test "a typing claim under another specification set is refused"
      (refusesSaying {} (.checkEnv { ctx with spec := otherSpec } (addr "root") none)
        "specification set")
  ++ test "  under every flag" (!admits everyFlag (.check { ctx with spec := otherSpec } (addr "c") none))
  ++ test "  and under a table the kernel admits"
      (!admits everyFlag (.checkEnv { ctx with spec := otherSpec, binding := addr "table" }
        (addr "root") none) (tableAdmitted := true))
  ++ test "  and as an evaluation" (!admits everyFlag (.eval { ctx with spec := otherSpec }
        (addr "in") (addr "out") none))
  ++ test "a binding claim under another specification set is refused under its flag"
      (!admits { binding := true } (.binding otherSpec (addr "binding")))
  ++ test "the kind flags accept no conditional typing claim"
      (!admits { reveal := true, contains := true, resource := true, binding := true }
        (.checkEnv { ctx with axioms := some (addr "axioms") } (addr "root") none))

/-- Whether `claim`'s statement says every one of `texts`. -/
private def statementSays (claim : Ix.Claim) (texts : List String)
    (bindingDischarged assumptionsDischarged tableAdmitted : Bool := false) : Bool :=
  match statement claim bindingDischarged assumptionsDischarged tableAdmitted with
  | .ok s => texts.all fun t => (s.splitOn t).length > 1
  | .error _ => false

/-- The verifier's report of each kind. -/
def statementTests : TestSeq :=
  let defaultTable := ctx.binding
  test "an unconditional check-env names its kind, subject and conditions"
    (statementSays (.checkEnv ctx (addr "root") none)
      ["kind: check-env", s!"subject: the constants of the canonical tree with root {addr "root"}",
       "conditions:", s!"specification set: {spec}, this build's",
       s!"role table: {defaultTable}, the default role table", "axioms: the standard three only",
       "role binding: validated in the proof", "typing assumptions: none"])
  ++ test "a check names its constant" (statementSays (.check ctx (addr "c") none)
      ["kind: check", s!"subject: the constant {addr "c"}"])
  ++ test "an eval names its input and output"
      (statementSays (.eval ctx (addr "in") (addr "out") none)
        ["kind: eval", s!"the constant {addr "in"}, evaluating to the constant {addr "out"}"])
  ++ test "each open condition names the flag that accepted it"
      (statementSays (.checkEnv
          { ctx with binding := addr "table", axioms := some (addr "ax"), bindingAssumed := true }
          (addr "root") (some (addr "leaves")))
        ["not admitted here (open; accepted under --allow-custom-binding)",
         s!"user axioms {addr "ax"} (open; accepted under --allow-axioms)",
         "(open; accepted under --allow-assumed-binding)",
         s!"the leaves under {addr "leaves"} (open; accepted under --allow-assumptions)"])
  ++ test "  and each discharged one what discharges it"
      (statementSays (.checkEnv { ctx with binding := addr "table", bindingAssumed := true }
          (addr "root") (some (addr "leaves"))) (bindingDischarged := true)
          (assumptionsDischarged := true) (tableAdmitted := true)
        [s!"role table: {addr "table"}, admitted by the kernel",
         "discharged by the verified binding proof", "owned by the partition verified with it"])
  ++ test "a literal class is open" (statementSays (.checkEnv { ctx with literalClass := true }
      (addr "root") none) ["any with the literal class", "--allow-custom-binding"])
  ++ test "a claim that states no typing says so"
      (statementSays (.contains (addr "tree") (addr "const"))
          ["kind: contains", s!"the leaf {addr "const"} of the tree with root {addr "tree"}",
           "none; the claim states no typing"]
        && statementSays (.reveal (addr "comm") (.axio none none none))
          ["kind: reveal", s!"the constant committed as {addr "comm"}"])
  ++ test "a binding claim names its table and specification set"
      (statementSays (.binding spec (addr "binding"))
        ["kind: binding", s!"the role table {addr "binding"}", s!"specification set: {spec}, this build's"])
  ++ test "a resource claim and a catalog name their subjects"
      (statementSays (.resource (addr "root") (addr "profile"))
          ["kind: resource", s!"resource profile {addr "profile"}", "does not cover"]
        && statementSays (.catalog (addr "members"))
          ["kind: catalog", s!"root {addr "members"}", "each member's own"])

def unitTests : TestSeq :=
  let unconditional : Ix.Claim := .checkEnv ctx (addr "root") none
  let assumed : Ix.Claim := .check ctx (addr "const") (some (addr "leaves"))
  let axioms : Ix.Claim := .checkEnv { ctx with axioms := some (addr "axioms") } (addr "root") none
  let bound : Ix.Claim := .checkEnv { ctx with bindingAssumed := true } (addr "root") none
  let other : Ix.Claim := .checkEnv { ctx with binding := addr "table" } (addr "root") none
  let literal : Ix.Claim := .checkEnv { ctx with literalClass := true } (addr "root") none
  test "an unconditional typing claim is admitted" (admits {} unconditional)
  ++ test "a claim with assumed leaves is refused" (!admits {} assumed)
  ++ test "  unless --allow-assumptions" (admits { assumptions := true } assumed)
  ++ test "  or a whole partition discharges them" (admits {} assumed false true)
  ++ test "an evaluation with assumed leaves is refused"
      (!admits {} (.eval ctx (addr "in") (addr "out") (some (addr "leaves"))))
  ++ test "a claim with user axioms is refused" (!admits {} axioms)
  ++ test "  even when its assumptions are discharged" (!admits {} axioms true true)
  ++ test "  unless --allow-axioms" (admits { axioms := true } axioms)
  ++ test "a claim that assumes its binding is refused" (!admits {} bound)
  ++ test "  unless a binding proof discharges it" (admits {} bound true)
  ++ test "  or --allow-assumed-binding" (admits { assumedBinding := true } bound)
  ++ test "a claim under another role table is refused" (!admits {} other)
  ++ test "  and one under a literal class" (!admits {} literal)
  ++ test "  unless --allow-custom-binding" (admits { customBinding := true } other)
  ++ test "  or the kernel admits the table" (admits {} other (tableAdmitted := true))
  ++ test "  which a literal class never is" (!admits {} literal (tableAdmitted := true))
  ++ test "  and the admission relaxes no other condition"
      (!admits {} (.checkEnv { ctx with binding := addr "table", axioms := some (addr "axioms") }
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
def standingTests : IO TestSeq := do
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
    return test "the default table needs no admission and reads no environment" (shape s0 == "default")
      ++ test "a literal class is not admitted" (shape s1 == "unestablished")
      ++ test "a claim under another specification set is not admitted" (shape s2 == "unestablished")
      ++ test "a table no supplied environment carries is not admitted" (shape s3 == "unestablished")
      ++ test "  nor one only another table's environment carries" (shape s4 == "unestablished")
      ++ test "a build with no admission run admits no table" (shape s5 == "unestablished")
      ++ test "a table the kernel refuses is not admitted, nor recorded"
          (shape s6 == "unestablished" && !recordedEarly)
      ++ test "  and the refusal gives the refusing stage" (says s6 "the test checker refuses")
      ++ test "a table the kernel admits is admitted and recorded"
          (shape s7 == "admitted false" && recorded)
      ++ test "  and the record answers the next claim without an environment or a run"
          (shape s8 == "admitted true")
      ++ test "  under its specification set only" (!otherSpec)
      ++ test "  and this checker version only" (!stale)
      ++ test "the environments were read only where the table needed them" ((← reads.get) == 5)
  finally
    IO.FS.removeDirAll dir

def suite : IO (List TestSeq) := do
  return [unitTests, kindTests, statementTests, ← standingTests]

end Tests.ClaimPolicy

end
