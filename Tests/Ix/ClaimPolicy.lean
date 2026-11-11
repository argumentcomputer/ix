module

public import LSpec
public import Ix.Cli.ClaimPolicy
public import IxC.Kernel.Ixon.Prelude

/-! # The conditional claims `ix verify` and `ix compress` refuse by default

`Ix.Cli.ClaimPolicy.refusal` over hand-made claims: an unconditional typing claim
is admitted; one under a role binding other than the default role table that the
kernel does not admit, or with user axioms, an assumed binding or assumed leaves,
is refused unless its flag allows it, or a binding proof or a whole partition
discharges the condition; claims that state no typing are not restricted.

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

private def ctx : Ix.ClaimContext :=
  { spec := addr "spec", binding := Ix.Kernel.Reader.defaultTableAddress.toOption.getD default,
    axioms := none }

/-- Whether `pol` admits `claim`. -/
def admits (pol : Policy) (claim : Ix.Claim) (bindingDischarged assumptionsDischarged : Bool := false)
    (tableAdmitted : Bool := false) : Bool :=
  match refusal pol claim bindingDischarged assumptionsDischarged tableAdmitted with
  | .ok none => true
  | _ => false

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
  ++ test "claims that state no typing are not restricted"
      (admits {} (.contains (addr "tree") (addr "const"))
        && admits {} (.binding (addr "spec") (addr "binding")))

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
  return [unitTests, ← standingTests]

end Tests.ClaimPolicy

end
