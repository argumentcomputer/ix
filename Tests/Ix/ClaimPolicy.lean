module

public import LSpec
public import Ix.Cli.ClaimPolicy

/-! # The conditional claims `ix verify` and `ix compress` refuse by default

`Ix.Cli.ClaimPolicy.refusal` over hand-made claims: an unconditional typing claim
is admitted; one with user axioms, an assumed binding or assumed leaves is
refused unless its flag allows it, or a binding proof or a whole partition
discharges the condition; claims that state no typing are not restricted. -/

public section

namespace Tests.ClaimPolicy

open LSpec Ix.Cli.ClaimPolicy

private def addr (s : String) : Address := Address.blake3 s.toUTF8

private def ctx : Ix.ClaimContext :=
  { spec := addr "spec", binding := addr "binding", axioms := none }

/-- Whether `pol` admits `claim`. -/
def admits (pol : Policy) (claim : Ix.Claim) (bindingDischarged assumptionsDischarged : Bool := false) :
    Bool :=
  match refusal pol claim bindingDischarged assumptionsDischarged with
  | .ok none => true
  | _ => false

def unitTests : TestSeq :=
  let unconditional : Ix.Claim := .checkEnv ctx (addr "root") none
  let assumed : Ix.Claim := .check ctx (addr "const") (some (addr "leaves"))
  let axioms : Ix.Claim := .checkEnv { ctx with axioms := some (addr "axioms") } (addr "root") none
  let bound : Ix.Claim := .checkEnv { ctx with bindingAssumed := true } (addr "root") none
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
  ++ test "claims that state no typing are not restricted"
      (admits {} (.contains (addr "tree") (addr "const"))
        && admits {} (.binding (addr "spec") (addr "binding")))

def suite : List TestSeq := [unitTests]

end Tests.ClaimPolicy

end
