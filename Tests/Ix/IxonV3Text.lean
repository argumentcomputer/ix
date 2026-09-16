import Tests.Ix.IxonSyntax

namespace Tests.IxonV3
open Ixon.Syntax

def textContractKey : Term → Option (String × Nat × Nat)
  | .lam binders _ _ => do
    let binder ← binders[0]?
    if binders.size != 1 then none else
      some ("lam", binder.contract.toBits.toNat, 0)
  | .pi binders result _ _ => do
    let binder ← binders[0]?
    if binders.size != 1 then none else
      some ("all", binder.contract.toBits.toNat, result.toBits.toNat)
  | .arrow result _ _ _ => some ("arrow", 7, result.toBits.toNat)
  | .letE contract _ _ _ _ _ =>
    some ("let", contract.binder.toBits.toNat, contract.flags.toNat)
  | _ => none

def runText : IO Nat := do
  let bytes ← IO.FS.readFile "Tests/Fixtures/ixon-v3/text.tsv"
  let mut count := 0
  for line in bytes.splitOn "\n" do
    if line.isEmpty then continue
    let [kind, input, output, source] := line.splitOn "\t"
      | throw (IO.userError s!"invalid text fixture: {line}")
    let some input := input.toNat? | throw (IO.userError "invalid input code")
    let some output := output.toNat? | throw (IO.userError "invalid output code")
    let term ← match parseTerm source with
      | .ok term => pure term
      | .error error => throw (IO.userError s!"{source}: {error}")
    unless textContractKey term == some (kind, input, output) do
      throw (IO.userError s!"text contract mismatch: {source}")
    let printed := printTerm term
    unless printed.replace "\n" " " == source do
      throw (IO.userError s!"text golden mismatch: {source} / {printed}")
    let reparsed ← match parseTerm printed with
      | .ok term => pure term
      | .error error => throw (IO.userError s!"{printed}: {error}")
    unless textContractKey reparsed == textContractKey term do
      throw (IO.userError s!"text roundtrip changed contracts: {source}")
    count := count + 3
  for source in [
      "fun (!! x : A) => x", "fun (~~ x : A) => x",
      "fun (01 x : A) => x", "fun (&1 x : A) => x",
      "fun (~!x : A) => x", "A → !! B", "A → ~~ B",
      "let borrow (~ x y : A) := z; x",
      "let (!1 x y : A) := z; x"] do
    if let .ok _ := parseTerm source then
      throw (IO.userError s!"malformed contract accepted: {source}")
    count := count + 1
  for ty in ["0", "1", "10", "101 0", "1 → Prop"] do
    let source := s!"fun [({ty})] => Prop"
    let term ← IO.ofExcept ((parseTerm source).mapError toString)
    let printed := printTerm term
    unless printed == source do
      throw (IO.userError s!"numeric unnamed binder lost disambiguation: {printed}")
    let reparsed ← IO.ofExcept ((parseTerm printed).mapError toString)
    unless textContractKey reparsed == some ("lam", 7, 0) do
      throw (IO.userError "numeric unnamed binder changed its usage")
    count := count + 1
  let result ← LSpec.lspecIO
    (.ofList [("ixon-text", Tests.IxonSyntax.suite)]) []
  unless result == 0 do throw (IO.userError "text grammar regression suite failed")
  return count

end Tests.IxonV3
