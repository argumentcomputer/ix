import Tests.Ix.IxonGolden
import Tests.Ix.IxonGoldenFFI
import Tests.Ix.IxonText
import Tests.Ix.ContractTransport
import Tests.Ix.ContractPipeline
import Tests.Ix.ContractDecompile
import Tests.Ix.ClaimsFixture
import Tests.Ix.IxonPaths
import Ix.IxVM.ClaimSeeds
import Ix.ModeCheck

def usage : String :=
  s!"usage: lake exe ixon-tests [--export-fixtures] [--primitives]

Run the Ixon codec, resource-contract, claim, and cross-language transport
checks, and check the generated fixtures of Tests/Fixtures/ixon/.

  --export-fixtures  write the generated text fixtures (claims) to
                     ixon-fixtures/ in the scratch directory
  --primitives       also validate the primitive closure that
                     `lake exe ixon-primitives` wrote, without the inert
                     axioms and the constants that use them

{Tests.IxonPaths.scratchUsage}"

/-- Write every generated text fixture of `Tests/Fixtures/ixon/` (claims)
from the producer its check compares against, to `ixon-fixtures/` in the scratch directory. `expressions.txt`
(independently specified bytes), `text.tsv` (text grammar sources) and
`primitives.tsv` (`ixon-primitives`) are not generated here. -/
def exportFixtures (dir : System.FilePath) : IO Unit := do
  let out := Tests.IxonPaths.fixtureExportDir dir
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "claims.tsv") Tests.ClaimsFixture.fixtureText
  IO.println s!"Exported claims.tsv to {out}"

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    IO.println usage
    return
  let dir ← Tests.IxonPaths.scratchDir
  if args.contains "--export-fixtures" then
    exportFixtures dir
  let cases ← Tests.IxonGolden.readExprCases
  let checks ← Tests.IxonGolden.runGolden cases
  IO.println s!"{Ixon.wireFormatId}: {checks} golden byte and rejection checks passed"
  let textChecks ← Tests.IxonText.runText
  IO.println s!"Ixon text grammar {Ixon.Syntax.VERSION}: {textChecks} text contract and \
    rejection checks passed"
  Tests.ContractTransport.run
  Tests.ContractPipeline.run
  Tests.ContractDecompile.run
  Tests.ClaimsFixture.run
  if args.contains "--primitives" then
    let bytes ← IO.FS.readBinFile (Tests.IxonPaths.primitivesIxe dir)
    let full ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv bytes)
    -- The inert axioms (`sorryAx`, Lean's compiler-trust axioms) and every constant that uses
    -- one (here `Lean.trustCompiler` and `Lean.reduceBool`, `Lean.reduceNat`, whose values use
    -- it) are outside Lean's logic: the default table binds those axioms as inert roles and the
    -- certified entry declines them. The closure is validated without them, as the claim and
    -- shard builders leave them out (`IxVM.ClaimHarness.inertUsers`).
    let inert := IxVM.ClaimHarness.inertUsers full
    let env := { full with
      consts := inert.fold (fun m a => m.erase a) full.consts
      named := full.named.filter fun _ n => !inert.contains n.addr
      addrToName := inert.fold (fun m a => m.erase a) full.addrToName }
    let names := inert.toList.filterMap (fun a => full.addrToName[a]?) |>.map toString
    IO.println s!"Validating {env.consts.size} constants from the primitive closure; left out \
      {inert.size}, the inert axioms and the constants that use one: {names.mergeSort (fun a b => decide (a ≤ b))}"
    IO.println (← IO.ofExcept (Ix.ModeCheck.checkArtifact env))
    -- Time the actual typing check on the same committed primitive closure.
    let t0 ← IO.monoMsNow
    let typing ← IO.lazyPure fun _ => Ix.Typing.typeCheck env
    let t1 ← IO.monoMsNow
    discard <| IO.ofExcept typing
    IO.println s!"Typing the primitive closure: IxC {t1 - t0} ms (accepted)"
  -- Lean/Rust byte parity last, after every Lean-only check.
  let ffiChecks ← Tests.IxonGolden.runFFI cases
  IO.println s!"{Ixon.wireFormatId}: {ffiChecks} FFI roundtrip and Lean/Rust byte parity checks passed"
