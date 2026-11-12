import Tests.Ix.IxonV4
import Tests.Ix.IxonV4FFI
import Tests.Ix.IxonText
import Tests.Ix.ContractTransport
import Tests.Ix.ContractPipeline
import Tests.Ix.ContractDecompile
import Tests.Ix.ClaimsV4
import Tests.Ix.Catalog
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver
import Tests.Ix.IxonV4Paths
import Ix.IxVM.ClaimSeeds
import Ix.ModeCheck

def usage : String :=
  s!"usage: lake exe ixon-v4-tests [--export-fixtures] [--primitives]

Run the Ixon v4 codec, locality, claim, contract and cross-language transport
checks, and check the generated fixtures of Tests/Fixtures/ixon-v4/.

  --export-fixtures  write the generated text fixtures (claims) to
                     ixon-v4-fixtures/ in the scratch directory
  --primitives       also validate the primitive closure that
                     `lake exe ixon-v4-primitives` wrote, without the inert
                     axioms and the constants that use them

{Tests.IxonV4.scratchUsage}"

/-- Write every generated text fixture of `Tests/Fixtures/ixon-v4/` (claims)
from the producer its check compares against, to `ixon-v4-fixtures/` in the scratch directory. `expressions.txt`
(independently specified bytes), `text.tsv` (text grammar sources) and
`primitives.tsv` (`ixon-v4-primitives`) are not generated here. -/
def exportFixtures (dir : System.FilePath) : IO Unit := do
  let out := Tests.IxonV4.fixtureExportDir dir
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "claims.tsv") Tests.ClaimsV4.fixtureText
  IO.println s!"Exported claims.tsv to {out}"

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    IO.println usage
    return
  let dir ← Tests.IxonV4.scratchDir
  if args.contains "--export-fixtures" then
    exportFixtures dir
  let cases ← Tests.IxonV4.readExprCases
  let checks ← Tests.IxonV4.runGolden cases
  IO.println s!"Ixon v4: {checks} golden byte and rejection checks passed"
  let ffiChecks ← Tests.IxonV4.runFFI cases
  IO.println s!"Ixon v4: {ffiChecks} FFI roundtrip and Lean/Rust byte parity checks passed"
  let textChecks ← Tests.IxonText.runText
  IO.println s!"Ixon text grammar {Ixon.Syntax.VERSION}: {textChecks} text contract and \
    rejection checks passed"
  Tests.ContractTransport.run
  Tests.ContractPipeline.run
  Tests.ContractDecompile.run
  Tests.ClaimsV4.run
  let result ← LSpec.lspecIO (.ofList [
    ("catalogs", Tests.Ix.Catalog.suite),
    ("primitive addresses", Tests.Ix.Kernel.PrimAddrs.suite),
    ("source contracts", Tests.Ix.SourceContract.suite ++
      Tests.Ix.SourceContract.Driver.suite)]) []
  unless result == 0 do throw <| IO.userError "primitive or source contract regression"
  if args.contains "--primitives" then
    let bytes ← IO.FS.readBinFile (Tests.IxonV4.primitivesIxe dir)
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
