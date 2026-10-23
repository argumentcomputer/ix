import LSpec
import Tests.Ix.Compile.Pass3Kernels
import Tests.Ix.Kernel.ReaderRoundtrip

namespace Tests.Ix.Compile.KernelLegs

open LSpec Tests.Ix.Compile.Harness

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def check : IO Nat := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let fixture := fun s => _root_.Ix.Name.fromLeanName (Tests.Ix.Kernel.ReaderRoundtrip.defs s)
  let some twice := inp.ixon.named[fixture "twice"]? | throw (IO.userError "missing twice")
  let some ax := inp.ixon.named[fixture "fidelityAxiom"]? | throw (IO.userError "missing axiom")
  let original ← IO.ofExcept ((inp.ixon.consts[twice.addr]?).get!.get)
  let .defn definition := original.info | throw (IO.userError "twice is not a definition")
  let addName := fun (env : Ixon.Env) (s : String) (nd : Ixon.Named) =>
    let n := _root_.Ix.Name.mkStr _root_.Ix.Name.mkAnon s
    { env.registerName n nd with names := Ixon.RawEnv.addNameComponents env.names n }
  let mut env := inp.ixon
  let aliases := (Array.range 5).map fun i => s!"KernelAlias{i}"
  for label in aliases do env := addName env label twice
  let bad : Ixon.Constant := { original with info := .defn { definition with value := definition.typ } }
  let badAddress := Address.blake3 (Ixon.serConstant bad)
  env := addName (env.storeConst badAddress bad) "KernelRejected" { twice with addr := badAddress }
  let blocked : Ixon.Constant := { original with
    refs := original.refs.push ax.addr
    info := .defn { definition with value := .ref original.refs.size.toUInt64 #[] } }
  let blockedAddress := Address.blake3 (Ixon.serConstant blocked)
  env := addName (env.storeConst blockedAddress blocked) "KernelBlocked" { twice with addr := blockedAddress }
  let labels := aliases ++ #[toString (fixture "spin._unsafe_rec"), toString (fixture "fidelityAxiom"),
    "KernelRejected", "KernelBlocked"]
  let bytes ← IO.ofExcept (Ixon.serEnv env)
  let keep? := (← IO.getEnv "PASS3_KEEP").map System.FilePath.mk
  let dir ← match keep? with
    | some d => do
      let p := d / "kernel-legs-control"
      IO.FS.createDirAll p
      pure p
    | none => IO.FS.createTempDir
  try
    let run ← kernelRun dir bytes labels
    ensure (run.targets == labels && run.leanOutcomes.map (·.label) == labels) "actual selected label order changed"
    ensure (run.leanOutcomes.map (·.outcome) == Array.replicate 5 "accept" ++ #["typed", "decline", "reject", "blocked"])
      s!"actual five outcomes changed: {run.leanSummary}"
    ensure ((kernelCoverageProblems run.selected 9).isEmpty) "actual independent coverage incomplete"
    ensure ((run.failed.filter (·.1 == "lean")).map (·.2.1) == labels.extract 6 9)
      "IxC refusals were dropped or successful typed subjects became failures"
    ensure ((run.leanOutcomes.extract 6 9).all (!·.reason.isEmpty)) "actual refusal reason was lost"
    -- Five labels share one producer, while the support closure is larger:
    -- each of the three legs must still report nine selected declarations.
    let expectedCounts := [("cert", 9), ("rs", 9), ("lean", 9)]
    ensure (run.selected == expectedCounts && run.checked == expectedCounts)
      s!"producer/support counts replaced subject counts: {run.checked}"
    let adir := dir / "anon"
    IO.FS.createDirAll adir
    let anonymous ← kernelRun adir bytes aliases (anon := true)
    ensure (anonymous.failed.isEmpty && anonymous.selected == [("cert", 5), ("rs", 5), ("lean", 5)])
      "anonymous mode lost one of the five selected aliases"
    ensure ((anonymous.checked.lookup "rs").any (· != 5)) "anonymous dependency-count control is vacuous"
    let countCases := [
      (expectedCounts.filter (·.1 != "cert"), 9), (expectedCounts.filter (·.1 != "rs"), 9),
      (expectedCounts.filter (·.1 != "lean"), 9), (expectedCounts ++ [("lean", 9)], 9),
      (expectedCounts ++ [("support", 1)], 9), ([("cert", 9), ("rs", 9), ("lean", 8)], 9),
      ([("cert", 0), ("rs", 0), ("lean", 0)], 0)]
    for (counts, requested) in countCases do
      ensure (!(kernelCoverageProblems counts requested).isEmpty) "missing/duplicate/zero/incomplete leg passed"
    let stdout ← IO.FS.readFile (dir / "lean.stdout")
    let stderr ← IO.FS.readFile (dir / "lean.stderr")
    let failures ← IO.FS.readFile (dir / "lean.fail")
    let rsOutput ← IO.FS.readFile (dir / "rs.stdout")
    for badSummary in ["", rsOutput ++ rsOutput,
        rsOutput.replace "[check] checking 9" "[check] checking bad"] do
      ensure (rsSelectedLabels badSummary false matches .error _)
        "Rust missing/duplicate/non-numeric seed evidence passed"
    let previous : KernelRun := {
      targets := labels, checked := [("cert", 9), ("rs", 9)]
      failed := #[("cert", "keep-cert", "decline: kept"), ("rs", "keep-rs", "kept")] }
    let joined ← IO.ofExcept (previous.withLeanReport stdout stderr failures 3)
    ensure (joined.failed.extract 0 2 == previous.failed && joined.checked.take 2 == previous.checked)
      "attaching IxC changed an older leg's evidence"
    let first := s!"[check-lean] {aliases[0]!}: accept (0ms)\n"
    let protocolCases := [
      previous.withLeanReport stdout stderr failures 1,
      previous.withLeanReport stdout stderr failures 2,
      previous.withLeanReport stdout stderr failures 0,
      previous.withLeanReport "" stderr failures 3,
      previous.withLeanReport stdout "" failures 3,
      previous.withLeanReport stdout stderr "" 3,
      previous.withLeanReport stdout (stderr ++ first) failures 3,
      previous.withLeanReport stdout (stderr ++ "[check-lean] Unknown: accept (0ms)\n") failures 3]
    for result in protocolCases do
      ensure (result matches .error _) "actual harness accepted invocation/protocol corruption"
    ensure ((mayBeEmptyControl Tests.Ix.Compile.Pass3Kernels.table).1.isEmpty) "older negative policy changed"
    ensure (countCases.length == 7 && protocolCases.length == 8) "not all controls ran"
    IO.println s!"kernel legs: {run.leanSummary}; 5 aliases share one producer; all three selected counts 9; anonymous {anonymous.selected} selected versus {anonymous.checked} checked; 18 coverage/protocol negatives; mayBeEmpty preserved"
    return 14 + countCases.length + protocolCases.length + 3
  finally
    if keep?.isNone then IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO "three actual kernel legs preserve exact IxC outcomes and independent coverage" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Compile.KernelLegs
