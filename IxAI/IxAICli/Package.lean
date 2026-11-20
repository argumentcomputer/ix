import IxAIVerify.Package
import IxAIVerify.Cli

/-!
# The full run's training evidence and package

`ixai aiur-chain` and `ixai aiur-diagnose` read a directory of per-step Aiur proofs or prover
reports; `ixai package-assemble` writes the trainer's side of the model package
(`docs/verification.md`).
-/

namespace IxAICli

open IxAI IxAIVerify

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

def packageDir : System.FilePath := IxAIVerify.projectDir / ".truthmines" / "package" / "full"

/-- Verify a directory of per-step proofs of the full run with `IxAIVerify.verifyStepRoute`:
every scheduled step must be present, and every proof verifies against the committed program and
a claim built from the specification. The program digest is the one the package's commitment
approves, the intermediate models are `DIR/expected.txt`, and the final model is the package's. -/
def aiurChain (dir : System.FilePath) : IO UInt32 := do
  let some c := IxAIVerify.configNamed? "full" | return 2
  let commitment ← match Lean.Json.parse (← IO.FS.readFile (packageDir / "commitment.json")) >>= Commitment.parse with
    | .ok cm => pure cm
    | .error e => IO.println s!"REJECT: no committed program to verify against ({e})"; return 1
  let some pd := ((commitment.programs.find? (·.1 == "Fixed::step")).map (·.2)).bind Digest.ofHex?
    | IO.println "REJECT: the commitment approves no Fixed::step program"; return 1
  let models ← match ← readModels (dir / "expected.txt") with
    | .ok ms => pure ms
    | .error _ => pure []
  let final ← match ← readModelFile (packageDir / "model.txt") with
    | .ok m => pure m
    | .missing e => IO.println s!"INCOMPLETE: {e}"; return 4
    | .malformed e => IO.println s!"REJECT: {e}"; return 1
  let work := (← Cli.workBase) / s!"ixai-aiur-chain-{← IO.monoNanosNow}"
  let r ← verifyStepRoute (← Tools.fromEnv) c (packageDir / "program-step.ixp") pd dir models final work
  try IO.FS.removeDirAll work catch _ => pure ()
  IO.println s!"[{r.kind}] {r.status.label}"
  for d in r.detail do IO.println s!"  {d}"
  return r.status.exitCode

/-- Read the prover's step reports and check their words against the specification. A diagnostic
for prover development: a report's `verified` field and words are the prover's own output, so this
verifies nothing, and it says so. -/
def aiurDiagnose (dir : System.FilePath) : IO UInt32 := do
  let some c := IxAIVerify.configNamed? "full" | return 2
  let s := IxAICore.Triage.spec
  let examples := examplesOf c
  let sched := c.schedule
  let mut m := c.init s
  let mut steps := 0
  IO.println "DIAGNOSTIC ONLY: reads prover reports; no proof is verified (use `ixai-verify chain`)"
  for (idx, i) in sched.zip (List.range sched.length) do
    let path := dir / s!"{stepName i}.report.json"
    unless ← path.pathExists do break
    let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    let args ← IO.ofExcept (reportNats j "args")
    let output ← IO.ofExcept (reportNats j "output")
    let batch := batchOf examples idx
    unless args == stepArgs c (rawOfModel m) batch do
      IO.println s!"report {i}: arguments are not the specified weights, batch and rate"; return 1
    let next := m.step ⟨c.lrRaw⟩ batch
    unless output == rawOfModel next do
      IO.println s!"report {i}: output is not Model.step of its input"; return 1
    m := next
    steps := steps + 1
  IO.println s!"{steps} of {sched.length} reports chain from config.init through the scheduled batches"
  return if steps == sched.length then 0 else 4

/-! ## The model package of the full run -/

/-- Assemble the trainer's side of the package (`docs/verification.md`) in `out` (default
`packageDir`): the model, the approved program packages cut from the deployed step and train
packages, and a receipt naming the evidence. The `aiur-exec` route names the aggregator package of
`packageDir`, relative to the receipt when `out` is `packageDir`, and the terminal PLONK verifying
key `plonkKey` when one is given, so that a job pinning the compression pipeline verifies the
certificate. The consumer's commitment is written separately, by `ixai-verify commit`. -/
def packageAssemble (out : System.FilePath := packageDir) (plonkKey : Option System.FilePath := none) :
    IO UInt32 := do
  let some c := IxAIVerify.configNamed? "full" | return 2
  let aiur := IxAIVerify.projectDir / ".truthmines" / "aiur"
  let key? ← match plonkKey with
    | none => pure none
    | some k =>
      unless ← k.pathExists do IO.eprintln s!"PLONK verifying key {k} is missing"; return 1
      pure (some (← IO.FS.realPath k))
  IO.FS.createDirAll out
  let inPlace ← try pure ((← IO.FS.realPath out) == (← IO.FS.realPath packageDir))
    catch _ => pure (out == packageDir)
  let aggregator := if inPlace then "aggregator.ixa" else (packageDir / "aggregator.ixa").toString
  let modelsPath := aiur / "full-bound" / "expected.txt"
  let models ← IO.ofExcept (← readModels modelsPath)
  let some final := models.getLast? | IO.eprintln "no models"; return 1
  IO.FS.writeFile (out / "model.txt") (joinInts final ++ "\n")
  let field := fun (x : Int) => (x % IxAIVerify.goldilocks).toNat
  let ex := examplesOf c
  let step0 := stepArgs c (rawOfModel (c.init IxAICore.Triage.spec)) (batchOf ex (c.schedule.headD []))
  let cut := fun (exec : System.FilePath) (args : List Int) (file : System.FilePath) => do
    match IxAIVerify.Ixon.programOf (← IO.FS.readBinFile exec) (args.map field) with
    | some p => IO.FS.writeBinFile file p; IO.println s!"{file}: {p.size} bytes, BLAKE3 {IxAI.blake3 p}"; return true
    | none => IO.eprintln s!"cannot find the program package in {exec}"; return false
  unless ← cut (aiur / "full-bound" / "step-000.ixa") step0 (out / "program-step.ixp") do return 1
  let trainIxa := aiur / "train" / "97d8e1d0fce5371b040383b82e51288759190812309fd522f0e76ff9e3a70868.ixa"
  unless ← cut trainIxa (trainArgs c) (out / "program-train.ixp") do return 1
  let plonk := aiur / "aiurexec" / "ladder" / "plonk" / "proof.bin"
  let index ← IO.FS.readFile (IxAIVerify.projectDir / ".truthmines" / "index.tsv")
  let rows := (index.splitOn "\n").map (·.splitOn "\t")
  let proofOf := fun (name : String) =>
    ((rows.filter fun r => r.getD 0 "" == "check" && r.getD 1 "" == name && r.getD 8 "" == "verified").getLast?).map (·.getD 5 "")
  let names := claimTemplates.map (s!"IxAICertified.full.{·.id}")
  let claims := names.filterMap fun n => (proofOf n).map fun p =>
    Lean.Json.mkObj [("claim", Lean.toJson ((n.splitOn ".").getLastD "")),
      ("name", Lean.toJson n), ("proof", Lean.toJson p)]
  let s := toString
  let receipt := Lean.Json.mkObj [
    ("format", Lean.toJson receiptFormat),
    ("model", Lean.toJson "model.txt"),
    ("environment", Lean.Json.mkObj [("ixe", Lean.toJson (s (IxAIVerify.projectDir / "ix" / "bundle" / "certified_full.ixe"))),
      ("source", Lean.toJson (s (IxAIVerify.projectDir / "ix" / "bundle" / "Certified_full.lean")))]),
    ("training", Lean.Json.arr #[
      Lean.Json.mkObj [("kind", Lean.toJson "aiur-steps"), ("program", Lean.toJson "program-step.ixp"),
        ("proofs", Lean.toJson (s (aiur / "full-bound"))), ("models", Lean.toJson (s modelsPath))],
      Lean.Json.mkObj [("kind", Lean.toJson "aiur-train"), ("program", Lean.toJson "program-train.ixp"),
        ("proof", Lean.toJson (s (aiur / "train" / "fb0a1af2ca9abee5ed0320b30751efd073d5158a65dd3ee146b104976d774c11.proof")))],
      Lean.Json.mkObj ([("kind", Lean.toJson "aiur-exec"), ("aggregator", Lean.toJson aggregator),
        ("program", Lean.toJson "program-step.ixp"), ("root", Lean.toJson (s (aiur / "aiurexec" / "top" / "root"))),
        ("plonk", Lean.toJson (s plonk)), ("plonkBlake3", Lean.toJson (← fileDigestStr plonk))] ++
        (key?.map fun k => [("plonkKey", Lean.toJson (s k))]).getD [])]),
    ("claims", Lean.Json.arr claims.toArray)]
  IO.FS.writeFile (out / "receipt.json") (receipt.pretty ++ "\n")
  IO.println s!"{out / "receipt.json"}: {claims.length} claims, 3 training routes; model weights {(modelDigest (modelOfRaw c.hidden final)).hex}"
  return 0

end IxAICli
