import IxAIVerify.Package
import IxAIVerify.Combined
import IxAIVerify.Cli

/-!
# `ixai-verify`: the consumer's verifier

A small executable with only the specification (`IxAICore`) and the verification layer
(`IxAIVerify`) linked in: no benchmarks, datasets or provers. See `docs/verification.md`.

* `ixai-verify package --commitment FILE [--commitment-blake3 HEX] --receipt FILE`: check a model
  package; outcome `PROVED` (exit 0), `REJECTED` (1), `PREDICTED` (3) or `INCOMPLETE` (4), with
  every hypothesis it rests on.
* `ixai-verify chain --config NAME --program FILE --program-blake3 HEX --proofs DIR --models FILE
  --model FILE`: only the per-step Aiur route: every scheduled step's proof, verified against
  claims built from the specification.
* `ixai-verify trajectory FILE [--job NAME | --job-digest HEX] [--weights HEX]`: check a
  trajectory against the consumer's job (default: `default`).
* `ixai-verify job NAME`: the digest of a named trajectory job.
* `ixai-verify template --config NAME --out FILE`: write the claim templates of a job, as Lean
  source to compile with `ixw compile` before any training.
* `ixai-verify commit --config NAME --template-source FILE --template-env FILE --out FILE
  [--program NAME=FILE]… [--ix-spec HEX] [--plonk-key FILE --wrap-layout FILE]`: write a job
  commitment from the compiled templates, the approved programs, the claim policy and, with the
  last two, the compression pipeline (the terminal PLONK verifying key and the wrapper layout whose
  key the statement names). Nothing in it depends on a trained model.
* `ixai-verify compressed --config NAME --shape steps|blocks:N|tree --aggregator FILE
  --aggregator-blake3 HEX --program FILE --program-blake3 HEX --plonk FILE --plonk-key FILE
  --plonk-key-blake3 HEX --wrap-key-blake3 HEX --model FILE [--models FILE]`: only the compressed
  certificate of an `aiurExec` root: the keys recompiled from the approved packages, the statement
  computed from them and the specification (`--models`: the intermediate models a `tree` root
  hashed), and the PLONK proof verified against the pinned key. No other file of the prover is read.
* `ixai-verify combined --commitment FILE [--commitment-blake3 HEX] --template-env FILE --root DIR
  --plonk FILE --plonk-key FILE --env FILE --partition FILE --run-root DIR --aggregator FILE
  --aggregator-blake3 HEX --program FILE --program-blake3 HEX --model FILE [--theorem NAME]
  [--binding NAME] [--block-steps N]`: one certificate for training and the environment of its
  refinement theorem (`IxAIVerify.Combined`): `aiur_join_check` on the joined root against the
  pinned artifacts and the run computed from the specification, then the PLONK proof against the
  job's pinned key and the statement computed here. Outcome `PROVED`, `REJECTED` or `INCOMPLETE`.
* `ixai-verify read-env FILE`: read an `.ixe` as the verifier does, every record authenticated by
  its address, and report its size and the time taken.
-/

open IxAI IxAIVerify IxAIVerify.Cli

def cmdChain (args : List String) : IO UInt32 := do
  let some c := (flag args "--config").getD "full" |> configNamed?
    | IO.eprintln "unknown config"; return 2
  match flag args "--program", (flag args "--program-blake3").bind Digest.ofHex?, flag args "--proofs",
      flag args "--models", flag args "--model" with
  | some prog, some pd, some proofs, some models, some model =>
    let tools ← Tools.fromEnv
    let ms ← match ← readModels models with
      | .ok ms => pure ms
      | .error e =>
        if ← System.FilePath.pathExists models then IO.println s!"[aiur-steps] REJECTED\n  {e}"; return 1
        else IO.println s!"[aiur-steps] INCOMPLETE\n  {e}"; return 4
    let final ← match ← readModelFile model with
      | .ok m => pure m
      | .missing e => IO.println s!"[aiur-steps] INCOMPLETE\n  {e}"; return 4
      | .malformed e => IO.println s!"[aiur-steps] REJECTED\n  {e}"; return 1
    let r ← withWorkDir fun w => verifyStepRoute tools c prog pd proofs ms final (w / "steps")
    printRoute r
    return r.status.exitCode
  | _, _, _, _, _ =>
    IO.eprintln "usage: ixai-verify chain --config NAME --program FILE --program-blake3 HEX --proofs DIR --models FILE --model FILE"
    return 2

def cmdCompressed (args : List String) : IO UInt32 := do
  let some c := (flag args "--config").getD "full" |> configNamed?
    | IO.eprintln "unknown config"; return 2
  let n := c.schedule.length
  -- The shape, and the steps of one execution, which fix the program's claim.
  let shape? : Option (Compression.ExecShape × Nat) :=
    match (flag args "--shape").getD "steps" with
    | "steps" => some (.steps, 1)
    | "tree" => some (.tree [], n)
    | s => match s.splitOn ":" with
      | ["blocks", k] => k.toNat?.bind fun k => if k > 0 then some (.blocks k, k) else none
      | _ => none
  let usage := "usage: ixai-verify compressed --config NAME --shape steps|blocks:N|tree --aggregator FILE --aggregator-blake3 HEX --program FILE --program-blake3 HEX --plonk FILE --plonk-key FILE --plonk-key-blake3 HEX --wrap-key-blake3 HEX --model FILE [--models FILE]"
  let some (shape0, steps) := shape? | IO.eprintln usage; return 2
  let d := fun (k : String) => (flag args k).bind Digest.ofHex?
  match flag args "--aggregator", d "--aggregator-blake3", flag args "--program", d "--program-blake3",
      flag args "--plonk", flag args "--plonk-key", d "--plonk-key-blake3", d "--wrap-key-blake3",
      flag args "--model" with
  | some ax, some axD, some prog, some progD, some plonk, some key, some keyD, some wrapD, some model =>
    let tools ← Tools.fromEnv
    let pin : Compression.Pin := { plonkKey := keyD, wrapKey := wrapD }
    let finish := fun (status : RouteStatus) (detail hyps : List String) => do
      printRoute { kind := "aiur-exec (compressed)", status, detail, hypotheses := hyps }
      return status.exitCode
    let final ← match ← readModelFile model with
      | .ok m => pure m
      | .missing e => return ← finish .incomplete [e] []
      | .malformed e => return ← finish .rejected [e] []
    if let .error e := checkModelWords c.hidden final then return ← finish .rejected [s!"the submitted model: {e}"] []
    let mut shape := shape0
    if let .tree _ := shape then
      let some mf := flag args "--models" | return ← finish .incomplete ["a tree root needs the intermediate models it hashed (--models FILE)"] []
      match ← readModels mf with
      | .error e =>
        return ← finish (if ← System.FilePath.pathExists mf then .rejected else .incomplete) [e] []
      | .ok ms =>
        for (m, i) in ms.zipIdx do
          if let .error e := checkModelWords c.hidden m then return ← finish .rejected [s!"the model after step {i}: {e}"] []
        if ms.getLast? != some final then return ← finish .rejected ["the last intermediate model is not the submitted model"] []
        shape := .tree ms
    let verifier ← fileDigestStr tools.plonkVerify
    let checker ← fileDigestStr tools.aiurExecCheck
    let programHyp := match shape with
      | .steps => (stepHypotheses tools "").drop 1
      | _ => ["the approved program computes `IxAICore.train` over the scheduled batches when its executions chain from config.init: for `Fixed::train_block` through `train_of_deployed_blocks`, for `FixedTree::train_tree` an unproved theorem (`train_tree_sound`, fork ix-aiurexec docs/aiur-composition.md) that also assumes the circuit's BLAKE3 is BLAKE3"]
    let hyps := [s!"`aiur_exec_check --keys` (BLAKE3 {checker}) recompiles the root and program keys from the approved packages as the prover's compilation does",
      "the aiurExec aggregator is an unproven prototype (fork ix-aiurexec): its soundness is assumed"] ++
      terminalHypotheses tools verifier pin ++ programHyp
    withWorkDir fun w => do
      let axD' ← fileDigest? ax
      if axD'.isNone then return ← finish .incomplete [s!"aggregator {ax} is missing"] hyps
      if axD' != some axD then return ← finish .rejected [s!"aggregator {ax} is not the approved {axD}"] hyps
      let pkg ← match ← approvedProgram prog progD w with
        | .ok p => pure p
        | .error e => return ← finish (if ← System.FilePath.pathExists prog then .rejected else .incomplete) [e] hyps
      let (ks, keys?, why) ← recompiledKeys tools ax pkg shape steps
      let some keys := keys? | return ← finish ks [why] hyps
      unless ks == .verified do return ← finish ks [why] hyps
      let (status, detail) ← verifyCompressed tools c shape keys pin key plonk final (w / "plonk")
      finish status detail hyps
  | _, _, _, _, _, _, _, _, _ => IO.eprintln usage; return 2

def cmdCombined (args : List String) : IO UInt32 := do
  let usage := "usage: ixai-verify combined --commitment FILE [--commitment-blake3 HEX] --template-env FILE --root DIR --plonk FILE --plonk-key FILE --env FILE --partition FILE --run-root DIR --aggregator FILE --aggregator-blake3 HEX --program FILE --program-blake3 HEX --model FILE [--theorem NAME] [--binding NAME] [--block-steps N] [--ixvm-blake3 HEX] [--join-aggregator-blake3 HEX]"
  let d := fun (k : String) => (flag args k).bind Digest.ofHex?
  let steps? := match flag args "--block-steps" with
    | none => some Combined.defaultBlockSteps
    | some s => s.toNat?.bind fun n => if n > 0 then some n else none
  match flag args "--commitment", flag args "--template-env", flag args "--root", flag args "--plonk",
      flag args "--plonk-key", flag args "--env", flag args "--partition", flag args "--run-root",
      flag args "--aggregator", d "--aggregator-blake3", flag args "--program", d "--program-blake3",
      flag args "--model", steps? with
  | some cmPath, some tenv, some root, some plonk, some key, some env, some part, some runRoot,
    some ax, some axD, some prog, some progD, some model, some blockSteps =>
    let tools ← Tools.fromEnv
    -- The two circuits are approved by digest: the built-in pins, or digests named here.
    let circuit := fun (k : String) (pin : String) => match flag args k with
      | none => some pin
      | some h => (Digest.ofHex? h).map Digest.hex
    let (ixvmD, aggrD) ← match circuit "--ixvm-blake3" Combined.ixvmPin,
        circuit "--join-aggregator-blake3" Combined.joinAggregatorPin with
      | some a, some b => pure (a, b)
      | _, _ => IO.eprintln usage; return 2
    let arts ← Combined.Artifacts.fromEnv ixvmD aggrD
    let finish := fun (o : Outcome) (lines : Array String) (rr : Option RouteResult) => do
      for l in lines do IO.println l
      if let some x := rr then printRoute x
      IO.println s!"OUTCOME: {o.label}"
      return o.exitCode
    let (cm, rep) ← match ← readCommitment cmPath (flag args "--commitment-blake3") {} with
      | .ok x => pure x
      | .error (o, rep) => return ← finish o rep.lines none
    let final ← match ← readModelFile model with
      | .ok m => pure m
      | .missing e => return ← finish .incomplete (rep.lines.push s!"  MISSING: {e}") none
      | .malformed e => return ← finish .rejected (rep.lines.push s!"  REJECT: {e}") none
    let ap : Combined.Approved :=
      { runAggregator := ax, runAggregatorDigest := axD, program := prog, programDigest := progD
        templateEnv := tenv, blockSteps
        theoremName := (flag args "--theorem").getD Combined.defaultTheorem
        binding := (flag args "--binding").getD Combined.defaultBinding }
    let ev : Combined.Evidence :=
      { root, plonk, plonkKey := key, env, partition := part, runRoot }
    let res ← withWorkDir fun w => Combined.verifyCombined tools cm arts ap ev final (w / "combined")
    let o : Outcome := match res.status with
      | .verified => .proved
      | .rejected => .rejected
      | _ => .incomplete
    let lines := if o == .proved then rep.lines.push s!"proved: {Combined.provedStatement cm ap final}" else rep.lines
    finish o lines (some res)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ => IO.eprintln usage; return 2

def cmdPackage (args : List String) : IO UInt32 := do
  match flag args "--commitment", flag args "--receipt" with
  | some c, some r =>
    let tools ← Tools.fromEnv
    let (o, rep) ← withWorkDir (verifyPackage tools c r (flag args "--commitment-blake3"))
    for l in rep.lines do IO.println l
    IO.println "hypotheses (what this outcome assumes):"
    for h in rep.hypotheses do IO.println s!"  - {h}"
    IO.println s!"OUTCOME: {o.label}"
    return o.exitCode
  | _, _ =>
    IO.eprintln "usage: ixai-verify package --commitment FILE [--commitment-blake3 HEX] --receipt FILE"
    return 2

def cmdTemplate (args : List String) : IO UInt32 := do
  let size := (flag args "--config").getD "full"
  let some c := configNamed? size | IO.eprintln s!"unknown config {size}"; return 2
  let some out := flag args "--out" | IO.eprintln "--out FILE is required"; return 2
  let text := templateSource size c
  IO.FS.writeFile out text
  IO.println s!"wrote {out}: {claimTemplates.length} claim templates for config {size}, BLAKE3 {IxAI.blake3 text.toUTF8}"
  return 0

/-- The specification digest (`Ix.SpecDigest.specDigest`) of the pinned ix build that `ix/ixw`
runs: the claims' `spec` field when the job does not name another. -/
def defaultIxSpec : String := "7e6bc58cf52458db99edc516b71fb18a5b74dfd8eb01ca6cf24b82bbaa623a82"

def cmdCommit (args : List String) : IO UInt32 := do
  let size := (flag args "--config").getD "full"
  let some c := configNamed? size | IO.eprintln s!"unknown config {size}"; return 2
  let some srcPath := flag args "--template-source" | IO.eprintln "--template-source FILE is required"; return 2
  let some envPath := flag args "--template-env" | IO.eprintln "--template-env FILE is required"; return 2
  let some out := flag args "--out" | IO.eprintln "--out FILE is required"; return 2
  let some spec := Digest.ofHex? ((flag args "--ix-spec").getD defaultIxSpec)
    | IO.eprintln "--ix-spec: not a digest"; return 2
  let src ← IO.FS.readFile srcPath
  unless src == templateSource size c do
    IO.eprintln s!"{srcPath} is not the template source of config {size} (`ixai-verify template`)"; return 1
  let envBytes ← IO.FS.readBinFile envPath
  let env ← IO.ofExcept (Ixon.readEnv envBytes)
  let some binding := env.binding
    | IO.eprintln s!"{envPath} carries no role binding (an .ixe of envelope version 5 is needed)"; return 1
  let tools ← Tools.fromEnv
  let addr := fun (n : String) => do
    match (← addrOf tools envPath n).bind Digest.ofHex? with
    | some a => pure a
    | none => throw (IO.userError s!"cannot resolve {n} in {envPath}")
  let mut programs : List (String × String) := []
  for p in flags args "--program" do
    match p.splitOn "=" with
    | [name, file] => programs := programs ++ [(name, ← fileDigestStr file)]
    | _ => IO.eprintln s!"malformed --program {p}"; return 2
  let enc ← modelEncodingNames.mapM fun (_, n) => addr n
  let encoding : ModelEncoding :=
    { modelMk := enc[0]!, listCons := enc[1]!, listNil := enc[2]!, fxMk := enc[3]!, intOfNat := enc[4]!,
      intNegSucc := enc[5]! }
  let actions ← actionNames.mapM fun (n, a) => do pure (a, ← addr n)
  let claims ← claimTemplates.mapM fun t => do
    let a ← addr s!"{templateNamespace size}.{t.id}"
    let d ← IO.ofExcept (env.definition? a)
    let v ← IO.ofExcept (env.resolve d d.value)
    let some body := Ixon.Term.unbind t.holes.length v
      | throw (IO.userError s!"template {t.id} does not bind its {t.holes.length} holes")
    pure ({ id := t.id, role := t.role, holes := t.holes, statement := body } : CommittedClaim)
  let cm : Commitment :=
    { specName := "IxAICore.Triage.spec", specAddress := (← addr "IxAICore.Triage.spec").hex
      trainAddress := (← addr "IxAICore.train").hex
      configName := size, config := c, configDigest := (configDigest c).hex
      datasetCount := c.trainSize, datasetRoot := (datasetRoot c).hex, programs
      claimEncoding := claimEncodingDigest.hex
      policy := { spec, binding }, encoding, actions
      templateSource := (IxAI.blake3 src.toUTF8).hex, templateEnv := (IxAI.blake3 envBytes).hex, claims }
  let compression ← match flag args "--plonk-key", flag args "--wrap-layout" with
    | none, none => pure none
    | some key, some layout =>
      let lj ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile layout))
      let some wrapKey := (jStr lj ["layout", "key_blake3"]).toOption.bind Digest.ofHex?
        | IO.eprintln s!"{layout}: no layout.key_blake3"; return 1
      pure (some ({ plonkKey := IxAI.blake3 (← IO.FS.readBinFile key), wrapKey } : Compression.Pin))
    | _, _ => IO.eprintln "--plonk-key and --wrap-layout go together"; return 2
  let cm := { cm with compression }
  let text := cm.toJson.pretty ++ "\n"
  IO.FS.writeFile out text
  IO.println s!"wrote {out}: BLAKE3 {IxAI.blake3 text.toUTF8}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "package" :: rest => cmdPackage rest
  | "compressed" :: rest => cmdCompressed rest
  | "combined" :: rest => cmdCombined rest
  | "chain" :: rest => cmdChain rest
  | "trajectory" :: file :: rest => trajectoryCommand file rest
  | ["job", name] =>
    match namedJobs.find? (·.1 == name) with
    | some (_, j) => IO.println s!"{name}: {j.digest}"; return 0
    | none => IO.eprintln s!"unknown job {name}"; return 2
  | "template" :: rest => cmdTemplate rest
  | "commit" :: rest => cmdCommit rest
  | ["blake3", f] => do IO.println (IxAI.blake3 (← IO.FS.readBinFile f)).hex; return 0
  | ["read-env", f] => do
    let t0 ← IO.monoMsNow
    match Ixon.readEnv (← IO.FS.readBinFile f) with
    | .ok e =>
      IO.println s!"{f}: {e.blobs.size} blobs and {e.consts.size} constants, each authenticated by its address ({(← IO.monoMsNow) - t0} ms)"
      return 0
    | .error e => IO.println s!"REJECT: {f}: {e}"; return 1
  | _ =>
    IO.eprintln "usage: ixai-verify (package|chain|compressed|combined|trajectory|job|template|commit|blake3|read-env) …; see docs/verification.md"
    return 2
