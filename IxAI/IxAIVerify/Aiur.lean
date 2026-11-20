import IxAIVerify.Spec
import IxAIVerify.Ixon
import IxAIVerify.Tools
import IxAIVerify.Compression
import Lean.Data.Json

/-!
# Training evidence from Aiur proofs

Each route checks one kind of training evidence against claims built here from the specification
(`IxAIVerify.Spec`) and an approved program package, never against a prover's report:

* `aiur-steps`: one `Fixed::step` STARK proof per scheduled step, each verified by `verify_claim`
  against `m_i ‖ batch_i ‖ lr → m_{i+1}`. `m_0` is `config.init`, `m_600` is the submitted model,
  and the models in between are the prover's, chained by the proofs. Every scheduled step must be
  present: a missing proof makes the route incomplete, never accepted.
* `aiur-train`: one `Fixed::train` STARK proof of `m_0 ‖ lr ‖ xs ‖ ts → model`.
* `aiur-exec`: an `aiurExec` root over chained `Fixed::step` executions, compressed by Ix's
  compression pipeline into one PLONK certificate. `aiur_exec_check` checks the root's claim
  against the specification and recompiles the root and program keys. When the job pins the
  pipeline (`Compression.Pin`), `aiur_plonk_verify` then verifies the certificate against the
  pinned verifying key and the statement computed here (`Compression.execStatement`) from those
  keys and the specification, and the route is `verified`; without a pin it is at best
  `attested`.

The approved program is a program package whose BLAKE3 the job commitment names. The verifier
wraps it in an execution package of its own (`Ixon.wrapPackage`), so `verify_claim` recompiles the
key from the approved program and from nothing a prover supplied.
-/

namespace IxAIVerify

open IxAI IxAICore

inductive RouteStatus where
  /-- Every proof of the route was verified here against expected claims. -/
  | verified
  /-- The route's claims were checked here, but a proof it depends on was verified only at proving
  time. -/
  | attested
  | incomplete
  | rejected
  deriving Repr, BEq, Inhabited

def RouteStatus.label : RouteStatus → String
  | .verified => "verified"
  | .attested => "attested (not re-verified here)"
  | .incomplete => "INCOMPLETE"
  | .rejected => "REJECTED"

structure RouteResult where
  kind : String
  status : RouteStatus
  detail : List String
  /-- What a consumer assumes when relying on this route. -/
  hypotheses : List String := []
  deriving Inhabited

/-- The proof file name of step `i`: at least three digits, zero-padded, so names sort in step order
and never collide (`step-999`, `step-1000`). -/
def stepName (i : Nat) : String :=
  let d := toString i
  s!"step-{String.ofList (List.replicate (3 - d.length) '0')}{d}"

def stepHypotheses (tools : Tools) (verifier : String) : List String :=
  [s!"STARK soundness: an accepting `verify_claim` (BLAKE3 {verifier}, {tools.verifyClaim}) implies the claimed execution of the approved program",
   "the approved `Fixed::step` package computes `Model.step` on these words: `step_sound_deployed` (IxAIRefine/Fixed/Deployed.lean) under its hypothesis `StepOnlyParity`, which is `#eval`-checked, not proved",
   "compilation `Fixed.source` ↦ circuits is an `#eval` parity check (`IxAIRefine.Check`), not a theorem",
   "the claim encoding (`IxAIVerify.stepClaimEncoding`) is read the same way by the circuit: checker code, not a Lean definition the claim names",
   "native evaluation of the specification here (examples, schedule, `config.init`; compiled Lean) agrees with kernel evaluation (`#eval` parity of the compiler)"]

/-- Write the approved program, wrapped, into `work`, after checking its digest. -/
def approvedPackage (program : System.FilePath) (expected : Digest) (work : System.FilePath) :
    IO (Except String System.FilePath) := do
  unless ← program.pathExists do return .error s!"approved program package {program} is missing"
  let bytes ← IO.FS.readBinFile program
  let d := blake3 bytes
  if d != expected then
    return .error s!"program package {program} has BLAKE3 {d}, not the approved {expected}"
  unless Ixon.isPackage bytes do return .error s!"{program} is not an Aiur program package"
  IO.FS.createDirAll work
  let path := work / s!"approved-{expected.short}.exec.ixa"
  IO.FS.writeBinFile path (Ixon.wrapPackage bytes)
  return .ok path

/-- A process that never reached its own code: not found, not executable, or its shared libraries
not loadable. Anything else a verifier does once started, including a panic, is its verdict on the
evidence it was given. -/
def notRun (r : IO.Process.Output) : Bool :=
  r.exitCode == 127 || r.exitCode == 126 ||
    (r.stderr.splitOn "error while loading shared libraries").length > 1

/-- The outcome of checking a list of claims with one verifier process. -/
inductive BatchResult where
  /-- Every claim verified. -/
  | ok
  /-- The verifier read the evidence and refused it: the listed claims (1-based) failed, or the
  process stopped after the key was built and before every claim had a verdict. -/
  | refused (why : List String)
  /-- The verifier did not get to the evidence: it could not start, or it stopped before its key
  was built. -/
  | unavailable (why : String)

/-- Verify `jobs`, each `(proof, arguments, output)`, with one `verify_claim --batch` process: the
key is compiled once from `pkg`, and the claims are checked on every core. The argument and output
files are written to `work` and removed afterwards. -/
def verifyBatch (tools : Tools) (pkg : System.FilePath) (work : System.FilePath)
    (jobs : List (System.FilePath × List Int × List Int)) (threads : Option Nat := none) :
    IO BatchResult := do
  IO.FS.createDirAll work
  let mut lines : Array String := #[]
  let mut files : Array System.FilePath := #[]
  for ((proof, args, out), i) in jobs.zipIdx do
    let a := work / s!"claim-{i}.args"
    let o := work / s!"claim-{i}.out"
    IO.FS.writeFile a (joinInts args)
    IO.FS.writeFile o (joinInts out)
    files := files.push a |>.push o
    lines := lines.push s!"{proof} {a} {o}"
  let manifest := work / "manifest.txt"
  IO.FS.writeFile manifest ("\n".intercalate lines.toList ++ "\n")
  files := files.push manifest
  let args := #["--batch", pkg.toString, manifest.toString] ++ (threads.map (#[toString ·])).getD #[]
  let r? ← run? tools.verifyClaim args
  for f in files do
    try IO.FS.removeFile f catch _ => pure ()
  let some r := r? | return .unavailable s!"cannot run {tools.verifyClaim}"
  if notRun r then return .unavailable s!"{tools.verifyClaim} did not start: {lastChars r.stderr 160}"
  let out := r.stdout.splitOn "\n"
  unless out.any (·.startsWith "key ready") do
    return .unavailable s!"{tools.verifyClaim} stopped before reading any proof: {lastChars (r.stderr ++ r.stdout) 200}"
  let oks := out.filter (·.startsWith "ok ")
  let fails := out.filter (·.startsWith "fail ")
  if r.exitCode == 0 && fails.isEmpty && oks.length == jobs.length then return .ok
  if !fails.isEmpty then
    return .refused (s!"{fails.length} of {jobs.length} claims do not verify" :: fails.take 3)
  return .refused [s!"the verifier stopped after the key was built, with {oks.length} of {jobs.length} verdicts (exit {r.exitCode}): {lastChars r.stderr 200}"]

/-- Read a models file: one model per line, raw words. -/
def readModels (path : System.FilePath) : IO (Except String (List (List Int))) := do
  unless ← path.pathExists do return .error s!"{path} is missing"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (·.trimAscii.toString != "")
  return lines.mapM fun l => parseInts (words l)

def verifyStepRoute (tools : Tools) (c : Config) (program : System.FilePath) (programDigest : Digest)
    (proofs : System.FilePath) (models : List (List Int)) (final : List Int)
    (work : System.FilePath) (threads : Option Nat := none) : IO RouteResult := do
  let verifier ← fileDigestStr tools.verifyClaim
  let hyps := stepHypotheses tools verifier
  let sched := c.schedule
  let n := sched.length
  let mut missing : Array Nat := #[]
  for i in List.range n do
    unless ← (proofs / s!"{stepName i}.proof").pathExists do missing := missing.push i
  if !missing.isEmpty || models.length != n then
    return { kind := "aiur-steps", status := .incomplete, hypotheses := hyps
             detail := [s!"{n - missing.size} of {n} scheduled step proofs present" ++
               (if missing.isEmpty then "" else s!" (missing steps {missing.toList.take 5}{if missing.size > 5 then ", …" else ""})"),
               s!"{models.length} of {n} intermediate models supplied"] }
  for (m, i) in models.zipIdx do
    if let .error e := checkModelWords c.hidden m then
      return { kind := "aiur-steps", status := .rejected, hypotheses := hyps
               detail := [s!"the model after step {i}: {e}"] }
  if models.getLast? != some final then
    return { kind := "aiur-steps", status := .rejected, hypotheses := hyps
             detail := ["the last proven step does not end at the submitted model"] }
  match ← approvedPackage program programDigest work with
  | .error e => return { kind := "aiur-steps", status := .rejected, detail := [e], hypotheses := hyps }
  | .ok pkg =>
    let ex := examplesOf c
    let m0 := rawOfModel (c.init Triage.spec)
    let befores := m0 :: models.dropLast
    let jobs := ((sched.zip (befores.zip models)).zipIdx).map fun ((idx, before, after), i) =>
      (proofs / s!"{stepName i}.proof", stepArgs c before (batchOf ex idx), after)
    let t0 ← IO.monoMsNow
    let result ← verifyBatch tools pkg work jobs threads
    let ms := (← IO.monoMsNow) - t0
    match result with
    | .refused why =>
      return { kind := "aiur-steps", status := .rejected, hypotheses := hyps, detail := why }
    | .unavailable why =>
      return { kind := "aiur-steps", status := .incomplete, hypotheses := hyps
               detail := [s!"{n} step proofs not checked: the verifier did not run", why] }
    | .ok =>
      return { kind := "aiur-steps", status := .verified, hypotheses := hyps
               detail := [s!"{n} of {n} step proofs verified against claims built from the specification ({ms / 1000}.{(ms % 1000) / 100} s, one key)",
                          s!"chain: config.init → … → submitted model, batches and rate from the schedule; every model in [{weightLo}, {weightHi})",
                          s!"approved program {programDigest}"] }

def verifyTrainRoute (tools : Tools) (c : Config) (program : System.FilePath) (programDigest : Digest)
    (proof : System.FilePath) (final : List Int) (work : System.FilePath) : IO RouteResult := do
  let verifier ← fileDigestStr tools.verifyClaim
  let hyps := (stepHypotheses tools verifier).map fun h =>
    if (h.splitOn "`Fixed::step` package").length > 1 then
      "the approved `Fixed::train` package computes `IxAICore.train` on these words: `train_sound_eq` and `train_refines` (IxAIRefine/Fixed/Soundness.lean), over a compilation of `Fixed.source` that is `#eval`-checked, not proved"
    else h
  unless ← proof.pathExists do
    return { kind := "aiur-train", status := .incomplete, detail := [s!"{proof} is missing"], hypotheses := hyps }
  if let .error e := checkModelWords c.hidden final then
    return { kind := "aiur-train", status := .rejected, detail := [s!"the submitted model: {e}"], hypotheses := hyps }
  match ← approvedPackage program programDigest work with
  | .error e => return { kind := "aiur-train", status := .rejected, detail := [e], hypotheses := hyps }
  | .ok pkg =>
    let t0 ← IO.monoMsNow
    match ← verifyBatch tools pkg work [(proof, trainArgs c, final)] with
    | .ok => return { kind := "aiur-train", status := .verified, hypotheses := hyps
                      detail := [s!"one proof of all {c.schedule.length} steps verified: config.init and the scheduled batches to the submitted model ({((← IO.monoMsNow) - t0) / 1000} s)",
                                 s!"approved program {programDigest}"] }
    | .refused e => return { kind := "aiur-train", status := .rejected, detail := e, hypotheses := hyps }
    | .unavailable e => return { kind := "aiur-train", status := .incomplete, detail := [e], hypotheses := hyps }

/-- The batches of the schedule, as `(xs, ts)` words. -/
def scheduledBatches (c : Config) : List (List Int × List Int) :=
  let ex := examplesOf c
  c.schedule.map fun idx => batchWords (batchOf ex idx)

/-- What the terminal PLONK check rests on, beyond the root claim's own hypotheses. -/
def terminalHypotheses (tools : Tools) (verifier : String) (pin : Compression.Pin) : List String :=
  [s!"`aiur_plonk_verify` (BLAKE3 {verifier}, {tools.plonkVerify}) runs Ix's gnark PLONK verifier (`tools/gnark` `verifyAiurProof`, BN254, Solidity-target transcript) as the compression pipeline does at proving time",
   s!"PLONK knowledge soundness (gnark, BN254 KZG) for the pinned verifying key {pin.plonkKey.short}…, which fixes the terminal circuit: the Lean-exported constraint system of `CompressFinalNarrow::verify_accumulator_v1` with its in-circuit pairing check, and the narrow stage's key and policy it embeds",
   "the KZG setup is the Aztec Ignition ceremony (MAIN IGNITION, final contributions 196 and 197, Ix's release SRS): the key's [1]G1, [1]G2 and [τ]G2 are checked equal to the parameters bundled in the verifier (Ix's release recursive key), so a development SRS with a known trapdoor is refused; soundness of the PLONK and of the narrow stage's KZG needs τ to be unknown, i.e. at least one Ignition contributor to have destroyed its secret",
   "each recursion layer between the root and the PLONK is sound and verifies what its predecessor claims: the terminal folds and checks the narrow stage's deferred pairing; the narrow stage (`CompressNarrowFixed::step_v1`, packed-SHPLONK KZG over BN254) verifies the CompressGL proof against the statement; CompressGL (`CompressGL::verify_root`, a Goldilocks FRI verifier over BN254) verifies the wrapper's proof under the key and claims the statement digests; the wrapper (`CompressWrap::verify_root`, a Goldilocks FRI STARK) verifies the root STARK under the root key and claim. These verifier programs are Aiur written in Lean, not proved to implement their verifiers; the Rust lowering of circuits, key writers, statements and policies are trusted (Ix docs/aiur-compression-architecture.md §3)",
   "STARK soundness (multi-stark, Goldilocks FRI, BLAKE3 transcripts) of the root, the wrapper and CompressGL at Ix's parameters; packed-SHPLONK soundness (Ix docs/aiur-packed-kzg-soundness.md)",
   s!"the statement format is Ix's (`compress_wrap::Statement`, `WrapPolicy::statement_for`, wrapper claim prefix {Compression.wrapClaimPrefix}): recomputed here, but its meaning is taken from Ix's source; the wrapper key {pin.wrapKey.short}… is the job's pin (the pipeline's `m16384w64-v3` layout), not recompiled here",
   "BLAKE3 is collision resistant: every key, claim and model enters the statement through a BLAKE3 digest"]

/-- Verify a terminal PLONK certificate against the pinned key and a statement computed by the
caller. The key file is checked against the pin and copied into `work` before the verifier reads
it. -/
def verifyTerminal (tools : Tools) (pin : Compression.Pin) (key proof : System.FilePath)
    (statement : Digest) (work : System.FilePath) : IO (RouteStatus × List String) := do
  unless ← key.pathExists do return (.incomplete, [s!"PLONK verifying key {key} is missing"])
  let keyBytes ← IO.FS.readBinFile key
  let kd := blake3 keyBytes
  if kd != pin.plonkKey then
    return (.rejected, [s!"PLONK verifying key {key} has BLAKE3 {kd}, not the pinned {pin.plonkKey}"])
  unless ← proof.pathExists do return (.incomplete, [s!"PLONK proof {proof} is missing"])
  IO.FS.createDirAll work
  let copy := work / s!"plonk-{pin.plonkKey.short}.vk"
  IO.FS.writeBinFile copy keyBytes
  let t0 ← IO.monoMsNow
  let r? ← run? tools.plonkVerify #[copy.toString, pin.plonkKey.hex, proof.toString, statement.hex]
  let ms := (← IO.monoMsNow) - t0
  try IO.FS.removeFile copy catch _ => pure ()
  let some r := r? | return (.incomplete, [s!"cannot run {tools.plonkVerify}"])
  if notRun r then
    return (.incomplete, [s!"{tools.plonkVerify} did not start: {lastChars r.stderr 160}"])
  let out := r.stdout.splitOn "\n"
  unless out.any (·.startsWith "key ready") do
    return (.incomplete, [s!"{tools.plonkVerify} stopped before reading the proof: {lastChars (r.stderr ++ r.stdout) 200}"])
  let (l0, l1) := Compression.statementLimbs statement
  let limbs := out.any (· == s!"statement {statement.hex}: public inputs {l0} {l1}")
  let accept := out.find? fun l => l.startsWith "ACCEPT" && (l.splitOn statement.hex).length > 1
  match r.exitCode == 0, limbs, accept with
  | true, true, some a =>
    return (.verified, [s!"PLONK certificate verified against the pinned key {pin.plonkKey.short}… and statement {statement.hex} ({ms} ms for the verifier process): {a}",
                        s!"public inputs {l0}, {l1}: the statement's halves, computed here"])
  | true, false, _ =>
    return (.rejected, [s!"the verifier's public inputs are not the halves of the statement computed here: {lastChars r.stdout 200}"])
  | _, _, _ =>
    let why := (out.find? (·.startsWith "REJECT")).getD s!"exit {r.exitCode}: {lastChars (r.stderr ++ r.stdout) 300}"
    return (.rejected, [s!"{tools.plonkVerify}: {why}"])

/-- The program file an `aiur_exec_check` run reads: an approved program package, wrapped as
`approvedPackage` does, or an approved execution package as it is. -/
def approvedProgram (program : System.FilePath) (expected : Digest) (work : System.FilePath) :
    IO (Except String System.FilePath) := do
  unless ← program.pathExists do return .error s!"approved program {program} is missing"
  let bytes ← IO.FS.readBinFile program
  if Ixon.isPackage bytes then return ← approvedPackage program expected work
  let d := blake3 bytes
  if d != expected then
    return .error s!"program {program} has BLAKE3 {d}, not the approved {expected}"
  unless bytes.size > Ixon.header && (bytes.extract 0 Ixon.header).toList == Ixon.executionMagic ++ Ixon.nat Ixon.formatVersion do
    return .error s!"{program} is neither an Aiur program package nor an execution package"
  IO.FS.createDirAll work
  let path := work / s!"approved-{expected.short}.exec.ixa"
  IO.FS.writeBinFile path bytes
  return .ok path

/-- The approved programs' keys, recompiled by `aiur_exec_check --keys`, without reading any file
of the prover. -/
def recompiledKeys (tools : Tools) (aggregator program : System.FilePath) (shape : Compression.ExecShape)
    (steps : Nat) : IO (RouteStatus × Option Compression.ExecKeys × String) := do
  let tree := match shape with | .tree _ => #["--tree"] | _ => #[]
  let r? ← run? tools.aiurExecCheck (#["--keys", aggregator.toString, program.toString, toString steps] ++ tree)
  let some r := r? | return (.incomplete, none, s!"cannot run {tools.aiurExecCheck}")
  if notRun r then return (.incomplete, none, s!"{tools.aiurExecCheck} did not start: {lastChars r.stderr 160}")
  match Compression.parseExecKeys r.stdout with
  | none => return (.incomplete, none, s!"{tools.aiurExecCheck} printed no recompiled keys: {lastChars (r.stderr ++ r.stdout) 160}")
  | some k =>
    if r.exitCode == 0 && (r.stdout.splitOn "\n").any (·.startsWith "ACCEPT") then return (.verified, some k, "")
    return (.rejected, some k, s!"aiur_exec_check --keys: {lastChars (r.stderr ++ r.stdout) 200}")

/-- The statement of the compressed root that chains `config.init` over the schedule's batches to
`final`, through `keys`, and the terminal check of `plonk` against it. -/
def verifyCompressed (tools : Tools) (c : Config) (shape : Compression.ExecShape)
    (keys : Compression.ExecKeys) (pin : Compression.Pin) (key plonk : System.FilePath)
    (final : List Int) (work : System.FilePath) : IO (RouteStatus × List String) := do
  match Compression.execStatement pin.wrapKey keys shape c.lrRaw (rawOfModel (c.init Triage.spec)) final
      (scheduledBatches c) with
  | .error e => return (.rejected, [s!"the expected statement: {e}"])
  | .ok s =>
    let (status, detail) ← verifyTerminal tools pin key plonk s work
    return (status, s!"statement {s.short}… computed from the root key {keys.aggregator.short}… (entry {keys.aggregatorEntry}), the program key {keys.program.short}… (entry {keys.programEntry}), {shape.label} from config.init over the scheduled batches to the submitted model, and the wrapper key {pin.wrapKey.short}…" :: detail)

def verifyExecRoute (tools : Tools) (c : Config) (aggregator : System.FilePath) (aggregatorDigest : Digest)
    (program : System.FilePath) (programDigest : Digest) (root : System.FilePath)
    (plonk : System.FilePath) (plonkDigest : Digest) (final : List Int) (work : System.FilePath)
    (pin : Option Compression.Pin := none) (plonkKey : Option System.FilePath := none) :
    IO RouteResult := do
  let checker ← fileDigestStr tools.aiurExecCheck
  let rootHyps := [s!"`aiur_exec_check` (BLAKE3 {checker}) reads the root claim as the circuit does and recompiles the root and program keys from the approved packages",
    "the aiurExec aggregator is an unproven prototype (fork ix-aiurexec): its soundness is assumed"]
  let attestedHyps := rootHyps ++
    ["the root STARK proof is bound by the compression pipeline's PLONK certificate, verified at proving time only: the job pins no PLONK verifying key; the certificate's statement binds root-vk.bin and root-claims.bin",
     "STARK and PLONK (gnark, BN254 KZG, Ignition SRS) soundness"]
  let hyps := match pin with
    | none => attestedHyps
    | some _ => rootHyps
  let sched := c.schedule
  if let .error e := checkModelWords c.hidden final then
    return { kind := "aiur-exec", status := .rejected, detail := [s!"the submitted model: {e}"], hypotheses := hyps }
  match ← approvedPackage program programDigest work with
  | .error e => return { kind := "aiur-exec", status := .rejected, detail := [e], hypotheses := hyps }
  | .ok pkg =>
    let aggD ← fileDigest? aggregator
    if aggD.isNone then
      return { kind := "aiur-exec", status := .incomplete, detail := [s!"aggregator {aggregator} is missing"], hypotheses := hyps }
    if aggD != some aggregatorDigest then
      return { kind := "aiur-exec", status := .rejected, hypotheses := hyps
               detail := [s!"aggregator {aggregator} is not the approved {aggregatorDigest}"] }
    let plonkD ← fileDigest? plonk
    if plonkD.isNone then
      return { kind := "aiur-exec", status := .incomplete, detail := [s!"{plonk} is missing"], hypotheses := hyps }
    if plonkD != some plonkDigest then
      return { kind := "aiur-exec", status := .rejected, hypotheses := hyps
               detail := [s!"PLONK proof {plonk} is not the committed {plonkDigest}"] }
    let words := scheduledBatches c
    let spec := rawOfModel (c.init Triage.spec) ++ [c.lrRaw] ++ (words.map (·.1)).flatten ++ (words.map (·.2)).flatten
    let a := work / "exec.spec"
    let o := work / "exec.out"
    IO.FS.writeFile a (joinInts spec)
    IO.FS.writeFile o (joinInts final)
    let r? ← run? tools.aiurExecCheck #[aggregator.toString, pkg.toString, root.toString, a.toString,
        o.toString, toString sched.length]
    for f in [a, o] do
      try IO.FS.removeFile f catch _ => pure ()
    match r? with
    | none => return { kind := "aiur-exec", status := .incomplete, detail := [s!"cannot run {tools.aiurExecCheck}"], hypotheses := hyps }
    | some r =>
      let accept := ((r.stdout.splitOn "\n").find? (·.startsWith "ACCEPT")).getD ""
      -- The checker prints an `ok:` line for each check of the evidence. Stopping before the first
      -- one, without a REJECT, means it failed in its own setup (keys of the approved programs) or
      -- could not read the root's files.
      let started := (r.stdout.splitOn "\n").any (·.startsWith "ok:") ||
        ((r.stderr ++ r.stdout).splitOn "REJECT").length > 1
      if notRun r || (r.exitCode != 0 && !started) then
        return { kind := "aiur-exec", status := .incomplete, hypotheses := hyps
                 detail := [s!"{tools.aiurExecCheck} did not reach the evidence: {lastChars (r.stderr ++ r.stdout) 160}"] }
      unless r.exitCode == 0 && accept != "" do
        return { kind := "aiur-exec", status := .rejected, hypotheses := hyps
                 detail := [s!"aiur_exec_check: {lastChars (r.stderr ++ r.stdout) 300}"] }
      let claimLine := s!"root claim checked against the specification: {accept}"
      match pin with
      | none =>
        return { kind := "aiur-exec", status := .attested, hypotheses := hyps
                 detail := [claimLine, s!"PLONK proof {plonkDigest} is the one the receipt names; not re-verified here: the job pins no compression pipeline"] }
      | some p =>
        let verifier ← fileDigestStr tools.plonkVerify
        let hyps := hyps ++ terminalHypotheses tools verifier p ++ (stepHypotheses tools "").drop 1
        let some key := plonkKey
          | return { kind := "aiur-exec", status := .incomplete, hypotheses := hyps
                     detail := [claimLine, "the job pins a PLONK verifying key, but the route names no key file (`plonkKey`)"] }
        let some keys := Compression.parseExecKeys r.stdout
          | return { kind := "aiur-exec", status := .incomplete, hypotheses := hyps
                     detail := [claimLine, s!"{tools.aiurExecCheck} printed no recompiled keys"] }
        let (status, detail) ← verifyCompressed tools c .steps keys p key plonk final (work / "plonk")
        return { kind := "aiur-exec", status, hypotheses := hyps, detail := claimLine :: detail }

/-! ## Diagnostics from prover reports

Not a verification: a report's `verified` field and words are the prover's output. -/

def reportNats (j : Lean.Json) (key : String) : Except String (List Int) := do
  let arr ← (← j.getObjVal? key).getArr?
  arr.toList.mapM fun v => do pure (decodeField (← v.getNat?))

end IxAIVerify
