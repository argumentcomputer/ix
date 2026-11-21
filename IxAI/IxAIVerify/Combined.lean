import IxAIVerify.Package

/-!
# One certificate for training and its environment

A combined certificate is one terminal PLONK proof of Ix's compression pipeline over the root of
an `ix_aggr` join (shape 18, `ChildKind.aiur`): one `AiurRun` claim that joins IxVM's `CheckEnv`
claim of an environment holding the refinement theorem and its binding with the `aiurExec` root of
a training run (`Fixed::train_block` executions, `blockSteps` scheduled steps each).

`verifyCombined` accepts it when all of the following hold, in this order:

1. `aiur_join_check` (fork `ix-cert`) accepts the joined root: it recompiles the IxVM and `ix_aggr`
   keys from the pinned artifacts (`ixvmPin`, `joinAggregatorPin`), rebuilds the environment's
   `CheckEnv` claim from the environment and its partition, finds the theorem and binding in it,
   recompiles the run aggregator's and the program's keys from the approved packages, and checks
   the run's endpoints and data against arguments and an expected model that are written here from
   the specification and the submitted model. Nothing the trainer computed about the run is read.
2. The addresses of `IxAICore.train` and `IxAICore.Triage.spec` that the theorem's statement
   references are the job's, and that of `IxAIAiur.fullConfig` is the address of the config in the
   consumer's own compilation of the job's templates.
3. The run's 104-byte output claim (`out.bin`) is the one computed here
   (`Compression.execOutput` over `config.init`, the submitted model, and the data root of the
   schedule's batches and the rate).
4. The PLONK certificate verifies under the job's pinned key against the statement computed here,
   `Compression.terminalStatement` of the job's wrapper key, the BLAKE3 of the root key and the
   root claim: the very bytes `aiur_join_check` was given and accepted.

The trainer's files are copied into the work directory before any check reads them, so every
check and the statement read the same bytes. The environment and its partition are read by
`aiur_join_check` only.
-/

namespace IxAIVerify.Combined

open IxAI IxAICore IxAIVerify Lean

/-- BLAKE3 of the IxVM circuit artifact whose key the environment's `CheckEnv` claim names. -/
def ixvmPin : String := "0cbcb6812057cbb047da1a290a6ff6c72b1582e56596cab337c927a39f24fcd7"

/-- BLAKE3 of the `ix_aggr` artifact with the join shapes 17 and 18: the root key. -/
def joinAggregatorPin : String := "80d584ab24439dd23ad642a57009210ba3d407f4c20a4755c600d043fcaefa2e"

def defaultTheorem : String := "IxAICombined.train_of_deployed_blocks_enc"
def defaultBinding : String := "IxAICombined.blockRun"

/-- Scheduled steps per `Fixed::train_block` execution. -/
def defaultBlockSteps : Nat := 20

/-- The two circuits the consumer approves, each by the BLAKE3 of its artifact, and the artifacts'
files. The digests default to `ixvmPin` and `joinAggregatorPin`; a certificate made under other
circuits is checked by naming their digests, which is the consumer's approval of them. The files
are `IXAI_IXVM_ARTIFACT` and `IXAI_JOIN_AGGREGATOR`, by default `ix/artifacts/ixvm-DIGEST.ixa` and
`ix/artifacts/aggregate-DIGEST.ixa` of this project: found by digest, never through the `cert`
profile of `ix/ixw`, whose digests may move on. -/
structure Artifacts where
  ixvm : System.FilePath
  joinAggregator : System.FilePath
  ixvmDigest : String := ixvmPin
  joinAggregatorDigest : String := joinAggregatorPin

def Artifacts.fromEnv (ixvmDigest : String := ixvmPin)
    (joinAggregatorDigest : String := joinAggregatorPin) : IO Artifacts := do
  let get := fun (var : String) (dflt : System.FilePath) => do
    return ((← IO.getEnv var).map System.FilePath.mk).getD dflt
  let dir := projectDir / "ix" / "artifacts"
  return { ixvm := ← get "IXAI_IXVM_ARTIFACT" (dir / s!"ixvm-{ixvmDigest}.ixa")
           joinAggregator := ← get "IXAI_JOIN_AGGREGATOR" (dir / s!"aggregate-{joinAggregatorDigest}.ixa")
           ixvmDigest, joinAggregatorDigest }

/-- How the two circuit digests were approved, for the hypothesis that names them. -/
def Artifacts.approval (arts : Artifacts) : String :=
  if arts.ixvmDigest == ixvmPin && arts.joinAggregatorDigest == joinAggregatorPin then
    "pinned by BLAKE3 here"
  else "given by BLAKE3 on the command line"

/-- What the consumer brings: the approved run aggregator and program (by BLAKE3), its own
compilation of the job's templates, and the names of the theorem and binding the environment must
hold. -/
structure Approved where
  runAggregator : System.FilePath
  runAggregatorDigest : Digest
  program : System.FilePath
  programDigest : Digest
  templateEnv : System.FilePath
  theoremName : String := defaultTheorem
  binding : String := defaultBinding
  blockSteps : Nat := defaultBlockSteps

/-- The trainer's files. -/
structure Evidence where
  /-- The joined root: `root-vk.bin`, `root-claims.bin`, `ix-claim.bin`. -/
  root : System.FilePath
  plonk : System.FilePath
  plonkKey : System.FilePath
  env : System.FilePath
  partition : System.FilePath
  /-- The training run's root: `root-claims.bin`, `allowed.bin`, `out.bin`. -/
  runRoot : System.FilePath

def rootFiles : List String := ["root-vk.bin", "root-claims.bin", "ix-claim.bin"]
def runRootFiles : List String := ["root-claims.bin", "allowed.bin", "out.bin"]

/-! ## What `aiur_join_check` prints -/

/-- `aiur_join_check`'s verdict: its `ok:` lines, its `PROVED` line, the hypotheses it lists, an
`assumed:` line when the theorem is an axiom of the environment, and the addresses of the constants
the theorem's statement references. -/
structure JoinVerdict where
  oks : List String
  proved : String
  hypotheses : List String
  assumed : Option String
  references : List (String × Digest)
  deriving Repr

def dropPrefix (p s : String) : Option String :=
  if s.startsWith p then some (String.ofList (s.toList.drop p.length)) else none

/-- `ok: the theorem's statement references NAME (HEX)`. -/
def parseReference (l : String) : Option (String × Digest) := do
  let rest ← dropPrefix "ok: the theorem's statement references " l
  match words rest with
  | [name, paren] =>
    let h ← dropPrefix "(" paren
    guard (h.endsWith ")")
    pure (name, ← Digest.ofHex? (String.ofList (h.toList.dropLast)))
  | _ => none

/-- The verdict of an accepting run, or `none` without both a `PROVED` and a `hypotheses:` line. -/
def parseJoinVerdict (out : String) : Option JoinVerdict := do
  let ls := (out.splitOn "\n").map fun l => l.trimAscii.toString
  let proved ← ls.find? (·.startsWith "PROVED ")
  let hyps ← ls.findSome? (dropPrefix "hypotheses: ")
  let hyps := (hyps.splitOn "; ").map fun h => if h.endsWith "." then String.ofList h.toList.dropLast else h
  pure { oks := ls.filter (·.startsWith "ok: "), proved, hypotheses := hyps.filter (· != "")
         assumed := ls.find? (·.startsWith "assumed: "), references := ls.filterMap parseReference }

/-- The run's expected 104-byte output claim from `m0` over `batches`, and its execution count. -/
def expectedOutput (c : Config) (steps : Nat) (m0 : List Int) (batches : List (List Int × List Int))
    (final : List Int) : Except String (Nat × ByteArray) := do
  let (count, data) ← Compression.execData (.blocks steps) c.lrRaw batches
  return (count, Compression.execOutput count m0 final data)

/-- The one 18-word claim of a root's `root-claims.bin`. -/
def rootClaimOf (bytes : ByteArray) : Option (List Nat) :=
  match Compression.decodeClaims bytes with
  | some [c] => if c.length == 18 then some c else none
  | _ => none

/-! ## The check -/

def combinedHypotheses (tools : Tools) (checker verifier : String) (pin : Compression.Pin)
    (arts : Artifacts) (ap : Approved) (join : List String) : List String :=
  [baseHypotheses.headD "",
   s!"the run aggregator (BLAKE3 {ap.runAggregatorDigest.short}…) and the `Fixed::train_block` program (BLAKE3 {ap.programDigest.short}…) are the compilation of the programs the consumer approved; their digests are given on the command line, not named by the job",
   s!"the IxVM artifact ({short arts.ixvmDigest}…) and the `ix_aggr` artifact with the join shapes ({short arts.joinAggregatorDigest}…) are the circuits the consumer approved: {arts.approval}, recompiled to keys by `aiur_join_check`",
   s!"`aiur_join_check` (BLAKE3 {checker}, {tools.aiurJoinCheck}) recompiles those keys, rebuilds the environment's CheckEnv claim from the environment and its partition, and reads the joined claim, the run's claims and the environment's records as Ix and the circuits do; it does not verify the root's proof, which the certificate binds",
   s!"`{ap.theoremName}` states the refinement its name says: its statement is checked to reference `IxAICore.train` and `IxAICore.Triage.spec` at the job's addresses and `IxAIAiur.fullConfig` at the address of the consumer's compiled config, and `{ap.binding}` to name the program key and the theorem; the statement itself is not compared with an expected term",
   "IxVM soundness for the CheckEnv claim: the pinned IxVM kernel differs from the one Ix PR 678 proves in `try_nat_dispatch_prewhnf`"] ++
  join.map (s!"aiur_join_check: " ++ ·) ++
  terminalHypotheses tools verifier pin ++
  (stepHypotheses tools "").drop 3

/-- Copy `names` from `src` into `dst`; the names missing from `src`. -/
def copyFiles (src dst : System.FilePath) (names : List String) : IO (List String) := do
  IO.FS.createDirAll dst
  let mut missing := []
  for n in names do
    if ← (src / n).pathExists then IO.FS.writeBinFile (dst / n) (← IO.FS.readBinFile (src / n))
    else missing := missing ++ [(src / n).toString]
  return missing

def verifyCombined (tools : Tools) (cm : Commitment) (arts : Artifacts) (ap : Approved)
    (ev : Evidence) (final : List Int) (work : System.FilePath) : IO RouteResult := do
  let checker ← fileDigestStr tools.aiurJoinCheck
  let verifier ← fileDigestStr tools.plonkVerify
  let c := cm.config
  let kind := "combined"
  let some pin := cm.compression
    | return { kind, status := .incomplete, detail := ["the job pins no compression pipeline: the certificate cannot be checked against it"] }
  let base := combinedHypotheses tools checker verifier pin arts ap []
  let done : RouteStatus → List String → IO RouteResult := fun status detail =>
    pure { kind, status, detail, hypotheses := base }
  if let .error e := checkModelWords c.hidden final then return ← done .rejected [s!"the submitted model: {e}"]
  let m0 := rawOfModel (c.init Triage.spec)
  let batches := scheduledBatches c
  let (count, out) ← match expectedOutput c ap.blockSteps m0 batches final with
    | .ok x => pure x
    | .error e => return ← done .rejected [s!"the expected run: {e}"]
  -- The consumer's own files.
  for (path, pinHex, what) in [(arts.ixvm, arts.ixvmDigest, "IxVM artifact"), (arts.joinAggregator, arts.joinAggregatorDigest, "ix_aggr artifact")] do
    match ← fileDigest? path with
    | none => return ← done .incomplete [s!"the pinned {what} {path} is missing"]
    | some d => if d.hex != pinHex then return ← done .incomplete [s!"the {what} {path} has BLAKE3 {d}, not the pinned {pinHex}"]
  match ← fileDigest? ap.templateEnv with
  | none => return ← done .incomplete [s!"the template environment {ap.templateEnv} is missing"]
  | some d => if d.hex != cm.templateEnv then
      return ← done .incomplete [s!"{ap.templateEnv} has BLAKE3 {d}, not the job's template environment {cm.templateEnv}"]
  let configName := s!"{templateNamespace cm.configName}.config"
  let some configAddr := (← addrOf tools ap.templateEnv configName).bind Digest.ofHex?
    | return ← done .incomplete [s!"cannot read the address of {configName} from {ap.templateEnv} with {tools.ixw}"]
  -- The approved packages, checked and copied.
  unless ← ap.runAggregator.pathExists do
    return ← done .incomplete [s!"run aggregator {ap.runAggregator} is missing"]
  let aggrBytes ← IO.FS.readBinFile ap.runAggregator
  if blake3 aggrBytes != ap.runAggregatorDigest then
    return ← done .rejected [s!"run aggregator {ap.runAggregator} is not the approved {ap.runAggregatorDigest}"]
  IO.FS.createDirAll work
  let runAggr := work / s!"run-aggregator-{ap.runAggregatorDigest.short}.ixa"
  IO.FS.writeBinFile runAggr aggrBytes
  let program ← match ← approvedProgram ap.program ap.programDigest work with
    | .ok p => pure p
    | .error e => return ← done (if ← ap.program.pathExists then .rejected else .incomplete) [e]
  -- The trainer's files, copied once.
  let root := work / "root"
  let runRoot := work / "run-root"
  let missing := (← copyFiles ev.root root rootFiles) ++ (← copyFiles ev.runRoot runRoot runRootFiles) ++
    (← [ev.env, ev.partition, ev.plonk].filterM fun p => do return !(← p.pathExists)).map (·.toString)
  -- The run's arguments and expected model, from the specification and the submitted model.
  let specArgs := m0 ++ [c.lrRaw] ++ (batches.map (·.1)).flatten ++ (batches.map (·.2)).flatten
  let argsFile := work / "spec-args.txt"
  let outFile := work / "expected-output.txt"
  IO.FS.writeFile argsFile (joinInts specArgs ++ "\n")
  IO.FS.writeFile outFile (joinInts final ++ "\n")
  let t0 ← IO.monoMsNow
  let r? ← run? tools.aiurJoinCheck #[arts.ixvm.toString, arts.ixvmDigest, arts.joinAggregator.toString, arts.joinAggregatorDigest,
      ev.env.toString, ev.partition.toString, root.toString, runAggr.toString, program.toString, runRoot.toString,
      argsFile.toString, outFile.toString, toString count, toString ap.blockSteps, ap.theoremName, ap.binding]
  let ms := (← IO.monoMsNow) - t0
  let some r := r? | return ← done .incomplete [s!"cannot run {tools.aiurJoinCheck}"]
  if notRun r then return ← done .incomplete [s!"{tools.aiurJoinCheck} did not start: {lastChars r.stderr 160}"]
  let all := r.stderr ++ r.stdout
  let rejectLine := (r.stdout.splitOn "\n" ++ r.stderr.splitOn "\n").find? (·.startsWith "REJECT")
  -- A REJECT is a contradiction whatever else is missing; any other failure with evidence
  -- missing is missing evidence, and one before the first `ok:` is a failure of the checker's own
  -- setup (its pinned artifacts).
  if let some l := rejectLine then
    return ← done .rejected [s!"aiur_join_check: {l}"]
  if r.exitCode != 0 then
    if !missing.isEmpty then return ← done .incomplete (missing.map (s!"missing: " ++ ·))
    unless (r.stdout.splitOn "\n").any (·.startsWith "ok:") do
      return ← done .incomplete [s!"{tools.aiurJoinCheck} did not reach the evidence: {lastChars all 200}"]
    return ← done .rejected [s!"aiur_join_check (exit {r.exitCode}): {lastChars all 300}"]
  let some v := parseJoinVerdict r.stdout
    | return ← done .rejected [s!"aiur_join_check exited 0 without a PROVED verdict: {lastChars all 300}"]
  let hyps := combinedHypotheses tools checker verifier pin arts ap v.hypotheses
  let done : RouteStatus → List String → IO RouteResult := fun status detail =>
    pure { kind, status, detail, hypotheses := hyps }
  let joinLines := s!"aiur_join_check accepted the joined root ({ms} ms, {v.oks.length} checks):" ::
    v.oks.map ("  " ++ ·) ++ [s!"  {v.proved}"]
  let modelHash := blake3 (Compression.encWords final)
  unless (v.proved.splitOn s!"the model with BLAKE3 {modelHash.hex}").length > 1 &&
      (v.proved.splitOn s!"contains {ap.theoremName} and {ap.binding}").length > 1 do
    return ← done .rejected (joinLines ++ [s!"its verdict is not about {ap.theoremName} and the submitted model (BLAKE3 {modelHash.hex})"])
  -- The constants the theorem states its conclusion with are the consumer's.
  let expectedRefs : List (String × Option Digest) :=
    [("IxAICore.train", Digest.ofHex? cm.trainAddress), ("IxAICore.Triage.spec", Digest.ofHex? cm.specAddress),
     ("IxAIAiur.fullConfig", some configAddr)]
  for (name, want) in expectedRefs do
    match v.references.lookup name with
    | none => return ← done .rejected (joinLines ++ [s!"aiur_join_check printed no address for {name}"])
    | some got =>
      if some got != want then
        return ← done .rejected (joinLines ++ [s!"the theorem's {name} is {got}, not the consumer's {(want.map (·.hex)).getD "?"}"])
  let refLine := s!"the theorem references the job's IxAICore.train ({short cm.trainAddress}…) and IxAICore.Triage.spec ({short cm.specAddress}…), and IxAIAiur.fullConfig is the consumer's {configName} ({configAddr.short}…)"
  if let some a := v.assumed then
    return ← done .incomplete (joinLines ++ [refLine, s!"the refinement theorem is an axiom of the environment, not proved in it: {a}"])
  -- The run's output claim, computed here.
  let runOut ← IO.FS.readBinFile (runRoot / "out.bin")
  if runOut.data != out.data then
    return ← done .rejected (joinLines ++ [refLine, s!"the run's output claim (out.bin, BLAKE3 {blake3 runOut}) is not the one computed here from config.init, the schedule's batches, the rate and the submitted model ({blake3 out})"])
  let outLine := s!"the run's output claim is the one computed here: {count} executions of {ap.blockSteps} steps from config.init to the submitted model over the schedule's batches and rate (BLAKE3 {(blake3 out).short}…)"
  -- The statement over the bytes `aiur_join_check` accepted.
  let rootKey := blake3 (← IO.FS.readBinFile (root / "root-vk.bin"))
  let some claim := rootClaimOf (← IO.FS.readBinFile (root / "root-claims.bin"))
    | return ← done .rejected (joinLines ++ [refLine, outLine, "root-claims.bin is not one canonical 18-word claim"])
  let statement := Compression.terminalStatement pin.wrapKey rootKey claim
  let (status, detail) ← verifyTerminal tools pin ev.plonkKey ev.plonk statement (work / "plonk")
  let stmtLine := s!"statement {statement.short}… computed from the joined root's key {rootKey.short}… (ix_aggr's, recompiled from the pinned artifact) and its AiurRun claim, through the job's wrapper key {pin.wrapKey.short}…"
  return ← done status (joinLines ++ [refLine, outLine, stmtLine] ++ detail)

/-- What a verified combined certificate proves. -/
def provedStatement (cm : Commitment) (ap : Approved) (final : List Int) : String :=
  s!"IxAICore.train IxAICore.Triage.spec (config {cm.configName}) is the submitted model (weights {(modelDigest (modelOfRaw cm.config.hidden final)).short}…): the environment that holds {ap.theoremName} and {ap.binding} is checked by IxVM, and the approved Fixed::train_block program ran the schedule from config.init to the submitted model, in one PLONK certificate"

end IxAIVerify.Combined
