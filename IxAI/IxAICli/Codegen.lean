import IxAIVerify.Package
import IxAICommon.Literal

/-!
# Claim and certificate sources for Ix

`ixai claims`, `chain`, `certified`, `forge` and `weights`: Lean files over `IxAICore` whose
definitions and theorems Ix certifies, with every output computed natively and written as a kernel
normal form (`IxAI.NormalForm`). The files are compiled in `ix/bundle`.
-/

namespace IxAICli

open IxAI IxAIVerify

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

/-- Safety theorems instantiated at the deployed model and gate, so their Check claims are bound to
the model's content address: the claim templates without outputs (`IxAIVerify.claimTemplates`). -/
def deployedTheorems : String :=
  String.join ((claimTemplates.filter (·.outputs.isEmpty)).map (·.theoremSource))

/-- Write `Claims.lean`: each Eval input next to its normal-form output, computed natively. -/
def writeClaims (dir : System.FilePath) (size : String) : IO UInt32 := do
  let some c := (triageConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let ns := s!"IxAIClaims.{size}"
  let open_ := s!"import IxAICore\nopen IxAICore Triage\n\nnamespace {ns}\n\n"
  let m := IxAICore.train IxAICore.Triage.spec c
  let cd := IxAICore.card IxAICore.Triage.spec c m
  let receipts := (receiptFormulas.zip (List.range receiptFormulas.length)).map fun (f, i) =>
    s!"def decisionInput{i} : Triage.Action := Triage.act ⟨{gateThreshold}⟩ trainedOutput {formulaSource f}\n" ++
      literalDef s!"decisionOutput{i}" (IxAICore.Triage.act ⟨gateThreshold⟩ m f) ++ "\n"
  let body := s!"def config : Config := {configSource c}\n\n" ++
    "def trainedInput : Model := train Triage.spec config\n\n" ++
    literalDef "trainedOutput" m ++ "\n" ++
    "def cardInput : Card := card Triage.spec config trainedOutput\n\n" ++
    literalDef "cardOutput" cd ++ "\n" ++ String.join receipts ++ deployedTheorems ++ s!"end {ns}\n"
  let file := dir / s!"Claims_{size}.lean"
  IO.FS.writeFile file (open_ ++ body)
  IO.println s!"wrote {file} ({size}): {m.w1.length} hidden units, {(m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).length} parameters"
  for q in cd.questions do
    IO.println s!"  {q.name}: {q.correct}/{q.total} correct, brier {q.brierRaw}, calibration error {q.calibrationRaw}"
  return 0

/-- Write `Chain_SIZE.lean`: the run as one Eval claim per training step, plus Eval claims for the
examples, schedule and initial weights, and the theorem that the chain equals `train`. -/
def writeChain (dir : System.FilePath) (size : String) : IO UInt32 := do
  let some c := (triageConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let s := IxAICore.Triage.spec
  let ns := s!"IxAIChain.{size}"
  let examples := (c.data s).map s.example
  let sched := c.schedule
  let w0 := c.init s
  let states := sched.foldl (fun (acc : Array IxAICore.Model) idx =>
    acc.push (c.stepFn s examples acc.back! idx)) #[w0]
  let header := s!"import IxAICore\nopen IxAICore Triage\n\nnamespace {ns}\n\n" ++
    s!"def config : Config := {configSource c}\n\n" ++
    "def examplesInput : List (List Fx × List Fx) := (config.data Triage.spec).map Triage.spec.example\n" ++
    literalDef "examplesOutput" examples ++ "\n" ++
    "def scheduleInput : List (List Nat) := config.schedule\n" ++
    literalDef "scheduleOutput" sched ++ "\n" ++
    "def initInput : Model := config.init Triage.spec\n" ++
    literalDef "w0" w0 ++ "\n"
  let steps := (sched.zip (List.range sched.length)).map fun (idx, i) =>
    s!"def stepInput{i} : Model := config.stepFn Triage.spec examplesOutput w{i} {NormalForm.render idx}\n" ++
      literalDef s!"w{i + 1}" states[i + 1]! ++ "\n"
  let links := "def links : List (Link Model (List Nat)) :=\n  [" ++
    ", ".intercalate ((sched.zip (List.range sched.length)).map fun (idx, i) =>
      s!"⟨w{i}, {NormalForm.render idx}, w{i + 1}⟩") ++ "]\n\n"
  let footer :=
    "def linksScheduleInput : List (List Nat) := links.map (·.input)\n\n" ++
    "/-- If the examples, schedule, initial-weight and step claims hold, the final weights are the\n" ++
    "specified training result. -/\n" ++
    "theorem trainedFromChain (hex : (config.data Triage.spec).map Triage.spec.example = examplesOutput)\n" ++
    "    (hsched : links.map (·.input) = config.schedule)\n" ++
    "    (hchain : ChainOK (config.stepFn Triage.spec examplesOutput) (config.init Triage.spec) links) :\n" ++
    "    chainEnd (config.init Triage.spec) links = train Triage.spec config :=\n" ++
    "  train_eq_of_chain _ _ _ _ hex hsched hchain\n\n" ++ s!"end {ns}\n"
  let file := dir / s!"Chain_{size}.lean"
  IO.FS.writeFile file (header ++ String.join steps ++ links ++ footer)
  IO.println s!"wrote {file}: {sched.length} steps, final weights equal train: {decide (states.back! = IxAICore.train s c)}"
  return 0

/-- Write `Certified_SIZE.lean`: the training result, evaluation card and gate decisions as
theorems the kernel checks by evaluation, next to the safety theorems. A CheckEnv claim over this
environment, aggregated and compressed, certifies all of them at once. -/
def writeCertified (dir : System.FilePath) (size : String) : IO UInt32 := do
  let some c := (triageConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let ns := s!"IxAICertified.{size}"
  let m := IxAICore.train IxAICore.Triage.spec c
  let cd := IxAICore.card IxAICore.Triage.spec c m
  let decisions := (receiptFormulas.zip (List.range receiptFormulas.length)).map fun (f, i) =>
    s!"theorem decision{i} : Triage.act ⟨{gateThreshold}⟩ trainedOutput {formulaSource f} = " ++
      s!"{NormalForm.render (IxAICore.Triage.act ⟨gateThreshold⟩ m f)} := by decide +kernel\n\n"
  let text := s!"import IxAICore\nopen IxAICore Triage\n\nnamespace {ns}\n\n" ++
    s!"def config : Config := {configSource c}\n\n" ++
    literalDef "trainedOutput" m ++ "\n" ++ literalDef "cardOutput" cd ++ "\n" ++
    "/-- The model is exactly the specified training result. -/\n" ++
    "theorem trainingCertified : train Triage.spec config = trainedOutput := by decide +kernel\n\n" ++
    "/-- The card is exactly the specified evaluation of the model. -/\n" ++
    "theorem cardCertified : card Triage.spec config trainedOutput = cardOutput := by decide +kernel\n\n" ++
    String.join decisions ++ deployedTheorems ++ s!"end {ns}\n"
  let file := dir / s!"Certified_{size}.lean"
  IO.FS.writeFile file text
  IO.println s!"wrote {file}"
  return 0

def joinRaw (xs : List IxAICore.Fx) : String := " ".intercalate (xs.map (toString ·.raw))

/-- Print a trained triage model's parameters in the format of `shell/triage.py`. -/
def writeWeights (size : String) : IO UInt32 := do
  let some c := (triageConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let m := IxAICore.train IxAICore.Triage.spec c
  IO.println s!"w1 {joinRaw m.w1.flatten}"
  IO.println s!"b1 {joinRaw m.b1}"
  IO.println s!"w2 {joinRaw m.w2.flatten}"
  IO.println s!"b2 {joinRaw m.b2}"
  return 0

/-- The triage spec with the `valid` labels inverted: what a reward hacker might train on. -/
def relabeledSpec : IxAICore.Spec IxAICore.Formula :=
  { IxAICore.Triage.spec with
    slots := [⟨"valid", 2, fun f => if f.valid then 0 else 1⟩, IxAICore.Triage.headQ.slot,
      IxAICore.Triage.coverageQ.slot] }

/-- Write `Forged_SIZE.lean`: claims a dishonest trainer might make, each of which Ix must refuse.
* `inflatedCard`: the honest model with its `valid` accuracy reported 5 points higher.
* `relabeledModel`: a model trained on inverted labels, claimed as the specified training result.
* `overtrainedModel`: a model trained one epoch longer than its config, claimed under that config. -/
structure ForgedClaims where
  inflated : IxAICore.Card
  relabeled : IxAICore.Model
  overtrained : IxAICore.Model

def forgedClaims (c : IxAICore.Config) (cd : IxAICore.Card) : ForgedClaims :=
  { inflated := ⟨cd.questions.map fun q => if q.name == "valid" then { q with correct := q.correct + 5 } else q⟩
    relabeled := IxAICore.train relabeledSpec c
    overtrained := IxAICore.train IxAICore.Triage.spec { c with epochs := c.epochs + 1 } }

def writeForged (dir : System.FilePath) (size : String) : IO UInt32 := do
  let some c := (triageConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let ns := s!"IxAIForged.{size}"
  let s := IxAICore.Triage.spec
  let m := IxAICore.train s c
  let cd := IxAICore.card s c m
  let ⟨inflated, relabeled, overtrained⟩ := forgedClaims c cd
  let text := s!"import IxAICore\nopen IxAICore Triage\n\nnamespace {ns}\n\n" ++
    s!"def config : Config := {configSource c}\n\n" ++
    literalDef "honestModel" m ++ "\n" ++
    "def cardInput : Card := card Triage.spec config honestModel\n" ++
    literalDef "inflatedCard" inflated ++ "\n" ++
    "def trainedInput : Model := train Triage.spec config\n" ++
    literalDef "relabeledModel" relabeled ++ "\n" ++
    literalDef "overtrainedModel" overtrained ++ "\n" ++ s!"end {ns}\n"
  let file := dir / s!"Forged_{size}.lean"
  IO.FS.writeFile file text
  IO.println s!"wrote {file}"
  return 0

/-- Write `Certified_SIZE.lean` for a long run, in chunks of `k` steps. Each chunk theorem says
that `k` steps from one checkpoint reach the next; `trainingCertified` then follows by rewriting
with the chunk theorems rather than by evaluating the run again. The chunk theorems are separate
constants, so a CheckEnv proof shards them across claims. -/
def writeCertifiedChunked (dir : System.FilePath) (size : String) (k : Nat) : IO UInt32 := do
  let some c := (triageConfigs.find? (·.1 == size)).map (·.2)
    | IO.println s!"unknown size {size}"; return 2
  let s := IxAICore.Triage.spec
  let ns := s!"IxAICertified.{size}"
  let examples := (c.data s).map s.example
  let sched := c.schedule
  let chunks := IxAICore.chunk k sched sched.length
  let ckpts := chunks.foldl (fun (acc : Array IxAICore.Model) ch =>
    acc.push (ch.foldl (c.stepFn s examples) acc.back!)) #[c.init s]
  let last := ckpts.back!
  let n := chunks.length
  let cd := IxAICore.card s c last
  let idx := List.range n
  let chunkDefs := String.join (idx.map fun j => literalDef s!"schedule{j}" chunks[j]! ++ "\n")
  -- One epoch per chunk when a chunk is exactly an epoch's batches: the schedule is then
  -- certified one shuffle at a time.
  -- Each epoch's batches must be a whole number of chunks for the schedule to be certified one
  -- epoch at a time: epoch `e` covers chunks `e*m … e*m + m - 1`.
  let batchesPerEpoch := c.trainSize / c.batch
  let m := batchesPerEpoch / k
  let perEpoch := c.batch * batchesPerEpoch == c.trainSize && m * k == batchesPerEpoch && m * c.epochs == n
  let epochChunks := fun (e : Nat) => " ++ ".intercalate ((List.range m).map fun i => s!"schedule{e * m + i}")
  let epochs := (List.range c.epochs).foldl (fun (acc : Array (Nat × List Nat)) _ =>
    let (r, _) := acc.back!
    let (perm, r') := IxAICore.shuffle (List.range c.trainSize) ⟨r⟩
    (acc.set! (acc.size - 1) (r, perm)).push (r'.state, [])) #[((IxAICore.Rng.seeded (c.seed + 7)).state, [])]
  let epochDefs := if !perEpoch then "" else String.join ((List.range (c.epochs + 1)).map fun e =>
      s!"def r{e} : Rng := ⟨{epochs[e]!.1}⟩\n") ++ "\n" ++
    String.join ((List.range c.epochs).map fun e => literalDef s!"perm{e}" epochs[e]!.2 ++ "\n") ++
    "theorem seedEq : Rng.seeded (config.seed + 7) = r0 := by decide +kernel\n\n" ++
    String.join ((List.range c.epochs).map fun e =>
      s!"theorem epoch{e} : shuffle (List.range config.trainSize) r{e} = (perm{e}, r{e + 1}) := by decide +kernel\n" ++
      s!"theorem batches{e} : chunk config.batch perm{e} config.trainSize = {epochChunks e} := by decide +kernel\n\n") ++
    "/-- The schedule, composed epoch by epoch from its parts given as hypotheses. -/\n" ++
    "theorem fromEpochs (hs : Rng.seeded (config.seed + 7) = r0)\n" ++
    String.join ((List.range c.epochs).map fun e =>
      s!"    (e{e} : shuffle (List.range config.trainSize) r{e} = (perm{e}, r{e + 1}))\n" ++
      s!"    (c{e} : chunk config.batch perm{e} config.trainSize = {epochChunks e})\n") ++
    s!"    : config.schedule = {" ++ ".intercalate (idx.map (s!"schedule{·}"))} := by\n" ++
    s!"  have he : config.epochs = {c.epochs} := rfl\n" ++
    String.join ((List.range c.epochs).map fun e =>
      s!"  have g{e} : Config.schedule.go config {c.epochs - e} r{e} = ({epochChunks e}) ++ Config.schedule.go config {c.epochs - e - 1} r{e + 1} := by\n" ++
      s!"    rw [schedule_go_succ config {c.epochs - e - 1} r{e}, e{e}]\n    simp only [c{e}]\n") ++
    "  rw [schedule_eq_go, he, hs, " ++ ", ".intercalate ((List.range c.epochs).map (s!"g{·}")) ++
    ", schedule_go_zero, List.append_nil]\n" ++
    "  simp only [List.append_assoc]\n\n"
  let ckptDefs := String.join ((List.range (n + 1)).map fun j => literalDef s!"w{j}" ckpts[j]! ++ "\n")
  let chunkThms := String.join (idx.map fun j =>
    s!"theorem chunk{j} : schedule{j}.foldl (config.stepFn Triage.spec examplesOutput) w{j} = w{j + 1} := by\n" ++
    "  decide +kernel\n\n")
  let scheduleSplit := " ++ ".intercalate (idx.map (s!"schedule{·}"))
  let rewrites := " ".intercalate (idx.map (s!"chunk{·}"))
  let hyps := ", ".intercalate (idx.map (s!"h{·}"))
  let decisions := (receiptFormulas.zip (List.range receiptFormulas.length)).map fun (f, i) =>
    s!"theorem decision{i} : Triage.act ⟨{gateThreshold}⟩ trainedOutput {formulaSource f} = " ++
      s!"{NormalForm.render (IxAICore.Triage.act ⟨gateThreshold⟩ last f)} := by decide +kernel\n\n"
  let text := s!"import IxAICore\nopen IxAICore Triage\n\n" ++
    "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n" ++
    s!"namespace {ns}\n\n" ++
    s!"def config : Config := {configSource c}\n\n" ++
    literalDef "examplesOutput" examples ++ "\n" ++ chunkDefs ++ ckptDefs ++
    "theorem examplesEq : (config.data Triage.spec).map Triage.spec.example = examplesOutput := by\n  decide +kernel\n\n" ++
    (if perEpoch then epochDefs ++
      s!"theorem scheduleEq : config.schedule = {scheduleSplit} :=\n  fromEpochs seedEq " ++
      " ".intercalate ((List.range c.epochs).flatMap fun e => [s!"epoch{e}", s!"batches{e}"]) ++ "\n\n"
     else s!"theorem scheduleEq : config.schedule = {scheduleSplit} := by\n  decide +kernel\n\n") ++
    "theorem initEq : config.init Triage.spec = w0 := by\n  decide +kernel\n\n" ++ chunkThms ++
    "/-- The run, composed from its parts. The parts are hypotheses, so checking this proof never\n" ++
    "evaluates the run: it only rewrites. -/\n" ++
    "theorem fromChunks\n" ++
    "    (hex : (config.data Triage.spec).map Triage.spec.example = examplesOutput)\n" ++
    s!"    (hs : config.schedule = {scheduleSplit})\n" ++
    "    (hi : config.init Triage.spec = w0)\n" ++
    String.join (idx.map fun j =>
      s!"    (h{j} : schedule{j}.foldl (config.stepFn Triage.spec examplesOutput) w{j} = w{j + 1})\n") ++
    s!"    : train Triage.spec config = w{n} := by\n" ++
    "  show config.schedule.foldl (config.stepFn Triage.spec ((config.data Triage.spec).map Triage.spec.example))\n" ++
    "    (config.init Triage.spec) = _\n" ++
    "  rw [hex, hs, hi]\n  simp only [List.foldl_append]\n" ++
    s!"  rw [{hyps}]\n\n" ++
    s!"/-- The model is exactly the specified training result. Checking it only matches the parts'\n" ++
    s!"statements against `fromChunks`'s hypotheses. -/\n" ++
    s!"theorem trainingCertified : train Triage.spec config = w{n} :=\n" ++
    s!"  fromChunks examplesEq scheduleEq initEq {rewrites}\n\n" ++
    s!"def trainedOutput : Model := w{n}\n\n" ++ literalDef "cardOutput" cd ++ "\n" ++
    "/-- The card is exactly the specified evaluation of the model. -/\n" ++
    "theorem cardCertified : card Triage.spec config trainedOutput = cardOutput := by decide +kernel\n\n" ++
    String.join decisions ++ deployedTheorems ++ s!"end {ns}\n"
  let file := dir / s!"Certified_{size}.lean"
  IO.FS.writeFile file text
  IO.println s!"wrote {file}: {sched.length} steps in {n} chunks of {k}"
  for q in cd.questions do
    IO.println s!"  {q.name}: {q.correct}/{q.total} correct, brier {q.brierRaw}, calibration error {q.calibrationRaw}"
  return 0

end IxAICli
