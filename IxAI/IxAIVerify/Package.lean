import IxAIVerify.Aiur
import IxAICommon.Literal
import Lean.Data.Json

/-!
# The model package: job, model, receipt

A consumer issues a **job** (`ixai-job-commitment-v2`) before any training, and identifies it by
its BLAKE3, which it keeps independently of the trainer. The job is built from the specification and
a config alone. It names:

* the specification: `IxAICore.Triage.spec` and `IxAICore.train`, by Ixon address;
* the config, field by field and by `configDigest`;
* the dataset: its example count and length-binding root (`datasetRoot`, `merkleRootV2`);
* the approved Aiur programs (program packages, by BLAKE3) and the claim encoding
  (`claimEncodingDigest`);
* the claim policy: every evaluation and deployment claim is an Ix `Check` claim under one
  context (specification digest, role binding, no axioms beyond the standard three), with no
  assumptions, validating its binding;
* the canonical model encoding: the Ixon addresses of the constructors a model literal is built
  from (`ModelEncoding`), and of the gate's actions;
* the claim templates: each evaluation and deployment claim as a statement with holes for the
  trained model and its outputs (`Ixon.Term`, read from the consumer's compilation of
  `templateSource`);
* optionally, the compression pipeline (`Compression.Pin`): the BLAKE3 of the terminal PLONK
  verifying key and of the wrapper key its statement names. Without it an `aiur-exec` route is at
  best `attested`.

A trainer returns the **model** (331 raw words, `rawOfModel` order) and a **receipt**
(`ixai-receipt-v1`) listing evidence: training routes (`IxAIVerify.Aiur`), the compiled
environment, and an Ix proof per claim template. Routes are tagged by `kind`; kinds this verifier
does not implement are reported and ignored.

`verifyPackage` never reads a `verified` field, a prover log, a report or a Lean source file, and
never runs SGD. A claim is accepted when its proof's `Check` claim is exactly the policy's claim
about a theorem of the environment, the theorem's type instantiates the claim's template, and
`ix verify` accepts the proof. The `trainedOutput` hole must be the same constant in every claim,
and that constant's value, read from its Ixon record, must be the submitted model: one model for
training, the evaluation card and the gate. Its outcome is one of:

* `proved`: a training route re-verified every proof here, and every claim verifies and is bound
  to the model;
* `predicted`: the claims verify, but no training route was fully re-verified: the model is
  checked only by its evaluation;
* `incomplete`: committed evidence is missing;
* `rejected`: some evidence contradicts the job.

Every hypothesis the outcome rests on is printed with it.
-/

namespace IxAIVerify

open IxAI IxAICore Lean

inductive Outcome where
  | proved
  | predicted
  | incomplete
  | rejected
  deriving Repr, BEq

def Outcome.label : Outcome → String
  | .proved => "PROVED"
  | .predicted => "PREDICTED (checked only by evaluation)"
  | .incomplete => "INCOMPLETE"
  | .rejected => "REJECTED"

def Outcome.exitCode : Outcome → UInt32
  | .proved => 0
  | .rejected => 1
  | .predicted => 3
  | .incomplete => 4


def commitmentFormat : String := "ixai-job-commitment-v2"
def receiptFormat : String := "ixai-receipt-v1"

/-! ## Claim templates -/

def gateThreshold : Int := 200

/-- Formulas the gate is asked about in the certified decision claims. -/
def receiptFormulas : List Formula :=
  let p := Formula.atom
  [.imp (p 0) (p 0), .imp (.and (p 0) (p 1)) (p 1), .imp (p 0) (p 1), .and (p 2) .top]

/-- An evaluation or deployment claim about the trained model `trainedOutput`, as Lean source. The
theorem a trainer proves states `statement` (after `binders`) with `trainedOutput` its model and
each output hole replaced by the value it computed; the template is the `Prop`-valued definition
`fun trainedOutput outputs… => ∀ binders, statement`. -/
structure ClaimTemplate where
  id : String
  role : String
  /-- Holes after `trainedOutput`, as `(name, type)`. -/
  outputs : List (String × String) := []
  /-- Binders before the theorem's colon. -/
  binders : String := ""
  statement : String
  doc : String := ""
  /-- A proof term for every model, when the claim needs no evaluation. -/
  proof : String := ""

def claimTemplates : List ClaimTemplate :=
  let g := gateThreshold
  [{ id := "cardCertified", role := "evaluation", outputs := [("cardOutput", "IxAICore.Card")]
     statement := "card Triage.spec config trainedOutput = cardOutput" }] ++
  (receiptFormulas.zipIdx.map fun (f, i) =>
    { id := s!"decision{i}", role := "deployment",
      outputs := [("decisionOutput", "IxAICore.Triage.Action")]
      statement := s!"Triage.act ⟨{g}⟩ trainedOutput {formulaSource f} = decisionOutput" }) ++
  [{ id := "deployedPublishSound", role := "deployment"
     binders := s!"(f : Formula) (h : Triage.act ⟨{g}⟩ trainedOutput f = .publish)"
     statement := "f.valid = true"
     doc := "The deployed system never publishes a false formula."
     proof := "Triage.act_publish_sound _ _ f h" },
   { id := "deployedPublishConfident", role := "deployment"
     binders := s!"(f : Formula) (h : Triage.act ⟨{g}⟩ trainedOutput f = .publish)"
     statement := s!"Triage.confidence trainedOutput f ≥ {g}"
     doc := "The deployed system publishes only formulas its model is confident about."
     proof := "Triage.act_publish_confident _ _ f h" },
   { id := "deployedDeferIff", role := "deployment"
     binders := "(f : Formula)"
     statement := s!"Triage.act ⟨{g}⟩ trainedOutput f = .defer ↔ Triage.confidence trainedOutput f < {g}"
     doc := "The deployed system defers exactly when its model is not confident."
     proof := "Triage.act_defer_iff _ _ f" }]

/-- The theorem a trainer proves for a template without outputs. -/
def ClaimTemplate.theoremSource (t : ClaimTemplate) : String :=
  s!"/-- {t.doc} -/\ntheorem {t.id} {t.binders} :\n    {t.statement} :=\n  {t.proof}\n\n"

/-- The template as a `Prop`-valued definition over its holes. -/
def ClaimTemplate.templateSource (t : ClaimTemplate) : String :=
  let holes := " ".intercalate (("(trainedOutput : Model)" :: t.outputs.map fun (n, ty) => s!"({n} : {ty})"))
  let body := if t.binders.isEmpty then t.statement else s!"∀ {t.binders}, {t.statement}"
  s!"def {t.id} {holes} : Prop :=\n  {body}\n\n"

def ClaimTemplate.holes (t : ClaimTemplate) : List String := "trainedOutput" :: t.outputs.map (·.1)

def templateNamespace (size : String) : String := s!"IxAITemplate.{size}"

/-- A model with words of both signs, written as the trainer writes its model, so the compiled
template carries every constructor of the model encoding. -/
def encodingSample : Model :=
  { w1 := [[⟨0⟩]], b1 := [⟨-1⟩], w2 := [], b2 := [] }

/-- The Lean source a consumer compiles, before training, to fix what its claims mean. -/
def templateSource (size : String) (c : Config) : String :=
  s!"import IxAICore\nopen IxAICore Triage\n\nnamespace {templateNamespace size}\n\n" ++
    s!"def config : Config := {configSource c}\n\n" ++
    "/-- The training the job asks for; it puts `IxAICore.train` in the environment. -/\n" ++
    "def training : Model := train Triage.spec config\n\n" ++
    "/-- Kernel roles a trained environment's closure binds, named so that the template's role\n" ++
    "binding, which the job's claim policy pins, is the one a trainer's environment carries. -/\n" ++
    "def roleAnchors := (@String.decEq, @String.toByteArray, @Int.decEq)\n\n" ++
    literalDef "modelEncoding" encodingSample ++ "\n" ++
    "def actionEncoding : List IxAICore.Triage.Action :=\n" ++
    "  [IxAICore.Triage.Action.publish, IxAICore.Triage.Action.refuted, IxAICore.Triage.Action.defer]\n\n" ++
    String.join (claimTemplates.map (·.templateSource)) ++ s!"end {templateNamespace size}\n"

/-! ## The job -/

/-- The constructors a model literal is built from, by Ixon address. -/
structure ModelEncoding where
  modelMk : Digest
  listCons : Digest
  listNil : Digest
  fxMk : Digest
  intOfNat : Digest
  intNegSucc : Digest

def modelEncodingNames : List (String × String) :=
  [("Model.mk", "IxAICore.Model.mk"), ("List.cons", "List.cons"), ("List.nil", "List.nil"),
   ("Fx.mk", "IxAICore.Fx.mk"), ("Int.ofNat", "Int.ofNat"), ("Int.negSucc", "Int.negSucc")]

def actionNames : List (String × Triage.Action) :=
  [("IxAICore.Triage.Action.publish", .publish), ("IxAICore.Triage.Action.refuted", .refuted),
   ("IxAICore.Triage.Action.defer", .defer)]

/-- The Ix claim every evaluation and deployment claim must be: `Check` of the claim's theorem
under this context, without assumptions, validating its role binding. -/
structure ClaimPolicy where
  spec : Digest
  binding : Digest

def ClaimPolicy.expected (p : ClaimPolicy) (const : Digest) : Ixon.CheckClaim :=
  { spec := p.spec, binding := p.binding, axioms := none, const, assumptions := none,
    bindingAssumed := false }

structure CommittedClaim where
  id : String
  role : String
  holes : List String
  statement : Ixon.Term

structure Commitment where
  specName : String
  specAddress : String
  trainAddress : String
  configName : String
  config : Config
  configDigest : String
  datasetCount : Nat
  datasetRoot : String
  programs : List (String × String)
  claimEncoding : String
  policy : ClaimPolicy
  encoding : ModelEncoding
  actions : List (Triage.Action × Digest)
  templateSource : String
  templateEnv : String
  claims : List CommittedClaim
  compression : Option Compression.Pin := none

/-- The programs a commitment can approve. -/
def programNames : List String := ["Fixed::step", "Fixed::train", "AiurExec::aiur_exec"]

def jStr (j : Json) (path : List String) : Except String String :=
  match path with
  | [] => j.getStr?
  | k :: ks => do jStr (← j.getObjVal? k) ks

def jNat (j : Json) (path : List String) : Except String Nat :=
  match path with
  | [] => j.getNat?
  | k :: ks => do jNat (← j.getObjVal? k) ks

def jInt (j : Json) (path : List String) : Except String Int :=
  match path with
  | [] => j.getInt?
  | k :: ks => do jInt (← j.getObjVal? k) ks

def jDigest (j : Json) (path : List String) : Except String Digest := do
  let s ← jStr j path
  match Digest.ofHex? s with
  | some d => pure d
  | none => throw s!"{".".intercalate path}: not a digest: {s}"

def Commitment.parse (j : Json) : Except String Commitment := do
  let fmt ← jStr j ["format"]
  unless fmt == commitmentFormat do throw s!"commitment format {fmt}, expected {commitmentFormat}"
  let config : Config :=
    { seed := ← jNat j ["config", "seed"], hidden := ← jNat j ["config", "hidden"]
      lrRaw := ← jInt j ["config", "lrRaw"], epochs := ← jNat j ["config", "epochs"]
      batch := ← jNat j ["config", "batch"], trainSize := ← jNat j ["config", "trainSize"]
      testSize := ← jNat j ["config", "testSize"] }
  let progs := programNames.filterMap fun k =>
    ((j.getObjValD "programs").getObjValAs? String k).toOption.map (k, ·)
  let pol ← j.getObjVal? "claimPolicy"
  unless (jStr pol ["kind"]).toOption == some "Check" && pol.getObjValD "axioms" == Json.null &&
      pol.getObjValD "assumptions" == Json.null && pol.getObjValD "bindingAssumed" == Json.bool false do
    throw "claim policy: this verifier implements unconditional Check claims over the standard axioms, validating their binding"
  let enc := fun (k : String) => jDigest j ["modelEncoding", k]
  let encoding : ModelEncoding :=
    { modelMk := ← enc "Model.mk", listCons := ← enc "List.cons", listNil := ← enc "List.nil"
      fxMk := ← enc "Fx.mk", intOfNat := ← enc "Int.ofNat", intNegSucc := ← enc "Int.negSucc" }
  let actions ← actionNames.mapM fun (n, a) => do pure (a, ← jDigest j ["actions", n])
  let claims ← (← j.getObjVal? "claims").getArr?
  let compression ← match j.getObjVal? "compression" with
    | .error _ => pure none
    | .ok cj => do
      pure (some ({ plonkKey := ← jDigest cj ["plonkVerifyingKeyBlake3"], wrapKey := ← jDigest cj ["wrapKeyBlake3"] } : Compression.Pin))
  return {
    specName := ← jStr j ["spec", "name"], specAddress := ← jStr j ["spec", "address"]
    trainAddress := ← jStr j ["spec", "trainAddress"]
    configName := ← jStr j ["config", "name"], config, configDigest := ← jStr j ["config", "digest"]
    datasetCount := ← jNat j ["dataset", "count"], datasetRoot := ← jStr j ["dataset", "root"]
    programs := progs
    claimEncoding := ← jStr j ["claimEncoding"]
    policy := { spec := ← jDigest pol ["spec"], binding := ← jDigest pol ["binding"] }
    encoding, actions
    templateSource := ← jStr j ["templates", "sourceBlake3"]
    templateEnv := ← jStr j ["templates", "environmentBlake3"]
    claims := ← claims.toList.mapM fun c => do
      let holes ← (← c.getObjVal? "holes").getArr?
      pure ({ id := ← jStr c ["id"], role := ← jStr c ["role"]
              holes := ← holes.toList.mapM (·.getStr?)
              statement := ← Ixon.Term.ofJson (← c.getObjVal? "statement") } : CommittedClaim)
    compression }

def Commitment.toJson (c : Commitment) : Json :=
  Json.mkObj <| ([
    ("format", commitmentFormat),
    ("spec", Json.mkObj [("name", c.specName), ("address", c.specAddress), ("train", "IxAICore.train"),
      ("trainAddress", c.trainAddress)]),
    ("config", Json.mkObj [("name", c.configName), ("seed", c.config.seed), ("hidden", c.config.hidden),
      ("lrRaw", c.config.lrRaw), ("epochs", c.config.epochs), ("batch", c.config.batch),
      ("trainSize", c.config.trainSize), ("testSize", c.config.testSize), ("digest", c.configDigest)]),
    ("dataset", Json.mkObj [("kind", "(config.data Triage.spec).map Triage.spec.example, leaf = H(job/example, inputs, targets)"),
      ("count", c.datasetCount), ("rootFormat", "ixai/merkle2 (merkleRootV2)"), ("root", c.datasetRoot)]),
    ("programs", Json.mkObj (c.programs.map fun (k, v) => (k, Json.str v))),
    ("claimEncoding", c.claimEncoding),
    ("claimEncodingText", stepClaimEncoding),
    ("claimPolicy", Json.mkObj [("kind", "Check"), ("spec", c.policy.spec.hex), ("binding", c.policy.binding.hex),
      ("axioms", Json.null), ("assumptions", Json.null), ("bindingAssumed", false)]),
    ("modelEncoding", Json.mkObj ((modelEncodingNames.map (·.1)).zip
      [c.encoding.modelMk, c.encoding.listCons, c.encoding.listNil, c.encoding.fxMk, c.encoding.intOfNat,
       c.encoding.intNegSucc] |>.map fun (k, d) => (k, Json.str d.hex))),
    ("actions", Json.mkObj (actionNames.filterMap fun (n, a) =>
      (c.actions.find? (·.1 == a)).map fun (_, d) => (n, Json.str d.hex))),
    ("templates", Json.mkObj [("source", "templateSource (IxAIVerify/Package.lean)"),
      ("sourceBlake3", c.templateSource), ("environmentBlake3", c.templateEnv)]),
    ("claims", Json.arr (c.claims.map fun cl =>
      Json.mkObj [("id", cl.id), ("role", cl.role), ("holes", Json.arr (cl.holes.map Json.str).toArray),
        ("statement", cl.statement.toJson)]).toArray)] : List (String × Json)) ++
    (c.compression.map fun p => [("compression", Json.mkObj [
      ("kind", "Ix compression pipeline: terminal gnark PLONK over BN254 (Ignition SRS), statement compress_wrap/v1 of the root key and claim through the wrapper"),
      ("plonkVerifyingKeyBlake3", p.plonkKey.hex), ("wrapKeyBlake3", p.wrapKey.hex)])]).getD []

/-! ## Reading the model from the environment -/

def decodeInt (enc : ModelEncoding) (t : Ixon.Term) : Except String Int :=
  match t.spine with
  | (.ref a _, [.nat n]) =>
    if a == enc.intOfNat then pure n else if a == enc.intNegSucc then pure (-((n : Int) + 1))
    else throw "not an integer literal"
  | _ => throw "not an integer literal"

def decodeFx (enc : ModelEncoding) (t : Ixon.Term) : Except String IxAICore.Fx :=
  match t.spine with
  | (.ref a _, [i]) => if a == enc.fxMk then return ⟨← decodeInt enc i⟩ else throw "not a fixed-point literal"
  | _ => throw "not a fixed-point literal"

partial def decodeList {α : Type} (enc : ModelEncoding) (f : Ixon.Term → Except String α)
    (t : Ixon.Term) : Except String (List α) :=
  match t.spine with
  | (.ref a _, [_, h, tl]) =>
    if a == enc.listCons then return (← f h) :: (← decodeList enc f tl) else throw "not a list literal"
  | (.ref a _, [_]) => if a == enc.listNil then pure [] else throw "not a list literal"
  | _ => throw "not a list literal"

/-- The value of a model literal: `Model.mk w1 b1 w2 b2` of lists of `Fx.mk` of `Int.ofNat n` or
`Int.negSucc n`, through the committed constructors. Type and universe arguments are not read: the
claim's `Check` covers the literal's typing. -/
def decodeModel (enc : ModelEncoding) (t : Ixon.Term) : Except String Model :=
  match t.spine with
  | (.ref a _, [w1, b1, w2, b2]) => do
    unless a == enc.modelMk do throw "not a model literal"
    return { w1 := ← decodeList enc (decodeList enc (decodeFx enc)) w1, b1 := ← decodeList enc (decodeFx enc) b1
             w2 := ← decodeList enc (decodeList enc (decodeFx enc)) w2, b2 := ← decodeList enc (decodeFx enc) b2 }
  | _ => throw "not a model literal"

/-- The model a constant denotes: a safe, universe-monomorphic definition whose value is a model
literal, or another such constant. -/
partial def modelOfConstant (env : Ixon.Env) (enc : ModelEncoding) (a : Digest) (fuel : Nat := 8) :
    Except String Model := do
  if fuel == 0 then throw "too many definitions between the claim and the model literal"
  let d ← env.definition? a
  unless d.kind == 0 && d.safety == 1 && d.lvls == 0 do
    throw s!"{a.short}… is not a safe definition (kind {d.kind}, safety {d.safety})"
  match ← env.resolve d d.value with
  | .ref b [] => modelOfConstant env enc b (fuel - 1)
  | v => decodeModel enc v

/-! ## Reading proofs -/

/-- The Ixon address of `name` in the environment `env`, by `ixw addr-of`. Used only when building
a job, on the consumer's own template environment. -/
def addrOf (tools : Tools) (env : System.FilePath) (name : String) : IO (Option String) := do
  match ← run? tools.ixw #["addr-of", "--ixe", env.toString, name] with
  | some r =>
    let line := ((r.stdout.splitOn "\n").filter (·.length == 64)).getLast?
    return if r.exitCode == 0 then line else none
  | none => return none

/-- The path of a stored object in an Ix store. -/
def storePath (store : System.FilePath) (a : Digest) : System.FilePath :=
  let h := a.hex.toList
  let part := fun (i n : Nat) => String.ofList ((h.drop i).take n)
  store / part 0 2 / part 2 2 / part 4 2 / part 6 58

/-- Why a proof's claim is not the expected one, field by field. -/
def claimDifference (got want : Ixon.CheckClaim) : List String :=
  (if got.spec != want.spec then [s!"specification digest {got.spec}, the policy's is {want.spec}"] else []) ++
  (if got.binding != want.binding then [s!"role binding {got.binding}, the policy's is {want.binding}"] else []) ++
  (if got.axioms != want.axioms then [s!"axioms beyond the standard three ({(got.axioms.map (·.hex)).getD "none"})"] else []) ++
  (if got.assumptions != want.assumptions then [s!"conditional on assumptions {(got.assumptions.map (·.hex)).getD "none"}"] else []) ++
  (if got.bindingAssumed != want.bindingAssumed then ["assumes its role binding instead of validating it"] else []) ++
  (if got.const != want.const then [s!"names {got.const}, not {want.const}"] else [])

/-! ## Verification -/

structure Report where
  lines : Array String := #[]
  hypotheses : Array String := #[]
  rejected : Bool := false
  incomplete : Bool := false

def Report.say (r : Report) (s : String) : Report := { r with lines := r.lines.push s }
def Report.reject (r : Report) (s : String) : Report := { r with lines := r.lines.push s!"  REJECT: {s}", rejected := true }
def Report.missing (r : Report) (s : String) : Report := { r with lines := r.lines.push s!"  MISSING: {s}", incomplete := true }
def Report.assume (r : Report) (hs : List String) : Report :=
  { r with hypotheses := hs.foldl (fun acc h => if acc.contains h then acc else acc.push h) r.hypotheses }

def short (s : String) : String := String.ofList (s.toList.take 12)

def resolve (base : System.FilePath) (p : String) : System.FilePath :=
  if p.startsWith "/" then p else base / p

/-- A model file: one line of words. A missing file is missing evidence; a malformed one is
refused. -/
inductive ModelFile where
  | ok (words : List Int)
  | missing (why : String)
  | malformed (why : String)

def readModelFile (path : System.FilePath) : IO ModelFile := do
  unless ← path.pathExists do return .missing s!"model {path} is missing"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (·.trimAscii.toString != "")
  match lines with
  | [l] => match parseInts (words l) with
    | .ok ws => return .ok ws
    | .error e => return .malformed s!"model {path}: {e}"
  | _ => return .malformed s!"model {path} has {lines.length} lines, not one"

def implementedKinds : List String := ["aiur-steps", "aiur-train", "aiur-exec"]

/-- How a receipt's training routes combine: whether one contradicts the job, whether one was
verified in full, and whether all the implemented ones lack evidence. Unknown kinds are ignored;
a receipt with only unknown kinds has no implemented route, so it is neither proved nor missing
evidence. -/
structure TrainingVerdict where
  rejected : Bool
  proved : Bool
  incomplete : Bool
  deriving BEq, Repr

def trainingVerdict (results : List RouteResult) : TrainingVerdict :=
  let implemented := results.filter (implementedKinds.contains ·.kind)
  let proved := implemented.any (·.status == .verified)
  { rejected := implemented.any (·.status == .rejected), proved
    incomplete := !proved && !implemented.isEmpty && implemented.all (·.status == .incomplete) }

def outcomeOf (rejected incomplete trainingProved claimsOk : Bool) : Outcome :=
  if rejected then .rejected
  else if trainingProved && claimsOk then .proved
  else if claimsOk && !incomplete then .predicted
  else .incomplete

def baseHypotheses : List String :=
  ["the job commitment is the consumer's own (its BLAKE3 was received independently of the trainer)",
   "the approved program packages are the compilation of the Aiur programs the consumer approved (`Fixed::step`, `Fixed::train`, `AiurExec::aiur_exec`); their digests are taken as given"]

def claimHypotheses (tools : Tools) (ixw : String) (cm : Commitment) : List String :=
  [s!"IxVM STARK soundness: an accepting `ix verify` (via {tools.ixw}, BLAKE3 {ixw}) of a proof whose claim is the policy's `Check` claim implies Ix's kernel accepts the theorem, its dependencies included",
   s!"the claim templates mean what the consumer intends: they are the Ixon terms of the consumer's own compilation of `templateSource` (source {short cm.templateSource}…, environment {short cm.templateEnv}…), and the committed constructor addresses are those of `IxAICore.Model.mk`, `List.cons`, `List.nil`, `IxAICore.Fx.mk`, `Int.ofNat`, `Int.negSucc` and the gate's actions",
   "this verifier reads Ixon as Ix writes it (`IxAIVerify.Ixon`: records authenticated by BLAKE3; expressions decoded here, not by Ix)",
   "Ix's kernel: card and gate decisions are `decide +kernel` evaluations; the safety theorems are proved for every model (`Triage.act_publish_sound`, `act_publish_confident`, `act_defer_iff`)"]

/-- Find the receipt's proof for template `id`: an entry whose `claim` is `id`, or else whose
`name` ends in `.id`. -/
def receiptProof (proofs : List Json) (id : String) : Option String :=
  let byClaim := proofs.find? fun p => (jStr p ["claim"]).toOption == some id
  let byName := proofs.find? fun p => ((jStr p ["name"]).toOption.map fun n => n == id || n.endsWith s!".{id}") == some true
  (byClaim.orElse fun _ => byName).bind fun p => (jStr p ["proof"]).toOption

/-- A claim that passed every check short of running `ix verify`. -/
structure PendingClaim where
  claim : CommittedClaim
  proof : String
  expected : Ixon.CheckClaim

/-- Check the receipt's claims against the job's templates, read the model they are about from the
environment, and verify their proofs. Returns whether every claim verified. -/
def verifyClaims (tools : Tools) (cm : Commitment) (rj : Json) (base : System.FilePath) (m : Model)
    (r0 : Report) : IO (Bool × Report) := do
  let mut r := r0
  let envPath := resolve base ((jStr rj ["environment", "ixe"]).toOption.getD "")
  unless ← envPath.pathExists do return (false, r.missing s!"environment {envPath}")
  let env ← match Ixon.readEnv (← IO.FS.readBinFile envPath) with
    | .ok e => pure e
    | .error e => return (false, r.reject s!"environment {envPath}: {e}")
  r := r.say s!"  environment {envPath}: {env.consts.size} constants, each authenticated by its address"
  let proofs := ((rj.getObjValD "claims").getArr?.toOption.getD #[]).toList
  let mut ok := !cm.claims.isEmpty
  let mut model? : Option Ixon.Term := none
  let mut pending : Array PendingClaim := #[]
  for cl in cm.claims do
    let some pf := receiptProof proofs cl.id
      | r := r.missing s!"{cl.role} claim {cl.id}: no proof in the receipt"; ok := false; continue
    let some pd := Digest.ofHex? pf
      | r := r.reject s!"{cl.id}: proof address {pf} is malformed"; ok := false; continue
    let path := storePath tools.ixStore pd
    unless ← path.pathExists do
      r := r.missing s!"{cl.id}: proof {pf} is not in the store {tools.ixStore}"; ok := false; continue
    let bytes ← IO.FS.readBinFile path
    if blake3 bytes != pd then
      r := r.reject s!"{cl.id}: the stored proof does not hash to {pf}"; ok := false; continue
    let got ← match Ixon.checkProofClaim bytes with
      | .ok c => pure c
      | .error e => r := r.reject s!"{cl.id}: proof {short pf}…: {e}"; ok := false; continue
    let want := cm.policy.expected got.const
    if got != want then
      r := r.reject s!"{cl.id}: proof {short pf}… is not the policy's Check claim: {"; ".intercalate (claimDifference got want)}"
      ok := false; continue
    let ty ← match env.definition? got.const >>= fun d =>
        if d.kind != 2 then throw s!"{got.const.short}… is not a theorem" else env.resolve d d.typ with
      | .ok t => pure t
      | .error e => r := r.reject s!"{cl.id}: the claim's constant: {e}"; ok := false; continue
    let some σ := Ixon.matchTemplate cl.holes.length cl.statement ty
      | r := r.reject s!"{cl.id}: theorem {got.const.short}… does not state the committed template"; ok := false; continue
    let some mt := σ[0]? | r := r.reject s!"{cl.id}: the template has no model hole"; ok := false; continue
    match model? with
    | none => model? := some mt
    | some prev =>
      if prev != mt then
        r := r.reject s!"{cl.id}: is about another model than the other claims"; ok := false; continue
    if cl.id.startsWith "decision" then
      let i := (String.ofList (cl.id.toList.drop "decision".length)).toNat?
      let native := (i.bind (receiptFormulas[·]?)).map (Triage.act ⟨gateThreshold⟩ m)
      let certified : Option Triage.Action := match (σ[1]? : Option Ixon.Term) with
        | some (Ixon.Term.ref a []) => (cm.actions.find? (·.2 == a)).map (·.1)
        | _ => none
      if certified.isNone || certified != native then
        r := r.reject s!"{cl.id}: the certified decision is not the native gate's on the submitted model ({repr native})"
        ok := false; continue
    pending := pending.push { claim := cl, proof := pf, expected := want }
  -- One model for every claim, and it is the submitted one.
  match model? with
  | some (.ref a []) =>
    match modelOfConstant env cm.encoding a with
    | .ok em =>
      if em == m then
        r := r.say s!"  the claims' model is constant {a.short}…, whose value is the submitted model (weights {(modelDigest m).hex})"
      else
        r := r.reject s!"the claims are about constant {a.short}…, whose value is not the submitted model"; ok := false
    | .error e => r := r.reject s!"the claims' model constant {a.short}…: {e}"; ok := false
  | some _ => r := r.reject "the claims' model is not a constant"; ok := false
  | none => ok := false
  if r.rejected || !ok then return (false, r)
  let results ← runPool 4 (pending.toList.map fun p => do
    let r? ← run? tools.ixw #["verify", p.proof]
    return (p, r?))
  for (p, r?) in results do
    let digest := p.expected.digest.hex
    match r? with
    | none => r := r.missing s!"{p.claim.id}: cannot run {tools.ixw}"; ok := false
    | some o =>
      if notRun o then r := r.missing s!"{p.claim.id}: {tools.ixw} did not start: {lastChars o.stderr 160}"; ok := false
      else if o.exitCode == 0 && (o.stdout.splitOn s!"ok: proof {p.proof} verifies claim {digest}").length > 1 then
        r := r.say s!"  [{p.claim.role}] {p.claim.id}: Check({short p.expected.const.hex}…) under the policy, claim {short digest}…, proof {short p.proof}… verified"
      else
        r := r.reject s!"{p.claim.id}: `ix verify {short p.proof}…` does not accept claim {short digest}… (exit {o.exitCode}): {lastChars (o.stderr ++ o.stdout) 200}"
        ok := false
  return (ok, r)

/-- Read the job: its BLAKE3 against the consumer's (`commitmentDigest`), then its specification,
config digest, dataset and claim encoding against this verifier's. An error carries the outcome
and the report so far. -/
def readCommitment (commitmentPath : System.FilePath) (commitmentDigest : Option String) (r0 : Report) :
    IO (Except (Outcome × Report) (Commitment × Report)) := do
  let mut r := r0
  let cBytes ← IO.FS.readBinFile commitmentPath
  let cDigest := (blake3 cBytes).hex
  if let some d := commitmentDigest then
    if Digest.ofHex? d != some (blake3 cBytes) then
      return .error (.rejected, r.reject s!"commitment {commitmentPath} has BLAKE3 {cDigest}, not the expected {d}")
  else
    r := r.say s!"note: no --commitment-blake3 given; the commitment file is trusted as the consumer's ({cDigest})"
  let some cText := String.fromUTF8? cBytes
    | return .error (.rejected, r.reject "unreadable commitment: not UTF-8")
  let cm ← match (Json.parse cText) >>= Commitment.parse with
    | .ok cm => pure cm
    | .error e => return .error (.rejected, r.reject s!"unreadable commitment: {e}")
  r := r.say s!"commitment {cDigest}: {cm.specName}, config {cm.configName}"
  let c := cm.config
  let mut ok := true
  if cm.specName != "IxAICore.Triage.spec" then
    r := r.reject s!"this verifier implements IxAICore.Triage.spec, not {cm.specName}"; ok := false
  if (configDigest c).hex != cm.configDigest then
    r := r.reject s!"config digest {(configDigest c).hex} does not match the committed {cm.configDigest}"; ok := false
  if c.trainSize != cm.datasetCount then
    r := r.reject s!"dataset count {cm.datasetCount} is not the config's {c.trainSize}"; ok := false
  let root := (datasetRoot c).hex
  if root != cm.datasetRoot then
    r := r.reject s!"dataset root {root} (computed from the spec) is not the committed {cm.datasetRoot}"; ok := false
  else r := r.say s!"  dataset: {c.trainSize} examples, root {root} (merkleRootV2), recomputed from the spec"
  if claimEncodingDigest.hex != cm.claimEncoding then
    r := r.reject s!"claim encoding {cm.claimEncoding} is not the one this verifier implements ({claimEncodingDigest.hex})"; ok := false
  unless ok do return .error (.rejected, r)
  return .ok (cm, r)

def verifyPackage (tools : Tools) (commitmentPath receiptPath : System.FilePath)
    (commitmentDigest : Option String) (work : System.FilePath) : IO (Outcome × Report) := do
  let mut r : Report := {}
  r := r.assume baseHypotheses
  let (cm, r') ← match ← readCommitment commitmentPath commitmentDigest r with
    | .ok x => pure x
    | .error e => return e
  r := r'
  let c := cm.config
  -- Receipt and model.
  let base := receiptPath.parent.getD "."
  let rText ← IO.FS.readFile receiptPath
  let rj ← match Json.parse rText with
    | .ok j => pure j
    | .error e => return (.rejected, r.reject s!"unreadable receipt: {e}")
  if (jStr rj ["format"]).toOption != some receiptFormat then
    return (.rejected, r.reject s!"receipt format is not {receiptFormat}")
  let modelPath := resolve base ((jStr rj ["model"]).toOption.getD "model.txt")
  let model ← match ← readModelFile modelPath with
    | .ok m => pure m
    | .missing e => return (.incomplete, r.missing e)
    | .malformed e => return (.rejected, r.reject e)
  if let .error e := checkModelWords c.hidden model then
    return (.rejected, r.reject s!"the submitted model: {e}")
  let m := modelOfRaw c.hidden model
  r := r.say s!"model {modelPath}: {model.length} parameters in [{weightLo}, {weightHi}), weights {(modelDigest m).hex}"
  let program := fun (name : String) => (cm.programs.find? (·.1 == name)).bind fun (_, d) => Digest.ofHex? d
  -- Training.
  r := r.say "training (`model = train Triage.spec config`):"
  let routes := ((rj.getObjValD "training").getArr?.toOption.getD #[]).toList
  let mut results : Array RouteResult := #[]
  for rt in routes do
    let kind := (jStr rt ["kind"]).toOption.getD "?"
    let path := fun (k : String) => resolve base ((jStr rt [k]).toOption.getD "")
    let res ← match kind with
      | "aiur-steps" => do
        match program "Fixed::step" with
        | none => pure { kind, status := .rejected, detail := ["the commitment approves no Fixed::step program"] }
        | some pd =>
          match ← readModels (path "models") with
          | .error e =>
            if ← (path "models").pathExists then pure { kind, status := .rejected, detail := [e] }
            else pure { kind, status := .incomplete, detail := [e] }
          | .ok ms => verifyStepRoute tools c (path "program") pd (path "proofs") ms model (work / "steps")
      | "aiur-train" => do
        match program "Fixed::train" with
        | none => pure { kind, status := .rejected, detail := ["the commitment approves no Fixed::train program"] }
        | some pd => verifyTrainRoute tools c (path "program") pd (path "proof") model (work / "train")
      | "aiur-exec" => do
        match program "Fixed::step", program "AiurExec::aiur_exec",
            Digest.ofHex? ((jStr rt ["plonkBlake3"]).toOption.getD "") with
        | some pd, some ad, some plonkD =>
          verifyExecRoute tools c (path "aggregator") ad (path "program") pd (path "root") (path "plonk") plonkD
            model (work / "exec") cm.compression ((jStr rt ["plonkKey"]).toOption.map (resolve base))
        | _, _, _ => pure { kind, status := .rejected, detail := ["the commitment approves no Fixed::step or AiurExec::aiur_exec program, or the route names no PLONK digest"] }
      | _ => pure { kind, status := .incomplete, detail := [s!"route kind `{kind}` is not implemented by this verifier; ignored"] }
    results := results.push res
    r := r.say s!"  [{kind}] {res.status.label}"
    for d in res.detail do r := r.say s!"    {d}"
  let tv := trainingVerdict results.toList
  if tv.rejected then r := { r with rejected := true }
  for x in results do
    if implementedKinds.contains x.kind && (x.status == .verified || x.status == .attested) then
      r := r.assume x.hypotheses
  if routes.isEmpty then r := r.say "  no training evidence in the receipt"
  else if !tv.proved then
    r := r.say "  no training route was re-verified in full"
    if tv.incomplete then r := { r with incomplete := true }
  -- Evaluation and deployment claims.
  r := r.say "evaluation and deployment claims:"
  let (claimsOk, r') ← verifyClaims tools cm rj base m r
  r := r'
  if claimsOk then r := r.assume (claimHypotheses tools (← fileDigestStr tools.ixw) cm)
  return (outcomeOf r.rejected r.incomplete tv.proved claimsOk, r)

end IxAIVerify
