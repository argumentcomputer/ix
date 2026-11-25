import IxCCAiur.Progress
import IxCCAiur.CompiledCert
import IxCCAiur.Hints
import IxCC.Compile
import IxCC.Recheck.RunFir
import IxCC.Recheck.Produce
import IxCC.Src.AutoHints
import IxCC.Fir.Proof.Lang
import Aiur.Trace.Export
import Aiur.Artifact

/-! # From a closure to a prover package

The steps the executable `ixcc-aiur` runs (`IxCCAiur.Main`), as functions:

```text
.ixe + equations ─Recheck.ingress→ Src.Program ─Recheck.produce→ certificate
                 ─Recheck.runFir→ Fir.Program ─Lower.lowerModule→ module Prog
                 ─Lower.linkedProgram (the UInt64 library)→ Aiur.Modules.Program
                 ─Aiur.Modules.prepare→ the prepared source (what the theorems quantify over)
                 ─compileOptimized, Trace.exportPlan→ circuits
                 ─Aiur.Artifact.execution→ an execution package (.ixa) for one invocation
```

The producer (`Recheck.produce`) is untrusted, as everywhere: `runFir` re-runs
the front half on its certificate. The package is what the Rust development
driver proves (`crates/aiur/examples/ixcc_prove.rs`); it carries no hint data,
the host answers the channels (`IxCCAiur.Hints`).

`worldReport` evaluates `World.checkWorld` on the prepared source: it is the
hypothesis `hw` of `Claim.accepted_nat_backward` and of the `fib` instance,
computed here natively for the program a package is written for, not
re-checked by the kernel. `aiurRun` evaluates an entry on Formal Aiur's
fuelled evaluator, whose successful runs are source derivations
(`Aiur.Modules.Prepared.run_spec`), and `firRun` is the compiler's
`Fir.firRun`; `main` writes a package only when the world check holds and the
two agree. -/

namespace IxCC.AiurBackend.Driver

open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets

abbrev F := Aiur.Library.U32.Goldilocks.F

def modulus : Nat := Aiur.Library.U32.Goldilocks.modulus

/-- What the front half makes of a closure: the ingested program, the
producer's certificate, and the levels down to Fir. -/
structure Front where
  input : Recheck.Input
  cfg : Recheck.Config
  cert : Recheck.Cert
  levels : Recheck.FrontFir

/-- Run `produceFir`, Stage A canonical relevance check, and `Recheck.runFir` on an ingested
input, retrying without `retryInline` on failure when `retryInline` is enabled. -/
def frontOfInput (input : Recheck.Input) : Except String Front := do
  let baseCfg := Recheck.Config.forInput {} input
  let attempt (cfg : Recheck.Config) : Except Recheck.Err Front := do
    let cert ← Recheck.produceFir cfg input
    unless Recheck.checkCanonicalRelevance cfg input cert.table cert.relevance do
      throw { stage := .relevance, code := "relevance-canonical"
              message := "certificate relevance annotation does not match canonical annotator output" }
    let levels ← Recheck.runFir cfg input.program cert
    return { input, cfg, cert, levels }
  (Compile.withRetry baseCfg attempt).mapError (·.render)

/-- Ingress with an explicit `ixcc/k1-equations/1` JSON sidecar, `produceFir`, and `runFir`. -/
def front (bytes : ByteArray) (equations : Lean.Json) (roots : List String) : Except String Front := do
  let input ← (Recheck.ingress bytes equations roots).mapError (·.render)
  frontOfInput input

/-- Auto-discovered ingress (`Src.AutoHints.resolveRoots` + `Compile.ingressRoots`),
`produceFir`, and `runFir`, requiring no external `EQUATIONS.json` sidecar. -/
def frontAuto (bytes : ByteArray) (roots : List String := [])
    (limits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits) : Except String Front := do
  let env ← (Ixon.V3.decodeAnonymousEnv bytes).mapError fun m => s!"ingress: decode: {m}"
  let chosen ← (Src.AutoHints.resolveRoots env roots).mapError fun m => s!"cli: cli.root: {m}"
  let input ← (Compile.ingressRoots env chosen limits).mapError (·.render)
  frontOfInput input

/-- A lowered program, linked with the `UInt64` library and prepared for the
one entry `Prog::main<i>`. -/
structure Linked where
  lowered : Aiur.Generic.Program Nat
  program : Aiur.Modules.Program F
  entry : String
  prepared : Aiur.Modules.Prepared program

/-- Lower a Fir program, link it and prepare it with export `i` as its entry. -/
def link (P : Fir.Program) (i : Nat) : Except String Linked := do
  let lowered ← lowerProgram P
  let m : Aiur.Modules.Program Nat :=
    { modules := [{ name := moduleName, body := .definitions { program := lowered } }] }
  let program := linkedProgram F m
  let entry := qualified (entryName i)
  let prepared ← Aiur.Modules.prepare program [entry]
  return { lowered, program, entry, prepared }

/-! ## The world check -/

/-- `World.checkWorld`'s three verdicts on the prepared source, and the
lowered functions that differ from it. -/
structure WorldReport where
  tables : Bool
  library : Bool
  functions : Bool
  failing : List String
  /-- The check refuses what it should: the lowered program with every body
  replaced by `()`, and a table against the empty row list. -/
  refuses : Bool

/-- `World.checkWorld` holds (and the check refused its two controls). -/
def WorldReport.ok (r : WorldReport) : Bool :=
  r.tables && r.library && r.functions && r.refuses

/-- Evaluate the world check on what `Aiur.Modules.prepare` returned. -/
def worldReport (l : Linked) : WorldReport :=
  let s := l.prepared.environment.source
  let changed : Aiur.Generic.Program Nat :=
    { l.lowered with functions := l.lowered.functions.map fun g => { g with body := .tuple [] } }
  { tables := World.checkTables s
    library := checkU64Functions s
    functions := World.checkFunctions s l.lowered
    failing := World.failing s l.lowered
    refuses := !World.checkFunctions s changed && !World.checkTable s "UInt8::pair_units" [] }

/-! ## The shape decision -/

/-- The source-progress lane's shape decision for root 0 at `n` `Nat`
arguments (`Progress.checkShape`), on the certificate its untrusted producer
proposes for the checked source. Where it holds, an accepted claim of the
entry is the source's value without the stuck-source disjunct
(`Progress.accepted_nat`); where it does not, the statement keeps the
disjunct. It does not gate the package. -/
def shapeCheck (f : Recheck.FrontFir) (n : Nat) : Bool :=
  match f.src.roots[0]? with
  | some (_, c) => Progress.checkShape f.src (SrcShape.Produce.produce f.src c) 0 n
  | none => false

/-! ## The two evaluators -/

/-- Read an `Obj` back through the heap as an observation: `N` is a `Nat`, a
source constructor its identity with its loaded fields; an erased value, a
string and a closure have none here. -/
def readback (P : Fir.Program) (heap : Aiur.Heap F) : Nat → Aiur.SourceValue F → Option Sem.Obs
  | 0, _ => none
  | _ + 1, .construct _ "N" [.field x] => some (.nat x.val)
  | fuel + 1, .construct _ name ps => do
    let idx ← (objCtorNames P).idxOf? name
    let entry ← P.ctors[idx]?
    let .src cid := entry.key | none
    let fs ← ps.mapM fun p => match p with
      | .ptr _ a => heap[a]? >>= readback P heap fuel
      | _ => none
    return .ctor cid fs
  | _ + 1, _ => none

/-- The Aiur evaluator's outcome for the linked entry on `Nat` inputs: an
observation, or why it found no derivation. -/
def aiurRun (P : Fir.Program) (l : Linked) (args : List Nat) (fuel : Nat := 100000000) :
    Except String (Aiur.SourceValue F × Option Sem.Obs) := do
  let hints := l.prepared.environment.source.checkedHints
    (Hints.dispatcher (fun (x : F) => x.val))
  let (value, heap) ← l.prepared.run l.entry (args.map fun n => .field (n : F)) fuel hints
  return (value, readback P heap 100000 value)

/-- Fir's outcome for export `i` at a large clock, as an observation. -/
def firRun (P : Fir.Program) (i : Nat) (args : List Nat) (clock : Nat := 1000000) :
    Sem.Result (Option Sem.Obs) :=
  (Fir.firRun P (i, args) clock).map Fir.obsV

/-! ## Circuits and the package -/

/-- Per-chip summary `(name, columns, call lookups, memory lookups)` from an
optimized circuit artifact (before grouping and the depth pass). -/
def chipSummaryOf {moduleProg : Aiur.Modules.Program F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    (compiled : Aiur.Optimized.ModulesArtifact prepared) :
    List (String × Nat × Nat × Nat) :=
  compiled.circuit.artifact.system.chips.map fun c =>
    (c.name, c.numVars, c.sends.length, c.memory.length)

/-- Result of a single compilation + trace export: carries chip stats, the
serialized `.ixa` artifact (`IXAIURP\0` program package or `IXAIURX\0` execution
package), and its pure-Lean BLAKE3 digest. -/
structure Compiled where
  chips : List (String × Nat × Nat × Nat)
  kind : CompiledCert.ArtifactKind
  bytes : ByteArray
  digest : Ixon.Address

/-- Compile `l` once (`compileOptimized` + parallel `Trace.exportPlanPar`),
returning chip stats and the serialized `.ixa` artifact with its BLAKE3 digest.
Defaults to a reusable `IXAIURP\0` program package (`ArtifactKind.program`). -/
def compilePackage (l : Linked)
    (kind : CompiledCert.ArtifactKind := .program)
    (args : List Nat := [])
    (config : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String Compiled := do
  let execution ← l.prepared.exportExecution
  let compiled ← l.prepared.compileOptimized config
  let chips := chipSummaryOf compiled
  let (execution, trace) ← Aiur.Trace.exportPlanPar modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact execution groups
  let bytes ← match kind with
    | .program => Aiur.Artifact.package execution modulus ZMod.val (some trace)
    | .execution => Aiur.Artifact.execution execution modulus ZMod.val (some trace) args [] #[]
  return { chips, kind, bytes, digest := Ixon.Address.blake3Pure bytes }

/-- Per chip of the compiled circuits: name, columns, call lookups, memory
lookups (before grouping and the depth pass). -/
def chipStats (l : Linked) (config : Aiur.Optimized.Config := {}) :
    Except String (List (String × Nat × Nat × Nat)) := do
  let compiled ← l.prepared.compileOptimized config
  return chipSummaryOf compiled

/-- The reusable program package (`IXAIURP\0`) for the linked entry: compiled
program and certified trace plan, independent of any invocation's arguments. -/
def programPackage (l : Linked) (config : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String ByteArray :=
  (·.bytes) <$> compilePackage l .program [] config groups

/-- The execution package (`IXAIURX\0`) for the linked entry on `args`: the
compiled program, its circuits, and one invocation. No hint data. -/
def package (l : Linked) (args : List Nat) (config : Aiur.Optimized.Config := {})
    (groups : List (String × List String) := []) : Except String ByteArray :=
  (·.bytes) <$> compilePackage l .execution args config groups

end IxCC.AiurBackend.Driver
