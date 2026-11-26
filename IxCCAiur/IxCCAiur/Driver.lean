import IxCCAiur.Progress
import IxCCAiur.CompiledCert
import IxCCAiur.TypedWorld
import IxCCAiur.InlineFuse
import IxCCAiur.GuessLower
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

/-! ## Typed / Unboxed Lowering Path (`TypedLower` + `CircuitSchedule`) -/

/-- Extract the originating source constant id of a `Fir` global key, following
specialization (`spec`), dead-parameter worker (`worker`), and root entry
(`entry`) wrappers back to the annotated source definition. -/
def gkeySourceCId? : IxCC.Key.GKey → Option IxCC.Src.CId
  | .const c _ | .byName c _ => some c
  | .spec g _ | .worker g _ | .entry g _ => gkeySourceCId? g
  | .recStar _ _ | .wrapper _ _ | .lam _ _ | .dispatch _ => none

/-- Look up the `Ixon.Address` of a `Fir` function's originating source
declaration in `src`, if any. -/
def funAddress? (src : Src.Program) (fd : Fir.Fun) : Option Ixon.Address :=
  (gkeySourceCId? fd.key).bind fun cid => (src.entry? cid).map (·.addr)

private def addToGroup (groups : List (String × List String)) (groupName chipName : String) :
    List (String × List String) :=
  match groups with
  | [] => [(groupName, [chipName])]
  | (g, chips) :: rest =>
    if g == groupName then
      if chips.contains chipName then (g, chips) :: rest
      else (g, chips ++ [chipName]) :: rest
    else
      (g, chips) :: addToGroup rest groupName chipName

/-- Resolve address-keyed `sched.byAddress` directives against `(src, P)`:
1. Any `Fir.FunId` not already overridden in `sched.byFun` whose source address
   appears in `sched.byAddress` gets its `FnSchedule` added to `byFun` so
   `TypedLower` honors `@[circuit_inline]` / `@[circuit_noinline]`.
2. Any resolved `FnSchedule` (from `byFun` or `byAddress`) with `group := some g`
   registers its non-inlined chip `Prog::f<fid>` under group `g`. -/
def resolveSchedule (src : Src.Program) (P : Fir.Program)
    (sched : Schedule.CircuitSchedule) : Schedule.CircuitSchedule :=
  let resolvedByFun :=
    P.funList.foldl (init := sched.byFun) fun acc (fid, fd) =>
      if acc.any (·.1 == fid) then acc
      else
        match (funAddress? src fd).bind (fun a => sched.byAddress.find? (·.1 == a)) with
        | some (_, fs) => acc ++ [(fid, fs)]
        | none => acc
  let sched1 : Schedule.CircuitSchedule := { sched with byFun := resolvedByFun }
  let resolvedGroups :=
    P.funList.foldl (init := sched.groups) fun acc (fid, fd) =>
      let fs := sched1.forFun fid (funAddress? src fd)
      match fs.group with
      | some grp =>
        if TypedRep.shouldInlineFun P sched1 fid fd then acc
        else addToGroup acc grp (qualified (funName fid))
      | none => acc
  { sched1 with groups := resolvedGroups }

/-- A typed/unboxed lowered program, demand-linked and prepared for `Prog::main<i>`. -/
structure TypedLinked where
  lowered : TypedLower.LoweredProgram
  shapeAccepted : Bool
  program : Aiur.Modules.Program F
  entry : String
  exportRep : TypedRep.Rep
  prepared : Aiur.Modules.Prepared program
  resolvedGroups : List (String × List String) := []

/-- Infer & check `Fir.Shape.ShapeCert`, resolve `Schedule.byAddress`, lower with
`TypedLower`, optionally run `InlineFuse.optimizeFns` + `pruneUnreachable`,
demand-link, and prepare `Prog::main<i>`. -/
def linkTyped (src : Src.Program) (P : Fir.Program) (i : Nat)
    (sched : Schedule.CircuitSchedule := {})
    (inlineFuse : Bool := false) : Except String TypedLinked := do
  let resolvedSched := resolveSchedule src P sched
  let (cert, shapeAccepted) := TypedRep.inferCheckedShapes src P
  let lowered0 ← TypedLower.lowerProgram P cert resolvedSched
  let lowered :=
    if inlineFuse then
      let optFns := InlineFuse.optimizeFns lowered0.program.functions
      let pruned := InlineFuse.pruneUnreachable [entryName i] optFns
      { lowered0 with program := { lowered0.program with functions := pruned } }
    else
      lowered0
  let program := TypedLower.linkedProgram F lowered
  let entry := qualified (entryName i)
  let exportRep := lowered.exportReps[i]?.getD .obj
  let prepared ← Aiur.Modules.prepare program [entry]
  return { lowered, shapeAccepted, program, entry, exportRep, prepared,
           resolvedGroups := resolvedSched.groups }

/-- Evaluate the tier-aware world check on a typed prepared source. -/
def typedWorldReport (l : TypedLinked) : WorldReport :=
  let s := l.prepared.environment.source
  let changed : Aiur.Generic.Program Nat :=
    { l.lowered.program with
      functions := l.lowered.program.functions.map fun g => { g with body := .tuple [] } }
  let tablesOk := match l.lowered.tier with
    | .none => true
    | .byte256 => TypedWorld.checkU8ByteTable s
    | .u32 | .u64 => World.checkTables s
  let libOk := match l.lowered.tier with
    | .u64 => checkU64Functions s
    | _ => true
  let fnsOk := World.checkFunctions s l.lowered.program
  let refuses :=
    !World.checkFunctions s changed &&
    (match l.lowered.tier with
     | .byte256 => !World.checkTable s "U8Byte::byte_units" []
     | .u32 | .u64 => !World.checkTable s "UInt8::pair_units" []
     | .none => true)
  { tables := tablesOk, library := libOk, functions := fnsOk
    failing := World.failing s l.lowered.program, refuses }

/-- Read an unboxed typed Aiur `SourceValue` back as an observation. -/
def typedReadback (P : Fir.Program) (cert : Fir.Shape.ShapeCert) (feat : TypedRep.Features)
    (heap : Aiur.Heap F) : Nat → TypedRep.Rep → Aiur.SourceValue F → Option Sem.Obs
  | 0, _, _ => none
  | _ + 1, .nat _, .field x => some (.nat x.val)
  | _ + 1, .w8, .field x => some (.nat x.val)
  | _ + 1, .w16, .field x => some (.nat x.val)
  | _ + 1, .w32, .tuple [.field b0, .field b1, .field b2, .field b3] =>
    some (.nat (b0.val + 256 * b1.val + 65536 * b2.val + 16777216 * b3.val))
  | _ + 1, .w64, .tuple [.field b0, .field b1, .field b2, .field b3,
                         .field b4, .field b5, .field b6, .field b7] =>
    some (.nat (Aiur.Library.U64.pack b0.val b1.val b2.val b3.val b4.val b5.val b6.val b7.val))
  | _ + 1, .enum _, .construct _ name [] => do
    let idx ← (objCtorNames P).idxOf? name
    let entry ← P.ctors[idx]?
    let .src cid := entry.key | none
    return .ctor cid []
  | fuel + 1, .data d, .construct _ name ps => do
    let idx ← (objCtorNames P).idxOf? name
    let entry ← P.ctors[idx]?
    let .src cid := entry.key | none
    let D ← cert.data? d
    let (_, fl) ← D.ctors.find? (·.1 == entry.key)
    let fs ← (ps.zip fl).mapM fun (pv, sh) => do
      let fr := TypedRep.repOf P cert feat sh
      let val ← if TypedRep.dataFieldNeedsPtr P cert feat d fr then
        match pv with
        | .ptr _ a => heap[a]?
        | _ => none
      else some pv
      typedReadback P cert feat heap fuel fr val
    return .ctor cid fs
  | fuel + 1, .obj, v => readback P heap (fuel + 1) v
  | _ + 1, _, _ => none

/-- Evaluate a typed linked entry on `Nat` inputs via Formal Aiur's fuelled evaluator. -/
def typedAiurRun (P : Fir.Program) (l : TypedLinked) (args : List Nat) (fuel : Nat := 100000000) :
    Except String (Aiur.SourceValue F × Option Sem.Obs) := do
  let hints := l.prepared.environment.source.checkedHints
    (Hints.dispatcher (fun (x : F) => x.val))
  let (value, heap) ← l.prepared.run l.entry (args.map fun n => .field (n : F)) fuel hints
  let feat := TypedRep.scanFeatures P
  return (value, typedReadback P l.lowered.cert feat heap 10000 l.exportRep value)

/-- Compile a typed linked program once (`compileOptimized` + budget check + parallel
`Trace.exportPlanPar`), returning chip stats, serialized `.ixa`, and its BLAKE3 digest. -/
def compileTypedPackage (l : TypedLinked)
    (sched : Schedule.CircuitSchedule := {})
    (kind : CompiledCert.ArtifactKind := .program)
    (args : List Nat := []) : Except String Compiled := do
  let execution ← l.prepared.exportExecution
  let compiled ← l.prepared.compileOptimized sched.aiurConfig
  let chips := chipSummaryOf compiled
  let summary : Schedule.CircuitSummary :=
    { chips := chips.map fun (name, columns, calls, memory) => { name, columns, calls, memory } }
  summary.checkBudget sched.budget
  let mergedGroups := sched.groups.foldl (init := l.resolvedGroups) fun acc (g, cs) =>
    cs.foldl (fun acc' c => addToGroup acc' g c) acc
  let (execution, trace) ← Aiur.Trace.exportPlanPar modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact execution mergedGroups
  let bytes ← match kind with
    | .program => Aiur.Artifact.package execution modulus ZMod.val (some trace)
    | .execution => Aiur.Artifact.execution execution modulus ZMod.val (some trace) args [] #[]
  return { chips, kind, bytes, digest := Ixon.Address.blake3Pure bytes }

/-- Per-chip stats for a typed linked program. -/
def typedChipStats (l : TypedLinked) (sched : Schedule.CircuitSchedule := {}) :
    Except String (List (String × Nat × Nat × Nat)) := do
  let compiled ← l.prepared.compileOptimized sched.aiurConfig
  return chipSummaryOf compiled

/-! ## Phase 2.2d Tier-2 `guess` Front-End, Lowering & Universal Advice Package -/

/-- Front-end ingress + `produceFir` + `runFir` with Tier-2 `guess` support:
1. Parses `equations` (`ixcc/k1-equations/1`) containing `"guesses"` (and optional `"equations"`).
2. If `"equations"` / `"theorems"` has no `.eqn`/`.word` proposals (as in `ix compile
   --circuit-guesses-out`), automatically merges `Src.AutoHints.discover env pins` so
   recursive functions (e.g. `egcdStep`) still unfold cleanly in the companion advice program.
3. Adds every `guess` checker address as a temporary root and adds both guess subjects and
   checkers to `budgets.«inline».noInline` so `Lam.erase`, `Anf.Inline`, and `Fir.lower` keep
   both `f` and `c` intact as distinct `Fir` functions.
4. Strips the extra checker exports back to the original user root count after `runFir`. -/
def frontWithGuesses (bytes : ByteArray) (equations : Lean.Json) (roots : List String)
    (limits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits) : Except String Front := do
  let env ← (Ixon.V3.decodeAnonymousEnv bytes).mapError fun m => s!"ingress: decode: {m}"
  let sidecar ← Src.Hints.ofK1Json equations
  let acc ← (Src.KernelFront.accept env limits).mapError fun r =>
    s!"ingress: kernel: {r.report}"
  let () ← (Src.KernelFront.defaultModeCheck acc).mapError fun r =>
    s!"ingress: mode-check: {r.report}"
  let pins := Src.KernelFront.pinsOfTable acc.table
  let chosen : Array (Ixon.Address × Option String) ←
    if !roots.isEmpty then
      (Src.AutoHints.resolveRoots env roots).mapError fun m => s!"cli: cli.root: {m}"
    else if !sidecar.roots.isEmpty then
      pure sidecar.roots
    else
      (Src.AutoHints.resolveRoots env []).mapError fun m => s!"cli: cli.root: {m}"
  let hasEqn := sidecar.proposals.any fun p => p.kind == .eqn || p.kind == .word
  let proposals :=
    if hasEqn then sidecar.proposals
    else Src.AutoHints.discover env pins ++ sidecar.proposals
  let origRootCount := chosen.size
  let checkerRoots : Array (Ixon.Address × Option String) :=
    proposals.foldl (init := #[]) fun acc p =>
      if p.kind == .guess then
        match p.checker? with
        | some chkAddr =>
          if chosen.any (·.1 == chkAddr) || acc.any (·.1 == chkAddr) then acc
          else acc.push (chkAddr, some s!"__guess_checker_{acc.size}")
        | none => acc
      else acc
  let allRoots := chosen ++ checkerRoots
  let names := allRoots.toList.zipIdx.map fun ((_, n), i) => n.getD s!"root{i}"
  let namedRoots := allRoots.zipIdx.map fun ((a, n), i) => (a, some (n.getD s!"root{i}"))
  let hints : Src.Hints := { roots := namedRoots, proposals }
  let records ← (Src.Ingress.reach env (Src.Ingress.Seeds.of hints pins)).mapError fun m =>
    s!"ingress: decode: {m}"
  let p ← (Src.Ingress.readConsts env records (namedRoots.map (·.1))).mapError fun m =>
    s!"ingress: ingress: {m}"
  let p := { p with known := { pins } }
  let p := { p with known := Src.Pinned.known p }
  let rd ← (Src.KernelFront.Reading.build acc p).mapError fun m =>
    s!"ingress: faithful: {m}"
  let input : Recheck.Input :=
    { env, hints, program := p, names, kernel := { acc, rd, fe := Ix.Kernel.mkFEnv acc.env } }
  let guessNoInline : List Key.GKey :=
    proposals.toList.flatMap fun pr =>
      if pr.kind == .guess then
        let sKeys := match p.lookup pr.subject with
          | some cid => [Key.GKey.const cid []]
          | none => []
        let cKeys := match pr.checker?.bind p.lookup with
          | some cid => [Key.GKey.const cid []]
          | none => []
        sKeys ++ cKeys
      else []
  let baseCfg0 := Recheck.Config.forInput {} input
  let baseCfg : Recheck.Config := {
    baseCfg0 with
    budgets := {
      baseCfg0.budgets with
      «inline» := {
        baseCfg0.budgets.«inline» with
        noInline := baseCfg0.budgets.«inline».noInline ++ guessNoInline
      }
    }
  }
  let attempt (cfg : Recheck.Config) : Except Recheck.Err Front := do
    let cert ← Recheck.produceFir cfg input
    unless Recheck.checkCanonicalRelevance cfg input cert.table cert.relevance do
      throw { stage := .relevance, code := "relevance-canonical"
              message := "certificate relevance annotation does not match canonical annotator output" }
    let levels ← Recheck.runFir cfg input.program cert
    let fir' := { levels.fir with exports := levels.fir.exports.take origRootCount }
    let levels' := { levels with fir := fir' }
    let input' := { input with names := input.names.take origRootCount }
    return { input := input', cfg, cert, levels := levels' }
  (Compile.withRetry baseCfg attempt).mapError (·.render)

/-- Unmodified pre-guess prepared program exposing every resolved guess subject as a
callable entrypoint for both Lean (`Hints.dispatcherWithAdvice`) and Rust
(`aiur::library::ixcc::register_advice_program`). -/
structure AdviceLinked where
  lowered : TypedLower.LoweredProgram
  program : Aiur.Modules.Program F
  entries : List String
  prepared : Aiur.Modules.Prepared program

/-- Serialize a bytecode-only `IXAIURP\0` package (no STARK trace section) for host advice
execution in `ixcc_prove --advice ADVICE.ixa`. -/
def compileAdvicePackage (adv : AdviceLinked) : Except String ByteArray := do
  let execution ← adv.prepared.exportExecution
  Aiur.Artifact.package execution modulus ZMod.val none

/-- Result of typed lowering with Phase 2.2d Tier-2 `guess` rewriting enabled. -/
structure TypedLinkedWithGuesses where
  linked : TypedLinked
  advice : Option AdviceLinked
  resolved : List GuessLower.ResolvedGuess
  skipped : List (Src.CId × String)
  manifest : GuessLower.AdviceManifest
  foldedFir : Fir.Program

/-- Typed lowering with Phase 2.2d Tier-2 `guess` rewriting:
1. Seeds `ShapeCert` so checkers receive exact unboxed parameter shapes (`seedGuessShapes`).
2. Runs the certified `foldOversizedNatCmp` pre-pass (for curve prime bounds like `2^384`).
3. Lowers the unmodified program (`lowered0`) and builds the companion `AdviceLinked`
   program exposing every resolved guess subject for zero-hardcoding host advice.
4. Rewrites resolved guess subjects via `GuessLower.applyGuesses` (keeping `isInline := false`
   on every guess wrapper per the Aiur cost law), optionally runs `InlineFuse.optimizeFns`,
   prunes unreachable functions (e.g. `egcdStep`), links, and prepares `Prog::main<i>`. -/
def linkTypedWithGuesses (src : Src.Program) (P : Fir.Program) (i : Nat)
    (sched : Schedule.CircuitSchedule := {})
    (inlineFuse : Bool := false) : Except String TypedLinkedWithGuesses := do
  let resolvedSched := resolveSchedule src P sched
  let (cert, shapeAccepted0) := GuessLower.seedGuessShapes src P
  let folded := GuessLower.foldOversizedNatCmp P cert
  let (PWork, shapeAccepted) :=
    if shapeAccepted0 && Fir.Shape.check folded cert then
      (folded, true)
    else
      (P, shapeAccepted0)
  let lowered0 ← TypedLower.lowerProgram PWork cert resolvedSched
  let gl := GuessLower.applyGuesses src PWork lowered0
  let entry := qualified (entryName i)
  let advice ←
    if gl.resolved.isEmpty then pure none
    else do
      let (advLowered, advEntries) := GuessLower.prepareAdviceProgram lowered0 gl.resolved
      let advProgram := TypedLower.linkedProgram F advLowered
      let allAdvEntries := entry :: advEntries.filter (· != entry)
      let advPrepared ← Aiur.Modules.prepare advProgram allAdvEntries
      pure (some {
        lowered := advLowered
        program := advProgram
        entries := allAdvEntries
        prepared := advPrepared
      })
  let lowered :=
    if inlineFuse then
      let optFns := InlineFuse.optimizeFns gl.lowered.program.functions
      let pruned := InlineFuse.pruneUnreachable [entryName i] optFns
      { gl.lowered with program := { gl.lowered.program with functions := pruned } }
    else if !gl.resolved.isEmpty then
      let pruned := InlineFuse.pruneUnreachable [entryName i] gl.lowered.program.functions
      { gl.lowered with program := { gl.lowered.program with functions := pruned } }
    else
      gl.lowered
  let program := TypedLower.linkedProgram F lowered
  let exportRep := lowered.exportReps[i]?.getD .obj
  let prepared ← Aiur.Modules.prepare program [entry]
  let linked : TypedLinked := {
    lowered, shapeAccepted, program, entry, exportRep, prepared
    resolvedGroups := resolvedSched.groups
  }
  return {
    linked, advice, resolved := gl.resolved, skipped := gl.skipped
    manifest := gl.manifest, foldedFir := PWork
  }

/-- Evaluate a guess-lowered typed entry on `Nat` inputs via Formal Aiur's fuelled evaluator,
answering `"ixcc.guess.<fn>"` channels automatically via `Hints.dispatcherWithAdvice`. -/
def typedAiurRunWithAdvice (P : Fir.Program) (l : TypedLinked)
    (advice : Option AdviceLinked) (args : List Nat) (fuel : Nat := 100000000) :
    Except String (Aiur.SourceValue F × Option Sem.Obs) := do
  let advicePair := advice.map fun a => (⟨a.program, a.prepared⟩ : Σ p : Aiur.Modules.Program F, Aiur.Modules.Prepared p)
  let hints := l.prepared.environment.source.checkedHints
    (Hints.dispatcherWithAdvice (fun (x : F) => x.val) advicePair)
  let (value, heap) ← l.prepared.run l.entry (args.map fun n => .field (n : F)) fuel hints
  let feat := TypedRep.scanFeatures P
  return (value, typedReadback P l.lowered.cert feat heap 10000 l.exportRep value)

end IxCC.AiurBackend.Driver
