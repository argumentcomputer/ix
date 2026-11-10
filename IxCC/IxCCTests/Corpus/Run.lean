import IxCCTests.Corpus.Manifest
import IxCCTests.Corpus.Budget
import IxCCTests.Pipeline.Levels
import IxCC.Anf.Print
import IxCC.Lir.Print
import IxCC.Xv.Print

/-! The corpus suite (MT.2): every root of every registered corpus family,
against its frozen cases (`ixcc/corpus/1`).

For each root the compiler (`Recheck.ingress`, `produce`, `run`) either

* **declines** it, and then the manifest must record exactly that
  `stage: code` (an unexpected decline fails, so a decline is always a
  reviewed fact of the manifest; a root the manifest expects declined must
  not compile); or
* **compiles** it, and then every case runs at every level the pipeline suite
  checks (`IxCCTests.Pipeline.Levels.runLevel`): SrcEval on the checked
  program, Lam, Anf after P1 and after each certificate step, Fir, Own
  (immortal) and Cfg, then Lir, Xv and Xl from `cx_init`'s memory, the typed
  x86 machine and ByteEval on the object's `.text` (only on the cases the
  manifest marks `machine`, since they step one instruction at a time), and
  natively (with `--cc`) under `fixtures/x86/runtime_driver.c`.

The expected observations come from Lean 4.34's interpreter (recorded in the
manifest by `corpus rebuild`) and, where given, an independent constant:

* the source levels (SrcEval to Cfg) have unbounded `Nat`, so they must give
  `ok` and the interpreter's value;
* the word levels (Lir onwards, and native code) must give that value when
  the arguments and the result are below `2⁶³`, and `natOverflow` (status 3)
  when the result is not; a case may `allow` reviewed resource failures
  (`natOverflow` when an intermediate value reaches `2⁶³`, `heap` when its
  immortal allocations outgrow the word levels' 64 KiB region), which are
  counted;
* a case with an argument of at least `2⁶³` has no word: only the entry
  wrapper runs (typed x86 and ByteEval when the argument fits a register,
  native code always) and must return status 3.

The big-step evaluators nest native frames per recursive call, so the
suite re-runs itself once with a large Lean stack (`LEAN_STACK_SIZE_KB`, as
`tests-src` does for `sum-loop`). -/

namespace IxCCTests.Corpus

open IxCC IxCC.Recheck IxCCTests.Src IxCCTests.Pipeline
open System

/-- Levels with unbounded `Nat` (before `Rt.lower`). -/
def sourceLevel (level : String) : Bool :=
  ["src", "lam", "fir", "own", "cfg"].contains level || level.startsWith "anf"

def wordLevel (level : String) : Bool := ["lir", "xv", "xl"].contains level

def machineLevel (level : String) : Bool := level == "x86" || level == "bytes"

/-- The resource failure an outcome is, by the driver's status codes
(1 heap, 2 stack, 3 natOverflow, 4 trap) or the word levels' `resource`. -/
def failure (outcome : String) : Option String :=
  match outcome with
  | "status 1" => some "heap" | "status 2" => some "stack" | "status 3" => some "natOverflow"
  | "status 4" | "trap" => some "trap"
  | _ =>
    if outcome.startsWith "resource" then
      ["heap", "stack", "natOverflow"].find? fun r => (outcome.splitOn r).length > 1
    else none

/-- An outcome that is the `natOverflow` failure (status 3). -/
def overflow (outcome : String) : Bool := failure outcome == some "natOverflow"

structure Options where
  cc : Option String := none
  work : Option FilePath := none
  manifests : List FilePath := []
  only : List String := []
  roots : List String := []
  machines : Bool := true
  progress : Bool := false
  survey : Bool := false
  dump : Bool := false
  observe : Bool := false

structure Tally where
  compiled : Nat := 0
  declined : Nat := 0
  cases : Nat := 0
  runs : Nat := 0
  native : Nat := 0
  allowed : Nat := 0

/-- Judge one word-level, machine or native outcome against the case: the
required failure where the level models it, else the value or an allowed
failure. Whether it was an allowed failure. -/
def judge (a : Assert) (label level : String) (want : Want) (allow : List String) (outcome : String)
    (obs : String) : IO Bool := do
  match want.value, want.fail with
  | none, f =>
    let f := f.getD "natOverflow"
    expect a (failure outcome == some f) s!"{label}: {outcome} {obs}, expected {f} (no word)"; pure false
  | some v, some f =>
    if models level f then
      expect a (failure outcome == some f) s!"{label}: {outcome} {obs}, expected the failure {f}"; pure false
    else
      expect a (outcome == "ok") s!"{label}: {outcome}, expected ok {v} (the level has no {f})"
      expect a (obs == v) s!"{label}: reads back {obs}, expected {v}"
      pure false
  | some v, none =>
    if (failure outcome).any allow.contains then expect a true ""; pure true
    else
      expect a (outcome == "ok") s!"{label}: {outcome}, expected ok {v}"
      expect a (obs == v) s!"{label}: reads back {obs}, expected {v}"
      pure false

/-- The readback type the suite reads a root's result at: the compiler's
(`Nat`, `Bool`), or for an `enum` result one inductive of field-less
constructors (Phase 1's `rootTy` reads enums back as nothing). -/
def resultTy (r : Root) (ty : Option (Rt.Sig × Rt.FoTy)) : Option (Rt.Sig × Rt.FoTy) :=
  match r.result, r.ctors with
  | "enum", some n => some ({ inds := [List.replicate n []] }, .ind 0)
  | _, _ => ty

/-- The word levels' region and the machines' stack budget for a case. -/
def caseRegion (cs : Case) : Nat := cs.region.getD IxCCTests.Rt.defaultSize
def caseBudget (cs : Case) : Lir.Word :=
  match cs.stack with
  | some s => UInt64.ofNat (s - 4096)
  | none => IxCCTests.Rt.defaultBudget

/-- The driver's region and stack for a case. -/
def nativeRegion (cs : Case) : Nat := cs.region.getD (1 <<< 24)
def nativeStack (cs : Case) : Nat := cs.stack.getD (1 <<< 28)

/-- Every case of one compiled root at every level, and natively. -/
def runRoot (a : Assert) (o : Options) (native : Option Rt.Native.Tools) (label : String) (r : Root)
    (c : Levels.Compiled) (t : IO.Ref Tally) : IO (Array String) := do
  let levels := Levels.levelNames c
  let some root0 := c.art.roots.head? | throw (IO.userError s!"{label}: no root")
  let root := { root0 with ty := resultTy r root0.ty }
  let c := { c with art := { c.art with roots := root :: c.art.roots.drop 1 } }
  expectEq a root.params r.params s!"{label}: parameters"
  let mut times : Array (String × Nat) := levels.toArray.map (·, 0)
  for cs in r.cases do
    let some want := cs.expect r | throw (IO.userError s!"{label} {cs.args}: no expectation")
    let src := cs.sourceObs r
    let noWord := cs.args.any (· ≥ limit)
    for (level, i) in levels.zipIdx do
      -- the source levels run on Lean's runtime `Nat`, which fails where its interpreter does
      let run := if sourceLevel level then !noWord && src.isSome && !cs.leanFails
        else if wordLevel level then !noWord
        else o.machines && (cs.machine || noWord) && cs.args.all (· < 2 ^ 64)
      if !run then continue
      let ((outcome, obs), ms) ← timed (Levels.runLevel c level cs.args (caseRegion cs) (caseBudget cs))
      let obs := (obs.map Rt.renderObs).getD "-"
      let l := s!"{label} {cs.args} at {level}"
      if sourceLevel level then
        expect a (outcome == "ok") s!"{l}: {outcome}, expected ok {src.getD ""}"
        expect a (some obs == src) s!"{l}: reads back {obs}, expected {src.getD ""}"
      else if ← judge a l level want cs.allow outcome obs then
        t.modify fun t => { t with allowed := t.allowed + 1 }
      times := times.modify i fun (n, ms') => (n, ms' + ms)
      t.modify fun t => { t with runs := t.runs + 1 }
      if o.progress then IO.eprintln s!"      {l}: {outcome} {obs} ({ms} ms)"
    t.modify fun t => { t with cases := t.cases + 1 }
  let mut out := #[s!"{label}: {r.cases.length} cases, {levels.length} levels (ms: \
    {", ".intercalate (times.toList.filter (·.2 > 0) |>.map fun (l, ms) => s!"{l} {ms}")})"]
  if let some nt := native then
    let exe ← link nt s!"corpus_{label.replace "/" "_"}" c.art.object root.symbol
    -- one driver run per region and stack; a non-`Nat` result's object area
    -- is dumped, so Lean's `Rt.readback` reads it back as the C decoder did
    let groups := r.cases.foldl (init := ([] : List (Nat × Nat))) fun gs cs =>
      let g := (nativeRegion cs, nativeStack cs)
      if gs.contains g then gs else gs ++ [g]
    let mut ms := 0
    let mut n := 0
    for (region, stack) in groups do
      let css := r.cases.filter fun cs => (nativeRegion cs, nativeStack cs) == (region, stack)
      let dump := r.result != "nat"
      let (lines, ms') ← timed (Rt.Native.run exe { region, stack, ty := root.ty, dump } (css.map (·.args)))
      ms := ms + ms'
      n := n + lines.length
      for (cs, ln) in css.zip lines do
        let some want := cs.expect r | continue
        let l := s!"{label} {cs.args} natively{if (region, stack) == (1 <<< 24, 1 <<< 28) then "" else s!" (--region {region} --stack {stack})"}"
        expect a ln.ok s!"{l}: registers not restored"
        let outcome := if ln.status == 0 then "ok" else s!"status {ln.status}"
        if ← judge a l "native" want cs.allow outcome (ln.obs.getD "-") then
          t.modify fun t => { t with allowed := t.allowed + 1 }
        -- Lean's readback of the native word (and object area) is the C decoder's
        if ln.status == 0 && !ln.init then
          if let some (sig, ty) := root.ty then
            let mem : X86.Memory := match ln.dump with
              | some d => d.memory region
              | none => { bytes := fun _ => 0, readable := fun _ => false, writable := fun _ => false }
            let lean := (Rt.readback sig (region / 8) mem ty ln.value).map Rt.renderObs
            expect a (lean == ln.obs) s!"{l}: Rt.readback gives {lean}, the C decoder {ln.obs}"
    t.modify fun t => { t with native := t.native + n }
    out := out.push s!"  natively: {n} cases agree ({ms} ms{if groups.length > 1 then s!", {groups.length} driver runs" else ""})"
  return out

/-- Ingress (without typing: the census covers it) and compile one root,
with the roots it is compiled `together` with; an ingress failure is a
decline at `ingress`. -/
def compileRoot (m : Family) (f : Fixture) (r : Root) : IO (Except Err (Cert × Artifact)) := do
  let dir : FilePath := m.directory
  let bytes ← IO.FS.readBinFile (dir / f.closure.path)
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / f.equations.path)))
  IO.lazyPure fun _ => do
    let inp ← ingress bytes json (r.name :: r.together) (typecheck := false)
    compileInput {} inp

/-- One root: declined as the manifest expects, or compiled and run. -/
def root (a : Assert) (o : Options) (native : Option Rt.Native.Tools) (m : Family) (f : Fixture) (r : Root)
    (t : IO.Ref Tally) : IO (Array String) := do
  let label := s!"{f.name}/{r.name}"
  let result ← compileRoot m f r
  match result, r.decline with
  | .error e, some d =>
    expect a (e.stage.name == d.stage && e.code == d.code)
      s!"{label}: declined with {e.render}, the manifest expects {d.stage}: {d.code}"
    t.modify fun t => { t with declined := t.declined + 1 }
    return #[s!"{label}: declined as expected: {(e.render.take 160).toString}"]
  | .error e, none =>
    expect a false s!"{label}: declined with {e.render}, but the manifest expects it to compile"
    return #[]
  | .ok _, some d =>
    expect a false s!"{label}: compiled, but the manifest expects the decline {d.stage}: {d.code}"
    return #[]
  | .ok (cert, art), none =>
    let c ← Levels.assemble label cert art
    t.modify fun t => { t with compiled := t.compiled + 1 }
    runRoot a o native label r c t

def suite (a : Assert) (o : Options) (work : FilePath) : IO Unit := do
  let native : Option Rt.Native.Tools := o.cc.map fun cc => { cc, work }
  let t ← IO.mkRef ({} : Tally)
  IO.println "tests-corpus"
  let manifests := if o.manifests.isEmpty then families else o.manifests
  for path in manifests do
    let m ← Family.read path
    for f in m.fixtures do
      if !o.only.isEmpty && !o.only.contains f.name then continue
      for r in f.roots do
        if !o.roots.isEmpty && !o.roots.contains r.name then continue
        let before ← a.get
        let (lines, ms) ← timed (root a o native m f r t)
        IO.println s!"  {m.family}/{f.name}/{r.name}: {(← a.get) - before} assertions, {ms} ms"
        for l in lines do IO.println s!"    {l}"
        (← IO.getStdout).flush
  let t ← t.get
  IO.println s!"  {t.compiled} roots compiled, {t.declined} declined as expected; {t.cases} cases, \
    {t.runs} level runs{if native.isSome then s!", {t.native} native runs" else ""}; \
    {t.allowed} allowed resource failures"
  -- the middle end's budgets against every committed program (a full run only)
  if o.manifests.isEmpty && o.only.isEmpty && o.roots.isEmpty then
    let before ← a.get
    let (lines, ms) ← timed (Budget.survey a)
    IO.println s!"  middle-end budgets: {(← a.get) - before} assertions, {ms} ms"
    for l in lines do IO.println s!"    {l}"

/-- The middle end's and the backend's input for a root `produce` declines:
Anf after the middle end, Lir and Xv (as `ixcc --dump-ir` prints them),
recomputed by `produce`'s own steps up to selection. For diagnosing a decline
at allocation or later. -/
def dumpIR (inp : Input) : Except String String := do
  let cfg := ({} : Config).forInput inp
  let P := inp.program
  let (table, _, _) := IxCC.Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  let ann ← IxCC.Src.Relevance.annotate inp.env p0
  let (src, checked) ← match IxCC.Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error _ => throw "relevance rejects it"
  let (lam, _) ← match (IxCC.Lam.erase src checked).mapError Err.ofErase with
    | .ok r => pure r
    | .error e => throw e.render
  let trace ← IxCC.Anf.Pipeline.produce cfg.budgets lam
  let anf := ((trace.stages.getLast?).map (·.2)).getD default
  let fir ← (IxCC.Fir.lower anf).mapError fun e => (Err.ofFir e).render
  let C := IxCC.Cfg.lower (IxCC.Own.immortal fir)
  let lowered ← (IxCC.Rt.lower { names := cfg.names } C).mapError fun e => (Err.ofRt e).render
  let (xv, _) ← (IxCC.Xv.Select.run lowered.program).mapError fun e => (Err.ofSelect e).render
  return s!"== anf\n{anf.render}\n== lir\n{lowered.program.text}\n== xv\n{xv.text}"

/-- Survey mode: compile every root and print `compiled` or its
`stage: code`, with what the manifest expects (no assertions; for
reviewing a new family before recording its declines). -/
def survey (o : Options) : IO Unit := do
  let manifests := if o.manifests.isEmpty then families else o.manifests
  for path in manifests do
    let m ← Family.read path
    for f in m.fixtures do
      if !o.only.isEmpty && !o.only.contains f.name then continue
      let dir : FilePath := m.directory
      for r in f.roots do
        if !o.roots.isEmpty && !o.roots.contains r.name then continue
        let ((result : Except Err (Cert × Artifact)), ms) ← timed (compileRoot m f r)
        let got := match result with
          | .ok _ => "compiled"
          | .error e => s!"{e.stage.name}: {e.code}"
        let want := match r.decline with
          | some d => s!"{d.stage}: {d.code}"
          | none => "compiled"
        IO.println s!"{m.family}/{f.name}/{r.name}\t{got}\t(manifest: {want}{if got == want then "" else ", DIFFERS"})\t{ms} ms"
        if let .error e := result then
          IO.println s!"  {(e.render.take 300).toString}"
          if o.dump && [Stage.alloc, .stacking, .layout, .x86, .elf].contains e.stage then
            let inp ← ingressFile (dir / f.closure.path) (dir / f.equations.path) (r.name :: r.together)
            match dumpIR inp with
            | .ok text => IO.println text
            | .error m => IO.println s!"  (no dump: {m})"

/-- Observe mode: every case of every compiled root at Cfg, Lir, Xv, Xl and
(with `--cc`) natively, as tab-separated rows, with the manifest's
expectation and no assertion (for reviewing a new family's `fail`, `allow`
and `spurious` marks, and for tabulating a boundary family). -/
def observe (o : Options) (work : FilePath) : IO Unit := do
  let native : Option Rt.Native.Tools := o.cc.map fun cc => { cc, work }
  let manifests := if o.manifests.isEmpty then families else o.manifests
  IO.println "root\targs\tvalue\tfail\tspurious\tcfg\tlir\txv\txl\tnative"
  for path in manifests do
    let m ← Family.read path
    for f in m.fixtures do
      if !o.only.isEmpty && !o.only.contains f.name then continue
      for r in f.roots do
        if !o.roots.isEmpty && !o.roots.contains r.name then continue
        match ← compileRoot m f r with
        | .error e => IO.println s!"{r.name}\t-\t-\t-\t-\tdeclined {e.stage.name}: {e.code}"
        | .ok (cert, art) =>
          let c ← Levels.assemble r.name cert art
          let some root0 := c.art.roots.head? | continue
          let root := { root0 with ty := resultTy r root0.ty }
          let c := { c with art := { c.art with roots := root :: c.art.roots.drop 1 } }
          let exe ← native.mapM fun nt => link nt s!"observe_{r.name.replace "." "_"}" c.art.object root.symbol
          for cs in r.cases do
            let noWord := cs.args.any (· ≥ limit)
            let mut cols : Array String := #[]
            for level in ["cfg", "lir", "xv", "xl"] do
              if noWord || (level == "cfg" && cs.leanFails) then cols := cols.push "·"
              else
                let (out, obs) ← Levels.runLevel c level cs.args (caseRegion cs) (caseBudget cs)
                let out := if out == "ok" then "" else ((failure out).getD out) ++ " "
                cols := cols.push s!"{out}{(obs.map Rt.renderObs).getD ""}".trimAscii.toString
            let n ← match exe with
              | none => pure "·"
              | some exe =>
                match ← Rt.Native.run exe { region := nativeRegion cs, stack := nativeStack cs, ty := root.ty } [cs.args] with
                | [l] => pure (if l.status == 0 then l.obs.getD s!"w{l.value}"
                    else s!"status {l.status}{if l.init then " (cx_init)" else ""}")
                | _ => pure "?"
            IO.println s!"{r.name}\t{cs.args}\t{cs.value}\t{cs.fail.getD ""}\t{if cs.spurious then "spurious" else ""}\t\
              {"\t".intercalate cols.toList}\t{n}"
            (← IO.getStdout).flush

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--cc" :: cc :: rest => do return { (← parseOptions rest) with cc := some cc }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--only" :: n :: rest => do let o ← parseOptions rest; return { o with only := n :: o.only }
  | "--root" :: n :: rest => do let o ← parseOptions rest; return { o with roots := n :: o.roots }
  | "--no-machines" :: rest => do return { (← parseOptions rest) with machines := false }
  | "--progress" :: rest => do return { (← parseOptions rest) with progress := true }
  | "--survey" :: rest => do return { (← parseOptions rest) with survey := true }
  | "--dump" :: rest => do return { (← parseOptions rest) with dump := true }
  | "--observe" :: rest => do return { (← parseOptions rest) with observe := true }
  | arg :: rest =>
    if arg.startsWith "--" then throw s!"unknown argument {arg}"
    else do let o ← parseOptions rest; return { o with manifests := arg :: o.manifests }

/-- The large stack the big-step evaluators need (as `tests-src`). -/
def stackKb : Nat := IxCCTests.Src.Bench.deepStackKb

/-- Usage: `tests-corpus [MANIFEST…] [--cc CC] [--work DIR] [--only FIXTURE]…
[--root ROOT]… [--no-machines] [--progress] [--survey [--dump] | --observe]`. Without a manifest, every
registered family (`Corpus.families`). -/
def suiteMain (args : List String) : IO UInt32 := do
  -- re-run once with a large stack for the big-step evaluators
  if (← IO.getEnv "IXCC_CORPUS_CHILD").isNone then
    let self ← IO.appPath
    let env : Array (String × Option String) :=
      #[("LEAN_STACK_SIZE_KB", some (toString stackKb)), ("IXCC_CORPUS_CHILD", some "1")]
    let child ← IO.Process.spawn { cmd := self.toString, args := args.toArray, env := env }
    return ← child.wait
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-corpus: {e}"; return 2
  if o.survey then
    survey o
    return 0
  if o.observe then
    match o.work with
    | some work => IO.FS.createDirAll work; observe o work
    | none => IO.FS.withTempDir fun work => observe o work
    return 0
  let a ← IO.mkRef 0
  try
    match o.work with
    | some work => IO.FS.createDirAll work; suite a o work
    | none => IO.FS.withTempDir fun work => suite a o work
    IO.println s!"tests-corpus: {← a.get} assertions passed{if o.cc.isSome then ", native runs agree" else ""}"
    return 0
  catch e =>
    IO.eprintln s!"tests-corpus: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Corpus
