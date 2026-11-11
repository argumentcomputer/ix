import IxCCTests.Corpus.Manifest
import IxCCTests.Corpus.Budget
import IxCCTests.Pipeline.Levels
import IxCCTests.Recheck.RootShape
import IxCC.Anf.Print
import IxCC.Lir.Print
import IxCC.Xv.Print
import IxCCTests.Exe.Support

/-! The corpus suite: every root of every registered corpus family,
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
  manifest marks `machine`, since they step one instruction at a time),
  natively (with `--native`) as a test executable IxCC writes
  (`IxCCTests.Rt.Native`), and (with `--exe`) as a standalone executable
  (`ixcc compile --exe`), which must also agree with SrcEval, with ByteEval
  where the case fixes the layout both use, and with the test executable when
  it ran; a root outside the executables' fragment
  must be refused with `exe.params` or `exe.result`.

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
  /-- Run natively, as test executables IxCC writes. -/
  runNative : Bool := false
  work : Option FilePath := none
  manifests : List FilePath := []
  only : List String := []
  roots : List String := []
  machines : Bool := true
  progress : Bool := false
  survey : Bool := false
  dump : Bool := false
  observe : Bool := false
  /-- Also run every root of the executables' fragment as a standalone executable. -/
  exe : Bool := false

structure Tally where
  compiled : Nat := 0
  declined : Nat := 0
  cases : Nat := 0
  runs : Nat := 0
  native : Nat := 0
  exe : Nat := 0
  exeRefused : Nat := 0
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

/-- The readback type of an `enum` result of `n` constructors: one inductive
of `n` field-less constructors. The suite reads every result at the
compiler's readback type (`Recheck.rootTy`), which must be this one for an
`enum` root, compiled alone or not. -/
def enumTy (n : Nat) : Rt.Sig × Rt.FoTy := ({ inds := [List.replicate n []] }, .ind 0)

/-- The word levels' region and the machines' stack budget for a case. -/
def caseRegion (cs : Case) : Nat := cs.region.getD IxCCTests.Rt.defaultSize
def caseBudget (cs : Case) : Lir.Word :=
  match cs.stack with
  | some s => UInt64.ofNat (s - 4096)
  | none => IxCCTests.Rt.defaultBudget

/-- The native runs' region and stack for a case. -/
def nativeRegion (cs : Case) : Nat := cs.region.getD (1 <<< 24)
def nativeStack (cs : Case) : Nat := cs.stack.getD (1 <<< 28)

/-- One root's cases as a standalone executable (`ixcc compile --exe`): one
executable per case region and stack, refused for a root outside the
executables' fragment or a layout outside the driver contract (a region under
4 KiB). Each run must give what the manifest requires of native code, and
agree with IxCC's own evaluators where they ran on the case: SrcEval's value
when the executable returned one, and ByteEval's outcome and value when the
case fixes the region and the stack both use. With `--native`, it must give
the test executable's outcome and observation too. -/
def runExe (a : Assert) (work : FilePath) (label : String) (r : Root) (c : Levels.Compiled)
    (src : Array (Option String)) (bytes : Array (Option (String × String)))
    (driver : Array (Option (String × String))) (t : IO.Ref Tally) : IO (Array String) := do
  match IxCC.Exe.fragment c.art with
  | .error e =>
    expect a (["exe.params", "exe.result"].contains e.code) s!"{label}: executable refused with {e.render}"
    t.modify fun t => { t with exeRefused := t.exeRefused + 1 }
    return #[s!"  as an executable: refused ({e.code})"]
  | .ok _ =>
    let groups := r.cases.foldl (init := ([] : List (Nat × Nat))) fun gs cs =>
      let g := (nativeRegion cs, nativeStack cs)
      if gs.contains g then gs else gs ++ [g]
    let mut n := 0
    let mut skipped := 0
    let mut ms := 0
    for (region, stack) in groups do
      let layout : IxCC.X86.Exe.Layout := { stack, region }
      let css := r.cases.zipIdx.filter fun (cs, _) => (nativeRegion cs, nativeStack cs) == (region, stack)
      if !layout.check then
        skipped := skipped + css.length
        continue
      let exe := work / s!"exe_{label.replace "/" "_"}_{region}_{stack}"
      match ← IxCCTests.Exe.build exe c.art layout with
      | .error e => expect a false s!"{label}: no executable for --region {region} --stack {stack}: {e.render}"
      | .ok () =>
        for (cs, i) in css do
          let some want := cs.expect r | continue
          let (run, ms') ← timed (IxCCTests.Exe.run exe (cs.args.map toString))
          ms := ms + ms'
          n := n + 1
          let outcome := run.outcome
          let obs := run.obs
          let l := s!"{label} {cs.args} as an executable (--region {region} --stack {stack})"
          expect a (outcome == "ok" || outcome.startsWith "status")
            s!"{l}: exit {run.code}, stderr {run.stderr}"
          if ← judge a l "native" want cs.allow outcome obs then
            t.modify fun t => { t with allowed := t.allowed + 1 }
          if outcome == "ok" then
            if let some (some s) := src[i]? then
              expect a (obs == s) s!"{l}: prints {obs}, SrcEval reads back {s}"
          if let some (some (bo, bobs)) := bytes[i]? then
            if outcome == "ok" && bo == "ok" then
              expect a (obs == bobs) s!"{l}: prints {obs}, ByteEval reads back {bobs}"
            else if cs.region.isSome && cs.stack.isSome then
              expect a (failure outcome == failure bo) s!"{l}: {outcome}, ByteEval {bo}"
          if let some (some (co, cobs)) := driver[i]? then
            expect a (outcome == co && obs == cobs) s!"{l}: {outcome} {obs}, the test executable {co} {cobs}"
    t.modify fun t => { t with exe := t.exe + n }
    return #[s!"  as an executable: {n} cases agree ({ms} ms{if skipped > 0 then s!", {skipped} skipped: a layout outside the driver contract" else ""})"]

/-- Every case of one compiled root at every level, natively and as an
executable. -/
def runRoot (a : Assert) (o : Options) (native : Option Rt.Native.Tools) (work : FilePath) (label : String) (r : Root)
    (c : Levels.Compiled) (t : IO.Ref Tally) : IO (Array String) := do
  let levels := Levels.levelNames c
  let some root := c.art.roots.head? | throw (IO.userError s!"{label}: no root")
  if r.result == "enum" then
    expect a (root.ty == r.ctors.map enumTy)
      s!"{label}: readback type {repr root.ty}, expected {repr (r.ctors.map enumTy)}"
  expectEq a root.params r.params s!"{label}: parameters"
  let mut times : Array (String × Nat) := levels.toArray.map (·, 0)
  -- SrcEval's observation and ByteEval's outcome per case, for the executable
  let mut srcObs : Array (Option String) := #[]
  let mut bytesOut : Array (Option (String × String)) := #[]
  for cs in r.cases do
    let some want := cs.expect r | throw (IO.userError s!"{label} {cs.args}: no expectation")
    let src := cs.sourceObs r
    let noWord := cs.args.any (· ≥ limit)
    let mut caseSrc := none
    let mut caseBytes := none
    for (level, i) in levels.zipIdx do
      -- the source levels run on Lean's runtime `Nat`, which fails where its interpreter does
      let run := if sourceLevel level then !noWord && src.isSome && !cs.leanFails
        else if wordLevel level then !noWord
        else o.machines && (cs.machine || noWord) && cs.args.all (· < 2 ^ 64)
      if !run then continue
      let ((outcome, obs), ms) ← timed (Levels.runLevel c level cs.args (caseRegion cs) (caseBudget cs))
      let obs := (obs.map Rt.renderObs).getD "-"
      let l := s!"{label} {cs.args} at {level}"
      if level == "src" && outcome == "ok" then caseSrc := some obs
      if level == "bytes" then caseBytes := some (outcome, obs)
      if sourceLevel level then
        expect a (outcome == "ok") s!"{l}: {outcome}, expected ok {src.getD ""}"
        expect a (some obs == src) s!"{l}: reads back {obs}, expected {src.getD ""}"
      else if ← judge a l level want cs.allow outcome obs then
        t.modify fun t => { t with allowed := t.allowed + 1 }
      times := times.modify i fun (n, ms') => (n, ms' + ms)
      t.modify fun t => { t with runs := t.runs + 1 }
      if o.progress then IO.eprintln s!"      {l}: {outcome} {obs} ({ms} ms)"
    srcObs := srcObs.push caseSrc
    bytesOut := bytesOut.push caseBytes
    t.modify fun t => { t with cases := t.cases + 1 }
  let mut out := #[s!"{label}: {r.cases.length} cases, {levels.length} levels (ms: \
    {", ".intercalate (times.toList.filter (·.2 > 0) |>.map fun (l, ms) => s!"{l} {ms}")})"]
  -- the test executable's outcome and observation per case, for the standalone executable
  let mut driverOut : Array (Option (String × String)) := Array.replicate r.cases.length none
  if let some nt := native then
    let exe ← link nt s!"corpus_{label.replace "/" "_"}" c.art.object root.symbol
    -- one run per region and stack; a non-`Nat` result's object area is
    -- dumped, so `Rt.readback` of the dump is compared with the independent
    -- decoder's observation
    let groups := r.cases.foldl (init := ([] : List (Nat × Nat))) fun gs cs =>
      let g := (nativeRegion cs, nativeStack cs)
      if gs.contains g then gs else gs ++ [g]
    let mut ms := 0
    let mut n := 0
    for (region, stack) in groups do
      let css := r.cases.zipIdx.filter fun (cs, _) => (nativeRegion cs, nativeStack cs) == (region, stack)
      let dump := r.result != "nat"
      let (lines, ms') ← timed (Rt.Native.run exe { region, stack, ty := root.ty, dump } (css.map (·.1.args)))
      ms := ms + ms'
      n := n + lines.length
      for ((cs, ci), ln) in css.zip lines do
        let some want := cs.expect r | continue
        let l := s!"{label} {cs.args} natively{if (region, stack) == (1 <<< 24, 1 <<< 28) then "" else s!" (--region {region} --stack {stack})"}"
        expect a ln.ok s!"{l}: registers not restored"
        let outcome := if ln.status == 0 then "ok" else s!"status {ln.status}"
        if ← judge a l "native" want cs.allow outcome (ln.obs.getD "-") then
          t.modify fun t => { t with allowed := t.allowed + 1 }
        driverOut := driverOut.set! ci (some (outcome, ln.obs.getD "-"))
        -- `Rt.readback` of the native word (and object area) is the independent decoder's
        if ln.status == 0 && !ln.init then
          if let some (sig, ty) := root.ty then
            let mem : X86.Memory := match ln.dump with
              | some d => d.memory region
              | none => { bytes := fun _ => 0, readable := fun _ => false, writable := fun _ => false }
            let lean := (Rt.readback sig (region / 8) mem ty ln.value).map Rt.renderObs
            expect a (lean == ln.obs) s!"{l}: Rt.readback gives {lean}, the independent decoder {ln.obs}"
    t.modify fun t => { t with native := t.native + n }
    out := out.push s!"  natively: {n} cases agree ({ms} ms{if groups.length > 1 then s!", {groups.length} runs" else ""})"
  if o.exe then
    out := out ++ (← runExe a work label r c srcObs bytesOut driverOut t)
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
def root (a : Assert) (o : Options) (native : Option Rt.Native.Tools) (work : FilePath) (m : Family) (f : Fixture) (r : Root)
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
    runRoot a o native work label r c t

def suite (a : Assert) (o : Options) (work : FilePath) : IO Unit := do
  let native : Option Rt.Native.Tools := if o.runNative then some { work } else none
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
        let (lines, ms) ← timed (root a o native work m f r t)
        IO.println s!"  {m.family}/{f.name}/{r.name}: {(← a.get) - before} assertions, {ms} ms"
        for l in lines do IO.println s!"    {l}"
        (← IO.getStdout).flush
  let t ← t.get
  IO.println s!"  {t.compiled} roots compiled, {t.declined} declined as expected; {t.cases} cases, \
    {t.runs} level runs{if native.isSome then s!", {t.native} native runs" else ""}\
    {if o.exe then s!", {t.exe} executable runs ({t.exeRefused} roots outside the executables' fragment)" else ""}; \
    {t.allowed} allowed resource failures"
  -- the middle end's budgets against every committed program (a full run only)
  if o.manifests.isEmpty && o.only.isEmpty && o.roots.isEmpty then
    let before ← a.get
    let (lines, ms) ← timed (Budget.survey a)
    IO.println s!"  middle-end budgets: {(← a.get) - before} assertions, {ms} ms"
    for l in lines do IO.println s!"    {l}"
    -- roots returning each constructor of their result type, compiled alone
    if let some nt := native then
      let before ← a.get
      let (lines, ms) ← timed (IxCCTests.Recheck.RootShape.nativeAlone a nt)
      IO.println s!"  result constructors of roots compiled alone, natively: {(← a.get) - before} \
        assertions, {ms} ms"
      for l in lines do IO.println s!"    {l}"

/-- The middle end's and the backend's input for a root `produce` declines:
Anf after the middle end and the closures step, Lir and Xv (as `ixcc
--dump-ir` prints them),
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
  let pre := ((trace.stages.getLast?).map (·.2)).getD default
  -- the closures step, as the producer runs it after the middle end
  let anf ← (closuresOf src pre).mapError (·.render)
  let fir ← (IxCC.Fir.lower anf).mapError fun e => (Err.ofFir e).render
  let C := IxCC.Cfg.lower (IxCC.Own.immortal fir)
  let lowered ← (IxCC.Rt.lower { names := cfg.names } C).mapError fun e => (Err.ofRt e).render
  let (xv, _) ← (IxCC.Xv.Select.run lowered.program).mapError fun e => (Err.ofSelect e).render
  return s!"== anf\n{anf.render}\n== lir\n{lowered.program.text}\n== xv\n{xv.text}"

/-- What the closures step made of a compiled root's program: unchanged, or
its closure keys `K` (P8's constructor rows), its dispatchers `M`, and the
back end's work on their switches (`Anf.Defun.dispatchWork`) against the
budget past which P8 refuses (`Anf.maxBackWork`), with the most keys that
budget admits at this `M` and table. -/
def closuresLine (cert : Cert) (art : Artifact) : String :=
  match Anf.Pipeline.run cert.mid art.lam with
  | .error _ => "closures step: the middle end does not replay"
  | .ok pre =>
    if pre.beq art.anf then "closures step: the program unchanged"
    else
      let K := art.anf.ctors.length - pre.ctors.length
      let M := (art.anf.globalList.filter fun (_, g) => g.key matches .dispatch _).length
      let entries := (art.anf.globalList.filter fun (_, g) => g.key matches .entry ..).length
      let w := Anf.Defun.dispatchWork pre M K
      let kmax := (List.range 4096).foldl (fun k _ =>
        if M > 0 && Anf.Defun.dispatchWork pre M (k + 1) ≤ Anf.maxBackWork then k + 1 else k) K
      s!"closures step: {entries} entries, {K} closure keys, {M} dispatchers, dispatch work {w} \
        ({w * 100 / Anf.maxBackWork}% of {Anf.maxBackWork}; at most {kmax} keys at {M} dispatchers)"

/-- Survey mode: compile every root and print `compiled` or its
`stage: code`, with what the manifest expects, and for a compiled root what
the closures step made of it (`closuresLine`) (no assertions; for reviewing a
new family before recording its declines). -/
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
        if let .ok (cert, art) := result then IO.println s!"  {closuresLine cert art}"
        if let .error e := result then
          IO.println s!"  {(e.render.take 300).toString}"
          if o.dump && [Stage.alloc, .stacking, .layout, .x86, .elf].contains e.stage then
            let inp ← ingressFile (dir / f.closure.path) (dir / f.equations.path) (r.name :: r.together)
            match dumpIR inp with
            | .ok text => IO.println text
            | .error m => IO.println s!"  (no dump: {m})"

/-- Observe mode: every case of every compiled root at Cfg, Lir, Xv, Xl and
(with `--native`) natively, as tab-separated rows, with the manifest's
expectation and no assertion (for reviewing a new family's `fail`, `allow`
and `spurious` marks, and for tabulating a boundary family). -/
def observe (o : Options) (work : FilePath) : IO Unit := do
  let native : Option Rt.Native.Tools := if o.runNative then some { work } else none
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
          let some root := c.art.roots.head? | continue
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
  | "--native" :: rest => do return { (← parseOptions rest) with runNative := true }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--only" :: n :: rest => do let o ← parseOptions rest; return { o with only := n :: o.only }
  | "--root" :: n :: rest => do let o ← parseOptions rest; return { o with roots := n :: o.roots }
  | "--no-machines" :: rest => do return { (← parseOptions rest) with machines := false }
  | "--progress" :: rest => do return { (← parseOptions rest) with progress := true }
  | "--survey" :: rest => do return { (← parseOptions rest) with survey := true }
  | "--dump" :: rest => do return { (← parseOptions rest) with dump := true }
  | "--observe" :: rest => do return { (← parseOptions rest) with observe := true }
  | "--exe" :: rest => do return { (← parseOptions rest) with exe := true }
  | arg :: rest =>
    if arg.startsWith "--" then throw s!"unknown argument {arg}"
    else do let o ← parseOptions rest; return { o with manifests := arg :: o.manifests }

/-- The large stack the big-step evaluators need (as `tests-src`). -/
def stackKb : Nat := IxCCTests.Src.Bench.deepStackKb

/-- Usage: `tests-corpus [MANIFEST…] [--native] [--work DIR] [--only FIXTURE]…
[--root ROOT]… [--no-machines] [--progress] [--exe] [--survey [--dump] | --observe]`. Without a manifest, every
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
    IO.println s!"tests-corpus: {← a.get} assertions passed{if o.runNative then ", native runs agree" else ""}{← IxCCTests.Rt.Native.agreement}"
    return 0
  catch e =>
    IO.eprintln s!"tests-corpus: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Corpus
