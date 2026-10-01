import CompilatrixTests.Corpus.Run
import CompilatrixTests.Own.Verdicts
import CompilatrixTests.Own.Strip
import CompilatrixTests.Own.Counters
import Compilatrix.Fir.Print
import Compilatrix.Cfg.Print

/-! # The ownership and usage-annotation suite, Phase 1 part (MT.7)

`lake exe tests-own` over `fixtures/ownership` (design:
`plans/fixtures/ownership-suite.md`). Each annotated program ix accepts is a
fixture of the `ownership` corpus family (`corpus.json`, format
`compilatrix/corpus/1`) beside its plain twin; ix's verdicts on every
annotated source are in `verdicts.json`. Parts:

* **`strip`**: every plain twin is its annotated source with the contract
  syntax deleted (`Own.Strip`), so the twins differ only in contracts.
* **`fixtures`**: `corpus check` of the family (hashes, sidecars, censuses
  reproduced, cases), and the verdicts checked against the sources and the
  manifest (`Own.Verdicts.check`).
* **`equiv`**: every root of every fixture at every level the pipeline
  checks (SrcEval, Lam, Anf after each step, Fir, Own, Cfg, Lir, Xv, Xl, the
  typed x86 machine and ByteEval on `machine` cases) and natively with
  `--cc`, against Lean 4.34's interpreter on the annotated source and on its
  twin (`tests-corpus`'s `root`); the twins' recorded cases and values are
  equal; and per root the twins' code: equal Fir, equal Cfg and an equal
  object, as `twinCode` records.
* **`erasure`**: `0` binders, proof arguments, `Subtype` and `Decidable`
  cost nothing: no `alloc` in the Cfg of the scalar fixtures, and the work
  of an erased argument (OS-03b's `cube`) is not in the code.
* **`counters`**: the Cfg stepper (`Own.Counters`) on every root and case
  with a word: its result is `Cfg.run`'s; annotated and plain twins count
  the same; no cell where none is expected; OS-16's `2n` cells, and with
  `--cc` its `48n` bump bytes natively; every reference-counting counter 0
  (Phase 1 has no such forms).
* **`cx1`**: CX-1, `0` binders in the relevance annotator: OS-03 compiles;
  the same program built by writing `ignoreFirst`'s parameter erased into
  the plain twin compiles to OS-03's object; and writing a *used* parameter
  erased (OS-01's `n`) is rejected with `relevance: relevance-C1`. -/

namespace CompilatrixTests.Own.Suite

open Compilatrix Compilatrix.Recheck CompilatrixTests.Src CompilatrixTests.Pipeline
open CompilatrixTests.Corpus (Family Fixture Root)
open System

def manifest : FilePath := "fixtures/ownership/corpus.json"

def parts : List String := ["strip", "fixtures", "equiv", "erasure", "counters", "cx1"]

structure Options where
  cc : Option String := none
  work : Option FilePath := none
  only : List String := []

def Options.runs (o : Options) (part : String) : Bool := o.only.isEmpty || o.only.contains part

/-- How a twin pair's code compares, per root (reviewed): equal Fir, equal
Cfg, equal object bytes. -/
structure TwinCode where
  fir : Bool := true
  cfg : Bool := true
  object : Bool := true

/-- An IR rendering with its source constants (`const N`, ingress's dense
indices, which depend on the closure's layout) renumbered by first
appearance, so twins compare up to constant numbering. -/
def renumberConsts (s : String) : String := Id.run do
  let pieces := s.splitOn "const "
  let mut seen : Array String := #[]
  let mut out := pieces.headD ""
  for p in pieces.drop 1 do
    let digits := String.ofList (p.toList.takeWhile Char.isDigit)
    let rest := String.ofList (p.toList.drop digits.length)
    if digits.isEmpty then out := out ++ "const " ++ p
    else
      let i := (seen.findIdx? (· == digits)).getD seen.size
      if i == seen.size then seen := seen.push digits
      out := out ++ s!"const #{i}" ++ rest
  return out

/-- An object with every occurrence of the root's content address zeroed:
the object's provenance note records it (`compilatrix/x86-object-provenance/1`),
and contracts are part of the address, so twins' objects differ there and
only there. -/
def maskAddr (obj addr : ByteArray) : ByteArray := Id.run do
  let mut out := obj
  if obj.size < addr.size then return out
  for i in [0:obj.size - addr.size + 1] do
    if obj.extract i (i + addr.size) == addr then
      for j in [0:addr.size] do out := out.set! (i + j) 0
  return out

/-- The reviewed expectation of each pair (annotated fixture, root). -/
def twinCode (_fixture _root : String) : TwinCode := {}

/-- Fixtures whose code must allocate nothing (scalar programs: erased
proofs, `Subtype`, `Decidable`, contracts on immediates). -/
def noAlloc (fixture : String) : Bool := fixture != "OS16-plain"

/-- OS-16: the hand-derived allocation of `entry n` in Phase 1 (immortal
cells, nothing freed or reused): `build` conses `n` cells and `revAcc` `n`
more; a cons cell is a header and two fields, 24 bytes. -/
def os16Cells (n : Nat) : Nat := 2 * n
def os16Bytes (n : Nat) : Nat := 48 * n
def os16Sizes : List Nat := [10, 100, 1000]

def fixtureOf (m : Family) (name : String) : IO Fixture := do
  let some f := m.fixtures.find? (·.name == name) | throw (IO.userError s!"{manifest}: no fixture {name}")
  return f

/-- The annotated fixtures with their twins, from the verdicts. -/
def pairs (m : Family) : IO (List (Fixture × Fixture)) := do
  let v ← Verdicts.File.read
  v.entries.filterMapM fun e => do
    match e.fixture, e.twin with
    | some a, some t => return some (← fixtureOf m a, ← fixtureOf m t)
    | _, _ => return none

def compileRoot (m : Family) (f : Fixture) (r : String) : IO (Cert × Artifact) := do
  let dir : FilePath := m.directory
  let inp ← ingressFile (dir / f.closure.path) (dir / f.equations.path) [r]
  compileIn s!"{f.name}/{r}" inp

/-! ## Parts -/

def strip (a : Assert) (m : Family) : IO (Array String) := do
  let ps ← pairs m
  for (ann, plain) in ps do
    let src ← IO.FS.readFile ((m.sourceRoot : FilePath) / ann.source.path)
    let twin ← IO.FS.readFile ((m.sourceRoot : FilePath) / plain.source.path)
    expect a (Strip.strip src == twin) s!"{plain.source.path} is not {ann.source.path} with its contracts deleted"
  return #[s!"strip: {ps.length} plain twins are their annotated sources without contracts"]

def fixtures (a : Assert) : IO (Array String) := do
  CompilatrixTests.Corpus.check {} [manifest] false
  expect a true ""
  let (n, acc, rej) ← Verdicts.check
  expect a true ""
  return #[s!"verdicts: {n} annotated sources, {acc} accepted by ix (frozen in {manifest}), {rej} rejected"]

def equiv (a : Assert) (o : Options) (work : FilePath) (m : Family) : IO (Array String) := do
  let native : Option Rt.Native.Tools := o.cc.map fun cc => { cc, work }
  let t ← IO.mkRef ({} : CompilatrixTests.Corpus.Tally)
  let co : CompilatrixTests.Corpus.Options := {}
  let mut out := #[]
  for f in m.fixtures do
    for r in f.roots do
      let before ← a.get
      let (lines, ms) ← timed (CompilatrixTests.Corpus.root a co native m f r t)
      out := out.push s!"  {f.name}/{r.name}: {(← a.get) - before} assertions, {ms} ms"
      out := out ++ lines.map ("    " ++ ·)
  let tl ← t.get
  out := out.push s!"equiv: {tl.compiled} roots compiled, {tl.cases} cases, {tl.runs} level runs, \
    {tl.native} native runs, {tl.allowed} allowed resource failures"
  -- the twins: the same cases and values, and the code `twinCode` records
  let mut same := 0
  for (ann, plain) in ← pairs m do
    expect a (ann.roots.map (·.name) == plain.roots.map (·.name)) s!"{ann.name}: roots differ from {plain.name}'s"
    for (ra, rp) in ann.roots.zip plain.roots do
      expect a (ra.cases.map (fun c => (c.args, c.value)) == rp.cases.map (fun c => (c.args, c.value)))
        s!"{ann.name}/{ra.name}: the interpreter's values differ from the plain twin's"
      let (_, aa) ← compileRoot m ann ra.name
      let (_, ap) ← compileRoot m plain rp.name
      let want := twinCode ann.name ra.name
      let fir := renumberConsts aa.fir.render == renumberConsts ap.fir.render
      let cfg := renumberConsts aa.cfg.render == renumberConsts ap.cfg.render
      let obj := match aa.roots.head?, ap.roots.head? with
        | some x, some y => maskAddr aa.object x.addr.hash == maskAddr ap.object y.addr.hash
        | _, _ => false
      expect a (fir == want.fir) s!"{ann.name}/{ra.name}: Fir {if fir then "equal" else "differs"} \
        (expected {if want.fir then "equal" else "different"})\n{aa.fir.render}\n-- plain --\n{ap.fir.render}"
      expect a (cfg == want.cfg) s!"{ann.name}/{ra.name}: Cfg {if cfg then "equal" else "differs"}\n{aa.cfg.render}\n-- plain --\n{ap.cfg.render}"
      expect a (obj == want.object) s!"{ann.name}/{ra.name}: object {if obj then "equal" else "differs"}"
      if fir && cfg && obj then same := same + 1
  out := out.push s!"equiv: {same} annotated roots compile to the plain twin's Fir, Cfg and object"
  return out

def erasure (a : Assert) (m : Family) : IO (Array String) := do
  let mut n := 0
  for f in m.fixtures do
    for r in f.roots do
      let (_, art) ← compileRoot m f r.name
      if noAlloc f.name then
        expectEq a (Counters.staticAllocs art.cfg) 0 s!"{f.name}/{r.name}: alloc in the Cfg\n{art.cfg.render}"
        n := n + 1
  -- an erased argument's work is not done: OS-03b passes `cube n` erased
  let (_, art) ← compileRoot m (← fixtureOf m "OS03b-annotated") "entry"
  let text := art.fir.render
  expect a (!(text.splitOn "natMul").length > 1) s!"OS03b-annotated: the erased `cube n` is computed\n{text}"
  return #[s!"erasure: {n} scalar roots allocate nothing in Cfg; OS-03b's erased `cube n` is not computed"]

/-- Every case with a word, through the Cfg stepper. -/
def counters (a : Assert) (o : Options) (work : FilePath) (m : Family) : IO (Array String) := do
  let clock := 1 <<< 24
  let countsOf := fun (art : Artifact) (args : List Nat) => do
    let some fn := art.cfg.exports.head? | throw (IO.userError "no Cfg root")
    pure (Counters.sameAsRun .immortal art.cfg clock fn (args.map fun n => .lit (.nat n)))
  let mut runs := 0
  let mut table : Array (String × Counters.Counts) := #[]
  for f in m.fixtures do
    for r in f.roots do
      let (_, art) ← compileRoot m f r.name
      for c in r.cases do
        if c.args.any (· ≥ CompilatrixTests.Corpus.limit) then continue
        let (same, k) ← countsOf art c.args
        let l := s!"{f.name}/{r.name} {c.args}"
        expect a same s!"{l}: the stepper's result is not Cfg.run's"
        expect a (k.inc + k.dec + k.isShared + k.takeUnique + k.reuseHit + k.reuseMiss == 0)
          s!"{l}: a reference-counting event in Phase 1: {k.render}"
        if noAlloc f.name then
          expect a (k.cells == 0 && k.allocInstrs == 0) s!"{l}: allocates: {k.render}"
        table := table.push (l, k)
        runs := runs + 1
  -- annotated and plain twins count the same
  let mut pairsSame := 0
  for (ann, plain) in ← pairs m do
    for (ra, rp) in ann.roots.zip plain.roots do
      for (ca, cp) in ra.cases.zip rp.cases do
        let ka := table.find? (·.1 == s!"{ann.name}/{ra.name} {ca.args}")
        let kp := table.find? (·.1 == s!"{plain.name}/{rp.name} {cp.args}")
        match ka, kp with
        | some (_, x), some (_, y) =>
          expect a (x == y) s!"{ann.name}/{ra.name} {ca.args}: counts differ from the plain twin's\n  {x.render}\n  {y.render}"
          pairsSame := pairsSame + 1
        | none, none => pure ()
        | _, _ => expect a false s!"{ann.name}/{ra.name} {ca.args}: counted on one twin only"
  -- OS-16: 2n cells in Cfg, and 48n bump bytes natively
  let f16 ← fixtureOf m "OS16-plain"
  let (_, art) ← compileRoot m f16 "entry"
  let mut os16 := #[]
  for n in os16Sizes do
    let (same, k) ← countsOf art [n]
    expect a same s!"OS16-plain/entry [{n}]: the stepper's result is not Cfg.run's"
    expectEq a k.cells (os16Cells n) s!"OS16-plain/entry [{n}]: cells ({k.render})"
    expectEq a k.peakLive (os16Cells n) s!"OS16-plain/entry [{n}]: peak live cells"
    os16 := os16.push s!"n = {n}: {k.cells} cells"
  if let some cc := o.cc then
    let some root := art.roots.head? | throw (IO.userError "OS16: no root")
    let exe ← link { cc, work } "own_os16" art.object root.symbol
    let lines ← Rt.Native.run exe { dump := true, ty := root.ty } (os16Sizes.map ([·]))
    for (n, ln) in os16Sizes.zip lines do
      let some d := ln.dump | throw (IO.userError s!"OS16 [{n}]: no dump")
      expectEq a ln.status 0 s!"OS16 [{n}] natively: status"
      expectEq a (d.bump - d.start).toNat (os16Bytes n) s!"OS16 [{n}] natively: bump bytes"
      os16 := os16.push s!"n = {n}: {(d.bump - d.start).toNat} bytes natively"
    -- and nothing for the scalar fixtures
    for f in m.fixtures do
      if !noAlloc f.name then continue
      for r in f.roots do
        let (_, art) ← compileRoot m f r.name
        let some root := art.roots.head? | throw (IO.userError s!"{f.name}: no root")
        let exe ← link { cc, work } s!"own_{f.name}_{r.name}" art.object root.symbol
        let cases := (r.cases.filter fun c => c.args.all (· < CompilatrixTests.Corpus.limit)).map (·.args)
        let lines ← Rt.Native.run exe { dump := true, ty := root.ty } cases
        for (args, ln) in cases.zip lines do
          let some d := ln.dump | throw (IO.userError s!"{f.name}/{r.name} {args}: no dump")
          expectEq a (d.bump - d.start).toNat 0 s!"{f.name}/{r.name} {args} natively: bump bytes"
  return #[s!"counters: {runs} Cfg runs stepped and equal to Cfg.run, {pairsSame} annotated runs count as \
    their twins; OS-16 {", ".intercalate os16.toList}"]

/-- The constant a root's value applies: `entry := λ n. g …`. -/
def calleeOf (p : Src.Program) (root : Src.CId) : Option Src.CId := do
  let .defn _ _ _ _ v ← p.decl? root | none
  let (_, body) := v.lams
  match body.spine.1 with
  | .const c _ => some c
  | _ => none

/-- Write parameter `i` of `c` erased, in its Π type and its λ value. -/
def eraseParam (p : Src.Program) (c : Src.CId) (i : Nat) : Option Src.Program := do
  let .defn k s n ty v ← p.decl? c | none
  let rec onPi : Nat → Src.Term → Src.Term
    | 0, .pi b r d t => .pi { b with contract := .erased } r d t
    | j + 1, .pi b r d t => .pi b r d (onPi j t)
    | _, t => t
  let rec onLam : Nat → Src.Term → Src.Term
    | 0, .lam b d t => .lam { b with contract := .erased } d t
    | j + 1, .lam b d t => .lam b d (onLam j t)
    | _, t => t
  return p.setDecl c (.defn k s n (onPi i ty) (onLam i v))

def cx1 (a : Assert) (m : Family) : IO (Array String) := do
  let dir : FilePath := m.directory
  let input := fun (name : String) => do
    let f ← fixtureOf m name
    ingressFile (dir / f.closure.path) (dir / f.equations.path) ["entry"]
  -- the annotated OS-03 compiles (relevance-C0 before CX-1)
  let inp3 ← input "OS03-annotated"
  let (_, art3) ← compileIn "OS03-annotated" inp3
  expect a true ""
  -- the plain twin with ignoreFirst's first parameter written erased: OS-03's object
  let inpP ← input "OS03-plain"
  let some root := inpP.program.roots.head? | throw (IO.userError "OS03-plain: no root")
  let some g := calleeOf inpP.program root.2 | throw (IO.userError "OS03-plain: entry calls no constant")
  let some p' := eraseParam inpP.program g 0 | throw (IO.userError "OS03-plain: ignoreFirst is not a definition")
  match compileInput {} { inpP with program := p' } with
  | .ok (_, art) =>
    let same := match art.roots.head?, art3.roots.head? with
      | some x, some y => maskAddr art.object x.addr.hash == maskAddr art3.object y.addr.hash
      | _, _ => false
    expect a same "OS03-plain with `0 _n` written: not OS-03's object (up to the root's address)"
  | .error e => expect a false s!"OS03-plain with `0 _n` written: {e.render}"
  -- a used parameter written erased: OS-01's `pick (_h : True) (n : Nat) := n + 1`, `n` erased
  let inp1 ← input "OS01-plain"
  let some root := inp1.program.roots.head? | throw (IO.userError "OS01-plain: no root")
  let some g := calleeOf inp1.program root.2 | throw (IO.userError "OS01-plain: entry calls no constant")
  let some p' := eraseParam inp1.program g 1 | throw (IO.userError "OS01-plain: pick is not a definition")
  let neg := match compileInput {} { inp1 with program := p' } with
    | .ok _ => "compiled"
    | .error e => s!"{e.stage.name}: {e.code}"
  expectEq a neg "relevance: relevance-C1" "OS01-plain with `0 n` written on a used n"
  return #["cx1: OS-03 compiles; the plain twin with `0 _n` written compiles to OS-03's object; \
    a used `0 n` is rejected with relevance: relevance-C1"]

def suite (a : Assert) (o : Options) (work : FilePath) : IO Unit := do
  IO.println "tests-own"
  let m ← Family.read manifest
  let run := fun (part : String) (x : IO (Array String)) => do
    if o.runs part then
      let before ← a.get
      let (lines, ms) ← timed x
      IO.println s!"  {part}: {(← a.get) - before} assertions, {ms} ms"
      for l in lines do IO.println s!"    {l}"
      (← IO.getStdout).flush
  run "strip" (strip a m)
  run "fixtures" (fixtures a)
  run "equiv" (equiv a o work m)
  run "erasure" (erasure a m)
  run "counters" (counters a o work m)
  run "cx1" (cx1 a m)

def usage : String :=
  "usage: tests-own [--cc CC] [--work DIR] [--only PART]…   (parts: " ++ ", ".intercalate parts ++ ")\n" ++
  "       tests-own verdicts --ix IX [--ix-path DIR]… [--work DIR]   (manual: rebuild verdicts.json)"

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--cc" :: cc :: rest => do return { (← parseOptions rest) with cc := some cc }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--only" :: p :: rest => do
    unless parts.contains p do throw s!"unknown part {p}"
    let o ← parseOptions rest; return { o with only := p :: o.only }
  | arg :: _ => throw s!"unknown argument {arg}\n{usage}"

def verdictsMain (args : List String) : IO UInt32 := do
  let rec parse (t : CompilatrixTests.Corpus.Tools) : List String → Except String CompilatrixTests.Corpus.Tools
    | [] => .ok t
    | "--ix" :: p :: rest => parse { t with ix := some p } rest
    | "--ix-path" :: p :: rest => parse { t with ixPath := t.ixPath ++ [p] } rest
    | "--work" :: p :: rest => parse { t with work := p } rest
    | a :: _ => .error s!"unknown argument {a}\n{usage}"
  match parse { work := "plans/ownership/work" } args with
  | .error e => IO.eprintln e; return 2
  | .ok t =>
    try Verdicts.rebuild t; return 0
    catch e => IO.eprintln s!"tests-own verdicts: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  if let "verdicts" :: rest := args then return ← verdictsMain rest
  -- re-run once with a large stack for the big-step evaluators (as tests-corpus)
  if (← IO.getEnv "COMPILATRIX_OWN_CHILD").isNone then
    let self ← IO.appPath
    let env : Array (String × Option String) :=
      #[("LEAN_STACK_SIZE_KB", some (toString CompilatrixTests.Corpus.stackKb)), ("COMPILATRIX_OWN_CHILD", some "1")]
    let child ← IO.Process.spawn { cmd := self.toString, args := args.toArray, env := env }
    return ← child.wait
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-own: {e}"; return 2
  let a ← IO.mkRef 0
  try
    match o.work with
    | some work => IO.FS.createDirAll work; suite a o work
    | none => IO.FS.withTempDir fun work => suite a o work
    IO.println s!"tests-own: {← a.get} assertions passed{if o.cc.isSome then ", native runs agree" else ""}"
    return 0
  catch e =>
    IO.eprintln s!"tests-own: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Own.Suite
