import CompilatrixTests.Backend.Native
import CompilatrixTests.Backend.Cases
import CompilatrixTests.Backend.KernelEval
import CompilatrixTests.Backend.Programs
import CompilatrixTests.Lir.Kernels
import CompilatrixTests.Lir.Gen
import Compilatrix.Xv.Select.Driver
import Compilatrix.Xv.Alloc.Driver
import Compilatrix.Xv.Semantics
import Compilatrix.Lir.SplitEdges
import Compilatrix.Lir.WellFormed

/-!
# `check-backend`

Stacking, layout and emission (M1.B5), end to end:

1. **Hand-written Xl** (`Programs`): frameless leaves, slots, a checked
   leaf, calls with callee-saved registers, stack arguments, tail calls at
   constant stack, failures deep in a call chain, a stack-budget failure,
   heap traffic and fused pairs.
2. **Kernels** (`CompilatrixTests.Lir.Kernels`: fib, sumLoop, sumFrom, gcd,
   natDiv, natMod, natAdd, natSub) through selection and M1.B4's allocation,
   both ways (`Alloc.run`: linear scan with the all-slots fallback; and all
   slots): `Lir.eval`, `Xv.eval` and `Xl.eval` agree, `Xl.eval` finishes at
   the kernel's exact clock and times out one below; then the object runs on
   the typed machine, the byte machine and natively (with bench-sized
   native-only inputs). Static spills, reloads and moves and the step
   counts are reported.
3. **Generated Lir** (`CompilatrixTests.Lir.Gen`, split): every program that
   selects, allocates and runs without getting stuck goes through the
   same levels, both allocations; a sample of linear-scan objects also runs
   natively, in a region at the Lean region's address.

Each object runs on the typed machine and the byte machine
(`Support.runOne`) and, with `--cc`, natively under
`fixtures/x86/backend_driver.c`; every level must return the same
`rax:rdx` with the callee-saved registers and `rsp` restored.

Usage: `check-backend [--cc CC] [--driver PATH] [--work DIR] [--programs N]
[--seeds S1,…] [--native-every K] [--max-blocks B]`.
-/

namespace CompilatrixTests.Backend

open Compilatrix Compilatrix.Xv CompilatrixTests.Lir

def testProvenance : X86.ELF.Provenance := .ixir1Policy (Ixon.Address.replicate 0x42) 1 1

structure Input where
  args : List Word
  budget : Word := defaultBudget
  /-- The expected result when Xl cannot give it: the target's own stack
  failure (status 2), or a run too long for the models. -/
  expect : Option Exit := none
  /-- Run the Lean models (else native only, against `expect`). -/
  models : Bool := true
  deriving Inhabited

structure Case where
  name : String
  program : LProgram
  reps : List Stacking.ArgRep
  inputs : List Input
  clock : Nat := 1000000
  seed : UInt64 := 0
  /-- Map the native region at the Lean region's address, filled with its
  pattern. -/
  fixed : Bool := false

structure Options where
  cc : Option String := none
  driver : System.FilePath := "fixtures/x86/backend_driver.c"
  work : Option System.FilePath := none
  programs : Nat := 125
  seeds : List UInt64 := [0x5eed0001, 0x5eed0002, 0x5eed0003, 0x5eed0004]
  nativeEvery : Nat := 25
  maxBlocks : Nat := 60

/-! ## One case -/

structure CaseReport where
  blocks : Nat := 0
  text : Nat := 0
  runs : List Run := []
  native : Nat := 0

def nat (n : Nat) : Word := UInt64.ofNat n
def tagged (n : Nat) : Word := 2 * UInt64.ofNat n + 1
def ok (v : Word) : Exit := ⟨0, v⟩

def inputLine (i : Input) : String := " ".intercalate ((i.budget :: i.args).map (toString ·.toNat))

/-- Emit, run the models, and (with `tools`) run natively. -/
def checkCase (tools : Option Native.Tools) (c : Case) : ExceptT String IO CaseReport := do
  let a ← match Backend.emit c.program
      { provenance := testProvenance, reps := fun fn => if fn == c.program.main then some c.reps else none } with
    | .ok a => pure a
    | .error e => throw s!"{c.name}: {e}"
  let mut runs := []
  let mut expects : List (Input × Exit) := []
  for i in c.inputs do
    if i.models then
      match runOne c.program a c.reps {} c.clock c.seed i.budget i.args i.expect with
      | .ok r =>
          runs := runs ++ [r]
          match r.exit with
          | some e => expects := expects ++ [(i, e)]
          | none => pure ()
      | .error e => throw s!"{c.name} {i.args}: {e}"
    else
      match i.expect with
      | some e => expects := expects ++ [(i, e)]
      | none => throw s!"{c.name} {i.args}: a native-only input needs an expected result"
  let mut native := 0
  if let some t := tools then
    let exe ← Native.link t c.name a.object a.exportName c.fixed
    let lines := (if c.fixed then [s!"seed {c.seed}"] else []) ++ expects.map (inputLine ·.1)
    let got ← Native.run exe lines
    unless got.length == expects.length do throw s!"{c.name}: {got.length} native results for {expects.length} inputs"
    for ((i, e), g) in expects.zip got do
      unless g.status == e.status && g.value == e.value && g.ok do
        throw s!"{c.name} {i.args}: native {g.status}:{g.value} (registers {if g.ok then "kept" else "clobbered"}), expected {e.status}:{e.value}"
      native := native + 1
  pure { blocks := a.program.blocks.size, text := a.encoded.text.size, runs, native }

def showExit : Option Exit → String
  | some e => if e.status == 0 then s!"0:{e.value}" else s!"{e.status}:0"
  | none => "-"

/-! ## Hand-written Xl -/

def natReps (n : Nat) : List Stacking.ArgRep := List.replicate n .nat
def wordReps (n : Nat) : List Stacking.ArgRep := List.replicate n .word

def handCases : List Case := [
  { name := "leaf", program := Programs.leaf, reps := natReps 2,
    inputs := [⟨[3, 4], defaultBudget, none, true⟩, ⟨[0, 2 ^ 62], defaultBudget, none, true⟩,
      -- a Nat argument ≥ 2^63 fails in the wrapper, at depth 0
      ⟨[2 ^ 63, 1], defaultBudget, some ⟨3, 0⟩, true⟩, ⟨[1, 2 ^ 64 - 1], defaultBudget, some ⟨3, 0⟩, true⟩] },
  { name := "leaf_words", program := Programs.leaf, reps := wordReps 2,
    inputs := [⟨[2 ^ 63, 5], defaultBudget, none, true⟩, ⟨[2 ^ 64 - 1, 1], defaultBudget, none, true⟩] },
  { name := "slots", program := Programs.slots, reps := natReps 2, inputs := [⟨[10, 20], defaultBudget, none, true⟩] },
  { name := "big_frame", program := Programs.bigFrame, reps := natReps 1,
    inputs := [⟨[7], defaultBudget, none, true⟩,
      -- the checked leaf's own frame does not fit a tiny budget: status 2
      ⟨[7], 16, some ⟨2, 0⟩, true⟩] },
  { name := "calls", program := Programs.calls, reps := natReps 1, inputs := [⟨[5], defaultBudget, none, true⟩] },
  { name := "stack_args", program := Programs.stackArgs, reps := natReps 1, inputs := [⟨[100], defaultBudget, none, true⟩] },
  { name := "countdown", program := Programs.countdown, reps := natReps 1,
    inputs := [⟨[0], defaultBudget, none, true⟩, ⟨[1000], 4096, none, true⟩,
      -- a million tail calls within a 4 KiB budget: the stack does not grow
      ⟨[1000000], 4096, some (ok 85), false⟩] },
  { name := "deep", program := Programs.deep, reps := natReps 2,
    inputs := [⟨[0, 0], defaultBudget, none, true⟩, ⟨[3, 0], defaultBudget, none, true⟩,
      -- failures three calls deep: heap, natOverflow, trap
      ⟨[3, 1], defaultBudget, none, true⟩, ⟨[3, 2], defaultBudget, none, true⟩, ⟨[3, 3], defaultBudget, none, true⟩,
      ⟨[0, 1], defaultBudget, none, true⟩,
      -- recursion past a small stack budget: status 2
      ⟨[1000, 0], 4096, some ⟨2, 0⟩, true⟩,
      ⟨[1000000, 0], 65536, some ⟨2, 0⟩, false⟩,
      -- success after failure on the same region
      ⟨[100, 0], defaultBudget, none, true⟩] },
  { name := "heap", program := Programs.heap, reps := wordReps 2, inputs := [⟨[40, 2], defaultBudget, none, true⟩] },
  { name := "fused", program := Programs.fused, reps := wordReps 2,
    inputs := [⟨[100, 7], defaultBudget, none, true⟩, ⟨[7, 100], defaultBudget, none, true⟩,
      ⟨[2 ^ 64 - 1, 3], defaultBudget, none, true⟩] }]

/-! ## Allocation -/

/-- A Lir program selected, then allocated two ways: M1.B4's `Alloc.run`
(linear scan, validated, falling back to all slots per function) and all
slots for every function. -/
structure Allocated where
  xv : VProgram
  scan : Alloc.Result
  slots : Alloc.Result

def allocate (p : Lir.Program) : Except String Allocated := do
  let (xv, _) ← (Select.run p).mapError fun e => s!"selection: {e.form}: {e.reason}"
  let scan ← (Alloc.run {} xv).mapError (s!"allocation: " ++ ·)
  let slots ← (Alloc.runAllSlots {} xv).mapError (s!"all slots: " ++ ·)
  pure { xv, scan, slots }

def countsOf (r : Alloc.Result) : Alloc.EditCounts := r.outs.foldl (fun c o => c.add o.counts) {}

/-- Functions whose linear-scan allocation was accepted. -/
def scanned (r : Alloc.Result) : Nat := r.outcomes.countP fun | .scan => true | _ => false

def Allocated.both (a : Allocated) : List (String × Alloc.Result) := [("scan", a.scan), ("slots", a.slots)]

/-! ## Kernels -/

def kernelInputs : List (Lir.Func × List (List Nat)) := [
  (Kernels.fib, [[0], [1], [2], [10], [15]]),
  (Kernels.sumLoop, [[0], [1], [10], [100], [1000]]),
  (Kernels.sumFrom, [[4, Kernels.natMax - 6], [4, Kernels.natMax - 5]]),
  (Kernels.gcd, [[0, 5], [12, 18], [1071, 462], [Kernels.fibNat 91, Kernels.fibNat 90]]),
  (Kernels.natDiv, [[7, 2], [7, 0], [Kernels.natMax, 1], [0, 5]]),
  (Kernels.natMod, [[7, 2], [7, 0], [Kernels.natMax, 2 ^ 62], [0, 5]]),
  (Kernels.natAdd, [[3, 4], [2 ^ 62, 2 ^ 62], [Kernels.natMax, 0]]),
  (Kernels.natSub, [[5, 3], [3, 5], [Kernels.natMax, 1]])]

/-- Native-only inputs at bench-like sizes, with their Lean-computed results. -/
def kernelBig : List (String × List Nat × Exit) := [
  ("fib", [30], ok (tagged (Kernels.fibNat 30))),
  ("sumLoop", [1000000], ok (tagged (Kernels.sumTo 1000000))),
  ("gcd", [Kernels.fibNat 92, Kernels.fibNat 91], ok (tagged 1))]

/-- The first clock at which Xl does not time out, if below `limit`. -/
def exactClock (p : LProgram) (args : List Word) (limit : Nat) : Option Nat :=
  let rec search (lo hi : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        if lo ≥ hi then some lo
        else
          let mid := (lo + hi) / 2
          match Xl.eval p {} mid args (refMemory 0 defaultBudget) Region.ctx with
          | .timeout => search (mid + 1) hi fuel
          | _ => search lo mid fuel
  match Xl.eval p {} limit args (refMemory 0 defaultBudget) Region.ctx with
  | .timeout => none
  | _ => search 0 limit 64

def checkKernels (tools : Option Native.Tools) : ExceptT String IO Unit := do
  for (f, inputs) in kernelInputs do
    let p := Kernels.program f
    let a ← match allocate p with
      | .ok r => pure r
      | .error e => throw s!"{f.name}: {e}"
    for (label, alloc) in a.both do
      let xl := alloc.program
      for args in inputs do
        let words := args.map Kernels.tag
        let mem := refMemory 0 defaultBudget
        let lir := Lir.eval p 1000000 words mem Region.ctx
        let v := Xv.eval a.xv 1000000 words mem Region.ctx
        let l := Xl.eval xl {} 1000000 words mem Region.ctx
        unless expected lir == expected v && expected v == expected l do
          throw s!"{f.name} {args} ({label}): Lir, Xv and Xl disagree"
        match exactClock xl words 1000000 with
        | some k =>
            if k > 0 then
              match Xl.eval xl {} (k - 1) words mem Region.ctx with
              | .timeout => pure ()
              | _ => throw s!"{f.name} {args} ({label}): Xl does not time out below its exact clock {k}"
        | none => throw s!"{f.name} {args} ({label}): Xl times out"
      let big := kernelBig.filterMap fun (name, args, e) =>
        if name == f.name then some ({ args := args.map nat, expect := some e, models := false } : Input) else none
      let c : Case := { name := s!"kernel_{f.name}_{label}", program := xl, reps := natReps f.params.length,
                        inputs := inputs.map (fun args => ({ args := args.map nat } : Input)) ++ big }
      let r ← checkCase tools c
      let e := countsOf alloc
      let slots := alloc.outs.foldl (· + ·.numSlots) 0
      let fell := if label == "scan" && scanned alloc != alloc.outcomes.length then ", fell back to all slots" else ""
      IO.println s!"kernel {f.name} ({label}{fell}): {slots} slots, {e.spills} spills, {e.reloads} reloads, {e.moves} moves; {r.blocks} blocks, {r.text} bytes of text, {r.native} native runs"
      for run in r.runs do
        let clock := match exactClock xl (run.args.map (2 * · + 1)) 1000000 with
          | some 0 => "exact clock 0"
          | some k => s!"exact clock {k} ({k - 1} times out)"
          | none => "no exact clock"
        IO.println s!"  {run.args.map (·.toNat)} → {showExit run.exit}: {clock}, typed steps {run.typedSteps}, byte steps {run.byteSteps}"

/-! ## Generated programs -/

/-- Make the generated program's `main` an export returning one word:
directly, or through a new entry that calls it and returns its only
result, the XOR of two, or 1 for none. `none` if `main` takes more than
five arguments. -/
def exported (raw : Lir.Program) : Option Lir.Program := do
  let p := { raw with funcs := raw.funcs.map fun (f : Lir.Func) => { f with conv := .internal } }
  let main ← p.funcs[p.main]?
  guard (main.params.length ≤ Stacking.sysvArgs.length)
  if main.results == 1 then
    pure { p with funcs := p.funcs.set! p.main { main with conv := .sysvExport "gen_main" } }
  else
    let n := main.params.length
    let params := List.range n
    let rs := (List.range main.results).map (n + ·)
    let body : Array Lir.Stmt := #[.call rs p.main (params.map .v)] ++
      (if main.results == 2 then #[.assign (n + 2) (.bin .xor .w64 (.v n) (.v (n + 1)))] else #[])
    let result : Lir.Arg := if main.results == 2 then .v (n + 2) else .imm 1
    let entry : Lir.Func := { name := "gen_entry", params, results := 1, conv := .sysvExport "gen_main",
                              blocks := #[{ body, term := .ret [result] }] }
    pure { funcs := p.funcs.push entry, main := p.funcs.size }

/-- Whether a program loads `entrySp` or `stackLimit`, which the native
wrapper sets to its own stack's addresses. -/
def readsFrameFields (p : Lir.Program) : Bool :=
  p.funcs.toList.any fun f => f.blocks.toList.any fun b => b.body.toList.any fun
    | .assign _ (.load _ _ { base := some .ctx, index := none, disp := d }) => d == -64 || d == -56
    | _ => false

structure GenReport where
  programs : Nat := 0
  compiled : Nat := 0
  skipped : Nat := 0
  outcomes : Array Nat := Array.replicate 5 0
  /-- Functions allocated, and those whose linear-scan allocation was accepted. -/
  funcs : Nat := 0
  scanned : Nat := 0
  /-- Objects emitted and run (two allocations per program). -/
  objects : Nat := 0
  typedSteps : Nat := 0
  byteSteps : Nat := 0
  text : Nat := 0
  native : Nat := 0

def genClock : Nat := 5000

def checkGenerated (tools : Option Native.Tools) (o : Options) : ExceptT String IO GenReport := do
  let cfg : Gen.Config := { maxBlocks := o.maxBlocks }
  let mut report : GenReport := {}
  for seed in o.seeds do
    for n in [:o.programs] do
      let programSeed := Support.Rng.derive seed n
      report := { report with programs := report.programs + 1 }
      let (raw, _) := Gen.program cfg programSeed
      let args := Gen.mainArgs raw programSeed
      let some p := exported raw.splitCriticalEdges
        | report := { report with skipped := report.skipped + 1 }; continue
      if let .error e := p.check then throw s!"generated {seed}/{n}: not well formed: {e}"
      let mem := refMemory programSeed defaultBudget
      let lir := Lir.eval p genClock args mem Region.ctx
      match expected lir with
      | none => report := { report with skipped := report.skipped + 1 }; continue
      | some _ => pure ()
      let a ← match allocate p with
        | .ok r => pure r
        | .error e => throw s!"generated {seed}/{n} (program seed {programSeed}): {e}"
      let v := Xv.eval a.xv genClock args mem Region.ctx
      let idx := match (expected v).map (·.status.toNat) with | some s => min s 4 | none => 4
      report := { report with
        compiled := report.compiled + 1
        outcomes := report.outcomes.modify idx (· + 1)
        funcs := report.funcs + a.scan.outcomes.length
        scanned := report.scanned + scanned a.scan }
      for (label, alloc) in a.both do
        let l := Xl.eval alloc.program {} genClock args mem Region.ctx
        unless expected lir == expected v && expected v == expected l do
          throw s!"generated {seed}/{n} (program seed {programSeed}, {label}): Lir {showExit (expected lir)}, Xv {showExit (expected v)}, Xl {showExit (expected l)}"
        let native := tools.isSome && label == "scan" && o.nativeEvery != 0 && n % o.nativeEvery == 0 &&
          !readsFrameFields p
        let c : Case := { name := s!"gen_{seed}_{n}_{label}", program := alloc.program, reps := wordReps args.length,
                          inputs := [{ args }], clock := genClock, seed := programSeed, fixed := true }
        let r ← tryCatch (checkCase (if native then tools else none) c) fun e =>
          throw s!"{e} (program seed {programSeed})"
        report := { report with
          objects := report.objects + 1
          typedSteps := report.typedSteps + (r.runs.map (·.typedSteps)).sum
          byteSteps := report.byteSteps + (r.runs.map (·.byteSteps)).sum
          text := report.text + r.text
          native := report.native + (if r.native > 0 then 1 else 0) }
  pure report

/-! ## Driver -/

def parseNat (flag n : String) : Except String Nat :=
  match n.toNat? with
  | some n => pure n
  | none => throw s!"bad {flag} {n}"

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--cc" :: cc :: rest => do return { (← parseOptions rest) with cc := some cc }
  | "--driver" :: d :: rest => do return { (← parseOptions rest) with driver := d }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--programs" :: n :: rest => do return { (← parseOptions rest) with programs := ← parseNat "--programs" n }
  | "--native-every" :: n :: rest => do
      return { (← parseOptions rest) with nativeEvery := ← parseNat "--native-every" n }
  | "--max-blocks" :: n :: rest => do
      return { (← parseOptions rest) with maxBlocks := ← parseNat "--max-blocks" n }
  | "--seeds" :: s :: rest => do
      let o ← parseOptions rest
      let seeds ← (s.splitOn ",").mapM fun t => UInt64.ofNat <$> parseNat "seed" t
      pure { o with seeds }
  | arg :: _ => throw s!"unknown argument {arg}"

def suite (o : Options) (tools : Option Native.Tools) : ExceptT String IO Unit := do
  let start ← IO.monoMsNow
  for c in handCases do
    let r ← checkCase tools c
    let runs := r.runs.map fun run => s!"{run.args.map (·.toNat)} → {showExit run.exit} ({run.typedSteps}/{run.byteSteps})"
    IO.println s!"xl {c.name}: {r.blocks} blocks, {r.text} bytes, {r.native} native; {", ".intercalate runs}"
  IO.println s!"hand-written Xl: {handCases.length} programs ok ({(← IO.monoMsNow) - start} ms)"
  let kernelStart ← IO.monoMsNow
  checkKernels tools
  IO.println s!"kernels ok ({(← IO.monoMsNow) - kernelStart} ms)"
  let genStart ← IO.monoMsNow
  let g ← checkGenerated tools o
  IO.println s!"generated: {g.programs} programs, {g.compiled} compiled ({g.skipped} skipped: stuck, timed out or over five arguments); {g.objects} objects run (linear scan and all slots), {g.native} natively"
  IO.println s!"  outcomes: ok {g.outcomes[0]!}, heap {g.outcomes[1]!}, stack {g.outcomes[2]!}, natOverflow {g.outcomes[3]!}, trap {g.outcomes[4]!}"
  IO.println s!"  linear scan accepted for {g.scanned} of {g.funcs} functions (the rest fell back to all slots)"
  IO.println s!"  steps: typed {g.typedSteps}, byte {g.byteSteps}; text {g.text} bytes ({(← IO.monoMsNow) - genStart} ms)"

def run (args : List String) : IO Bool := do
  match parseOptions args with
  | .error e =>
      IO.eprintln s!"check-backend: {e}"
      return false
  | .ok o =>
      let start ← IO.monoMsNow
      let go (tools : Option Native.Tools) : IO Bool := do
        match ← (suite o tools).run with
        | .ok () =>
            IO.println s!"check-backend: ok ({(← IO.monoMsNow) - start} ms){if tools.isSome then ", native runs agree" else ""}"
            return true
        | .error e =>
            IO.eprintln s!"check-backend: {e}"
            return false
      match o.cc, o.work with
      | none, _ => go none
      | some cc, some work =>
          IO.FS.createDirAll work
          go (some { cc, driver := o.driver, work })
      | some cc, none => IO.FS.withTempDir fun work => go (some { cc, driver := o.driver, work })

end CompilatrixTests.Backend
