import IxCCTests.Rt.Machine
import IxCCTests.Rt.Native
import IxCCTests.Rt.Differential
import IxCCTests.Rt.Cases
import IxCC.Tools.Check

/-! `Rt.lower`'s output at every level down to native (M1.F6):

* the **bench-k1 entries**: small inputs at Cfg, Lir, Xv, Xl, typed x86 and
  the byte machine; with `--cc`, natively at those inputs, at the test
  sizes (against `expected.txt`) and at the bench sizes (against the
  manifest's `bench_expected`), and an argument past 2^63 (status 3 from the
  wrapper);
* the **hand-written values** (pairs, options, lists, trees) at every level,
  and natively with the object area dumped: the C decoder's observation, the
  Lean `Rt.readback` of the dump and Cfg's observation agree;
* a **sample of generated programs** at every level and natively;
* natively: a list too long for a 4 KiB region (status 1, heap), and a
  recursion 10⁶ calls deep on a 1 MiB stack (status 2, the budget) and on a
  256 MiB one (the value). -/

namespace IxCCTests.Rt.Levels

open IxCC IxCCTests.Src IxCCTests.Fir IxCCTests.Rt.Machine
open IxCCTests.Backend (Exit)
open IxCC.Tools.Check (readJson strField arrField)

/-- Bench arguments and expected output from the manifest. -/
def benchCase (name : String) : IO (List Nat × Nat) := do
  let m ← readJson "benchmarks/fixtures/manifest.json"
  for f in ← arrField m "fixtures" do
    if (← strField f "name") == name then
      let args ← (← arrField f "bench_args").toList.mapM fun j => do
        match j.getStr? with
        | .ok s => pure s.toNat!
        | .error e => throw (IO.userError e)
      return (args, (← strField f "bench_expected").trimAscii.toString.toNat!)
  throw (IO.userError s!"{name} is not in the manifest")

/-- Small inputs for the models. -/
def modelArgs : String → List (List Nat)
  | "fib" => [[0], [1], [10]]
  | "sum-loop" => [[0], [100]]
  | "ackermann" => [[0, 0], [2, 3]]
  | "tak" => [[6, 4, 2, 1], [5, 3, 2, 1]]
  | "gcd" => [[0, 5], [1071, 462], [2 ^ 62, 2 ^ 61 + 3]]
  | _ => []

def lirExpect (c : Compiled) (root : Nat) (args : List Nat) (mem : X86.Memory) : Option Exit :=
  IxCCTests.Backend.expected (Lir.eval { c.lir.program with main := root } (1 <<< 40) (args.map tag) mem ctx)

structure Stats where
  programs : Nat := 0
  report : Report := {}
  native : Nat := 0
  decoded : Nat := 0
  lines : Array String := #[]

/-- Native runs of one root: each line's status and value must be the
expected exit (for an immediate) or read back as the expected observation
(both through the C decoder and through `Rt.readback` of the dump). -/
def nativeCheck (a : Assert) (t : Native.Tools) (c : Compiled) (name : String) (root : Nat)
    (inputs : List (List Nat × Exit × Option Sem.Obs)) (o : Native.Options) : IO (List Native.Line) := do
  let some symbol := c.lir.roots.lookup root | throw (IO.userError s!"{name}: f{root} is not a root")
  let exe ← Native.link t name c.artifact.object symbol
  let lines ← Native.run exe o (inputs.map (·.1))
  for ((xs, e, obs), l) in inputs.zip lines do
    expect a l.ok s!"{name} {xs}: a callee-saved register or rsp changed natively"
    expect a (l.status == e.status) s!"{name} {xs}: native status {l.status}, expected {e.status}"
    match obs, o.ty with
    | some want, some (sig, ty) =>
      expect a (l.obs == some (Rt.renderObs want)) s!"{name} {xs}: the C decoder gives {l.obs}, expected {Rt.renderObs want}"
      if o.dump then
        expect a (l.readback o.region sig ty == some want)
          s!"{name} {xs}: Rt.readback of the dump gives {repr (l.readback o.region sig ty)}"
    | _, _ =>
      -- immediates agree as words
      if e.value % 2 == 1 || e.status != 0 then
        expect a (l.value == e.value) s!"{name} {xs}: native value {l.value}, expected {e.value}"
  pure lines

def benches (a : Assert) (tools : Option Native.Tools) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let (S, root) ← Differential.entry name
    let c ← IO.ofExcept ((compile S.lir).mapError (s!"{name}: " ++ ·))
    let ms ← IO.ofExcept ((initMachines c).mapError (s!"{name} cx_init: " ++ ·))
    let mut r : Report := {}
    for xs in modelArgs name do
      r ← IO.ofExcept ((check c root xs 1000000 ms r).mapError (s!"{name} {xs}: " ++ ·))
      a.modify (· + 1)
    -- an argument past 2^63 fails in the wrapper
    let arity := S.levels.cfg.fun? root |>.bind (·.blocks.head?) |>.map (·.params.length) |>.getD 1
    r ← IO.ofExcept ((check c root (2 ^ 63 :: List.replicate (arity - 1) 1) 0 ms r (wrapperOnly := true)).mapError
      (s!"{name}: " ++ ·))
    let text := c.artifact.encoded.text.size
    let mut line := s!"{name}: {r.runs} model runs agree (typed steps {r.typedSteps}, byte steps {r.byteSteps}); \
      text {text} bytes"
    if let some t := tools then
      let (testArgs, testWant) ← IxCCTests.Src.Bench.testCase name
      let (benchArgs, benchWant) ← benchCase name
      let mem ← IO.ofExcept (initRegion c.lir)
      let small := (modelArgs name).filterMap fun xs => (lirExpect c root xs mem).map (xs, ·, none)
      let inputs := small ++ [(testArgs, ⟨0, tag testWant⟩, none), (benchArgs, ⟨0, tag benchWant⟩, none),
        (2 ^ 63 :: List.replicate (arity - 1) 1, ⟨3, 0⟩, none)]
      let lines ← nativeCheck a t c name root inputs { time := true }
      let ns := lines.filterMap (·.ns)
      line := line ++ s!"; native {lines.length} runs agree (test size {ns[small.length]!} ns, \
        bench size {benchArgs} {ns[small.length + 1]!} ns)"
    out := out.push line
  return out

/-- The hand-written values at every level and natively, with dumps. -/
def values (a : Assert) (tools : Option Native.Tools) : IO (Array String) := do
  let C := Cases.cfgOf Cases.values'
  let (l, mem) ← Cases.lirOf C
  let c ← IO.ofExcept (compile l)
  let ms ← IO.ofExcept (initMachines c)
  let mut r : Report := {}
  for (f, xs, _, _) in Cases.cases do
    r ← IO.ofExcept ((check c f xs 100000 ms r).mapError (s!"values f{f} {xs}: " ++ ·))
    a.modify (· + 1)
  let mut out := #[s!"values: {r.runs} model runs agree (typed steps {r.typedSteps}, byte steps {r.byteSteps})"]
  if let some t := tools then
    let mut n := 0
    for f in List.range Cases.values'.size do
      let rows := Cases.cases.filter (·.1 == f)
      let some (_, _, ty, _) := rows.head? | continue
      let inputs := rows.filterMap fun (_, xs, _, want) => (lirExpect c f xs mem).map (xs, ·, want)
      let lines ← nativeCheck a t c s!"values_f{f}" f inputs { ty := some (Cases.sig, ty), dump := true }
      n := n + lines.length
    -- a list of 200 cells does not fit a 4 KiB region; 100 do
    let lines ← nativeCheck a t c "values_heap" 2
      [([100], ⟨0, 0⟩, none), ([200], ⟨1, 0⟩, none)] { region := 4096 }
    n := n + lines.length
    out := out.push s!"values natively: {n} runs agree; the C decoder and Rt.readback of each dump match Cfg's \
      observation; a 200-cell list in 4 KiB fails with heap"
  return out

/-- `deep n = if n = 0 then 0 else deep (n - 1) + 1`: one frame per call. -/
def deep : FProgram := Cases.prog
  [([0], .case 0 [.mk Cases.natZ (.ret (Cases.n 0)),
      .mk Cases.natS (.bind 1 (.proj 0 Cases.natS 0) (.bind 2 (.call 0 [Cases.v 1])
        (.bind 3 (.prim .natAdd [Cases.v 2, Cases.n 1]) (.ret (Cases.v 3)))))] none)]

def stacks (a : Assert) (t : Native.Tools) : IO (Array String) := do
  let (l, _) ← Cases.lirOf (Cases.cfgOf deep)
  let c ← IO.ofExcept (compile l)
  let _ ← nativeCheck a t c "deep_small" 0 [([1000], ⟨0, tag 1000⟩, none), ([1000000], ⟨2, 0⟩, none)]
    { stack := 1 <<< 20 }
  let _ ← nativeCheck a t c "deep_big" 0 [([1000000], ⟨0, tag 1000000⟩, none)] { stack := 1 <<< 28 }
  return #["deep recursion: 10⁶ calls fail with status 2 on a 1 MiB stack and return 10⁶ on a 256 MiB one"]

/-- Every `every`-th generated program at every level, and natively. -/
def generated (a : Assert) (tools : Option Native.Tools) (count every : Nat) : IO (Array String) := do
  let mut r : Report := {}
  let mut programs := 0
  let mut native := 0
  for seed in (List.range count).filter (· % every == 0) do
    let (A, ty) := Gen.ofSeedTy seed
    let S ← IO.ofExcept ((lowerAll A).mapError (s!"generated seed {seed}: " ++ ·))
    let c ← IO.ofExcept ((compile S.lir).mapError (s!"generated seed {seed}: " ++ ·))
    let ms ← IO.ofExcept ((initMachines c).mapError (s!"generated seed {seed} cx_init: " ++ ·))
    let mut inputs := []
    for xs in [[0], [1], [3], [5]] do
      match lirExpect c 0 xs S.mem with
      | some e =>
        r ← IO.ofExcept ((check c 0 xs 100000 ms r).mapError (s!"generated seed {seed} {xs}: " ++ ·))
        a.modify (· + 1)
        let want ← match ← runCfg .immortal S.levels.cfg 100000 0 xs with
          | .ok (v, H) => pure (H.readback v)
          | _ => pure none
        inputs := inputs ++ [(xs, e, want)]
      | none => pure ()   -- stuck or timed out at Lir: nothing to compare
    programs := programs + 1
    if let some t := tools then
      let lines ← nativeCheck a t c s!"gen_{seed}" 0 inputs
        { ty := some (Differential.genSig, Differential.genTy ty), dump := true }
      native := native + lines.length
  return #[s!"{programs} generated programs: {r.runs} model runs agree (typed steps {r.typedSteps}, \
    byte steps {r.byteSteps}); {native} native runs agree (C decoder and dump readback included)"]

end IxCCTests.Rt.Levels
