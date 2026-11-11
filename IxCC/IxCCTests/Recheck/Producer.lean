import IxCCTests.Recheck.Perf
import IxCCTests.Recheck.ProducerRef
import IxCCTests.Lir.Gen
import IxCC.Lir.SplitEdges
import IxCCTests.Support.LamGen
import IxCC.Lam.WellFormed
import IxCC.Lam.ModesOk

/-! # The producer's cost and its rewritten oracles

Regression tests for the producer (`ixcc compile`'s untrusted half), which no
checker budget bounds:

* **Same output.** Each oracle rewritten for speed produces exactly what the
  code it replaced produced (`ProducerRef`), on generated Lir programs (with
  counted loops, branches and calls), on the Anf-level loop and chain shapes,
  on generated Lam programs and on the scaling closures; the producer's
  allocation driver (`Alloc.runProducer`) gives `Alloc.run`'s result.
* **Within the budgets.** The middle end's producer refuses at once a
  program the re-run would refuse, and no longer fails where fewer shrink
  rounds are accepted (`budgets`).
* **Work.** The producer's stages, measured in allocations (the runtime's
  heartbeat count, `IO.getNumHeartbeats`: deterministic for a given input and
  build, unlike wall time), grow near-linearly on scaling inputs: an input
  four times larger may cost at most eight times more. A quadratic step that
  allocates costs sixteen times more and an exponential one far more, so a
  regression to either fails here whatever the machine's load (the replaced
  code fails it: its loop search 133 and 215 times more, its P3 oracle 14.8
  times; `tests-recheck --producer-reference`). Scans that allocate nothing
  escape this count, as the replaced block order's quadratic chain starts
  did; the block order is therefore also timed against the code it replaced,
  on one input in one process, and must be at least four times faster. -/

namespace IxCCTests.Recheck.Producer

open IxCC
open IxCCTests.Src (Assert expect)

/-- The producer's back end on an Xv program up to the tunnelled, stacked
program and its layout shape. -/
def stackedOf (env : Xv.Xl.Env) (xv : Xv.VProgram)
    (reps : Lir.FunId → Option (List Xv.Stacking.ArgRep)) : Except String (X86.Program × X86.Layout.Shape) := do
  let r ← Xv.Alloc.runProducer env xv
  let st ← (Xv.Stacking.run r.program (Xv.Stacking.produce r.program) reps env).mapError toString
  return (X86.Layout.tunnel st.program, st.shape)

/-- The same from an Anf program. -/
def anfStacked (P : Anf.Program) : Except String (X86.Program × X86.Layout.Shape) := do
  let fir ← (Fir.lower P).mapError fun _ => "Fir.lower refused"
  let l ← (Rt.lower {} (Cfg.lower (Own.immortal fir))).mapError fun _ => "Rt.lower refused"
  let (xv, _) ← (Xv.Select.run l.program).mapError fun _ => "Select.run refused"
  stackedOf {} xv l.reps

/-- The block order of the rewritten oracle equals the reference's: on
`count` generated Lir programs and on the Anf-level loop and chain shapes. -/
def orderSame (a : Assert) (count : Nat) : IO (Array String) := do
  let mut compared := 0
  let mut blocks := 0
  let mut declined := 0
  let mut unstacked : Array String := #[]
  for seed in [0:count] do
    -- the forms selection supports (`check-xv-select --restricted`), so most programs reach the order
    let gen : IxCCTests.Lir.Gen.Config :=
      { shiftOps := #[.shl], varShifts := false, divs := false, selects := false, tests := false }
    let (raw, _) := IxCCTests.Lir.Gen.program gen (UInt64.ofNat seed)
    -- `main` as an exported entry, as stacking requires
    let lir := raw.splitCriticalEdges
    let lir := { lir with funcs := lir.funcs.modify lir.main fun f => { f with conv := .sysvExport "cx_main" } }
    match Xv.Select.run lir with
    | .error _ => declined := declined + 1
    | .ok (xv, _) =>
      -- the producer's allocation driver (no closing validation) against `Alloc.run`
      match Xv.Alloc.run {} xv, Xv.Alloc.runProducer {} xv with
      | .ok r, .ok r' =>
        expect a (r.outs == r'.outs && r.program == r'.program)
          s!"generated Lir program {seed}: Alloc.runProducer differs from Alloc.run"
      | .error m, .error m' => expect a (m == m') s!"generated Lir program {seed}: the allocators fail differently"
      | _, _ => expect a false s!"generated Lir program {seed}: one allocator fails, the other does not"
      match stackedOf {} xv (fun _ => none) with
      | .error m => unstacked := unstacked.push m
      | .ok (t, sh) =>
        expect a (X86.Layout.Order.produce t sh == ProducerRef.orderProduce t sh)
          s!"generated Lir program {seed}: the block order differs from the reference"
        compared := compared + 1
        blocks := blocks + t.blocks.size
  let shapes := [("loop", 6, 2), ("loop", 12, 1), ("loop0", 6, 2), ("loop0", 12, 1), ("case", 300, 2),
    ("case2", 300, 2), ("tcase", 200, 2), ("join", 200, 2), ("joinb", 200, 2), ("wide", 100, 2),
    ("comb", 40, 1), ("live", 60, 2)]
  for (kind, n, k) in shapes do
    match anfStacked (Perf.anfProgram kind n k) with
    | .error m => expect a false s!"anf {kind} {n}: {m}"
    | .ok (t, sh) =>
      expect a (X86.Layout.Order.produce t sh == ProducerRef.orderProduce t sh)
        s!"anf {kind} {n} x{k}: the block order differs from the reference"
      blocks := blocks + t.blocks.size
  return #[s!"{compared} generated Lir programs and {shapes.length} Anf shapes ({blocks} blocks): \
    the same block order as the reference ({declined} generated programs declined by selection, \
    {unstacked.size} not stacked: {unstacked.toList.take 2})"]


/-- A scaling shape's Lam program: ingress, the producer's table and
annotation, and erasure. -/
def lamOf (name : String) (n : Nat) : IO Lam.Program := do
  let (e, main) ← IO.ofExcept (Perf.shapeEnv (← IxCCTests.Support.Bound.loadBase) name n)
  let inp ← IO.ofExcept ((Recheck.ingress (Hostile.bytes e)
    (Hostile.sidecar [("main", main)]) []).mapError (·.render))
  let cfg := Recheck.Config.forInput {} inp
  let P := inp.program
  let (table, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  let ann ← IO.ofExcept (inp.kernel.annotateChecked p0)
  let (src, checked) ← IO.ofExcept ((Src.Recheck.annotation p0 ann).mapError fun _ => s!"{name} {n}: annotation")
  let (lam, _) ← IO.ofExcept ((Lam.erase src checked).mapError fun _ => s!"{name} {n}: erasure")
  return lam

/-- The decisions of a specialisation certificate, comparable. -/
def decisions (c : Anf.Specialize.Cert) : List (Nat × Nat × List Bool) :=
  c.decisions.map fun d => (d.caller, d.callee, d.mask)

/-- The middle end's rewritten oracles (P2's certificate, P3's round, P4's
decisions) give the reference's output on every program the default
pipeline passes through, on `count` generated Lam programs and on `extra`. -/
def middleSame (a : Assert) (count : Nat) (extra : List (String × Lam.Program)) : IO (Array String) := do
  let generated := (List.range count).filterMap fun seed =>
    let L := IxCCTests.Support.LamGen.ofSeed seed
    if Lam.wellFormed L && Lam.modesOk L then some (s!"generated program {seed}", L) else none
  let mut programs := 0
  let mut stages := 0
  for (label, L) in generated ++ extra do
    match Anf.Pipeline.produce {} L with
    | .error _ => pure ()
    | .ok tr =>
      programs := programs + 1
      for (step, P) in tr.stages do
        stages := stages + 1
        -- the reference's choices, cut to the certificate's caps
        let refRound := (ProducerRef.inlineProduce {} P).map fun (g, cs) => (g, cs.take Anf.Inline.maxCertCallees)
        expect a (Anf.Inline.produce {} P == refRound)
          s!"{label} after {step}: P3's oracle differs from the reference"
        for inv in [0:3] do
          let refDs := ((ProducerRef.specializeProduce {} inv P).decisions.filter
            (·.mask.length ≤ Anf.Specialize.maxCertMask)).take Anf.Specialize.maxCertDecisions
          expect a (decisions (Anf.Specialize.produce {} inv P) == decisions { inv, decisions := refDs })
            s!"{label} after {step}: P4's oracle differs from the reference"
        -- shrink: the reference's certificate wherever the re-run accepts it;
        -- elsewhere one the re-run accepts
        match Anf.Shrink.produce {} P with
        | .error m => expect a false s!"{label} after {step}: P2's oracle fails: {m}"
        | .ok (c, Q, _) =>
          match ProducerRef.shrinkProduce {} P with
          | .ok (c', Q', _) =>
            if (Anf.Shrink.run {} c' P).isOk then
              expect a (c == c' && Q.beq Q') s!"{label} after {step}: P2's oracle differs from the reference"
            else
              expect a (Anf.Shrink.run {} c P).isOk
                s!"{label} after {step}: P2's certificate is past the re-run's budgets"
          | .error _ =>
            expect a (Anf.Shrink.run {} c P).isOk
              s!"{label} after {step}: P2's certificate is past the re-run's budgets"
  return #[s!"{programs} programs, {stages} programs on their way through the default pipeline: \
    P2, P3 and P4's oracles give the reference's output"]


/-- `k` Lam globals, each a chain of `n` one-field constructors (`Deep.lamChain "con"`). -/
def lamGlobals (n k : Nat) : Lam.Program :=
  let g := fun i => ({ key := .dispatch i, body := Deep.lamChain "con" n } : Lam.Global)
  { globals := Src.NatMap.ofList ((List.range k).map fun i => (i, g i)), size := k, roots := [k - 1],
    ctors := [{ key := .src 0, tag := 0, arity := 1 }, { key := .src 1, tag := 1, arity := 0 }],
    known := default }

/-- The producer stays within the re-run's budgets: on an input whose P1 is
past the back end's work budget (twenty globals of 2,000 nested
constructors) it refuses at P1 with the re-run's message, where it used to
shrink every global and run its back end for a certificate the re-run
refuses; on the shapes whose first shrink round passes a walk's work budget
it records fewer rounds, and the certificate is accepted; and its step count
stays within the certificate's cap. -/
def budgets (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  let L := lamGlobals 2000 20
  match Anf.Pipeline.produce {} L with
  | .ok _ => expect a false "a P1 past the back end's work budget: produced a certificate"
  | .error m =>
    expect a ((m.splitOn "back end's work budget").length > 1) s!"a P1 past the back end's work budget: {m}"
    lines := lines.push s!"20 globals of 2,000 nested constructors: refused at P1 ({m})"
  -- `deep 1000`'s first shrink round passes a walk's work budget: the producer
  -- used to fail there; it now records no round for that global and the
  -- checker accepts the certificate. `tree`, `dag` and `wide` at depth 10 are
  -- past the depth budget at P1: refused there, with the re-run's message.
  for (shape, n, accepted) in [("deep", 1000, true), ("tree", 10, false), ("dag", 10, false),
      ("wide", 10, false)] do
    let (e, main) ← IO.ofExcept (Perf.shapeEnv (← IxCCTests.Support.Bound.loadBase) shape n)
    let inp ← IO.ofExcept ((Recheck.ingress (Hostile.bytes e)
      (Hostile.sidecar [("main", main)]) []).mapError (·.render))
    let cfg := Recheck.Config.forInput {} inp
    match Recheck.produce cfg inp, accepted with
    | .error e, true => expect a false s!"{shape} {n}: the producer refuses: {e.render}"
    | .error e, false =>
      expect a (e.code == "anf.produce" && (e.message.splitOn "depth budget").length > 1)
        s!"{shape} {n}: refused, but not at P1's depth budget: {e.render}"
      lines := lines.push s!"{shape} {n}: refused ({e.render})"
    | .ok _, false => expect a false s!"{shape} {n}: a certificate past the depth budget"
    | .ok c, true =>
      expect a (c.mid.steps.length ≤ Anf.Pipeline.maxSteps) s!"{shape} {n}: {c.mid.steps.length} steps"
      match Recheck.run cfg inp.program c with
      | .ok art => lines := lines.push s!"{shape} {n}: certificate accepted, object {art.object.size} bytes"
      | .error e => expect a false s!"{shape} {n}: the checker refuses the producer's certificate: {e.render}"
  expect a (Recheck.checkMidCert { steps := List.replicate Anf.Pipeline.maxSteps .prune }).isOk
    "Pipeline.maxSteps is past the certificate's step cap"
  return lines

/-- Allocations of a pure computation and a measure of its result, both
evaluated when the action runs. -/
def allocations {α : Type} (x : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let h0 ← IO.getNumHeartbeats
  let n ← IO.lazyPure fun _ => force (x ())
  let h1 ← IO.getNumHeartbeats
  return (h1 - h0, n)

/-- The least of three wall times of a pure computation and a measure of its
result, evaluated when the action runs, in microseconds. -/
def leastTime {α : Type} (x : Unit → α) (force : α → Nat) : IO Nat := do
  let mut best := 0
  for i in [0:3] do
    let t0 ← IO.monoNanosNow
    let _ ← IO.lazyPure fun _ => force (x ())
    let t1 ← IO.monoNanosNow
    let d := (t1 - t0) / 1000
    if i == 0 || d < best then best := d
  return best

/-- `small` and `large` (four times `small`'s size) through `work`, which must
cost at most `8 ×` more allocations on `large`; a line with both counts. -/
def nearLinear (a : Assert) (label : String) (work : Nat → IO Nat) (small : Nat) : IO String := do
  let s ← work small
  let l ← work (4 * small)
  expect a (s > 0) s!"{label}: no allocations counted at {small}"
  expect a (l ≤ 8 * s) s!"{label}: {l} allocations at {4 * small} against {s} at {small} (more than 8×)"
  return s!"{label}: {s} allocations at {small}, {l} at {4 * small} ({l * 10 / max s 1 / 10}.{l * 10 / max s 1 % 10}×)"

/-- The block order's allocations on the Anf shape `kind` of size `n`. -/
def orderWork (kind : String) (k : Nat) (n : Nat) : IO Nat := do
  let (t, sh) ← IO.ofExcept (anfStacked (Perf.anfProgram kind n k))
  let (w, _) ← allocations (fun _ => X86.Layout.Order.produce t sh) fun o => o.flatten.length
  return w

/-- The work part: each line one stage on one scaling shape. -/
def work (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  -- a loop of two-way branches in sequence: the old loop search doubled its
  -- frontier at each branch (2^32 steps at the larger size)
  lines := lines.push (← nearLinear a "block order, loop of n branches" (orderWork "loop0" 1) 8)
  lines := lines.push (← nearLinear a "block order, loop of n branches with work in both arms"
    (orderWork "loop" 1) 8)
  -- one long chain of single-alternative cases (a block each): the old
  -- depth-first search searched its path at every edge
  lines := lines.push (← nearLinear a "block order, a chain of n blocks" (orderWork "case" 1) 500)
  -- two-way cases nested n deep: n chains, each started after a scan of the pending blocks
  lines := lines.push (← nearLinear a "block order, n nested two-way cases" (orderWork "case2" 1) 500)
  -- the replaced block order's quadratic part is scans that allocate little
  -- (its allocations grow 3.9 times here), so it is timed against the code
  -- it replaced instead, on the same input in the same process, the least of
  -- three runs each: at least four times faster (about twenty times today)
  let (t, sh) ← IO.ofExcept (anfStacked (Perf.anfProgram "case2" 2000 1))
  let now ← leastTime (fun _ => X86.Layout.Order.produce t sh) fun o => o.flatten.length
  let old ← leastTime (fun _ => ProducerRef.orderProduce t sh) fun o => o.flatten.length
  expect a (4 * now ≤ old)
    s!"block order, 2,000 nested two-way cases: {now} µs, against the replaced code's {old} µs"
  lines := lines.push s!"block order, 2,000 nested two-way cases: {now} µs, the replaced code {old} µs"
  -- `n` globals each calling the next: the old recursive-global search walked
  -- the call graph from every global (quadratic in the globals)
  lines := lines.push (← nearLinear a "middle end (P1 to the last prune), a chain of n calls" (fun n => do
    let L ← lamOf "many" n
    let (w, _) ← allocations (fun _ => Anf.Pipeline.produce {} L) fun r => match r with
      | .ok tr => tr.stages.length
      | .error _ => 0
    return w) 250)
  -- the whole producer on a closure of n distinct non-recursive functions
  lines := lines.push (← nearLinear a "producer (table to block order), n small functions" (fun n => do
    let (e, main) ← IO.ofExcept (Perf.shapeEnv (← IxCCTests.Support.Bound.loadBase) "fns" n)
    let inp ← IO.ofExcept ((Recheck.ingress (Hostile.bytes e)
      (Hostile.sidecar [("main", main)]) []).mapError (·.render))
    let cfg := Recheck.Config.forInput {} inp
    let (w, _) ← allocations (fun _ => Recheck.produce cfg inp) fun r => match r with
      | .ok c => c.alloc.length
      | .error _ => 0
    return w) 25)
  return lines


/-- `tests-recheck --producer-reference`: the same allocation counts for the
code the rewrites replaced (`ProducerRef`), on the inputs of `work` it can
finish (the block order of a loop of branches at 4 and 16 branches, not 8 and
32: it doubles at every branch), and the new code beside it: what the work
bounds would have measured before the rewrites. A diagnostic, not part of the
suite. -/
def referenceWork : IO UInt32 := do
  let ratio := fun (s l : Nat) => s!"{l * 10 / max s 1 / 10}.{l * 10 / max s 1 % 10}×"
  for (label, kind, small) in [("loop of n branches", "loop0", 4), ("loop of n branches with work in both arms", "loop", 4),
      ("a chain of n blocks", "case", 500), ("n nested two-way cases", "case2", 500)] do
    let refW := fun (n : Nat) => do
      let (t, sh) ← IO.ofExcept (anfStacked (Perf.anfProgram kind n 1))
      let (w, _) ← allocations (fun _ => ProducerRef.orderProduce t sh) fun o => o.flatten.length
      return w
    let s ← refW small
    let l ← refW (4 * small)
    let s' ← orderWork kind 1 small
    let l' ← orderWork kind 1 (4 * small)
    IO.println s!"block order, {label}: reference {s} at {small}, {l} at {4 * small} ({ratio s l}); \
      now {s'}, {l'} ({ratio s' l'})"
  -- the recursive-global search and the P3 oracle on the middle end's first program of `many n`
  for (label, small) in [("P3 oracle on a chain of n calls", 250)] do
    let measure := fun (n : Nat) (old : Bool) => do
      let L ← lamOf "many" n
      let P ← IO.ofExcept (Anf.convert L)
      let (w, _) ← allocations (fun _ => if old then ProducerRef.inlineProduce {} P else Anf.Inline.produce {} P)
        fun r => r.length
      return w
    let s ← measure small true
    let l ← measure (4 * small) true
    let s' ← measure small false
    let l' ← measure (4 * small) false
    IO.println s!"{label}: reference {s} at {small}, {l} at {4 * small} ({ratio s l}); now {s'}, {l'} ({ratio s' l'})"
  return 0

end IxCCTests.Recheck.Producer
