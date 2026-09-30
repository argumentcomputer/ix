import Compilatrix.Backend
import CompilatrixTests.Lir.Kernels
import Lean.Data.Json

/-!
# `backend-probe`: the MEAS-4 kernels as objects (M1.B6, 05 §12)

Compiles the synthetic Lir kernels `fib`, `sumLoop` and `gcd`
(`CompilatrixTests.Lir.Kernels`) with `Backend.compile` (selection, M1.B4's
linear scan with the all-slots fallback, stacking, layout, E1/E2 and the
ELF writer) into `DIR/lir_<kernel>.o`, each exporting `lir_<kernel>`, and
prints one JSON line per kernel:

- `text`: the object's text bytes, and `function`: the kernel function's
  own bytes (without the export wrapper and the exit group);
- `xl`: allocation's static spills, reloads and moves (`Alloc.EditCounts`);
- `loop`: in the laid-out x86, the blocks inside natural loops, and the
  register moves, stack stores (spills) and stack loads (reloads) there;
- `stackChecks`: functions whose prologue checks the stack (three
  instructions per call of a non-leaf frame);
- `compile_ms`: the median time of selection, allocation, emission and the
  whole of `Backend.compile` over `--reps` runs (default 20), natively.

The probe feeds the MEAS-4 measurement (`benchmarks/meas4`); these kernels
are never reported as real-program results (roadmap §9).

Usage: `backend-probe DIR [--reps N]`.
-/

namespace CompilatrixTests.Backend.Probe

open Lean Compilatrix Compilatrix.Xv CompilatrixTests.Lir

/-- The object's provenance; `i` only varies the timed runs. -/
def provenance (i : Nat) : X86.ELF.Provenance := .ixir1Policy (Ixon.Address.replicate 0x42) (UInt32.ofNat i) 1

/-! ## Timed phases (not inlined, so each run recomputes) -/

@[noinline] def selectOnce (p : Lir.Program) (i : Nat) : Nat :=
  match Select.run p with
  | .ok (xv, _) => xv.funcs.size + i % 1
  | .error _ => 0

@[noinline] def allocOnce (xv : VProgram) (i : Nat) : Nat :=
  match Alloc.run {} xv with
  | .ok r => r.program.funcs.size + i % 1
  | .error _ => 0

@[noinline] def emitOnce (xl : LProgram) (i : Nat) : Nat :=
  match Backend.emit xl { provenance := provenance i } with
  | .ok a => a.object.size
  | .error _ => 0

@[noinline] def compileOnce (p : Lir.Program) (i : Nat) : Nat :=
  match Backend.compile p { provenance := provenance i } with
  | .ok a => a.object.size
  | .error _ => 0

/-- The median of `reps` timings of `f i`, in milliseconds. -/
def medianMs (reps : Nat) (f : Nat → Nat) : IO Float := do
  let mut samples : Array Nat := #[]
  for i in [:reps] do
    let start ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => f (i + 1)
    let stop ← IO.monoNanosNow
    if r == 0 then throw (IO.userError "a timed phase failed")
    samples := samples.push (stop - start)
  let sorted := samples.qsort (· < ·)
  return (sorted[sorted.size / 2]?.getD 0).toFloat / 1e6

/-! ## Static counts in the laid-out x86 -/

/-- The blocks of natural loops, over terminator edges. -/
def loopBlocks (p : X86.Program) : X86.Layout.NatSet :=
  let m := X86.Layout.blockMap p
  let ok (_ : Nat) : Bool := true
  let fuel := p.blocks.size + 1
  let all := List.range p.blocks.size
  let (_, backs) := all.foldl (init := (({} : X86.Layout.NatSet), ([] : List (Nat × Nat)))) fun acc r =>
    if acc.1.contains r then acc else X86.Layout.backEdges m ok fuel [] acc r
  let preds := X86.Layout.predsIn m ok all
  backs.foldl (init := {}) fun s (u, h) =>
    (X86.Layout.loopBody preds fuel (({} : X86.Layout.NatSet).insert h) [u]).toList.foldl (·.insert ·) s

def onStack (a : X86.Arg) : Bool :=
  match a with
  | .mem m => m.base == some .rsp
  | _ => false

/-- Register moves, stack stores and stack loads among `instrs`. -/
def classify (instrs : List X86.Instr) : Nat × Nat × Nat :=
  instrs.foldl (init := (0, 0, 0)) fun (moves, stores, loads) i =>
    match i with
    | .op o [.reg _, .reg _] => if o.mn == .mov then (moves + 1, stores, loads) else (moves, stores, loads)
    | .op o [a, .reg _] => if o.mn == .mov && onStack a then (moves, stores + 1, loads) else (moves, stores, loads)
    | .op o [.reg _, a] =>
        if (o.mn == .mov || o.mn == .movzx) && onStack a then (moves, stores, loads + 1) else (moves, stores, loads)
    | _ => (moves, stores, loads)

/-! ## One kernel -/

def kernelJson (dir : System.FilePath) (reps : Nat) (f : Lir.Func) : IO Json := do
  let p := Kernels.program f
  let a ← match Backend.compile p { provenance := provenance 1 } with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{f.name}: {e}")
  IO.FS.writeBinFile (dir / s!"lir_{f.name}.o") a.object
  let (xv, _) ← IO.ofExcept ((Select.run p).mapError fun e => s!"{e.form}: {e.reason}")
  let alloc ← IO.ofExcept (Alloc.run {} xv)
  let counts : Alloc.EditCounts := alloc.outs.foldl (fun (c : Alloc.EditCounts) o => c.add o.counts) {}
  let xl := alloc.program
  -- the kernel function's bytes: its layout group, after the wrapper's
  let order := X86.Layout.Order.produce (X86.Layout.tunnel a.stacked.program) a.stacked.shape
  let start := (order[0]?.getD []).length
  let stop := start + (order[1]?.getD []).length
  let offset (b : Nat) : Nat := a.encoded.blockOffsets[b]?.getD a.encoded.text.size
  let loops := loopBlocks a.program
  let inLoops := loops.toList.flatMap fun b => ((a.program.blocks[b]?.map (·.instructions.toList)).getD [])
  let (loopMoves, loopStores, loopLoads) := classify inLoops
  let fnBlocks := (List.range stop).drop start
  let (allMoves, allStores, allLoads) := classify (fnBlocks.flatMap fun b =>
    ((a.program.blocks[b]?.map (·.instructions.toList)).getD []))
  -- machine instructions as encoded: a fused pair is two, a terminator its
  -- producer, jcc and any jmp
  let ops (b : Nat) : Nat := match a.program.blocks[b]? with
    | some blk => (blk.instructions.toList.map fun | .fused .. => 2 | _ => 1).sum +
        (X86.Encode.terminatorOperations blk.terminator).length
    | none => 0
  let fnOps := (fnBlocks.map ops).sum
  let loopOps := (loops.toList.map ops).sum
  let layouts := Stacking.produce xl
  let checks := (xl.funcs.toList.zip layouts).countP fun (g, l) => Stacking.FrameLayout.checked g.facts l
  let selectMs ← medianMs reps (selectOnce p)
  let allocMs ← medianMs reps (allocOnce xv)
  let emitMs ← medianMs reps (emitOnce xl)
  let compileMs ← medianMs reps (compileOnce p)
  return Json.mkObj [
    ("kernel", Json.str f.name), ("symbol", Json.str a.exportName),
    ("allocation", Json.str (if alloc.outcomes.all (fun | .scan => true | _ => false) then "linear scan" else "all slots")),
    ("text", toJson a.encoded.text.size), ("function", toJson (offset stop - offset start)),
    ("blocks", toJson a.program.blocks.size),
    ("xl", Json.mkObj [("spills", toJson counts.spills), ("reloads", toJson counts.reloads),
      ("moves", toJson counts.moves)]),
    ("function_x86", Json.mkObj [("instructions", toJson fnOps), ("moves", toJson allMoves),
      ("stack_stores", toJson allStores), ("stack_loads", toJson allLoads)]),
    ("loop", Json.mkObj [("blocks", toJson loops.size), ("instructions", toJson loopOps),
      ("moves", toJson loopMoves), ("stack_stores", toJson loopStores), ("stack_loads", toJson loopLoads)]),
    ("stackChecks", toJson checks),
    ("compile_ms", Json.mkObj [("select", toJson selectMs), ("allocate", toJson allocMs),
      ("emit", toJson emitMs), ("compile", toJson compileMs), ("reps", toJson reps)])]

def kernels : List Lir.Func := [Kernels.fib, Kernels.sumLoop, Kernels.gcd]

def run (args : List String) : IO UInt32 := do
  let (dir, reps) ← match args with
    | [dir] => pure (dir, 20)
    | [dir, "--reps", n] => pure (dir, n.toNat!)
    | _ =>
        IO.eprintln "usage: backend-probe DIR [--reps N]"
        return 2
  IO.FS.createDirAll dir
  for f in kernels do
    IO.println (← kernelJson dir reps f).compress
  return 0

end CompilatrixTests.Backend.Probe
