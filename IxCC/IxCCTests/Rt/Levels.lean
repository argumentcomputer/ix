import IxCCTests.Rt.Machine
import IxCCTests.Rt.Native
import IxCCTests.Rt.Differential
import IxCCTests.Rt.Cases
import IxCC.Tools.Check

/-! `Rt.lower`'s output at every level down to native:

* the **bench-k1 entries**: small inputs at Cfg, Lir, Xv, Xl, typed x86 and
  the byte machine; with `--native`, natively at those inputs, at the test
  sizes (against `expected.txt`) and at the bench sizes (against the
  manifest's `bench_expected`), and an argument past 2^63 (status 3 from the
  wrapper);
* the **hand-written values** (pairs, options, lists, trees) at every level,
  and natively with the object area dumped: the independent decoder's
  observation, `Rt.readback` of the dump and Cfg's observation agree;
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
(both through the independent decoder and through `Rt.readback` of the dump). -/
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
      expect a (l.obs == some (Rt.renderObs want)) s!"{name} {xs}: the independent decoder gives {l.obs}, expected {Rt.renderObs want}"
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
    out := out.push s!"values natively: {n} runs agree; the independent decoder and Rt.readback of each dump match Cfg's \
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

/-- End-to-end backend tests for the new hardware limb primitives (`mulWide64`, `divWide64`,
`addCarry64`, `subBorrow64`, `bsr64`) and `brOvf .mulOvf` across Lir, Xv, Xl, Validate,
Stacking, Typed x86, and ByteEval. -/
def limbOps (a : Assert) : IO (Array String) := do
  let mkLimbFn (name sym : String) (params : List Lir.VReg) (op : Lir.LimbOp) (retHi : Bool) : Lir.Func :=
    { name, params, results := 1, conv := .sysvExport sym
      blocks := #[{ body := #[.limb 10 11 op], term := .ret [.v (if retHi then 11 else 10)] }] }
  let bsrFn : Lir.Func :=
    { name := "bsr64", params := [0], results := 1, conv := .sysvExport "limb_bsr64"
      blocks := #[{ body := #[.assign 10 (.bsr64 (.v 0))], term := .ret [.v 10] }] }
  let mulOvfFn : Lir.Func :=
    { name := "mulOvf", params := [0, 1], results := 1, conv := .sysvExport "limb_mulOvf"
      blocks := #[
        { term := .brOvf .mulOvf 10 (.v 0) (.v 1) ⟨1, []⟩ ⟨2, []⟩ },
        { term := .ret [.v 10] },
        { term := .fail .natOverflow, cold := true }] }
  let prog : Lir.Program := {
    main := 0
    funcs := #[
      mkLimbFn "mulWideLo" "limb_mulWideLo" [0, 1] (.mulWide64 (.v 0) (.v 1)) false,
      mkLimbFn "mulWideHi" "limb_mulWideHi" [0, 1] (.mulWide64 (.v 0) (.v 1)) true,
      mkLimbFn "divWideQ" "limb_divWideQ" [0, 1, 2] (.divWide64 (.v 0) (.v 1) (.v 2)) false,
      mkLimbFn "divWideR" "limb_divWideR" [0, 1, 2] (.divWide64 (.v 0) (.v 1) (.v 2)) true,
      mkLimbFn "addCarryS" "limb_addCarryS" [0, 1, 2] (.addCarry64 (.v 0) (.v 1) (.v 2)) false,
      mkLimbFn "addCarryC" "limb_addCarryC" [0, 1, 2] (.addCarry64 (.v 0) (.v 1) (.v 2)) true,
      mkLimbFn "subBorrowD" "limb_subBorrowD" [0, 1, 2] (.subBorrow64 (.v 0) (.v 1) (.v 2)) false,
      mkLimbFn "subBorrowB" "limb_subBorrowB" [0, 1, 2] (.subBorrow64 (.v 0) (.v 1) (.v 2)) true,
      bsrFn,
      mulOvfFn] }
  match prog.check with
  | .ok () => expect a true ""
  | .error e => expect a false s!"limbOps: Lir not WellFormed: {e}"
  let (xv, _) ← IO.ofExcept ((Xv.Select.run prog).mapError fun e => s!"limbOps select: {e.form}: {e.reason}")
  match xv.check with
  | .ok () => expect a true ""
  | .error e => expect a false s!"limbOps: Xv not WellFormed: {e}"
  let alloc ← IO.ofExcept ((Xv.Alloc.run {} xv).mapError (s!"limbOps alloc: " ++ ·))
  match Xv.Validate.run {} xv alloc.outs with
  | .ok _ => expect a true ""
  | .error e => expect a false s!"limbOps: Validate refused: {e}"
  let cfg : Backend.Config := {
    reps := fun fi => prog.funcs[fi]?.map fun f => List.replicate f.params.length .word
    provenance := testProvenance }
  let art ← IO.ofExcept ((Backend.emit alloc.program cfg).mapError toString)
  let c : Compiled := {
    lir := { program := prog, init := 0, natPow := 0, natGcd := 0, roots := [] }
    xv, xl := alloc.program, artifact := art }
  let mem := IxCCTests.Backend.refMemory 0 IxCCTests.Backend.defaultBudget
  let checkRaw (fn : Nat) (sym : String) (args : List Word) (want : Exit) : IO Unit := do
    let rl := Lir.eval { prog with main := fn } 1000 args mem IxCCTests.Lir.Region.ctx
    let rx := Xv.eval { xv with main := fn } 1000 args mem IxCCTests.Lir.Region.ctx
    let rxl := Xv.Xl.eval { alloc.program with main := fn } {} 1000 args mem IxCCTests.Lir.Region.ctx
    expect a (IxCCTests.Backend.expected rl == some want) s!"{sym} {args}: Lir {repr (IxCCTests.Backend.expected rl)}, expected {repr want}"
    expect a (IxCCTests.Backend.expected rx == some want) s!"{sym} {args}: Xv mismatch"
    expect a (IxCCTests.Backend.expected rxl == some want) s!"{sym} {args}: Xl mismatch"
    let sh : IxCCTests.Backend.Shadow := { base := IxCCTests.Backend.machineMemory 0 IxCCTests.Backend.defaultBudget }
    let (et, _, _) ← IO.ofExcept (runExportTyped c sym args sh)
    let (eb, _, _) ← IO.ofExcept (runExportBytes c sym args sh)
    expect a (et == want) s!"{sym} {args}: typed {repr et}, expected {repr want}"
    expect a (eb == want) s!"{sym} {args}: bytes {repr eb}, expected {repr want}"
  let maxW : Word := 0xffffffffffffffff
  -- mulWide64: (2^64-1)*(2^64-1) = (2^64-2)*2^64 + 1
  checkRaw 0 "limb_mulWideLo" [maxW, maxW] ⟨0, 1⟩
  checkRaw 1 "limb_mulWideHi" [maxW, maxW] ⟨0, maxW - 1⟩
  checkRaw 0 "limb_mulWideLo" [0x100000000, 0x100000000] ⟨0, 0⟩
  checkRaw 1 "limb_mulWideHi" [0x100000000, 0x100000000] ⟨0, 1⟩
  checkRaw 0 "limb_mulWideLo" [0x123456789abcdef0, 0xfedcba9876543210] ⟨0, 0x123456789abcdef0 * 0xfedcba9876543210⟩
  -- divWide64: ((1 * 2^64 + 0) / 0x100000000 = 0x100000000 rem 0), ((2 * 2^64 + 7) / 3)
  checkRaw 2 "limb_divWideQ" [1, 0, 0x100000000] ⟨0, 0x100000000⟩
  checkRaw 3 "limb_divWideR" [1, 0, 0x100000000] ⟨0, 0⟩
  checkRaw 2 "limb_divWideQ" [2, 7, 3] ⟨0, UInt64.ofNat ((2 * 2 ^ 64 + 7) / 3)⟩
  checkRaw 3 "limb_divWideR" [2, 7, 3] ⟨0, UInt64.ofNat ((2 * 2 ^ 64 + 7) % 3)⟩
  checkRaw 2 "limb_divWideQ" [maxW - 1, maxW, maxW] ⟨0, maxW⟩
  checkRaw 3 "limb_divWideR" [maxW - 1, maxW, maxW] ⟨0, maxW - 1⟩
  -- addCarry64
  checkRaw 4 "limb_addCarryS" [maxW, 0, 1] ⟨0, 0⟩
  checkRaw 5 "limb_addCarryC" [maxW, 0, 1] ⟨0, 1⟩
  checkRaw 4 "limb_addCarryS" [maxW, maxW, 1] ⟨0, maxW⟩
  checkRaw 5 "limb_addCarryC" [maxW, maxW, 1] ⟨0, 1⟩
  checkRaw 4 "limb_addCarryS" [maxW, 0, 0] ⟨0, maxW⟩
  checkRaw 5 "limb_addCarryC" [maxW, 0, 0] ⟨0, 0⟩
  checkRaw 4 "limb_addCarryS" [10, 20, 7] ⟨0, 31⟩
  checkRaw 5 "limb_addCarryC" [10, 20, 7] ⟨0, 0⟩
  -- subBorrow64
  checkRaw 6 "limb_subBorrowD" [0, 0, 1] ⟨0, maxW⟩
  checkRaw 7 "limb_subBorrowB" [0, 0, 1] ⟨0, 1⟩
  checkRaw 6 "limb_subBorrowD" [0, 1, 0] ⟨0, maxW⟩
  checkRaw 7 "limb_subBorrowB" [0, 1, 0] ⟨0, 1⟩
  checkRaw 6 "limb_subBorrowD" [1, 1, 1] ⟨0, maxW⟩
  checkRaw 7 "limb_subBorrowB" [1, 1, 1] ⟨0, 1⟩
  checkRaw 6 "limb_subBorrowD" [10, 3, 1] ⟨0, 6⟩
  checkRaw 7 "limb_subBorrowB" [10, 3, 1] ⟨0, 0⟩
  checkRaw 6 "limb_subBorrowD" [0, maxW, 1] ⟨0, 0⟩
  checkRaw 7 "limb_subBorrowB" [0, maxW, 1] ⟨0, 1⟩
  -- bsr64
  checkRaw 8 "limb_bsr64" [1] ⟨0, 0⟩
  checkRaw 8 "limb_bsr64" [2] ⟨0, 1⟩
  checkRaw 8 "limb_bsr64" [0x80000000] ⟨0, 31⟩
  checkRaw 8 "limb_bsr64" [0x8000000000000000] ⟨0, 63⟩
  checkRaw 8 "limb_bsr64" [maxW] ⟨0, 63⟩
  -- brOvf .mulOvf
  checkRaw 9 "limb_mulOvf" [0xffffffff, 0xffffffff] ⟨0, 0xffffffff * 0xffffffff⟩
  checkRaw 9 "limb_mulOvf" [0x100000000, 0x100000000] ⟨3, 0⟩
  checkRaw 9 "limb_mulOvf" [maxW, 1] ⟨0, maxW⟩
  checkRaw 9 "limb_mulOvf" [maxW, 2] ⟨3, 0⟩
  return #[s!"limb primitives (mulWide64, divWide64, addCarry64, subBorrow64, bsr64, brOvf.mulOvf): 39 vectors agree across Lir/Xv/Xl/Typed/Bytes; text {art.encoded.text.size} bytes"]

/-! ### DR2 Stage W2: Raw 64-bit `UInt64`, `box64`/`unbox64`, `nscalar > 0`, Zero-Alloc Limb Pairs, and K4 Blake3 Kernel -/

private def countLimbs (fn : Lir.Func) : Nat :=
  fn.blocks.foldl (fun acc b => acc + b.body.foldl (fun c s => match s with | .limb .. => c + 1 | _ => c) 0) 0

private def countHeapFails (fn : Lir.Func) : Nat :=
  fn.blocks.foldl (fun acc b => acc + match b.term with | .fail .heap => 1 | _ => 0) 0

private def mkW2Prog (fs : List (List (Nat × Fir.Rep) × Fir.Code)) (exports : List Nat) : FProgram :=
  let funs := fs.zipIdx.map fun ((ps, body), i) =>
    (i, ({ key := .const i [], params := ps, body, vars := 128, joins := 16 } : Fir.Fun))
  { funs := Src.NatMap.ofList funs, size := fs.length, exports, ctors := Cases.ctors, known := Cases.known }

private def mkFunCert (params : List (Nat × Fir.Rep)) (ret : Fir.Rep)
    (extraVars : List (Nat × Fir.Rep) := []) (joins : List (Nat × List Fir.Rep) := []) : Fir.Rep.FunCert :=
  { params := params.map (·.2)
    ret
    vars := Src.NatMap.ofList (params ++ extraVars)
    joins := Src.NatMap.ofList joins }

private def compileRep (label : String) (F : FProgram) (cert : Fir.Rep.Cert) :
    IO (Compiled × X86.Memory × Machines) := do
  unless Fir.Rep.check F cert do
    throw (IO.userError s!"{label}: Fir.Rep.check refused certificate")
  let C := Cases.cfgOf F
  let l ← IO.ofExcept ((Rt.lowerRep {} cert C).mapError fun e => s!"{label}: {e.render}")
  match l.program.check with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{label}: Lir not WellFormed: {e}")
  let (xv, _) ← IO.ofExcept ((Xv.Select.run l.program).mapError fun e => s!"{label} select: {e.form}: {e.reason}")
  match xv.check with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{label}: Xv not WellFormed: {e}")
  let alloc ← IO.ofExcept ((Xv.Alloc.run {} xv).mapError (s!"{label} alloc: " ++ ·))
  match Xv.Validate.run {} xv alloc.outs with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"{label}: Validate refused: {e}")
  let argReps (fn : Lir.FunId) : Option (List Xv.Stacking.ArgRep) :=
    if fn == l.init then some [.word, .word]
    else (cert.funs.get? fn).map fun fc => fc.params.map fun r => if r == .word then .word else .nat
  let art ← IO.ofExcept ((Backend.emit alloc.program { provenance := testProvenance, reps := argReps }).mapError toString)
  let c : Compiled := { lir := l, xv, xl := alloc.program, artifact := art }
  let mem ← IO.ofExcept (initRegion l)
  let ms ← IO.ofExcept (initMachines c)
  pure (c, mem, ms)

private def checkRepRaw (a : Assert) (c : Compiled) (mem : X86.Memory) (ms : Machines)
    (label : String) (fn : Nat) (args : List Word) (want : Word) : IO Unit := do
  let some sym := c.lir.roots.lookup fn | throw (IO.userError s!"{label}: f{fn} is not exported")
  let rl := Lir.eval { c.lir.program with main := fn } 500000 args mem ctx
  let rx := Xv.eval { c.xv with main := fn } 500000 args mem ctx
  let rxl := Xv.Xl.eval { c.xl with main := fn } {} 500000 args mem ctx
  let wantExit : Exit := ⟨0, want⟩
  expect a (IxCCTests.Backend.expected rl == some wantExit)
    s!"{label} {args}: Lir {repr (IxCCTests.Backend.expected rl)}, expected {repr wantExit}"
  expect a (IxCCTests.Backend.expected rx == some wantExit) s!"{label} {args}: Xv mismatch"
  expect a (IxCCTests.Backend.expected rxl == some wantExit) s!"{label} {args}: Xl mismatch"
  let (em, _) ← IO.ofExcept ((runExport c sym args ms).mapError (s!"{label} {args}: " ++ ·))
  expect a (em == wantExit) s!"{label} {args}: machines {repr em}, expected {repr wantExit}"

private def checkRepNative (a : Assert) (t : Native.Tools) (c : Compiled) (name : String)
    (fn : Nat) (cases : List (List Word × Word)) (assertZeroAlloc : Bool := false) : IO Nat := do
  let some sym := c.lir.roots.lookup fn | throw (IO.userError s!"{name}: f{fn} is not exported")
  let exe ← Native.link t name c.artifact.object sym
  let lines ← Native.run exe { dump := assertZeroAlloc } (cases.map fun (xs, _) => xs.map (·.toNat))
  for ((xs, want), l) in cases.zip lines do
    expect a l.ok s!"{name} {xs}: callee-saved register or rsp changed natively"
    expect a (l.status == 0) s!"{name} {xs}: native status {l.status}, expected 0"
    expect a (l.value == want) s!"{name} {xs}: native value {l.value}, expected {want}"
    if assertZeroAlloc then
      match l.dump with
      | some d => expect a (d.bump == d.start) s!"{name} {xs}: allocated {d.bump - d.start} bytes, expected 0"
      | none => expect a false s!"{name} {xs}: missing heap dump"
  pure lines.length

/-- Reference BLAKE3 32-bit right rotate and quarter-round `g` (from `benchmarks/fixtures/blake3/Blake3.lean`). -/
private def b3Rotr32 (w c : UInt32) : UInt32 := (w >>> c) ||| (w <<< (32 - c))

private def b3Quarter (va vb vc vd mx my : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let va := va + vb + mx
  let vd := b3Rotr32 (vd ^^^ va) 16
  let vc := vc + vd
  let vb := b3Rotr32 (vb ^^^ vc) 12
  let va := va + vb + my
  let vd := b3Rotr32 (vd ^^^ va) 8
  let vc := vc + vd
  let vb := b3Rotr32 (vb ^^^ vc) 7
  (va, vb, vc, vd)

/-- Reference 64-bit packed BLAKE3 quarter-round + 64-bit counter split (matching `w2Blake3`). -/
private def b3KernelRef (pAB pCD pM counter : UInt64) : UInt64 :=
  let va0 := pAB.toUInt32
  let vb0 := (pAB >>> 32).toUInt32
  let vc0 := pCD.toUInt32
  let vd0 := (pCD >>> 32).toUInt32
  let mx := pM.toUInt32 ^^^ counter.toUInt32
  let my := (pM >>> 32).toUInt32 ^^^ (counter >>> 32).toUInt32
  let (va, vb, vc, vd) := b3Quarter va0 vb0 vc0 vd0 mx my
  let lo := (va ^^^ vc).toUInt64
  let hi := (vb ^^^ vd).toUInt64
  lo ||| (hi <<< 32)

/-- Reference 128-bit multiply-accumulate loop (`iters` steps of `mulWide64` + two `addCarry64`s). -/
private def mulAddLoopRef (iters a b accLo accHi : UInt64) : UInt64 := Id.run do
  let mut k := iters
  let mut lo := accLo
  let mut hi := accHi
  while k != 0 do
    let (pLo, pHi) := IxCC.BigNat.mulWide64 a b
    let (lo', c1) := IxCC.BigNat.addCarry64 lo pLo false
    let (hi', _) := IxCC.BigNat.addCarry64 hi pHi c1
    lo := lo'
    hi := hi'
    k := k - 1
  return lo ^^^ hi

/-- End-to-end DR2 Stage W2 test suite: full `[0, 2^64)` raw `UInt64` (zero `natOverflow`),
`box64`/`unbox64`, `CtorInfo.nscalar > 0` scalar tails + `Rt.readbackWord`, all 5 hardware limb
primitives & zero-alloc fused pair loop (asserting 1 `Lir.Stmt.limb` per pair and 0 heap bytes
allocated natively), and K4 `Blake3` compression kernel across Lir/Xv/Xl/Typed/Bytes + Native Xeon. -/
def stageW2 (a : Assert) (tools : Option Native.Tools) : IO (Array String) := do
  let v := Cases.v
  let n := Cases.n
  let maxW : Word := 0xFFFFFFFFFFFFFFFF
  let hiBit : Word := 0x8000000000000000
  let loMax : Word := 0x7FFFFFFFFFFFFFFF
  let mut nativeRuns := 0
  let mut modelRuns := 0

  -- 1. Full [0, 2^64) raw 64-bit UInt64 operations + raw unsigned comparisons (ZERO natOverflow)
  let rawBinOps : List (Src.WordOp × (Word → Word → Word)) := [
    (.add, (· + ·)), (.sub, (· - ·)), (.mul, (· * ·)),
    (.div, (· / ·)), (.mod, (· % ·)),
    (.land, (· &&& ·)), (.lor, (· ||| ·)), (.xor, (· ^^^ ·)),
    (.shiftLeft, (· <<< ·)), (.shiftRight, (· >>> ·))
  ]
  let rawUnOps : List (Src.WordOp × (Word → Word)) := [
    (.complement, (~~~ ·)), (.neg, (- ·)), (.ofNat, id), (.toNat, id),
    (.convert .w8, fun x => x.toUInt8.toUInt64),
    (.convert .w16, fun x => x.toUInt16.toUInt64),
    (.convert .w32, fun x => x.toUInt32.toUInt64),
    (.convert .w64, id)
  ]
  let rawBinFuns : List (List (Nat × Fir.Rep) × Fir.Code) := rawBinOps.map fun (op, _) =>
    ([(0, .word), (1, .word)], .bind 10 (.prim (.word .w64 op) [v 0, v 1]) (.ret (v 10)))
  let rawUnFuns : List (List (Nat × Fir.Rep) × Fir.Code) := rawUnOps.map fun (op, _) =>
    ([(0, .word)], .bind 10 (.prim (.word .w64 op) [v 0]) (.ret (v 10)))
  -- Fused raw 64-bit comparisons (natBeq / natBle / natBlt) returning raw 1 / 0
  let rawCmpFuns : List (List (Nat × Fir.Rep) × Fir.Code) :=
    ([Lam.Prim.natBeq, Lam.Prim.natBle, Lam.Prim.natBlt]).map fun cmp =>
      ([(0, .word), (1, .word)],
        .bind 10 (.prim cmp [v 0, v 1])
          (.case 10 [.mk Cases.bF (.ret (n 0)), .mk Cases.bT (.ret (n 1))] none))
  let allRawFuns := rawBinFuns ++ rawUnFuns ++ rawCmpFuns
  let rawProg := mkW2Prog allRawFuns (List.range allRawFuns.length)
  let rawCertFuns : List (Nat × Fir.Rep.FunCert) :=
    (rawBinFuns.zipIdx.map fun (_, i) => (i, mkFunCert [(0, .word), (1, .word)] .word [(10, .word)])) ++
    (rawUnFuns.zipIdx.map fun (_, i) => (rawBinFuns.length + i, mkFunCert [(0, .word)] .word [(10, .word)])) ++
    (rawCmpFuns.zipIdx.map fun (_, i) =>
      (rawBinFuns.length + rawUnFuns.length + i, mkFunCert [(0, .word), (1, .word)] .word [(10, .tobj)]))
  let rawCert : Fir.Rep.Cert := { funs := Src.NatMap.ofList rawCertFuns }
  -- Verify Fir.Rep.infer also produces a sound certificate on rawProg
  let inferredRaw := Fir.Rep.infer rawProg
  expect a (Fir.Rep.check rawProg inferredRaw) "stageW2: Fir.Rep.infer produced unchecked cert"
  let (cRaw, memRaw, msRaw) ← compileRep "w2RawOps" rawProg rawCert
  let rawPairs : List (Word × Word) := [
    (0, 0), (0, 1), (1, 0), (loMax, 1), (loMax, loMax), (hiBit, 0), (hiBit, 1),
    (hiBit, hiBit), (maxW, 0), (maxW, 1), (maxW, 63), (maxW, 64), (maxW, maxW),
    (0xFEDCBA9876543210, 0x0123456789ABCDEF)
  ]
  let rawSingles : List Word := [0, 1, 255, 65536, 0xFFFFFFFF, loMax, hiBit, maxW - 1, maxW]
  for ((op, fnRef), idx) in rawBinOps.zipIdx do
    for (x, y) in rawPairs do
      checkRepRaw a cRaw memRaw msRaw s!"w2_{op.leanName .w64}" idx [x, y] (fnRef x y)
      modelRuns := modelRuns + 1
    if let some t := tools then
      nativeRuns := nativeRuns + (← checkRepNative a t cRaw s!"w2_bin_{idx}" idx
        (rawPairs.map fun (x, y) => ([x, y], fnRef x y)))
  for ((op, fnRef), idx) in rawUnOps.zipIdx do
    let fi := rawBinOps.length + idx
    for x in rawSingles do
      checkRepRaw a cRaw memRaw msRaw s!"w2_{op.leanName .w64}" fi [x] (fnRef x)
      modelRuns := modelRuns + 1
    if let some t := tools then
      nativeRuns := nativeRuns + (← checkRepNative a t cRaw s!"w2_un_{idx}" fi
        (rawSingles.map fun x => ([x], fnRef x)))
  let cmpRefs : List (Word → Word → Word) := [
    fun x y => if x == y then 1 else 0,
    fun x y => if x ≤ y then 1 else 0,
    fun x y => if x < y then 1 else 0
  ]
  for (fnRef, idx) in cmpRefs.zipIdx do
    let fi := rawBinOps.length + rawUnOps.length + idx
    for (x, y) in rawPairs do
      checkRepRaw a cRaw memRaw msRaw s!"w2_cmp_{idx}" fi [x, y] (fnRef x y)
      modelRuns := modelRuns + 1
    if let some t := tools then
      nativeRuns := nativeRuns + (← checkRepNative a t cRaw s!"w2_cmp_{idx}" fi
        (rawPairs.map fun (x, y) => ([x, y], fnRef x y)))

  -- 2. box64 / unbox64 uniform boundary + CtorInfo.nscalar > 0 scalar tails + Rt.readbackWord
  let pairScInfo := Fir.Rep.CtorInfo.withScalars (Cases.info Cases.pairK) 0 2
  let nodeScInfo := Fir.Rep.CtorInfo.withScalars (Cases.info Cases.nodeK) 1 2
  let boxProg := mkW2Prog [
    -- f0: box64 -> polyId -> unbox64 round-trip across [0, 2^64)
    ([(0, .word)], .bind 10 (.call 1 [v 0]) (.bind 11 (.prim (.word .w64 .toNat) [v 10]) (.ret (v 11)))),
    -- f1: polymorphic identity (.obj -> .obj)
    ([(0, .obj)], .ret (v 0)),
    -- f2: box64 returning a 1-scalar-word cell (.word -> .obj)
    ([(0, .word)], .ret (v 0)),
    -- f3: allocate pure scalar-tail cell (nobj = 0, nscalar = 2)
    ([(0, .word), (1, .word)], .bind 10 (.ctor pairScInfo [v 0, v 1]) (.ret (v 10))),
    -- f4: allocate & project both scalar fields of nscalar = 2 cell, XORing raw words
    ([(0, .word), (1, .word)],
      .bind 10 (.ctor pairScInfo [v 0, v 1])
        (.bind 11 (.proj 10 Cases.pairK 0)
          (.bind 12 (.proj 10 Cases.pairK 1)
            (.bind 13 (.prim (.word .w64 .xor) [v 11, v 12]) (.ret (v 13)))))),
    -- f5: mixed cell (nobj = 1 tagged Nat, nscalar = 2 raw 64-bit words)
    ([(0, .tobj), (1, .word), (2, .word)],
      .bind 10 (.ctor nodeScInfo [v 0, v 1, v 2]) (.ret (v 10)))
  ] [0, 2, 3, 4, 5]
  let boxCert : Fir.Rep.Cert := {
    funs := Src.NatMap.ofList [
      (0, mkFunCert [(0, .word)] .word [(10, .obj), (11, .word)]),
      (1, mkFunCert [(0, .obj)] .obj),
      (2, mkFunCert [(0, .word)] .obj),
      (3, mkFunCert [(0, .word), (1, .word)] .obj [(10, .obj)]),
      (4, mkFunCert [(0, .word), (1, .word)] .word [(10, .obj), (11, .word), (12, .word), (13, .word)]),
      (5, mkFunCert [(0, .tobj), (1, .word), (2, .word)] .obj [(10, .obj)])
    ]
    ctors := [
      { key := Cases.pairK, nobj := 0, nscalar := 2, objRep := .obj },
      { key := Cases.nodeK, nobj := 1, nscalar := 2, objRep := .tobj }
    ]
  }
  let (cBox, memBox, msBox) ← compileRep "w2BoxScalar" boxProg boxCert
  let boxVals : List Word := [0, 1, 42, loMax, hiBit, maxW - 1, maxW]
  for x in boxVals do
    checkRepRaw a cBox memBox msBox "w2_box_roundtrip" 0 [x] x
    modelRuns := modelRuns + 1
    -- Readback boxed 1-scalar-word cell at Lir
    match Lir.eval { cBox.lir.program with main := 2 } 50000 [x] memBox ctx with
    | .ok ([ptr], m') =>
      let obs := Rt.readbackWord Cases.sig 1000 m' .boxedWord64 ptr
      expect a (obs == some (.word x)) s!"w2_box_readback {x}: got {repr obs}"
      modelRuns := modelRuns + 1
    | other => expect a false s!"w2_box_readback {x}: Lir {lirOutcome other}"
  for (x, y) in [(0, maxW), (loMax, hiBit), (hiBit, maxW), (0x123456789ABCDEF0, 0xFEDCBA9876543210)] do
    checkRepRaw a cBox memBox msBox "w2_scalar_proj" 4 [x, y] (x ^^^ y)
    modelRuns := modelRuns + 1
    match Lir.eval { cBox.lir.program with main := 3 } 50000 [x, y] memBox ctx with
    | .ok ([ptr], m') =>
      let ty := Rt.WordTy.scalarCell 0 [] 2
      let obs := Rt.readbackWord Cases.sig 1000 m' ty ptr
      expect a (obs == some (.ctor 0 [.word x, .word y])) s!"w2_scalar_cell_readback: got {repr obs}"
      modelRuns := modelRuns + 1
    | other => expect a false s!"w2_scalar_cell_readback: Lir {lirOutcome other}"
    match Lir.eval { cBox.lir.program with main := 5 } 50000 [tag 77, x, y] memBox ctx with
    | .ok ([ptr], m') =>
      let ty := Rt.WordTy.scalarCell 1 [.nat] 2
      let obs := Rt.readbackWord Cases.sig 1000 m' ty ptr
      expect a (obs == some (.ctor 1 [.nat 77, .word x, .word y])) s!"w2_mixed_cell_readback: got {repr obs}"
      modelRuns := modelRuns + 1
    | other => expect a false s!"w2_mixed_cell_readback: Lir {lirOutcome other}"
  if let some t := tools then
    nativeRuns := nativeRuns + (← checkRepNative a t cBox "w2_box_rt" 0 (boxVals.map fun x => ([x], x)))
    nativeRuns := nativeRuns + (← checkRepNative a t cBox "w2_sc_proj" 4
      ([(0, maxW), (loMax, hiBit), (hiBit, maxW)].map fun (x, y) => ([x, y], x ^^^ y)))
    -- Native readback of boxed 1-scalar-word cells and scalar-tail cells from real Xeon heap dumps
    let some symBox := cBox.lir.roots.lookup 2 | throw (IO.userError "w2_box: missing root 2")
    let exeBox ← Native.link t "w2_box_cell" cBox.artifact.object symBox
    let linesBox ← Native.run exeBox { dump := true } (boxVals.map fun x => [x.toNat])
    for (x, l) in boxVals.zip linesBox do
      expect a (l.ok && l.status == 0) s!"w2_box_cell {x}: native status {l.status}"
      let obs := l.dump.bind fun d => Rt.readbackWord Cases.sig 1000 (d.memory (1 <<< 24)) .boxedWord64 l.value
      expect a (obs == some (.word x)) s!"w2_box_cell {x}: native readback {repr obs}"
      nativeRuns := nativeRuns + 1
    let some symMix := cBox.lir.roots.lookup 5 | throw (IO.userError "w2_mix: missing root 5")
    let exeMix ← Native.link t "w2_mixed_cell" cBox.artifact.object symMix
    let mixInputs : List (Nat × Word × Word) := [(77, hiBit, maxW), (0, loMax, 0xCAFEBABE12345678)]
    let linesMix ← Native.run exeMix { dump := true } (mixInputs.map fun (k, x, y) => [k, x.toNat, y.toNat])
    for ((k, x, y), l) in mixInputs.zip linesMix do
      expect a (l.ok && l.status == 0) s!"w2_mixed_cell: native status {l.status}"
      let ty := Rt.WordTy.scalarCell 1 [.nat] 2
      let obs := l.dump.bind fun d => Rt.readbackWord Cases.sig 1000 (d.memory (1 <<< 24)) ty l.value
      expect a (obs == some (.ctor 1 [.nat k, .word x, .word y])) s!"w2_mixed_cell: native readback {repr obs}"
      nativeRuns := nativeRuns + 1

  -- 3. All 5 hardware limb primitives + zero-alloc fused pair loop (asserting 1 limb stmt/pair & 0 heap bytes!)
  let limbProg := mkW2Prog [
    -- f0: clz64
    ([(0, .word)], .bind 10 (.prim (.word .w64 .clz64) [v 0]) (.ret (v 10))),
    -- f1: fused mulWide64 (lo ^^^ hi)
    ([(0, .word), (1, .word)],
      .bind 10 (.prim (.word .w64 .mulWideLo) [v 0, v 1])
        (.bind 11 (.prim (.word .w64 .mulWideHi) [v 0, v 1])
          (.bind 12 (.prim (.word .w64 .xor) [v 10, v 11]) (.ret (v 12))))),
    -- f2: fused divWide64 (q ^^^ r)
    ([(0, .word), (1, .word), (2, .word)],
      .bind 10 (.prim (.word .w64 .divWideQ) [v 0, v 1, v 2])
        (.bind 11 (.prim (.word .w64 .divWideR) [v 0, v 1, v 2])
          (.bind 12 (.prim (.word .w64 .xor) [v 10, v 11]) (.ret (v 12))))),
    -- f3: fused addCarry64 (lo + co)
    ([(0, .word), (1, .word), (2, .word)],
      .bind 10 (.prim (.word .w64 .addCarryLo) [v 0, v 1, v 2])
        (.bind 11 (.prim (.word .w64 .addCarryOut) [v 0, v 1, v 2])
          (.bind 12 (.prim (.word .w64 .add) [v 10, v 11]) (.ret (v 12))))),
    -- f4: fused subBorrow64 (lo + bo)
    ([(0, .word), (1, .word), (2, .word)],
      .bind 10 (.prim (.word .w64 .subBorrowLo) [v 0, v 1, v 2])
        (.bind 11 (.prim (.word .w64 .subBorrowOut) [v 0, v 1, v 2])
          (.bind 12 (.prim (.word .w64 .add) [v 10, v 11]) (.ret (v 12))))),
    -- f5: zero-alloc 128-bit multiply-accumulate loop (iters, a, b, accLo, accHi)
    ([(0, .word), (1, .word), (2, .word), (3, .word), (4, .word)],
      .jp 0 [10, 11, 12] true
        (.bind 20 (.prim .natBeq [v 10, n 0])
          (.case 20 [
            .mk Cases.bT (.bind 21 (.prim (.word .w64 .xor) [v 11, v 12]) (.ret (v 21))),
            .mk Cases.bF
              (.bind 22 (.prim (.word .w64 .mulWideLo) [v 1, v 2])
                (.bind 23 (.prim (.word .w64 .mulWideHi) [v 1, v 2])
                  (.bind 24 (.prim (.word .w64 .addCarryLo) [v 11, v 22, n 0])
                    (.bind 25 (.prim (.word .w64 .addCarryOut) [v 11, v 22, n 0])
                      (.bind 26 (.prim (.word .w64 .addCarryLo) [v 12, v 23, v 25])
                        (.bind 27 (.prim (.word .w64 .addCarryOut) [v 12, v 23, v 25])
                          (.bind 28 (.prim (.word .w64 .sub) [v 10, n 1])
                            (.jmp 0 [v 28, v 24, v 26]))))))))
          ] none))
        (.jmp 0 [v 0, v 3, v 4]))
  ] [0, 1, 2, 3, 4, 5]
  let limbCert : Fir.Rep.Cert := {
    funs := Src.NatMap.ofList [
      (0, mkFunCert [(0, .word)] .word [(10, .word)]),
      (1, mkFunCert [(0, .word), (1, .word)] .word [(10, .word), (11, .word), (12, .word)]),
      (2, mkFunCert [(0, .word), (1, .word), (2, .word)] .word [(10, .word), (11, .word), (12, .word)]),
      (3, mkFunCert [(0, .word), (1, .word), (2, .word)] .word [(10, .word), (11, .word), (12, .word)]),
      (4, mkFunCert [(0, .word), (1, .word), (2, .word)] .word [(10, .word), (11, .word), (12, .word)]),
      (5, mkFunCert [(0, .word), (1, .word), (2, .word), (3, .word), (4, .word)] .word
        [(10, .word), (11, .word), (12, .word), (20, .tobj), (21, .word), (22, .word), (23, .word),
         (24, .word), (25, .word), (26, .word), (27, .word), (28, .word)]
        [(0, [.word, .word, .word])])
    ]
  }
  let (cLimb, memLimb, msLimb) ← compileRep "w2Limbs" limbProg limbCert
  -- Verify zero-alloc limb pair fusion directly in the lowered Lir IR!
  for (fi, wantLimbs) in [(1, 1), (2, 1), (3, 1), (4, 1), (5, 3)] do
    let some fn := cLimb.lir.program.funcs[fi]? | throw (IO.userError s!"w2Limbs: missing f{fi}")
    expect a (countLimbs fn == wantLimbs)
      s!"w2Limbs f{fi}: expected {wantLimbs} fused Lir.Stmt.limb, got {countLimbs fn}"
    expect a (countHeapFails fn == 0)
      s!"w2Limbs f{fi}: expected 0 heap allocations, got {countHeapFails fn} heap-fail blocks"
  let clzCases : List (List Word × Word) :=
    ([0, 1, 2, 0x80000000, loMax, hiBit, maxW]).map fun x => ([x], IxCC.BigNat.clz64 x)
  for (xs, want) in clzCases do
    checkRepRaw a cLimb memLimb msLimb "w2_clz64" 0 xs want; modelRuns := modelRuns + 1
  let mulCases : List (List Word × Word) :=
    ([(0, 0), (maxW, maxW), (hiBit, hiBit), (0x123456789ABCDEF0, 0xFEDCBA9876543210)]).map fun (x, y) =>
      let (lo, hi) := IxCC.BigNat.mulWide64 x y; ([x, y], lo ^^^ hi)
  for (xs, want) in mulCases do
    checkRepRaw a cLimb memLimb msLimb "w2_mulWide" 1 xs want; modelRuns := modelRuns + 1
  let divInputs : List (Word × Word × Word) := [
    (0, maxW, 1), (1, 0, 0x100000000), (2, 7, 3), (maxW - 1, maxW, maxW), (hiBit - 1, maxW, hiBit)
  ]
  let divCases : List (List Word × Word) := divInputs.filterMap fun (hi, lo, d) =>
    if h : hi < d then
      let (q, r) := IxCC.BigNat.divWide64 hi lo d h; some ([hi, lo, d], q ^^^ r)
    else none
  for (xs, want) in divCases do
    checkRepRaw a cLimb memLimb msLimb "w2_divWide" 2 xs want; modelRuns := modelRuns + 1
  let acCases : List (List Word × Word) :=
    ([(maxW, 0, false), (maxW, 0, true), (maxW, maxW, true), (hiBit, hiBit, false)]).map fun (x, y, c) =>
      let (lo, co) := IxCC.BigNat.addCarry64 x y c; ([x, y, UInt64.ofNat c.toNat], lo + UInt64.ofNat co.toNat)
  for (xs, want) in acCases do
    checkRepRaw a cLimb memLimb msLimb "w2_addCarry" 3 xs want; modelRuns := modelRuns + 1
  let sbCases : List (List Word × Word) :=
    ([(0, 0, true), (0, 1, false), (1, 1, true), (hiBit, maxW, true), (maxW, hiBit, false)]).map fun (x, y, b) =>
      let (lo, bo) := IxCC.BigNat.subBorrow64 x y b; ([x, y, UInt64.ofNat b.toNat], lo + UInt64.ofNat bo.toNat)
  for (xs, want) in sbCases do
    checkRepRaw a cLimb memLimb msLimb "w2_subBorrow" 4 xs want; modelRuns := modelRuns + 1
  let loopModelCases : List (List Word × Word) := [
    ([0, maxW, maxW, 11, 22], mulAddLoopRef 0 maxW maxW 11 22),
    ([1, maxW, maxW, 0, 0], mulAddLoopRef 1 maxW maxW 0 0),
    ([8, 0x123456789ABCDEF0, 0xFEDCBA9876543210, hiBit, loMax],
      mulAddLoopRef 8 0x123456789ABCDEF0 0xFEDCBA9876543210 hiBit loMax)
  ]
  for (xs, want) in loopModelCases do
    checkRepRaw a cLimb memLimb msLimb "w2_mulAddLoop" 5 xs want; modelRuns := modelRuns + 1
  if let some t := tools then
    nativeRuns := nativeRuns + (← checkRepNative a t cLimb "w2_clz64" 0 clzCases true)
    nativeRuns := nativeRuns + (← checkRepNative a t cLimb "w2_mulWide" 1 mulCases true)
    nativeRuns := nativeRuns + (← checkRepNative a t cLimb "w2_divWide" 2 divCases true)
    nativeRuns := nativeRuns + (← checkRepNative a t cLimb "w2_addCarry" 3 acCases true)
    nativeRuns := nativeRuns + (← checkRepNative a t cLimb "w2_subBorrow" 4 sbCases true)
    let loopNativeCases := loopModelCases ++ [
      ([1000, maxW, maxW, hiBit, loMax], mulAddLoopRef 1000 maxW maxW hiBit loMax)
    ]
    nativeRuns := nativeRuns + (← checkRepNative a t cLimb "w2_mulAddLoop" 5 loopNativeCases true)

  -- 4. K4 Blake3 32/64-bit compression quarter-round + 64-bit counter split (native Xeon!)
  let w32 (op : Src.WordOp) (args : List Fir.Arg) : Fir.Rhs := .prim (.word .w32 op) args
  let w64 (op : Src.WordOp) (args : List Fir.Arg) : Fir.Rhs := .prim (.word .w64 op) args
  let rotr32Body (dst x rot tmp1 tmp2 : Nat) (k : Fir.Code) : Fir.Code :=
    .bind tmp1 (w32 .shiftRight [v x, n rot])
      (.bind tmp2 (w32 .shiftLeft [v x, n (32 - rot)])
        (.bind dst (w32 .lor [v tmp1, v tmp2]) k))
  let b3Body : Fir.Code :=
    -- Unpack (va, vb) from arg 0, (vc, vd) from arg 1, (mx0, my0) from arg 2, counter from arg 3
    .bind 10 (w64 (.convert .w32) [v 0])
    (.bind 11 (w64 .shiftRight [v 0, n 32])
    (.bind 12 (w64 (.convert .w32) [v 11])
    (.bind 13 (w64 (.convert .w32) [v 1])
    (.bind 14 (w64 .shiftRight [v 1, n 32])
    (.bind 15 (w64 (.convert .w32) [v 14])
    (.bind 16 (w64 (.convert .w32) [v 2])
    (.bind 17 (w64 .shiftRight [v 2, n 32])
    (.bind 18 (w64 (.convert .w32) [v 17])
    (.bind 19 (w64 (.convert .w32) [v 3])
    (.bind 20 (w64 .shiftRight [v 3, n 32])
    (.bind 21 (w64 (.convert .w32) [v 20])
    (.bind 22 (w32 .xor [v 16, v 19])      -- mx = mx0 ^^^ counter.toUInt32
    (.bind 23 (w32 .xor [v 18, v 21])      -- my = my0 ^^^ (counter >>> 32).toUInt32
    -- va = va + vb + mx; vd = rotr32 (vd ^^^ va) 16
    (.bind 24 (w32 .add [v 10, v 12])
    (.bind 25 (w32 .add [v 24, v 22])
    (.bind 26 (w32 .xor [v 15, v 25])
    (rotr32Body 27 26 16 28 29
    -- vc = vc + vd; vb = rotr32 (vb ^^^ vc) 12
    (.bind 30 (w32 .add [v 13, v 27])
    (.bind 31 (w32 .xor [v 12, v 30])
    (rotr32Body 32 31 12 33 34
    -- va = va + vb + my; vd = rotr32 (vd ^^^ va) 8
    (.bind 35 (w32 .add [v 25, v 32])
    (.bind 36 (w32 .add [v 35, v 23])
    (.bind 37 (w32 .xor [v 27, v 36])
    (rotr32Body 38 37 8 39 40
    -- vc = vc + vd; vb = rotr32 (vb ^^^ vc) 7
    (.bind 41 (w32 .add [v 30, v 38])
    (.bind 42 (w32 .xor [v 32, v 41])
    (rotr32Body 43 42 7 44 45
    -- Pack (va ^^^ vc) | ((vb ^^^ vd) <<< 32) as raw 64-bit UInt64
    (.bind 46 (w32 .xor [v 36, v 41])
    (.bind 47 (w32 .xor [v 43, v 38])
    (.bind 48 (w32 (.convert .w64) [v 46])
    (.bind 49 (w32 (.convert .w64) [v 47])
    (.bind 50 (w64 .shiftLeft [v 49, n 32])
    (.bind 51 (w64 .lor [v 48, v 50])
      (.ret (v 51)))))))))))))))))))))))))))))))))))
  let b3Prog := mkW2Prog [([(0, .word), (1, .word), (2, .word), (3, .word)], b3Body)] [0]
  let b3WordVars : List (Nat × Fir.Rep) :=
    [(11, .word), (14, .word), (17, .word), (20, .word), (48, .word), (49, .word), (50, .word), (51, .word)]
  let b3Cert : Fir.Rep.Cert := {
    funs := Src.NatMap.ofList [
      (0, mkFunCert [(0, .word), (1, .word), (2, .word), (3, .word)] .word b3WordVars)
    ]
  }
  let (cB3, memB3, msB3) ← compileRep "w2Blake3" b3Prog b3Cert
  let b3Inputs : List (Word × Word × Word × Word) := [
    -- BLAKE3 IV[0..3] with counter = 0 and counter >= 2^63!
    (0xBB67AE856A09E667, 0xA54FF53A3C6EF372, 0x0302010007060504, 0),
    (0xBB67AE856A09E667, 0xA54FF53A3C6EF372, 0x0302010007060504, 0x8000000000000042),
    (0x9B05688C510E527F, 0x5BE0CD191F83D9AB, 0xFFFFFFFFFFFFFFFF, 0xFEDCBA9876543210),
    (maxW, hiBit, loMax, maxW)
  ]
  let b3Cases := b3Inputs.map fun (a0, b0, c0, d0) => ([a0, b0, c0, d0], b3KernelRef a0 b0 c0 d0)
  for (xs, want) in b3Cases do
    checkRepRaw a cB3 memB3 msB3 "w2_blake3_g" 0 xs want; modelRuns := modelRuns + 1
  if let some t := tools then
    nativeRuns := nativeRuns + (← checkRepNative a t cB3 "w2_blake3_g" 0 b3Cases true)

  return #[s!"stage W2 (raw 64-bit UInt64 [0,2^64), box64/unbox64, nscalar>0 readback, 5 zero-alloc fused limbs, K4 Blake3 kernel): {modelRuns} model runs agree across Lir/Xv/Xl/Typed/Bytes{if tools.isSome then s!"; {nativeRuns} native Xeon runs agree (0 bytes allocated in limb loops!)" else ""}"]

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
    byte steps {r.byteSteps}); {native} native runs agree (the independent decoder and dump readback included)"]

end IxCCTests.Rt.Levels
