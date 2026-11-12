import IxCCTests.Rt.Mutants
import IxCCTests.Rt.Machine

/-! The fixed-width word primitives (stage W1) through `Rt.lower`:

* **boundaries**: every primitive operation of every width (`WordOp.primitives`), as a Fir
  program with its operands as variables or a literal in either position, lowered and run at
  Lir on every pair of boundary numbers, against `WordOp.eval` directly (not `Lam.Prim.sem`): the
  tagged word of `eval`'s number below `2^63`, `fail natOverflow` at or above it (width 64 only);
  out-of-range literals (where SrcEval's rule F6w and the Lam primitive are stuck, so nothing is
  owed) are lowered and checked well formed only;
* **planted mutations** of the lowered programs, each caught on the operations it changes: the
  tagged mask one bit too wide, the shift amount not reduced to the width, width 64's overflow
  check never taken;
* **the backend**: each operation's program through selection, allocation and emission, at Xv,
  Xl, the typed x86 machine and the byte machine, against Lir (`Rt.Machine.check`). -/

namespace IxCCTests.Rt.Words

open IxCC IxCCTests.Src IxCCTests.Rt IxCCTests.Rt.Cases
open IxCC.Src (Width WordOp)
open IxCC.Lir (Stmt Term)

def bnd : Width → List Nat
  | .w8 => [0, 1, 2, 7, 8, 9, 127, 128, 254, 255]
  | .w16 => [0, 1, 15, 16, 17, 255, 256, 32767, 32768, 65534, 65535]
  | .w32 => [0, 1, 31, 32, 33, 65535, 65536, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 2, 2 ^ 32 - 1]
  | .w64 => [0, 1, 2, 63, 64, 65, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 62, 2 ^ 62 + 1, 2 ^ 63 - 2, 2 ^ 63 - 1]

/-- `ofNat`'s argument: any `Nat` with a tagged word. -/
def natBnd : List Nat :=
  [0, 1, 255, 256, 257, 65535, 65536, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 62, 2 ^ 63 - 1]

def firsts (w : Width) (op : WordOp) : List Nat := if op == .ofNat then natBnd else bnd w

/-- Literals at or above the size (lowered only). -/
def outLits (w : Width) : List Nat := if w == .w64 then [] else [w.size, w.size + 1, 2 * w.size - 1]

/-- What Lir must give: the tagged word of `eval`'s number below `2^63`, else `natOverflow`. -/
def want (w : Width) (op : WordOp) (xs : List Nat) : Option Lir.Word :=
  IxCC.Rt.natWord (op.eval w (xs.getD 0 0) (xs.getD 1 0)).val

structure Tally where
  runs : Nat := 0
  overflows : Nat := 0
  programs : Nat := 0
  illFormed : Nat := 0
  wrong : Array String := #[]

def Tally.add (t u : Tally) : Tally :=
  { runs := t.runs + u.runs, overflows := t.overflows + u.overflows, programs := t.programs + u.programs,
    illFormed := t.illFormed + u.illFormed, wrong := t.wrong ++ u.wrong }

def lowered (p : Lam.Prim) (ops : List (Option Nat)) (mutate : Lir.Program → Lir.Program) :
    IO (IxCC.Rt.Lowered × X86.Memory) := do
  let (l, m) ← lirOf (cfgOf (primProg p ops false))
  pure ({ l with program := mutate l.program }, m)

def pairs (w : Width) (op : WordOp) : List (List Nat) :=
  if op.arity == 1 then (firsts w op).map ([·]) else (firsts w op).flatMap fun x => (bnd w).map ([x, ·])

/-- One operation at one width on every boundary case. -/
def opCases (w : Width) (op : WordOp) (mutate : Lir.Program → Lir.Program := id) : IO Tally := do
  let p := Lam.Prim.word w op
  let arity := op.arity
  let mut t : Tally := {}
  let record := fun (t : Tally) (label : String) (xs : List Nat) (r : Lir.Outcome) =>
    let e := want w op xs
    let t := { t with runs := t.runs + 1, overflows := t.overflows + (if e.isNone then 1 else 0) }
    if outcomeWord r == some e then t
    else { t with wrong := t.wrong.push s!"{p.name} {xs} ({label}): Lir {lirOutcome r}, want {e.map (·.toNat)}" }
  let (l, m) ← lowered p (List.replicate arity none) mutate
  t := { t with programs := t.programs + 1, illFormed := t.illFormed + (if l.program.wellFormed then 0 else 1) }
  for xs in pairs w op do
    t := record t "variables" xs (← runLir l 0 1000 xs m)
  for pos in List.range arity do
    let lits := if pos == 0 then firsts w op else bnd w
    for k in lits ++ (if pos == 0 && op == .ofNat then [] else outLits w) do
      let ops := (List.range arity).map fun i => if i == pos then some k else none
      let (l, m) ← lowered p ops mutate
      t := { t with programs := t.programs + 1, illFormed := t.illFormed + (if l.program.wellFormed then 0 else 1) }
      if k ≥ w.size && op != .ofNat then continue
      let others := if arity == 1 then [[]] else if pos == 0 then (bnd w).map ([·]) else (firsts w op).map ([·])
      for ys in others do
        let xs := if pos == 0 then k :: ys else ys ++ [k]
        t := record t s!"literal at {pos}" xs (← runLir l 0 1000 ys m)
  return t

def boundaries (a : Assert) : IO (Array String) := do
  let mut total : Tally := {}
  let mut out := #[]
  for w in Width.all do
    let mut tw : Tally := {}
    for op in WordOp.primitives w do
      tw := tw.add (← opCases w op)
    out := out.push s!"{w.name}: {(WordOp.primitives w).length} operations, {tw.programs} programs, \
      {tw.runs} runs ({tw.overflows} natOverflow)"
    total := total.add tw
  expect a (total.illFormed == 0) s!"{total.illFormed} lowered word programs are not well formed"
  expect a total.wrong.isEmpty s!"word primitives at Lir:\n{"\n".intercalate (total.wrong.extract 0 20).toList}"
  expect a (total.overflows > 0) "width 64 never overflowed"
  return out

/-! ## Planted mutations -/

def mapTerms (p : Lir.Program) (f : Term → Term) : Lir.Program :=
  Mutants.mapBlocks p fun b => { b with term := f b.term }

/-- An immediate operand of an `and` changed. -/
def andImm (from' to : Lir.Word) (p : Lir.Program) : Lir.Program :=
  Mutants.mapStmts p fun
    | .assign x (.bin .and .w64 a (.imm k)) => .assign x (.bin .and .w64 a (.imm (if k == from' then to else k)))
    | s => s

/-- Width 64's overflow check never taken. -/
def noCheck (p : Lir.Program) : Lir.Program :=
  mapTerms p fun
    | .br .ugt w a (.imm 0x7fffffffffffffff) t f => .br .ugt w a (.imm 0xffffffffffffffff) t f
    | t => t

def mutants (a : Assert) : IO (Array String) := do
  let mut out := #[]
  let ms : List (String × (Width → Lir.Program → Lir.Program) × List (Width × WordOp)) :=
    [("the tagged mask one bit too wide", fun w => andImm (IxCC.Rt.Lower.tagMask w) (2 * IxCC.Rt.Lower.tagMask w + 1),
        [(.w8, .add), (.w16, .sub), (.w32, .mul), (.w8, .shiftLeft), (.w16, .neg), (.w8, .ofNat)]),
     ("the shift amount not reduced", fun w => andImm (UInt64.ofNat (w.bits - 1)) 63,
        [(.w8, .shiftLeft), (.w16, .shiftRight), (.w32, .shiftLeft)]),
     ("width 64's overflow check never taken", fun _ => noCheck,
        [(.w64, .mul), (.w64, .shiftLeft), (.w64, .complement), (.w64, .neg), (.w64, .sub), (.w64, .add)])]
  for (name, mk, expected) in ms do
    let mut caught := #[]
    let mut runs := 0
    for w in Width.all do
      for op in WordOp.primitives w do
        let t ← opCases w op (mk w)
        if !t.wrong.isEmpty then caught := caught.push (w, op)
        runs := runs + t.wrong.size
    for (w, op) in expected do
      expect a (caught.contains (w, op)) s!"mutant '{name}' not caught on {op.leanName w}"
    out := out.push s!"'{name}': caught on {caught.size} operations ({runs} runs differ)"
  return out

/-! ## The backend -/

def backend (a : Assert) : IO (Array String) := do
  let mut runs := 0
  let mut typed := 0
  let mut progs := 0
  let mut errs := #[]
  for w in Width.all do
    for op in WordOp.primitives w do
      let p := Lam.Prim.word w op
      let (l, _) ← lirOf (cfgOf (primProg p (List.replicate op.arity none) false))
      match IxCCTests.Rt.Machine.compile l with
      | .error e => errs := errs.push s!"{p.name}: {e}"
      | .ok c =>
        progs := progs + 1
        match IxCCTests.Rt.Machine.initMachines c with
        | .error e => errs := errs.push s!"{p.name}: cx_init {e}"
        | .ok ms =>
          let mut r : IxCCTests.Rt.Machine.Report := {}
          for xs in pairs w op do
            match IxCCTests.Rt.Machine.check c 0 xs 1000 ms r with
            | .ok r' => r := r'
            | .error e => errs := errs.push s!"{p.name} {xs}: {e}"
          runs := runs + r.runs
          typed := typed + r.typedSteps
  expect a errs.isEmpty s!"word programs at the backend levels:\n{"\n".intercalate (errs.extract 0 20).toList}"
  return #[s!"{progs} programs selected, allocated and emitted; {runs} runs agree at Lir, Xv, Xl, typed x86 \
    and bytes ({typed} typed steps)"]

def run (a : Assert) : IO (Array String) := do
  return (← boundaries a) ++ (← mutants a) ++ (← backend a)

end IxCCTests.Rt.Words
