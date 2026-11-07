import IxCCTests.Rt.Cases

/-! Planted mutations of `Rt.lower`'s output (M1.F6). Each mutant must be
caught:

* **by `Lir.WellFormed`**, for the structural invariants the backend relies
  on: an edge into the entry, an undefined or twice-defined register, a
  store to the protected context cells, a critical edge, an unreachable
  block, an edge or call of the wrong arity, a displacement beyond i32;
* **by the differential** (`compare` against Cfg, typed readback, the
  primitive oracle, `cx_init`'s block), for well-formed mutants that change
  what the program computes: a `Nat` word off by two, a constructor tag, a
  field offset, swapped switch arms, a missing overflow exit, a forward
  edge made backward (an extra charge), the bump pointer not advanced, a
  truncated subtraction's select swapped, the `Bool` words swapped, and a
  misplaced first object. -/

namespace IxCCTests.Rt.Mutants

open IxCC IxCCTests.Src IxCCTests.Fir IxCCTests.Rt.Cases
open IxCC.Lir (Stmt Rhs Addr Block Func Term Edge)

/-! ## Rewriting a program -/

def mapFuncs (p : Lir.Program) (f : Nat → Func → Func) : Lir.Program :=
  { p with funcs := p.funcs.mapIdx fun i g => f i g }

def mapBlocks (p : Lir.Program) (f : Block → Block) : Lir.Program :=
  mapFuncs p fun _ g => { g with blocks := g.blocks.map f }

def mapStmts (p : Lir.Program) (f : Stmt → Stmt) : Lir.Program :=
  mapBlocks p fun b => { b with body := b.body.map f }

/-- Change the first statement (in function `fi`) that `f` changes. -/
def firstStmt (p : Lir.Program) (fi : Nat) (f : Stmt → Option (List Stmt)) : Option Lir.Program := do
  let g ← p.funcs[fi]?
  let rec go : List (Block × Nat) → Option (Nat × Block)
    | [] => none
    | (b, l) :: rest =>
      let rec inBody : List Stmt → Option (List Stmt)
        | [] => none
        | s :: ss => match f s with
          | some new => some (new ++ ss)
          | none => (inBody ss).map (s :: ·)
      match inBody b.body.toList with
      | some body => some (l, { b with body := body.toArray })
      | none => go rest
  let (l, b) ← go g.blocks.toList.zipIdx
  pure { p with funcs := p.funcs.set! fi { g with blocks := g.blocks.set! l b } }

/-- Change the first terminator (in function `fi`) that `f` changes. -/
def firstTerm (p : Lir.Program) (fi : Nat) (f : Term → Option Term) : Option Lir.Program := do
  let g ← p.funcs[fi]?
  let (b, l) ← g.blocks.toList.zipIdx.find? fun (b, _) => (f b.term).isSome
  let t ← f b.term
  pure { p with funcs := p.funcs.set! fi { g with blocks := g.blocks.set! l { b with term := t } } }

/-- Swap blocks `i` and `j` of function `fi`, renaming every edge. -/
def swapBlocks (p : Lir.Program) (fi i j : Nat) : Option Lir.Program := do
  let g ← p.funcs[fi]?
  let bi ← g.blocks[i]?
  let bj ← g.blocks[j]?
  let rename := fun (l : Nat) => if l == i then j else if l == j then i else l
  let blocks := (g.blocks.set! i bj).set! j bi
  let blocks := blocks.map fun b =>
    { b with term := b.term.setEdges (b.term.edges.map fun e => { e with target := rename e.target }) }
  pure { p with funcs := p.funcs.set! fi { g with blocks } }

def isCtxStore (d : Int) : Stmt → Bool
  | .store _ { base := some .ctx, index := none, disp } _ => disp == d
  | _ => false

/-! ## Well-formedness mutants -/

/-- Mutants of the list program's function (`f2`: a fresh entry, a loop, an
allocation) that `Lir.WellFormed` must reject, with the reason. -/
def intoEntry : Term → Option Term
  | .jump e => if e.target == 1 then some (.jump { e with target := 0 }) else none
  | _ => none

def undefinedUse : Stmt → Option (List Stmt)
  | .assign x (.bin o w _ b) => some [.assign x (.bin o w (.v 9999) b)]
  | _ => none

def twice : Stmt → Option (List Stmt)
  | s@(.assign ..) => some [s, s]
  | _ => none

def toEntrySp : Stmt → Option (List Stmt)
  | .store w { base := some .ctx, index := none, disp := -40 } a => some [.store w { base := some .ctx, disp := -64 } a]
  | _ => none

def bothArms : Term → Option Term
  | .br c w a b t _ => some (.br c w a b t t)
  | _ => none

def extraArg : Term → Option Term
  | .jump e => if e.args.isEmpty then none else some (.jump { e with args := e.args ++ [.imm 1] })
  | _ => none

def dropCallArg : Stmt → Option (List Stmt)
  | .call rs g (_ :: as) => some [.call rs g as]
  | _ => none

def farLoad : Stmt → Option (List Stmt)
  | .assign x (.load w e m) => some [.assign x (.load w e { m with disp := 2 ^ 31 })]
  | _ => none

def wfMutants (p : Lir.Program) : List (String × Option Lir.Program × String) :=
  [("an edge into the entry", firstTerm p 2 intoEntry, "edge to the entry block"),
   ("an undefined register", firstStmt p 2 undefinedUse, "never defined"),
   ("a register defined twice", firstStmt p 2 twice, "defined twice"),
   ("a store to entrySp", firstStmt p 2 toEntrySp, "entrySp or stackLimit"),
   ("a critical edge", firstTerm p 2 bothArms, "critical edge"),
   ("an unreachable block",
      some (mapFuncs p fun i g => if i == 2 then { g with blocks := g.blocks.push { term := .trap } } else g),
      "unreachable blocks"),
   ("an edge of the wrong arity", firstTerm p 2 extraArg, "arguments for"),
   ("a call of the wrong arity", firstStmt p 3 dropCallArg, "arguments for"),
   ("a displacement beyond i32", firstStmt p 2 farLoad, "does not fit i32")]

/-! ## Semantic mutants -/

/-- Whether a check throws: the mutant is caught. -/
def caught (check : Assert → IO Unit) : IO Bool := do
  let a ← IO.mkRef 0
  try check a; pure false catch _ => pure true

/-- Compare a mutated program with Cfg on the given runs and read the
results back. -/
def differs (C : CProgram) (l : IxCC.Rt.Lowered) (p : Lir.Program)
    (runs : List (Nat × List Nat × Option Rt.FoTy)) : IO Bool :=
  -- a semantic mutant must be well formed, so only the differential can catch it
  if !p.wellFormed then pure false else caught fun a => do
  let l := { l with program := p }
  let m ← IO.ofExcept (initRegion l)
  for (f, xs, ty) in runs do
    let _ ← compare a (run C l m f xs ty "mutant") 100000 {}
    if let some ty := ty then
      let want ← match ← runCfg .immortal C 100000 f xs with
        | .ok (v, H) => pure (H.readback v)
        | _ => pure none
      let got ← lirObs l m f xs ty
      expect a (got == want) "readback differs"

/-- A primitive program's mutant against `Prim.sem` at the boundaries. -/
def primDiffers (p : Lam.Prim) (mutate : Lir.Program → Option Lir.Program) : IO Bool := do
  let (l, m) ← lirOf (cfgOf (primProg p [none, none] false))
  let some q := mutate l.program | pure false
  if !q.wellFormed then return false
  let l := { l with program := q }
  caught fun a => do
    for x in values do
      for y in secondValues p do
        let r ← runLir l 0 1000 [x, y] m
        expect a (outcomeWord r == some (expected p [x, y])) "differs"

def semMutants (vals : CProgram × IxCC.Rt.Lowered) : List (String × IO Bool) :=
  let (C, l) := vals
  let p := l.program
  let runs := cases.map fun (f, xs, ty, _) => (f, xs, some ty)
  [("a Nat word off by two",
      differs C l (mapBlocks p fun b => { b with term := match b.term with
        | .ret [.imm w] => if w % 2 == 1 && w > 1 then .ret [.imm (w + 2)] else b.term
        | t => t }) runs),
   ("a constructor tag", differs C l (mapStmts p fun
      | .store .w32 m (.imm w) => if m.disp == 0 then .store .w32 m (.imm (w + 65536)) else .store .w32 m (.imm w)
      | s => s) runs),
   ("a field offset", differs C l (mapStmts p fun
      | .store w m a => if m.disp == 8 && m.base != some .ctx then .store w { m with disp := 16 } a else .store w m a
      | s => s) runs),
   ("swapped switch arms",
      match firstTerm p 1 fun | .br .eq w a (.imm 1) t f => some (.br .eq w a (.imm 1) f t) | _ => none with
      | some q => differs C l q runs
      | none => pure false),
   ("a missing overflow exit", primDiffers .natAdd fun q =>
      some (mapBlocks q fun b => if b.term == .fail .natOverflow then { b with term := .ret [.imm 1] } else b)),
   ("a forward edge made backward",
      -- f3 (sum): swapping a block with the next one it jumps to turns
      -- that edge backward (one more charge on every pass)
      let f3 := (p.funcs[3]?).map (·.blocks.toList) |>.getD []
      match (f3.zipIdx.find? fun (b, l) => l ≥ 1 && b.term.succs.contains (l + 1)).bind
          fun (_, l) => swapBlocks p 3 l (l + 1) with
      | some q => differs C l q runs
      | none => pure false),
   ("the bump pointer not advanced", differs C l (mapBlocks p fun b =>
      { b with body := b.body.filter (!isCtxStore IxCC.Rt.bumpOff ·) }) runs),
   ("natSub's select swapped", primDiffers .natSub fun q => some (mapStmts q fun
      | .assign x (.select .ult w a b t f) => .assign x (.select .ult w a b f t)
      | s => s)),
   ("the Bool words swapped", primDiffers .natBle fun q => some (mapStmts q fun
      | .assign x (.select c w a b t f) => .assign x (.select c w a b f t)
      | s => s)),
   ("a misplaced first object", caught fun _ => do
      let q := mapFuncs p fun i g => if i == l.init then
        { g with blocks := g.blocks.map fun b => { b with body := b.body.map fun
          | .assign x (.addr m) => if m.disp == 703 then .assign x (.addr { m with disp := 711 }) else .assign x (.addr m)
          | s => s } } else g
      let _ ← IO.ofExcept (initRegion { l with program := q })
      pure ())]

def run (a : Assert) : IO (Array String) := do
  let C := cfgOf values'
  let (l, _) ← lirOf C
  let mut wf := 0
  for (label, q, why) in wfMutants l.program do
    match q with
    | none => expect a false s!"mutant {label}: no site"
    | some q =>
      match q.check with
      | .error e => expect a ((e.splitOn why).length > 1) s!"mutant {label}: rejected for {e}, expected {why}"
      | .ok () => expect a false s!"mutant {label}: accepted by Lir.WellFormed"
      wf := wf + 1
  let mut sem := 0
  for (label, detect) in semMutants (C, l) do
    expect a (← detect) s!"mutant {label}: not caught by the differential"
    sem := sem + 1
  return #[s!"{wf} mutants rejected by Lir.WellFormed, {sem} caught by the differential"]

end IxCCTests.Rt.Mutants
