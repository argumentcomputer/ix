import Compilatrix.Xv.Operands
import Compilatrix.Xv.XlSemantics

/-!
# A test allocator: every virtual register in its own home

A stand-in for M1.B4's allocator (`Alloc.allSlots` and the linear scan),
so the backend tests can take Lir through selection, allocation, stacking
and layout before B4 lands. It is test code, unvalidated: the tests check
it by running `Xl.eval` against `Xv.eval` on every program they allocate.

Each virtual register gets a home: a frame slot, or its incoming stack
cell for a parameter past the seventh. Each instruction loads its uses into
registers, runs on registers only, and stores its definitions home:

- operand registers come from `Inst.operands`: a `fixed` operand in its
  register, a `reuse i` definition in use `i`'s register, every other
  operand in a register of its own;
- a call loads its arguments into the convention's locations (stack
  arguments through `r11` into `outArg` cells) and stores its results;
- block parameters become parallel moves through registers: at the end of
  a jumping block, or at the head of a branch target (which has one
  predecessor, since Lir has no critical edges), after the branch's own
  definitions are stored;
- the entry block stores the register parameters home.
-/

namespace CompilatrixTests.Backend.SlotAlloc

open Compilatrix Compilatrix.Lir Compilatrix.Xv

abbrev NatMap (α : Type) := Std.TreeMap Nat α compare

/-- Registers for operands, caller-saved first. -/
def pool : List X86.GPR := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rbx, .r12, .r13, .r14]

/-- Every virtual register a function names, in order of appearance. -/
def vregs (f : Func VReg) : List VReg :=
  f.params ++ f.blocks.toList.flatMap fun b =>
    b.params ++ b.body.toList.flatMap (fun i => i.uses ++ i.defs) ++ b.term.uses ++ b.term.defs ++ b.term.edgeUses

/-- Homes: incoming cells for parameters past the seventh, slots for the rest. -/
def homes (f : Func VReg) : NatMap Loc :=
  let incoming := (f.params.drop Xl.nArgRegs).zipIdx.foldl (fun m (v, i) => m.insert v (Loc.inArg i)) {}
  (vregs f).foldl (init := (incoming, 0)) (fun (m, n) v =>
    if m.contains v then (m, n) else (m.insert v (.slot n), n + 1)) |>.1

structure Ctx where
  homes : NatMap Loc
  /-- Block parameters, by label. -/
  params : NatMap (List VReg)

def Ctx.home (c : Ctx) (v : VReg) : Except String Loc :=
  match c.homes.get? v with
  | some l => pure l
  | none => throw s!"v{v} has no home"

def Ctx.load (c : Ctx) (r : X86.GPR) (v : VReg) : Except String (Inst Loc) := do
  pure (.move (.reg r) (← c.home v))

def Ctx.store (c : Ctx) (v : VReg) (r : X86.GPR) : Except String (Inst Loc) := do
  pure (.move (← c.home v) (.reg r))

/-- A register per operand: fixed ones as required, ties to their use,
the rest distinct and unused by the instruction. -/
def assign (ops : List (Operand VReg)) : Except String (List X86.GPR) := do
  let fixed := ops.filterMap fun o => match o.con with | .fixed r => some r | _ => none
  let (out, _) ← ops.foldlM (init := (([] : List X86.GPR), fixed)) fun (out, used) o =>
    match o.con with
    | .fixed r => pure (out ++ [r], used)
    | .reuse i =>
        match out[i]? with
        | some r => pure (out ++ [r], used)
        | none => throw "a tie to a later operand"
    | .stack => throw "a stack operand outside a call"
    | .any | .reg =>
        match pool.find? (!used.contains ·) with
        | some r => pure (out ++ [r], used ++ [r])
        | none => throw "out of registers"
  pure out

/-- Load uses, run on registers, store definitions. -/
def Ctx.operandsIn (c : Ctx) (ops : List (Operand VReg)) :
    Except String (List X86.GPR × List (Inst Loc) × List (Inst Loc)) := do
  let regs ← assign ops
  let pairs := ops.zip regs
  let loads ← (pairs.filter (·.1.kind == .use)).mapM fun (o, r) => c.load r o.v
  let stores ← (pairs.filter (·.1.kind == .define)).mapM fun (o, r) => c.store o.v r
  pure (regs, loads, stores)

/-- A parallel move of `args` into `params`, through registers. -/
def Ctx.bind (c : Ctx) (params args : List VReg) : Except String (List (Inst Loc)) := do
  unless params.length == args.length do throw "edge arity"
  unless params.length ≤ pool.length do throw "too many block parameters"
  let regs := pool.take params.length
  let loads ← (regs.zip args).mapM fun (r, a) => c.load r a
  let stores ← (params.zip regs).mapM fun (p, r) => c.store p r
  pure (loads ++ stores)

def Ctx.edge (c : Ctx) (e : Edge VReg) : Except String (List (Inst Loc)) :=
  c.bind ((c.params.get? e.target).getD []) e.args

def Ctx.call (c : Ctx) (g : FunId) (args rets : List VReg) : Except String (List (Inst Loc)) := do
  unless rets.length ≤ Xl.nResultRegs do throw "too many results"
  let stack ← (args.drop Xl.nArgRegs).zipIdx.mapM fun (a, j) => do
    pure [← c.load .r11 a, Inst.move (.outArg j) (.reg .r11)]
  let regs ← (args.take Xl.nArgRegs).zipIdx.mapM fun (a, i) =>
    match Lir.Conv.argRegs[i]? with
    | some r => c.load r a
    | none => throw "argument register"
  let results ← rets.zipIdx.mapM fun (v, i) =>
    match Lir.Conv.resultRegs[i]? with
    | some r => c.store v r
    | none => throw "result register"
  pure (stack.flatten ++ regs ++
    [.call g ((List.range args.length).map Xl.argLoc) ((List.range rets.length).filterMap Xl.resultLoc)] ++ results)

def Ctx.inst (c : Ctx) : Inst VReg → Except String (List (Inst Loc))
  | .call g args rets => c.call g args rets
  | .move dst src => do pure [← c.load .rax src, ← c.store dst .rax]
  | i => do
      let (regs, loads, stores) ← c.operandsIn i.operands
      let some i' := i.substitute (regs.map Loc.reg) | throw "substitution failed"
      pure (loads ++ [i'] ++ stores)

/-- A terminator: instructions before it, the terminator, and instructions
for the head of each successor (a branch's definitions, then its edge's
parameter moves). -/
def Ctx.term (c : Ctx) : Term VReg → Except String (List (Inst Loc) × Term Loc × List (Label × List (Inst Loc)))
  | .jmp e => do pure (← c.edge e, .jmp ⟨e.target, []⟩, [])
  | t@(.jcc _ _ _ _ yes no) => do
      let (regs, loads, stores) ← c.operandsIn t.operands
      let some t' := t.substitute (regs.map Loc.reg) [[], []] | throw "substitution failed"
      pure (loads, t', [(yes.target, stores ++ (← c.edge yes)), (no.target, stores ++ (← c.edge no))])
  | .ret vs => do
      unless vs.length ≤ Xl.nResultRegs do throw "too many results"
      let loads ← vs.zipIdx.mapM fun (v, i) =>
        match Lir.Conv.resultRegs[i]? with
        | some r => c.load r v
        | none => throw "result register"
      pure (loads, .ret ((List.range vs.length).filterMap Xl.resultLoc), [])
  | .tail g args => do
      unless args.length ≤ Xl.nArgRegs do throw "a tail call with stack arguments"
      let loads ← args.zipIdx.mapM fun (a, i) =>
        match Lir.Conv.argRegs[i]? with
        | some r => c.load r a
        | none => throw "argument register"
      pure (loads, .tail g ((List.range args.length).map Xl.argLoc), [])
  | .fail r => pure ([], .fail r, [])
  | .trap => pure ([], .trap, [])

def allocFunc (f : Func VReg) : Except String (Func Loc) := do
  let c : Ctx := { homes := homes f,
                   params := f.blocks.toList.zipIdx.foldl (fun m (b, l) => m.insert l b.params) {} }
  let entry ← (f.params.take Xl.nArgRegs).zipIdx.mapM fun (v, i) =>
    match Lir.Conv.argRegs[i]? with
    | some r => c.store v r
    | none => throw "argument register"
  let blocks ← f.blocks.toList.zipIdx.mapM fun (b, l) => do
    let body ← b.body.toList.mapM c.inst
    let (pre, t, heads) ← c.term b.term
    pure (l, (if l == 0 then entry else []) ++ body.flatten ++ pre, t, heads)
  let heads : NatMap (List (Inst Loc)) := blocks.foldl (init := {}) fun m (_, _, _, hs) =>
    hs.foldl (fun m (l, is) => m.insert l ((m.getD l []) ++ is)) m
  pure { name := f.name, params := (List.range f.params.length).map Xl.paramLoc, results := f.results,
         conv := f.conv,
         blocks := (blocks.map fun (l, body, t, _) =>
           ({ body := ((heads.getD l []) ++ body).toArray, term := t, cold := (f.blocks[l]?.map (·.cold)).getD false } :
             Block Loc)).toArray }

/-- Allocate every function. -/
def run (p : VProgram) : Except String LProgram := do
  let funcs ← p.funcs.toList.zipIdx.mapM fun (f, fn) => (allocFunc f).mapError (s!"function {fn}: " ++ ·)
  pure { funcs := funcs.toArray, main := p.main }

end CompilatrixTests.Backend.SlotAlloc
