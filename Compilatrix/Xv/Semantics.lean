import Compilatrix.Xv.Slots
import Compilatrix.Lir.Semantics
import Compilatrix.Sem.Clock

/-!
# Xv semantics

An executable, clocked small-step semantics for Xv (05 §3), over Lir's
states: the same frames (`Lir.Frame`, an environment `VReg → Word` per
activation), memory and context word. Labels, calls, returns and the clock
are Lir's, so Lir and Xv charge exactly the same events (`call`, `tail`,
and edges whose target label is at most their source label) and a
selected program runs in lock-step with its source.

**Rows.** An `op` runs its table row through `Op.exec` (`Xv.Slots`) with
undefined input flags, as typed `X86.Eval` does. Its register operands sit
in scratch registers for the duration of the row (`assignRegs`): the uses
are read, the row runs, and the definitions are read back, a tied
definition from its use's register. A definition's register starts at 0,
so a well-formed instruction (no narrow write-only register destination,
`Xv.WellFormed`) never depends on anything but its uses. `fused` runs the
producer and then the consumer on one core, threading the producer's flags
into the consumer; `jcc` runs its producer and decides with the `jcc` row's
own semantics. The context register is `r15`, holding `ctx`.

**Outcomes** are Lir's: `stuck` for an undefined register, a faulting row
(denied memory, or a flag the consumer reads left undefined), a missing
function or block, or an arity mismatch.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Label FunId Word Env Frame State)

/-- Every register operand the bound slots name, tied definitions excluded
(they share their use's register). -/
def placeVars (bs : List (Bound VReg)) : List VReg :=
  bs.flatMap fun
    | .input _ a => a.regs
    | .output _ x => [x]
    | .tied _ a _ => [a]
    | .memory _ m => m.regs

/-- Scratch registers for each distinct operand, in order. -/
def assignRegs (bs : List (Bound VReg)) : Option (List (VReg × X86.GPR)) :=
  let vars := dedup (placeVars bs)
  if vars.length ≤ scratch.length then some (vars.zip scratch) else none

/-- Run rows whose slots are bound over virtual registers, on one core: the
new environment (definitions read back), memory and flags. -/
def execBound (parts : List (X86.Op × List (Bound VReg))) (ρ : Env) (mem : X86.Memory) (ctx : Word) :
    Option (Env × X86.Memory × X86.ByteEval.Flags) := do
  let bs := parts.flatMap (·.2)
  let table ← assignRegs bs
  let place (x : VReg) : Option X86.GPR := table.lookup x
  let uses := bs.flatMap Bound.uses
  let _ ← uses.mapM fun x => ρ[x]?
  let registers : X86.Registers := fun r =>
    if r == .r15 then ctx else
    match table.find? (·.2 == r) with
    | some (x, _) => if uses.contains x then ρ[x]?.getD 0 else 0
    | none => 0
  let margs ← parts.mapM fun (o, bs) => do return (o, ← bs.mapM (Bound.machine place place))
  let (core, flags) ← execRows margs { registers, memory := mem }
  let ρ' ← (bs.flatMap (Bound.readback place)).foldlM (init := ρ) fun ρ (x, r) => do
    return ρ.insert x (core.readReg (← r))
  return (ρ', core.memory, flags)

/-- The row of the zeroing idiom, `xor r32, r32`. -/
def zeroRow : X86.Op := { mn := .xor, w := .w32, form := .MR }

/-- One instruction other than a call. -/
def Inst.exec (ρ : Env) (mem : X86.Memory) (ctx : Word) : Inst VReg → Option (Env × X86.Memory)
  | .op o defs args => do
      let bs ← bindRow o defs args
      let (ρ', mem', _) ← execBound [(o, bs)] ρ mem ctx
      pure (ρ', mem')
  | .fused p pargs c defs cargs => do
      let pb ← bindRow p [] pargs
      let cb ← bindRow c defs cargs
      let (ρ', mem', _) ← execBound [(p, pb), (c, cb)] ρ mem ctx
      pure (ρ', mem')
  | .move dst src => do pure (ρ.insert dst (← ρ[src]?), mem)
  | .zero x => do
      let (core, _) ← execRows [(zeroRow, [.reg .rax, .reg .rax])] { registers := fun _ => 0, memory := mem }
      pure (ρ.insert x (core.readReg .rax), core.memory)
  | .call .. => none

/-- A `jcc` terminator's producer and decision: the new environment and
memory, and whether the branch is taken. -/
def execJcc (p : X86.Op) (pargs : List (XArg VReg)) (defs : List VReg) (c : X86.Condition)
    (ρ : Env) (mem : X86.Memory) (ctx : Word) : Option (Env × X86.Memory × Bool) := do
  let bs ← bindRow p defs pargs
  let (ρ', mem', flags) ← execBound [(p, bs)] ρ mem ctx
  let taken ← jccTaken c flags
  pure (ρ', mem', taken)

/-! ## States and steps -/

abbrev XStep := Sem.Step State (List Word × X86.Memory)

def readAll (ρ : Env) (xs : List VReg) : Option (List Word) := xs.mapM (ρ[·]?)

/-- Leave the running frame along `e`, with the edge arguments read in `ρ`. -/
def takeEdge (f : Func VReg) (s : State) (fr : Frame) (rest : List Frame) (ρ : Env) (e : Edge VReg) :
    XStep :=
  match readAll ρ e.args, f.blocks[e.target]? with
  | some vals, some target =>
      match Lir.bindParams ρ target.params vals with
      | some ρ' =>
          .next { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest }
            (decide (e.target ≤ fr.label))
      | none => .stuck
  | _, _ => .stuck

/-- A fresh activation of `g` with arguments `vals`. -/
def enter (p : VProgram) (g : FunId) (vals : List Word) : Option Frame := do
  let callee ← p.funcs[g]?
  let ρ ← Lir.bindParams {} callee.params vals
  some { fn := g, label := 0, pos := 0, env := ρ }

def step (p : VProgram) (s : State) : XStep :=
  match s.stack with
  | [] => .stuck
  | fr :: rest =>
    match p.funcs[fr.fn]? with
    | none => .stuck
    | some f =>
    match f.blocks[fr.label]? with
    | none => .stuck
    | some b =>
    if h : fr.pos < b.body.size then
      match b.body[fr.pos] with
      | .call g args rets =>
          match readAll fr.env args >>= enter p g with
          | some callee =>
              .next { s with stack := callee :: { fr with pos := fr.pos + 1, dsts := rets } :: rest } true
          | none => .stuck
      | inst =>
          match inst.exec fr.env s.mem s.ctx with
          | some (ρ, mem) => .next { s with mem, stack := { fr with pos := fr.pos + 1, env := ρ } :: rest } false
          | none => .stuck
    else
      match b.term with
      | .jmp e => takeEdge f s fr rest fr.env e
      | .jcc p' pargs defs c t e =>
          match execJcc p' pargs defs c fr.env s.mem s.ctx with
          | some (ρ, mem, taken) => takeEdge f { s with mem } fr rest ρ (if taken then t else e)
          | none => .stuck
      | .ret vs =>
          match readAll fr.env vs with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done (vals, s.mem)
              | caller :: rest' =>
                  match Lir.bindParams caller.env caller.dsts vals with
                  | some ρ => .next { s with stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g args =>
          match readAll fr.env args >>= enter p g with
          | some callee => .next { s with stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap

/-- The step bound for clock `k`, as for Lir (`Lir.fuelFor`): between two
charges an activation moves forward through its blocks. -/
def fuelFor (p : VProgram) (k : Nat) : Nat := (2 * k + 3) * (p.size + 1)

def State.initial (p : VProgram) (args : List Word) (mem : X86.Memory) (ctx : Word) : Option State := do
  let fr ← enter p p.main args
  some { mem, ctx, stack := [fr] }

/-- Run `main` on `args` with clock `k`: its results and final memory. -/
def eval (p : VProgram) (k : Nat) (args : List Word) (mem : X86.Memory) (ctx : Word) : Lir.Outcome :=
  match State.initial p args mem ctx with
  | some s => Sem.runClocked (step p) (fuelFor p k) k s
  | none => .stuck

end Compilatrix.Xv
