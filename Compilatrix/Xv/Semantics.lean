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
undefined input flags, as typed `X86.Eval` does. Each operand position sits
in its own scratch register for the duration of the row (`Placer`), an
implicit operand in its fixed register: the uses are read, the row runs,
and the definitions are read back, a tied definition from its use's
register. A definition's register starts at 0, so a well-formed
instruction never depends on anything but its uses, and a fused `setcc`
definition is zero-extended, as its `xor`-first expansion makes it.
`fused` runs the producer and then the consumer on one core, threading the
producer's flags into the consumer; `jcc` runs its producer and decides with
the `jcc` row's own semantics. The context register is `r15`, holding `ctx`.

**Outcomes** are Lir's: `stuck` for an undefined register, a faulting row
(denied memory, or a flag the consumer reads left undefined), a missing
function or block, or an arity mismatch.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Label FunId Word Env Frame State)

/-- Registers for one Xv instruction's operands, handed out as its bound
operands are visited: `free` scratch registers (the instruction's fixed
registers excluded), the registers to fill with operand values before the
rows run, and the definitions to read back after. -/
structure Placer where
  free : List X86.GPR
  loads : List (X86.GPR × VReg) := []
  reads : List (VReg × X86.GPR) := []

def Placer.take (p : Placer) : Option (X86.GPR × Placer) :=
  match p.free with
  | r :: rs => some (r, { p with free := rs })
  | [] => none

/-- A fresh register holding the value of `x`. -/
def Placer.use (p : Placer) (x : VReg) : Option (X86.GPR × Placer) := do
  let (r, p) ← p.take
  pure (r, { p with loads := (r, x) :: p.loads })

def Placer.amode (p : Placer) (a : Amode VReg) : Option (X86.MemAddr × Placer) := do
  let (base, p) ← match a.base with
    | none => pure (none, p)
    | some .ctx => pure (some X86.GPR.r15, p)
    | some (.r b) => do
        let (r, p) ← p.use b
        pure (some r, p)
  let (index, scale, p) ← match a.index with
    | none => pure (none, X86.Scale.one, p)
    | some (x, s) => do
        let (r, p) ← p.use x
        pure (some (← indexReg r), s, p)
  pure ({ base, index, scale, displacement := a.disp.toUInt32 }, p)

/-- Place one bound operand: its machine argument (none for an implicit
register) and the updated placer. -/
def Placer.bound (p : Placer) : Bound VReg → Option (Option X86.Arg × Placer)
  | .input _ (.r a) => do
      let (r, p) ← p.use a
      pure (some (.reg r), p)
  | .input _ (.m a) | .memory _ a => do
      let (m, p) ← p.amode a
      pure (some (.mem m), p)
  | .input _ (.i w) => pure (some (.imm w), p)
  | .output _ x => do
      let (r, p) ← p.take
      pure (some (.reg r), { p with reads := (x, r) :: p.reads })
  | .tied _ a x => do
      let (r, p) ← p.use a
      pure (some (.reg r), { p with reads := (x, r) :: p.reads })
  | .fixedUse i a => pure (none, { p with loads := (i.reg, a) :: p.loads })
  | .fixedDef i x => pure (none, { p with reads := (x, i.reg) :: p.reads })
  | .fixedTied i a x => pure (none, { p with loads := (i.reg, a) :: p.loads, reads := (x, i.reg) :: p.reads })

def Placer.bounds (p : Placer) : List (Bound VReg) → Option (List X86.Arg × Placer)
  | [] => some ([], p)
  | b :: bs => do
      let (arg, p) ← p.bound b
      let (args, p) ← Placer.bounds p bs
      pure (arg.toList ++ args, p)

/-- Place one part's operands after the previous parts'. -/
def placePart (s : List (X86.Op × List X86.Arg) × Placer) (part : X86.Op × List (Bound VReg)) :
    Option (List (X86.Op × List X86.Arg) × Placer) := do
  let (args, p) ← s.2.bounds part.2
  pure (s.1 ++ [(part.1, args)], p)

/-- A loaded register with its operand's value. -/
def loadValue (ρ : Env) (l : X86.GPR × VReg) : Option (X86.GPR × Word) := do
  pure (l.1, ← ρ[l.2]?)

/-- The core's registers before a row: the context register, each loaded
value, and zero elsewhere. -/
def loadRegisters (ctx : Word) (vals : List (X86.GPR × Word)) : X86.Registers := fun r =>
  if r == .r15 then ctx else ((vals.find? (·.1 == r)).map (·.2)).getD 0

/-- Read definitions back from their registers, in order. -/
def readBack (core : X86.Core) (ρ : Env) (reads : List (VReg × X86.GPR)) : Env :=
  reads.foldl (fun ρ d => ρ.insert d.1 (core.readReg d.2)) ρ

/-- Run rows whose slots are bound over virtual registers, on one core: the
new environment (definitions read back, in order), memory and flags. Each
operand position has its own register, so a register named twice sits in
two; an implicit operand sits in its fixed register, and two fixed uses of
one register must agree. A definition's register starts at 0. -/
def execBound (parts : List (X86.Op × List (Bound VReg))) (ρ : Env) (mem : X86.Memory) (ctx : Word) :
    Option (Env × X86.Memory × X86.ByteEval.Flags) := do
  let fixed := parts.flatMap fun part => part.2.filterMap Bound.fixed?
  let (margs, p) ← parts.foldlM (init := ([], ({ free := scratch.filter (!fixed.contains ·) } : Placer)))
    placePart
  let vals ← p.loads.mapM (loadValue ρ)
  guard (vals.all fun v => vals.all fun v' => v.1 != v'.1 || v.2 == v'.2)
  let (core, flags) ← execRows margs { registers := loadRegisters ctx vals, memory := mem }
  return (readBack core ρ p.reads.reverse, core.memory, flags)

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
