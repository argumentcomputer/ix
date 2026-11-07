import IxCC.Lir.Syntax
import IxCC.X86.State
import Std.Data.HashMap

/-!
# Lir semantics

An executable, clocked small-step semantics (05 §2). The state is a stack of
frames over the machine's permissioned byte memory (`X86.Memory`) and the
context word; there is no stack memory, so Lir addresses only the heap and
context regions (04 §6).

**Words.** An operation at width `w` reads the low `w` bits of its operands
and yields a zero-extended word. Shift counts are masked as the machine masks
them (6 bits at width 64, 5 bits below), so a selected shift computes the
same low `w` bits. At widths 32 and 64 the machine's result is the Lir word;
8- and 16-bit machine writes keep the upper bits, so selection must
zero-extend them (or show they are dead).

**Outcomes** (`Sem.Result`). `stuck` is a semantic error that well-formed,
well-behaved programs never reach: an undefined register, a division by zero,
a denied memory access, a missing function or block, or an arity mismatch.
A step that succeeds therefore implies each machine row's safety
precondition. `fail r` is `resource r`; `trap` is `trap`.

**Clock.** `call`, `tail`, and every edge whose target label is at most its
source label charge one unit, so every cycle is charged. A charge with an
empty clock is `timeout`. `ret` and forward edges are free.

**Fuel.** `eval` also bounds the number of steps, by `fuelFor`, only so that
the definition is structural. Between two charges or returns an activation
moves strictly forward through its blocks, so a run that spends `c` charges
takes at most `(2c + 2) · (size + 1)` steps (returns never exceed calls plus
one). The fuel is larger, so running out of it never happens before the
clock runs out; `check-lir` tests the bound on every generated program.
-/

namespace IxCC.Lir

/-! ## Word operations -/

/-- The machine's shift-count mask at this operand width. -/
def shiftMask : Width → Word
  | .w64 => 63
  | _ => 31

/-- Sign extension of the low `w` bits. -/
def sext : Width → Word → Word
  | .w8, a => a.toUInt8.toInt8.toInt64.toUInt64
  | .w16, a => a.toUInt16.toInt16.toInt64.toUInt64
  | .w32, a => a.toUInt32.toInt32.toInt64.toUInt64
  | .w64, a => a

/-- Arithmetic right shift of the low `w` bits by `c < 64`. -/
def sarWord (w : Width) (a c : Word) : Word :=
  w.truncate ((sext w a).toInt64 >>> c.toInt64).toUInt64

/-- `none` is a division by zero. -/
def BinOp.eval (o : BinOp) (w : Width) (a b : Word) : Option Word :=
  match o with
  | .add => some (w.truncate (a + b))
  | .sub => some (w.truncate (a - b))
  | .and => some (w.truncate (a &&& b))
  | .or => some (w.truncate (a ||| b))
  | .xor => some (w.truncate (a ^^^ b))
  | .mul => some (w.truncate (a * b))
  | .shl => some (w.truncate (a <<< (b &&& shiftMask w)))
  | .shr => some (w.truncate (w.truncate a >>> (b &&& shiftMask w)))
  | .sar => some (sarWord w a (b &&& shiftMask w))
  | .udiv =>
      let d := w.truncate b
      if d == 0 then none else some (w.truncate a / d)
  | .urem =>
      let d := w.truncate b
      if d == 0 then none else some (w.truncate a % d)

/-- Conditions on the low `w` bits; the signed ones read them as two's
complement. The ten comparisons mirror `X86.Condition.holds`. -/
def Cond.holds (c : Cond) (w : Width) (a b : Word) : Bool :=
  let ua := w.truncate a
  let ub := w.truncate b
  match c with
  | .eq => ua == ub
  | .ne => ua != ub
  | .ult => decide (ua < ub)
  | .ule => decide (ua ≤ ub)
  | .ugt => decide (ua > ub)
  | .uge => decide (ua ≥ ub)
  | .slt => decide (w.signedValue a < w.signedValue b)
  | .sle => decide (w.signedValue a ≤ w.signedValue b)
  | .sgt => decide (w.signedValue a > w.signedValue b)
  | .sge => decide (w.signedValue a ≥ w.signedValue b)
  | .tz => w.truncate (a &&& b) == 0
  | .tnz => w.truncate (a &&& b) != 0

/-- The 64-bit result and whether the unsigned operation carried (borrowed). -/
def Ovf.eval : Ovf → Word → Word → Word × Bool
  | .addC, a, b => (a + b, decide (a + b < a))
  | .subB, a, b => (a - b, decide (a < b))

/-- A displacement as a word (two's complement modulo 2^64). -/
def dispWord (d : Int) : Word := UInt64.ofBitVec (BitVec.ofInt 64 d)

/-! ## Environments and expressions -/

/-- The registers of one activation. -/
abbrev Env := Std.HashMap VReg Word

def Arg.eval (ρ : Env) : Arg → Option Word
  | .v x => ρ[x]?
  | .imm w => some w

def evalArgs (ρ : Env) (as : List Arg) : Option (List Word) := as.mapM (Arg.eval ρ)

def Addr.eval (ρ : Env) (ctx : Word) (m : Addr) : Option Word := do
  let base ← match m.base with
    | none => some 0
    | some (.v x) => ρ[x]?
    | some .ctx => some ctx
  let index ← match m.index with
    | none => some 0
    | some (x, s) => (· * s.word) <$> ρ[x]?
  some (base + index + dispWord m.disp)

/-- Bind parameters to values; `none` on an arity mismatch. -/
def bindParams (ρ : Env) : List VReg → List Word → Option Env
  | [], [] => some ρ
  | x :: xs, v :: vs => bindParams (ρ.insert x v) xs vs
  | _, _ => none

/-- A `w`-byte read, extended to a word; `none` if any byte is not readable. -/
def loadWord (mem : X86.Memory) (w : Width) (e : Ext) (address : Word) : Option Word :=
  match mem.read? w address with
  | .ok v => some (match e with | .zero => v | .sign => sext w v)
  | .error _ => none

def Rhs.eval (ρ : Env) (mem : X86.Memory) (ctx : Word) : Rhs → Option Word
  | .arg a => a.eval ρ
  | .bin o w a b => do o.eval w (← a.eval ρ) (← b.eval ρ)
  | .load w e m => do loadWord mem w e (← m.eval ρ ctx)
  | .addr m => m.eval ρ ctx
  | .select c w a b t f => do
      let va ← a.eval ρ
      let vb ← b.eval ρ
      let vt ← t.eval ρ
      let vf ← f.eval ρ
      some (if c.holds w va vb then vt else vf)
  | .test c w a b => do
      let va ← a.eval ρ
      let vb ← b.eval ρ
      some (if c.holds w va vb then 1 else 0)

/-- One local statement. Calls are not local (`step` runs them), so a call
here is `none`, as is every stuck case. -/
def Stmt.exec (ρ : Env) (mem : X86.Memory) (ctx : Word) : Stmt → Option (Env × X86.Memory)
  | .assign x r => do
      let v ← r.eval ρ mem ctx
      some (ρ.insert x v, mem)
  | .store w m a => do
      let address ← m.eval ρ ctx
      let v ← a.eval ρ
      match mem.write? w address v with
      | .ok mem' => some (ρ, mem')
      | .error _ => none
  | .call .. => none

/-! ## States and steps -/

structure Frame where
  fn : FunId
  label : Label
  /-- The next statement; `body.size` is the terminator. -/
  pos : Nat
  env : Env
  /-- For a suspended caller: the registers its callee's results bind. -/
  dsts : List VReg := []

structure State where
  mem : X86.Memory
  ctx : Word
  /-- The running frame first. -/
  stack : List Frame

inductive Step where
  /-- `charge`: this step spends one unit of clock. -/
  | next (s : State) (charge : Bool)
  | done (vals : List Word) (mem : X86.Memory)
  | fail (r : Sem.Resource)
  | trap
  | stuck

/-- Leave the running frame along `e`, with the edge arguments read in `ρ`. -/
def takeEdge (f : Func) (s : State) (fr : Frame) (rest : List Frame) (ρ : Env) (e : Edge) :
    Step :=
  match evalArgs ρ e.args, f.blocks[e.target]? with
  | some vals, some target =>
      match bindParams ρ target.params vals with
      | some ρ' =>
          .next { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest }
            (decide (e.target ≤ fr.label))
      | none => .stuck
  | _, _ => .stuck

/-- A fresh activation of `g` with arguments `vals`. -/
def enter (p : Program) (g : FunId) (vals : List Word) : Option Frame := do
  let callee ← p.funcs[g]?
  let ρ ← bindParams {} callee.params vals
  some { fn := g, label := 0, pos := 0, env := ρ }

def step (p : Program) (s : State) : Step :=
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
      | .call rs g as =>
          match evalArgs fr.env as >>= enter p g with
          | some callee =>
              .next { s with stack := callee :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } true
          | none => .stuck
      | stmt =>
          match stmt.exec fr.env s.mem s.ctx with
          | some (ρ, mem) => .next { s with mem, stack := { fr with pos := fr.pos + 1, env := ρ } :: rest } false
          | none => .stuck
    else
      match b.term with
      | .jump e => takeEdge f s fr rest fr.env e
      | .br c w a b' t e =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb => takeEdge f s fr rest fr.env (if c.holds w va vb then t else e)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge f s fr rest (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret as =>
          match evalArgs fr.env as with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals s.mem
              | caller :: rest' =>
                  match bindParams caller.env caller.dsts vals with
                  | some ρ => .next { s with stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g as =>
          match evalArgs fr.env as >>= enter p g with
          | some callee => .next { s with stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap

abbrev Outcome := Sem.Result (List Word × X86.Memory)

/-- Iterate `step` with at most `fuel` steps and clock `k`. -/
def run (p : Program) : (fuel k : Nat) → State → Outcome
  | 0, _, _ => .timeout
  | fuel + 1, k, s =>
      match step p s with
      | .next s' false => run p fuel k s'
      | .next s' true =>
          match k with
          | 0 => .timeout
          | k + 1 => run p fuel k s'
      | .done vals mem => .ok (vals, mem)
      | .fail r => .resource r
      | .trap => .trap
      | .stuck => .stuck

/-- The step bound for clock `k` (see the module note). -/
def fuelFor (p : Program) (k : Nat) : Nat := (2 * k + 3) * (p.size + 1)

def State.initial (p : Program) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Option State := do
  let fr ← enter p p.main args
  some { mem, ctx, stack := [fr] }

/-- Run `main` on `args` with clock `k`: its results and final memory. -/
def eval (p : Program) (k : Nat) (args : List Word) (mem : X86.Memory) (ctx : Word) : Outcome :=
  match State.initial p args mem ctx with
  | some s => run p (fuelFor p k) k s
  | none => .stuck

end IxCC.Lir
