import Compilatrix.Xv.Stacking.Proof.Code
import Compilatrix.Xv.Stacking.Proof.Exit

/-!
# The stacking invariant

How a running Xl state sits in the stacked machine (`Match`):

* **The running activation** (`Top`): the machine is at the stacked code of
  Xl's position, its registers, memory and frame cells agree with Xl's
  (`Agree`), `rsp` is the frame's stack pointer, and every register its
  caller expects back that it has not saved still holds its entry value.
* **Every activation** (`ActFacts`): its saves hold its entry registers, its
  return slot holds its continuation and the callee-saved snapshot the
  machine checks, and its caller lets it change at least what it may.
* **Suspended activations** (`Chain`): each is at a call, its cells and the
  registers at the call agree with Xl's frame and saved registers, and it is
  linked to its callee (`Link`): the callee returns into it, below it on
  the stack, giving back the registers at the call. The last one is
  linked to the export wrapper (`Bottom`).
* **The machine stack** (`Global`): the stack between the wrapper's limit
  and its caller's return address, and the context cells, are Xl-free and
  machine-accessible; the failure exit's frame (`EntryFrame`) holds;
  holes are only where Xl cannot look.

Stack addresses are compared by `toNat`: the stack never wraps.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- The checked stacked program. -/
def Stk.cs (S : Stk) : Checked :=
  ⟨S.st.program, by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := run_ok S.ok; exact h⟩

/-- A function, its layout and its placement. -/
structure FnAt (S : Stk) (k : Lir.FunId) (f : Func Loc) (l : FrameLayout) (pl : Placed) : Prop where
  func : S.p.funcs[k]? = some f
  layout : S.layouts[k]? = some l
  placed : S.placed[k]? = some pl
  pfunc : pl.func = f
  play : pl.layout = l
  pfacts : pl.facts = f.facts

theorem FnAt.unique {S : Stk} {k : Lir.FunId} {f f' : Func Loc} {l l' : FrameLayout} {pl pl' : Placed}
    (h : FnAt S k f l pl) (h' : FnAt S k f' l' pl') : f' = f ∧ l' = l ∧ pl' = pl := by
  refine ⟨?_, ?_, ?_⟩
  · have := h.func; rw [h'.func] at this; exact Option.some.inj this
  · have := h.layout; rw [h'.layout] at this; exact Option.some.inj this
  · have := h.placed; rw [h'.placed] at this; exact Option.some.inj this

/-- The export wrapper's frame and the stack it gives the program. -/
structure Wrap where
  /-- The context register. -/
  ctx : Word
  /-- The wrapper's `rsp` at its call (`entrySp`). -/
  entrySp : Word
  /-- The registers of the wrapper's caller. -/
  core₀ : Core
  retAddr : Word
  /-- `stackLimit`. -/
  limit : Word
  /-- The return frame of the wrapper's call. -/
  frame : ReturnFrame
  /-- The registers at the wrapper's call. -/
  regs : GPR → Word

/-- The stack from the wrapper's limit to its caller's return address. -/
def Wrap.InStack (W : Wrap) (x : Word) : Prop := W.limit.toNat ≤ x.toNat ∧ x.toNat < W.entrySp.toNat + 64

/-- An activation: its body's stack pointer, the registers it gives back,
the registers its caller lets it change, and (while it waits on a call)
the registers at that call. -/
structure Act where
  sp : Word
  entry : GPR → Word
  allow : List GPR
  regs : GPR → Word

/-- A core with stack pointer `sp`, to evaluate frame cells. -/
def atSp (sp : Word) : Core := { registers := fun _ => sp, memory := Memory.flat }

/-! ## Positions -/

/-- The prologue before label 0's body. -/
def preOf (l : FrameLayout) (label : Nat) : List Instr := if label = 0 then prologue l else []

/-- The offset of instruction `pos`'s code in its block. -/
def offsetOf (l : FrameLayout) (label pos : Nat) (codes : List (List Instr)) : Nat :=
  (preOf l label).length + ((codes.take pos).flatten.length)

/-- Label `label` of function `pl`, at offset `offset`. -/
def pcOf (S : Stk) (pl : Placed) (label offset : Nat) : PC :=
  ⟨UInt32.ofNat ((ctxOf S.placed pl).labelBase + label), UInt32.ofNat offset⟩

/-- Xl's position in frame `fr`: label `fr.label`'s block `b` with the code
of each of its instructions and of its terminator. -/
structure XlPos (S : Stk) (fr : Xl.Frame) (f : Func Loc) (l : FrameLayout) (pl : Placed) (b : Block Loc)
    (codes : List (List Instr)) (post : List Instr) (t : X86.Terminator) : Prop where
  block : f.blocks[fr.label]? = some b
  found : S.st.program.blocks[(ctxOf S.placed pl).labelBase + fr.label]? =
    some { instructions := (preOf l fr.label ++ codes.flatten ++ post).toArray, terminator := t }
  len : codes.length = b.body.size
  insts : ∀ (i : Nat) (x : Inst Loc), b.body[i]? = some x →
    ∃ code, codes[i]? = some code ∧ (ctxOf S.placed pl).inst x = .ok code
  term : (ctxOf S.placed pl).term b.term = .ok (post, t)
  pos : fr.pos ≤ b.body.size

/-! ## Activations -/

/-- What every activation keeps. -/
structure ActFacts (S : Stk) (W : Wrap) (mem : Memory) (holes : Holes) (fr : Xl.Frame) (a : Act)
    (ret : ReturnFrame) (f : Func Loc) (l : FrameLayout) : Prop where
  saves : ∀ r o, (r, o) ∈ l.saveOff → mem.read64 (a.sp + UInt64.ofNat o) = a.entry r
  savesData : ∀ r o, (r, o) ∈ l.saveOff → ReadableData holes (a.sp + UInt64.ofNat o) 8
  allowed : ∀ r ∈ allowedChanges S.env fr.fn f, r ∈ a.allow
  slot : ret.returnSlot = a.sp + UInt64.ofNat l.size
  retAddr : mem.read64 ret.returnSlot = ret.continuation.encode
  snapshot : ret.calleeSaved = SysV.calleeSaved.map a.entry
  align : (a.sp.toNat + l.size) % 16 = 8
  low : W.limit.toNat ≤ a.sp.toNat
  high : a.sp.toNat + l.size + 8 + 8 * f.facts.inArgs ≤ W.entrySp.toNat
  inBound : 8 * f.facts.inArgs ≤ maxFrame

/-- A suspended activation: Xl's frame waits on a call; its saved registers
are the machine's at the call; its cells hold its values. -/
structure SuspFacts (S : Stk) (W : Wrap) (mem : Memory) (holes : Holes) (fr : Xl.Frame) (a : Act)
    (f : Func Loc) (l : FrameLayout) (pl : Placed) : Prop where
  call : ∃ b g args rets, f.blocks[fr.label]? = some b ∧ 0 < fr.pos ∧
    b.body[fr.pos - 1]? = some (.call g args rets) ∧ fr.clobber = S.env.clobbers g ∧ fr.results = rets.length
  outArgs : ∀ i : Nat, fr.outArgs[i]? = none
  size : fr.saved.size = 16
  regs : RegsRel fr.saved ⟨a.regs, Memory.flat⟩
  r15 : a.regs .r15 = W.ctx
  rsp : a.regs .rsp = a.sp
  kept : ∀ r, r ∉ a.allow → r ≠ .rsp → r ∈ l.saved ∨ a.regs r = a.entry r
  cells : ∀ x, x.isCell = true → ∀ v, Xl.read Xl.Regs.empty fr x = some v →
    ∃ m, (ctxOf S.placed pl).cell x = .ok m ∧ mem.read64 (m.eval (atSp a.sp)) = v ∧
      ReadableData holes (m.eval (atSp a.sp)) 8
  inArgs : fr.inArgs.size = f.facts.inArgs
  /-- It made a call, so it had the room a call needs. -/
  room : W.limit.toNat + slack ≤ a.sp.toNat

/-- Callee `fr₀` (activation `a₀`, return frame `ret₀`) of caller `fr₁`. -/
structure Link (S : Stk) (a₀ : Act) (ret₀ : ReturnFrame) (f₀ : Func Loc) (l₀ : FrameLayout)
    (fr₁ : Xl.Frame) (a₁ : Act) (f₁ : Func Loc) (l₁ : FrameLayout) (pl₁ : Placed) : Prop where
  cont : ∃ b codes post t, XlPos S fr₁ f₁ l₁ pl₁ b codes post t ∧
    ret₀.continuation = pcOf S pl₁ fr₁.label (offsetOf l₁ fr₁.label fr₁.pos codes)
  sp : a₀.sp.toNat + l₀.size + 8 = a₁.sp.toNat
  entry : ∀ r, r ≠ .rsp → a₀.entry r = a₁.regs r
  allow : ∃ b g args rets gf, f₁.blocks[fr₁.label]? = some b ∧
    b.body[fr₁.pos - 1]? = some (.call g args rets) ∧ S.p.funcs[g]? = some gf ∧
    a₀.allow = allowedChanges S.env g gf
  room : a₀.sp.toNat + l₀.size + 8 + 8 * f₀.facts.inArgs ≤ a₁.sp.toNat + 8 * l₁.outArgs

/-- The outermost activation, `main`'s (or what it tail-called), returns
to the export wrapper. -/
structure Bottom (S : Stk) (W : Wrap) (a : Act) (ret : ReturnFrame) (f : Func Loc) (l : FrameLayout) :
    Prop where
  frame : ret = W.frame
  sp : a.sp.toNat + l.size + 8 = W.entrySp.toNat
  entry : ∀ r, r ≠ .rsp → a.entry r = W.regs r
  allow : ∃ mf, S.p.funcs[S.p.main]? = some mf ∧ a.allow = allowedChanges S.env S.p.main mf
  inArgs : f.facts.inArgs = 0

/-- The suspended activations below `fr`, innermost first, each with its
return frame. -/
def Chain (S : Stk) (W : Wrap) (mem : Memory) (holes : Holes) :
    Xl.Frame → Act → ReturnFrame → List (Xl.Frame × Act × ReturnFrame) → Prop
  | fr, a, ret, [] => ∀ f l pl, FnAt S fr.fn f l pl → Bottom S W a ret f l
  | fr, a, ret, (fr₁, a₁, ret₁) :: rest =>
      (∃ f₁ l₁ pl₁, FnAt S fr₁.fn f₁ l₁ pl₁) ∧
      (∀ f l pl, FnAt S fr.fn f l pl → ∀ f₁ l₁ pl₁, FnAt S fr₁.fn f₁ l₁ pl₁ →
        Link S a ret f l fr₁ a₁ f₁ l₁ pl₁ ∧ ActFacts S W mem holes fr₁ a₁ ret₁ f₁ l₁ ∧
          SuspFacts S W mem holes fr₁ a₁ f₁ l₁ pl₁) ∧
      Chain S W mem holes fr₁ a₁ ret₁ rest

/-- The running activation. -/
structure Top (S : Stk) (W : Wrap) (s : Xl.State) (m : Machine) (holes : Holes) (fr : Xl.Frame) (a : Act)
    (ret : ReturnFrame) (f : Func Loc) (l : FrameLayout) (pl : Placed) : Prop where
  fn : FnAt S fr.fn f l pl
  code : ∃ b codes post t, XlPos S fr f l pl b codes post t ∧
    m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes)
  agree : Agree (ctxOf S.placed pl) s.regs fr s.mem W.ctx m.core
  rsp : m.core.readReg .rsp = a.sp
  kept : ∀ r, r ∉ a.allow → r ≠ .rsp → r ∈ l.saved ∨ m.core.readReg r = a.entry r
  act : ActFacts S W m.core.memory holes fr a ret f l
  cellsData : ∀ x, x.isCell = true → ∀ v, Xl.read s.regs fr x = some v → ∀ mm,
    (ctxOf S.placed pl).cell x = .ok mm → ReadableData holes (mm.eval m.core) 8
  room : f.facts.calls = true → W.limit.toNat + slack ≤ a.sp.toNat
  inArgs : fr.inArgs.size = f.facts.inArgs

/-- The machine stack and the context cells. -/
structure Global (W : Wrap) (xm : Memory) (m : Machine) (holes : Holes) : Prop where
  stack : ∀ x, W.InStack x → xm.readable x = false ∧ xm.writable x = false ∧
    m.core.memory.readable x = true ∧ m.core.memory.writable x = true
  ctxCells : ∀ i < 16, xm.readable (W.ctx - 64 + UInt64.ofNat i) = false ∧
    xm.writable (W.ctx - 64 + UInt64.ofNat i) = false ∧
    m.core.memory.readable (W.ctx - 64 + UInt64.ofNat i) = true ∧
    m.core.memory.writable (W.ctx - 64 + UInt64.ofNat i) = true
  apart : ∀ i < 16, ¬ W.InStack (W.ctx - 64 + UInt64.ofNat i)
  holesFree : ∀ x, holes x → xm.readable x = false ∧ xm.writable x = false
  entry : EntryFrame W.ctx W.entrySp W.core₀ W.retAddr m holes
  limit : m.core.memory.read64 (W.ctx - 56) = W.limit
  limitData : ReadableData holes (W.ctx - 56) 8
  top : W.entrySp.toNat + 64 ≤ 2 ^ 64
  low : maxFrame + slack ≤ W.limit.toNat
  /-- The wrapper calls with room for a frame without a stack check. -/
  room : W.limit.toNat + slack ≤ W.entrySp.toNat

/-- A running Xl state in the stacked machine: the running activation
`fr`/`a` with return frame `ret`, and the suspended ones `below`. -/
structure Match (S : Stk) (W : Wrap) (s : Xl.State) (m : Machine) (holes : Holes) (fr : Xl.Frame) (a : Act)
    (ret : ReturnFrame) (below : List (Xl.Frame × Act × ReturnFrame)) : Prop where
  running : m.status = .running
  stack : s.stack = fr :: below.map (·.1)
  returns : m.returns = ret :: below.map (·.2.2)
  ctx : s.ctx = W.ctx
  top : ∃ f l pl, Top S W s m holes fr a ret f l pl
  chain : Chain S W m.core.memory holes fr a ret below
  global : Global W s.mem m holes

end Compilatrix.Xv.Stacking.Proof
