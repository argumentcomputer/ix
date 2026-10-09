import Compilatrix.Lir.Proof.Run

namespace Compilatrix.Rt.Rc.Procs
open Lir

/-- Embed one call-free activation at an arbitrary function index above an
unchanged suspended caller stack. -/
def localState (mem : X86.Memory) (context : Word) (frame : Frame) : State :=
  { mem, ctx := context, stack := [frame] }
def ambientState (mem : X86.Memory) (context : Word) (fn : Nat) (frame : Frame)
    (callers : List Frame) : State :=
  { mem, ctx := context, stack := {frame with fn} :: callers }

def localProgram (f : Func) : Program := { funcs := #[f], main := 0 }

def CallFree (f : Func) : Prop :=
  (∀ b ∈ f.blocks, ∀ stmt ∈ b.body, ∀ dsts callee args, stmt ≠ .call dsts callee args) ∧
  (∀ b ∈ f.blocks, ∀ callee args, b.term ≠ .tail callee args)

/-- Branch transport is independent of caller registers and function number;
only the current function's block table participates in an edge. -/
theorem takeEdge_transport (f : Func) (mem : X86.Memory) (context : Word)
    (frame : Frame) (env : Env) (edge : Edge) (fn : Nat) (callers : List Frame)
    {next : State} {charge : Bool}
    (h : takeEdge f (localState mem context frame) frame [] env edge = .next next charge) :
    ∃ nextFrame,
      next = localState mem context nextFrame ∧ nextFrame.fn = frame.fn ∧
      takeEdge f (ambientState mem context fn frame callers) {frame with fn} callers env edge =
        .next (ambientState mem context fn nextFrame callers) charge := by
  unfold takeEdge at h ⊢
  cases he : evalArgs env edge.args with
  | none => simp [he] at h
  | some values =>
    cases hb : f.blocks[edge.target]? with
    | none => simp [he, hb] at h
    | some target =>
      cases hp : bindParams env target.params values with
      | none => simp [he, hb, hp] at h
      | some env' =>
        simp only [he, hb, hp] at h ⊢
        cases h
        exact ⟨{frame with label := edge.target, pos := 0, env := env'}, rfl, rfl, rfl⟩


end Compilatrix.Rt.Rc.Procs

namespace Compilatrix.Rt.Rc.Procs
open Lir

theorem local_next_transport (f : Func) (hfree : CallFree f) (P : Program) (fn : Nat)
    (hfn : P.funcs[fn]? = some f) (mem : X86.Memory) (context : Word) (frame : Frame)
    (hzero : frame.fn = 0) (callers : List Frame) {next : State} {charge : Bool}
    (hs : step (localProgram f) (localState mem context frame) = .next next charge) :
    ∃ mem' nextFrame,
      next = localState mem' context nextFrame ∧ nextFrame.fn = 0 ∧
      step P (ambientState mem context fn frame callers) =
        .next (ambientState mem' context fn nextFrame callers) charge := by
  have hlocal : (localProgram f).funcs[frame.fn]? = some f := by simp [localProgram, hzero]
  simp only [step, localState, ambientState, hlocal, hfn] at hs ⊢
  cases hb : f.blocks[frame.label]? with
  | none => simp [hb] at hs
  | some block =>
    simp only [hb] at hs ⊢
    have hmem : block ∈ f.blocks := Array.mem_of_getElem? hb
    by_cases hpos : frame.pos < block.body.size
    · simp only [dif_pos hpos] at hs ⊢
      have hstmt : block.body[frame.pos] ∈ block.body := Array.getElem_mem hpos
      cases hi : block.body[frame.pos] with
      | call dsts callee args => exact False.elim (hfree.1 block hmem _ hstmt dsts callee args hi)
      | assign x rhs =>
        simp only [hi] at hs ⊢
        cases he : (Stmt.assign x rhs).exec frame.env mem context with
        | none => simp [he] at hs
        | some result =>
          rcases result with ⟨env', mem'⟩
          simp only [he] at hs ⊢
          cases hs
          exact ⟨mem', {frame with pos := frame.pos+1, env := env'}, rfl, hzero, rfl⟩
      | store width address value =>
        simp only [hi] at hs ⊢
        cases he : (Stmt.store width address value).exec frame.env mem context with
        | none => simp [he] at hs
        | some result =>
          rcases result with ⟨env', mem'⟩
          simp only [he] at hs ⊢
          cases hs
          exact ⟨mem', {frame with pos := frame.pos+1, env := env'}, rfl, hzero, rfl⟩
    · simp only [dif_neg hpos] at hs ⊢
      have edgeCase (env : Env) (edge : Edge)
          (he : takeEdge f (localState mem context frame) frame [] env edge = .next next charge) :
          ∃ mem' nextFrame, next = localState mem' context nextFrame ∧ nextFrame.fn = 0 ∧
            takeEdge f (ambientState mem context fn frame callers) {frame with fn} callers env edge =
              .next (ambientState mem' context fn nextFrame callers) charge := by
        obtain ⟨nextFrame, hn, hf, ht⟩ := takeEdge_transport f mem context frame env edge fn callers he
        exact ⟨mem, nextFrame, hn, hf.trans hzero, ht⟩
      cases ht : block.term with
      | jump edge => simp only [ht] at hs ⊢; exact edgeCase frame.env edge hs
      | br cond width a b yes no =>
        simp only [ht] at hs ⊢
        cases ha : a.eval frame.env <;> cases hb : b.eval frame.env <;> simp only [ha, hb] at hs ⊢
        all_goals first | cases hs | exact edgeCase _ _ hs
      | brOvf op x a b yes no =>
        simp only [ht] at hs ⊢
        cases ha : a.eval frame.env <;> cases hb : b.eval frame.env <;> simp only [ha, hb] at hs ⊢
        all_goals first | cases hs | exact edgeCase _ _ hs
      | ret args =>
        simp only [ht] at hs
        cases he : evalArgs frame.env args <;> simp [he] at hs
      | tail callee args => exact False.elim (hfree.2 block hmem callee args ht)
      | fail resource => simp [ht] at hs
      | trap => simp [ht] at hs


end Compilatrix.Rt.Rc.Procs
