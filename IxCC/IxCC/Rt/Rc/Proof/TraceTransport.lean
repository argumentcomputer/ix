import IxCC.Rt.Rc.Proof.LocalTransport

namespace IxCC.Rt.Rc.Procs
open Lir

/-- Lift any actual finite trace of a syntactically call-free function. The
suspended callers are unchanged at every non-return step. -/
theorem local_star_transport (f : Func) (hfree : CallFree f) (P : Program) (fn : Nat)
    (hfn : P.funcs[fn]? = some f) (context : Word) (callers : List Frame)
    {start finish : State} {charges : Nat}
    (path : Sem.Star (semStep (localProgram f)) start charges finish) :
    ∀ mem frame, frame.fn = 0 → start = localState mem context frame →
      ∃ mem' nextFrame,
        finish = localState mem' context nextFrame ∧ nextFrame.fn = 0 ∧
        Sem.Star (semStep P) (ambientState mem context fn frame callers) charges
          (ambientState mem' context fn nextFrame callers) := by
  induction path with
  | refl start =>
    intro mem frame hzero he
    exact ⟨mem, frame, he, hzero, .refl _⟩
  | free hs rest ih =>
    intro mem frame hzero he
    have hs' : step (localProgram f) (localState mem context frame) = .next _ false :=
      semStep_next.mp (by simpa only [he] using hs)
    obtain ⟨mem', fr', hn, hz, ht⟩ := local_next_transport f hfree P fn hfn mem context frame hzero callers hs'
    obtain ⟨mem'', fr'', hf, hz', hp⟩ := ih mem' fr' hz hn
    exact ⟨mem'', fr'', hf, hz', .free (semStep_next.mpr ht) hp⟩
  | charge hs rest ih =>
    intro mem frame hzero he
    have hs' : step (localProgram f) (localState mem context frame) = .next _ true :=
      semStep_next.mp (by simpa only [he] using hs)
    obtain ⟨mem', fr', hn, hz, ht⟩ := local_next_transport f hfree P fn hfn mem context frame hzero callers hs'
    obtain ⟨mem'', fr'', hf, hz', hp⟩ := ih mem' fr' hz hn
    exact ⟨mem'', fr'', hf, hz', .charge (semStep_next.mpr ht) hp⟩

/-- A standalone successful return binds exactly the caller's declared
result registers and resumes its already-advanced position in the ambient
program. The final memory is the procedure's actual changed memory. -/
theorem local_return_transport (f : Func) (P : Program) (fn : Nat)
    (hfn : P.funcs[fn]? = some f) (mem : X86.Memory) (context : Word) (frame : Frame)
    (hzero : frame.fn = 0) (caller : Frame) (callers : List Frame)
    {values : List Word} {finalMem : X86.Memory} {env : Env}
    (hs : step (localProgram f) (localState mem context frame) = .done values finalMem)
    (hbind : bindParams caller.env caller.dsts values = some env) :
    step P (ambientState mem context fn frame (caller :: callers)) =
      .next { mem := finalMem, ctx := context, stack := {caller with env, dsts := []} :: callers } false := by
  have hlocal : (localProgram f).funcs[frame.fn]? = some f := by simp [localProgram, hzero]
  simp only [step, localState, ambientState, hlocal, hfn] at hs ⊢
  cases hb : f.blocks[frame.label]? with
  | none => simp [hb] at hs
  | some block =>
    simp only [hb] at hs ⊢
    by_cases hpos : frame.pos < block.body.size
    · simp only [dif_pos hpos] at hs
      cases hi : block.body[frame.pos] with
      | call dsts callee args =>
        simp only [hi] at hs
        cases he : evalArgs frame.env args >>= enter (localProgram f) callee <;> simp [he] at hs
      | assign x rhs =>
        simp only [hi] at hs
        cases he : (Stmt.assign x rhs).exec frame.env mem context <;> simp [he] at hs
      | store width addr value =>
        simp only [hi] at hs
        cases he : (Stmt.store width addr value).exec frame.env mem context <;> simp [he] at hs
    · simp only [dif_neg hpos] at hs ⊢
      have edge_not_done (env : Env) (edge : Edge) :
          takeEdge f (localState mem context frame) frame [] env edge ≠ .done values finalMem := by
        unfold takeEdge
        cases evalArgs env edge.args <;> cases f.blocks[edge.target]? <;> simp
        split <;> simp
      cases ht : block.term with
      | jump edge => exact False.elim (edge_not_done _ _ (by simpa only [ht, localState] using hs))
      | br cond width a b yes no =>
        simp only [ht] at hs
        cases ha : a.eval frame.env <;> cases hb : b.eval frame.env <;> simp only [ha, hb] at hs
        all_goals first | cases hs | exact False.elim (edge_not_done _ _ hs)
      | brOvf op x a b yes no =>
        simp only [ht] at hs
        cases ha : a.eval frame.env <;> cases hb : b.eval frame.env <;> simp only [ha, hb] at hs
        all_goals first | cases hs | exact False.elim (edge_not_done _ _ hs)
      | ret args =>
        simp only [ht] at hs ⊢
        cases he : evalArgs frame.env args with
        | none => simp [he] at hs
        | some vals =>
          simp only [he] at hs ⊢
          cases hs
          simp only [hbind]
      | tail callee args =>
        simp only [ht] at hs
        cases he : evalArgs frame.env args >>= enter (localProgram f) callee <;> simp [he] at hs
      | fail resource => simp [ht] at hs
      | trap => simp [ht] at hs



end IxCC.Rt.Rc.Procs
