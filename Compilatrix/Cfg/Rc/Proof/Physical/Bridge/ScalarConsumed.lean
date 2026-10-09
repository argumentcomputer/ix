import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarCursor
import Compilatrix.Cfg.Rc.Proof.Native.FrameState
import Compilatrix.Cfg.Rc.Proof.Native.Fieldless

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Lir (Word)

theorem consume_pure {P : Program} {layout : Layout} {x : Nat} {rhs : Own.Rhs}
    (pureRhs : PureRhs rhs) {actual : Cfg.Instr}
    (accepted : consume P layout (.bind x rhs) = .ok actual) : actual = .bind x rhs := by
  match rhs, pureRhs with
  | .fir (.arg a), _ =>
    simpa [consume, reserved, pure, Except.pure] using accepted.symm
  | .fir (.prim op args), _ =>
    simpa [consume, reserved, pure, Except.pure] using accepted.symm
  | .alloc c args kind, fieldless =>
    change c.fieldless = true at fieldless
    have zero : c.arity = 0 := by simpa only [Fir.CtorInfo.fieldless, beq_iff_eq] using fieldless
    exact (consume_fieldless zero accepted).2.2.2.2.2.2.2
  | .fir (.call ..), impossible | .fir (.ctor ..), impossible | .fir (.proj ..), impossible
  | .proj .., impossible => exact False.elim impossible

theorem tablesOf_boolsOk (P : Program) (pairs : List (Nat × Cfg.Fun)) :
    BoolsOk (tablesOf P pairs) := by
  exact tables_boolsOk (consumed P pairs)

/-- The full source map, its real bound and constructor compatibility survive
an actual consumed scalar instruction. Every code/operand receipt comes from
the cursor; the resource branch is the emitted target failure. -/
theorem frame_step {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    (pow : lp.funcs[(tablesOf P pairs).natPow]? = some Procs.natPow)
    (gcd : lp.funcs[(tablesOf P pairs).natGcd]? = some Procs.natGcd)
    {addresses : AddressMap} {bound size : Nat} {fd : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses size bound fd source target)
    (supply : bound ≤ supOf fd)
    {x : Nat} {rhs : Own.Rhs} {tail : List Cfg.Instr}
    (head : source.rest = .bind x rhs :: tail) (pureRhs : PureRhs rhs) (real : x < bound)
    {H H' : Own.Heap} {value : Own.RVal}
    (effect : Own.evalRhs .rc P.base.tables source.env H rhs = .ok (value, H'))
    (running : target.dsts = [])
    (mem : X86.Memory) (context : Word) (callers : List Lir.Frame) :
    H' = H ∧
    ((∃ charge after, after.dsts = [] ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} charge
        {mem, ctx := context, stack := after :: callers} ∧
      FrameState P pairs lp addresses size bound fd
        {source with rest := tail, env := source.env.insert x value} after ∧
      ∀ block, fd.blocks[source.blk]? = some block →
        FusedDone (tablesOf P pairs) fd block
          {source with rest := tail, env := source.env.insert x value}) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers}) := by
  obtain ⟨actual, rest, accepted, remaining, position⟩ := before.cursor.next head
  have identical := consume_pure pureRhs accepted
  subst actual
  have sourceEffect : Own.evalRhs .rc (ownTables (tablesOf P pairs)) source.env H rhs =
      .ok (value, H') := effect
  obtain ⟨same, result⟩ := cursor_step (source := {source with rest := .bind x rhs :: rest})
    (tablesOf_boolsOk P pairs) pow gcd before.lookup position
    before.words before.compatible before.bounded supply rfl pureRhs real sourceEffect mem context callers
  refine ⟨same, ?_⟩
  have initial : ({mem, ctx := context, stack := target :: callers} : Lir.State) =
      Lir.atState mem context target.fn target.label target.pos target.env callers :=
    state_eq rfl running
  rcases result with ⟨charge, after, afterRunning, trace, next, words, ctors, bounded, done⟩ | failed
  · have final : ({mem, ctx := context, stack := after :: callers} : Lir.State) =
        Lir.atState mem context after.fn after.label after.pos after.env callers :=
      state_eq rfl afterRunning
    refine .inl ⟨charge, after, afterRunning, ?_,
      ⟨before.lookup, ⟨rest, remaining, next⟩, words, bounded, ctors⟩, ?_⟩
    · rw [initial, final]
      exact trace
    · intro block blockLookup init cond a b fused empty
      have tailEmpty : tail = [] := empty
      rw [tailEmpty] at remaining
      have restEmpty : rest = [] := by simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using remaining.symm
      exact done block blockLookup init cond a b fused restEmpty
  · exact .inr (by rw [initial]; exact failed)




end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
