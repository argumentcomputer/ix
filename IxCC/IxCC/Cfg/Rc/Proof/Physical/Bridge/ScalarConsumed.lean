import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarCursor
import IxCC.Cfg.Rc.Proof.Native.FrameState
import IxCC.Cfg.Rc.Proof.Native.Fieldless

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec
open IxCC.Lir (Word)

theorem consume_pure {P : Program} {layout : Layout} {x : Nat} {rhs : Own.Rhs}
    (pureRhs : PureRhs rhs) {actual : Cfg.Instr}
    (accepted : consume P layout (.bind x rhs) = .ok actual) : actual = .bind x rhs := by
  match rhs, pureRhs with
  | .fir (.arg a), _ =>
    simpa [consume, reserved, isReuseOp, pure, Except.pure] using accepted.symm
  | .fir (.prim op args), _ =>
    simpa [consume, reserved, isReuseOp, pure, Except.pure] using accepted.symm
  | .alloc c args kind, fieldless =>
    change c.fieldless = true at fieldless
    have zero : c.arity = 0 := by simpa only [Fir.CtorInfo.fieldless, beq_iff_eq] using fieldless
    exact (consume_fieldless zero accepted).2.2.2.2.2.2.2
  | .fir (.call ..), impossible | .fir (.ctor ..), impossible | .fir (.proj ..), impossible
  | .proj .., impossible => exact False.elim impossible

theorem tablesOf_boolsOk (P : Program) (pairs : List (Nat × Cfg.Fun)) :
    BoolsOk (tablesOf P pairs) := by
  exact tables_boolsOk (consumed P pairs)

/-- A pure binding of a function with a raw register is on the raw path, by the accepted flow
check: a 64-bit word operation `rawPrim` takes, or a copy into a raw register. -/
theorem rawPure_of_flows {P : Program} {pairs : List (Nat × Cfg.Fun)} {f x : Nat} {rhs : Own.Rhs}
    (pureRhs : PureRhs rhs) (raw : Raw.rawFnInstr P.raw (consumed P pairs) f (.bind x rhs) = true)
    (flows : Raw.instrOk P.raw (consumed P pairs) f (.bind x rhs) = true) :
    RawPure (tablesOf P pairs) f x rhs := by
  match rhs, pureRhs with
  | .fir (.arg a), _ =>
    simp only [Raw.rawFnInstr] at raw
    simp only [Raw.instrOk, raw] at flows
    exact ⟨raw, flows⟩
  | .fir (.prim op as), _ =>
    cases op
    all_goals (first | (simp [Raw.rawFnInstr] at raw; done) | skip)
    all_goals (cases ‹Src.Width› <;>
      first | exact raw | simpa [rawPrim, Raw.rawFnInstr] using raw | simp [Raw.rawFnInstr] at raw)
  | .alloc c args kind, _ => simp [Raw.rawFnInstr] at raw
  | .fir (.call ..), impossible | .fir (.ctor ..), impossible | .fir (.proj ..), impossible
  | .proj .., impossible => exact False.elim impossible

/-- The full source map, its real bound and constructor compatibility survive
an actual consumed scalar instruction. Every code/operand receipt comes from
the cursor; the resource branch is the emitted target failure. -/
theorem frame_step {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    (consuming : consumeAll P = .ok pairs) (rawChecked : Raw.rawOk P.raw (consumed P pairs) = true)
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
  have range := consumed_lookup_lt consuming before.lookup
  have flows : (∀ y, (tablesOf P pairs).rawVar source.fn y = false) ∨
      RawPure (tablesOf P pairs) source.fn x rhs := by
    rcases before.cursor.rawCases head accepted rawChecked range with noRaw | raw
    · exact .inl noRaw
    · exact .inr (rawPure_of_flows pureRhs raw
        (before.cursor.instrOk head accepted rawChecked range))
  obtain ⟨same, result⟩ := cursor_step (source := {source with rest := .bind x rhs :: rest})
    (tablesOf_boolsOk P pairs) pow gcd before.lookup position
    before.words before.raws before.compatible before.bounded supply rfl pureRhs real flows
    sourceEffect mem context callers
  refine ⟨same, ?_⟩
  have initial : ({mem, ctx := context, stack := target :: callers} : Lir.State) =
      Lir.atState mem context target.fn target.label target.pos target.env callers :=
    state_eq rfl running
  rcases result with ⟨charge, after, afterRunning, trace, next, words, raws, ctors, bounded, done⟩ |
      failed
  · have final : ({mem, ctx := context, stack := after :: callers} : Lir.State) =
        Lir.atState mem context after.fn after.label after.pos after.env callers :=
      state_eq rfl afterRunning
    refine .inl ⟨charge, after, afterRunning, ?_,
      ⟨before.lookup, ⟨rest, remaining, next⟩, words, raws, bounded, ctors⟩, ?_⟩
    · rw [initial, final]
      exact trace
    · intro block blockLookup init cond a b fused empty
      have tailEmpty : tail = [] := empty
      rw [tailEmpty] at remaining
      have restEmpty : rest = [] := by simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using remaining.symm
      exact done block blockLookup init cond a b fused restEmpty
  · exact .inr (by rw [initial]; exact failed)




end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
