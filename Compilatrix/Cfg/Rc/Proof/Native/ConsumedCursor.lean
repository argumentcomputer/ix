import Compilatrix.Cfg.Rc.Proof.Native.Cursor

/-! Pair the original RC instruction stream with the consumed instruction
stream used by ordinary Rt lowering. The latter is a syntax/layout cursor;
its ordinary call instructions are never assigned the source RC semantics. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec

def ConsumedCursor (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (source : Cfg.Frame) (target : Lir.Frame) : Prop :=
  ∃ rest, source.rest.mapM (consume P (layoutOf P)) = .ok rest ∧
    Cursor (tablesOf P pairs) (consumed P pairs) lp {source with rest} target

theorem ConsumedCursor.withEnvs {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs lp source target)
    (sourceEnv : Own.Env) (targetEnv : Lir.Env) (destinations : List Nat) :
    ConsumedCursor P pairs lp {source with env := sourceEnv}
      {target with env := targetEnv, dsts := destinations} := by
  obtain ⟨rest, lowering, position⟩ := cursor
  exact ⟨rest, lowering, position.withEnvs sourceEnv targetEnv destinations⟩

/-- Recover the actual successful consuming decision and remaining syntax
at the current source instruction. -/
theorem ConsumedCursor.next {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs lp source target)
    {instruction : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = instruction :: tail) :
    ∃ actual rest,
      consume P (layoutOf P) instruction = .ok actual ∧
      tail.mapM (consume P (layoutOf P)) = .ok rest ∧
      Cursor (tablesOf P pairs) (consumed P pairs) lp
        {source with rest := actual :: rest} target := by
  obtain ⟨rest, lowering, position⟩ := cursor
  rw [head, List.mapM_cons] at lowering
  cases hc : consume P (layoutOf P) instruction with
  | error e => simp [hc, bind, Except.bind] at lowering
  | ok actual =>
    cases ht : tail.mapM (consume P (layoutOf P)) with
    | error e => simp [hc, ht, bind, Except.bind] at lowering
    | ok remaining =>
      simp only [hc, ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowering
      subst rest
      exact ⟨actual, remaining, rfl, rfl, position⟩

/-- Start an actual consumed chunk from the admitted source-function receipt.
The exact chunk head is derived from the accepted raw lowering. -/
theorem ConsumedCursor.head {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {f i : Nat} (range : f < P.base.size)
    {fd : Cfg.Fun} {block : Cfg.Block} (lookup : P.base.fun? f = some fd)
    (blockLookup : fd.blocks[i]? = some block) (sourceEnv : Own.Env) (targetEnv : Lir.Env) :
    ∃ offset, ConsumedCursor P pairs
      (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      {fn := f, blk := i, rest := block.body, env := sourceEnv}
      {fn := f, label := offset, pos := 0, env := targetEnv} := by
  obtain ⟨original, consumedFd, starts, originalLookup, receipt, consumedLookup, targetLookup, layout⟩ :=
    Public.Spec.source_raw_layout consuming lowered main range
  rw [lookup] at originalLookup
  cases originalLookup
  obtain ⟨body, consumedBody, targetBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  obtain ⟨offset, _, _, _, start, _⟩ := layout.chunk targetBlock
  refine ⟨offset, body, consumedBody, ?_⟩
  exact Cursor.head consumedLookup targetLookup layout targetBlock start sourceEnv targetEnv

/-- Current source admission and the raw lowering cursor supply the exact
call statement and rebuilt continuation cursor, or actual Nat overflow. -/
theorem ConsumedCursor.call {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs lp source target)
    {instruction : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = instruction :: tail)
    {x callee : Nat} {args : List Fir.Arg}
    (consuming : consume P (layoutOf P) instruction = .ok (.bind x (.fir (.call callee args))))
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    (∃ operands function block,
      Rt.Lower.operands source.fn args = .ok (some operands) ∧
      lp.funcs[target.fn]? = some function ∧ function.blocks[target.label]? = some block ∧
      ∃ position : target.pos < block.body.size,
        block.body[target.pos] = .call [x] callee operands ∧
        ConsumedCursor P pairs lp {source with rest := tail} {target with pos := target.pos + 1}) ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context target.fn target.label target.pos target.env callers) := by
  obtain ⟨actual, rest, hc, ht, position⟩ := cursor.next head
  rw [consuming] at hc
  cases hc
  rcases position.call rfl mem context callers with success | failed
  · obtain ⟨operands, function, block, hop, hf, hb, hp, hs, next⟩ := success
    exact .inl ⟨operands, function, block, hop, hf, hb, hp, hs, rest, ht, next⟩
  · exact .inr failed





end Compilatrix.Cfg.Rc.Native.Spec
