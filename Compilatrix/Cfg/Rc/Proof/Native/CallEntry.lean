import Compilatrix.Cfg.Rc.Proof.Native.EntryWords
import Compilatrix.Cfg.Rc.Proof.Physical.ConsumedMarkers

/-! Execute an actual source call from its consumed lowering cursor. Argument
words, the native call statement, the callee entry, and the suspended caller
position are all derived from admitted syntax and the current word relation.
The initial heap and all older caller frames remain literally unchanged. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs

theorem consume_user_call {P : Program} {x f : Nat} {args : List Fir.Arg}
    (range : f < P.base.size) :
    consume P (layoutOf P) (.bind x (.fir (.call f args))) =
      .ok (.bind x (.fir (.call f args))) := by
  simp [consume, reserved, show f ≠ P.base.size by omega,
    show f ≠ P.base.size + 1 by omega, pure, Except.pure]

/-- A non-tail call spends exactly one charge before its callee body.
Unrepresentable literal operands instead follow the actual emitted failure
branch. This proof does not assume a native call or native entry succeeds. -/
theorem consumed_user_call_entry {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs
      (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) source target)
    {x f : Nat} {args : List Fir.Arg} {tail : List Cfg.Instr}
    (head : source.rest = .bind x (.fir (.call f args)) :: tail)
    {callerFunction : Cfg.Fun}
    (callerLookup : (consumed P pairs).fun? source.fn = some callerFunction)
    {addresses : AddressMap} {bound : Nat} {sourceEnv : Own.Env}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) callerFunction)
      bound sourceEnv target.env)
    {values : List Own.RVal} (arguments : Own.evalArgs sourceEnv args = some values)
    (range : f < P.base.size) {fd : Cfg.Fun} {block : Cfg.Block}
    (lookup : P.base.fun? f = some fd) (blockLookup : fd.blocks[0]? = some block)
    {calleeBound : Nat} (arity : block.params.length = values.length)
    (real : ∀ y ∈ block.params.map Prod.fst, y < calleeBound)
    (running : target.dsts = [])
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    let suspended := {target with pos := target.pos + 1, dsts := [x]}
    let calleeEnv := Own.bindAll .leaf (block.params.map Prod.fst) values
    (∃ consumedFd targetEnv offset,
      (consumed P pairs).fun? f = some consumedFd ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} 1
        (Lir.atState mem context f offset 0 targetEnv (suspended :: callers)) ∧
      ConsumedCursor P pairs lp {fn := f, blk := 0, rest := block.body, env := calleeEnv}
        {fn := f, label := offset, pos := 0, env := targetEnv} ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) consumedFd)
        calleeBound calleeEnv targetEnv ∧
      ConsumedCursor P pairs lp {source with rest := tail} suspended ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) callerFunction)
        bound sourceEnv suspended.env) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  dsimp only
  have decision := consume_user_call (x := x) (args := args) range
  rcases cursor.call head decision mem context callers with success | failed
  · obtain ⟨operands, function, output, operandsLowered, functionLookup,
      outputLookup, position, statement, continuation⟩ := success
    have live := consumed_call_live cursor head decision callerLookup
    obtain ⟨words, evaluated, represented, _⟩ :=
      fused_operands_words registers operandsLowered live arguments
    obtain ⟨consumedFd, callee, targetEnv, offset, consumedLookup, entered,
      entryTrace, entryCursor, entryWords⟩ := consumed_entry_words consuming lowered main
        range lookup blockLookup represented arity real mem context
          ({target with pos := target.pos + 1, dsts := [x]} :: callers)
    have called := Lir.step_call (mem := mem) (ctx := context) (rest := callers)
      functionLookup outputLookup position statement evaluated entered
    refine .inl ⟨consumedFd, targetEnv, offset, consumedLookup,
      ?_, entryCursor, entryWords, ?_, registers⟩
    · simpa using (Lir.star_of_step called).trans entryTrace
    · exact continuation.withEnvs source.env target.env [x]
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        {mem, ctx := context, stack := target :: callers} := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failed
    exact failed



end Compilatrix.Cfg.Rc.Native.Spec
