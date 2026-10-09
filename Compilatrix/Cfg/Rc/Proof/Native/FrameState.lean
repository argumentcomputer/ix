import Compilatrix.Cfg.Rc.Proof.Native.ReturnResume
import Compilatrix.Cfg.Rc.Proof.Physical.FusedLexical
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedCtorEnv

/-! The concrete native activation-frame invariant. Register meanings cover
the entire original RC Cfg environment, including stale bindings; lexical and
saved-join views are restrictions. Neither this relation nor its preservation
lemmas assume execution of a source function or a physical simulation. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs

structure FrameState (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (addresses : AddressMap) (heapSize bound : Nat) (function : Cfg.Fun)
    (source : Cfg.Frame) (target : Lir.Frame) : Prop where
  lookup : (consumed P pairs).fun? source.fn = some function
  cursor : ConsumedCursor P pairs lp source target
  words : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function)
    bound source.env target.env
  bounded : Own.Plain.EnvBounded heapSize source.env
  compatible : FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) source.env

theorem FrameState.lexical {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses heapSize bound function source target)
    {env : Own.Env} (sub : EnvSub env source.env) :
    FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound env target.env ∧
    Own.Plain.EnvBounded heapSize env ∧
    FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) env :=
  ⟨before.words.restrict sub, fun x value lookup => before.bounded x value (sub x value lookup),
    fun x value lookup live => before.compatible x value (sub x value lookup) live⟩

/-- Publication changes the interpretation map only at a fresh logical ID.
All suspended and running native frames retain their literal registers. -/
theorem FrameState.placeFresh {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {oldSize newSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses oldSize bound function source target)
    (growth : oldSize ≤ newSize) (address : Lir.Word) :
    FrameState P pairs lp (Native.placeFresh addresses oldSize address) newSize bound function source target :=
  ⟨before.lookup, before.cursor, before.words.placeFresh before.bounded address,
    before.bounded.mono growth, before.compatible⟩

/-- Execute the real call and construct complete callee and suspended-frame
invariants. Heap size, memory and caller frames are unchanged during entry;
ownership-root transfer is supplied by the canonical copy/call proof. -/
theorem FrameState.call {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      addresses heapSize bound function source target)
    {x f : Nat} {args : List Fir.Arg} {tail : List Cfg.Instr}
    (head : source.rest = .bind x (.fir (.call f args)) :: tail)
    {values : List Own.RVal} (arguments : Own.evalArgs source.env args = some values)
    (range : f < P.base.size) {fd : Cfg.Fun} {block : Cfg.Block}
    (lookup : P.base.fun? f = some fd) (blockLookup : fd.blocks[0]? = some block)
    {calleeBound : Nat} (arity : block.params.length = values.length)
    (real : ∀ y ∈ block.params.map Prod.fst, y < calleeBound)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    let suspended := {target with pos := target.pos + 1, dsts := [x]}
    let calleeEnv := Own.bindAll .leaf (block.params.map Prod.fst) values
    (∃ consumedFd targetEnv offset,
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} 1
        (Lir.atState mem context f offset 0 targetEnv (suspended :: callers)) ∧
      FrameState P pairs lp addresses heapSize calleeBound consumedFd
        {fn := f, blk := 0, rest := block.body, env := calleeEnv}
        {fn := f, label := offset, pos := 0, env := targetEnv} ∧
      FrameState P pairs lp addresses heapSize bound function {source with rest := tail} suspended) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  dsimp only
  have live := consumed_call_live before.cursor head (consume_user_call range) before.lookup
  have compatible := before.compatible.args live arguments
  have bounded := before.bounded.args args arguments
  rcases consumed_user_call_entry consuming lowered main before.cursor head before.lookup
      before.words arguments range lookup blockLookup arity real running mem context callers with success | failed
  · obtain ⟨consumedFd, targetEnv, offset, consumedLookup, trace, entered, words, saved, savedWords⟩ := success
    refine .inl ⟨consumedFd, targetEnv, offset, trace, ?_, ?_⟩
    · exact ⟨consumedLookup, entered, words,
        (Own.Plain.envBounded_empty heapSize).bindAll _ bounded,
        FusedCtorOk.empty.bindAll _ _ compatible⟩
    · exact ⟨before.lookup, saved, savedWords, before.bounded, before.compatible⟩
  · exact .inr failed

/-- A returned value updates exactly the destination and restores the saved
whole-frame invariant. Its bound/compatibility are facts about the returned
source value, obtained from the callee's return operand. -/
theorem FrameState.resume {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {caller returning : Lir.Frame}
    (before : FrameState P pairs lp addresses heapSize bound function source caller)
    {x : Nat} (destination : caller.dsts = [x]) (real : x < bound)
    {value : Own.RVal} {word : Lir.Word} (represented : valueWord addresses value = some word)
    (bounded : Own.Plain.Bounded heapSize value) (compatible : ValueCtorOk (tablesOf P pairs) value)
    (returned : Rt.Proof.RetAt lp returning word)
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    let resumed := {caller with env := caller.env.insert x word, dsts := []}
    Lir.step lp {mem, ctx := context, stack := returning :: caller :: callers} =
      .next {mem, ctx := context, stack := resumed :: callers} false ∧
    FrameState P pairs lp addresses heapSize bound function
      {source with env := source.env.insert x value} resumed := by
  obtain ⟨step, cursor, words⟩ := return_resume before.cursor destination before.words
    real represented returned mem context callers
  exact ⟨step, before.lookup, cursor, words, before.bounded.insert x bounded,
    before.compatible.bind x compatible⟩





end Compilatrix.Cfg.Rc.Native.Spec
