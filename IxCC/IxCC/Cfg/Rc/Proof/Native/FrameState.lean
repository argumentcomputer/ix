import IxCC.Cfg.Rc.Proof.Native.ReturnResume
import IxCC.Cfg.Rc.Proof.Physical.FusedLexical
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedCtorEnv
import IxCC.Cfg.Rc.Proof.Native.RawFacts

/-! The concrete native activation-frame invariant. Register meanings cover
the entire original RC Cfg environment, including stale bindings; lexical and
saved-join views are restrictions. Neither this relation nor its preservation
lemmas assume execution of a source function or a physical simulation. A raw register holds the
raw word of its `Nat` literal (`raws`); the tagged relation (`words`) omits it. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

structure FrameState (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (addresses : AddressMap) (heapSize bound : Nat) (function : Cfg.Fun)
    (source : Cfg.Frame) (target : Lir.Frame) : Prop where
  lookup : (consumed P pairs).fun? source.fn = some function
  cursor : ConsumedCursor P pairs lp source target
  words : FusedWords addresses (Omit (tablesOf P pairs) source.fn function)
    bound source.env target.env
  raws : RawWords ((tablesOf P pairs).rawVar source.fn) source.env target.env
  bounded : Own.Plain.EnvBounded heapSize source.env
  compatible : FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) source.env

theorem FrameState.lexical {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses heapSize bound function source target)
    {env : Own.Env} (sub : EnvSub env source.env) :
    FusedWords addresses (Omit (tablesOf P pairs) source.fn function) bound env target.env ∧
    Own.Plain.EnvBounded heapSize env ∧
    FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) env ∧
    RawWords ((tablesOf P pairs).rawVar source.fn) env target.env :=
  ⟨before.words.restrict sub, fun x value lookup => before.bounded x value (sub x value lookup),
    fun x value lookup live => before.compatible x value (sub x value lookup) live,
    before.raws.restrict sub⟩

/-- In a function with no raw register the tagged relation is over the fused comparisons. -/
theorem FrameState.fused {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses heapSize bound function source target)
    (noRaw : ∀ y, (tablesOf P pairs).rawVar source.fn y = false) :
    FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound source.env target.env :=
  before.words.toFused noRaw

/-- The frame invariant of a function with no raw register, from the relation over the fused
comparisons. -/
theorem FrameState.ofFused {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (lookup : (consumed P pairs).fun? source.fn = some function)
    (cursor : ConsumedCursor P pairs lp source target)
    (words : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function)
      bound source.env target.env)
    (noRaw : ∀ y, (tablesOf P pairs).rawVar source.fn y = false)
    (bounded : Own.Plain.EnvBounded heapSize source.env)
    (compatible : FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function)
      source.env) :
    FrameState P pairs lp addresses heapSize bound function source target :=
  ⟨lookup, cursor, words.ofFused, RawWords.of_noRaw noRaw, bounded, compatible⟩

/-- Publication changes the interpretation map only at a fresh logical ID.
All suspended and running native frames retain their literal registers. -/
theorem FrameState.placeFresh {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {oldSize newSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses oldSize bound function source target)
    (growth : oldSize ≤ newSize) (address : Lir.Word) :
    FrameState P pairs lp (Native.placeFresh addresses oldSize address) newSize bound function source target :=
  ⟨before.lookup, before.cursor, before.words.placeFresh before.bounded address, before.raws,
    before.bounded.mono growth, before.compatible⟩

/-- Execute the real call and construct complete callee and suspended-frame
invariants. Heap size, memory and caller frames are unchanged during entry;
ownership-root transfer is supplied by the canonical copy/call proof. Arguments reach the
callee's parameters at their raw or tagged positions, as the accepted flow check states. -/
theorem FrameState.call {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (rawChecked : Raw.rawOk P.raw (consumed P pairs) = true)
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
      FrameState P pairs lp addresses heapSize bound function {source with rest := tail} suspended ∧
      (tablesOf P pairs).rawVar source.fn x = false) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  dsimp only
  have live := consumed_call_live before.cursor head (consume_user_call range) before.lookup
  have compatible := before.compatible.args live arguments
  have bounded := before.bounded.args args arguments
  have flows := before.cursor.instrOk head (consume_user_call range) rawChecked
    (consumed_lookup_lt consuming before.lookup)
  simp only [Raw.instrOk, Bool.and_eq_true, beq_iff_eq] at flows
  have destination : (tablesOf P pairs).rawVar source.fn x = false := by
    rw [tablesOf_rawVar, flows.2]
    exact rawOk_retRaw rawChecked f
  rcases consumed_user_call_entry consuming lowered main before.cursor head before.lookup
      before.words before.raws flows.1 arguments range lookup blockLookup arity real running mem
      context callers with success | failed
  · obtain ⟨consumedFd, targetEnv, offset, consumedLookup, trace, entered, words, raws, saved,
      savedWords, savedRaws⟩ := success
    refine .inl ⟨consumedFd, targetEnv, offset, trace, ?_, ?_, destination⟩
    · exact ⟨consumedLookup, entered, words, raws,
        (Own.Plain.envBounded_empty heapSize).bindAll _ bounded,
        FusedCtorOk.empty.bindAll _ _ compatible⟩
    · exact ⟨before.lookup, saved, savedWords, savedRaws, before.bounded, before.compatible⟩
  · exact .inr failed

/-- A returned value updates exactly the destination and restores the saved
whole-frame invariant. Its bound/compatibility are facts about the returned
source value, obtained from the callee's return operand. A call's destination is tagged. -/
theorem FrameState.resume {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {caller returning : Lir.Frame}
    (before : FrameState P pairs lp addresses heapSize bound function source caller)
    {x : Nat} (destination : caller.dsts = [x]) (real : x < bound)
    (notRaw : (tablesOf P pairs).rawVar source.fn x = false)
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
  exact ⟨step, before.lookup, cursor, words,
    before.raws.insert_tagged before.words.dom notRaw value
      (fun y _ ne => Lir.env_insert_ne _ _ (Ne.symm ne)),
    before.bounded.insert x bounded, before.compatible.bind x compatible⟩

end IxCC.Cfg.Rc.Native.Spec
