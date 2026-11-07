import IxCC.Cfg.Rc.Proof.Native.EntryCursor
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedBindings

/-! Construct the actual consumed entry cursor and dynamic register relation
together. Entry uses real argument words and the real parameter binding;
omitted comparisons do not force nonexistent native registers into existence. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

theorem consumed_entry_words {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {f : Nat} (range : f < P.base.size)
    {fd : Cfg.Fun} {block : Cfg.Block} (lookup : P.base.fun? f = some fd)
    (blockLookup : fd.blocks[0]? = some block)
    {values : List Own.RVal} {words : List Lir.Word} {addresses : AddressMap} {bound : Nat}
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (arity : block.params.length = values.length)
    (real : ∀ x ∈ block.params.map Prod.fst, x < bound)
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    let sourceEnv := Own.bindAll .leaf (block.params.map Prod.fst) values
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    ∃ consumedFd callee targetEnv offset,
      (consumed P pairs).fun? f = some consumedFd ∧
      Lir.enter lp f words = some callee ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := callee :: callers} 0
        (Lir.atState mem context f offset 0 targetEnv callers) ∧
      ConsumedCursor P pairs lp {fn := f, blk := 0, rest := block.body, env := sourceEnv}
        {fn := f, label := offset, pos := 0, env := targetEnv} ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) consumedFd) bound sourceEnv targetEnv := by
  obtain ⟨_, consumedFd, _, _, consumedLookup⟩ := consumed_entry consuming range
  have wordArity : words.length = block.params.length := represented.length_eq.symm.trans arity.symm
  obtain ⟨callee, prior, targetEnv, offset, entered, binding, trace, cursor⟩ :=
    ConsumedCursor.enter consuming lowered main range lookup blockLookup
      (Own.bindAll .leaf (block.params.map Prod.fst) values) words wordArity mem context callers
  refine ⟨consumedFd, callee, targetEnv, offset, consumedLookup, entered, trace, cursor, ?_⟩
  exact FusedWords.boundParams FusedWords.empty represented (by simpa using arity) real binding


end IxCC.Cfg.Rc.Native.Spec
