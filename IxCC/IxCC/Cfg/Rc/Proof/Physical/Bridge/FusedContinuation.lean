import IxCC.Cfg.Rc.Proof.Native.ConsumedCursor

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Cfg.Rc.Native.Spec IxCC.Cfg.Rc.Native
open IxCC.Rt.Lower IxCC.Rt.Proof

theorem consumed_call_done {P : Cfg.Rc.Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {source : Cfg.Frame} {target : Lir.Frame} {fd : Cfg.Fun}
    (lookup : (consumed P pairs).fun? source.fn = some fd)
    (cursor : ConsumedCursor P pairs lp source target)
    {instruction : Cfg.Instr} {tail : List Cfg.Instr}
    (head : source.rest = instruction :: tail)
    {x callee : Nat} {args : List Fir.Arg}
    (accepted : consume P (layoutOf P) instruction = .ok (.bind x (.fir (.call callee args))))
    (env : Own.Env) :
    ∀ block, fd.blocks[source.blk]? = some block →
      FusedDone (tablesOf P pairs) fd block {source with rest := tail, env} := by
  obtain ⟨actual, rest, accepted', remaining, position⟩ := cursor.next head
  rw [accepted] at accepted'
  cases accepted'
  obtain ⟨fd', block, function, starts, off, chunk, state, final, lookup', blockLookup,
    _, _, _, _, _, _, _, _, _, ⟨pre, body⟩, _⟩ := position
  rw [lookup] at lookup'
  cases lookup'
  intro block' blockLookup' init cond a b fused empty
  rw [blockLookup] at blockLookup'
  cases blockLookup'
  have tailEmpty : tail = [] := empty
  rw [tailEmpty] at remaining
  have restEmpty : rest = [] := by simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using remaining.symm
  rw [restEmpty] at body
  obtain ⟨y, op, _, _, impossible, _⟩ := fused_last fused body
  simp only [Cfg.Instr.bind.injEq] at impossible
  cases impossible.2


end IxCC.Cfg.Rc.Proof.Physical.Bridge
