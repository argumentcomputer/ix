import Compilatrix.Cfg.Rc.Proof.Native.ReturnCursor

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Rt.Lower Compilatrix.Rt.Proof

theorem Cursor.trap {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    {fd : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.fun? source.fn = some fd) (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) (terminal : block.term = .trap)
    (running : target.dsts = []) (memory : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    Lir.step lp {mem := memory, ctx := context, stack := target :: callers} = .trap := by
  obtain ⟨fd', block', function, starts, off, chunk, state, final, sourceLookup', blockLookup',
    functionLookup, layout, start, held, lowering, extension, labeled, opened, supply,
    body, fn, label, pos⟩ := cursor
  have sameFd : fd' = fd := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  subst fd'
  have sameBlock : block' = block := Option.some.inj (blockLookup'.symm.trans blockLookup)
  subst block'
  rw [finished] at lowering
  have code := rest_nil lowering
  have unfused : fusable T (useCounts fd) block = none := by
    cases fused : fusable T (useCounts fd) block with
    | none => rfl
    | some row =>
      obtain ⟨init, condition, left, right⟩ := row
      obtain ⟨x, op, alts, default, _, _, switch, _⟩ := fusable_some fused
      rw [terminal] at switch
      cases switch
  simp only [unfused, terminal] at code
  have closed := term_trap code
  rw [closed] at extension
  obtain ⟨output, outputLookup, size, term⟩ :=
    closedAt_of held (Grows.refl _) extension (t := .trap) rfl
  have same : Lir.atState memory context source.fn (off + state.cur) state.acc.length target.env callers =
      {mem := memory, ctx := context, stack := target :: callers} := by
    rw [← fn, ← label, ← pos]
    cases target
    simp_all [Lir.atState]
  rw [← same]
  exact Lir.trap_at functionLookup outputLookup size.symm term

theorem ConsumedCursor.trap {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : ConsumedCursor P pairs lp source target)
    (range : source.fn < P.base.size) {fd : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.base.fun? source.fn = some fd)
    (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) (terminal : block.term = .trap)
    (running : target.dsts = []) (memory : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    Lir.step lp {mem := memory, ctx := context, stack := target :: callers} = .trap := by
  obtain ⟨original, actual, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming range
  have sourceSame : original = fd := Option.some.inj (originalLookup.symm.trans sourceLookup)
  subst original
  obtain ⟨body, _, targetBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  obtain ⟨rest, consumeRest, position⟩ := cursor
  rw [finished] at consumeRest
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
  subst rest
  exact position.trap consumedLookup targetBlock rfl terminal running memory context callers



end Compilatrix.Cfg.Rc.Native.Spec
