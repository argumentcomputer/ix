import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionSem
import IxCC.Own.Plain.Proof.RhsShape
import IxCC.Cfg.Rc.Proof.Native.FrameState

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC.Rt.Rc
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Native.Spec IxCC.Cfg.Rc.Native
open IxCC.Lir (Word)

/-- A projection reads and writes tagged registers (the flow check): the raw ones keep their
words, and the tagged relation over the omitted registers survives. -/
theorem projection_cursor {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} {fd : Cfg.Fun}
    (lookup : P.fun? source.fn = some fd) (cursor : Cursor T P lp source target)
    {addresses : AddressMap} {bound : Nat} {H : Own.Heap} {mem : X86.Memory}
    (physical : Gen.HeapLive H addresses mem) (compatible : HeapCtorOk T H) (ordered : Own.Rc.HeapOk H)
    (words : FusedWords addresses (Omit T source.fn fd) bound source.env target.env)
    (raws : RawWords (T.rawVar source.fn) source.env target.env)
    (ctors : FusedCtorOk T (Fused T fd) source.env)
    (bounded : Own.Plain.EnvBounded H.size source.env)
    {x y i : Nat} {key : Key.CtorKey} {tail : List Cfg.Instr}
    (head : source.rest = .bind x (.proj y key i) :: tail) (real : x < bound)
    (taggedX : T.rawVar source.fn x = false) (taggedY : T.rawVar source.fn y = false)
    {value : Own.RVal}
    (effect : Own.evalRhs .rc (ownTables T) source.env H (.proj y key i) = .ok (value, H))
    (context : Word) (callers : List Lir.Frame) :
    (∃ after, after.dsts = [] ∧
      Sem.Star (Lir.semStep lp)
        (Lir.atState mem context target.fn target.label target.pos target.env callers) 0
        (Lir.atState mem context after.fn after.label after.pos after.env callers) ∧
      Cursor T P lp {source with rest := tail, env := source.env.insert x value} after ∧
      FusedWords addresses (Omit T source.fn fd) bound (source.env.insert x value) after.env ∧
      RawWords (T.rawVar source.fn) (source.env.insert x value) after.env ∧
      FusedCtorOk T (Fused T fd) (source.env.insert x value) ∧
      Own.Plain.EnvBounded H.size (source.env.insert x value) ∧
      ∀ block, fd.blocks[source.blk]? = some block →
        FusedDone T fd block {source with rest := tail, env := source.env.insert x value}) ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context target.fn target.label target.pos target.env callers) := by
  obtain ⟨_, parent, fields, _, view, field⟩ := evalRhs_proj effect
  have valueBound := Own.Plain.asCtor_bounded ordered T.known view value (List.mem_of_getElem? field)
  obtain ⟨otherFd, block, function, starts, off, chunk, state, final, sourceLookup, blockLookup,
    targetLookup, layout, start, held, lowering, extension, labeled, opened, fresh,
    ⟨pre, body⟩, fn, label, pos⟩ := cursor
  rw [lookup] at sourceLookup
  cases sourceLookup
  rw [head] at lowering body
  have live : ¬ Fused T fd y := instr_live blockLookup body y (by simp [Cfg.Check.rhsVars])
  have kept : ¬ Omit T source.fn fd y := by
    rintro (omitted | raw)
    · exact live omitted
    · rw [taggedY] at raw; cases raw
  have omitCtors : FusedCtorOk T (Omit T source.fn fd) source.env :=
    fun z v found notOmitted => ctors z v found (fun omitted => notOmitted (.inl omitted))
  have unfused : (fusable T (useCounts fd) block).isSome = true → tail ≠ [] := by
    intro someFused empty
    subst tail
    obtain ⟨⟨init, cond, a, b⟩, fused⟩ := Option.isSome_iff_exists.1 someFused
    obtain ⟨_, _, _, _, impossible, _⟩ := fused_last fused body
    simp only [Cfg.Instr.bind.injEq] at impossible
    cases impossible.2
  obtain ⟨continues, next, lowered, ⟨rfl, rest⟩ | ⟨rfl, rfl⟩⟩ := rest_cons lowering unfused
  · obtain ⟨grows, labeled', opened'⟩ := instr_mono lowered labeled opened
    have nextExt : Ext chunk next := (rest_grows rest labeled' opened').ext extension
    have projection : (Lower.proj source.fn T x y key i).run state = .ok ((), next) := by
      simp only [instr, bind, StateT.bind, StateT.run, pure, StateT.pure, Except.bind, Except.pure] at lowered
      revert lowered
      cases h : Lower.proj source.fn T x y key i state with
      | error e => simp
      | ok v => intro lowered; simp only [Except.ok.injEq, Prod.mk.injEq] at lowered
                rw [StateT.run, h, ← lowered.2]
    obtain ⟨_, registers, trace, related, same⟩ := projection_sim targetLookup held projection nextExt
      opened real kept callers physical compatible (EnvRel.of_fused words omitCtors) effect (ctx := context)
    let after : Lir.Frame := {fn := source.fn, label := off + next.cur, pos := next.acc.length, env := registers}
    obtain ⟨afterWords, afterCtors⟩ := related.to_fused
    have fusedCtors : FusedCtorOk T (Fused T fd) (source.env.insert x value) := by
      intro z v found notFused
      rw [Src.NatMap.get?_insert] at found
      split at found
      · rename_i equal
        subst equal
        refine afterCtors z v (by rw [Src.NatMap.get?_insert_self]; exact found) ?_
        rintro (omitted | raw)
        · exact notFused omitted
        · rw [taggedX] at raw; cases raw
      · exact ctors z v found notFused
    refine .inl ⟨after, rfl, ?_, ?_, afterWords,
      raws.insert_tagged words.dom taggedX value (fun z _ ne => same z ne), fusedCtors,
      bounded.insert x valueBound, ?_⟩
    · simpa only [fn, label, pos] using trace
    · exact ⟨fd, block, function, starts, off, chunk, next, final, lookup, blockLookup, targetLookup,
        layout, start, held, rest, extension, labeled', opened', Nat.le_trans fresh grows.fresh,
        ⟨pre ++ [.bind x (.proj y key i)], by simpa using body⟩, rfl, rfl, rfl⟩
    · intro block' blockLookup'
      rw [blockLookup] at blockLookup'
      cases blockLookup'
      intro init cond a b fused empty
      exact False.elim (unfused (by simp [fused]) empty)
  · right
    rw [fn, label, pos]
    exact instr_fails targetLookup held lowered extension opened mem target.env callers

theorem projection_frame {P : Cfg.Rc.Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    (consuming : consumeAll P = .ok pairs) (rawChecked : Raw.rawOk P.raw (consumed P pairs) = true)
    {addresses : AddressMap} {H : Own.Heap} {bound : Nat} {fd : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs lp addresses H.size bound fd source target)
    {mem : X86.Memory} (physical : Gen.HeapLive H addresses mem)
    (compatible : HeapCtorOk (tablesOf P pairs) H) (ordered : Own.Rc.HeapOk H)
    {x y i : Nat} {key : Key.CtorKey} {tail : List Cfg.Instr}
    (head : source.rest = .bind x (.proj y key i) :: tail) (real : x < bound)
    {value : Own.RVal}
    (effect : Own.evalRhs .rc P.base.tables source.env H (.proj y key i) = .ok (value, H))
    (running : target.dsts = []) (context : Word) (callers : List Lir.Frame) :
    (∃ after, after.dsts = [] ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} 0
        {mem, ctx := context, stack := after :: callers} ∧
      FrameState P pairs lp addresses H.size bound fd
        {source with rest := tail, env := source.env.insert x value} after ∧
      ∀ block, fd.blocks[source.blk]? = some block →
        FusedDone (tablesOf P pairs) fd block {source with rest := tail, env := source.env.insert x value}) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨actual, rest, accepted, remaining, position⟩ := before.cursor.next head
  have same : actual = .bind x (.proj y key i) := by
    simpa [consume, Cfg.Rc.reserved, Cfg.Rc.isReuseOp, pure, Except.pure] using accepted.symm
  subst actual
  have flows := before.cursor.instrOk head accepted rawChecked
    (consumed_lookup_lt consuming before.lookup)
  simp only [Raw.instrOk, Cfg.Check.rhsVars, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, Bool.not_eq_true'] at flows
  have initial : ({mem, ctx := context, stack := target :: callers} : Lir.State) =
      Lir.atState mem context target.fn target.label target.pos target.env callers := state_eq rfl running
  rcases projection_cursor (source := {source with rest := .bind x (.proj y key i) :: rest})
      before.lookup position physical compatible ordered before.words before.raws before.compatible
      before.bounded rfl real flows.1 flows.2 effect context callers with success | failed
  · obtain ⟨after, running', trace, next, words, raws, ctors, bounded, fused⟩ := success
    refine .inl ⟨after, running', ?_,
      ⟨before.lookup, ⟨rest, remaining, next⟩, words, raws, bounded, ctors⟩, ?_⟩
    · rw [initial, state_eq (s := {mem, ctx := context, stack := after :: callers}) rfl running']
      exact trace
    · intro block blockLookup init cond a b isFused empty
      have tailEmpty : tail = [] := empty
      rw [tailEmpty] at remaining
      have restEmpty : rest = [] := by
        simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using remaining.symm
      exact fused block blockLookup init cond a b isFused restEmpty
  · exact .inr (by rw [initial]; exact failed)



end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
