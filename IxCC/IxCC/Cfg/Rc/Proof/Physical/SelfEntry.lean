import IxCC.Cfg.Rc.Proof.Physical.EntryActivation
import IxCC.Cfg.Rc.Proof.Physical.Jump
import IxCC.Cfg.Rc.Proof.Extend

/-! The self-tail back edge over the typing context: a function's tail call to itself re-enters
block zero by its charged edge, keeping the actual Cfg map; the callee starts with exactly its
parameters' tokens. All entry bounds come from admission. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Rt.Proof
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-- The self-tail back edge re-enters block zero with the function's parameters, over the typing
context. The Cfg map is the frame's; the callee starts with exactly its parameters' tokens. -/
theorem self_entry_activation {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (tagged : Rt.Proof.Tagged (tablesOf P pairs)) {lp : Lir.Program}
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat} {priv : Nat → Prop}
    {source : Cfg.Frame} {target : Lir.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {rslots : Src.NatMap Own.RVal}
    {args : List Fir.Arg} {sourceFunction : Fir.Fun} {function : Cfg.Fun}
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    (sourceState : At F P source ρ saved (.tcall source.fn args) rslots)
    (frame : FrameState P pairs lp addresses H.size (funcFirst bodies source.fn sourceFunction)
      function source target)
    {fields : List RVal} {logical : List Fir.Val}
    (arguments : Own.evalArgs ρ args = some fields)
    (den : Sem.Forall2 (Own.Proof.Den H) fields logical)
    (balance : Balance H external (Own.Plain.selectOwnedVals (borrows.getD source.fn []) fields))
    (hbrw : ∀ v, v ∈ Own.Plain.selectBorrowedVals (borrows.getD source.fn []) fields →
      Own.Plain.ReachableFrom H external v)
    (huniq : ∀ v, v ∈ Own.Plain.selectUniqueVals (borrows.getD source.fn [])
        (uniqs.getD source.fn ([], false)).1 fields →
      Own.Plain.UniqVal F.ctors H external (Own.Plain.selectOwnedVals (borrows.getD source.fn []) fields) v)
    (hprivB : ∀ l, priv l → l < H.size)
    (hprivE : ∀ l, priv l → Own.Rc.edgeCount H l = 0)
    (hprivArgs : ∀ l, priv l → ∀ v, v ∈ fields → v ≠ .loc l)
    (arity : fields.length = sourceFunction.params.length)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (callers : List Lir.Frame) :
    let bs := borrows.getD source.fn []
    let us := (uniqs.getD source.fn ([], false)).1
    let retU := (uniqs.getD source.fn ([], false)).2
    (∃ after final cost body,
      Own.Plain.eraseCode body = sourceFunction.body ∧
      Activation F P pairs lp H addresses external (sourceFunction.params.map Prod.fst)
        (Ctx.entryWith (sourceFunction.params.map Prod.fst) bs us) .leaf
        (Fir.bindAll .leaf (sourceFunction.params.map Prod.fst) logical)
        (Own.bindAll .leaf (sourceFunction.params.map Prod.fst) fields)
        (Own.Plain.selectOwnedVals bs fields) [] [] []
        body (funcFirst bodies source.fn sourceFunction) function after final
        borrows uniqs retU priv .leaf [] ∧
      after.fn = source.fn ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} cost
        {mem, ctx := context, stack := final :: callers} ∧ 1 ≤ cost) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨fd, scopeNames, params, acc, next, supply, low, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, names, vb, rc, joins⟩ := sourceState
  have finished : source.rest = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  let edge : Cfg.Edge := {target := 0, args, back := true}
  let block : Cfg.Block := {params, body := acc.reverse, term := .jump edge}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Proof.tcallTerm, ↓reduceIte, Cfg.Fun.block?]
      using layout
  have member : edge ∈ block.term.edges := by simp [block, Cfg.Term.edges]
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  obtain ⟨body, _, bodyLookup, erased, typed, fresh, sourceScope⟩ :=
    checked_owned_body checked sourceLookup
  obtain ⟨entryFd, entryBlock, entryLookup, entryBlockLookup, entryParams, entryLength, _, bounds⟩ :=
    checked_entry_block checked range sourceLookup bodyLookup
  have sameEntry : entryFd = fd := Option.some.inj (entryLookup.symm.trans lookup)
  subst entryFd
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming nativeRange
  have sameOriginal : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst original
  have sameActual : actual = function := Option.some.inj (actualLookup.symm.trans frame.lookup)
  subst actual
  obtain ⟨native, starts, off, chunks, lowLabel, pe, le, nativeLookup, lowering, start, held,
      nativeLower, edgeOk, back, resolved, reached⟩ :=
    frame.cursor.jump_reaches consuming nativeRange lookup frame.lookup blockLookup finished rfl mem context callers
  have length : entryBlock.params.length = fields.length := entryLength.trans arity.symm
  rcases consumed_take_edge tagged receipt frame.lookup blockLookup nativeLookup lowering start held nativeLower
      member entryBlockLookup edgeOk resolved sub (Cfg.Proof.sub_leaf source.env) frame.words arguments
      length (functionBounds_params bounds entryBlockLookup) reached with failure | success
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        {mem, ctx := context, stack := target :: callers} := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failure
    exact failure
  · obtain ⟨offset, charges, label, argumentWords, targetEnv, targetStart, labelLower, represented,
      binding, trace, actualBack, costBound, charged, entered, savedSub, registers, lexicalWords⟩ := success
    have frameArgs := Cfg.Proof.evalArgs_sub sub arguments
    obtain ⟨blockBody, _, actualBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
    have compatible := frame.compatible.args (edge_live actualBlock member) frameArgs
    obtain ⟨sourceStep, entryAt⟩ := checked_entry_at checked range sourceLookup bodyLookup
      lookup entryBlockLookup fields arity sourceCallers H
    have entryAt' := entryAt.extend (Cfg.Proof.Sub.bindAll (Cfg.Proof.sub_leaf source.env)
      (sourceFunction.params.map Prod.fst) fields)
    rw [entryParams] at entered registers savedSub lexicalWords
    let after : Cfg.Frame := {
      fn := source.fn
      blk := 0
      rest := entryBlock.body
      env := Own.bindAll source.env (sourceFunction.params.map Prod.fst) fields }
    let final : Lir.Frame := {fn := source.fn, label := offset, pos := 0, env := targetEnv}
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        {mem, ctx := context, stack := target :: callers} := by
      cases target
      simp_all [Lir.atState]
    rw [same] at trace
    refine .inl ⟨after, final, charges + (decide (offset ≤ label)).toNat, body, erased, ?_, rfl,
      trace, ?_⟩
    · refine ⟨Own.Plain.ownedState_entryFull_exact (Own.Plain.signatures F) H external _
          (borrows.getD source.fn []) (uniqs.getD source.fn ([], false)).1 fields logical den
          (by simpa using arity) fresh balance hbrw borrows uniqs
          (uniqs.getD source.fn ([], false)).2 F.ctors F.known priv
          huniq hprivB hprivE hprivArgs,
        typed, entryAt', ⟨frame.lookup, entered, registers,
          frame.bounded.bindAll _ (Own.Plain.dens_bounded den),
          frame.compatible.bindAll _ _ compatible⟩, sourceScope, rfl, ?_⟩
      intro consumedTarget foundTarget
      obtain ⟨entryBody, mapping, actualTarget⟩ :=
        (consumeFunction_parts receipt).2.2.2.2.2 entryBlockLookup
      rw [foundTarget] at actualTarget
      cases actualTarget
      intro init condition left right fused empty
      have originalEmpty : entryBlock.body = [] := empty
      have actualEmpty : entryBody = [] := by
        simpa only [originalEmpty, List.mapM_nil, pure, Except.pure, Except.ok.injEq] using mapping.symm
      obtain ⟨x, op, alts, default, nonempty, _⟩ := fusable_some fused
      simp [actualEmpty] at nonempty
    · exact costBound

end IxCC.Cfg.Rc.Native.Spec
