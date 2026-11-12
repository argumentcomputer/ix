import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Cfg.Rc.Proof.Physical.Jump
import IxCC.Cfg.Rc.Proof.Extend
import IxCC.Own.Plain.Proof.Admission
import IxCC.Own.Plain.Proof.Owned.Simulation

/-! # Function entry over the typing context (heap stage 2)

A called function starts from its parameters, each holding one token (`Ctx.entry`), with the
body the map holds for it, which the checker accepted from that context and which erases to the
source body. Two ways in: a call or tail call to another function (`entry_activation_owned`)
and a function's tail call to itself, which re-enters block zero by a back edge
(`self_entry_activation_owned`). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Rt.Proof
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-- The body the map holds for a numbered function, checked from its parameters. -/
theorem checked_owned_body {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) {f : Nat} {source : Fir.Fun}
    (sourceLookup : F.fun? f = some source) :
    ∃ body, f < F.size ∧ bodies.get? f = some body ∧ Own.Plain.eraseCode body = source.body ∧
      checkCode .leaf (Ctx.entry (source.params.map Prod.fst)) body = .ok () ∧
      Own.Plain.fresh [] (source.params.map Prod.fst) = true ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (source.params.map Prod.fst)
        (Own.Plain.stackArities []) (Own.Plain.eraseCode body) = true := by
  have range := checked_source_dense checked sourceLookup
  obtain ⟨domain, _, checkedBodies⟩ := checkScopedProgram_ownedParts checked
  obtain ⟨body, bodyLookup, erased, typed⟩ := checkedBodies f source range sourceLookup
  obtain ⟨_, fresh, scope⟩ := Own.Plain.programDomain_function domain range sourceLookup
  refine ⟨body, range, bodyLookup, erased, typed, fresh, ?_⟩
  rw [erased]
  exact scope

/-- Actual checked entry constructs the complete source/native activation over the typing
context. All register-name bounds, the body, its scope and the entry layout come from admission;
the arguments' denotation, counts and words are the caller's concrete state. -/
theorem entry_activation_owned {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {f : Nat} {source : Fir.Fun} (sourceLookup : F.fun? f = some source)
    {H : Own.Heap} {external : Nat → Nat} {addresses : AddressMap}
    {values : List Own.RVal} {logical : List Fir.Val} {words : List Lir.Word}
    (den : Sem.Forall2 (Own.Proof.Den H) values logical)
    (balance : Own.Rc.Balance H external values)
    (represented : Rt.Proof.ListRel (fun value word => valueWord addresses value = some word) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = source.params.length)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    let params := source.params.map Prod.fst
    ∃ fd block consumedFd callee targetEnv offset body,
      P.base.fun? f = some fd ∧ fd.blocks[0]? = some block ∧
      Own.Plain.eraseCode body = source.body ∧
      Lir.enter lp f words = some callee ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := callee :: callers} 0
        (Lir.atState mem context f offset 0 targetEnv callers) ∧
      step P (.call f values sourceCallers H) =
        .next (.run {
          fn := f
          blk := 0
          rest := block.body
          env := Own.bindAll .leaf params values } sourceCallers H) true ∧
      ActivationOwned F P pairs lp H addresses external params (Ctx.entry params) .leaf
        (Fir.bindAll .leaf params logical) (Own.bindAll .leaf params values) values [] [] []
        body source.vars consumedFd
        {fn := f, blk := 0, rest := block.body, env := Own.bindAll .leaf params values}
        {fn := f, label := offset, pos := 0, env := targetEnv} := by
  dsimp only
  obtain ⟨body, range, bodyLookup, erased, typed, fresh, scope⟩ :=
    checked_owned_body checked sourceLookup
  have generation := (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have rangeP : f < P.base.size := by rw [generate_size generation]; exact range
  obtain ⟨fd, block, lookup, blockLookup, params, length, _, bounds⟩ :=
    checked_entry_block checked range sourceLookup bodyLookup
  have real := functionBounds_params bounds blockLookup
  obtain ⟨consumedFd, callee, targetEnv, offset, consumedLookup, entered, trace, cursor, registers⟩ :=
    consumed_entry_words consuming lowered main rangeP lookup blockLookup represented
      (length.trans arity.symm) real mem context callers
  rw [params] at cursor registers
  obtain ⟨sourceStep, atEntry⟩ := checked_entry_at checked range sourceLookup bodyLookup
    lookup blockLookup values arity sourceCallers H
  refine ⟨fd, block, consumedFd, callee, targetEnv, offset, body, lookup, blockLookup, erased,
    entered, trace, sourceStep, ?_⟩
  refine ⟨Own.Plain.ownedState_entry_exact (Own.Plain.signatures F) H external _ values logical den
      (by simpa using arity) fresh balance,
    typed, atEntry, ⟨consumedLookup, cursor, registers,
      (Own.Plain.envBounded_empty H.size).bindAll _ (Own.Plain.dens_bounded den),
      FusedCtorOk.empty.bindAll _ _ compatible⟩,
    scope, rfl, ?_⟩
  intro actualBlock actualBlockLookup
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming rangeP
  have sameOriginal : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst original
  have sameActual : actual = consumedFd := Option.some.inj (actualLookup.symm.trans consumedLookup)
  subst actual
  obtain ⟨body', bodyRun, entryBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  have sameBlock : actualBlock = {block with body := body'} :=
    Option.some.inj (actualBlockLookup.symm.trans entryBlock)
  subst actualBlock
  intro init condition left right fused empty
  have emptyBody : block.body = [] := empty
  rw [emptyBody] at bodyRun
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at bodyRun
  have bodyNil : body' = [] := bodyRun.symm
  obtain ⟨x, op, alts, default, actualBody, _⟩ := Rt.Proof.fusable_some fused
  simp only [bodyNil, List.length_append, List.length_cons, List.length_nil] at actualBody
  have lengths := congrArg List.length actualBody
  simp at lengths

/-- The self-tail back edge re-enters block zero with the function's parameters, over the typing
context. The Cfg map is the frame's; the callee starts with exactly its parameters' tokens. -/
theorem self_entry_activation_owned {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs) {lp : Lir.Program}
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat}
    {source : Cfg.Frame} {target : Lir.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {args : List Fir.Arg} {sourceFunction : Fir.Fun} {function : Cfg.Fun}
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    (sourceState : At F P source ρ saved (.tcall source.fn args))
    (frame : FrameState P pairs lp addresses H.size sourceFunction.vars function source target)
    {fields : List RVal} {logical : List Fir.Val}
    (arguments : Own.evalArgs ρ args = some fields)
    (den : Sem.Forall2 (Own.Proof.Den H) fields logical)
    (balance : Balance H external fields) (arity : fields.length = sourceFunction.params.length)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (callers : List Lir.Frame) :
    (∃ after final cost body,
      Own.Plain.eraseCode body = sourceFunction.body ∧
      ActivationOwned F P pairs lp H addresses external (sourceFunction.params.map Prod.fst)
        (Ctx.entry (sourceFunction.params.map Prod.fst)) .leaf
        (Fir.bindAll .leaf (sourceFunction.params.map Prod.fst) logical)
        (Own.bindAll .leaf (sourceFunction.params.map Prod.fst) fields) fields [] [] []
        body sourceFunction.vars function after final ∧
      after.fn = source.fn ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} cost
        {mem, ctx := context, stack := final :: callers} ∧ 1 ≤ cost) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨fd, scopeNames, params, acc, next, supply, low, lookup, range, layout, cursor,
    sub, below, names, joins⟩ := sourceState
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
  rcases consumed_take_edge receipt frame.lookup blockLookup nativeLookup lowering start held nativeLower
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
    · refine ⟨Own.Plain.ownedState_entry_exact (Own.Plain.signatures F) H external _ fields logical
          den (by simpa using arity) fresh balance,
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
