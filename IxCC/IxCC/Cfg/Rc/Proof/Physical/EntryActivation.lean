import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Own.Plain.Proof.Admission
import IxCC.Own.Plain.Proof.Owned.Simulation

/-! Function entry over the typing context: a called function starts from its parameters, each
holding one token (`Ctx.entry`), with the body the map holds for it, which the checker accepted
from that context and which erases to the source body. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs IxCC.Rt.Proof
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-- The body the map holds for a numbered function, checked from its parameters with its
borrow and uniqueness masks. -/
theorem checked_owned_body {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true) {f : Nat} {source : Fir.Fun}
    (sourceLookup : F.fun? f = some source) :
    ∃ body, f < F.size ∧ bodies.get? f = some body ∧ Own.Plain.eraseCode body = source.body ∧
      checkCode .leaf
        (Ctx.entryWith (source.params.map Prod.fst) (borrows.getD f []) (uniqs.getD f ([], false)).1)
        body borrows uniqs (uniqs.getD f ([], false)).2 F.ctors F.known = .ok () ∧
      Own.Plain.fresh [] (source.params.map Prod.fst) = true ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (source.params.map Prod.fst)
        (Own.Plain.stackArities []) (Own.Plain.eraseCode body) = true := by
  have range := checked_source_dense checked sourceLookup
  obtain ⟨domain, _, checkedBodies, _⟩ := checkScopedProgram_ownedParts checked
  obtain ⟨body, bodyLookup, erased, typed⟩ := checkedBodies f source range sourceLookup
  obtain ⟨_, fresh, scope⟩ := Own.Plain.programDomain_function domain range sourceLookup
  refine ⟨body, range, bodyLookup, erased, typed, fresh, ?_⟩
  rw [erased]
  exact scope

/-- Actual checked entry constructs the complete source/native activation over the typing
context, including `@borrowed`, `@unique`, and `priv` isolation invariants. All register-name
bounds, the body, its scope and the entry layout come from admission; the arguments' denotation,
counts, reachability, uniqueness, and words are the caller's concrete state. -/
theorem entry_activation {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (checked : checkScopedProgram F bodies P borrows uniqs = true)
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {f : Nat} {source : Fir.Fun} (sourceLookup : F.fun? f = some source)
    {H : Own.Heap} {external : Nat → Nat} {addresses : AddressMap}
    {priv : Nat → Prop}
    {values : List Own.RVal} {logical : List Fir.Val} {words : List Lir.Word}
    (den : Sem.Forall2 (Own.Proof.Den H) values logical)
    (balance : Own.Rc.Balance H external (Own.Plain.selectOwnedVals (borrows.getD f []) values))
    (hbrw : ∀ v, v ∈ Own.Plain.selectBorrowedVals (borrows.getD f []) values →
      Own.Plain.ReachableFrom H external v)
    (huniq : ∀ v, v ∈ Own.Plain.selectUniqueVals (borrows.getD f []) (uniqs.getD f ([], false)).1 values →
      Own.Plain.UniqVal F.ctors H external (Own.Plain.selectOwnedVals (borrows.getD f []) values) v)
    (hprivB : ∀ l, priv l → l < H.size)
    (hprivE : ∀ l, priv l → Own.Rc.edgeCount H l = 0)
    (hprivArgs : ∀ l, priv l → ∀ v, v ∈ values → v ≠ .loc l)
    (represented : SlotsRel addresses ((tablesOf P pairs).rawParams f 0) values words)
    (compatible : ∀ value ∈ values, ValueCtorOk (tablesOf P pairs) value)
    (arity : values.length = source.params.length)
    (sourceCallers : List (Cfg.Frame × Fir.Var)) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    let params := source.params.map Prod.fst
    let bs := borrows.getD f []
    let us := (uniqs.getD f ([], false)).1
    let retU := (uniqs.getD f ([], false)).2
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
      Activation F P pairs lp H addresses external params (Ctx.entryWith params bs us) .leaf
        (Fir.bindAll .leaf params logical) (Own.bindAll .leaf params values)
        (Own.Plain.selectOwnedVals bs values) [] [] []
        body (funcFirst bodies f source) consumedFd
        {fn := f, blk := 0, rest := block.body, env := Own.bindAll .leaf params values}
        {fn := f, label := offset, pos := 0, env := targetEnv}
        borrows uniqs retU priv .leaf [] := by
  dsimp only
  obtain ⟨body, range, bodyLookup, erased, typed, fresh, scope⟩ :=
    checked_owned_body checked sourceLookup
  have generation := (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have rangeP : f < P.base.size := by rw [generate_size generation]; exact range
  obtain ⟨fd, block, lookup, blockLookup, params, length, _, bounds⟩ :=
    checked_entry_block checked range sourceLookup bodyLookup
  have real := functionBounds_params bounds blockLookup
  rw [rawParams_consumed consuming rangeP lookup blockLookup] at represented
  obtain ⟨consumedFd, callee, targetEnv, offset, consumedLookup, entered, trace, cursor, registers,
    raws⟩ :=
    consumed_entry_words consuming lowered main rangeP lookup blockLookup represented
      (length.trans arity.symm) real mem context callers
  rw [params] at cursor registers raws
  obtain ⟨sourceStep, atEntry⟩ := checked_entry_at checked range sourceLookup bodyLookup
    lookup blockLookup values arity sourceCallers H
  refine ⟨fd, block, consumedFd, callee, targetEnv, offset, body, lookup, blockLookup, erased,
    entered, trace, sourceStep, ?_⟩
  refine ⟨Own.Plain.ownedState_entryFull_exact (Own.Plain.signatures F) H external _
      (borrows.getD f []) (uniqs.getD f ([], false)).1 values logical den (by simpa using arity)
      fresh balance hbrw borrows uniqs (uniqs.getD f ([], false)).2 F.ctors F.known priv
      huniq hprivB hprivE hprivArgs,
    typed, atEntry, ⟨consumedLookup, cursor, registers, raws,
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


end IxCC.Cfg.Rc.Native.Spec
