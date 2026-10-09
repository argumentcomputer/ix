import Compilatrix.Cfg.Rc.Proof.Physical.Admission
import Compilatrix.Cfg.Rc.Proof.Native.Activation
import Compilatrix.Own.Plain.Proof.Admission

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs

/-- Actual checked entry constructs the complete source/native activation.
All register-name bounds, canonical code, scope, and entry layout come from
admission. Argument denotation/counts/words are the caller's concrete state. -/
theorem entry_activation {config : Rt.Config} {F : Fir.Program}
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
    ∃ fd block consumedFd callee targetEnv offset,
      P.base.fun? f = some fd ∧ fd.blocks[0]? = some block ∧
      Lir.enter lp f words = some callee ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := callee :: callers} 0
        (Lir.atState mem context f offset 0 targetEnv callers) ∧
      step P (.call f values sourceCallers H) =
        .next (.run {
          fn := f
          blk := 0
          rest := block.body
          env := Own.bindAll .leaf params values } sourceCallers H) true ∧
      Activation F P pairs lp H addresses external params (Fir.bindAll .leaf params logical)
        (Own.bindAll .leaf params values) values [] [] [] source.body source.vars consumedFd
        {fn := f, blk := 0, rest := block.body, env := Own.bindAll .leaf params values}
        {fn := f, label := offset, pos := 0, env := targetEnv} := by
  dsimp only
  have range := checked_source_dense checked sourceLookup
  have generation := (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have rangeP : f < P.base.size := by rw [generate_size generation]; exact range
  have plain := (checkProgram_parts (checkScopedProgram_parts checked).1).1
  obtain ⟨domain, _, canonical⟩ := Own.Plain.checkPlainMap_parts plain
  have bodyMap : bodies = (Own.Plain.Program.canonical F).bodies :=
    congrArg Own.Plain.Program.bodies canonical
  have bodyLookup : bodies.get? f =
      some (Own.Plain.lowerCode (source.params.map Prod.fst) [] source.body) := by
    rw [bodyMap]
    exact Own.Plain.canonical_body_of sourceLookup
  obtain ⟨_, fresh, scope⟩ := Own.Plain.programDomain_function domain range sourceLookup
  obtain ⟨fd, block, lookup, blockLookup, params, length, _, bounds⟩ :=
    checked_entry_block checked range sourceLookup bodyLookup
  have real := functionBounds_params bounds blockLookup
  obtain ⟨consumedFd, callee, targetEnv, offset, consumedLookup, entered, trace, cursor, registers⟩ :=
    consumed_entry_words consuming lowered main rangeP lookup blockLookup represented
      (length.trans arity.symm) real mem context callers
  rw [params] at cursor registers
  obtain ⟨sourceStep, atEntry⟩ := checked_entry_at checked range sourceLookup bodyLookup
    lookup blockLookup values arity sourceCallers H
  refine ⟨fd, block, consumedFd, callee, targetEnv, offset, lookup, blockLookup,
    entered, trace, sourceStep, ?_⟩
  refine ⟨Own.Plain.state_entry (Own.Plain.signatures F) H external _ values logical den
      (by simpa using arity) fresh balance,
    atEntry, ⟨consumedLookup, cursor, registers,
      (Own.Plain.envBounded_empty H.size).bindAll _ (Own.Plain.dens_bounded den),
      FusedCtorOk.empty.bindAll _ _ compatible⟩,
    scope, rfl, ?_⟩
  intro actualBlock actualBlockLookup
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming rangeP
  have sameOriginal : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst original
  have sameActual : actual = consumedFd := Option.some.inj (actualLookup.symm.trans consumedLookup)
  subst actual
  obtain ⟨body, bodyRun, entryBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  have sameBlock : actualBlock = {block with body} :=
    Option.some.inj (actualBlockLookup.symm.trans entryBlock)
  subst actualBlock
  intro init condition left right fused empty
  have emptyBody : block.body = [] := empty
  rw [emptyBody] at bodyRun
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at bodyRun
  have bodyNil : body = [] := bodyRun.symm
  obtain ⟨x, op, alts, default, actualBody, _⟩ := Rt.Proof.fusable_some fused
  simp only [bodyNil, List.length_append, List.length_cons, List.length_nil] at actualBody
  have lengths := congrArg List.length actualBody
  simp at lengths


end Compilatrix.Cfg.Rc.Native.Spec
