import Compilatrix.Cfg.Rc.Proof.Entry
import Compilatrix.Cfg.Rc.Proof.Extend

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Cfg.Proof (Impl spine)

/-- Self-tail calls are the existing block-zero back edge, not an additional
runtime call. Extra target activation bindings are ignored by EnvSub. -/
theorem At.tail_self {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) {fr : Frame} {ρ : Own.Env}
    {saved : List Own.Plain.JEntry} {args : List Fir.Arg}
    (stateRel : At F P fr ρ saved (.tcall fr.fn args))
    {source : Fir.Fun} {body : Own.Plain.Code} (sourceLookup : F.fun? fr.fn = some source)
    (bodyLookup : bodies.get? fr.fn = some body) {vs : List Own.RVal}
    (values : Own.evalArgs ρ args = some vs) (arity : vs.length = source.params.length)
    (stk : List (Frame × Fir.Var)) (H : Own.Heap) :
    ∃ after, step P (.run fr stk H) = .next (.run after stk H) true ∧
      At F P after (Own.bindAll .leaf (source.params.map (·.1)) vs) [] body := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    env, below, scopedNames, joins⟩ := stateRel
  obtain ⟨actual, table, actualLookup, tableLookup, source', body', sourceLookup', bodyLookup',
    lowering, bounds, collected⟩ := checked_entry (checkScopedProgram_parts checked).1 range
  have hs : source' = source := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  have hc : body' = body := Option.some.inj (bodyLookup'.symm.trans bodyLookup)
  subst source'; subst body'
  have targetEq : actual = fd := Option.some.inj (actualLookup.symm.trans lookup)
  have fdEq : fd = lowerFunction F.size fr.fn source body := targetEq.symm.trans lowering
  rw [fdEq] at lookup layout
  let ownFd : Own.Fun := { Own.immFun source with
    body := skeleton F.size source.vars body
    vars := source.vars + actionCount body }
  obtain ⟨term, entryBlock⟩ := Cfg.Proof.block_zero fr.fn ownFd
  change (lowerFunction F.size fr.fn source body).block? 0 =
    some { params := ownFd.params.zip ownFd.sig.params, body := spine ownFd.body, term } at entryBlock
  have paramsEq : (ownFd.params.zip ownFd.sig.params).map (·.1) = ownFd.params :=
    Cfg.Proof.zip_fst (by simp [ownFd, Own.immFun])
  have length : vs.length = (ownFd.params.zip ownFd.sig.params).length := by
    simp [ownFd, Own.immFun, arity]
  obtain ⟨entry, entryStep, entryRel⟩ := checked_entry_step checked range sourceLookup bodyLookup vs arity stk H
  have entryShape : entry = {
      fn := fr.fn
      blk := 0
      rest := spine ownFd.body
      env := Own.bindAll .leaf (ownFd.params.zip ownFd.sig.params |>.map (·.1)) vs } := by
    simp only [step, Cfg.step, lookup, entryBlock, length, ↓reduceIte,
      Sem.Step.next.injEq, State.run.injEq, and_true] at entryStep
    exact entryStep.symm
  rw [entryShape] at entryRel
  let targetEnv := Own.bindAll fr.env (ownFd.params.zip ownFd.sig.params |>.map (·.1)) vs
  let after : Frame := {
    fr with
    blk := 0
    rest := spine ownFd.body
    env := targetEnv }
  refine ⟨after, ?_, ?_⟩
  · simp only [skeleton, Impl] at layout
    simp only [skeleton, spine] at cursor
    simp only [step, cursor]
    rw [Cfg.Proof.step_run_term cursor lookup layout]
    simp only [Cfg.Proof.termStep, Cfg.Proof.tcallTerm, ↓reduceIte]
    rw [Cfg.Proof.takeEdge_eq entryBlock (Cfg.Proof.evalArgs_sub env values) length]
  · exact entryRel.extend (Cfg.Proof.Sub.bindAll (Cfg.Proof.sub_leaf fr.env) _ _)


end Compilatrix.Cfg.Rc
