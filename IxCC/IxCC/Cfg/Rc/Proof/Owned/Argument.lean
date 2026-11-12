import IxCC.Cfg.Rc.Proof.Owned.Activation
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarConsumed
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarRuntime
import IxCC.Cfg.Rc.Proof.CallStep
import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.NonCall
import IxCC.Fir.Proof.Unfold

/-! # An argument binding over the typing context (heap stage 2)

`x := a` moves `a`'s token to `x` (or binds an immediate): no heap change, no action prefix; the
native step is the canonical layer's `frame_step`. The template for the other bindings. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **`x := a`.** -/
theorem argument_result_owned (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} (arg : Fir.Arg) {k : Own.Plain.Code}
    (next : PhysicalCodeOwned F P config pairs main clock sourceJoins k) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.bind x (.arg arg) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.arg arg) (Own.Plain.eraseCode k)))
  rw [Fir.eval_bind_arg]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.arg arg) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    have scope : x ∉ live ∧ Own.Plain.argIn live arg = true ∧
        Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
          (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseCode k) = true := by
      have s := before.scope
      simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true,
        and_assoc] using s
    obtain ⟨fresh, _, bodyScope⟩ := scope
    obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
    have sourceArg : arg.eval sourceEnv = some logical :=
      Own.Plain.Result.ofOption_ok (by simpa only [Fir.evalRhs] using evaluation)
    obtain ⟨value, owned', lexicalArg, state, refs⟩ :=
      Own.Plain.arg_step_refs before.owned fresh hbind sourceArg
    have sub := before.lexical.1
    have fullArg : Own.evalArg source.env arg = some value := Cfg.Proof.evalArg_sub sub lexicalArg
    obtain ⟨tail, head, continuation⟩ := before.layout.bind_continuation
    obtain ⟨supply, real⟩ := checked_binding_bounds admission.scopedProgram admission.consuming
      sourceLookup before.frame.lookup before.layout trivial
    obtain ⟨pow, gcd⟩ := source_stage_scalar_runtime P pairs (Public.Spec.rawSource config P pairs) main
    have effect : Own.evalRhs .rc P.base.tables source.env H (.fir (.arg arg)) = .ok (value, H) := by
      simp [Own.evalRhs, fullArg]
    rcases (frame_step pow gcd before.frame supply head trivial real effect before.running
        memory context callers).2 with scalar | failed
    · obtain ⟨charge, after, running, trace, frame, fused⟩ := scalar
      have activation : ActivationOwned F P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
          external (live ++ [x]) Γ' Δ (sourceEnv.insert x logical) (ownedEnv.insert x value) owned'
          lex sourceJoins ownedJoins k sourceFunction.vars function
          {source with rest := tail, env := source.env.insert x value} after :=
        ⟨state, typed, continuation value, frame, bodyScope, running, fused⟩
      have heap' : HeapState P pairs H addresses memory external owned' context base bump limit
          regionBytes slots lists :=
        ⟨by rw [holdRoots_sameRefs refs]; exact heap.ready, heap.ordered, heap.compatible,
          heap.extent⟩
      exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
        (next H addresses external (live ++ [x]) Γ' Δ (sourceEnv.insert x logical)
          (ownedEnv.insert x value) owned' lex ownedJoins sourceFunction function
          {source with rest := tail, env := source.env.insert x value} after memory context base
          bump limit regionBytes slots lists callers sourceLookup activation heap')
    · exact ResultAt.of_fails failed

end

end IxCC.Cfg.Rc.Native.Spec
