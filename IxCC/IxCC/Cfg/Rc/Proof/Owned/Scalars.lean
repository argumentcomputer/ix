import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarConsumed
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarRuntime
import IxCC.Cfg.Rc.Proof.CallStep
import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Scalars
import IxCC.Own.Plain.Proof.NonCall
import IxCC.Fir.Proof.Unfold

/-! # A field-less constructor and a primitive over the typing context (heap stage 2)

Both bind an immediate and change no heap. A primitive's arguments that its signature marks
become immediates as well (`primImmArgs`): their tokens were vacuous, so the roots stay
reference-count equal. The native step is the canonical layer's `frame_step`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **`x := C`**, a constructor without fields: an immediate. -/
theorem fieldless_result_owned (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} (ctor : Fir.CtorInfo) (args : List Fir.Arg) (zero : ctor.arity = 0)
    {k : Own.Plain.Code}
    (next : PhysicalCodeOwned F P config pairs main clock sourceJoins k) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.bind x (.ctor ctor args) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.ctor ctor args) (Own.Plain.eraseCode k)))
  rw [Fir.eval_bind_ctor]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.ctor ctor args) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    have scope : x ∉ live ∧ Own.Plain.rhsIn (Own.Plain.signatures F) live (.ctor ctor args) = true ∧
        Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
          (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseCode k) = true := by
      simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] using before.scope
    obtain ⟨fresh, rhsScope, bodyScope⟩ := scope
    have arity : args.length = ctor.arity := by
      simp only [Own.Plain.rhsIn, Bool.and_eq_true, decide_eq_true_eq] at rhsScope
      exact rhsScope.1.1.1.1
    have empty : args = [] := List.length_eq_zero_iff.mp (arity.trans zero)
    subst args
    have logicalEqual : Fir.Val.ctor ctor [] = logical := by
      simpa [Fir.evalRhs, Fir.evalArgs, zero] using evaluation
    subst logical
    obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
    have hΓ : Γ.setImm x = Γ' := by simpa [Own.Plain.bindCtx, zero] using hbind
    subst hΓ
    have state := before.owned.pre.bindImm fresh (Own.Proof.den_ctor0 H ctor)
      (by intro l h; cases h) before.owned.counts
    have fieldless : ctor.fieldless = true := by simp [Fir.CtorInfo.fieldless, zero]
    obtain ⟨tail, head, continuation⟩ := before.layout.bind_continuation
    have pureRhs : PureRhs (Own.immRhs (.ctor ctor [])) := fieldless
    have effect : Own.evalRhs .rc P.base.tables source.env H (Own.immRhs (.ctor ctor [])) =
        .ok (.ctor0 ctor, H) := by
      simp [Own.immRhs, Own.evalRhs, Own.evalArgs, zero, fieldless]
    obtain ⟨supply, real⟩ := checked_binding_bounds admission.scopedProgram admission.consuming
      sourceLookup before.frame.lookup before.layout pureRhs
    obtain ⟨pow, gcd⟩ := source_stage_scalar_runtime P pairs (Public.Spec.rawSource config P pairs) main
    rcases (frame_step pow gcd before.frame supply head pureRhs real effect before.running
        memory context callers).2 with scalar | failed
    · obtain ⟨charge, after, running, trace, frame, fused⟩ := scalar
      have activation : ActivationOwned F P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
          external (live ++ [x]) (Γ.setImm x) Δ (sourceEnv.insert x (.ctor ctor []))
          (ownedEnv.insert x (.ctor0 ctor)) roots lex sourceJoins ownedJoins k sourceFunction.vars
          function {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} after :=
        ⟨state, typed, continuation (.ctor0 ctor), frame, bodyScope, running, fused⟩
      exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
        (next H addresses external (live ++ [x]) (Γ.setImm x) Δ (sourceEnv.insert x (.ctor ctor []))
          (ownedEnv.insert x (.ctor0 ctor)) roots lex ownedJoins sourceFunction function
          {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} after memory context
          base bump limit regionBytes slots lists callers sourceLookup activation heap)
    · exact ResultAt.of_fails failed

/-- **`x := op args`**: the result is an immediate; the arguments the signature marks become
immediates (their tokens are vacuous). -/
theorem primitive_result_owned (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} (op : Lam.Prim) (args : List Fir.Arg) {k : Own.Plain.Code}
    (next : PhysicalCodeOwned F P config pairs main clock sourceJoins k) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.bind x (.prim op args) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.prim op args) (Own.Plain.eraseCode k)))
  rw [Fir.eval_bind_prim]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.prim op args) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    have scope : x ∉ live ∧ Own.Plain.rhsIn (Own.Plain.signatures F) live (.prim op args) = true ∧
        Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
          (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseCode k) = true := by
      simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] using before.scope
    obtain ⟨fresh, _, bodyScope⟩ := scope
    have pins := Own.Plain.checkBoolPins_sound
      (checkScopedProgram_ownedParts admission.scopedProgram).2.1
    obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
    obtain ⟨u, hneed, hΓ⟩ := Own.Plain.except_bind_ok hbind
    have hΓ := Own.Plain.except_pure_ok hΓ
    subst hΓ
    have havail := Own.Plain.Ctx.needArgs_avail hneed
    obtain ⟨values, logicalArgs, arguments, sourceArgs, denArgs⟩ :=
      Own.Plain.needArgs_sem before.owned.den havail
    have primitive : Fir.primResult F op logicalArgs = .ok logical := by
      simpa only [Fir.evalRhs, sourceArgs] using evaluation
    obtain ⟨value, result, den, immediate⟩ := Own.Plain.primResult_immediate pins denArgs primitive
    have argsImmediate := Own.Plain.primResult_args_immediate denArgs primitive
    obtain ⟨owned', pre', refs⟩ := before.owned.pre.immArgs (Own.Plain.primImmArgs op args.length)
      args (fun y hy => by
        refine ⟨havail y hy, ?_⟩
        obtain ⟨v, _, hv, _, _⟩ := before.owned.den y (havail y hy)
        exact ⟨v, hv, argsImmediate v (Own.Plain.evalArgs_mem arguments hy hv)⟩)
    have state := pre'.bindImm fresh den immediate (refs.balance before.owned.counts)
    have lexicalEffect : Own.evalRhs .rc ({ctors := F.ctors, known := F.known} : Own.Tables)
        ownedEnv H (.fir (.prim op args)) = .ok (value, H) := by
      simp [Own.evalRhs, arguments, result, Sem.Result.map]
    obtain ⟨tail, head, continuation⟩ := before.layout.bind_continuation
    have sub := before.lexical.1
    have fullEffect : Own.evalRhs .rc P.base.tables source.env H (.fir (.prim op args)) =
        .ok (value, H) := by
      rw [generate_tables (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2]
      exact Cfg.Proof.evalRhs_sub_ok sub lexicalEffect
    obtain ⟨supply, real⟩ := checked_binding_bounds admission.scopedProgram admission.consuming
      sourceLookup before.frame.lookup before.layout trivial
    obtain ⟨pow, gcd⟩ := source_stage_scalar_runtime P pairs (Public.Spec.rawSource config P pairs) main
    rcases (frame_step pow gcd before.frame supply head trivial real fullEffect before.running
        memory context callers).2 with scalar | failed
    · obtain ⟨charge, after, running, trace, frame, fused⟩ := scalar
      have activation : ActivationOwned F P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
          external (live ++ [x])
          ((Ctx.immArgs Γ (Own.Plain.primImmArgs op args.length) args).setImm x) Δ
          (sourceEnv.insert x logical) (ownedEnv.insert x value) owned' lex sourceJoins ownedJoins k
          sourceFunction.vars function {source with rest := tail, env := source.env.insert x value}
          after :=
        ⟨state, typed, continuation value, frame, bodyScope, running, fused⟩
      have heap' : HeapState P pairs H addresses memory external owned' context base bump limit
          regionBytes slots lists :=
        ⟨by rw [← holdRoots_sameRefs refs]; exact heap.ready, heap.ordered, heap.compatible,
          heap.extent⟩
      exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
        (next H addresses external (live ++ [x])
          ((Ctx.immArgs Γ (Own.Plain.primImmArgs op args.length) args).setImm x) Δ
          (sourceEnv.insert x logical) (ownedEnv.insert x value) owned' lex ownedJoins
          sourceFunction function {source with rest := tail, env := source.env.insert x value}
          after memory context base bump limit regionBytes slots lists callers sourceLookup
          activation heap')
    · exact ResultAt.of_fails failed

end

end IxCC.Cfg.Rc.Native.Spec
