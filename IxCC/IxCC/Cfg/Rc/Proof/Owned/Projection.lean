import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionActivation
import IxCC.Cfg.Rc.Proof.Native.Outcome
import IxCC.Own.Plain.Proof.Owned.Binds
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Own.Plain.Proof.NonCall
import IxCC.Fir.Proof.Unfold

/-! # A projection over the typing context (heap stage 2)

`x := y.i` alone: the native load (or the `Nat` successor view) and nothing else. The field is
**borrowed** (no token: the projected cell holds it, and a release ends the borrow), or an
immediate when `y` is one. The increment the canonical producer places right after a projection
is now a separate `inc` (`physical_inc`'s borrowed case). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **`x := y.i`**: borrowed, or immediate. -/
theorem projection_result_owned (admission : CodeAdmission F bodies P config pairs functions)
    {x : Fir.Var} (y : Fir.Var) (key : Key.CtorKey) (i : Nat) {k : Own.Plain.Code}
    (next : PhysicalCodeOwned F P config pairs main clock sourceJoins k) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.bind x (.proj y key i) k) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.proj y key i) (Own.Plain.eraseCode k)))
  rw [Fir.eval_bind_proj]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.proj y key i) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    have scope : x ∉ live ∧ y ∈ live ∧
        Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
          (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseCode k) = true := by
      simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true,
        and_assoc] using before.scope
    obtain ⟨fresh, _, bodyScope⟩ := scope
    obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
    obtain ⟨u, hneed, hΓ⟩ := Own.Plain.except_bind_ok hbind
    have hΓ := Own.Plain.except_pure_ok hΓ
    subst hΓ
    have available : Γ.avail y = true := Own.Plain.Ctx.need_avail hneed
    have denY : Own.Plain.EnvDen H [y] sourceEnv ownedEnv := by
      intro z member
      simp only [List.mem_singleton] at member
      subst member
      exact before.owned.den z available
    obtain ⟨value, sourceEffect, den, permission, immediateOf⟩ :=
      source_projection denY before.owned.counts (List.mem_singleton_self y) evaluation
    have sub := before.lexical.1
    have fullEffect : Own.evalRhs .rc P.base.tables source.env H (.proj y key i) = .ok (value, H) := by
      rw [generate_tables (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2]
      exact Cfg.Proof.evalRhs_sub_ok sub sourceEffect
    obtain ⟨tail, head, continuation⟩ := before.layout.bind_continuation
    have real := checked_bind_real admission.scopedProgram before.layout sourceLookup (by rfl)
    have state : Own.Plain.OwnedState (Own.Plain.signatures F) H external (live ++ [x])
        (if Γ.isImm y then Γ.setImm x else Γ.setBorrow x) (sourceEnv.insert x logical)
        (ownedEnv.insert x value) roots lex Δ sourceJoins ownedJoins := by
      cases immediateY : Γ.isImm y with
      | true =>
        simp only [↓reduceIte]
        obtain ⟨parent, parentLookup, parentImmediate⟩ := before.owned.immOk y immediateY
        have immEnv : Own.Plain.ImmEnv ownedEnv [y] := by
          intro z member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨parent, parentLookup, parentImmediate⟩
        exact before.owned.pre.bindImm fresh den (immediateOf immEnv (by simp))
          before.owned.counts
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact before.owned.pre.bindBorrow fresh den permission before.owned.counts
    rcases projection_frame before.frame heap.ready.idle.live heap.compatible heap.ordered head real
        fullEffect before.running context callers with projected | failed
    · obtain ⟨after, running, trace, frame, fused⟩ := projected
      have activation : ActivationOwned F P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
          external (live ++ [x]) (if Γ.isImm y then Γ.setImm x else Γ.setBorrow x) Δ
          (sourceEnv.insert x logical) (ownedEnv.insert x value) roots lex sourceJoins ownedJoins k
          sourceFunction.vars function {source with rest := tail, env := source.env.insert x value}
          after :=
        ⟨state, typed, continuation value, frame, bodyScope, running, fused⟩
      exact ResultAt.prefix trace (fun _ _ _ den => den) (HeapHistory.refl _ _) (by omega)
        (next H addresses external (live ++ [x]) (if Γ.isImm y then Γ.setImm x else Γ.setBorrow x)
          Δ (sourceEnv.insert x logical) (ownedEnv.insert x value) roots lex ownedJoins
          sourceFunction function {source with rest := tail, env := source.env.insert x value}
          after memory context base bump limit regionBytes slots lists callers sourceLookup
          activation heap)
    · exact ResultAt.of_fails failed

end

end IxCC.Cfg.Rc.Native.Spec
