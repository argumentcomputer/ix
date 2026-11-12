import IxCC.Cfg.Rc.Proof.Owned.Activation
import IxCC.Own.Plain.Proof.Owned.Joins
import IxCC.Fir.Proof.Unfold

/-! # Join declaration over the typing context (heap stage 2)

Zero native steps: the saved entry is the Own body the checker typed from `Γ.enter`, and the join
context maps the join to its captured list. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx JCtx checkCode)

theorem ActivationOwned.declare {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live : List Fir.Var} {Γ : Ctx} {Δ : JCtx} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {roots : List Own.RVal} {lex : Own.Plain.Joins} {sourceJoins : List Fir.JEntry}
    {ownedJoins : List Own.Plain.JEntry} {j : Fir.JoinId} {params captured : List Fir.Var}
    {rec : Bool} {body cont : Own.Plain.Code} {bound : Nat}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : ActivationOwned F P pairs lp H addresses external live Γ Δ sourceEnv ownedEnv roots
      lex sourceJoins ownedJoins (.jp j params captured rec body cont) bound function source target) :
    ActivationOwned F P pairs lp H addresses external live Γ (Δ.insert j captured) sourceEnv
      ownedEnv roots ((j, live) :: lex)
      ({id := j, charged := false, env := sourceEnv, params, body := Own.Plain.eraseCode body,
        isRec := rec} :: sourceJoins)
      ({id := j, charged := false, env := ownedEnv, params, body, isRec := rec} :: ownedJoins)
      cont bound function source target := by
  obtain ⟨hnd, hneed, htyped, hcont⟩ := Own.Plain.checkCode_jp before.typed
  have scopeFacts := before.scope
  simp only [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at scopeFacts
  obtain ⟨hnone, fresh, bodyScope, contScope⟩ := scopeFacts
  refine ⟨before.owned.declare hnd hneed htyped hnone fresh bodyScope, hcont, before.layout.join,
    before.frame, ?_, before.running, before.fused⟩
  simpa only [Own.Plain.stackArities, List.map_cons] using contScope

section
variable {F : Fir.Program} {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **A join declaration.** -/
theorem physical_declare_owned {j : Fir.JoinId} {params captured : List Fir.Var} {rec : Bool}
    {body cont : Own.Plain.Code}
    (next : ∀ sourceEnv : Fir.Env,
      PhysicalCodeOwned F P config pairs main clock
        ({id := j, charged := false, env := sourceEnv, params, body := Own.Plain.eraseCode body,
          isRec := rec} :: sourceJoins) cont) :
    PhysicalCodeOwned F P config pairs main clock sourceJoins (.jp j params captured rec body cont) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins
      (.jp j params rec (Own.Plain.eraseCode body) (Own.Plain.eraseCode cont)))
  rw [Fir.eval_jp]
  exact next sourceEnv H addresses external live Γ (Δ.insert j captured) sourceEnv ownedEnv roots
    ((j, live) :: lex) _ sourceFunction function source target memory context base bump limit
    regionBytes slots lists callers sourceLookup before.declare heap

end

end IxCC.Cfg.Rc.Native.Spec
