import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Native.ReturnActivation
import IxCC.Cfg.Rc.Proof.Native.TrapCursor
import IxCC.Fir.Proof.Unfold

/-! The terminals and a join declaration over the typing context. `ret a` returns the only root
(`Activation.return_value`); a `trap` ends the run with any tokens held (a trap ends the whole
process); a declaration takes zero native steps (`Activation.declare`). -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry} {borrows : Own.Plain.BorrowSigs}
  {uniqs : Own.Plain.UniqSigs}

/-- **`ret a`.** -/
theorem physical_return (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    (arg : Fir.Arg) :
    PhysicalCode F P config pairs main clock sourceJoins (.ret arg) borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  rcases before.return_value admission.scopedProgram admission.consuming admission.rawOk
      (Public.Spec.rawSource config P pairs) main sourceLookup heap callers with success | failure
  · obtain ⟨value, logical, word, _, sourceValue, den, balance, afterState, ret, represented,
      bounded, compatible, retNoPriv, uniqRet⟩ := success
    show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins (.ret arg))
      F.ctors retUniq priv
    simp only [Fir.eval_ret, sourceValue, Sem.Result.ofOption]
    let returned : Returned P pairs
        (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
        external context base limit regionBytes logical F.ctors retUniq priv := {
      heap := H
      addresses := addresses
      memory := memory
      bump := bump
      slots := slots
      lists := lists
      frame := target
      value := value
      word := word
      den := den
      balance := balance
      state := afterState
      terminator := ret
      represented := represented
      bounded := bounded
      compatible := compatible
      preserved := fun _ _ _ h => h
      reachable := Own.Plain.ReachablePreserved.refl H external
      history := ⟨Nat.le_refl _, fun _ _ => rfl⟩
      privPreserved := Own.Plain.PrivPreserved.refl before.owned.privNoEdge
      retNoPriv := retNoPriv
      uniqRet := uniqRet }
    exact .inl ⟨returned, 0, .refl _⟩
  · exact ResultAt.of_fails failure

/-- **`trap`**: the tokens held are not released (a trap ends the run). -/
theorem physical_trap (admission : CodeAdmission F bodies P config pairs functions borrows uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins .trap borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins .trap)
    F.ctors retUniq priv
  rw [Fir.eval_trap]
  obtain ⟨fd, scopeNames, params, acc, next, supply, lower, slotBase, lookup, range, layout, cursor,
    sub, below, loSlot, slotSub, names, vb, rc, saved⟩ := before.layout
  have finished : source.rest = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  let block : Cfg.Block := {params, body := acc.reverse, term := .trap}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  exact .inl ⟨0, _, .refl _, before.frame.cursor.trap admission.consuming nativeRange lookup
    blockLookup finished rfl before.running memory context callers⟩

end

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)}
  {main clock : Nat} {sourceJoins : List Fir.JEntry} {borrows : Own.Plain.BorrowSigs}
  {uniqs : Own.Plain.UniqSigs}

/-- **A join declaration.** -/
theorem physical_declare {j : Fir.JoinId} {params captured : List Fir.Var} {rec : Bool}
    {body cont : Own.Plain.Code}
    (next : ∀ sourceEnv : Fir.Env,
      PhysicalCode F P config pairs main clock
        ({id := j, charged := false, env := sourceEnv, params, body := Own.Plain.eraseCode body,
          isRec := rec} :: sourceJoins) cont borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins
      (.jp j params captured rec body cont) borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins
      (.jp j params rec (Own.Plain.eraseCode body) (Own.Plain.eraseCode cont)))
    F.ctors retUniq priv
  rw [Fir.eval_jp]
  exact next sourceEnv H addresses external retUniq priv rslots slotVals live Γ
    (Δ.insert j captured) sourceEnv ownedEnv roots ((j, live) :: lex) _ sourceFunction function
    source target memory context base bump limit regionBytes slots lists callers sourceLookup
    before.declare heap

end

end IxCC.Cfg.Rc.Native.Spec
