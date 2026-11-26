import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Physical.CaseEntry
import IxCC.Cfg.Rc.Proof.Physical.CaseSelection
import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Values
import IxCC.Fir.Proof.Unfold

/-! A `case` over the typing context: every branch was checked from the same context (Own has no
merge point), so the selected branch starts from the scrutinising activation's state unchanged. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-- The source branch selected from the erased alternatives is the erasure of the Own branch
selected from the alternatives, which the checker accepted (with `Γ.setCtor x key` on a tagged
arm or `Γ` on the default arm). -/
theorem ownCase_erase (x : Fir.Var) (key : Key.CtorKey) {Δ : JCtx} {Γ : Ctx}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {known : Lam.Known} :
    ∀ (alts : List Own.Plain.Alt) (d : Option Own.Plain.Code),
    Own.Plain.checkAlts Δ Γ x alts borrows uniqs retUniq ctors known = .ok () →
    Own.Plain.checkOpt Δ Γ d borrows uniqs retUniq ctors known = .ok () →
    ∀ fbody, firCase key (Own.Plain.eraseAlts alts) (Own.Plain.eraseOpt d) = some fbody →
    ∃ body Γb, ownCase key alts d = some body ∧ Own.Plain.eraseCode body = fbody ∧
      checkCode Δ Γb body borrows uniqs retUniq ctors known = .ok () ∧
      (Γb = Γ ∨ Γb = Γ.setCtor x key)
  | [], none, _, _, fbody, h => by simp [Own.Plain.eraseAlts, Own.Plain.eraseOpt, firCase] at h
  | [], some c, _, ho, fbody, h => by
    simp only [Own.Plain.eraseAlts, Own.Plain.eraseOpt, firCase, Option.some.injEq] at h
    exact ⟨c, Γ, rfl, h, by simpa [Own.Plain.checkOpt] using ho, Or.inl rfl⟩
  | .mk tag b :: rest, d, ha, ho, fbody, h => by
    obtain ⟨tb, tr⟩ := Own.Plain.checkAlts_cons ha
    simp only [Own.Plain.eraseAlts, firCase] at h
    by_cases ht : tag = key
    · subst ht
      simp only [↓reduceIte, Option.some.injEq] at h
      exact ⟨b, Γ.setCtor x tag, by simp [ownCase], h, tb, Or.inr rfl⟩
    · simp only [ht, ↓reduceIte] at h
      obtain ⟨body, Γb, chosen, erased, typed, hΓb⟩ := ownCase_erase x key rest d tr ho fbody h
      exact ⟨body, Γb, by simp [ownCase, ht, chosen], erased, typed, hΓb⟩

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry} {borrows : Own.Plain.BorrowSigs}
  {uniqs : Own.Plain.UniqSigs}

/-- **A `case`.** -/
theorem case_result (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {x : Fir.Var} {alts : List Own.Plain.Alt} {dflt : Option Own.Plain.Code}
    (next : ∀ body : Own.Plain.Code,
      (Own.Plain.eraseCode body).size < (Own.Plain.eraseCode (.case x alts dflt)).size →
      PhysicalCode F P config pairs main clock sourceJoins body borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.case x alts dflt)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins
    (.case x (Own.Plain.eraseAlts alts) (Own.Plain.eraseOpt dflt))) F.ctors retUniq priv
  rw [Fir.eval_case]
  obtain ⟨hneed, typedAlts, typedOpt⟩ := Own.Plain.checkCode_case before.typed
  cases lookup : sourceEnv.get? x with
  | none => simp only [Sem.Result.ofOption, Sem.Result.bind]; trivial
  | some logical =>
    simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
    cases constructor : logical.asCtor F.known with
    | none => trivial
    | some pair =>
      obtain ⟨key, fields⟩ := pair
      simp only []
      rw [firCase_eval]
      cases selected : firCase key (Own.Plain.eraseAlts alts) (Own.Plain.eraseOpt dflt) with
      | none => trivial
      | some fbody =>
        simp only []
        obtain ⟨body, Γb, chosen, erased, typed, hΓb⟩ :=
          ownCase_erase x key alts dflt typedAlts typedOpt fbody selected
        have havail := Own.Plain.Ctx.need_avail hneed
        obtain ⟨value, actualLogical, ownedLookup, logicalLookup, den⟩ := before.owned.den x havail
        have equal : actualLogical = logical := Option.some.inj (logicalLookup.symm.trans lookup)
        subst actualLogical
        obtain ⟨ownFields, ownCtor, _⟩ :=
          (Own.Plain.Values.asCtor_den F.known den).1 key fields constructor
        have known : (tablesOf P pairs).known = F.known :=
          congrArg Own.Tables.known
            (generate_tables (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2)
        have ctor : value.asCtor (tablesOf P pairs).known H = some (key, ownFields) := by
          rw [known]; exact ownCtor
        obtain ⟨fd, _, _, _, _, _, _, _, fdLookup, range, _⟩ := before.layout
        have programSize : P.base.size = F.size :=
          generate_size (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
        have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
        obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ :=
          consumed_entry admission.consuming nativeRange
        have originalEqual : original = fd := Option.some.inj (originalLookup.symm.trans fdLookup)
        subst original
        have actualEqual : actual = function :=
          Option.some.inj (actualLookup.symm.trans before.frame.lookup)
        subst actual
        have real := checked_consumed_sup admission.scopedProgram range sourceLookup fdLookup receipt
        rcases case_entry admission.consuming admission.switches admission.rawOk before.layout chosen before.frame
            nativeRange real before.fused ownedLookup ctor heap.ready.idle.live heap.compatible
            before.running context callers with success | failure
        · obtain ⟨after, final, cost, layout, frame, trace, running, sameFn, fused⟩ := success
          have caseScope : Own.Plain.scopeOk (Own.Plain.signatures F) live
              (Own.Plain.stackArities sourceJoins)
              (.case x (Own.Plain.eraseAlts alts) (Own.Plain.eraseOpt dflt)) = true := before.scope
          have parts : x ∈ live ∧ Own.Plain.scopeAlts (Own.Plain.signatures F) live
              (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseAlts alts) = true ∧
              Own.Plain.scopeOpt (Own.Plain.signatures F) live (Own.Plain.stackArities sourceJoins)
                (Own.Plain.eraseOpt dflt) = true := by
            simpa [Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] using caseScope
          have ownedB : Own.Plain.OwnedState (Own.Plain.signatures F) H external live Γb sourceEnv
              ownedEnv roots lex Δ sourceJoins ownedJoins borrows uniqs retUniq F.ctors F.known
              priv rslots slotVals := by
            rcases hΓb with rfl | rfl
            · exact before.owned
            · exact before.owned.setCtor parts.1 ownedLookup ownCtor
          have activation : Activation F P pairs
              (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
              external live Γb Δ sourceEnv ownedEnv roots lex sourceJoins ownedJoins body
              (funcFirst bodies after.fn sourceFunction) function after final
              borrows uniqs retUniq priv rslots slotVals :=
            ⟨ownedB, typed, layout, by simpa only [sameFn] using frame,
              by rw [erased]; exact firCase_scope parts.2.1 parts.2.2 selected, running, fused⟩
          have smaller : (Own.Plain.eraseCode body).size <
              (Own.Plain.eraseCode (.case x alts dflt)).size := by
            have size := firCase_size selected
            rw [erased]
            simp only [Own.Plain.eraseCode, Fir.Code.size]
            omega
          rw [← erased]
          exact ResultAt.prefix trace (Own.Plain.ReachablePreserved.refl H external)
            (Own.Plain.PrivPreserved.refl before.owned.privNoEdge)
            (HeapHistory.refl _ _) (by omega)
            (next body smaller H addresses external retUniq priv rslots slotVals live Γb Δ
              sourceEnv ownedEnv roots lex ownedJoins
              sourceFunction function after final memory context base bump limit regionBytes slots
              lists callers (by simpa only [sameFn] using sourceLookup) activation heap)
        · exact ResultAt.of_fails failure

end

end IxCC.Cfg.Rc.Native.Spec
