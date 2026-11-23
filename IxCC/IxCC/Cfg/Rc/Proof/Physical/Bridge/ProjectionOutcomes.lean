import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionActivation
import IxCC.Cfg.Rc.Proof.Physical.CallResume
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarConsumed
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarAdmission
import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarRuntime
import IxCC.Cfg.Rc.Proof.CallStep
import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Own.Plain.Proof.Owned.Binds
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.NonCall
import IxCC.Fir.Proof.Unfold

/-! A field-less constructor and a projection over the typing context. `x := C` binds an
immediate. `x := y.i` is the native load (or the `Nat` successor view) alone: the field is
**borrowed** (no token: the projected cell holds it, and a release ends the borrow), or an
immediate when `y` is one. The increment the canonical producer places right after a projection
is a separate `inc` (`physical_inc`'s borrowed case). -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry} {borrows : Own.Plain.BorrowSigs}
  {uniqs : Own.Plain.UniqSigs}

private theorem proj_asCtor_field_immUniq {ctors : List Lam.CtorInfo} {H : Own.Heap} {K : Lam.Known}
    {parent v : Own.RVal} {key : Key.CtorKey} {fields : List Own.RVal}
    (himm : Own.Plain.ImmVal parent) (hc : parent.asCtor K H = some (key, fields)) (hm : v ∈ fields) :
    Own.Plain.ImmUniq ctors v := by
  cases parent with
  | loc l => exact absurd rfl (himm l)
  | erased => simp [Own.RVal.asCtor] at hc
  | ctor0 c =>
    have he : c.key = key ∧ [] = fields := by simpa [Own.RVal.asCtor] using hc
    rw [← he.2] at hm; simp at hm
  | lit lit =>
    cases lit with
    | str _ => simp [Own.RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [Own.RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [Own.RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have : v = .lit (.nat n) := by simpa using hm
        subst this; exact ⟨(fun _ h => by cases h), trivial⟩

private theorem proj_asCtor_field_noPriv {H : Own.Heap} {K : Lam.Known} {priv : Nat → Prop}
    (he : ∀ l, priv l → Own.Rc.edgeCount H l = 0) {parent v : Own.RVal} {key : Key.CtorKey}
    {fields : List Own.RVal} (hc : parent.asCtor K H = some (key, fields)) (hm : v ∈ fields) :
    ∀ l, priv l → v ≠ .loc l := by
  intro l hl hEq; subst hEq
  cases parent with
  | loc k =>
    cases hk : H.cell? k with
    | none => simp [Own.RVal.asCtor, hk] at hc
    | some cell =>
      cases cell with
      | dead => simp [Own.RVal.asCtor, hk] at hc
      | live rc m b =>
        have hbf : b.fields = fields :=
          (Prod.mk.inj (Option.some.inj (by simpa [Own.RVal.asCtor, hk] using hc))).2
        rw [← hbf] at hm
        exact Own.Rc.fields_avoid (he l hl) hk hm
  | lit lit =>
    cases lit with
    | str _ => simp [Own.RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [Own.RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [Own.RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
  | ctor0 c =>
    have hbf : [] = fields := (Prod.mk.inj (Option.some.inj (by simpa [Own.RVal.asCtor] using hc))).2
    rw [← hbf] at hm; simp at hm
  | erased => simp [Own.RVal.asCtor] at hc

/-- **`x := C`**, a constructor without fields: an immediate. -/
theorem fieldless_result (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {x : Fir.Var} (ctor : Fir.CtorInfo) (args : List Fir.Arg) (zero : ctor.arity = 0)
    {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.ctor ctor args) k)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.ctor ctor args) (Own.Plain.eraseCode k)))
    F.ctors retUniq priv
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
    have hΓ : (if Own.Plain.ctor0Valid F.ctors ctor then Γ.setImmUniq x else Γ.setImm x) = Γ' := by
      simpa [Own.Plain.bindCtx, zero] using hbind
    subst hΓ
    have state : Own.Plain.OwnedState (Own.Plain.signatures F) H external (live ++ [x])
        (if Own.Plain.ctor0Valid F.ctors ctor then Γ.setImmUniq x else Γ.setImm x)
        (sourceEnv.insert x (.ctor ctor [])) (ownedEnv.insert x (.ctor0 ctor)) roots lex Δ
        sourceJoins ownedJoins borrows uniqs retUniq F.ctors F.known priv rslots slotVals := by
      cases hcv : Own.Plain.ctor0Valid F.ctors ctor with
      | true =>
        simp only [↓reduceIte]
        exact before.owned.pre.bindImmUniq fresh (Own.Proof.den_ctor0 H ctor)
          ⟨(fun _ h => by cases h), Own.Plain.ctor0Valid_ok hcv⟩ before.owned.counts
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact before.owned.pre.bindImm fresh (Own.Proof.den_ctor0 H ctor)
          (fun _ h => by cases h) before.owned.counts
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
      have activation : Activation F P pairs
          (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
          external (live ++ [x])
          (if Own.Plain.ctor0Valid F.ctors ctor then Γ.setImmUniq x else Γ.setImm x) Δ
          (sourceEnv.insert x (.ctor ctor []))
          (ownedEnv.insert x (.ctor0 ctor)) roots lex sourceJoins ownedJoins k
          (funcFirst bodies source.fn sourceFunction)
          function {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} after
          borrows uniqs retUniq priv rslots slotVals :=
        ⟨state, typed, continuation (.ctor0 ctor), frame, bodyScope, running, fused⟩
      exact ResultAt.prefix trace (Own.Plain.ReachablePreserved.refl H external)
        (Own.Plain.PrivPreserved.refl before.owned.privNoEdge)
        (HeapHistory.refl _ _) (by omega)
        (next H addresses external retUniq priv rslots slotVals (live ++ [x])
          (if Own.Plain.ctor0Valid F.ctors ctor then Γ.setImmUniq x else Γ.setImm x) Δ
          (sourceEnv.insert x (.ctor ctor []))
          (ownedEnv.insert x (.ctor0 ctor)) roots lex ownedJoins sourceFunction function
          {source with rest := tail, env := source.env.insert x (.ctor0 ctor)} after memory context
          base bump limit regionBytes slots lists callers sourceLookup activation heap)
    · exact ResultAt.of_fails failed

/-- **`x := y.i`**: borrowed, caller-backed borrowed (`pbrw`), or immediate. -/
theorem projection_result (admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    {x : Fir.Var} (y : Fir.Var) (key : Key.CtorKey) (i : Nat) {k : Own.Plain.Code}
    (next : PhysicalCode F P config pairs main clock sourceJoins k borrows bodies uniqs) :
    PhysicalCode F P config pairs main clock sourceJoins (.bind x (.proj y key i) k)
      borrows bodies uniqs := by
  intro H addresses external retUniq priv rslots slotVals live Γ Δ sourceEnv ownedEnv roots lex
    ownedJoins sourceFunction function source target memory context base bump limit regionBytes
    slots lists callers sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _
    (Fir.eval F clock sourceEnv sourceJoins (.bind x (.proj y key i) (Own.Plain.eraseCode k)))
    F.ctors retUniq priv
  rw [Fir.eval_bind_proj]
  rcases Own.Plain.fir_rhs_pure F sourceEnv (.proj y key i) with stuck | ⟨logical, evaluation⟩
  · rw [stuck]; trivial
  · rw [evaluation, Sem.Result.bind_ok]
    have scope : x ∉ live ∧ y ∈ live ∧
        Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
          (Own.Plain.stackArities sourceJoins) (Own.Plain.eraseCode k) = true := by
      simpa [Own.Plain.eraseCode, Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true,
        and_assoc] using before.scope
    obtain ⟨fresh, hyLive, bodyScope⟩ := scope
    have hyx : y ≠ x := fun h => fresh (h ▸ hyLive)
    obtain ⟨Γ', hbind, typed⟩ := Own.Plain.checkCode_bind before.typed
    obtain ⟨u, hneed, hΓ⟩ := Own.Plain.except_bind_ok hbind
    have hΓ := Own.Plain.except_pure_ok hΓ
    subst hΓ
    have available : Γ.avail y = true := Own.Plain.Ctx.need_avail hneed
    obtain ⟨vy, wy, hvy, hwy, hdy⟩ := before.owned.den y available
    have evF := evaluation
    simp only [Fir.evalRhs, hwy] at evF
    cases hcw : wy.asCtor F.known with
    | none => rw [hcw] at evF; cases evF
    | some p =>
      obtain ⟨key', ffields⟩ := p
      rw [hcw] at evF
      by_cases hk : key' = key
      · subst hk
        simp only [↓reduceIte] at evF
        have hi : ffields[i]? = some logical := Own.Plain.Result.ofOption_ok evF
        obtain ⟨vs, hview, hfields⟩ := (Own.Plain.Values.asCtor_den F.known hdy).1 key' ffields hcw
        obtain ⟨value, hget, den⟩ := hfields.get' hi
        have hm : value ∈ vs := List.mem_of_getElem? hget
        have sourceEffect : Own.evalRhs .rc ({ctors := F.ctors, known := F.known} : Own.Tables)
            ownedEnv H (.proj y key' i) = .ok (value, H) := by
          simp [Own.evalRhs, hvy, hview, hget, Sem.Result.ofOption, Sem.Result.map]
        have sub := before.lexical.1
        have fullEffect : Own.evalRhs .rc P.base.tables source.env H (.proj y key' i) = .ok (value, H) := by
          rw [generate_tables (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2]
          exact Cfg.Proof.evalRhs_sub_ok sub sourceEffect
        obtain ⟨tail, head, continuation⟩ := before.layout.bind_continuation
        have real := checked_bind_real admission.scopedProgram before.layout sourceLookup (by rfl) (by rfl)
        have hxlive : x ∈ live ++ [x] := List.mem_append_right _ (List.mem_singleton_self _)
        have hylive' : y ∈ live ++ [x] := List.mem_append_left _ hyLive
        have hvy' : (ownedEnv.insert x value).get? y = some vy := by
          rw [Src.NatMap.get?_insert_ne _ _ hyx]; exact hvy
        have hvx' : (ownedEnv.insert x value).get? x = some value := Src.NatMap.get?_insert_self ..
        let Γnext : Ctx :=
          (if Γ.isImm y then Γ.setImmUniq x else if Γ.isPbrw y then Γ.setPbrw x else Γ.setBorrow x).setProj x y key' i
        have state : Own.Plain.OwnedState (Own.Plain.signatures F) H external (live ++ [x]) Γnext
            (sourceEnv.insert x logical) (ownedEnv.insert x value) roots lex Δ sourceJoins ownedJoins
            borrows uniqs retUniq F.ctors F.known priv rslots slotVals := by
          dsimp only [Γnext]
          cases immediateY : Γ.isImm y with
          | true =>
            simp only [↓reduceIte]
            obtain ⟨parent, parentLookup, parentImmediate⟩ := before.owned.immOk y immediateY
            have : parent = vy := Option.some.inj (parentLookup.symm.trans hvy); subst this
            exact (before.owned.pre.bindImmUniq fresh den
              (proj_asCtor_field_immUniq parentImmediate hview hm) before.owned.counts).setProj
              hxlive hylive' hvy' hview hget hvx'
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases pbrwY : Γ.isPbrw y with
            | true =>
              simp only [↓reduceIte]
              obtain ⟨parent, parentLookup, hreach⟩ := before.owned.pbrwOk y pbrwY
              have : parent = vy := Option.some.inj (parentLookup.symm.trans hvy); subst this
              exact (before.owned.pre.bindPbrw fresh den (hreach.asCtor_field hview hm)
                before.owned.counts (proj_asCtor_field_noPriv before.owned.privNoEdge hview hm)).setProj
                hxlive hylive' hvy' hview hget hvx'
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact (before.owned.pre.bindBorrow fresh den
                (Own.Plain.BorrowVal.asCtor_field hview hm) before.owned.counts).setProj
                hxlive hylive' hvy' hview hget hvx'
        rcases projection_frame before.frame heap.ready.idle.live heap.compatible heap.ordered head real
            fullEffect before.running context callers with projected | failed
        · obtain ⟨after, running, trace, frame, fused⟩ := projected
          have activation : Activation F P pairs
              (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
              external (live ++ [x]) Γnext Δ
              (sourceEnv.insert x logical) (ownedEnv.insert x value) roots lex sourceJoins ownedJoins k
              (funcFirst bodies source.fn sourceFunction) function
              {source with rest := tail, env := source.env.insert x value}
              after borrows uniqs retUniq priv rslots slotVals :=
            ⟨state, typed, continuation value, frame, bodyScope, running, fused⟩
          exact ResultAt.prefix trace (Own.Plain.ReachablePreserved.refl H external)
            (Own.Plain.PrivPreserved.refl before.owned.privNoEdge)
            (HeapHistory.refl _ _) (by omega)
            (next H addresses external retUniq priv rslots slotVals (live ++ [x]) Γnext
              Δ (sourceEnv.insert x logical) (ownedEnv.insert x value) roots lex ownedJoins
              sourceFunction function {source with rest := tail, env := source.env.insert x value}
              after memory context base bump limit regionBytes slots lists callers sourceLookup
              activation heap)
        · exact ResultAt.of_fails failed
      · simp only [hk, ↓reduceIte] at evF; cases evF

end

end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
