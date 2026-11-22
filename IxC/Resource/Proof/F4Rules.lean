import IxC.Resource.Proof.F4Inv
import IxC.Resource.Proof.Ops

/-!
# Soundness of Non-Recursive Checker Rules (`F4Rules`)

Bridges `IxC.Resource.Check`'s non-recursive abstract helpers (`valid`, `readVar`,
`isUniq`, `notOnceSrc`, `killSrc`, `flowTo`, `bindInner`, `retCheck`, `anCtor`,
`anProj`, `caseField`, `papVal`, `callResult`, `applyValue`, `APrimArgs`, `ACaps`)
and `IxC.Resource.Proof.Ops` operational specs (`conform_spec_full`, `bindAt_spec`,
`ret_spec`, `prim_spec`, `construct_spec`, `makePap_spec`, `formClosure_spec`,
`bindParamsM_spec`, `strValue_ok`, `readOut_ok`) to the `F4Inv` logical relation
(`StOk`, `FunOkAt`, `CtorFieldsOk`, `VSim`, `Sim`, `ValEnvDisj`).
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. `CM` / `Runs` Unpacking Algebra -/

theorem CM_get_run (s : CSt) : ((get : CM CSt).run s) = .ok (s, s) := rfl

theorem CM_set_run (s' s : CSt) : ((set s' : CM Unit).run s) = .ok ((), s') := rfl

theorem CM_modify_run (f : CSt → CSt) (s : CSt) : ((modify f : CM Unit).run s) = .ok ((), f s) := rfl

theorem CM_refuseM_run {α : Type} (w : String) (s : CSt) :
    ((refuseM w : CM α).run s) = .error (.refuse w) := rfl

theorem AState.toCSt_inj {σ₁ σ₂ : AState} {k₁ k₂ : Nat} (h : σ₁.toCSt k₁ = σ₂.toCSt k₂) :
    σ₁ = σ₂ := by
  have := congrArg AState.ofCSt h
  simpa using this

theorem Runs_ok_eq {α : Type} {a b : α} {σ₁ σ₂ : AState}
    (h : (Except.ok (a, σ₁.toCSt 0) : Except Halt (α × CSt)) = .ok (b, σ₂.toCSt 0)) :
    a = b ∧ σ₁ = σ₂ := by
  have hp := Except.ok.inj h
  exact ⟨congrArg Prod.fst hp, AState.toCSt_inj (congrArg Prod.snd hp)⟩

theorem Runs_pure_iff {α : Type} {σ σ' : AState} {a b : α} :
    Runs (pure a) σ b σ' ↔ b = a ∧ σ' = σ := by
  unfold Runs
  rw [CM_pure_run]
  constructor
  · intro h; obtain ⟨h1, h2⟩ := Runs_ok_eq h; exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem Runs_bind {α β : Type} {m : CM α} {f : α → CM β} {σ σ'' : AState} {b : β}
    (hm : StepIndep m) (h : Runs (m >>= f) σ b σ'') :
    ∃ a σ', Runs m σ a σ' ∧ Runs (f a) σ' b σ'' := by
  unfold Runs at h ⊢
  rw [CM_bind_run] at h
  cases hm1 : m.run (σ.toCSt 0) with
  | error e => rw [hm1] at h; cases h
  | ok p =>
    rcases p with ⟨a, s1⟩
    rw [hm1] at h
    have hpSteps : s1.steps = 0 := ((hm σ 0 0).1 a s1 hm1).1
    have hpEq : (AState.ofCSt s1).toCSt 0 = s1 := by
      rw [← hpSteps]; exact AState.toCSt_ofCSt s1
    refine ⟨a, AState.ofCSt s1, ?_, ?_⟩
    · rw [hpEq]
    · rw [hpEq]; exact h

theorem Runs_stOf {σ σ' : AState} {id : Nat} {b : BSt}
    (h : Runs (stOf id) σ b σ') :
    b = σ.st[id]?.getD .dead ∧ σ' = σ := by
  unfold Runs stOf at h
  rw [CM_bind_run, CM_get_run] at h
  obtain ⟨h1, h2⟩ := Runs_ok_eq h
  exact ⟨h1.symm, h2.symm⟩

theorem Runs_isOnceBnd {σ σ' : AState} {id : Nat} {b : Bool}
    (h : Runs (isOnceBnd id) σ b σ') :
    b = σ.once[id]?.getD false ∧ σ' = σ := by
  unfold Runs isOnceBnd at h
  rw [CM_bind_run, CM_get_run] at h
  obtain ⟨h1, h2⟩ := Runs_ok_eq h
  exact ⟨h1.symm, h2.symm⟩

theorem Runs_isSpent {σ σ' : AState} {id : Nat} {b : Bool}
    (h : Runs (isSpent id) σ b σ') :
    b = σ.spent[id]?.getD false ∧ σ' = σ := by
  unfold Runs isSpent at h
  rw [CM_bind_run, CM_get_run] at h
  obtain ⟨h1, h2⟩ := Runs_ok_eq h
  exact ⟨h1.symm, h2.symm⟩

theorem Runs_innermost {σ σ' : AState} {r : Nat}
    (h : Runs innermost σ r σ') :
    r = σ.regions.headD 1 ∧ σ' = σ := by
  unfold Runs innermost at h
  rw [CM_bind_run, CM_get_run] at h
  obtain ⟨h1, h2⟩ := Runs_ok_eq h
  exact ⟨h1.symm, h2.symm⟩

theorem Runs_setSt {σ σ' : AState} {id : Nat} {b : BSt}
    (h : Runs (setSt id b) σ () σ') :
    σ' = { σ with st := σ.st.set! id b } := by
  unfold Runs setSt at h
  rw [CM_modify_run] at h
  exact (Runs_ok_eq (σ₁ := { σ with st := σ.st.set! id b }) h).2.symm

theorem Runs_markSpent {σ σ' : AState} {id : Nat}
    (h : Runs (markSpent id) σ () σ') :
    σ' = { σ with spent := σ.spent.set! id true } := by
  unfold Runs markSpent at h
  rw [CM_modify_run] at h
  exact (Runs_ok_eq (σ₁ := { σ with spent := σ.spent.set! id true }) h).2.symm

theorem Runs_openReg {σ σ' : AState} {s : Nat}
    (h : Runs openReg σ s σ') :
    s = σ.openReg.1 ∧ σ' = σ.openReg.2 := by
  unfold Runs openReg at h
  rw [CM_bind_run, CM_get_run] at h
  dsimp only at h
  rw [CM_bind_run, CM_set_run] at h
  dsimp only at h
  rw [CM_pure_run] at h
  obtain ⟨h1, h2⟩ := Runs_ok_eq (σ₁ := σ.openReg.2) h
  exact ⟨h1.symm, h2.symm⟩

theorem Runs_closeReg {σ σ' : AState} {s : Nat}
    (h : Runs (closeReg s) σ () σ') :
    σ' = σ.closeReg s := by
  unfold Runs closeReg at h
  rw [CM_modify_run] at h
  exact (Runs_ok_eq (σ₁ := σ.closeReg s) h).2.symm

theorem Runs_newBnd {σ σ' : AState} {v : AVal} {isOnce : Bool} {id : Nat}
    (h : Runs (newBnd v isOnce) σ id σ') :
    id = (σ.pushBnd v isOnce).1 ∧ σ' = (σ.pushBnd v isOnce).2 := by
  unfold Runs newBnd at h
  rw [CM_bind_run, CM_get_run] at h
  dsimp only at h
  rw [CM_bind_run, CM_set_run] at h
  dsimp only at h
  rw [CM_pure_run] at h
  obtain ⟨h1, h2⟩ := Runs_ok_eq (σ₁ := (σ.pushBnd v isOnce).2) h
  exact ⟨h1.symm, h2.symm⟩

theorem AStateOk_setSt {σ : AState} (hok : AStateOk σ) {id : Nat} {b : BSt}
    (hmon : match σ.st[id]? with | some b0 => BSt.le b0 b | none => True) :
    AStateOk { σ with st := σ.st.set! id b } ∧ AStateLe σ { σ with st := σ.st.set! id b } := by
  have hsz : (σ.st.set! id b).size = σ.st.size := by simp [Array.set!_eq_setIfInBounds]
  refine ⟨⟨by rw [hsz]; exact hok.1, by rw [hsz]; exact hok.2.1, hok.2.2⟩,
    ⟨by dsimp only; omega, Nat.le_refl _, fun i hi => ?_, fun _ _ => rfl, fun _ _ h => h⟩⟩
  by_cases heq : i = id
  · subst heq
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
    simp only [hi, ↓reduceIte]
    cases h0 : σ.st[i]? with
    | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
    | some b0 => rw [h0] at hmon; exact hmon
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm heq)]
    cases h0 : σ.st[i]? with
    | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
    | some b0 => exact BSt.le_refl b0

theorem AStateOk_markSpent {σ : AState} (hok : AStateOk σ) (id : Nat) :
    AStateOk { σ with spent := σ.spent.set! id true } ∧
    AStateLe σ { σ with spent := σ.spent.set! id true } := by
  have hsz : (σ.spent.set! id true).size = σ.spent.size := by simp [Array.set!_eq_setIfInBounds]
  refine ⟨⟨hok.1, by rw [hsz]; exact hok.2.1, hok.2.2⟩,
    ⟨Nat.le_refl _, Nat.le_refl _, fun i hi => ?_, fun _ _ => rfl, fun i hi h => ?_⟩⟩
  · cases h0 : σ.st[i]? with
    | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
    | some b0 => exact BSt.le_refl b0
  · by_cases heq : i = id
    · subst heq
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
      simp only [hi, ↓reduceIte]
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm heq)]
      exact h

theorem getD_eq_of_getElem? {α : Type} {a : Array α} {i : Nat} {x d : α}
    (h : a[i]? = some x) : a.getD i d = x := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  simp [Array.getD, hlt]

theorem getElem?_eq_some_of_getD_ne {α : Type} {a : Array α} {i : Nat} {d : α}
    (h : a.getD i d ≠ d) : ∃ x, a[i]? = some x ∧ x ≠ d := by
  by_cases hlt : i < a.size
  · simp [Array.getD, hlt] at h
    exact ⟨a[i], Array.getElem?_eq_getElem hlt, h⟩
  · simp [Array.getD, hlt] at h

theorem CM_stOf_run (d : Nat) (s : CSt) : (stOf d).run s = .ok (s.st[d]?.getD .dead, s) := rfl

theorem CM_isOnceBnd_run (d : Nat) (s : CSt) : (isOnceBnd d).run s = .ok (s.once[d]?.getD false, s) := rfl

theorem CM_isSpent_run (d : Nat) (s : CSt) : (isSpent d).run s = .ok (s.spent[d]?.getD false, s) := rfl

/-- Generic unpacking lemma for a read-only `for x in xs do` validation loop in `CM`. -/
theorem CM_forIn_unit_check {α : Type} {f : α → PUnit → CM (ForInStep PUnit)} {P : α → CSt → Prop}
    (hstep : ∀ x s,
      (∀ s', (f x PUnit.unit).run s = .ok (.yield PUnit.unit, s') → s' = s ∧ P x s) ∧
      (∀ s', (f x PUnit.unit).run s ≠ .ok (.done PUnit.unit, s')))
    (xs : List α) (s s' : CSt)
    (hr : (forIn xs PUnit.unit f).run s = .ok (PUnit.unit, s')) :
    (∀ x ∈ xs, P x s) ∧ s' = s := by
  induction xs with
  | nil =>
    simp only [List.forIn_nil] at hr
    rw [CM_pure_run] at hr
    cases hr
    exact ⟨fun _ hm => (by cases hm), rfl⟩
  | cons x rest ih =>
    simp only [List.forIn_cons] at hr
    rw [CM_bind_run] at hr
    cases hfx : (f x PUnit.unit).run s with
    | error e => rw [hfx] at hr; cases hr
    | ok p =>
      rcases p with ⟨step, s1⟩
      rw [hfx] at hr
      cases step with
      | done b =>
        cases b
        exact absurd hfx ((hstep x s).2 s1)
      | yield b =>
        cases b
        obtain ⟨rfl, hPx⟩ := (hstep x s).1 s1 hfx
        obtain ⟨hrest, hsEq⟩ := ih hr
        refine ⟨fun y hy => ?_, hsEq⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hPx
        · exact hrest y hy'

theorem Runs_valid {σ σ' : AState} {v : AVal} {w : String}
    (h : Runs (valid v w) σ () σ') :
    ValidDeps σ v.deps ∧ σ' = σ := by
  unfold Runs valid at h
  rw [CM_bind_run] at h
  cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) (σ.toCSt 0) with
  | error e => rw [hl] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, s1⟩
    rw [hl] at h
    dsimp only at h
    rw [CM_pure_run] at h
    have hp := Except.ok.inj h
    have hstEq : s1 = σ'.toCSt 0 := congrArg Prod.snd hp
    have hdd : (BSt.dead == BSt.dead) = true := rfl
    have hld : (BSt.live == BSt.dead) = false := rfl
    have hsd : (BSt.shared == BSt.dead) = false := rfl
    obtain ⟨hall, hsEq⟩ := CM_forIn_unit_check (P := fun d s => d < s.st.size ∧ s.st[d]? ≠ some .dead)
      (fun d s => by
        constructor
        · intro s' hrun
          rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
          cases hget : s.st[d]? with
          | none =>
            simp only [hget, Option.getD_none, hdd, ↓reduceIte] at hrun
            rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
          | some b =>
            cases b with
            | dead =>
              simp only [hget, Option.getD_some, hdd, ↓reduceIte] at hrun
              rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
            | live =>
              simp only [hget, Option.getD_some, hld, Bool.false_eq_true, ↓reduceIte] at hrun
              rw [CM_pure_run] at hrun; cases hrun
              exact ⟨rfl, (Array.getElem?_eq_some_iff.mp hget).1, by decide⟩
            | shared =>
              simp only [hget, Option.getD_some, hsd, Bool.false_eq_true, ↓reduceIte] at hrun
              rw [CM_pure_run] at hrun; cases hrun
              exact ⟨rfl, (Array.getElem?_eq_some_iff.mp hget).1, by decide⟩
        · intro s' hrun
          rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
          cases hget : s.st[d]? with
          | none =>
            simp only [hget, Option.getD_none, hdd, ↓reduceIte] at hrun
            rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
          | some b =>
            cases b with
            | dead =>
              simp only [hget, Option.getD_some, hdd, ↓reduceIte] at hrun
              rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
            | live =>
              simp only [hget, Option.getD_some, hld, Bool.false_eq_true, ↓reduceIte] at hrun
              rw [CM_pure_run] at hrun; cases hrun
            | shared =>
              simp only [hget, Option.getD_some, hsd, Bool.false_eq_true, ↓reduceIte] at hrun
              rw [CM_pure_run] at hrun; cases hrun)
      v.deps (σ.toCSt 0) s1 hl
    exact ⟨hall, AState.toCSt_inj (hstEq.symm.trans hsEq)⟩

theorem Runs_readVar {env : List ABnd} {i : Nat} {σ σ' : AState} {v : AVal}
    (h : Runs (readVar env i) σ v σ') :
    ∃ ab, env[i]? = some ab ∧ ab.mode ≠ .erased ∧
      v = effVal ab ∧ ValidDeps σ (effVal ab).deps ∧ σ' = σ := by
  unfold Runs readVar at h
  cases hlu : env[i]? with
  | none =>
    simp only [hlu] at h
    rw [CM_refuseM_run] at h; cases h
  | some ab =>
    simp only [hlu] at h
    cases her : (ab.mode == .erased) with
    | true =>
      simp only [her, ↓reduceIte] at h
      rw [CM_bind_run, CM_refuseM_run] at h; cases h
    | false =>
      simp only [her, Bool.false_eq_true, ↓reduceIte] at h
      rw [CM_bind_run] at h
      have hvdef : ({ ab.val with deps := ab.id :: ab.val.deps.filter (· != ab.id), src := some ab.id } : AVal) = effVal ab := rfl
      rw [hvdef] at h
      cases hv : (valid (effVal ab) "a binding is read").run (σ.toCSt 0) with
      | error e => rw [hv] at h; cases h
      | ok p =>
        rw [hv] at h
        dsimp only at h
        rw [CM_pure_run] at h
        have hp := Except.ok.inj h
        have hvEq : v = effVal ab := (congrArg Prod.fst hp).symm
        have hstEq : p.2 = σ'.toCSt 0 := congrArg Prod.snd hp
        have hvalid : Runs (valid (effVal ab) "a binding is read") σ () σ' := by
          unfold Runs; rw [← hstEq]; exact hv
        obtain ⟨hvd, hst⟩ := Runs_valid hvalid
        exact ⟨ab, rfl, by simpa using her, hvEq, hvd, hst⟩

/-- Generic unpacking lemma for an early-return `Option Bool × Unit` `forIn` check in `CM`. -/
theorem CM_forIn_optBool_check {α : Type}
    {f : α → Option Bool × Unit → CM (ForInStep (Option Bool × Unit))}
    {P : α → CSt → Prop}
    (hstep : ∀ x s,
      (∀ s', (f x (none, ())).run s = .ok (.yield (none, ()), s') → s' = s ∧ P x s) ∧
      (∀ s', (f x (none, ())).run s = .ok (.done (some false, ()), s') → s' = s ∧ ¬ P x s) ∧
      (∀ res s', (f x (none, ())).run s = .ok (res, s') →
        res = .yield (none, ()) ∨ res = .done (some false, ())))
    (xs : List α) (s s' : CSt) (r : Option Bool × Unit)
    (hr : (forIn xs (none, ()) f).run s = .ok (r, s')) :
    s' = s ∧ ((r.1 = none ∧ ∀ x ∈ xs, P x s) ∨ (r.1 = some false ∧ ∃ x ∈ xs, ¬ P x s)) := by
  induction xs with
  | nil =>
    simp only [List.forIn_nil] at hr
    rw [CM_pure_run] at hr; cases hr
    exact ⟨rfl, Or.inl ⟨rfl, fun _ hm => (by cases hm)⟩⟩
  | cons x rest ih =>
    simp only [List.forIn_cons] at hr
    rw [CM_bind_run] at hr
    cases hfx : (f x (none, ())).run s with
    | error e => rw [hfx] at hr; cases hr
    | ok p =>
      rcases p with ⟨step, s1⟩
      rw [hfx] at hr
      rcases (hstep x s).2.2 step s1 hfx with rfl | rfl
      · obtain ⟨rfl, hPx⟩ := (hstep x s).1 s1 hfx
        obtain ⟨hsEq, hdisj⟩ := ih hr
        refine ⟨hsEq, ?_⟩
        rcases hdisj with ⟨hr1, hall⟩ | ⟨hr1, y, hy, hnot⟩
        · left
          refine ⟨hr1, fun z hz => ?_⟩
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hPx
          · exact hall z hz'
        · exact Or.inr ⟨hr1, y, List.mem_cons_of_mem _ hy, hnot⟩
      · obtain ⟨rfl, hnotPx⟩ := (hstep x s).2.1 s1 hfx
        dsimp only at hr
        rw [CM_pure_run] at hr; cases hr
        exact ⟨rfl, Or.inr ⟨rfl, x, List.mem_cons_self .., hnotPx⟩⟩

theorem Runs_isUniq {σ σ' : AState} {v : AVal} {res : Bool}
    (h : Runs (isUniq v) σ res σ') :
    σ' = σ ∧ (res = true ↔ v.cls ≠ .val ∨ (v.own = .uniq ∧ ∀ d ∈ v.deps, σ.st[d]? = some .live)) := by
  unfold Runs isUniq at h
  cases hcls : (v.cls != .val) with
  | true =>
    simp only [hcls, ↓reduceIte] at h
    rw [CM_pure_run] at h
    obtain ⟨h1, h2⟩ := Runs_ok_eq h
    have hne : v.cls ≠ .val := fun heq => by rw [heq] at hcls; cases hcls
    exact ⟨h2.symm, ⟨fun _ => Or.inl hne, fun _ => h1.symm⟩⟩
  | false =>
    simp only [hcls, Bool.false_eq_true, ↓reduceIte] at h
    have hclsVal : v.cls = .val := by
      cases hc : v.cls <;> try rfl
      all_goals (rw [hc] at hcls; cases hcls)
    cases hown : (v.own != .uniq) with
    | true =>
      simp only [hown, ↓reduceIte] at h
      rw [CM_pure_run] at h
      obtain ⟨h1, h2⟩ := Runs_ok_eq h
      refine ⟨h2.symm, ⟨fun ht => (by rw [← h1] at ht; cases ht), fun hdisj => ?_⟩⟩
      rcases hdisj with hne | ⟨ho, _⟩
      · exact absurd hclsVal hne
      · rw [ho] at hown; cases hown
    | false =>
      simp only [hown, Bool.false_eq_true, ↓reduceIte] at h
      have hownEq : v.own = .uniq := by
        cases ho : v.own <;> try rfl
        rw [ho] at hown; cases hown
      rw [CM_bind_run] at h
      cases hl : StateT.run (forIn (m := CM) v.deps ((none : Option Bool), ()) _) (σ.toCSt 0) with
      | error e => rw [hl] at h; cases h
      | ok p =>
        rcases p with ⟨r0, s1⟩
        rw [hl] at h
        have hdl : (BSt.dead == BSt.live) = false := rfl
        have hsl : (BSt.shared == BSt.live) = false := rfl
        have hll : (BSt.live == BSt.live) = true := rfl
        obtain ⟨hsEq, hdisj⟩ := CM_forIn_optBool_check (P := fun d s => s.st[d]? = some .live)
          (fun d s => by
            refine ⟨?_, ?_, ?_⟩
            · intro s' hrun
              rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
              cases hget : s.st[d]? with
              | none =>
                simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hrun
                rw [CM_pure_run] at hrun; cases hrun
              | some b =>
                cases b with
                | shared =>
                  simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun
                | dead =>
                  simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun
                | live =>
                  simp only [hget, Option.getD_some, hll, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun
                  exact ⟨rfl, rfl⟩
            · intro s' hrun
              rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
              cases hget : s.st[d]? with
              | none =>
                simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hrun
                rw [CM_pure_run] at hrun; cases hrun
                exact ⟨rfl, by simp⟩
              | some b =>
                cases b with
                | shared =>
                  simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun
                  exact ⟨rfl, by decide⟩
                | dead =>
                  simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun
                  exact ⟨rfl, by decide⟩
                | live =>
                  simp only [hget, Option.getD_some, hll, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun
            · intro r1 s' hrun
              rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
              cases hget : s.st[d]? with
              | none =>
                simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hrun
                rw [CM_pure_run] at hrun; cases hrun; exact Or.inr rfl
              | some b =>
                cases b with
                | shared =>
                  simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun; exact Or.inr rfl
                | dead =>
                  simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun; exact Or.inr rfl
                | live =>
                  simp only [hget, Option.getD_some, hll, ↓reduceIte] at hrun
                  rw [CM_pure_run] at hrun; cases hrun; exact Or.inl rfl)
          v.deps (σ.toCSt 0) s1 r0 hl
        rcases hdisj with ⟨hp1, hall⟩ | ⟨hp1, x, hx, hnot⟩
        · dsimp only at h
          rw [hp1, hsEq] at h
          dsimp only at h
          rw [CM_pure_run] at h
          obtain ⟨h1, h2⟩ := Runs_ok_eq h
          exact ⟨h2.symm, ⟨fun _ => Or.inr ⟨hownEq, hall⟩, fun _ => h1.symm⟩⟩
        · dsimp only at h
          rw [hp1, hsEq] at h
          dsimp only at h
          rw [CM_pure_run] at h
          obtain ⟨h1, h2⟩ := Runs_ok_eq h
          refine ⟨h2.symm, ⟨fun ht => (by rw [← h1] at ht; cases ht), fun hd => ?_⟩⟩
          rcases hd with hne | ⟨_, hall⟩
          · exact absurd hclsVal hne
          · exact absurd (hall x hx) hnot

theorem Runs_notOnceSrc {σ σ' : AState} {v : AVal} {w : String}
    (h : Runs (notOnceSrc v w) σ () σ') :
    ¬ IsOnceSrc σ v ∧ σ' = σ := by
  unfold Runs notOnceSrc at h
  cases hsrc : v.src with
  | none =>
    simp only [hsrc] at h
    rw [CM_pure_run] at h
    exact ⟨(by rintro ⟨_, hs, _⟩; rw [hsrc] at hs; cases hs), (Runs_ok_eq h).2.symm⟩
  | some x =>
    simp only [hsrc] at h
    rw [CM_bind_run, CM_isOnceBnd_run] at h
    dsimp only at h
    cases ho : σ.once[x]? with
    | none =>
      simp only [AState.toCSt, ho, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at h
      rw [CM_pure_run] at h
      refine ⟨?_, (Runs_ok_eq h).2.symm⟩
      rintro ⟨id, hs, honce⟩
      rw [hsrc] at hs; cases hs; rw [ho] at honce; cases honce
    | some b =>
      cases b with
      | true =>
        simp only [AState.toCSt, ho, Option.getD_some, ↓reduceIte] at h
        rw [CM_refuseM_run] at h; cases h
      | false =>
        simp only [AState.toCSt, ho, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at h
        rw [CM_pure_run] at h
        refine ⟨?_, (Runs_ok_eq h).2.symm⟩
        rintro ⟨id, hs, honce⟩
        rw [hsrc] at hs; cases hs; rw [ho] at honce; cases honce

theorem Runs_killSrc {σ σ' : AState} {v : AVal}
    (hok : AStateOk σ) (h : Runs (killSrc v) σ () σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    (v.onceOnly = true → ∀ x, v.src = some x → x < σ.st.size → σ'.st[x]? = some .dead) ∧
    (∀ y, (v.onceOnly = true → v.src ≠ some y) → σ'.st[y]? = σ.st[y]?) ∧
    σ'.once = σ.once ∧ σ'.spent = σ.spent ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion := by
  unfold Runs killSrc at h
  cases ho : v.onceOnly with
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
    rw [CM_pure_run] at h
    have hEq := (Runs_ok_eq h).2.symm
    rw [hEq]
    exact ⟨hok, AStateLe.refl σ, fun hf => (by cases hf), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | true =>
    simp only [ho, ↓reduceIte] at h
    cases hsrc : v.src with
    | none =>
      simp only [hsrc] at h
      rw [CM_pure_run] at h
      have hEq := (Runs_ok_eq h).2.symm
      rw [hEq]
      exact ⟨hok, AStateLe.refl σ, fun _ _ hs => (by cases hs), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | some x =>
      simp only [hsrc] at h
      have hst : σ' = { σ with st := σ.st.set! x .dead } := Runs_setSt h
      subst hst
      have hmon : match σ.st[x]? with | some b0 => BSt.le b0 .dead | none => True := by
        cases σ.st[x]? with
        | none => trivial
        | some b0 => cases b0 <;> trivial
      obtain ⟨hok', hle'⟩ := AStateOk_setSt hok hmon
      refine ⟨hok', hle', ?_, ?_, rfl, rfl, rfl, rfl⟩
      · intro _ y hy hlt
        cases hy
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
        simp only [hlt, ↓reduceIte]
      · intro y hne
        have hyne : y ≠ x := fun heq => hne rfl (by simp [heq])
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hyne)]

/-! ## 2. Heap, `OldSameShape`, `StOk`, `CtorFieldsOk`, and `NoOnceCell` Bridges -/

theorem OldSameShape.to_sameShapeOn {h₁ h₂ : Heap} (h : OldSameShape h₁ h₂) (S : Nat → Prop) :
    SameShapeOn S h₁ h₂ :=
  fun l o₁ _ ho₁ => h.2 l o₁ ho₁

theorem PreservesOnceShell.of_oldSameShape_noOnce {h₁ h₂ : Heap} {S : Nat → Prop}
    (hp : PreservesLocs (fun l => l < h₁.objs.size ∧ ¬ S l) h₁ h₂)
    (hno : ∀ l o tgt sp, S l → h₁.objs[l]? = some o → o.cell ≠ .once tgt sp) :
    PreservesOnceShell h₁ h₂ := by
  intro l o₁ tgt₁ sp₁ ho₁ hcell₁
  have hlt : l < h₁.objs.size := (Array.getElem?_eq_some_iff.mp ho₁).1
  have hnotS : ¬ S l := fun hs => hno l o₁ tgt₁ sp₁ hs ho₁ hcell₁
  exact ⟨o₁, tgt₁, sp₁, (hp l ⟨hlt, hnotS⟩).trans ho₁, rfl, hcell₁⟩

theorem StOk_staticStrLoc_lt {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} {l : Nat}
    (hst : StOk P ext B st) (hl : StaticStrLoc st l) : l < st.heap.objs.size := by
  rcases hl with ⟨r, v, hm, hr⟩ | ⟨s, v, hm, hr⟩
  · obtain ⟨_, _, _, _, hbase, _⟩ := hst.2.2.1 r v hm
    exact hbase.1.reach_lt_size hr
  · obtain ⟨loc, cap, o, rfl, ho, _, hcell⟩ := hst.2.2.2 s v hm
    cases hr with
    | here => exact (Array.getElem?_eq_some_iff.mp ho).1
    | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1

theorem StOk_of_preserves_outside {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    {S : Nat → Prop}
    (hst : StOk P ext B st)
    (hcaps : CapsOk st'.heap)
    (hregs : st'.regions = st.regions)
    (hnr : st.nextRegion ≤ st'.nextRegion)
    (hstat : st'.statics = st.statics)
    (hstr : st'.strs = st.strs)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ S l) st.heap st'.heap)
    (hdisj : ∀ l, StaticStrLoc st l → ¬ S l) :
    StOk P ext B st' := by
  have hregs' : RegsOk st' := by
    obtain ⟨hpos, hnd, hlt⟩ := hst.2.1
    exact ⟨Nat.lt_of_lt_of_le hpos hnr, by rw [hregs]; exact hnd,
      fun r hr => let ⟨h1, h2⟩ := hlt r (by rwa [← hregs]); ⟨h1, Nat.lt_of_lt_of_le h2 hnr⟩⟩
  have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
    hp.mono fun l hl => ⟨StOk_staticStrLoc_lt hst hl, hdisj l hl⟩
  exact StOk_preserve hst hcaps hregs' (RegsFuture.same_regions hnr hregs) hstat hstr hpSS

theorem StOk_of_preserves_old {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    (hst : StOk P ext B st)
    (hcaps : CapsOk st'.heap)
    (hregs : st'.regions = st.regions)
    (hnr : st.nextRegion ≤ st'.nextRegion)
    (hstat : st'.statics = st.statics)
    (hstr : st'.strs = st.strs)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap) :
    StOk P ext B st' :=
  StOk_of_preserves_outside (S := fun _ => False) hst hcaps hregs hnr hstat hstr
    (hp.mono fun _ h => h.1) (fun _ _ h => h)

theorem StaticStrLoc_of_preserves_outside {st st' : St}
    (hstat : st'.statics = st.statics) (hstr : st'.strs = st.strs)
    (hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap) :
    ∀ l, StaticStrLoc st' l → StaticStrLoc st l := by
  intro l hl
  rcases hl with ⟨r, v, hm, hr⟩ | ⟨s, v, hm, hr⟩
  · rw [hstat] at hm
    have hpV : PreservesLocs (Reach st.heap v) st.heap st'.heap :=
      hpSS.mono fun x hx => Or.inl ⟨r, v, hm, hx⟩
    exact Or.inl ⟨r, v, hm, (Reach_congr hpV l).mp hr⟩
  · rw [hstr] at hm
    have hpV : PreservesLocs (Reach st.heap v) st.heap st'.heap :=
      hpSS.mono fun x hx => Or.inr ⟨s, v, hm, hx⟩
    exact Or.inr ⟨s, v, hm, (Reach_congr hpV l).mp hr⟩

theorem StaticStrFresh_of_preserves_outside {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    {S : Nat → Prop}
    (hst : StOk P ext B st)
    (hstat : st'.statics = st.statics) (hstr : st'.strs = st.strs)
    (hp : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ S l) st.heap st'.heap)
    (hdisj : ∀ l, StaticStrLoc st l → ¬ S l) :
    StaticStrFresh st st' := by
  have hpSS : PreservesLocs (StaticStrLoc st) st.heap st'.heap :=
    hp.mono fun l hl => ⟨StOk_staticStrLoc_lt hst hl, hdisj l hl⟩
  exact fun l hl => Or.inr (Or.inl (StaticStrLoc_of_preserves_outside hstat hstr hpSS l hl))

theorem DeepTaintsBounded_of_oldSameShape {h₁ h₂ : Heap} {b : Nat} {v₁ v₂ : Val}
    (hdl₁ : DeepLive h₁ v₁) (hoss : OldSameShape h₁ h₂)
    (hloc : SameLoc v₁ v₂)
    (htTop : ∀ r ∈ v₂.taint, r < b)
    (hb₁ : DeepTaintsBounded h₁ b v₁) :
    DeepTaintsBounded h₂ b v₂ := by
  intro w₂ hw₂ r hr
  rcases hw₂ with rfl | ⟨l, o₂, hr₂, ho₂, hmem₂⟩
  · exact htTop r hr
  · have hr₁ : Reach h₁ v₁ l := Reach_of_sameShapeOn_rev hdl₁ (hoss.to_sameShapeOn _) hloc hr₂
    obtain ⟨o₁, ho₁⟩ := hdl₁.exists_obj hr₁
    obtain ⟨o₂', ho₂', hcs⟩ := hoss.2 l o₁ ho₁
    rw [ho₂] at ho₂'; cases ho₂'
    obtain ⟨w₁, hmem₁, hvs⟩ := hcs.symm.vals_fwd hmem₂
    rw [hvs.taint_eq] at hr
    exact hb₁ w₁ (Or.inr ⟨l, o₁, hr₁, ho₁, hmem₁⟩) r hr

theorem ValBaseOk_of_deepLive {st : St} {v : Val}
    (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v)
    (htb : DeepTaintsBounded st.heap st.nextRegion v) :
    ValBaseOk st v :=
  ⟨hdl, hacyc, fun w hw => (hdl w hw).2, htb⟩

theorem DeepTaintsBounded_addTaint {h : Heap} {b s : Nat} {v : Val}
    (hs : s < b) (hb : DeepTaintsBounded h b v) :
    DeepTaintsBounded h b (addTaint s v) := by
  intro w hw r hr
  rcases hw with rfl | ⟨l, o, hr', ho, hm⟩
  · rcases mem_taint_addTaint hr with rfl | hv
    · exact hs
    · exact hb v (HeldBy.refl _ _) r hv
  · exact hb w (Or.inr ⟨l, o, (Reach_addTaint_iff l).mp hr', ho, hm⟩) r hr

theorem DeepTaintsBounded_renameTaint {h : Heap} {b s cur : Nat} {v : Val}
    (hcur : cur < b) (hb : DeepTaintsBounded h b v) :
    DeepTaintsBounded h b (renameTaint s cur v) := by
  intro w hw r hr
  rcases hw with rfl | ⟨l, o, hr', ho, hm⟩
  · cases v with
    | imm _ => cases hr
    | ref loc cap t =>
      simp only [IxC.Resource.renameTaint] at hr
      split at hr
      · split at hr
        · simp only [Val.taint, List.mem_filter] at hr
          exact hb (.ref loc cap t) (HeldBy.refl _ _) r hr.1
        · simp only [Val.taint, List.mem_cons, List.mem_filter] at hr
          rcases hr with rfl | h1
          · exact hcur
          · exact hb (.ref loc cap t) (HeldBy.refl _ _) r h1.1
      · exact hb (.ref loc cap t) (HeldBy.refl _ _) r hr
  · exact hb w (Or.inr ⟨l, o, (Reach_renameTaint_iff l).mp hr', ho, hm⟩) r hr

theorem DeepTaintsBounded_alloc {h : Heap} {b : Nat} {c : Cell} {t : List Nat}
    (ht : ∀ r ∈ t, r < b)
    (hdl : ∀ w ∈ c.vals, DeepLive h w)
    (hsub : ∀ w ∈ c.vals, DeepTaintsBounded h b w) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    DeepTaintsBounded h' b (.ref h.objs.size h.nextCap t) := by
  intro h' w hw r hr
  rcases HeldBy_alloc_new (t := t) hdl hw with rfl | ⟨u, hu, hwu⟩
  · exact ht r hr
  · exact hsub u hu w hwu r hr

theorem DeepTaintsBounded_imm (h : Heap) (b : Nat) (i : Imm) :
    DeepTaintsBounded h b (.imm i) := by
  intro w hw r hr
  rcases hw with rfl | ⟨_, _, hreach, _, _⟩
  · cases hr
  · cases hreach

theorem DeepTaintsBounded_num {h : Heap} {b loc cap : Nat} {o : Obj} {n : Nat}
    (ho : h.objs[loc]? = some o) (hcell : o.cell = .num n) :
    DeepTaintsBounded h b (.ref loc cap []) := by
  intro w hw r hr
  rcases hw with rfl | ⟨l, o', hreach, ho', hm⟩
  · cases hr
  · cases hreach with
    | here => rw [ho] at ho'; cases ho'; rw [hcell] at hm; cases hm
    | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1

theorem DeepTaintsBounded_str {h : Heap} {b loc cap : Nat} {o : Obj} {s : String}
    (ho : h.objs[loc]? = some o) (hcell : o.cell = .str s) :
    DeepTaintsBounded h b (.ref loc cap []) := by
  intro w hw r hr
  rcases hw with rfl | ⟨l, o', hreach, ho', hm⟩
  · cases hr
  · cases hreach with
    | here => rw [ho] at ho'; cases ho'; rw [hcell] at hm; cases hm
    | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1

theorem NoOnceCell_alloc_nonOnce {h : Heap} {c : Cell} {t : List Nat}
    (hnot : ∀ tgt sp, c ≠ .once tgt sp)
    (hsub : ∀ w ∈ c.vals, DeepLive h w ∧ NoOnceCell h w) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    NoOnceCell h' (.ref h.objs.size h.nextCap t) := by
  intro h' l o hr ho tgt sp hcell
  cases hr with
  | here =>
    simp only [h', Array.getElem?_push_size, Option.some.injEq] at ho
    subst ho
    exact hnot tgt sp hcell
  | @step _ _ _ _ u _ ho0 hm0 hr1 =>
    simp only [h', Array.getElem?_push_size, Option.some.injEq] at ho0
    subst ho0
    have ⟨hdlW, hnoW⟩ := hsub u hm0
    have hpW : PreservesLocs (Reach h u) h h' := by
      intro x hx
      have hlt : x < h.objs.size := hdlW.reach_lt_size hx
      dsimp only [h']
      rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
    exact NoOnceCell_congr hdlW hpW hnoW l o hr1 ho tgt sp hcell

theorem CtorFieldsOk_alloc_ctor {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {r : Ref} {fs : Array Val} {t : List Nat}
    (hfs : ∀ w ∈ fs.toList, DeepLive st.heap w ∧ NoOnceCell st.heap w ∧
      FunOkAt P ext B st .unknown false (fun _ => False) w ∧ CtorFieldsOk P ext B st w) :
    let st' : St := { st with heap := { objs := st.heap.objs.push ⟨.ctor r fs, st.heap.nextCap⟩,
                                        nextCap := st.heap.nextCap + 1 } }
    CtorFieldsOk P ext B st' (.ref st.heap.objs.size st.heap.nextCap t) := by
  intro st' l o r' fs' w hr ho hcell hw
  have hpOld : PreservesLocs (fun x => x < st.heap.objs.size) st.heap st'.heap :=
    alloc_preserves_old (.ctor r fs) t st
  have hrf : RegsFuture st st' := RegsFuture.same_regions (Nat.le_refl _) rfl
  cases hr with
  | here =>
    simp only [st', Array.getElem?_push_size, Option.some.injEq] at ho
    subst ho
    cases hcell
    obtain ⟨hdlW, hnoW, hfunW, _⟩ := hfs w hw
    have hpW : PreservesLocs (Reach st.heap w) st.heap st'.heap :=
      hpOld.mono fun x hx => hdlW.reach_lt_size hx
    exact ⟨NoOnceCell_congr hdlW hpW hnoW, FunOkAt_preserve_locs hpW hrf hfunW⟩
  | step ho0 hm0 hr1 =>
    simp only [st', Array.getElem?_push_size, Option.some.injEq] at ho0
    subst ho0
    obtain ⟨hdlU, _, _, hcfU⟩ := hfs _ hm0
    have hpU : PreservesLocs (Reach st.heap _) st.heap st'.heap :=
      hpOld.mono fun x hx => hdlU.reach_lt_size hx
    exact CtorFieldsOk_congr hdlU hpU hrf hcfU l o r' fs' w hr1 ho hcell hw

theorem CtorFieldsOk_alloc_nonCtor {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {c : Cell} {t : List Nat}
    (hnot : ∀ r fs, c ≠ .ctor r fs)
    (hsub : ∀ w ∈ c.vals, DeepLive st.heap w ∧ CtorFieldsOk P ext B st w) :
    let st' : St := { st with heap := { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩,
                                        nextCap := st.heap.nextCap + 1 } }
    CtorFieldsOk P ext B st' (.ref st.heap.objs.size st.heap.nextCap t) := by
  intro st' l o r' fs' w hr ho hcell hw
  have hpOld : PreservesLocs (fun x => x < st.heap.objs.size) st.heap st'.heap :=
    alloc_preserves_old c t st
  have hrf : RegsFuture st st' := RegsFuture.same_regions (Nat.le_refl _) rfl
  cases hr with
  | here =>
    simp only [st', Array.getElem?_push_size, Option.some.injEq] at ho
    subst ho
    exact False.elim (hnot r' fs' hcell)
  | step ho0 hm0 hr1 =>
    simp only [st', Array.getElem?_push_size, Option.some.injEq] at ho0
    subst ho0
    obtain ⟨hdlU, hcfU⟩ := hsub _ hm0
    have hpU : PreservesLocs (Reach st.heap _) st.heap st'.heap :=
      hpOld.mono fun x hx => hdlU.reach_lt_size hx
    exact CtorFieldsOk_congr hdlU hpU hrf hcfU l o r' fs' w hr1 ho hcell hw

/-! ## 3. Operational Rule Bridges (`conform`, `strValue`, `prim`, `readOut`, `bindAt`, `ret`, `construct`) -/

/-- `conform c v` on a `SpentOnceSafe` value never produces a violation. -/
theorem conform_spentOnceSafe {st : St} {c : Cls} {v : Val}
    (hs : SpentOnceSafe st.heap v) :
    (conform c v).run st = .error .stuck ∨
    ∃ v', (conform c v).run st = .ok (v', st) ∧
      ((v' = v ∧ c = .val) ∨ (v' = .imm .irr ∧ (c = .irr ∨ c = .imm))) := by
  rcases hs with rfl | ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩
  · cases c with
    | irr => exact Or.inr ⟨.imm .irr, rfl, Or.inr ⟨rfl, Or.inl rfl⟩⟩
    | val => exact Or.inr ⟨.imm .irr, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | imm => exact Or.inr ⟨.imm .irr, rfl, Or.inr ⟨rfl, Or.inr rfl⟩⟩
    | leaf => exact Or.inl rfl
  · have hlive : LiveRef st.heap (.ref loc cap t) := ⟨o, ho, hcap⟩
    cases c with
    | irr => exact Or.inr ⟨.imm .irr, rfl, Or.inr ⟨rfl, Or.inl rfl⟩⟩
    | val => exact Or.inr ⟨.ref loc cap t, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | imm =>
      left
      unfold conform
      rw [M_bind_run, numOf?_ok hlive]
      simp [ho, hcell]; rfl
    | leaf =>
      left
      unfold conform
      rw [M_bind_run, numOf?_ok hlive]
      simp [ho, hcell]; rfl

/-- `conform c v` on a full `ValBaseOk` value preserves `StOk`, `ValBaseOk`, `CtorFieldsOk`,
`NoOnceCell`, `FunOkAt`, `PreservesOnceShell`, `StaticStrFresh`. -/
theorem conform_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {c : Cls} {sk : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {v : Val}
    (hst : StOk P ext B st)
    (hbase : ValBaseOk st v)
    (hcf : CtorFieldsOk P ext B st v)
    (hno : onceOnly = false → NoOnceCell st.heap v)
    (hfun : FunOkAt P ext B st sk onceOnly Foot v) :
    (conform c v).run st = .error .stuck ∨
    ∃ v' st', (conform c v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' v' ∧
      ClsSafe st'.heap c v' ∧
      CtorFieldsOk P ext B st' v' ∧
      (∀ rs A, DeepOpenUnder st.heap rs A v → DeepOpenUnder st'.heap rs A v') ∧
      (∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
      (∀ l, OwnReach P st'.heap v' l → OwnReach P st.heap v l) ∧
      (OwnTreeFull P st.heap v → OwnTreeFull P st'.heap v') ∧
      (onceOnly = false → NoOnceCell st'.heap v') ∧
      (c = .val → v' = v ∧ st' = st) ∧
      (c ≠ .val → NoOnceCell st'.heap v' ∧ FunOkAt P ext B st' sk false (fun _ => False) v') ∧
      FunOkAt P ext B st' sk onceOnly Foot v' := by
  rcases conform_spec_full (P := P) hst.1 hbase.1 hbase.2.1 with hstck |
    ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, hc', hdl', hcls', hacyc',
      ht', hreach', hown', htree', hdou'⟩
  · exact Or.inl hstck
  · right
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_preservesLocs (hpres.mono fun l ⟨o, _, _, ho, _⟩ =>
        (Array.getElem?_eq_some_iff.mp ho).1)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat hstr
        (hpres.mono fun _ h => h.1) (fun _ _ h => h)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_old hst hc' hr (by rw [hnr]; exact Nat.le_refl _) hstat hstr hpres
    have hvalCase : c = .val → v' = v ∧ st' = st := by
      intro hcv; subst hcv; unfold conform at hrun; cases hrun; exact ⟨rfl, rfl⟩
    have hbase' : ValBaseOk st' v' := by
      refine ValBaseOk_of_deepLive hdl' hacyc' ?_
      cases c with
      | val =>
        obtain ⟨rfl, rfl⟩ := hvalCase rfl; exact hbase.2.2.2
      | irr =>
        rw [hcls']; exact DeepTaintsBounded_imm _ _ _
      | imm =>
        obtain ⟨i, rfl⟩ := hcls'; exact DeepTaintsBounded_imm _ _ _
      | leaf =>
        obtain ⟨loc, cap, o, n, rfl, ho, hcell, _⟩ := hcls'
        exact DeepTaintsBounded_num ho hcell
    have hcf' : CtorFieldsOk P ext B st' v' := by
      cases c with
      | val => obtain ⟨rfl, rfl⟩ := hvalCase rfl; exact hcf
      | irr | imm | leaf => exact ClsSafe_ctorFieldsOk P ext B st' (by decide) (ClsSafe.of_clsOk hcls')
    have hnoNe : c ≠ .val → NoOnceCell st'.heap v' := by
      intro hne
      exact ClsSafe_noOnceCell hne (ClsSafe.of_clsOk hcls')
    have hfunNe : c ≠ .val → FunOkAt P ext B st' sk false (fun _ => False) v' := by
      intro hne
      exact ClsSafe_funOkAt P ext B st' sk hne (ClsSafe.of_clsOk hcls')
    have hno' : onceOnly = false → NoOnceCell st'.heap v' := by
      intro hoF
      cases c with
      | val => obtain ⟨rfl, rfl⟩ := hvalCase rfl; exact hno hoF
      | irr | imm | leaf => exact hnoNe (by decide)
    have hfun' : FunOkAt P ext B st' sk onceOnly Foot v' := by
      cases c with
      | val => obtain ⟨rfl, rfl⟩ := hvalCase rfl; exact hfun
      | irr | imm | leaf =>
        have hfp := hfunNe (by decide)
        cases onceOnly with
        | false => exact FunOkAt_weaken_foot (fun _ h => False.elim h) hfp
        | true => exact FunOkAt_weaken_foot (fun _ h => False.elim h) (FunOkAt_weaken_onceOnly hfp)
    exact ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf, hst',
      hbase', ClsSafe.of_clsOk hcls', hcf', hdou', hreach', hown', htree', hno', hvalCase,
      fun hne => ⟨hnoNe hne, hfunNe hne⟩, hfun'⟩

/-- Soundness & framing of `Eval.strValue` wrt `StOk`, `ValBaseOk`, `FunOkAt`, `StaticStrFresh`. -/
theorem strValue_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} (s : String)
    (hst : StOk P ext B st) :
    ∃ v st', (strValue s).run st = .ok (v, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ ArrayExtends st.strs st'.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' v ∧
      DeepOpenUnder st'.heap st'.regions [] v ∧
      CtorFieldsOk P ext B st' v ∧
      NoOnceCell st'.heap v ∧
      FunOkAt P ext B st' .data false (fun _ => False) v ∧
      (∀ l, Reach st'.heap v l → st.heap.objs.size ≤ l ∨ StaticStrLoc st l) := by
  unfold strValue
  rw [M_bind_run, M_get_run]; dsimp only
  cases hfind : st.strs.find? (·.1 == s) with
  | some p =>
    have hmem : p ∈ st.strs.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    obtain ⟨loc, cap, o, hpEq, ho, hcap, hcell⟩ := hst.2.2.2 p.1 p.2 hmem
    have hlive : LiveRef st.heap p.2 := by rw [hpEq]; exact ⟨o, ho, hcap⟩
    have hrun : (do live p.2; pure p.2 : M Val).run st = .ok (p.2, st) := by
      rw [M_bind_run, live_ok hlive]; rfl
    have hdl : DeepLive st.heap (.ref loc cap []) := by
      intro w hw
      rcases hw with rfl | ⟨l, o', hr, ho', hm⟩
      · exact ⟨⟨o, ho, hcap⟩, fun o' n ho' hc' => rfl⟩
      · cases hr with
        | here => rw [ho] at ho'; cases ho'; rw [hcell] at hm; cases hm
        | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
    have hacyc : AcyclicFrom st.heap (.ref loc cap []) := by
      intro l o' w hr ho' hm
      cases hr with
      | here => rw [ho] at ho'; cases ho'; rw [hcell] at hm; cases hm
      | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
    have hdou : DeepOpenUnder st.heap st.regions [] (.ref loc cap []) := by
      intro w hw r hr _
      rcases hw with rfl | ⟨l, o', hreach, ho', hm⟩
      · cases hr
      · cases hreach with
        | here => rw [ho] at ho'; cases ho'; rw [hcell] at hm; cases hm
        | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
    have hcf : CtorFieldsOk P ext B st (.ref loc cap []) := by
      intro l o' r' fs w hr ho' hc' _
      cases hr with
      | here => rw [ho] at ho'; cases ho'; rw [hcell] at hc'; cases hc'
      | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
    have hno : NoOnceCell st.heap (.ref loc cap []) := by
      intro l o' hr ho' _ _ hc'
      cases hr with
      | here => rw [ho] at ho'; cases ho'; rw [hcell] at hc'; cases hc'
      | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
    refine ⟨p.2, st, hrun, rfl, rfl, rfl, ArrayExtends.refl _, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, PreservesOnceShell.refl _, StaticStrFresh.refl _, hst, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpEq]; exact ValBaseOk_of_deepLive hdl hacyc (DeepTaintsBounded_str ho hcell)
    · rw [hpEq]; exact hdou
    · rw [hpEq]; exact hcf
    · rw [hpEq]; exact hno
    · rw [hpEq]; exact FunOkAt_nonCallable_ref P ext B st .data ho (by rw [hcell]; trivial)
    · intro l hr; exact Or.inr (Or.inr ⟨p.1, p.2, hmem, hr⟩)
  | none =>
    let loc := st.heap.objs.size
    let cap := st.heap.nextCap
    let st₁ : St := { st with heap := { objs := st.heap.objs.push ⟨.str s, cap⟩, nextCap := cap + 1 } }
    let st₂ : St := { st₁ with strs := st₁.strs.push (s, .ref loc cap []) }
    have ho : st₁.heap.objs[loc]? = some ⟨.str s, cap⟩ := by simp [st₁, loc]
    have hst₁ : StOk P ext B st₁ := StOk_alloc (.str s) hst
    have hst₂ : StOk P ext B st₂ := StOk_pushStr hst₁ ho rfl rfl
    have hpres : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₂.heap :=
      alloc_preserves_old (.str s) [] st
    have hdl : DeepLive st₂.heap (.ref loc cap []) := by
      intro w hw
      rcases hw with rfl | ⟨l, o', hr, ho', hm⟩
      · exact ⟨⟨⟨.str s, cap⟩, ho, rfl⟩, fun _ _ _ _ => rfl⟩
      · cases hr with
        | here => rw [ho] at ho'; cases ho'; cases hm
        | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; cases hm1
    have hacyc : AcyclicFrom st₂.heap (.ref loc cap []) := by
      intro l o' w hr ho' hm
      cases hr with
      | here => rw [ho] at ho'; cases ho'; cases hm
      | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; cases hm1
    have hdou : DeepOpenUnder st₂.heap st₂.regions [] (.ref loc cap []) := by
      intro w hw r hr _
      rcases hw with rfl | ⟨l, o', hreach, ho', hm⟩
      · cases hr
      · cases hreach with
        | here => rw [ho] at ho'; cases ho'; cases hm
        | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; cases hm1
    have hcf : CtorFieldsOk P ext B st₂ (.ref loc cap []) := by
      intro l o' r' fs w hr ho' hc' _
      cases hr with
      | here => rw [ho] at ho'; cases ho'; cases hc'
      | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; cases hm1
    have hno : NoOnceCell st₂.heap (.ref loc cap []) :=
      NoOnceCell_alloc_nonOnce (by intro _ _ h; cases h) (fun _ h => by cases h)
    have hssf : StaticStrFresh st st₂ := by
      intro l hl
      rcases hl with ⟨r, v, hm, hr⟩ | ⟨s', v, hm, hr⟩
      · have hpV : PreservesLocs (Reach st.heap v) st.heap st₂.heap :=
          hpres.mono fun x hx => StOk_staticStrLoc_lt hst (Or.inl ⟨r, v, hm, hx⟩)
        exact Or.inr (Or.inl (Or.inl ⟨r, v, hm, (Reach_congr hpV l).mp hr⟩))
      · rw [show st₂.strs.toList = st.strs.toList ++ [(s, .ref loc cap [])] by
              simp [st₂, st₁, Array.toList_push]] at hm
        rcases List.mem_append.mp hm with hmOld | hmNew
        · obtain ⟨l0, c0, o0, rfl, ho0, _, hc0⟩ := hst.2.2.2 s' v hmOld
          have hpV : PreservesLocs (Reach st.heap (.ref l0 c0 [])) st.heap st₂.heap :=
            hpres.mono fun x hx => by
              cases hx with
              | here => exact (Array.getElem?_eq_some_iff.mp ho0).1
              | step ho1 hm1 _ => rw [ho0] at ho1; cases ho1; rw [hc0] at hm1; cases hm1
          exact Or.inr (Or.inl (Or.inr ⟨s', .ref l0 c0 [], hmOld, (Reach_congr hpV l).mp hr⟩))
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmNew
          obtain ⟨_, rfl⟩ := hmNew
          cases hr with
          | here => exact Or.inl (Nat.le_refl _)
          | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; cases hm1
    refine ⟨.ref loc cap [], st₂, rfl, rfl, rfl, rfl, ArrayExtends.push _ _,
      by simp [st₂, st₁], by simp [st₂, st₁, cap], hpres,
      PreservesOnceShell.of_alloc (.str s) st.heap, hssf, hst₂,
      ValBaseOk_of_deepLive hdl hacyc (DeepTaintsBounded_str ho rfl),
      hdou, hcf, hno, FunOkAt_nonCallable_ref P ext B st₂ .data ho trivial, ?_⟩
    intro l hr
    cases hr with
    | here => exact Or.inl (Nat.le_refl _)
    | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; cases hm1

/-- Soundness & framing of `Eval.prim` followed by `conform c`. -/
theorem prim_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {p : Prim} {vs : List Val} {c : Cls}
    (hst : StOk P ext B st)
    (hl : ∀ v ∈ vs, LiveRef st.heap v) :
    (do conform c (← prim p vs)).run st = .error .stuck ∨
    ∃ rv st', (do conform c (← prim p vs)).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' rv ∧
      ClsSafe st'.heap c rv ∧
      DeepOpenUnder st'.heap st'.regions [] rv ∧
      CtorFieldsOk P ext B st' rv ∧
      NoOnceCell st'.heap rv ∧
      FunOkAt P ext B st' .unknown false (fun _ => False) rv ∧
      OwnTreeFull P st'.heap rv ∧
      (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l) := by
  rw [M_bind_run]
  rcases prim_spec (P := P) hst.1 hl with hstck |
    ⟨v₁, st₁, hrun₁, hr₁, hnr₁, hstat₁, hstr₁, hsz₁, hcap₁, hpres₁, hc₁, _, hdl₁, _, _, hacyc₁, htree₁, hvShape⟩
  · left; rw [hstck]
  · rw [hrun₁]; dsimp only
    have hst₁ : StOk P ext B st₁ :=
      StOk_of_preserves_old hst hc₁ hr₁ (by rw [hnr₁]; exact Nat.le_refl _) hstat₁ hstr₁ hpres₁
    have honce₁ : PreservesOnceShell st.heap st₁.heap :=
      PreservesOnceShell.of_preservesLocs (hpres₁.mono fun l ⟨o, _, _, ho, _⟩ =>
        (Array.getElem?_eq_some_iff.mp ho).1)
    have hssf₁ : StaticStrFresh st st₁ :=
      StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat₁ hstr₁
        (hpres₁.mono fun _ h => h.1) (fun _ _ h => h)
    have ⟨htb₁, hdou₁, hcf₁, hno₁, hfun₁, hreach₁⟩ :
        DeepTaintsBounded st₁.heap st₁.nextRegion v₁ ∧
        DeepOpenUnder st₁.heap st₁.regions [] v₁ ∧
        CtorFieldsOk P ext B st₁ v₁ ∧
        NoOnceCell st₁.heap v₁ ∧
        FunOkAt P ext B st₁ .unknown false (fun _ => False) v₁ ∧
        (∀ l, Reach st₁.heap v₁ l → st.heap.objs.size ≤ l) := by
      rcases hvShape with ⟨i, rfl, _⟩ | ⟨loc, cap, o, n, rfl, hge, ho, hcell, hcapO⟩
      · refine ⟨DeepTaintsBounded_imm _ _ _, DeepOpenUnder_imm _ _ _ _,
          CtorFieldsOk_imm P ext B st₁ i, NoOnceCell_imm _ _, ?_, fun _ hr => by cases hr⟩
        cases i with
        | irr => exact FunOkAt_imm_irr P ext B st₁ .unknown
        | con _ => exact FunOkAt_nonCallable_imm P ext B st₁ .unknown (by intro h; cases h)
        | bits _ => exact FunOkAt_nonCallable_imm P ext B st₁ .unknown (by intro h; cases h)
      · have hclsL : ClsSafe st₁.heap .leaf (.ref loc cap []) :=
          ClsSafe.of_clsOk ⟨loc, cap, o, n, rfl, ho, hcell, hcapO⟩
        refine ⟨DeepTaintsBounded_num ho hcell,
          ClsSafe_deepOpenUnder_nil (c := .leaf) (by decide) hclsL,
          ClsSafe_ctorFieldsOk P ext B st₁ (by decide) hclsL,
          ClsSafe_noOnceCell (c := .leaf) (by decide) hclsL,
          ClsSafe_funOkAt P ext B st₁ .unknown (by decide) hclsL,
          fun l hr => ?_⟩
        cases hr with
        | here => exact hge
        | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
    rcases conform_sound (P := P) (ext := ext) (B := B) (c := c) (sk := .unknown)
      (onceOnly := false) (Foot := fun _ => False) hst₁
      (ValBaseOk_of_deepLive hdl₁ hacyc₁ htb₁) hcf₁ (fun _ => hno₁) hfun₁ with hstck2 |
      ⟨rv, st', hrun₂, hr₂, hnr₂, hstat₂, hstr₂, hsz₂, hcap₂, hpres₂, honce₂, hssf₂, hst',
        hbase', hcls', hcf', hdou', hreach₂, _, htree₂, hno', _, _, hfun'⟩
    · exact Or.inl hstck2
    · right
      refine ⟨rv, st', hrun₂, hr₂.trans hr₁, hnr₂.trans hnr₁, hstat₂.trans hstat₁, hstr₂.trans hstr₁,
        Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
        PreservesLocs.trans hpres₁ (hpres₂.mono fun l hl => Nat.lt_of_lt_of_le hl hsz₁),
        honce₁.trans honce₂,
        StaticStrFresh.trans hsz₁ (hpres₂.mono fun l hl => StOk_staticStrLoc_lt hst₁ hl) hssf₁ hssf₂,
        hst', hbase', hcls', by rw [hr₂]; exact hdou' st₁.regions [] hdou₁, hcf', hno' rfl, hfun', htree₂ htree₁, ?_⟩
      intro l hr
      rcases hreach₂ l hr with hnew | hold
      · exact Nat.le_trans hsz₁ hnew
      · exact hreach₁ l hold

/-- Soundness of `Eval.readOut` on a value read out of a cell with taint `t`. -/
theorem readOut_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {inherit : Bool} {t : List Nat} {v : Val} {sk : Skel} {A : List Nat}
    (hbase : ValBaseOk st v)
    (htb : inherit = true → ∀ r ∈ t, r < st.nextRegion)
    (htA : inherit = true → ∀ r ∈ t, r ∈ st.regions → r ∈ A)
    (hopen : DeepOpenUnder st.heap st.regions A v)
    (hcf : CtorFieldsOk P ext B st v)
    (hno : NoOnceCell st.heap v)
    (hfun : FunOkAt P ext B st sk false (fun _ => False) v) :
    ∃ v', (readOut inherit t v).run st = .ok (v', st) ∧
      SameLoc v v' ∧
      ValBaseOk st v' ∧
      DeepOpenUnder st.heap st.regions A v' ∧
      CtorFieldsOk P ext B st v' ∧
      NoOnceCell st.heap v' ∧
      FunOkAt P ext B st sk false (fun _ => False) v' ∧
      (∀ l, Reach st.heap v' l ↔ Reach st.heap v l) ∧
      (∀ l, OwnReach P st.heap v' l ↔ OwnReach P st.heap v l) ∧
      (OwnTreeFull P st.heap v → OwnTreeFull P st.heap v') := by
  obtain ⟨v', hrun, hlive', hlu', ht', hreach', hheld'⟩ :=
    readOut_ok (inherit := inherit) (t := t) hbase.1.self.1 hbase.1.self.2
  have hshape : (∀ i, v = .imm i → v' = .imm i) ∧
      (∀ loc cap tv, v = .ref loc cap tv → ∃ tv', v' = .ref loc cap tv') := by
    constructor
    · intro i hv; subst hv
      unfold readOut at hrun
      rw [M_bind_run, isLeaf_ok hbase.1.self.1] at hrun
      cases inherit with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at hrun
        cases hrun; rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
        rw [foldl_addTaint_imm] at hrun
        cases hrun; rfl
    · intro loc cap tv hv; subst hv
      unfold readOut at hrun
      rw [M_bind_run, isLeaf_ok hbase.1.self.1] at hrun
      obtain ⟨o, ho, _⟩ := hbase.1.self.1
      simp only [ho] at hrun
      cases hc : o.cell.isNum with
      | true =>
        simp only [hc, ↓reduceIte] at hrun
        cases hrun; exact ⟨[], rfl⟩
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hrun
        cases inherit with
        | false =>
          simp only [Bool.not_false, ↓reduceIte] at hrun
          cases hrun; exact ⟨tv, rfl⟩
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
          obtain ⟨tv1, htv1⟩ := foldl_addTaint_ref t loc cap tv
          rw [htv1] at hrun; cases hrun; exact ⟨tv1, rfl⟩
  have hloc : SameLoc v v' := by
    cases v with
    | imm i => rw [hshape.1 i rfl]; rfl
    | ref loc cap tv => obtain ⟨tv', hEq⟩ := hshape.2 loc cap tv rfl; rw [hEq]; rfl
  have hdl' : DeepLive st.heap v' := by
    intro w hw
    rcases hheld' w hw with rfl | hwv
    · exact ⟨hlive', hlu'⟩
    · exact hbase.1 w hwv
  have hacyc' : AcyclicFrom st.heap v' :=
    fun l o w hr ho hm => hbase.2.1 l o w ((hreach' l).mp hr) ho hm
  have htb' : DeepTaintsBounded st.heap st.nextRegion v' := by
    intro w hw r hr
    rcases hheld' w hw with rfl | hwv
    · rcases ht' r hr with hrv | ⟨hi, hrt⟩
      · exact hbase.2.2.2 v (HeldBy.refl _ _) r hrv
      · exact htb hi r hrt
    · exact hbase.2.2.2 w hwv r hr
  have hopen' : DeepOpenUnder st.heap st.regions A v' := by
    intro w hw r hr hreg
    rcases hheld' w hw with rfl | hwv
    · rcases ht' r hr with hrv | ⟨hi, hrt⟩
      · exact hopen v (HeldBy.refl _ _) r hrv hreg
      · exact htA hi r hrt hreg
    · exact hopen w hwv r hr hreg
  have hcf' : CtorFieldsOk P ext B st v' :=
    fun l o r fs w hr => hcf l o r fs w ((hreach' l).mp hr)
  have hno' : NoOnceCell st.heap v' :=
    fun l o hr => hno l o ((hreach' l).mp hr)
  have hfun' : FunOkAt P ext B st sk false (fun _ => False) v' :=
    FunOkAt_preserve_sameShape hloc (SameShapeOn.refl _ _) (RegsFuture.refl st) hfun
  have hown' : ∀ l, OwnReach P st.heap v' l ↔ OwnReach P st.heap v l := by
    intro l
    cases v with
    | imm i => rw [hshape.1 i rfl]
    | ref loc cap tv =>
      obtain ⟨tv', hEq⟩ := hshape.2 loc cap tv rfl; rw [hEq]; exact OwnReach_ref_taint
  have htree' : OwnTreeFull P st.heap v → OwnTreeFull P st.heap v' := by
    intro ht
    cases v with
    | imm i => rw [hshape.1 i rfl]; exact OwnTreeFull_imm P _ _
    | ref loc cap tv =>
      obtain ⟨tv', hEq⟩ := hshape.2 loc cap tv rfl; rw [hEq]; exact OwnTreeFull_ref_taint ht
  exact ⟨v', hrun, hloc, ValBaseOk_of_deepLive hdl' hacyc' htb', hopen', hcf', hno', hfun',
    hreach', hown', htree'⟩

/-- Local flattening of `bindAt` at class `.val` (where `conform .val v = pure v`). -/
private theorem bindAt_val_flat (P : Prog) (fuel s : Nat) (m : BinderMode) (v : Val)
    (hm : m ≠ .erased) (st : St) :
    (bindAt P fuel s m .val v).run st =
      ((if m.isUnique = true then transfer P fuel m.isBorrowed v else pure v) >>= fun v₂ =>
       (isLeaf v₂ >>= fun b =>
         if (m.isBorrowed && !b) = true then pure (addTaint s v₂) else pure v₂) >>= fun v₃ =>
       (if (m.usage == .once) = true then alloc (.once v₃ false) v₃.taint else pure v₃) >>= fun v₄ =>
       pure ⟨v₄, m⟩).run st := by
  have hmne : (m == .erased) = false := beq_false_of_ne hm
  have htail : ∀ (v₂ : Val) (st₂ : St),
      (do
        let __do_lift ← isLeaf v₂
        if (m.isBorrowed && !__do_lift) = true then do
          let v ← pure (addTaint s v₂)
          if (m.usage == .once) = true then do
            let v ← alloc (.once v false) v.taint
            pure ⟨v, m⟩
          else do
            let v ← pure v
            pure ⟨v, m⟩
        else do
          let v ← pure v₂
          if (m.usage == .once) = true then do
            let v ← alloc (.once v false) v.taint
            pure ⟨v, m⟩
          else do
            let v ← pure v
            pure ⟨v, m⟩ : M Bnd).run st₂ =
      ((isLeaf v₂ >>= fun b =>
          if (m.isBorrowed && !b) = true then pure (addTaint s v₂) else pure v₂) >>= fun v₃ =>
       (if (m.usage == .once) = true then alloc (.once v₃ false) v₃.taint else pure v₃) >>= fun v₄ =>
       pure ⟨v₄, m⟩).run st₂ := by
    intro v₂ st₂
    rw [M_bind_run, M_bind_run, M_bind_run]
    cases (isLeaf v₂).run st₂ with
    | error e => rfl
    | ok pb =>
      dsimp only
      cases (m.isBorrowed && !pb.1) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      · rw [M_bind_run, M_pure_run]
        dsimp only
        cases (m.usage == .once) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
  unfold bindAt
  simp only [hmne, Bool.false_eq_true, ↓reduceIte]
  rw [M_bind_run]
  have hconfVal : (conform .val v).run st = .ok (v, st) := rfl
  rw [hconfVal]; dsimp only
  cases hu : m.isUnique <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [M_bind_run, M_bind_run, M_pure_run]
    dsimp only
    exact htail v st
  · rw [M_bind_run, M_bind_run]
    cases (transfer P fuel m.isBorrowed v).run st with
    | error e => rfl
    | ok p₂ =>
      dsimp only
      exact htail p₂.1 p₂.2

/-- Helper: when `bindAt` binds at a `@once` mode with class `.val`, it does not transfer and
directly wraps `base` (with `SameLoc v base`) in a fresh `.once` cell at `st.heap.objs.size`. -/
theorem bindAt_once_val_sameLoc {P : Prog} {fuel s : Nat} {m : BinderMode} {v : Val} {st : St}
    (hm : m.usage = .once) (hdl : DeepLive st.heap v) :
    ∃ base st', (bindAt P fuel s m .val v).run st = .ok (⟨.ref st.heap.objs.size st.heap.nextCap base.taint, m⟩, st') ∧
      SameLoc v base ∧
      DeepLive st.heap base ∧
      (∀ r ∈ base.taint, r ∈ v.taint ∨ (m.isBorrowed = true ∧ r = s)) ∧
      st' = { st with heap := { objs := st.heap.objs.push ⟨.once base false, st.heap.nextCap⟩,
                                nextCap := st.heap.nextCap + 1 } } := by
  have hne : m ≠ .erased := by intro h; subst h; cases hm
  have hnotU : m.isUnique = false := by cases m <;> simp_all [BinderMode.usage, BinderMode.isUnique]
  rw [bindAt_val_flat P fuel s m v hne st]
  simp only [hnotU, Bool.false_eq_true, ↓reduceIte, hm, beq_self_eq_true]
  rw [M_bind_run, M_pure_run]; dsimp only
  rw [M_bind_run, M_bind_run, isLeaf_ok hdl.self.1]; dsimp only
  cases v with
  | imm i =>
    dsimp only
    by_cases hbr : m.isBorrowed = true
    · simp only [hbr, Bool.not_false, Bool.true_and, ↓reduceIte]
      rw [M_pure_run]; dsimp only
      refine ⟨.imm i, _, rfl, SameLoc.refl _, hdl, fun _ h => Or.inl h, rfl⟩
    · have hbrF : m.isBorrowed = false := Bool.eq_false_iff.mpr hbr
      simp only [hbrF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [M_pure_run]; dsimp only
      refine ⟨.imm i, _, rfl, SameLoc.refl _, hdl, fun _ h => Or.inl h, rfl⟩
  | ref loc cap t =>
    obtain ⟨o, ho, _⟩ := hdl.self.1
    simp only [ho]
    by_cases hbr : m.isBorrowed = true
    · cases hnum : o.cell.isNum with
      | true =>
        simp only [hbr, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [M_pure_run]; dsimp only
        refine ⟨.ref loc cap t, _, rfl, SameLoc.refl _, hdl, fun _ h => Or.inl h, rfl⟩
      | false =>
        simp only [hbr, Bool.not_false, Bool.and_true, ↓reduceIte]
        rw [M_pure_run]; dsimp only
        have hdlAdd : DeepLive st.heap (addTaint s (.ref loc cap t)) :=
          DeepLive_addTaint hdl (fun loc' cap' t' o' n heq ho' hc' => by
            cases heq; rw [ho] at ho'; cases ho'; simp [hc', Cell.isNum] at hnum)
        refine ⟨addTaint s (.ref loc cap t), _, rfl, SameLoc.addTaint_right s _, hdlAdd, ?_, rfl⟩
        intro r hr
        rcases mem_taint_addTaint hr with rfl | h1
        · exact Or.inr ⟨trivial, rfl⟩
        · exact Or.inl h1
    · have hbrF : m.isBorrowed = false := Bool.eq_false_iff.mpr hbr
      simp only [hbrF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [M_pure_run]; dsimp only
      refine ⟨.ref loc cap t, _, rfl, SameLoc.refl _, hdl, fun _ h => Or.inl h, rfl⟩

/-- Helper: when `bindAt` binds at a non-erased, non-once mode with class `.val`, it allocates no
cells (`st'.heap.objs.size = st.heap.objs.size`) and preserves `SameLoc v bnd.val`. -/
theorem bindAt_plain_val_shape {P : Prog} {fuel s : Nat} {m : BinderMode} {v : Val} {st st' : St}
    {bnd : Bnd}
    (her : m ≠ .erased) (hu : m.usage ≠ .once)
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v)
    (htree : m.isUnique = true → OwnTreeFull P st.heap v)
    (hconf : m.isUnique = true → m.isBorrowed = false → OpenUnder st.regions [] v)
    (hrun : (bindAt P fuel s m .val v).run st = .ok (bnd, st')) :
    st'.heap.objs.size = st.heap.objs.size ∧ SameLoc v bnd.val := by
  have huF : (m.usage == .once) = false := beq_false_of_ne hu
  rw [bindAt_val_flat P fuel s m v her st] at hrun
  have hstep : ∀ (v₂ : Val) (st₂ : St),
      DeepLive st₂.heap v₂ →
      ((isLeaf v₂ >>= fun b =>
          if (m.isBorrowed && !b) = true then pure (addTaint s v₂) else pure v₂) >>= fun v₃ =>
       (if (m.usage == .once) = true then alloc (.once v₃ false) v₃.taint else pure v₃) >>= fun v₄ =>
       pure ⟨v₄, m⟩).run st₂ = .ok (bnd, st') →
      st' = st₂ ∧ SameLoc v₂ bnd.val := by
    intro v₂ st₂ hdl₂ hr
    rw [M_bind_run, M_bind_run] at hr
    have hleafRun : ∃ b : Bool, (isLeaf v₂).run st₂ = .ok (b, st₂) :=
      ⟨_, isLeaf_ok hdl₂.self.1⟩
    obtain ⟨b, hb⟩ := hleafRun
    rw [hb] at hr; dsimp only at hr
    cases hcond : (m.isBorrowed && !b) with
    | true =>
      simp only [hcond, ↓reduceIte] at hr
      rw [M_pure_run] at hr; dsimp only at hr
      simp only [huF, Bool.false_eq_true, ↓reduceIte] at hr
      rw [M_bind_run, M_pure_run] at hr; dsimp only at hr
      rw [M_pure_run] at hr; cases hr
      exact ⟨rfl, SameLoc.addTaint_right s v₂⟩
    | false =>
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hr
      rw [M_pure_run] at hr; dsimp only at hr
      simp only [huF, Bool.false_eq_true, ↓reduceIte] at hr
      rw [M_bind_run, M_pure_run] at hr; dsimp only at hr
      rw [M_pure_run] at hr; cases hr
      exact ⟨rfl, SameLoc.refl v₂⟩
  rw [M_bind_run] at hrun
  cases hmu : m.isUnique with
  | false =>
    simp only [hmu, Bool.false_eq_true, ↓reduceIte] at hrun
    rw [M_pure_run] at hrun; dsimp only at hrun
    obtain ⟨rfl, hloc⟩ := hstep v st hdl hrun
    exact ⟨rfl, hloc⟩
  | true =>
    simp only [hmu, ↓reduceIte] at hrun
    rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := m.isBorrowed)
      hc hdl hacyc (htree hmu) (hconf hmu) with hOOF |
      ⟨vT, stT, htrT, _, _, _, _, hszT, _, _, _, hvsT, hdlT, _⟩
    · rw [hOOF] at hrun; cases hrun
    · rw [htrT] at hrun; dsimp only at hrun
      obtain ⟨rfl, hloc⟩ := hstep vT stT hdlT hrun
      exact ⟨hszT, (SameLoc.of_valSameShape hvsT).trans hloc⟩

/-- Soundness & framing of `Eval.bindAt` wrt `StOk`, `ValBaseOk`, `CtorFieldsOk`, `FunOkAt`,
`PreservesOnceShell`, `StaticStrFresh`, and `.once` wrapper footprints. -/
theorem bindAt_sound {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {fuel s : Nat} {m : BinderMode} {c : Cls} {sk : Skel}
    {onceOnly : Bool} {Foot : Nat → Prop} {v : Val}
    (hst : StOk P ext B st)
    (hs : s < st.nextRegion)
    (hbase : m ≠ .erased → ValBaseOk st v)
    (hcf : m ≠ .erased → CtorFieldsOk P ext B st v)
    (hno : m ≠ .erased → m.usage ≠ .once → NoOnceCell st.heap v)
    (hfun : m ≠ .erased → FunOkAt P ext B st sk onceOnly Foot v)
    (honceMatch : m.usage ≠ .once → onceOnly = false)
    (hFootFalse : onceOnly = false → ∀ l, ¬ Foot l)
    (hFootOk : m.usage = .once → ∀ l, Foot l → Reach st.heap v l ∧ ¬ StaticStrLoc st l)
    (htree : m.isUnique = true → OwnTreeFull P st.heap v)
    (hdisjSS : m.isUnique = true → ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l)
    (hconf : m.isUnique = true → m.isBorrowed = false → OpenUnder st.regions [] v) :
    (bindAt P fuel s m c v).run st = .error .stuck ∨
    (bindAt P fuel s m c v).run st = .error .outOfFuel ∨
    ∃ bnd st', (bindAt P fuel s m c v).run st = .ok (bnd, st') ∧
      bnd.mode = m ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧ (m.isUnique = true → ¬ OwnReach P st.heap v l))
        st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' bnd.val ∧
      CtorFieldsOk P ext B st' bnd.val ∧
      (m = .erased → bnd = ⟨.imm .irr, .erased⟩ ∧ st' = st) ∧
      (m ≠ .erased → m.usage ≠ .once →
        ClsSafe st'.heap c bnd.val ∧ NoOnceCell st'.heap bnd.val ∧
        FunOkAt P ext B st' sk false (fun _ => False) bnd.val) ∧
      (m.usage = .once →
        SpentOnceSafe st'.heap bnd.val ∧
        ∃ loc resFoot, st.heap.objs.size ≤ loc ∧
          (∀ l, resFoot l → l = loc ∨ Foot l) ∧
          (∀ l, resFoot l → Reach st'.heap bnd.val l ∧ ¬ StaticStrLoc st' l) ∧
          FunOkAt P ext B st' sk true resFoot bnd.val) ∧
      (m.isUnique = true → OwnTreeFull P st'.heap bnd.val) ∧
      (c = .leaf → bnd.val.taint = []) ∧
      (∀ rs A, (m ≠ .erased → DeepOpenUnder st.heap rs A v) →
        DeepOpenUnder st'.heap rs (if m.isBorrowed then s :: A else A) bnd.val) ∧
      (∀ l, Reach st'.heap bnd.val l → st.heap.objs.size ≤ l ∨ (m ≠ .erased ∧ Reach st.heap v l)) ∧
      (∀ l, OwnReach P st'.heap bnd.val l →
        st.heap.objs.size ≤ l ∨ (m ≠ .erased ∧ OwnReach P st.heap v l)) := by
  rcases bindAt_spec (P := P) (fuel := fuel) (s := s) (m := m) (c := c) (v := v) hst.1
    (fun h => (hbase h).1) (fun h => (hbase h).2.1) htree hconf with hStuck | hOOF |
    ⟨bnd, st', hrun, hmode, hr, hnr, hstat, hstr, hsz, hcap, hc', hoss, hpres,
      hdl', hacyc', htree', her', hcls', honce', ht', hleaf', hdou', hreach', hown'⟩
  · exact Or.inl hStuck
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hnotOnceU : m.isUnique = true → m.usage ≠ .once := by
      cases m <;> simp [BinderMode.isUnique, BinderMode.usage]
    have hneU : m.isUnique = true → m ≠ .erased := by
      cases m <;> simp [BinderMode.isUnique]
    have honceSh : PreservesOnceShell st.heap st'.heap := by
      refine PreservesOnceShell.of_oldSameShape_noOnce (S := fun l => m.isUnique = true ∧ OwnReach P st.heap v l) ?_ ?_
      · exact hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun hu hor => hnot ⟨hu, hor⟩⟩
      · intro l o tgt sp ⟨hu, hor⟩ ho hcell
        exact hno (hneU hu) (hnotOnceU hu) l o (OwnReach_toReach hor) ho tgt sp hcell
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside (S := fun l => m.isUnique = true ∧ OwnReach P st.heap v l)
        hst hstat hstr (hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun hu hor => hnot ⟨hu, hor⟩⟩)
        (fun l hss ⟨hu, hor⟩ => hdisjSS hu l hor hss)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_outside (S := fun l => m.isUnique = true ∧ OwnReach P st.heap v l)
        hst hc' hr (by rw [hnr]; exact Nat.le_refl _) hstat hstr
        (hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun hu hor => hnot ⟨hu, hor⟩⟩)
        (fun l hss ⟨hu, hor⟩ => hdisjSS hu l hor hss)
    have hrf : RegsFuture st st' := RegsFuture.same_regions (by rw [hnr]; exact Nat.le_refl _) hr
    have htb' : DeepTaintsBounded st'.heap st'.nextRegion bnd.val := by
      by_cases her : m = .erased
      · obtain ⟨hbEq, _⟩ := her' her
        rw [hbEq]; exact DeepTaintsBounded_imm _ _ _
      · have hbaseV := hbase her
        have htTop : ∀ r ∈ bnd.val.taint, r < st'.nextRegion := by
          intro r hr'
          rw [hnr]
          rcases ht' r hr' with hv | ⟨_, rfl⟩
          · exact hbaseV.2.2.2 v (HeldBy.refl _ _) r hv
          · exact hs
        by_cases hu : m.usage = .once
        · obtain ⟨base, loc, cap, hbv, _, _, ho, _, hclsBase, _, htBase⟩ := honce' hu
          by_cases hcv : c = .val
          · subst hcv
            obtain ⟨base0, st0, hrun0, hloc0, hdl0, htBase0, hst0⟩ :=
              bindAt_once_val_sameLoc (P := P) (fuel := fuel) (s := s) hu hbaseV.1
            have hEq0 := Except.ok.inj (hrun0.symm.trans hrun)
            have hbvEq : bnd.val = .ref st.heap.objs.size st.heap.nextCap base0.taint :=
              congrArg Bnd.val (congrArg Prod.fst hEq0).symm
            have hstEq : st' = { st with heap := { objs := st.heap.objs.push ⟨.once base0 false, st.heap.nextCap⟩,
                                                   nextCap := st.heap.nextCap + 1 } } :=
              (congrArg Prod.snd hEq0).symm.trans hst0
            rw [hbvEq, hstEq]
            refine DeepTaintsBounded_alloc (h := st.heap) (b := st.nextRegion) (c := .once base0 false)
              (t := base0.taint) ?_ ?_ ?_
            · intro r hr0
              rcases htBase0 r hr0 with h1 | ⟨_, rfl⟩
              · exact hbaseV.2.2.2 v (HeldBy.refl _ _) r h1
              · exact hs
            · intro w hw; simp only [Cell.vals, List.mem_singleton] at hw; subst hw; exact hdl0
            · intro w hw
              simp only [Cell.vals, List.mem_singleton] at hw
              subst hw
              exact DeepTaintsBounded_of_oldSameShape hbaseV.1 (OldSameShape.refl _) hloc0
                (fun r hr0 => by
                  rcases htBase0 r hr0 with h1 | ⟨_, rfl⟩
                  · exact hbaseV.2.2.2 v (HeldBy.refl _ _) r h1
                  · exact hs)
                hbaseV.2.2.2
          · intro w hw r hrW
            rcases hw with rfl | ⟨l, o', hreach, ho', hm'⟩
            · exact htTop r hrW
            · rw [hbv] at hreach
              cases hreach with
              | here =>
                rw [ho] at ho'; cases ho'
                simp only [Cell.vals, List.mem_singleton] at hm'
                subst hm'
                rw [hnr]
                rcases htBase r hrW with h1 | ⟨_, rfl⟩
                · exact hbaseV.2.2.2 v (HeldBy.refl _ _) r h1
                · exact hs
              | step ho1 hm1 hr2 =>
                rw [ho] at ho1; cases ho1
                simp only [Cell.vals, List.mem_singleton] at hm1
                subst hm1
                cases c with
                | val => exact absurd rfl hcv
                | irr => rw [hclsBase] at hr2; cases hr2
                | imm => obtain ⟨_, hEq⟩ := hclsBase; rw [hEq] at hr2; cases hr2
                | leaf =>
                  obtain ⟨lB, cB, oB, nB, hEq, hoB, hcB, _⟩ := hclsBase
                  rw [hEq] at hr2
                  cases hr2 with
                  | here => rw [hoB] at ho'; cases ho'; rw [hcB] at hm'; cases hm'
                  | step ho2 hm2 _ => rw [hoB] at ho2; cases ho2; rw [hcB] at hm2; cases hm2
        · by_cases hcv : c = .val
          · subst hcv
            have ⟨hszEq, _⟩ := bindAt_plain_val_shape her hu hst.1 hbaseV.1 hbaseV.2.1 htree hconf hrun
            intro w hw r hrW
            rcases hw with rfl | ⟨l, o', hreach, ho', hm'⟩
            · exact htTop r hrW
            · rcases hreach' l hreach with hge | ⟨_, hrOld⟩
              · have hlt' : l < st'.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho').1
                omega
              · obtain ⟨o₁, ho₁⟩ := hbaseV.1.exists_obj hrOld
                obtain ⟨o₂', ho₂', hcs⟩ := hoss.2 l o₁ ho₁
                rw [ho'] at ho₂'; cases ho₂'
                obtain ⟨w₁, hm₁, hvs⟩ := hcs.symm.vals_fwd hm'
                rw [hvs.taint_eq] at hrW
                rw [hnr]
                exact hbaseV.2.2.2 w₁ (Or.inr ⟨l, o₁, hrOld, ho₁, hm₁⟩) r hrW
          · have hclsB := hcls' her hu
            cases c with
            | val => exact absurd rfl hcv
            | irr => rw [hclsB]; exact DeepTaintsBounded_imm _ _ _
            | imm => obtain ⟨_, hEq⟩ := hclsB; rw [hEq]; exact DeepTaintsBounded_imm _ _ _
            | leaf =>
              obtain ⟨loc, cap, o, n, hEq, ho, hcell, _⟩ := hclsB
              rw [hEq]; exact DeepTaintsBounded_num ho hcell
    have hlocPlainVal : m ≠ .erased → m.usage ≠ .once → c = .val → SameLoc v bnd.val := by
      intro her hu hcv
      subst hcv
      exact (bindAt_plain_val_shape her hu hst.1 (hbase her).1 (hbase her).2.1 htree hconf hrun).2
    have hcf' : CtorFieldsOk P ext B st' bnd.val := by
      by_cases her : m = .erased
      · obtain ⟨hbEq, _⟩ := her' her; rw [hbEq]; exact CtorFieldsOk_imm P ext B st' .irr
      · by_cases hu : m.usage = .once
        · by_cases hcv : c = .val
          · subst hcv
            obtain ⟨base0, st0, hrun0, hloc0, hdl0, _, hst0⟩ :=
              bindAt_once_val_sameLoc (P := P) (fuel := fuel) (s := s) hu (hbase her).1
            have hEq0 := Except.ok.inj (hrun0.symm.trans hrun)
            have hbvEq : bnd.val = .ref st.heap.objs.size st.heap.nextCap base0.taint :=
              congrArg Bnd.val (congrArg Prod.fst hEq0).symm
            have hstEq : st' = { st with heap := { objs := st.heap.objs.push ⟨.once base0 false, st.heap.nextCap⟩,
                                                   nextCap := st.heap.nextCap + 1 } } :=
              (congrArg Prod.snd hEq0).symm.trans hst0
            rw [hbvEq, hstEq]
            refine CtorFieldsOk_alloc_nonCtor (by intro _ _ h; cases h) ?_
            intro w hw
            simp only [Cell.vals, List.mem_singleton] at hw; subst hw
            exact ⟨hdl0, CtorFieldsOk_of_sameShape (hbase her).1 (SameShapeOn.refl _ _) hloc0 (RegsFuture.refl st) (hcf her)⟩
          · obtain ⟨base, loc, cap, hbv, _, _, ho, _, hclsBase, _, _⟩ := honce' hu
            intro l o r' fs w hr ho' hc' _
            rw [hbv] at hr
            cases hr with
            | here => rw [ho] at ho'; cases ho'; cases hc'
            | step ho1 hm1 hr2 =>
              rw [ho] at ho1; cases ho1
              simp only [Cell.vals, List.mem_singleton] at hm1; subst hm1
              exact ClsSafe_ctorFieldsOk P ext B st' hcv (ClsSafe.of_clsOk hclsBase) l o r' fs w hr2 ho' hc' ‹_›
        · by_cases hcv : c = .val
          · exact CtorFieldsOk_of_sameShape (hbase her).1 (hoss.to_sameShapeOn _) (hlocPlainVal her hu hcv) hrf (hcf her)
          · exact ClsSafe_ctorFieldsOk P ext B st' hcv (ClsSafe.of_clsOk (hcls' her hu))
    refine ⟨bnd, st', hrun, hmode, hr, hnr, hstat, hstr, hsz, hcap, hoss, hpres, honceSh, hssf, hst',
      ValBaseOk_of_deepLive hdl' hacyc' htb', hcf', her', ?_, ?_, htree', hleaf', hdou', hreach', hown'⟩
    · intro her hu
      refine ⟨ClsSafe.of_clsOk (hcls' her hu), ?_, ?_⟩
      · by_cases hcv : c = .val
        · exact NoOnceCell_of_sameShape (hbase her).1 (hoss.to_sameShapeOn _) (hlocPlainVal her hu hcv) (hno her hu)
        · exact ClsSafe_noOnceCell hcv (ClsSafe.of_clsOk (hcls' her hu))
      · by_cases hcv : c = .val
        · have hoF := honceMatch hu
          have hfun0 := hfun her
          cases onceOnly with
          | true => cases hoF
          | false =>
            have hfunE : FunOkAt P ext B st sk false (fun _ => False) v :=
              FunOkAt_weaken_foot (fun l hl => False.elim (hFootFalse rfl l hl)) hfun0
            exact FunOkAt_preserve_sameShape (hlocPlainVal her hu hcv) (hoss.to_sameShapeOn _) hrf hfunE
        · exact ClsSafe_funOkAt P ext B st' sk hcv (ClsSafe.of_clsOk (hcls' her hu))
    · intro hu
      have her : m ≠ .erased := by intro h; subst h; cases hu
      have hssBack : ∀ l, StaticStrLoc st' l → StaticStrLoc st l :=
        StaticStrLoc_of_preserves_outside hstat hstr
          (hpres.mono fun x hx => ⟨StOk_staticStrLoc_lt hst hx, fun hmu hor => hdisjSS hmu x hor hx⟩)
      obtain ⟨base, loc, cap, hbv, _, hge, ho, _, hclsBase, _, _⟩ := honce' hu
      have hlocNotSS : ¬ StaticStrLoc st' loc := fun hss =>
        Nat.not_lt_of_ge hge (StOk_staticStrLoc_lt hst (hssBack loc hss))
      refine ⟨by rw [hbv]; exact SpentOnceSafe.of_once ho rfl rfl, ?_⟩
      by_cases hcv : c = .val
      · subst hcv
        obtain ⟨base0, st0, hrun0, hloc0, _, _, hst0⟩ :=
          bindAt_once_val_sameLoc (P := P) (fuel := fuel) (s := s) hu (hbase her).1
        have hEq0 := Except.ok.inj (hrun0.symm.trans hrun)
        have hbvEq : bnd.val = .ref st.heap.objs.size st.heap.nextCap base0.taint :=
          congrArg Bnd.val (congrArg Prod.fst hEq0).symm
        have hstEq : st' = { st with heap := { objs := st.heap.objs.push ⟨.once base0 false, st.heap.nextCap⟩,
                                               nextCap := st.heap.nextCap + 1 } } :=
          (congrArg Prod.snd hEq0).symm.trans hst0
        have hoN : st'.heap.objs[st.heap.objs.size]? = some ⟨.once base0 false, st.heap.nextCap⟩ := by
          rw [hstEq]; simp
        have hlocEq : loc = st.heap.objs.size := by
          rw [hbvEq] at hbv
          exact (congrArg (fun | .ref l _ _ => l | _ => 0) hbv).symm
        have hlocNotSS' : ¬ StaticStrLoc st' st.heap.objs.size := hlocEq ▸ hlocNotSS
        refine ⟨st.heap.objs.size, fun l => l = st.heap.objs.size ∨ Foot l, Nat.le_refl _,
          fun _ h => h, ?_, ?_⟩
        · intro l hl
          rcases hl with rfl | hft
          · exact ⟨by rw [hbvEq]; exact .here, hlocNotSS'⟩
          · obtain ⟨hrV, hnotSS⟩ := hFootOk hu l hft
            have hrB0 : Reach st.heap base0 l := Reach_of_sameShapeOn (SameShapeOn.refl _ _) hloc0 hrV
            have hrB : Reach st'.heap base0 l :=
              Reach_of_sameShapeOn (hoss.to_sameShapeOn _) (SameLoc.refl _) hrB0
            have hmem0 : base0 ∈ (Obj.mk (.once base0 false) st.heap.nextCap).cell.vals :=
              List.mem_singleton_self _
            exact ⟨by rw [hbvEq]; exact .step hoN hmem0 hrB, fun hss => hnotSS (hssBack l hss)⟩
        · have hfBase : FunOkAt P ext B st' sk true Foot base0 := by
            cases onceOnly with
            | true =>
              exact FunOkAt_preserve_sameShape hloc0 (hoss.to_sameShapeOn _) hrf (hfun her)
            | false =>
              have hfF : FunOkAt P ext B st sk false (fun _ => False) v :=
                FunOkAt_weaken_foot (fun l hl => False.elim (hFootFalse rfl l hl)) (hfun her)
              exact FunOkAt_weaken_foot (fun _ h => False.elim h)
                (FunOkAt_weaken_onceOnly (FunOkAt_preserve_sameShape hloc0 (hoss.to_sameShapeOn _) hrf hfF))
          rw [hbvEq]
          exact FunOkAt_once_wrap hoN rfl hfBase
      · refine ⟨loc, fun l => l = loc, hge, fun _ h => Or.inl h, ?_, ?_⟩
        · intro l hl; subst hl
          exact ⟨by rw [hbv]; exact .here, hlocNotSS⟩
        · rw [hbv]
          have hfBase : FunOkAt P ext B st' sk false (fun _ => False) base :=
            ClsSafe_funOkAt P ext B st' sk hcv (ClsSafe.of_clsOk hclsBase)
          exact FunOkAt_once_wrap_plain ho rfl hfBase

/-! ## 4. Remaining Operational Bridges (`transfer`, `ret`, `construct`, `proj`, `makePap`, `formClosure`) -/

/-- `transfer` lifted to `F4Inv` predicates (used by consuming `case` and `ret_sound`). -/
theorem transfer_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {toBorrowed : Bool} {v : Val} {st : St} {sk : Skel}
    (hst : StOk P ext B st)
    (hbase : ValBaseOk st v)
    (hno : NoOnceCell st.heap v)
    (hcf : CtorFieldsOk P ext B st v)
    (hfun : FunOkAt P ext B st sk false (fun _ => False) v)
    (htree : OwnTreeFull P st.heap v)
    (hconf : toBorrowed = false → OpenUnder st.regions [] v)
    (hdisjSS : ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l) :
    (transfer P fuel toBorrowed v).run st = .error .outOfFuel ∨
    ∃ v' st', (transfer P fuel toBorrowed v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      HeapSameShape st.heap st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      ValSameShape v v' ∧
      PreservesLocs (fun l => ¬ OwnReach P st.heap v l) st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' v' ∧
      NoOnceCell st'.heap v' ∧
      CtorFieldsOk P ext B st' v' ∧
      FunOkAt P ext B st' sk false (fun _ => False) v' ∧
      OwnTreeFull P st'.heap v' ∧
      (∀ rs A, DeepOpenUnder st.heap rs A v → DeepOpenUnder st'.heap rs A v') ∧
      (∀ l, Reach st'.heap v' l ↔ Reach st.heap v l) ∧
      (∀ l, OwnReach P st'.heap v' l ↔ OwnReach P st.heap v l) := by
  rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := toBorrowed)
    hst.1 hbase.1 hbase.2.1 htree hconf with hOOF |
    ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hc', hsh, hvsh, hdl', hpres⟩
  · exact Or.inl hOOF
  · right
    have hoss : OldSameShape st.heap st'.heap := OldSameShape.of_heapSameShape hsh
    have hloc : SameLoc v v' := SameLoc.of_valSameShape hvsh
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    have hpresOwn : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ OwnReach P st.heap v l) st.heap st'.heap :=
      hpres.mono fun _ h => h.2
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_oldSameShape_noOnce hpresOwn
        (fun l o₁ t₁ sp₁ hor ho₁ hc₁ => hno l o₁ (OwnReach_toReach hor) ho₁ t₁ sp₁ hc₁)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside hst hstat hstr hpresOwn (fun l hss hor => hdisjSS l hor hss)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_outside hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpresOwn
        (fun l hss hor => hdisjSS l hor hss)
    have htb' : DeepTaintsBounded st'.heap st'.nextRegion v' := by
      rw [hnr]
      exact DeepTaintsBounded_of_oldSameShape hbase.1 hoss hloc
        (fun r hrV => by
          have htEq : v'.taint = v.taint := by
            cases v <;> cases v' <;> simp [ValSameShape, Val.taint] at hvsh ⊢
            exact hvsh.2.symm
          rw [htEq] at hrV
          exact hbase.2.2.2 v (HeldBy.refl _ _) r hrV)
        hbase.2.2.2
    have hacyc' : AcyclicFrom st'.heap v' := AcyclicFrom_of_sameShape hsh hvsh hbase.2.1
    have hno' : NoOnceCell st'.heap v' := NoOnceCell_of_sameShape hbase.1 (hoss.to_sameShapeOn _) hloc hno
    have hcf' : CtorFieldsOk P ext B st' v' :=
      CtorFieldsOk_of_sameShape hbase.1 (hoss.to_sameShapeOn _) hloc hrf hcf
    have hfun' : FunOkAt P ext B st' sk false (fun _ => False) v' :=
      FunOkAt_preserve_sameShape hloc (hoss.to_sameShapeOn _) hrf hfun
    have htree' : OwnTreeFull P st'.heap v' := OwnTreeFull_of_sameShape hsh hvsh htree
    refine ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hsh, hoss, hvsh, hpres, honceSh, hssf,
      hst', ValBaseOk_of_deepLive hdl' hacyc' htb', hno', hcf', hfun', htree',
      fun rs A hdou => DeepOpenUnder_of_sameShape hsh hvsh hdou,
      fun l => (Reach_iff_sameShape hsh hvsh l).symm,
      fun l => (OwnReach_iff_sameShape hsh hvsh l).symm⟩

/-- Helper: when `c = .val`, `ret` preserves `SameLoc v v'`. -/
private theorem ret_val_sameLoc {P : Prog} {fuel s cur : Nat} {r : ResultMode} {v : Val} {st st' : St}
    {v' : Val}
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v)
    (htree : r.isUnique = true → OwnTreeFull P st.heap v)
    (hnoOpen : r = .unique → OpenUnder st.regions [] v)
    (hrun : (ret P fuel s cur r .val v).run st = .ok (v', st')) :
    SameLoc v v' := by
  unfold ret at hrun
  rw [M_bind_run] at hrun
  have hconf : (conform .val v).run st = .ok (v, st) := by
    unfold conform; rw [M_pure_run]
  rw [hconf] at hrun; dsimp only at hrun
  cases r with
  | shared =>
    dsimp only at hrun
    split at hrun
    · change Except.error _ = Except.ok _ at hrun; cases hrun
    · rw [M_pure_run] at hrun; cases hrun; exact SameLoc.refl _
  | unique =>
    dsimp only at hrun
    split at hrun
    · change Except.error _ = Except.ok _ at hrun; cases hrun
    · rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := false)
        hc hdl hacyc (htree rfl) (fun _ => hnoOpen rfl) with hOOF | ⟨v1, st1, htr, rest⟩
      · rw [hOOF] at hrun; cases hrun
      · rw [htr] at hrun; cases hrun
        exact SameLoc.of_valSameShape rest.2.2.2.2.2.2.2.2.1
  | borrowed =>
    dsimp only at hrun
    rw [M_pure_run] at hrun; cases hrun
    exact SameLoc.renameTaint_right s cur v
  | uniqueBorrowed =>
    dsimp only at hrun
    rw [M_bind_run] at hrun
    rcases transfer_spec (P := P) (fuel := fuel) (toBorrowed := true)
      hc hdl hacyc (htree rfl) (fun h => by cases h) with hOOF | ⟨v1, st1, htr, rest⟩
    · rw [hOOF] at hrun; cases hrun
    · rw [htr] at hrun; dsimp only at hrun; rw [M_pure_run] at hrun; cases hrun
      exact SameLoc.trans (SameLoc.of_valSameShape rest.2.2.2.2.2.2.2.2.1)
        (SameLoc.renameTaint_right s cur v1)

/-- `Eval.ret` lifted to `F4Inv` predicates (`StOk`, `ValBaseOk`, `NoOnceCell`, `CtorFieldsOk`,
`FunOkAt`, `PreservesOnceShell`, `StaticStrFresh`). -/
theorem ret_sound {P : Prog} {ext : ExternOracle} {B fuel s cur : Nat}
    {r : ResultMode} {c : Cls} {v : Val} {st : St} {sk : Skel}
    (hst : StOk P ext B st)
    (hbase : ValBaseOk st v)
    (hno : NoOnceCell st.heap v)
    (hcf : CtorFieldsOk P ext B st v)
    (hfun : FunOkAt P ext B st sk false (fun _ => False) v)
    (hcur : cur < st.nextRegion)
    (htree : r.isUnique = true → OwnTreeFull P st.heap v)
    (hnoS : (r = .shared ∨ r = .unique) → OpenUnder [s] [] v)
    (hnoOpen : r = .unique → OpenUnder st.regions [] v)
    (hdisjSS : r.isUnique = true → ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l) :
    (ret P fuel s cur r c v).run st = .error .stuck ∨
    (ret P fuel s cur r c v).run st = .error .outOfFuel ∨
    ∃ v' st', (ret P fuel s cur r c v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧ (r.isUnique = true → ¬ OwnReach P st.heap v l))
        st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' v' ∧
      ClsSafe st'.heap c v' ∧
      NoOnceCell st'.heap v' ∧
      CtorFieldsOk P ext B st' v' ∧
      FunOkAt P ext B st' sk false (fun _ => False) v' ∧
      (r.isUnique = true → OwnTreeFull P st'.heap v') ∧
      (∀ rs A, (r = .shared ∨ r = .unique) → DeepOpenUnder st.heap rs A v →
        DeepOpenUnder st'.heap rs A v') ∧
      (∀ rs A, (cur = 0 ∨ cur ∈ A) → DeepOpenUnder st.heap rs (s :: A) v →
        DeepOpenUnder st'.heap (rs.filter (· != s)) A v') ∧
      (∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
      (∀ l, OwnReach P st'.heap v' l → OwnReach P st.heap v l) := by
  rcases ret_spec (P := P) (fuel := fuel) (s := s) (cur := cur) (r := r) (c := c)
    hst.1 hbase.1 hbase.2.1 htree hnoS hnoOpen with hStuck | hOOF |
    ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hc', hoss, hpres, hcls', hdl', hacyc',
      htree', htSU, htB, hdouSU, _, hdouB, hreach', hown'⟩
  · exact Or.inl hStuck
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    have hpresS : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ (r.isUnique = true ∧ OwnReach P st.heap v l)) st.heap st'.heap :=
      hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun hru hor => hnot ⟨hru, hor⟩⟩
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_oldSameShape_noOnce hpresS
        (fun l o₁ t₁ sp₁ ⟨_, hor⟩ ho₁ hc₁ => hno l o₁ (OwnReach_toReach hor) ho₁ t₁ sp₁ hc₁)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside hst hstat hstr hpresS (fun l hss ⟨hru, hor⟩ => hdisjSS hru l hor hss)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_outside hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpresS
        (fun l hss ⟨hru, hor⟩ => hdisjSS hru l hor hss)
    have htTop : ∀ x ∈ v'.taint, x < st.nextRegion := by
      intro x hx
      cases r with
      | shared =>
        exact hbase.2.2.2 v (HeldBy.refl _ _) x (htSU (Or.inl rfl) x hx)
      | unique =>
        exact hbase.2.2.2 v (HeldBy.refl _ _) x (htSU (Or.inr rfl) x hx)
      | borrowed | uniqueBorrowed =>
        rcases htB rfl x hx with ⟨hxV, _⟩ | ⟨rfl, _, _⟩
        · exact hbase.2.2.2 v (HeldBy.refl _ _) x hxV
        · exact hcur
    have htb' : DeepTaintsBounded st'.heap st'.nextRegion v' := by
      rw [hnr]
      by_cases hcv : c = .val
      · subst hcv
        have hloc := ret_val_sameLoc hst.1 hbase.1 hbase.2.1 htree hnoOpen hrun
        exact DeepTaintsBounded_of_oldSameShape hbase.1 hoss hloc htTop hbase.2.2.2
      · intro w hw x hx
        rcases ClsSafe.of_clsOk hcls' with rfl | hc'
        · rcases hw with rfl | ⟨_, _, hreach, _, _⟩
          · cases hx
          · cases hreach
        · cases c with
          | val => exact absurd rfl hcv
          | irr =>
            rw [hc'] at hw
            rcases hw with rfl | ⟨_, _, hreach, _, _⟩
            · cases hx
            · cases hreach
          | imm =>
            obtain ⟨_, heq⟩ := hc'; rw [heq] at hw
            rcases hw with rfl | ⟨_, _, hreach, _, _⟩
            · cases hx
            · cases hreach
          | leaf =>
            obtain ⟨loc, cap, o, n, heq, ho, hnum, _⟩ := hc'; rw [heq] at hw
            rcases hw with rfl | ⟨l, o', hreach, ho', hm'⟩
            · cases hx
            · cases hreach with
              | here => rw [ho] at ho'; cases ho'; rw [hnum] at hm'; cases hm'
              | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hnum] at hm1; cases hm1
    have hno' : NoOnceCell st'.heap v' := by
      by_cases hcv : c = .val
      · subst hcv
        exact NoOnceCell_of_sameShape hbase.1 (hoss.to_sameShapeOn _)
          (ret_val_sameLoc hst.1 hbase.1 hbase.2.1 htree hnoOpen hrun) hno
      · exact ClsSafe_noOnceCell hcv (ClsSafe.of_clsOk hcls')
    have hcf' : CtorFieldsOk P ext B st' v' := by
      by_cases hcv : c = .val
      · subst hcv
        exact CtorFieldsOk_of_sameShape hbase.1 (hoss.to_sameShapeOn _)
          (ret_val_sameLoc hst.1 hbase.1 hbase.2.1 htree hnoOpen hrun) hrf hcf
      · exact ClsSafe_ctorFieldsOk P ext B st' hcv (ClsSafe.of_clsOk hcls')
    have hfun' : FunOkAt P ext B st' sk false (fun _ => False) v' := by
      by_cases hcv : c = .val
      · subst hcv
        exact FunOkAt_preserve_sameShape
          (ret_val_sameLoc hst.1 hbase.1 hbase.2.1 htree hnoOpen hrun) (hoss.to_sameShapeOn _) hrf hfun
      · exact ClsSafe_funOkAt P ext B st' sk hcv (ClsSafe.of_clsOk hcls')
    exact ⟨v', st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hoss, hpres, honceSh, hssf, hst',
      ValBaseOk_of_deepLive hdl' hacyc' htb', ClsSafe.of_clsOk hcls', hno', hcf', hfun', htree',
      hdouSU, hdouB, hreach', hown'⟩

/-- Auxiliary soundness for `Ops.constructLoop` lifted to `F4Inv` predicates (`StOk`, `ValBaseOk`,
`NoOnceCell`, `CtorFieldsOk`, `FunOkAt .unknown false False`). -/
theorem constructLoop_sound {P : Prog} {ext : ExternOracle} {B : Nat}
    (xs : List (Field × Val)) (out : Array Val) (st : St)
    (hst : StOk P ext B st)
    (hout : ∀ w ∈ out.toList,
      ValBaseOk st w ∧ NoOnceCell st.heap w ∧ CtorFieldsOk P ext B st w ∧
      FunOkAt P ext B st .unknown false (fun _ => False) w)
    (hxs : ∀ fv ∈ xs, fv.1.kept = true →
      ValBaseOk st fv.2 ∧ NoOnceCell st.heap fv.2 ∧ CtorFieldsOk P ext B st fv.2 ∧
      FunOkAt P ext B st .unknown false (fun _ => False) fv.2) :
    (constructLoop xs out).run st = .error .stuck ∨
    ∃ out' st', (constructLoop xs out).run st = .ok (out', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      StOk P ext B st' ∧
      (∀ w ∈ out'.toList,
        ValBaseOk st' w ∧ NoOnceCell st'.heap w ∧ CtorFieldsOk P ext B st' w ∧
        FunOkAt P ext B st' .unknown false (fun _ => False) w) := by
  induction xs generalizing out st with
  | nil =>
    right
    exact ⟨out, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hst, hout⟩
  | cons fv rest ih =>
    rcases fv with ⟨f, v⟩
    have hstep1 :
        (if f.kept = true then conform f.cls v else pure (.imm .irr)).run st = .error .stuck ∨
        ∃ v' st₁,
          (if f.kept = true then conform f.cls v else pure (.imm .irr)).run st = .ok (v', st₁) ∧
          st₁.regions = st.regions ∧ st₁.nextRegion = st.nextRegion ∧
          st₁.statics = st.statics ∧ st₁.strs = st.strs ∧
          st.heap.objs.size ≤ st₁.heap.objs.size ∧ st.heap.nextCap ≤ st₁.heap.nextCap ∧
          PreservesLocs (fun l => l < st.heap.objs.size) st.heap st₁.heap ∧
          StOk P ext B st₁ ∧
          ValBaseOk st₁ v' ∧ NoOnceCell st₁.heap v' ∧ CtorFieldsOk P ext B st₁ v' ∧
          FunOkAt P ext B st₁ .unknown false (fun _ => False) v' := by
      cases hfk : f.kept with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        right
        exact ⟨.imm .irr, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
          PreservesLocs.refl _ _, hst, ValBaseOk_imm st .irr, NoOnceCell_imm _ _,
          ClsSafe_ctorFieldsOk P ext B st (by decide : Cls.irr ≠ .val) (ClsSafe.irr _ _),
          FunOkAt_imm_irr ..⟩
      | true =>
        simp only [↓reduceIte]
        obtain ⟨hbv, hnov, hcfv, hfunv⟩ := hxs (f, v) (List.mem_cons_self ..) hfk
        rcases conform_sound (P := P) (ext := ext) (B := B) (c := f.cls) (sk := .unknown)
          (onceOnly := false) (Foot := fun _ => False)
          hst hbv hcfv (fun _ => hnov) hfunv with hSt | ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁,
            hsz₁, hcap₁, hpres₁, _, _, hstOk₁, hbv', _, hcf', _, _, _, _, hno', _, _, hfun'⟩
        · exact Or.inl hSt
        · exact Or.inr ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁,
            hstOk₁, hbv', hno' rfl, hcf', hfun'⟩
    unfold constructLoop
    rw [M_bind_run]
    rcases hstep1 with hSt | ⟨v', st₁, hrun₁, hr₁, hnr₁, hst₁, hstr₁, hsz₁, hcap₁, hpres₁,
        hstOk₁, hbv', hno', hcf', hfun'⟩
    · left; rw [hSt]
    · rw [hrun₁]; dsimp only
      have hrf₁ : RegsFuture st st₁ := RegsFuture.same_regions (hnr₁ ▸ Nat.le_refl _) hr₁
      have hlift : ∀ w,
          ValBaseOk st w ∧ NoOnceCell st.heap w ∧ CtorFieldsOk P ext B st w ∧
          FunOkAt P ext B st .unknown false (fun _ => False) w →
          ValBaseOk st₁ w ∧ NoOnceCell st₁.heap w ∧ CtorFieldsOk P ext B st₁ w ∧
          FunOkAt P ext B st₁ .unknown false (fun _ => False) w := by
        intro w ⟨hbw, hnow, hcfw, hfunw⟩
        have hpw : PreservesLocs (Reach st.heap w) st.heap st₁.heap :=
          hpres₁.mono fun l hr => hbw.1.reach_lt_size hr
        exact ⟨ValBaseOk_congr hpw (hnr₁ ▸ Nat.le_refl _) hbw,
          NoOnceCell_congr hbw.1 hpw hnow,
          CtorFieldsOk_congr hbw.1 hpw hrf₁ hcfw,
          FunOkAt_preserve_locs hpw hrf₁ hfunw⟩
      have hout₁ : ∀ w ∈ (out.push v').toList,
          ValBaseOk st₁ w ∧ NoOnceCell st₁.heap w ∧ CtorFieldsOk P ext B st₁ w ∧
          FunOkAt P ext B st₁ .unknown false (fun _ => False) w := by
        intro w hw
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact hlift w (hout w hw)
        · exact ⟨hbv', hno', hcf', hfun'⟩
      have hxs₁ : ∀ fv' ∈ rest, fv'.1.kept = true →
          ValBaseOk st₁ fv'.2 ∧ NoOnceCell st₁.heap fv'.2 ∧ CtorFieldsOk P ext B st₁ fv'.2 ∧
          FunOkAt P ext B st₁ .unknown false (fun _ => False) fv'.2 :=
        fun fv' hmem hfk => hlift fv'.2 (hxs fv' (List.mem_cons_of_mem _ hmem) hfk)
      rcases ih (out.push v') st₁ hstOk₁ hout₁ hxs₁ with hSt2 |
        ⟨out', st₂, hrun₂, hr₂, hnr₂, hst₂, hstr₂, hsz₂, hcap₂, hpres₂, hstOk₂, hout₂⟩
      · exact Or.inl hSt2
      · right
        exact ⟨out', st₂, hrun₂, hr₂.trans hr₁, hnr₂.trans hnr₁, hst₂.trans hst₁,
          hstr₂.trans hstr₁, Nat.le_trans hsz₁ hsz₂, Nat.le_trans hcap₁ hcap₂,
          PreservesLocs.trans hpres₁ (hpres₂.mono fun l hl => Nat.lt_of_lt_of_le hl hsz₁),
          hstOk₂, hout₂⟩

/-- `Eval.construct` lifted to `F4Inv` predicates (`StOk`, `ValBaseOk`, `NoOnceCell`,
`CtorFieldsOk`, `FunOkAt .unknown false False`, `PreservesOnceShell`, `StaticStrFresh`). -/
theorem construct_sound {P : Prog} {ext : ExternOracle} {B : Nat}
    {r : Ref} {fields : Array Field} {vs : List Val} {c : Cls} {st : St}
    (hst : StOk P ext B st)
    (hvs : ∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
      ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext B st v ∧
      FunOkAt P ext B st .unknown false (fun _ => False) v) :
    (construct r fields vs c).run st = .error .stuck ∨
    ∃ rv st', (construct r fields vs c).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      FunOkAt P ext B st' .unknown false (fun _ => False) rv ∧
      (∀ rs A,
        (∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
          DeepOpenUnder st.heap rs A v) →
        DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l →
        st.heap.objs.size ≤ l ∨
        ∃ (i : Nat) (f : Field) (v : Val), fields[i]? = some f ∧ vs[i]? = some v ∧ f.kept = true ∧ Reach st.heap v l) ∧
      (rv = .imm (.con r) ∨
       ((c = .imm ∨ c = .leaf) ∧ ClsSafe st'.heap c rv) ∨
       (c = .val ∧ ClsSafe st'.heap c rv) ∨
       (∃ loc cap out,
         rv = .ref loc cap (taints out.toList) ∧
         loc = st'.heap.objs.size - 1 ∧
         st.heap.objs.size ≤ loc ∧
         st'.heap.objs[loc]? = some ⟨.ctor r out, cap⟩ ∧
         out.size = min fields.size vs.length)) ∧
      ((∃ ind tag nP, P.ctorOf? r = some (ind, tag, nP, fields)) →
       (∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
         f.fmode = .inherited → OwnTreeFull P st.heap v) →
       (∀ (i j : Nat) (fi : Field) (vi : Val) (fj : Field) (vj : Val), i ≠ j →
         fields[i]? = some fi → vs[i]? = some vi →
         fields[j]? = some fj → vs[j]? = some vj →
         fi.kept = true → fj.kept = true → fi.fmode = .inherited →
         ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) →
       OwnTreeFull P st'.heap rv) := by
  have hvsDL : ∀ (i : Nat) (f : Field) (v : Val), fields[i]? = some f → vs[i]? = some v → f.kept = true →
      DeepLive st.heap v ∧ AcyclicFrom st.heap v :=
    fun i f v hf hv hfk => ⟨(hvs i f v hf hv hfk).1.1, (hvs i f v hf hv hfk).1.2.1⟩
  rcases construct_spec (P := P) (r := r) (fields := fields) (vs := vs) (c := c) hst.1 hvsDL with
    hSt | ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, hc', hoss, hdl', hacyc',
      hdou', hreach', _, hshape, htree'⟩
  · exact Or.inl hSt
  · right
    have hxsZip : ∀ fv ∈ fields.toList.zip vs, fv.1.kept = true →
        ValBaseOk st fv.2 ∧ NoOnceCell st.heap fv.2 ∧ CtorFieldsOk P ext B st fv.2 ∧
        FunOkAt P ext B st .unknown false (fun _ => False) fv.2 := by
      intro fv hmem hfk
      obtain ⟨k, hk, hEq⟩ := List.getElem_of_mem hmem
      have hk' : k < min fields.size vs.length := by simpa [List.length_zip] using hk
      have hkf : k < fields.size := Nat.lt_of_lt_of_le hk' (Nat.min_le_left ..)
      have hkv : k < vs.length := Nat.lt_of_lt_of_le hk' (Nat.min_le_right ..)
      have h1 : fields[k]? = some fv.1 := by
        rw [Array.getElem?_eq_getElem hkf]
        have := congrArg Prod.fst hEq; simpa [List.getElem_zip] using this
      have h2 : vs[k]? = some fv.2 := by
        rw [List.getElem?_eq_getElem hkv]
        have := congrArg Prod.snd hEq; simpa [List.getElem_zip] using this
      exact hvs k fv.1 fv.2 h1 h2 hfk
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_oldSameShape_noOnce (S := fun _ => False)
        (hpres.mono fun _ h => h.1) (fun _ _ _ _ h => False.elim h)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside (S := fun _ => False) hst hstat hstr
        (hpres.mono fun _ h => h.1) (fun _ _ h => h)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_old hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpres
    have hbaseNoCfFun :
        ValBaseOk st' rv ∧ NoOnceCell st'.heap rv ∧ CtorFieldsOk P ext B st' rv ∧
        FunOkAt P ext B st' .unknown false (fun _ => False) rv := by
      rcases hshape with rfl | ⟨hcIL, hclsIL⟩ | ⟨loc, cap, out, hrvEq, _, _, hoNew, _⟩
      · exact ⟨ValBaseOk_imm st' (.con r), NoOnceCell_imm _ _,
          ClsSafe_ctorFieldsOk P ext B st' (by decide : Cls.imm ≠ .val) (ClsSafe.of_clsOk ⟨.con r, rfl⟩),
          FunOkAt_nonCallable_imm P ext B st' .unknown (by intro h; cases h)⟩
      · have hne : c ≠ .val := by rcases hcIL with rfl | rfl <;> decide
        have hcs := ClsSafe.of_clsOk hclsIL
        have htb : DeepTaintsBounded st'.heap st'.nextRegion rv := by
          intro w hw x hx
          cases c with
          | val => exact absurd rfl hne
          | irr =>
            rw [hclsIL] at hw
            rcases hw with rfl | ⟨_, _, hre, _, _⟩
            · cases hx
            · cases hre
          | imm =>
            obtain ⟨_, hEq⟩ := hclsIL
            rw [hEq] at hw
            rcases hw with rfl | ⟨_, _, hre, _, _⟩
            · cases hx
            · cases hre
          | leaf =>
            obtain ⟨l0, c0, o0, n0, hEq, ho0, hnum0, _⟩ := hclsIL
            rw [hEq] at hw
            rcases hw with rfl | ⟨l, o', hre, ho', hm'⟩
            · cases hx
            · cases hre with
              | here => rw [ho0] at ho'; cases ho'; rw [hnum0] at hm'; cases hm'
              | step ho1 hm1 _ => rw [ho0] at ho1; cases ho1; rw [hnum0] at hm1; cases hm1
        exact ⟨ValBaseOk_of_deepLive hdl' hacyc' htb, ClsSafe_noOnceCell hne hcs,
          ClsSafe_ctorFieldsOk P ext B st' hne hcs, ClsSafe_funOkAt P ext B st' .unknown hne hcs⟩
      · unfold construct at hrun
        rw [M_bind_run] at hrun
        erw [forIn_list_constructLoop] at hrun
        rcases constructLoop_sound (P := P) (ext := ext) (B := B) (fields.toList.zip vs) #[] st hst
          (fun _ hm => by simp at hm) hxsZip with hStL |
          ⟨outL, stL, hrunL, _, _, _, _, _, _, _, hstOkL, houtL⟩
        · rw [hStL] at hrun; cases hrun
        · rw [hrunL] at hrun; dsimp only at hrun
          have hkeptNE : ¬ (((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty = true) := by
            intro he; simp only [he, ↓reduceIte] at hrun; rw [M_pure_run] at hrun
            cases hrun; cases hrvEq
          have hnotWrap : ¬ (((c == .imm || c == .leaf) &&
              ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1) = true) := by
            intro hw
            simp only [hkeptNE, Bool.false_eq_true, ↓reduceIte, hw] at hrun
            cases hk0 : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2))[0]? with
            | none =>
              simp only [hk0] at hrun
              change Except.error _ = Except.ok _ at hrun; cases hrun
            | some idx =>
              cases ho0 : outL[idx]? with
              | none =>
                simp only [hk0, ho0] at hrun
                change Except.error _ = Except.ok _ at hrun; cases hrun
              | some v0 =>
                simp only [hk0, ho0] at hrun
                have hcIL : c = .imm ∨ c = .leaf := by
                  cases hc : c
                  · rw [hc] at hw; simp only [Bool.and_eq_true, Bool.or_eq_true] at hw
                    rcases hw.1 with h | h <;> cases h
                  · exact Or.inl rfl
                  · exact Or.inr rfl
                  · rw [hc] at hw; simp only [Bool.and_eq_true, Bool.or_eq_true] at hw
                    rcases hw.1 with h | h <;> cases h
                have hbw0 := (houtL v0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? ho0))).1
                rcases conform_spec_full (P := P) hstOkL.1 hbw0.1 hbw0.2.1 (c := c) with hStC |
                  ⟨vC, stC, hrunC, _, _, _, _, _, _, _, _, _, hclsC, _, _, _, _, _, _⟩
                · rw [hStC] at hrun; cases hrun
                · rw [hrunC] at hrun; cases hrun
                  rcases hcIL with rfl | rfl
                  · obtain ⟨_, hEq⟩ := hclsC; rw [hEq] at hrvEq; cases hrvEq
                  · obtain ⟨lC, capC, oC, nC, hEq, hoC, hnumC, _⟩ := hclsC
                    have hlEq : lC = loc := congrArg (fun | .ref l _ _ => l | _ => 0) (hEq.symm.trans hrvEq)
                    subst hlEq
                    rw [hoC] at hoNew; cases hoNew; cases hnumC
          simp only [hkeptNE, Bool.false_eq_true, ↓reduceIte, hnotWrap] at hrun
          unfold alloc at hrun
          simp only [StateT.run, get, set, MonadStateOf.set, pure, Pure.pure, bind, Bind.bind] at hrun
          cases hrun
          have hlocL : loc = stL.heap.objs.size := by
            have := congrArg (fun | .ref l _ _ => l | _ => 0) hrvEq
            exact this.symm
          have houtEq : out = outL := by
            have : stL.heap.objs.size = loc := hlocL.symm
            rw [← this] at hoNew
            simp only [Array.getElem?_push_size, Option.some.injEq, Obj.mk.injEq, Cell.ctor.injEq] at hoNew
            exact hoNew.1.2.symm
          subst houtEq
          have htb : DeepTaintsBounded
              { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩,
                nextCap := stL.heap.nextCap + 1 } stL.nextRegion
              (.ref stL.heap.objs.size stL.heap.nextCap (taints out.toList)) := by
            refine DeepTaintsBounded_alloc (h := stL.heap) (b := stL.nextRegion) (c := .ctor r out)
              (t := taints out.toList) ?_ ?_ ?_
            · intro x hx
              obtain ⟨w, hw, hxw⟩ := mem_taints.mp hx
              exact (houtL w hw).1.2.2.2 w (HeldBy.refl _ _) x hxw
            · intro w hw
              exact (houtL w hw).1.1
            · intro w hw
              exact (houtL w hw).1.2.2.2
          have hnoC : NoOnceCell
              { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩,
                nextCap := stL.heap.nextCap + 1 }
              (.ref stL.heap.objs.size stL.heap.nextCap (taints out.toList)) :=
            NoOnceCell_alloc_nonOnce (by intro t sp h; cases h)
              (fun w hw => ⟨(houtL w hw).1.1, (houtL w hw).2.1⟩)
          have hcfC : CtorFieldsOk P ext B
              { stL with heap := { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩,
                                   nextCap := stL.heap.nextCap + 1 } }
              (.ref stL.heap.objs.size stL.heap.nextCap (taints out.toList)) := by
            refine CtorFieldsOk_alloc_ctor (P := P) (ext := ext) (B := B) (st := stL)
              (r := r) (fs := out) (t := taints out.toList) ?_
            intro w hw
            exact ⟨(houtL w hw).1.1, (houtL w hw).2.1, (houtL w hw).2.2.2, (houtL w hw).2.2.1⟩
          have hfunC : FunOkAt P ext B
              { stL with heap := { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩,
                                   nextCap := stL.heap.nextCap + 1 } }
              .unknown false (fun _ => False)
              (.ref stL.heap.objs.size stL.heap.nextCap (taints out.toList)) :=
            FunOkAt_nonCallable_ref P ext B
              { stL with heap := { objs := stL.heap.objs.push ⟨.ctor r out, stL.heap.nextCap⟩,
                                   nextCap := stL.heap.nextCap + 1 } }
              .unknown
              (o₀ := ⟨.ctor r out, stL.heap.nextCap⟩)
              (by simp) trivial
          exact ⟨ValBaseOk_of_deepLive hdl' hacyc' htb, hnoC, hcfC, hfunC⟩
    refine ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, hoss, honceSh, hssf, hst',
      hbaseNoCfFun.1, hbaseNoCfFun.2.1, hbaseNoCfFun.2.2.1, hbaseNoCfFun.2.2.2,
      hdou', hreach', ?_, htree'⟩
    rcases hshape with h1 | ⟨hIL, hclsIL⟩ | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨hIL, ClsSafe.of_clsOk hclsIL⟩)
    · exact Or.inr (Or.inr (Or.inr h3))

/-- The runtime projection tail (`evalS` for `.proj s i e c` after evaluating `e`). -/
def projTail (P : Prog) (s : Ref) (i : Nat) (v : Val) (c : Cls) : M Val := do
  live v
  let cs := P.ctorsOf s
  let some ctor := cs[0]? | stuckM
  let some (_, _, _, fields) := P.ctorOf? ctor | stuckM
  let some f := fields[i]? | stuckM
  if f.mode == .erased then violate .erasedRead
  if f.cls == .irr then return .imm .irr
  let asWrapper : M Val :=
    if P.wrapperField? s == some i then conform c v else stuckM
  match v with
  | .ref loc _ tv => do
    match (← obj loc).cell with
    | .ctor r' fs =>
      unless r' == ctor do stuckM
      let some fv := fs[i]? | stuckM
      conform c (← readOut (f.fmode == .inherited) tv fv)
    | .num _ => asWrapper
    | _ => stuckM
  | .imm _ => asWrapper

/-- Soundness and framing of `projTail`, matching `Eval.eval`/`EvalS.evalS` for `.proj`. -/
theorem proj_sound {P : Prog} {ext : ExternOracle} {B : Nat}
    {s : Ref} {i : Nat} {v : Val} {c : Cls} {st : St} {sk : Skel} {A : List Nat}
    (hst : StOk P ext B st)
    (hbase : ValBaseOk st v)
    (hno : NoOnceCell st.heap v)
    (hcf : CtorFieldsOk P ext B st v)
    (hdou : DeepOpenUnder st.heap st.regions A v)
    (hnotEr : ∀ ctor ind ci nP fs f,
      (P.ctorsOf s)[0]? = some ctor →
      P.ctorOf? ctor = some (ind, ci, nP, fs) →
      fs[i]? = some f → f.mode ≠ .erased)
    (hskNonCtor : (v = .imm .irr ∨ (∃ im, v = .imm im) ∨
      ∃ loc cap o n, v = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n) →
      FunOkAt P ext B st sk false (fun _ => False) v)
    (hskCtor : sk = .unknown ∨ c ≠ .val) :
    (projTail P s i v c).run st = .error .stuck ∨
    ∃ rv st', (projTail P s i v c).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      ValBaseOk st' rv ∧
      ClsSafe st'.heap c rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      FunOkAt P ext B st' sk false (fun _ => False) rv ∧
      DeepOpenUnder st'.heap st'.regions (if c == .val then A else []) rv ∧
      (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) := by
  unfold projTail
  rw [M_bind_run, live_ok hbase.1.self.1]; dsimp only
  cases hcs0 : (P.ctorsOf s)[0]? with
  | none => left; rfl
  | some ctor =>
    simp only
    cases hco : P.ctorOf? ctor with
    | none => left; rfl
    | some q =>
      rcases q with ⟨ind, ci, nP, fields⟩
      simp only
      cases hf : fields[i]? with
      | none => left; rfl
      | some f =>
        simp only
        have hneEr : (f.mode == .erased) = false :=
          beq_false_of_ne (hnotEr ctor ind ci nP fields f hcs0 hco hf)
        simp only [hneEr, Bool.false_eq_true, ↓reduceIte]
        cases hfirr : (f.cls == .irr) with
        | true =>
          simp only [↓reduceIte]
          rw [M_pure_run]
          right
          refine ⟨.imm .irr, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
            PreservesLocs.refl _ _, OldSameShape.refl _, PreservesOnceShell.refl _,
            StaticStrFresh.refl _, hst, ValBaseOk_imm st .irr, ClsSafe.irr _ _,
            NoOnceCell_imm _ _, ClsSafe_ctorFieldsOk P ext B st (by decide : Cls.irr ≠ .val) (ClsSafe.irr _ _),
            FunOkAt_imm_irr P ext B st sk, DeepOpenUnder_imm st.heap st.regions _ .irr, fun _ hr => (by cases hr)⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have handleWrapper :
              (v = .imm .irr ∨ (∃ im, v = .imm im) ∨
                ∃ loc cap o n, v = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧ o.cell = .num n) →
              (if P.wrapperField? s == some i then conform c v else stuckM).run st = .error .stuck ∨
              ∃ rv st', (if P.wrapperField? s == some i then conform c v else stuckM).run st = .ok (rv, st') ∧
                st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
                st'.statics = st.statics ∧ st'.strs = st.strs ∧
                st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
                PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
                OldSameShape st.heap st'.heap ∧
                PreservesOnceShell st.heap st'.heap ∧
                StaticStrFresh st st' ∧
                StOk P ext B st' ∧
                ValBaseOk st' rv ∧ ClsSafe st'.heap c rv ∧ NoOnceCell st'.heap rv ∧
                CtorFieldsOk P ext B st' rv ∧
                FunOkAt P ext B st' sk false (fun _ => False) rv ∧
                DeepOpenUnder st'.heap st'.regions (if c == .val then A else []) rv ∧
                (∀ l, Reach st'.heap rv l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) := by
            intro hwrapV
            split
            · rcases conform_sound (P := P) (ext := ext) (B := B) (c := c) (sk := sk)
                (onceOnly := false) (Foot := fun _ => False)
                hst hbase hcf (fun _ => hno) (hskNonCtor hwrapV) with hSt |
                ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf,
                  hst', hbv', hcls', hcf', hdou', hreach', _, _, hno', _, _, hfun'⟩
              · exact Or.inl hSt
              · right
                have hoss : OldSameShape st.heap st'.heap := OldSameShape.of_preserves_old hsz hpres
                refine ⟨rv, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hpres, hoss, honceSh,
                  hssf, hst', hbv', hcls', hno' rfl, hcf', hfun', ?_, hreach'⟩
                by_cases hcv : c = .val
                · subst hcv
                  have : (Cls.val == Cls.val) = true := rfl
                  simp only [this, ↓reduceIte]
                  rw [hr]; exact hdou' st.regions A hdou
                · have hcfB : (c == .val) = false := by
                    cases hc : c <;> try rfl
                    exact absurd hc hcv
                  simp only [hcfB, Bool.false_eq_true, ↓reduceIte]
                  exact ClsSafe_deepOpenUnder_nil hcv hcls'
            · left; rfl
          cases v with
          | imm im =>
            exact handleWrapper (Or.inr (Or.inl ⟨im, rfl⟩))
          | ref loc cap tv =>
            rw [M_bind_run]
            obtain ⟨o, ho, _⟩ := hbase.1.self.1
            rw [obj_ok ho]; dsimp only
            cases hcell : o.cell with
            | ctor r' fs =>
              cases hreq : (r' == ctor) with
              | false =>
                left; simp only [hreq, Bool.false_eq_true, ↓reduceIte]
                rw [M_bind_run]; rfl
              | true =>
                simp only [hreq, ↓reduceIte]
                cases hfsi : fs[i]? with
                | none => left; rfl
                | some fv =>
                  simp only
                  have hfvMem : fv ∈ fs.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfsi)
                  have hfvVals : fv ∈ o.cell.vals := by rw [hcell]; exact hfvMem
                  have hfvHeld : HeldBy st.heap (.ref loc cap tv) fv := HeldBy_of_mem_vals ho hfvVals
                  have hbvF : ValBaseOk st fv := hbase.sub hfvHeld
                  have hnoF : NoOnceCell st.heap fv := (hcf loc o r' fs fv .here ho hcell hfvMem).1
                  have hfunF : FunOkAt P ext B st .unknown false (fun _ => False) fv :=
                    (hcf loc o r' fs fv .here ho hcell hfvMem).2
                  have hcfF : CtorFieldsOk P ext B st fv := fun l' o' r'' fs' w' hr' =>
                    hcf l' o' r'' fs' w' (.step ho hfvVals hr')
                  have hdouF : DeepOpenUnder st.heap st.regions A fv := hdou.sub hfvHeld
                  rw [M_bind_run]
                  obtain ⟨fv', hrunR, _, hbvR, hdouR, hcfR, hnoR, hfunR, hreachR, _, _⟩ :=
                    readOut_sound (P := P) (ext := ext) (B := B)
                      (inherit := f.fmode == .inherited) (t := tv) (sk := .unknown) (A := A)
                      hbvF (fun _ x hx => hbase.2.2.2 _ (HeldBy.refl _ _) x hx)
                      (fun _ x hx hopen => hdou.self x hx hopen) hdouF hcfF hnoF hfunF
                  rw [hrunR]; dsimp only
                  rcases conform_sound (P := P) (ext := ext) (B := B) (c := c) (sk := .unknown)
                    (onceOnly := false) (Foot := fun _ => False)
                    hst hbvR hcfR (fun _ => hnoR) hfunR with hSt |
                    ⟨rv, st', hrunC, hr, hnr, hstat, hstr, hsz, hcap, hpres, honceSh, hssf,
                      hst', hbv', hcls', hcf', hdou', hreach', _, _, hno', _, _, hfun'⟩
                  · exact Or.inl hSt
                  · right
                    have hoss : OldSameShape st.heap st'.heap := OldSameShape.of_preserves_old hsz hpres
                    refine ⟨rv, st', hrunC, hr, hnr, hstat, hstr, hsz, hcap, hpres, hoss, honceSh,
                      hssf, hst', hbv', hcls', hno' rfl, hcf', ?_, ?_, ?_⟩
                    · rcases hskCtor with rfl | hne
                      · exact hfun'
                      · exact ClsSafe_funOkAt P ext B st' sk hne hcls'
                    · by_cases hcv : c = .val
                      · subst hcv
                        have : (Cls.val == Cls.val) = true := rfl
                        simp only [this, ↓reduceIte]
                        rw [hr]; exact hdou' st.regions A hdouR
                      · have hcfB : (c == .val) = false := by
                          cases hc : c <;> try rfl
                          exact absurd hc hcv
                        simp only [hcfB, Bool.false_eq_true, ↓reduceIte]
                        exact ClsSafe_deepOpenUnder_nil hcv hcls'
                    · intro l hrl
                      rcases hreach' l hrl with hge | hrR
                      · exact Or.inl hge
                      · exact Or.inr (.step ho hfvVals ((hreachR l).mp hrR))
            | num n =>
              have htv : tv = [] := hbase.1.self.2 o n ho hcell
              subst htv
              exact handleWrapper (Or.inr (Or.inr ⟨loc, cap, o, n, rfl, ho, hcell⟩))
            | str _ => left; rfl
            | clo _ _ _ _ _ _ => left; rfl
            | pap _ _ => left; rfl
            | once _ _ => left; rfl

/-- `Eval.makePap` lifted to `F4Inv` predicates (`StOk`, `ValBaseOk`, `NoOnceCell`, `CtorFieldsOk`,
`PreservesOnceShell`, `StaticStrFresh`, and per-arg `FunOkAt`/`ValBaseOk`/`NoOnceCell`/`CtorFieldsOk`). -/
theorem makePap_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {r : Ref} {params : Array Param} {vs : List Val} {st : St}
    (hst : StOk P ext B st)
    (hvs : ∀ v ∈ vs, ValBaseOk st v ∧ NoOnceCell st.heap v ∧ CtorFieldsOk P ext B st v)
    (huniq : ∀ (i : Nat) (v : Val), vs[i]? = some v →
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      OwnTreeFull P st.heap v ∧
      (((params[i]?.map Param.mode).getD BinderMode.many).isBorrowed = false → OpenUnder st.regions [] v) ∧
      ∀ l, OwnReach P st.heap v l → ¬ StaticStrLoc st l)
    (hdisj : ∀ (i j : Nat) (vi vj : Val), i ≠ j →
      vs[i]? = some vi → vs[j]? = some vj →
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true →
      ∀ l, OwnReach P st.heap vi l → ¬ Reach st.heap vj l) :
    (makePap P fuel r params vs).run st = .error .outOfFuel ∨
    ∃ rv out st', (makePap P fuel r params vs).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size + 1 ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧
          ∀ (i : Nat) (v : Val), vs[i]? = some v →
            ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true → ¬ OwnReach P st.heap v l)
        st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      (∃ cap, rv = .ref st.heap.objs.size cap (taints out.toList) ∧
        st'.heap.objs[st.heap.objs.size]? = some ⟨.pap r out, cap⟩) ∧
      out.size = vs.length ∧
      (∀ (i : Nat) (v : Val), vs[i]? = some v →
        ∃ w, out[i]? = some w ∧ ValSameShape v w ∧ ValBaseOk st' w ∧
          NoOnceCell st'.heap w ∧ CtorFieldsOk P ext B st' w ∧
          (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot v →
            FunOkAt P ext B st' sk onceOnly Foot w)) ∧
      ValBaseOk st' rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      (∀ rs A, (∀ v ∈ vs, DeepOpenUnder st.heap rs A v) → DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l → l = st.heap.objs.size ∨ ∃ v ∈ vs, Reach st.heap v l) := by
  rcases makePap_spec (P := P) (fuel := fuel) (r := r) (params := params) (vs := vs) hst.1
    (fun v hv => ⟨(hvs v hv).1.1, (hvs v hv).1.2.1⟩)
    (fun i v hv hu => ⟨(huniq i v hv hu).1, (huniq i v hv hu).2.1⟩)
    hdisj with hOOF |
    ⟨rv, out, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hc', hoss, hpres, hrvObj, houtSz,
      houtShape, htRv, hdl', hacyc', _, hdou', hreach'⟩
  · exact Or.inl hOOF
  · right
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    let S : Nat → Prop := fun l => ∃ (i : Nat) (v : Val), vs[i]? = some v ∧
      ((params[i]?.map Param.mode).getD BinderMode.many).isUnique = true ∧ OwnReach P st.heap v l
    have hpresS : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ S l) st.heap st'.heap :=
      hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun i v hv hu hor => hnot ⟨i, v, hv, hu, hor⟩⟩
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_oldSameShape_noOnce hpresS
        (fun l o₁ t₁ sp₁ ⟨_, v, hv, _, hor⟩ ho₁ hc₁ =>
          (hvs v (List.mem_of_getElem? hv)).2.1 l o₁ (OwnReach_toReach hor) ho₁ t₁ sp₁ hc₁)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside hst hstat hstr hpresS
        (fun l hss ⟨i, v, hv, hu, hor⟩ => (huniq i v hv hu).2.2 l hor hss)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_outside hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpresS
        (fun l hss ⟨i, v, hv, hu, hor⟩ => (huniq i v hv hu).2.2 l hor hss)
    obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
    have houtProps : ∀ (i : Nat) (v : Val), vs[i]? = some v →
        ∃ w, out[i]? = some w ∧ ValSameShape v w ∧ ValBaseOk st' w ∧
          NoOnceCell st'.heap w ∧ CtorFieldsOk P ext B st' w ∧
          (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot v →
            FunOkAt P ext B st' sk onceOnly Foot w) := by
      intro i v hv
      obtain ⟨w, hw, hvsh⟩ := houtShape i v hv
      have hvMem : v ∈ vs := List.mem_of_getElem? hv
      obtain ⟨hbv, hnov, hcfv⟩ := hvs v hvMem
      have hwMem : w ∈ out.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw)
      have hwHeld : HeldBy st'.heap rv w := by
        rw [hrvEq]; exact HeldBy_of_mem_vals hoNew (by simpa [Cell.vals] using hwMem)
      have hdlW : DeepLive st'.heap w := hdl'.sub hwHeld
      have hacycW : AcyclicFrom st'.heap w := hacyc'.sub hwHeld
      have hlocW : SameLoc v w := SameLoc.of_valSameShape hvsh
      have htbW : DeepTaintsBounded st'.heap st'.nextRegion w := by
        rw [hnr]
        exact DeepTaintsBounded_of_oldSameShape hbv.1 hoss hlocW
          (fun x hx => by
            have htEq : w.taint = v.taint := by
              cases v <;> cases w <;> simp [ValSameShape, Val.taint] at hvsh ⊢
              exact hvsh.2.symm
            rw [htEq] at hx; exact hbv.2.2.2 v (HeldBy.refl _ _) x hx)
          hbv.2.2.2
      exact ⟨w, hw, hvsh, ValBaseOk_of_deepLive hdlW hacycW htbW,
        NoOnceCell_of_sameShape hbv.1 (hoss.to_sameShapeOn _) hlocW hnov,
        CtorFieldsOk_of_sameShape hbv.1 (hoss.to_sameShapeOn _) hlocW hrf hcfv,
        fun sk oo ft hf => FunOkAt_preserve_sameShape hlocW (hoss.to_sameShapeOn _) hrf hf⟩
    have houtMem : ∀ w ∈ out.toList, ValBaseOk st' w ∧ NoOnceCell st'.heap w ∧ CtorFieldsOk P ext B st' w := by
      intro w hw
      obtain ⟨i, hi, hwi⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hw)
      have hiV : i < vs.length := houtSz ▸ hi
      obtain ⟨w', hw', _, hbw', hno', hcf', _⟩ := houtProps i vs[i] (List.getElem?_eq_getElem hiV)
      rw [Array.getElem?_eq_getElem hi] at hw'; cases hw'; subst hwi
      exact ⟨hbw', hno', hcf'⟩
    have htbRv : DeepTaintsBounded st'.heap st'.nextRegion rv := by
      intro w hw x hx
      rcases hw with rfl | ⟨l, o', hr', ho', hm'⟩
      · obtain ⟨v, hv, hxv⟩ := (htRv x).mp hx
        rw [hnr]; exact (hvs v hv).1.2.2.2 v (HeldBy.refl _ _) x hxv
      · rw [hrvEq] at hr'
        cases hr' with
        | here =>
          rw [hoNew] at ho'; cases ho'
          exact (houtMem w (by simpa [Cell.vals] using hm')).1.2.2.2 w (HeldBy.refl _ _) x hx
        | step ho1 hm1 hr2 =>
          rw [hoNew] at ho1; cases ho1
          exact (houtMem _ (by simpa [Cell.vals] using hm1)).1.2.2.2 w (Or.inr ⟨l, o', hr2, ho', hm'⟩) x hx
    have hnoRv : NoOnceCell st'.heap rv := by
      intro l o hr' ho' t sp hcell
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        exact (houtMem _ (by simpa [Cell.vals] using hm1)).2.1 l o hr2 ho' t sp hcell
    have hcfRv : CtorFieldsOk P ext B st' rv := by
      intro l o rc fs w hr' ho' hcell hw
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        exact (houtMem _ (by simpa [Cell.vals] using hm1)).2.2 l o rc fs w hr2 ho' hcell hw
    exact ⟨rv, out, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hoss, hpres, honceSh, hssf, hst',
      ⟨cap, hrvEq, hoNew⟩, houtSz, houtProps, ValBaseOk_of_deepLive hdl' hacyc' htbRv,
      hnoRv, hcfRv, hdou', hreach'⟩

/-- `Eval.formClosure` lifted to `F4Inv` predicates (`StOk`, `ValBaseOk`, `NoOnceCell`,
`CtorFieldsOk`, `PreservesOnceShell`, `StaticStrFresh`, and capture `FunOkAt` preservation). -/
theorem formClosure_sound {P : Prog} {ext : ExternOracle} {B fuel : Nat}
    {env : List Bnd} {p : Param} {res : ResultMode} {rc : Cls} {fvs : Array Nat} {body : Term}
    {st : St}
    (hst : StOk P ext B st)
    (hfvs : ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b →
      b.mode ≠ .erased ∧ ValBaseOk st b.val ∧ NoOnceCell st.heap b.val ∧ CtorFieldsOk P ext B st b.val ∧
      (b.mode.isUnique = true →
        OwnTreeFull P st.heap b.val ∧
        (b.mode.isBorrowed = false → OpenUnder st.regions [] b.val) ∧
        ∀ l, OwnReach P st.heap b.val l → ¬ StaticStrLoc st l))
    (hdisj : ∀ (a b : Nat) (ia ib : Nat) (ba bb : Bnd), a ≠ b →
      fvs.toList[a]? = some ia → fvs.toList[b]? = some ib →
      env[ia]? = some ba → env[ib]? = some bb →
      ba.mode.isUnique = true →
      ∀ l, OwnReach P st.heap ba.val l → ¬ Reach st.heap bb.val l) :
    (formClosure P fuel env p res rc fvs body).run st = .error .stuck ∨
    (formClosure P fuel env p res rc fvs body).run st = .error .outOfFuel ∨
    ∃ rv env' taint st',
      (formClosure P fuel env p res rc fvs body).run st = .ok (rv, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size + 1 ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      OldSameShape st.heap st'.heap ∧
      PreservesLocs
        (fun l => l < st.heap.objs.size ∧
          ∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → b.mode.isUnique = true →
            ¬ OwnReach P st.heap b.val l)
        st.heap st'.heap ∧
      PreservesOnceShell st.heap st'.heap ∧
      StaticStrFresh st st' ∧
      StOk P ext B st' ∧
      (∃ cap, rv = .ref st.heap.objs.size cap taint ∧
        st'.heap.objs[st.heap.objs.size]? = some ⟨.clo env' p res rc fvs body, cap⟩) ∧
      (∀ i ∈ fvs.toList, ∃ b v', env[i]? = some b ∧ env'[i]? = some { b with val := v' } ∧
        ValSameShape b.val v' ∧ ValBaseOk st' v' ∧ NoOnceCell st'.heap v' ∧
        CtorFieldsOk P ext B st' v' ∧
        (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot b.val →
          FunOkAt P ext B st' sk onceOnly Foot v')) ∧
      (∀ j, j ∉ fvs.toList → env'[j]? = env[j]?) ∧
      ValBaseOk st' rv ∧
      NoOnceCell st'.heap rv ∧
      CtorFieldsOk P ext B st' rv ∧
      (∀ rs A, (∀ i ∈ fvs.toList, ∀ b, env[i]? = some b → DeepOpenUnder st.heap rs A b.val) →
        DeepOpenUnder st'.heap rs A rv) ∧
      (∀ l, Reach st'.heap rv l →
        l = st.heap.objs.size ∨ ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧ Reach st.heap b.val l) := by
  rcases formClosure_spec (P := P) (fuel := fuel) (env := env) (p := p) (res := res) (rc := rc)
    (fvs := fvs) (body := body) hst.1
    (fun i hi b hb =>
      let h := hfvs i hi b hb
      ⟨h.1, h.2.1.1, h.2.1.2.1, fun hu => ⟨(h.2.2.2.2 hu).1, (h.2.2.2.2 hu).2.1⟩⟩)
    hdisj with hSt | hOOF |
    ⟨rv, env', taint, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hc', hoss, hpres, hrvObj,
      henvFvs, henvOut, htRv, hdl', hacyc', _, hdou', hreach'⟩
  · exact Or.inl hSt
  · exact Or.inr (Or.inl hOOF)
  · right; right
    have hrf : RegsFuture st st' := RegsFuture.same_regions (hnr ▸ Nat.le_refl _) hr
    let S : Nat → Prop := fun l => ∃ i ∈ fvs.toList, ∃ b, env[i]? = some b ∧
      b.mode.isUnique = true ∧ OwnReach P st.heap b.val l
    have hpresS : PreservesLocs (fun l => l < st.heap.objs.size ∧ ¬ S l) st.heap st'.heap :=
      hpres.mono fun l ⟨hlt, hnot⟩ => ⟨hlt, fun i hi b hb hu hor => hnot ⟨i, hi, b, hb, hu, hor⟩⟩
    have honceSh : PreservesOnceShell st.heap st'.heap :=
      PreservesOnceShell.of_oldSameShape_noOnce hpresS
        (fun l o₁ t₁ sp₁ ⟨i, hi, b, hb, _, hor⟩ ho₁ hc₁ =>
          (hfvs i hi b hb).2.2.1 l o₁ (OwnReach_toReach hor) ho₁ t₁ sp₁ hc₁)
    have hssf : StaticStrFresh st st' :=
      StaticStrFresh_of_preserves_outside hst hstat hstr hpresS
        (fun l hss ⟨i, hi, b, hb, hu, hor⟩ => ((hfvs i hi b hb).2.2.2.2 hu).2.2 l hor hss)
    have hst' : StOk P ext B st' :=
      StOk_of_preserves_outside hst hc' hr (hnr ▸ Nat.le_refl _) hstat hstr hpresS
        (fun l hss ⟨i, hi, b, hb, hu, hor⟩ => ((hfvs i hi b hb).2.2.2.2 hu).2.2 l hor hss)
    obtain ⟨cap, hrvEq, hoNew⟩ := hrvObj
    have hcapProps : ∀ i ∈ fvs.toList, ∃ b v', env[i]? = some b ∧ env'[i]? = some { b with val := v' } ∧
        ValSameShape b.val v' ∧ ValBaseOk st' v' ∧ NoOnceCell st'.heap v' ∧
        CtorFieldsOk P ext B st' v' ∧
        (∀ sk onceOnly Foot, FunOkAt P ext B st sk onceOnly Foot b.val →
          FunOkAt P ext B st' sk onceOnly Foot v') := by
      intro i hi
      obtain ⟨b, v', hb, hb', hvsh, hdlV', hacycV'⟩ := henvFvs i hi
      obtain ⟨_, hbv, hnov, hcfv, _⟩ := hfvs i hi b hb
      have hlocV : SameLoc b.val v' := SameLoc.of_valSameShape hvsh
      have htbV' : DeepTaintsBounded st'.heap st'.nextRegion v' := by
        rw [hnr]
        exact DeepTaintsBounded_of_oldSameShape hbv.1 hoss hlocV
          (fun x hx => by
            have htEq : v'.taint = b.val.taint := by
              cases hb0 : b.val <;> cases hv0 : v' <;> rw [hb0, hv0] at hvsh <;>
                simp [ValSameShape, Val.taint] at hvsh ⊢
              exact hvsh.2.symm
            rw [htEq] at hx; exact hbv.2.2.2 b.val (HeldBy.refl _ _) x hx)
          hbv.2.2.2
      exact ⟨b, v', hb, hb', hvsh, ValBaseOk_of_deepLive hdlV' hacycV' htbV',
        NoOnceCell_of_sameShape hbv.1 (hoss.to_sameShapeOn _) hlocV hnov,
        CtorFieldsOk_of_sameShape hbv.1 (hoss.to_sameShapeOn _) hlocV hrf hcfv,
        fun sk oo ft hf => FunOkAt_preserve_sameShape hlocV (hoss.to_sameShapeOn _) hrf hf⟩
    have hvalMem : ∀ w ∈ (Cell.clo env' p res rc fvs body).vals,
        ValBaseOk st' w ∧ NoOnceCell st'.heap w ∧ CtorFieldsOk P ext B st' w := by
      intro w hw
      simp only [Cell.vals, List.mem_filterMap] at hw
      obtain ⟨i, hi, hmap⟩ := hw
      obtain ⟨b, v', _, hb', _, hbv', hno', hcf', _⟩ := hcapProps i hi
      rw [hb'] at hmap; simp only [Option.map_some, Option.some.injEq] at hmap
      subst hmap
      exact ⟨hbv', hno', hcf'⟩
    have htbRv : DeepTaintsBounded st'.heap st'.nextRegion rv := by
      intro w hw x hx
      rcases hw with rfl | ⟨l, o', hr', ho', hm'⟩
      · obtain ⟨i, hi, b, hb, hxb⟩ := (htRv x).mp hx
        rw [hnr]; exact (hfvs i hi b hb).2.1.2.2.2 b.val (HeldBy.refl _ _) x hxb
      · rw [hrvEq] at hr'
        cases hr' with
        | here =>
          rw [hoNew] at ho'; cases ho'
          exact (hvalMem w hm').1.2.2.2 w (HeldBy.refl _ _) x hx
        | step ho1 hm1 hr2 =>
          rw [hoNew] at ho1; cases ho1
          exact (hvalMem _ hm1).1.2.2.2 w (Or.inr ⟨l, o', hr2, ho', hm'⟩) x hx
    have hnoRv : NoOnceCell st'.heap rv := by
      intro l o hr' ho' t sp hcell
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        exact (hvalMem _ hm1).2.1 l o hr2 ho' t sp hcell
    have hcfRv : CtorFieldsOk P ext B st' rv := by
      intro l o r' fs w hr' ho' hcell hw
      rw [hrvEq] at hr'
      cases hr' with
      | here => rw [hoNew] at ho'; cases ho'; cases hcell
      | step ho1 hm1 hr2 =>
        rw [hoNew] at ho1; cases ho1
        exact (hvalMem _ hm1).2.2 l o r' fs w hr2 ho' hcell hw
    exact ⟨rv, env', taint, st', hrun, hr, hnr, hstat, hstr, hsz, hcap, hoss, hpres, honceSh, hssf,
      hst', ⟨cap, hrvEq, hoNew⟩, hcapProps, henvOut, ValBaseOk_of_deepLive hdl' hacyc' htbRv,
      hnoRv, hcfRv, hdou', hreach'⟩

/-! ## 5. Checker Helper `Runs` Unpackers (`flowTo`, `bindInner`, `retCheck`, `anProj`, ...) -/

theorem CM_setSt_run (d : Nat) (b : BSt) (s : CSt) :
    (setSt d b).run s = .ok ((), { s with st := s.st.set! d b }) := rfl

theorem CM_markSpent_run (d : Nat) (s : CSt) :
    (markSpent d).run s = .ok ((), { s with spent := s.spent.set! d true }) := rfl

theorem CM_innermost_run (s : CSt) :
    innermost.run s = .ok (s.regions.headD 1, s) := rfl

/-- Generic relational fold lemma for `for x in xs do ...` loops over `PUnit` in `CM` that never
early-return (only `yield` or `refuseM`). -/
theorem CM_forIn_unit_fold {α : Type} {f : α → PUnit → CM (ForInStep PUnit)}
    {R : List α → CSt → CSt → Prop}
    (hnil : ∀ s, R [] s s)
    (hcons : ∀ x rest s s1 s2,
      (f x PUnit.unit).run s = .ok (.yield PUnit.unit, s1) →
      R rest s1 s2 → R (x :: rest) s s2)
    (hnoDone : ∀ x s s', (f x PUnit.unit).run s ≠ .ok (.done PUnit.unit, s'))
    (xs : List α) (s s' : CSt)
    (hr : StateT.run (forIn (m := CM) xs PUnit.unit f) s = .ok (PUnit.unit, s')) :
    R xs s s' := by
  induction xs generalizing s with
  | nil =>
    simp only [List.forIn_nil] at hr
    rw [CM_pure_run] at hr; cases hr
    exact hnil _
  | cons x rest ih =>
    simp only [List.forIn_cons] at hr
    rw [CM_bind_run] at hr
    cases hfx : (f x PUnit.unit).run s with
    | error e => rw [hfx] at hr; cases hr
    | ok p =>
      rcases p with ⟨step, s1⟩
      rw [hfx] at hr
      cases step with
      | done b =>
        cases b
        exact absurd hfx (hnoDone x s s1)
      | yield b =>
        cases b
        exact hcons x rest s s1 s' hfx (ih s1 hr)

/-- Unpack the once-unspent check loop in `flowTo .once`. -/
theorem CM_forIn_checkOnceUnspent {ds : List Nat} {s s' : CSt} {msg : String}
    (hr : StateT.run (forIn (m := CM) ds PUnit.unit fun x _ => do
        if (← isOnceBnd x) && (← isSpent x) then refuseM msg
        pure (ForInStep.yield PUnit.unit)) s = .ok (PUnit.unit, s')) :
    s' = s ∧ ∀ x ∈ ds, s.once[x]? = some true → s.spent[x]? ≠ some true := by
  have h := CM_forIn_unit_check (P := fun x st => st.once[x]? = some true → st.spent[x]? ≠ some true)
    (fun x st => by
      constructor
      · intro st1 hrun
        rw [CM_bind_run, CM_isOnceBnd_run] at hrun; dsimp only at hrun
        rw [CM_bind_run, CM_isSpent_run] at hrun; dsimp only at hrun
        cases ho : st.once[x]? with
        | none =>
          simp only [ho, Option.getD_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrun
          rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, fun h => by cases h⟩
        | some bo =>
          cases bo with
          | false =>
            simp only [ho, Option.getD_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrun
            rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, fun h => by cases h⟩
          | true =>
            cases hsp : st.spent[x]? with
            | none =>
              simp only [ho, hsp, Option.getD_some, Option.getD_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrun
              rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, fun _ h => by cases h⟩
            | some bsp =>
              cases bsp with
              | false =>
                simp only [ho, hsp, Option.getD_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrun
                rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, fun _ h => by cases h⟩
              | true =>
                simp only [ho, hsp, Option.getD_some, Bool.and_self, ↓reduceIte] at hrun
                rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
      · intro st1 hrun
        rw [CM_bind_run, CM_isOnceBnd_run] at hrun; dsimp only at hrun
        rw [CM_bind_run, CM_isSpent_run] at hrun; dsimp only at hrun
        cases hcond : ((st.once[x]?.getD false && st.spent[x]?.getD false)) with
        | false =>
          simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hrun
          rw [CM_pure_run] at hrun; cases hrun
        | true =>
          simp only [hcond, ↓reduceIte] at hrun
          rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun)
    ds s s' hr
  exact ⟨h.2, h.1⟩

/-- Unpack the mark-spent loop `for x in ds do if ← isOnceBnd x then markSpent x`. -/
theorem CM_forIn_markSpentOnce {ds : List Nat} {s s' : CSt}
    (hr : StateT.run (forIn (m := CM) ds PUnit.unit fun x _ => do
        if ← isOnceBnd x then markSpent x
        pure (ForInStep.yield PUnit.unit)) s = .ok (PUnit.unit, s')) :
    s'.st = s.st ∧ s'.once = s.once ∧ s'.regions = s.regions ∧
    s'.nextRegion = s.nextRegion ∧ s'.steps = s.steps ∧
    s'.spent.size = s.spent.size ∧
    (∀ i, i < s.spent.size →
      s'.spent[i]? = if i ∈ ds ∧ s.once[i]? = some true then some true else s.spent[i]?) := by
  refine CM_forIn_unit_fold
    (R := fun xs s0 s1 =>
      s1.st = s0.st ∧ s1.once = s0.once ∧ s1.regions = s0.regions ∧
      s1.nextRegion = s0.nextRegion ∧ s1.steps = s0.steps ∧
      s1.spent.size = s0.spent.size ∧
      (∀ i, i < s0.spent.size →
        s1.spent[i]? = if i ∈ xs ∧ s0.once[i]? = some true then some true else s0.spent[i]?))
    (fun s0 => ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp⟩)
    (fun x rest s0 s1 s2 hfx hrest => by
      rw [CM_bind_run, CM_isOnceBnd_run] at hfx; dsimp only at hfx
      obtain ⟨hst2, honce2, hreg2, hnr2, hsteps2, hsz2, hsp2⟩ := hrest
      cases ho : s0.once[x]? with
      | none =>
        simp only [ho, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at hfx
        rw [CM_pure_run] at hfx; cases hfx
        refine ⟨hst2, honce2, hreg2, hnr2, hsteps2, hsz2, fun i hi => ?_⟩
        rw [hsp2 i hi]
        by_cases hix : i = x
        · subst hix; simp [ho]
        · simp [hix]
      | some bo =>
        cases bo with
        | false =>
          simp only [ho, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hfx
          rw [CM_pure_run] at hfx; cases hfx
          refine ⟨hst2, honce2, hreg2, hnr2, hsteps2, hsz2, fun i hi => ?_⟩
          rw [hsp2 i hi]
          by_cases hix : i = x
          · subst hix; simp [ho]
          · simp [hix]
        | true =>
          simp only [ho, Option.getD_some, ↓reduceIte] at hfx
          rw [CM_bind_run, CM_markSpent_run] at hfx; dsimp only at hfx
          rw [CM_pure_run] at hfx; cases hfx
          have hsz1 : (s0.spent.set! x true).size = s0.spent.size := by simp [Array.set!_eq_setIfInBounds]
          refine ⟨hst2, honce2, hreg2, hnr2, hsteps2, hsz2.trans hsz1, fun i hi => ?_⟩
          have hi1 : i < (s0.spent.set! x true).size := by rw [hsz1]; exact hi
          rw [hsp2 i hi1]
          by_cases hix : i = x
          · subst hix
            simp only [List.mem_cons, true_or, ho, and_self, ↓reduceIte]
            split
            · rfl
            · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
              simp [hi]
          · simp only [List.mem_cons, hix, false_or]
            split
            · rfl
            · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hix)])
    (fun x s0 s1 hfx => by
      rw [CM_bind_run, CM_isOnceBnd_run] at hfx; dsimp only at hfx
      cases ho : s0.once[x]? with
      | none =>
        simp only [ho, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at hfx
        rw [CM_pure_run] at hfx; cases hfx
      | some bo =>
        cases bo with
        | false =>
          simp only [ho, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hfx
          rw [CM_pure_run] at hfx; cases hfx
        | true =>
          simp only [ho, Option.getD_some, ↓reduceIte] at hfx
          rw [CM_bind_run, CM_markSpent_run] at hfx; dsimp only at hfx
          rw [CM_pure_run] at hfx; cases hfx)
    ds s s' hr

/-- Unpack the share-deps loop `for x in ds do if (← stOf x) == BSt.live then setSt x BSt.shared`. -/
theorem CM_forIn_shareDeps {ds : List Nat} {s s' : CSt}
    (hr : StateT.run (forIn (m := CM) ds PUnit.unit fun x _ => do
        if (← stOf x) == BSt.live then setSt x BSt.shared
        pure (ForInStep.yield PUnit.unit)) s = .ok (PUnit.unit, s')) :
    s'.once = s.once ∧ s'.spent = s.spent ∧ s'.regions = s.regions ∧
    s'.nextRegion = s.nextRegion ∧ s'.steps = s.steps ∧
    s'.st.size = s.st.size ∧
    (∀ i, i < s.st.size →
      s'.st[i]? = if i ∈ ds ∧ s.st[i]? = some .live then some .shared else s.st[i]?) := by
  have hdl : (BSt.dead == BSt.live) = false := rfl
  have hsl : (BSt.shared == BSt.live) = false := rfl
  have hll : (BSt.live == BSt.live) = true := rfl
  refine CM_forIn_unit_fold
    (R := fun xs s0 s1 =>
      s1.once = s0.once ∧ s1.spent = s0.spent ∧ s1.regions = s0.regions ∧
      s1.nextRegion = s0.nextRegion ∧ s1.steps = s0.steps ∧
      s1.st.size = s0.st.size ∧
      (∀ i, i < s0.st.size →
        s1.st[i]? = if i ∈ xs ∧ s0.st[i]? = some .live then some .shared else s0.st[i]?))
    (fun s0 => ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp⟩)
    (fun x rest s0 s1 s2 hfx hrest => by
      rw [CM_bind_run, CM_stOf_run] at hfx; dsimp only at hfx
      obtain ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2, hst2⟩ := hrest
      cases hget : s0.st[x]? with
      | none =>
        simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hfx
        rw [CM_pure_run] at hfx; cases hfx
        refine ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2, fun i hi => ?_⟩
        rw [hst2 i hi]
        by_cases hix : i = x
        · subst hix; simp [hget]
        · simp [hix]
      | some b =>
        cases b with
        | dead =>
          simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hfx
          rw [CM_pure_run] at hfx; cases hfx
          refine ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2, fun i hi => ?_⟩
          rw [hst2 i hi]
          by_cases hix : i = x
          · subst hix; simp [hget]
          · simp [hix]
        | shared =>
          simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hfx
          rw [CM_pure_run] at hfx; cases hfx
          refine ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2, fun i hi => ?_⟩
          rw [hst2 i hi]
          by_cases hix : i = x
          · subst hix; simp [hget]
          · simp [hix]
        | live =>
          simp only [hget, Option.getD_some, hll, ↓reduceIte] at hfx
          rw [CM_bind_run, CM_setSt_run] at hfx; dsimp only at hfx
          rw [CM_pure_run] at hfx; cases hfx
          have hsz1 : (s0.st.set! x BSt.shared).size = s0.st.size := by simp [Array.set!_eq_setIfInBounds]
          refine ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2.trans hsz1, fun i hi => ?_⟩
          have hi1 : i < (s0.st.set! x BSt.shared).size := by rw [hsz1]; exact hi
          rw [hst2 i hi1]
          by_cases hix : i = x
          · subst hix
            have hsetSelf : (s0.st.set! i BSt.shared)[i]? = some BSt.shared := by
              rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]; simp [hi]
            rw [hsetSelf]
            simp only [List.mem_cons, true_or, hget, and_self, ↓reduceIte]
            split <;> rfl
          · have hsetNe : (s0.st.set! x BSt.shared)[i]? = s0.st[i]? := by
              rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hix)]
            rw [hsetNe]
            simp only [List.mem_cons, hix, false_or])
    (fun x s0 s1 hfx => by
      rw [CM_bind_run, CM_stOf_run] at hfx; dsimp only at hfx
      cases hget : s0.st[x]? with
      | none =>
        simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hfx
        rw [CM_pure_run] at hfx; cases hfx
      | some b =>
        cases b with
        | dead =>
          simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hfx
          rw [CM_pure_run] at hfx; cases hfx
        | shared =>
          simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hfx
          rw [CM_pure_run] at hfx; cases hfx
        | live =>
          simp only [hget, Option.getD_some, hll, ↓reduceIte] at hfx
          rw [CM_bind_run, CM_setSt_run] at hfx; dsimp only at hfx
          rw [CM_pure_run] at hfx; cases hfx)
    ds s s' hr

/-- Unpack the kill-deps loop `for x in ds do setSt x BSt.dead`. -/
theorem CM_forIn_killDeps {ds : List Nat} {s s' : CSt}
    (hr : StateT.run (forIn (m := CM) ds PUnit.unit fun x _ => do
        setSt x BSt.dead
        pure (ForInStep.yield PUnit.unit)) s = .ok (PUnit.unit, s')) :
    s'.once = s.once ∧ s'.spent = s.spent ∧ s'.regions = s.regions ∧
    s'.nextRegion = s.nextRegion ∧ s'.steps = s.steps ∧
    s'.st.size = s.st.size ∧
    (∀ i, i < s.st.size → s'.st[i]? = if i ∈ ds then some .dead else s.st[i]?) := by
  refine CM_forIn_unit_fold
    (R := fun xs s0 s1 =>
      s1.once = s0.once ∧ s1.spent = s0.spent ∧ s1.regions = s0.regions ∧
      s1.nextRegion = s0.nextRegion ∧ s1.steps = s0.steps ∧
      s1.st.size = s0.st.size ∧
      (∀ i, i < s0.st.size → s1.st[i]? = if i ∈ xs then some .dead else s0.st[i]?))
    (fun s0 => ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp⟩)
    (fun x rest s0 s1 s2 hfx hrest => by
      rw [CM_bind_run, CM_setSt_run] at hfx; dsimp only at hfx
      rw [CM_pure_run] at hfx; cases hfx
      obtain ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2, hst2⟩ := hrest
      have hsz1 : (s0.st.set! x BSt.dead).size = s0.st.size := by simp [Array.set!_eq_setIfInBounds]
      refine ⟨honce2, hsp2, hreg2, hnr2, hsteps2, hsz2.trans hsz1, fun i hi => ?_⟩
      have hi1 : i < (s0.st.set! x BSt.dead).size := by rw [hsz1]; exact hi
      rw [hst2 i hi1]
      by_cases hix : i = x
      · subst hix
        have hsetSelf : (s0.st.set! i BSt.dead)[i]? = some BSt.dead := by
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]; simp [hi]
        rw [hsetSelf]
        simp only [List.mem_cons, true_or, ↓reduceIte, ite_self]
      · have hsetNe : (s0.st.set! x BSt.dead)[i]? = s0.st[i]? := by
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hix)]
        rw [hsetNe]
        simp only [List.mem_cons, hix, false_or])
    (fun x s0 s1 hfx => by
      rw [CM_bind_run, CM_setSt_run] at hfx; dsimp only at hfx
      rw [CM_pure_run] at hfx; cases hfx)
    ds s s' hr

theorem CM_valid_ok {v : AVal} {w : String} {s s' : CSt}
    (h : (valid v w).run s = .ok ((), s')) :
    s' = s ∧ ∀ d ∈ v.deps, d < s.st.size ∧ s.st[d]? ≠ some .dead := by
  unfold valid at h; rw [CM_bind_run] at h
  cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) s with
  | error e => rw [hl] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, s1⟩; rw [hl] at h; dsimp only at h; rw [CM_pure_run] at h; cases h
    have hdd : (BSt.dead == BSt.dead) = true := rfl
    have hld : (BSt.live == BSt.dead) = false := rfl
    have hsd : (BSt.shared == BSt.dead) = false := rfl
    obtain ⟨hall, hsEq⟩ := CM_forIn_unit_check (P := fun d st => d < st.st.size ∧ st.st[d]? ≠ some .dead)
      (fun d st => by
        constructor
        · intro st1 hrun; rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
          cases hget : st.st[d]? with
          | none => simp only [hget, Option.getD_none, hdd, ↓reduceIte] at hrun; rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
          | some b => cases b with
            | dead => simp only [hget, Option.getD_some, hdd, ↓reduceIte] at hrun; rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
            | live => simp only [hget, Option.getD_some, hld, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, (Array.getElem?_eq_some_iff.mp hget).1, by decide⟩
            | shared => simp only [hget, Option.getD_some, hsd, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, (Array.getElem?_eq_some_iff.mp hget).1, by decide⟩
        · intro st1 hrun; rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
          cases hget : st.st[d]? with
          | none => simp only [hget, Option.getD_none, hdd, ↓reduceIte] at hrun; rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
          | some b => cases b with
            | dead => simp only [hget, Option.getD_some, hdd, ↓reduceIte] at hrun; rw [CM_bind_run, CM_refuseM_run] at hrun; cases hrun
            | live => simp only [hget, Option.getD_some, hld, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun
            | shared => simp only [hget, Option.getD_some, hsd, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun)
      v.deps s s' hl
    exact ⟨hsEq, hall⟩

theorem CM_notOnceSrc_ok {v : AVal} {w : String} {s s' : CSt}
    (h : (notOnceSrc v w).run s = .ok ((), s')) :
    s' = s ∧ ¬ IsOnceSrc (AState.ofCSt s) v := by
  unfold notOnceSrc at h
  cases hsrc : v.src with
  | none =>
    simp only [hsrc] at h; rw [CM_pure_run] at h; cases h
    exact ⟨rfl, by rintro ⟨_, hs, _⟩; rw [hsrc] at hs; cases hs⟩
  | some x =>
    simp only [hsrc] at h; rw [CM_bind_run, CM_isOnceBnd_run] at h; dsimp only at h
    cases ho : s.once[x]? with
    | none =>
      simp only [ho, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at h
      rw [CM_pure_run] at h; cases h
      exact ⟨rfl, by rintro ⟨_, hs, h1⟩; rw [hsrc] at hs; cases hs; dsimp [AState.ofCSt] at h1; rw [ho] at h1; cases h1⟩
    | some b =>
      cases b with
      | true =>
        simp only [ho, Option.getD_some, ↓reduceIte] at h
        rw [CM_refuseM_run] at h; cases h
      | false =>
        simp only [ho, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at h
        rw [CM_pure_run] at h; cases h
        exact ⟨rfl, by rintro ⟨_, hs, h1⟩; rw [hsrc] at hs; cases hs; dsimp [AState.ofCSt] at h1; rw [ho] at h1; cases h1⟩

theorem CM_isUniq_ok {v : AVal} {res : Bool} {s s' : CSt}
    (h : (isUniq v).run s = .ok (res, s')) :
    s' = s ∧ (res = true ↔ v.cls ≠ .val ∨ (v.own = .uniq ∧ ∀ d ∈ v.deps, s.st[d]? = some .live)) := by
  unfold isUniq at h
  cases hcls : (v.cls != .val) with
  | true =>
    simp only [hcls, ↓reduceIte] at h; rw [CM_pure_run] at h; cases h
    have hne : v.cls ≠ .val := fun heq => by rw [heq] at hcls; cases hcls
    exact ⟨rfl, ⟨fun _ => Or.inl hne, fun _ => rfl⟩⟩
  | false =>
    simp only [hcls, Bool.false_eq_true, ↓reduceIte] at h
    have hclsVal : v.cls = .val := by
      cases hc : v.cls <;> try rfl
      all_goals (rw [hc] at hcls; cases hcls)
    cases hown : (v.own != .uniq) with
    | true =>
      simp only [hown, ↓reduceIte] at h; rw [CM_pure_run] at h; cases h
      refine ⟨rfl, ⟨fun ht => (by cases ht), fun hdisj => ?_⟩⟩
      rcases hdisj with hne | ⟨ho, _⟩
      · exact absurd hclsVal hne
      · rw [ho] at hown; cases hown
    | false =>
      simp only [hown, Bool.false_eq_true, ↓reduceIte] at h
      have hownEq : v.own = .uniq := by
        cases ho : v.own <;> try rfl
        rw [ho] at hown; cases hown
      rw [CM_bind_run] at h
      cases hl : StateT.run (forIn (m := CM) v.deps ((none : Option Bool), ()) _) s with
      | error e => rw [hl] at h; cases h
      | ok p =>
        rcases p with ⟨r0, s1⟩; rw [hl] at h
        have hdl : (BSt.dead == BSt.live) = false := rfl
        have hsl : (BSt.shared == BSt.live) = false := rfl
        have hll : (BSt.live == BSt.live) = true := rfl
        obtain ⟨hsEq, hdisj⟩ := CM_forIn_optBool_check (P := fun d st => st.st[d]? = some .live)
          (fun d st => by
            refine ⟨?_, ?_, ?_⟩
            · intro st1 hrun; rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
              cases hget : st.st[d]? with
              | none => simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun
              | some b => cases b with
                | shared => simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun
                | dead => simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun
                | live => simp only [hget, Option.getD_some, hll, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, rfl⟩
            · intro st1 hrun; rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
              cases hget : st.st[d]? with
              | none => simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, by simp⟩
              | some b => cases b with
                | shared => simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, by decide⟩
                | dead => simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact ⟨rfl, by decide⟩
                | live => simp only [hget, Option.getD_some, hll, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun
            · intro r1 st1 hrun; rw [CM_bind_run, CM_stOf_run] at hrun; dsimp only at hrun
              cases hget : st.st[d]? with
              | none => simp only [hget, Option.getD_none, hdl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact Or.inr rfl
              | some b => cases b with
                | shared => simp only [hget, Option.getD_some, hsl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact Or.inr rfl
                | dead => simp only [hget, Option.getD_some, hdl, Bool.false_eq_true, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact Or.inr rfl
                | live => simp only [hget, Option.getD_some, hll, ↓reduceIte] at hrun; rw [CM_pure_run] at hrun; cases hrun; exact Or.inl rfl)
          v.deps s s1 r0 hl
        rcases hdisj with ⟨hp1, hall⟩ | ⟨hp1, x, hx, hnot⟩
        · dsimp only at h; rw [hp1, hsEq] at h; dsimp only at h; rw [CM_pure_run] at h; cases h
          exact ⟨rfl, ⟨fun _ => Or.inr ⟨hownEq, hall⟩, fun _ => rfl⟩⟩
        · dsimp only at h; rw [hp1, hsEq] at h; dsimp only at h; rw [CM_pure_run] at h; cases h
          refine ⟨rfl, ⟨fun ht => (by cases ht), fun hd => ?_⟩⟩
          rcases hd with hne | ⟨_, hall⟩
          · exact absurd hclsVal hne
          · exact absurd (hall x hx) hnot

theorem CM_killSrc_ok {v : AVal} {s s' : CSt}
    (h : (killSrc v).run s = .ok ((), s')) :
    s'.once = s.once ∧ s'.spent = s.spent ∧ s'.regions = s.regions ∧
    s'.nextRegion = s.nextRegion ∧ s'.steps = s.steps ∧
    s'.st.size = s.st.size ∧
    (∀ i, i < s.st.size →
      s'.st[i]? = if v.onceOnly = true ∧ v.src = some i then some .dead else s.st[i]?) := by
  unfold killSrc at h
  cases ho : v.onceOnly with
  | false =>
    simp only [ho, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_pure_run] at h; cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp⟩
  | true =>
    simp only [ho, ↓reduceIte] at h
    cases hsrc : v.src with
    | none =>
      simp only [hsrc] at h; rw [CM_pure_run] at h; cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp⟩
    | some x =>
      simp only [hsrc] at h; rw [CM_setSt_run] at h; cases h
      have hsz : (s.st.set! x BSt.dead).size = s.st.size := by simp [Array.set!_eq_setIfInBounds]
      refine ⟨rfl, rfl, rfl, rfl, rfl, hsz, fun i hi => ?_⟩
      by_cases hix : i = x
      · subst hix
        simp only [true_and, ↓reduceIte]
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]; simp [hi]
      · have hne : ¬ (some x = some i) := fun h1 => hix (Option.some.inj h1).symm
        simp only [true_and, hne, ↓reduceIte]
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hix)]

/-- Helper: build `AStateOk σ' ∧ AStateLe σ σ'` when `σ'` keeps `once`/`regions`/`nextRegion`
and only monotonically advances `st` and `spent` at the same array sizes. -/
theorem AStateOk_AStateLe_of_pointwise {σ σ' : AState}
    (hok : AStateOk σ)
    (hszSt : σ'.st.size = σ.st.size)
    (honce : σ'.once = σ.once)
    (hszSp : σ'.spent.size = σ.spent.size)
    (hreg : σ'.regions = σ.regions)
    (hnr : σ'.nextRegion = σ.nextRegion)
    (hstLe : ∀ i, i < σ.st.size →
      match σ.st[i]?, σ'.st[i]? with | some b1, some b2 => BSt.le b1 b2 | _, _ => False)
    (hspLe : ∀ i, i < σ.spent.size → σ.spent[i]? = some true → σ'.spent[i]? = some true) :
    AStateOk σ' ∧ AStateLe σ σ' := by
  refine ⟨⟨by rw [hszSt, honce]; exact hok.1, by rw [hszSt, hszSp]; exact hok.2.1,
    by rw [hnr]; exact hok.2.2.1, by rw [hreg]; exact hok.2.2.2.1,
    by rw [hreg]; exact hok.2.2.2.2.1, by rw [hreg, hnr]; exact hok.2.2.2.2.2⟩,
    ⟨by omega, by omega, hstLe, fun i _ => by rw [honce], hspLe⟩⟩

/-- Complete unpacking of `Check.flowTo` (`Runs (flowTo d exp v w) σ () σ'`). -/
theorem Runs_flowTo {d : Dest} {exp : Skel} {v : AVal} {w : String} {σ σ' : AState}
    (hok : AStateOk σ) (h : Runs (flowTo d exp v w) σ () σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    ValidDeps σ v.deps ∧
    (d = .once → exp.admitsNA v.skel = true ∧ UnspentOnceDeps σ v.deps) ∧
    (d ≠ .once → exp.admits v.skel = true ∧ v.onceOnly = false ∧ ¬ IsOnceSrc σ v) ∧
    (∀ i, i < σ.spent.size →
      σ'.spent[i]? = if i ∈ v.deps ∧ σ.once[i]? = some true then some true else σ.spent[i]?) ∧
    (d = .lend → σ'.st = σ.st) ∧
    (d = .share → ∀ i, i < σ.st.size →
      σ'.st[i]? = if v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live then some .shared else σ.st[i]?) ∧
    (d = .once → ∀ i, i < σ.st.size →
      σ'.st[i]? = if v.onceOnly = true ∧ v.src = some i then some .dead
        else if v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live then some .shared else σ.st[i]?) ∧
    (∀ b, d = .uniq b →
      (v.cls = .val → v.own = .uniq ∧ (∀ x ∈ v.deps, σ.st[x]? = some .live) ∧
        (b = false → v.regs = [])) ∧
      ∀ i, i < σ.st.size → σ'.st[i]? = if v.cls = .val ∧ i ∈ v.deps then some .dead else σ.st[i]?) := by
  unfold Runs flowTo at h
  rw [CM_bind_run] at h
  cases hval : (valid v w).run (σ.toCSt 0) with
  | error e => rw [hval] at h; cases h
  | ok p1 =>
    rcases p1 with ⟨⟨⟩, s1⟩
    rw [hval] at h; dsimp only at h
    obtain ⟨rfl, hvd⟩ := CM_valid_ok hval
    dsimp only [AState.toCSt] at hvd
    have hskStep :
        (match d with
        | .once => exp.admitsNA v.skel
        | _ => if v.onceOnly then exp.admitsNA v.skel else exp.admits v.skel) = true ∧
        ((do
          match d with
          | .once => do
              for x in v.deps do
                if (← isOnceBnd x) && (← isSpent x) then
                  refuseM s!"onceReentry: a once binding passed on after it was called or passed on: {w}"
          | _ => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
              notOnceSrc v w
          for x in v.deps do
            if ← isOnceBnd x then markSpent x
          match d with
          | .lend => pure ()
          | .share => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .once => do
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .uniq b => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure given away: {w}"
              if v.cls == .val then
                unless ← isUniq v do refuseM s!"revokedUse: a value that may be shared, at a unique position: {w}"
                if !b && !v.regs.isEmpty then refuseM s!"borrowEscape: a borrowed value given away: {w}"
                for x in v.deps do setSt x BSt.dead
          killSrc v) : CM Unit).run (σ.toCSt 0) = .ok ((), σ'.toCSt 0) := by
      cases d with
      | once =>
        dsimp only at h ⊢
        cases ha : exp.admitsNA v.skel with
        | true => simp only [ha, ↓reduceIte] at h; exact ⟨rfl, h⟩
        | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
      | lend | share | uniq _ =>
        dsimp only at h ⊢
        cases hoo : v.onceOnly with
        | true =>
          simp only [hoo, ↓reduceIte] at h ⊢
          cases ha : exp.admitsNA v.skel with
          | true => simp only [ha, ↓reduceIte] at h; exact ⟨rfl, h⟩
          | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
        | false =>
          simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases ha : exp.admits v.skel with
          | true => simp only [ha, ↓reduceIte] at h; exact ⟨rfl, h⟩
          | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
    have hskOk := hskStep.1
    have h := hskStep.2
    -- Phase 1: once-unspent vs non-once check (read-only)
    have hphase1 :
        (d = .once → UnspentOnceDeps σ v.deps) ∧
        (d ≠ .once → v.onceOnly = false ∧ ¬ IsOnceSrc σ v) ∧
        ((do
          for x in v.deps do
            if ← isOnceBnd x then markSpent x
          match d with
          | .lend => pure ()
          | .share => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .once => do
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .uniq b => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure given away: {w}"
              if v.cls == .val then
                unless ← isUniq v do refuseM s!"revokedUse: a value that may be shared, at a unique position: {w}"
                if !b && !v.regs.isEmpty then refuseM s!"borrowEscape: a borrowed value given away: {w}"
                for x in v.deps do setSt x BSt.dead
          killSrc v) : CM Unit).run (σ.toCSt 0) = .ok ((), σ'.toCSt 0) := by
      cases d with
      | once =>
        dsimp only at h ⊢
        rw [CM_bind_run] at h
        cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) (σ.toCSt 0) with
        | error e => rw [hl] at h; cases h
        | ok p =>
          rcases p with ⟨⟨⟩, s2⟩
          obtain ⟨rfl, hunsp⟩ := CM_forIn_checkOnceUnspent hl
          dsimp only [AState.toCSt] at hunsp
          have hunsp' : UnspentOnceDeps σ v.deps := by
            intro d hd ho
            have hne := hunsp d hd ho
            have hlt : d < σ.spent.size := by
              have hlt1 : d < σ.once.size :=
                Nat.lt_of_not_ge fun hge => by rw [Array.getElem?_eq_none hge] at ho; cases ho
              have h1 := hok.1; have h2 := hok.2.1; omega
            cases hsp : σ.spent[d]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp hsp) (Nat.not_le_of_lt hlt)
            | some b => cases b with
              | false => rfl
              | true => exact absurd hsp hne
          rw [hl] at h; dsimp only at h
          exact ⟨fun _ => hunsp', fun hne => absurd rfl hne, h⟩
      | lend | share | uniq _ =>
        dsimp only at h ⊢
        cases hoo : v.onceOnly with
        | true =>
          simp only [hoo, ↓reduceIte] at h
          rw [CM_bind_run, CM_refuseM_run] at h; cases h
        | false =>
          simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
          rw [CM_bind_run] at h
          cases hno : (notOnceSrc v w).run (σ.toCSt 0) with
          | error e => rw [hno] at h; cases h
          | ok p =>
            rcases p with ⟨⟨⟩, s2⟩
            obtain ⟨rfl, hnotOnce⟩ := CM_notOnceSrc_ok hno
            dsimp only [AState.toCSt] at hnotOnce
            rw [hno] at h; dsimp only at h
            exact ⟨fun hc => (by cases hc), fun _ => ⟨rfl, hnotOnce⟩, h⟩
    obtain ⟨hunspOnce, hnonOnce, h⟩ := hphase1
    -- Phase 2: mark once deps spent
    rw [CM_bind_run] at h
    cases hms : StateT.run (forIn (m := CM) v.deps PUnit.unit fun x _ => do
        if ← isOnceBnd x then markSpent x
        pure (ForInStep.yield PUnit.unit)) (σ.toCSt 0) with
    | error e => rw [hms] at h; cases h
    | ok p3 =>
      rcases p3 with ⟨⟨⟩, s3⟩
      rw [hms] at h; dsimp only at h
      obtain ⟨hst3, honce3, hreg3, hnr3, hsteps3, hszSp3, hsp3⟩ := CM_forIn_markSpentOnce hms
      dsimp only [AState.toCSt] at hst3 honce3 hreg3 hnr3 hsteps3 hszSp3 hsp3
      -- Phase 3 + Phase 4 (`match d` + `killSrc v`)
      have hskOnce : d = .once → exp.admitsNA v.skel = true := by
        intro hd; subst hd; exact hskOk
      have hskOther : d ≠ .once → exp.admits v.skel = true := by
        intro hne
        have hoo : v.onceOnly = false := (hnonOnce hne).1
        cases d with
        | once => exact absurd rfl hne
        | lend | share | uniq _ => simpa [hoo] using hskOk
      cases d with
      | lend =>
        dsimp only at h
        obtain ⟨honce4, hsp4, hreg4, hnr4, _, hszSt4, hst4⟩ := CM_killSrc_ok h
        dsimp only [AState.toCSt] at honce4 hsp4 hreg4 hnr4 hszSt4 hst4
        have hneO : Dest.lend ≠ Dest.once := fun hc => by cases hc
        have hoo : v.onceOnly = false := (hnonOnce hneO).1
        have hstEq : σ'.st = σ.st := by
          apply Array.ext
          · exact hszSt4.trans (congrArg Array.size hst3)
          · intro i hi1 hi2
            have hget := hst4 i (by rw [← hszSt4]; exact hi1)
            simp only [hoo, Bool.false_eq_true, false_and, ↓reduceIte, hst3] at hget
            have h1 : σ'.st[i]? = some σ'.st[i] := Array.getElem?_eq_getElem hi1
            have h2 : σ.st[i]? = some σ.st[i] := Array.getElem?_eq_getElem hi2
            rw [h1, h2] at hget; exact Option.some.inj hget
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok (hstEq ▸ rfl)
          (honce4.trans honce3) (by rw [hsp4]; exact hszSp3) (hreg4.trans hreg3) (hnr4.trans hnr3)
          (fun i hi => by rw [hstEq, Array.getElem?_eq_getElem hi]; exact BSt.le_refl _)
          (fun i hi hsp => by
            rw [hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
        exact ⟨hok', hle', hstEq ▸ rfl, honce4.trans honce3, by rw [hsp4]; exact hszSp3,
          hreg4.trans hreg3, hnr4.trans hnr3, hvd, fun hc => (by cases hc),
          fun _ => ⟨hskOther hneO, hoo, (hnonOnce hneO).2⟩,
          fun i hi => by rw [hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc], fun _ => hstEq,
          fun hc => (by cases hc), fun hc => (by cases hc), fun _ hc => (by cases hc)⟩
      | share =>
        dsimp only at h
        have hneO : Dest.share ≠ Dest.once := fun hc => by cases hc
        have hoo : v.onceOnly = false := (hnonOnce hneO).1
        simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
        have hphase3 :
            ∃ s4,
              (killSrc v).run s4 = .ok ((), σ'.toCSt 0) ∧
              s4.once = s3.once ∧ s4.spent = s3.spent ∧ s4.regions = s3.regions ∧
              s4.nextRegion = s3.nextRegion ∧ s4.steps = s3.steps ∧
              s4.st.size = s3.st.size ∧
              (∀ i, i < s3.st.size →
                s4.st[i]? = if v.cls = .val ∧ i ∈ v.deps ∧ s3.st[i]? = some .live then some .shared else s3.st[i]?) := by
          cases hcv : (v.cls == .val) with
          | false =>
            simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h
            have hneV : v.cls ≠ .val := fun heq => by rw [heq] at hcv; cases hcv
            exact ⟨s3, h, rfl, rfl, rfl, rfl, rfl, rfl, fun i _ => by simp [hneV]⟩
          | true =>
            have hcvEq : v.cls = .val := by
              cases hc : v.cls <;> try rfl
              all_goals (rw [hc] at hcv; cases hcv)
            simp only [hcv, ↓reduceIte] at h
            rw [CM_bind_run] at h
            cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit fun x _ => do
                if (← stOf x) == BSt.live then setSt x BSt.shared
                pure (ForInStep.yield PUnit.unit)) s3 with
            | error e => rw [hl] at h; cases h
            | ok p4 =>
              rcases p4 with ⟨⟨⟩, s4⟩
              rw [hl] at h; dsimp only at h
              obtain ⟨honce4, hsp4, hreg4, hnr4, hsteps4, hszSt4, hst4⟩ := CM_forIn_shareDeps hl
              exact ⟨s4, h, honce4, hsp4, hreg4, hnr4, hsteps4, hszSt4,
                fun i hi => by simpa [hcvEq] using hst4 i hi⟩
        obtain ⟨s4, hk4, honce4, hsp4, hreg4, hnr4, _, hszSt4, hst4⟩ := hphase3
        obtain ⟨honce5, hsp5, hreg5, hnr5, _, hszSt5, hst5⟩ := CM_killSrc_ok hk4
        dsimp only [AState.toCSt] at honce5 hsp5 hreg5 hnr5 hszSt5 hst5
        have hstPt : ∀ i, i < σ.st.size →
            σ'.st[i]? = if v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live then some .shared else σ.st[i]? := by
          intro i hi
          have hi4 : i < s4.st.size := by rw [hszSt4, hst3]; exact hi
          have h5 := hst5 i hi4
          simp only [hoo, Bool.false_eq_true, false_and, ↓reduceIte] at h5
          rw [h5, hst4 i (by rw [hst3]; exact hi), hst3]
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok
          (by rw [hszSt5, hszSt4, hst3]) (honce5.trans (honce4.trans honce3))
          (by rw [hsp5, hsp4]; exact hszSp3) (hreg5.trans (hreg4.trans hreg3))
          (hnr5.trans (hnr4.trans hnr3))
          (fun i hi => by
            rw [hstPt i hi]
            cases h0 : σ.st[i]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
            | some b0 =>
              by_cases hc : v.cls = .val ∧ i ∈ v.deps ∧ some b0 = some .live
              · simp only [hc, and_self, ↓reduceIte]; cases hc.2.2; exact trivial
              · simp only [hc, ↓reduceIte]; exact BSt.le_refl b0)
          (fun i hi hsp => by
            rw [hsp5, hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
        exact ⟨hok', hle', by rw [hszSt5, hszSt4, hst3], honce5.trans (honce4.trans honce3),
          by rw [hsp5, hsp4]; exact hszSp3, hreg5.trans (hreg4.trans hreg3),
          hnr5.trans (hnr4.trans hnr3), hvd, fun hc => (by cases hc),
          fun _ => ⟨hskOther hneO, hoo, (hnonOnce hneO).2⟩,
          fun i hi => by rw [hsp5, hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc], fun hc => (by cases hc),
          fun _ => hstPt, fun hc => (by cases hc), fun _ hc => (by cases hc)⟩
      | once =>
        dsimp only at h
        have hphase3 :
            ∃ s4,
              (killSrc v).run s4 = .ok ((), σ'.toCSt 0) ∧
              s4.once = s3.once ∧ s4.spent = s3.spent ∧ s4.regions = s3.regions ∧
              s4.nextRegion = s3.nextRegion ∧ s4.steps = s3.steps ∧
              s4.st.size = s3.st.size ∧
              (∀ i, i < s3.st.size →
                s4.st[i]? = if v.cls = .val ∧ i ∈ v.deps ∧ s3.st[i]? = some .live then some .shared else s3.st[i]?) := by
          cases hcv : (v.cls == .val) with
          | false =>
            simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h
            have hneV : v.cls ≠ .val := fun heq => by rw [heq] at hcv; cases hcv
            exact ⟨s3, h, rfl, rfl, rfl, rfl, rfl, rfl, fun i _ => by simp [hneV]⟩
          | true =>
            have hcvEq : v.cls = .val := by
              cases hc : v.cls <;> try rfl
              all_goals (rw [hc] at hcv; cases hcv)
            simp only [hcv, ↓reduceIte] at h
            rw [CM_bind_run] at h
            cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit fun x _ => do
                if (← stOf x) == BSt.live then setSt x BSt.shared
                pure (ForInStep.yield PUnit.unit)) s3 with
            | error e => rw [hl] at h; cases h
            | ok p4 =>
              rcases p4 with ⟨⟨⟩, s4⟩
              rw [hl] at h; dsimp only at h
              obtain ⟨honce4, hsp4, hreg4, hnr4, hsteps4, hszSt4, hst4⟩ := CM_forIn_shareDeps hl
              exact ⟨s4, h, honce4, hsp4, hreg4, hnr4, hsteps4, hszSt4,
                fun i hi => by simpa [hcvEq] using hst4 i hi⟩
        obtain ⟨s4, hk4, honce4, hsp4, hreg4, hnr4, _, hszSt4, hst4⟩ := hphase3
        obtain ⟨honce5, hsp5, hreg5, hnr5, _, hszSt5, hst5⟩ := CM_killSrc_ok hk4
        dsimp only [AState.toCSt] at honce5 hsp5 hreg5 hnr5 hszSt5 hst5
        have hstPt : ∀ i, i < σ.st.size →
            σ'.st[i]? = if v.onceOnly = true ∧ v.src = some i then some .dead
              else if v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live then some .shared else σ.st[i]? := by
          intro i hi
          have hi4 : i < s4.st.size := by rw [hszSt4, hst3]; exact hi
          rw [hst5 i hi4]
          by_cases hc : v.onceOnly = true ∧ v.src = some i
          · simp only [hc, and_self, ↓reduceIte]
          · simp only [hc, ↓reduceIte]; rw [hst4 i (by rw [hst3]; exact hi), hst3]
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok
          (by rw [hszSt5, hszSt4, hst3]) (honce5.trans (honce4.trans honce3))
          (by rw [hsp5, hsp4]; exact hszSp3) (hreg5.trans (hreg4.trans hreg3))
          (hnr5.trans (hnr4.trans hnr3))
          (fun i hi => by
            rw [hstPt i hi]
            cases h0 : σ.st[i]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
            | some b0 =>
              by_cases hc1 : v.onceOnly = true ∧ v.src = some i
              · simp only [hc1, and_self, ↓reduceIte]; cases b0 <;> trivial
              · simp only [hc1, ↓reduceIte]
                by_cases hc2 : v.cls = .val ∧ i ∈ v.deps ∧ some b0 = some .live
                · simp only [hc2, and_self, ↓reduceIte]; cases hc2.2.2; exact trivial
                · simp only [hc2, ↓reduceIte]; exact BSt.le_refl b0)
          (fun i hi hsp => by
            rw [hsp5, hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
        exact ⟨hok', hle', by rw [hszSt5, hszSt4, hst3], honce5.trans (honce4.trans honce3),
          by rw [hsp5, hsp4]; exact hszSp3, hreg5.trans (hreg4.trans hreg3),
          hnr5.trans (hnr4.trans hnr3), hvd, fun _ => ⟨hskOnce rfl, hunspOnce rfl⟩,
          fun hc => absurd rfl hc, fun i hi => by rw [hsp5, hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc],
          fun hc => (by cases hc), fun hc => (by cases hc), fun _ => hstPt,
          fun _ hc => (by cases hc)⟩
      | uniq b =>
        dsimp only at h
        have hneO : Dest.uniq b ≠ Dest.once := fun hc => by cases hc
        have hoo : v.onceOnly = false := (hnonOnce hneO).1
        simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
        have hphase3 :
            ∃ s4,
              (killSrc v).run s4 = .ok ((), σ'.toCSt 0) ∧
              (v.cls = .val → v.own = .uniq ∧ (∀ x ∈ v.deps, s3.st[x]? = some .live) ∧
                (b = false → v.regs = [])) ∧
              s4.once = s3.once ∧ s4.spent = s3.spent ∧ s4.regions = s3.regions ∧
              s4.nextRegion = s3.nextRegion ∧ s4.steps = s3.steps ∧
              s4.st.size = s3.st.size ∧
              (∀ i, i < s3.st.size → s4.st[i]? = if v.cls = .val ∧ i ∈ v.deps then some .dead else s3.st[i]?) := by
          cases hcv : (v.cls == .val) with
          | false =>
            simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h
            have hneV : v.cls ≠ .val := fun heq => by rw [heq] at hcv; cases hcv
            exact ⟨s3, h, fun hv => absurd hv hneV, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp [hneV]⟩
          | true =>
            have hcvEq : v.cls = .val := by
              cases hc : v.cls <;> try rfl
              all_goals (rw [hc] at hcv; cases hcv)
            simp only [hcv, ↓reduceIte] at h
            rw [CM_bind_run] at h
            cases hiu : (isUniq v).run s3 with
            | error e => rw [hiu] at h; cases h
            | ok pu =>
              rcases pu with ⟨uRes, su⟩
              obtain ⟨hsuEq, huIff⟩ := CM_isUniq_ok hiu
              rw [hiu, hsuEq] at h; dsimp only at h
              cases uRes with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h
                rw [CM_bind_run, CM_refuseM_run] at h; cases h
              | true =>
                have ⟨hownEq, hlive⟩ : v.own = .uniq ∧ ∀ x ∈ v.deps, s3.st[x]? = some .live := by
                  rcases huIff.mp rfl with hne | hokU
                  · exact absurd hcvEq hne
                  · exact hokU
                simp only [↓reduceIte] at h
                have hregsOk : (!b && !v.regs.isEmpty) = false := by
                  cases hbr : (!b && !v.regs.isEmpty) with
                  | false => rfl
                  | true =>
                    simp only [hbr, ↓reduceIte] at h
                    rw [CM_bind_run, CM_refuseM_run] at h; cases h
                have hregsNil : b = false → v.regs = [] := by
                  intro hbf; subst hbf
                  cases hr : v.regs with
                  | nil => rfl
                  | cons _ _ => simp [hr] at hregsOk
                simp only [hregsOk, Bool.false_eq_true, ↓reduceIte] at h
                rw [CM_bind_run] at h
                cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit fun x _ => do
                    setSt x BSt.dead
                    pure (ForInStep.yield PUnit.unit)) s3 with
                | error e => rw [hl] at h; cases h
                | ok p4 =>
                  rcases p4 with ⟨⟨⟩, s4⟩
                  rw [hl] at h; dsimp only at h
                  obtain ⟨honce4, hsp4, hreg4, hnr4, hsteps4, hszSt4, hst4⟩ := CM_forIn_killDeps hl
                  exact ⟨s4, h, fun _ => ⟨hownEq, hlive, hregsNil⟩, honce4, hsp4, hreg4, hnr4,
                    hsteps4, hszSt4, fun i hi => by simpa [hcvEq] using hst4 i hi⟩
        obtain ⟨s4, hk4, huniqProps, honce4, hsp4, hreg4, hnr4, _, hszSt4, hst4⟩ := hphase3
        obtain ⟨honce5, hsp5, hreg5, hnr5, _, hszSt5, hst5⟩ := CM_killSrc_ok hk4
        dsimp only [AState.toCSt] at honce5 hsp5 hreg5 hnr5 hszSt5 hst5
        have hstPt : ∀ i, i < σ.st.size →
            σ'.st[i]? = if v.cls = .val ∧ i ∈ v.deps then some .dead else σ.st[i]? := by
          intro i hi
          have hi4 : i < s4.st.size := by rw [hszSt4, hst3]; exact hi
          have h5 := hst5 i hi4
          simp only [hoo, Bool.false_eq_true, false_and, ↓reduceIte] at h5
          rw [h5, hst4 i (by rw [hst3]; exact hi), hst3]
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok
          (by rw [hszSt5, hszSt4, hst3]) (honce5.trans (honce4.trans honce3))
          (by rw [hsp5, hsp4]; exact hszSp3) (hreg5.trans (hreg4.trans hreg3))
          (hnr5.trans (hnr4.trans hnr3))
          (fun i hi => by
            rw [hstPt i hi]
            cases h0 : σ.st[i]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
            | some b0 =>
              by_cases hc : v.cls = .val ∧ i ∈ v.deps
              · simp only [hc, and_self, ↓reduceIte]; cases b0 <;> trivial
              · simp only [hc, ↓reduceIte]; exact BSt.le_refl b0)
          (fun i hi hsp => by
            rw [hsp5, hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
        refine ⟨hok', hle', by rw [hszSt5, hszSt4, hst3], honce5.trans (honce4.trans honce3),
          by rw [hsp5, hsp4]; exact hszSp3, hreg5.trans (hreg4.trans hreg3),
          hnr5.trans (hnr4.trans hnr3), hvd, fun hc => (by cases hc),
          fun _ => ⟨hskOther hneO, hoo, (hnonOnce hneO).2⟩,
          fun i hi => by rw [hsp5, hsp4, hsp3 i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc], fun hc => (by cases hc),
          fun hc => (by cases hc), fun hc => (by cases hc), fun b' hbEq => ?_⟩
        cases hbEq
        exact ⟨fun hcv => by simpa [hst3] using huniqProps hcv, hstPt⟩

/-- Complete unpacking of `Check.bindInner` (`Runs (bindInner m cls v s w) σ bv σ'`). -/
theorem Runs_bindInner {m : BinderMode} {cls : Cls} {v : AVal} {s : Nat} {w : String}
    {σ σ' : AState} {bv : AVal}
    (hok : AStateOk σ) (h : Runs (bindInner m cls v s w) σ bv σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    (m.usage ≠ .once → ¬ IsOnceSrc σ v) ∧
    (m ≠ .erased → ValidDeps σ v.deps) ∧
    (m.isUnique = true → v.onceOnly = false ∧
      (v.cls = .val → v.own = .uniq ∧ (∀ x ∈ v.deps, σ.st[x]? = some .live) ∧
        (m.isBorrowed = false → v.regs = []))) ∧
    (m.usage = .once → UnspentOnceDeps σ v.deps) ∧
    (∀ i, i < σ.spent.size →
      σ'.spent[i]? = if (m.isUnique = true ∨ m.usage = .once) ∧ i ∈ v.deps ∧ σ.once[i]? = some true
        then some true else σ.spent[i]?) ∧
    (∀ i, i < σ.st.size →
      σ'.st[i]? =
        if m.isUnique = true ∧ v.cls = .val ∧ i ∈ v.deps then some .dead
        else if v.onceOnly = true ∧ v.src = some i then some .dead
        else if m.usage = .once ∧ v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live then some .shared
        else σ.st[i]?) ∧
    bv = (let r : AVal := match m with
      | .erased => { cls := .irr }
      | .unique => { cls, own := .uniq, regs := [], skel := v.skel }
      | .uniqueBorrowed => { cls, own := .uniq, regs := natUnion v.regs [s], skel := v.skel }
      | .borrowed => { v with cls, regs := natUnion v.regs [s], src := none }
      | .once => { v with cls, src := none }
      | .onceBorrowed => { v with cls, regs := natUnion v.regs [s], src := none }
      | .many => { v with cls, src := none }
      if cls == .leaf then { r with regs := [] } else r) := by
  unfold Runs bindInner at h
  have hstep1 :
      (m.usage ≠ .once → ¬ IsOnceSrc σ v) ∧
      ((do
        let r ← bindInnerBase m cls v s w
        killSrc v
        pure r) : CM AVal).run (σ.toCSt 0) = .ok (bv, σ'.toCSt 0) := by
    cases hmu : (m.usage != .once) with
    | false =>
      have hmo : m.usage = .once := by cases m <;> simp [BinderMode.usage] at hmu ⊢
      simp only [hmu, Bool.false_eq_true, ↓reduceIte] at h
      exact ⟨fun hne => absurd hmo hne, h⟩
    | true =>
      simp only [hmu, ↓reduceIte] at h
      rw [CM_bind_run] at h
      cases hno : (notOnceSrc v w).run (σ.toCSt 0) with
      | error e => rw [hno] at h; cases h
      | ok p =>
        rcases p with ⟨⟨⟩, s1⟩
        obtain ⟨rfl, hno'⟩ := CM_notOnceSrc_ok hno
        rw [hno] at h; dsimp only at h
        exact ⟨fun _ => hno', h⟩
  have hnotOnce : (m.usage ≠ .once → ¬ IsOnceSrc σ v) := hstep1.1
  have h := hstep1.2
  unfold bindInnerBase bindInnerRegs at h
  rw [CM_bind_run, CM_bind_run] at h
  cases m with
  | erased =>
    dsimp only at h ⊢
    rw [CM_pure_run] at h; dsimp only at h
    rw [CM_pure_run] at h; dsimp only at h
    rw [CM_bind_run] at h
    cases hk : (killSrc v).run (σ.toCSt 0) with
    | error e => rw [hk] at h; cases h
    | ok pk =>
      rcases pk with ⟨⟨⟩, sk⟩
      rw [hk] at h; dsimp only at h
      rw [CM_pure_run] at h; cases h
      obtain ⟨honceK, hspK, hregK, hnrK, _, hszStK, hstK⟩ := CM_killSrc_ok hk
      dsimp only [AState.toCSt] at honceK hspK hregK hnrK hszStK hstK
      have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok hszStK honceK (by rw [hspK]) hregK hnrK
        (fun i hi => by
          rw [hstK i hi]
          cases h0 : σ.st[i]? with
          | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
          | some b0 =>
            by_cases hc : v.onceOnly = true ∧ v.src = some i
            · simp only [hc, and_self, ↓reduceIte]; cases b0 <;> trivial
            · simp only [hc, ↓reduceIte]; exact BSt.le_refl b0)
        (fun i _ hsp => by rw [hspK]; exact hsp)
      refine ⟨hok', hle', hszStK, honceK, by rw [hspK], hregK, hnrK, hnotOnce,
        fun hc => absurd rfl hc, fun hc => (by cases hc), fun hc => (by cases hc),
        fun i _ => by rw [hspK]; simp [BinderMode.isUnique, BinderMode.usage],
        fun i hi => by rw [hstK i hi]; simp [BinderMode.isUnique, BinderMode.usage],
        by cases cls <;> rfl⟩
  | unique | uniqueBorrowed =>
    dsimp only at h ⊢
    rw [CM_bind_run] at h
    cases hfl : (flowTo (.uniq _) v.skel v w).run (σ.toCSt 0) with
    | error e => rw [hfl] at h; cases h
    | ok pf =>
      rcases pf with ⟨⟨⟩, sf⟩
      rw [hfl] at h; dsimp only at h
      rw [CM_pure_run] at h; dsimp only at h
      rw [CM_pure_run] at h; dsimp only at h
      rw [CM_bind_run] at h
      cases hk : (killSrc v).run sf with
      | error e => rw [hk] at h; cases h
      | ok pk =>
        rcases pk with ⟨⟨⟩, sk⟩
        rw [hk] at h; dsimp only at h
        rw [CM_pure_run] at h; cases h
        obtain ⟨honceK, hspK, hregK, hnrK, hstepsK, hszStK, hstK⟩ := CM_killSrc_ok hk
        dsimp only [AState.toCSt] at honceK hspK hregK hnrK hstepsK hszStK hstK
        obtain ⟨_, _, hszStF, honceF, hszSpF, hregF, hnrF, hvd, _, hnonOnceF, hspF, _, _, _, huniqF⟩ :=
          Runs_flowTo hok (by
            unfold Runs; rw [show (AState.ofCSt sf).toCSt 0 = sf by rw [hstepsK, AState.toCSt_ofCSt]]; exact hfl)
        obtain ⟨huProps, hstF⟩ := huniqF _ rfl
        dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstF
        have hoo : v.onceOnly = false := (hnonOnceF (fun hc => by cases hc)).2.1
        have hstPt : ∀ i, i < σ.st.size →
            σ'.st[i]? = if v.cls = .val ∧ i ∈ v.deps then some .dead else σ.st[i]? := by
          intro i hi
          have hiF : i < sf.st.size := by rw [hszStF]; exact hi
          have h1 := hstK i hiF
          simp only [hoo, Bool.false_eq_true, false_and, ↓reduceIte] at h1
          exact h1.trans (hstF i hi)
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok (hszStK.trans hszStF)
          (honceK.trans honceF) (by rw [hspK]; exact hszSpF) (hregK.trans hregF) (hnrK.trans hnrF)
          (fun i hi => by
            rw [hstPt i hi]
            cases h0 : σ.st[i]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
            | some b0 =>
              by_cases hc : v.cls = .val ∧ i ∈ v.deps
              · simp only [hc, and_self, ↓reduceIte]; cases b0 <;> trivial
              · simp only [hc, ↓reduceIte]; exact BSt.le_refl b0)
          (fun i hi hsp => by
            rw [hspK, hspF i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
        refine ⟨hok', hle', hszStK.trans hszStF, honceK.trans honceF, by rw [hspK]; exact hszSpF,
          hregK.trans hregF, hnrK.trans hnrF, hnotOnce, fun _ => hvd,
          fun _ => ⟨hoo, huProps⟩, fun hc => (by cases hc),
          fun i hi => by rw [hspK, hspF i hi]; simp [BinderMode.isUnique],
          fun i hi => by rw [hstPt i hi]; simp [BinderMode.isUnique, BinderMode.usage, hoo], ?_⟩
        cases cls <;> rfl
  | borrowed | many =>
    dsimp only at h ⊢
    rw [CM_bind_run] at h
    cases hval : (valid v w).run (σ.toCSt 0) with
    | error e => rw [hval] at h; cases h
    | ok pv =>
      rcases pv with ⟨⟨⟩, sv⟩
      obtain ⟨rfl, hvd⟩ := CM_valid_ok hval
      dsimp only [AState.toCSt] at hvd
      rw [hval] at h; dsimp only at h
      rw [CM_pure_run] at h; dsimp only at h
      rw [CM_pure_run] at h; dsimp only at h
      rw [CM_bind_run] at h
      cases hk : (killSrc v).run (σ.toCSt 0) with
      | error e => rw [hk] at h; cases h
      | ok pk =>
        rcases pk with ⟨⟨⟩, sk⟩
        rw [hk] at h; dsimp only at h
        rw [CM_pure_run] at h; cases h
        obtain ⟨honceK, hspK, hregK, hnrK, _, hszStK, hstK⟩ := CM_killSrc_ok hk
        dsimp only [AState.toCSt] at honceK hspK hregK hnrK hszStK hstK
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok hszStK honceK (by rw [hspK]) hregK hnrK
          (fun i hi => by
            rw [hstK i hi]
            cases h0 : σ.st[i]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
            | some b0 =>
              by_cases hc : v.onceOnly = true ∧ v.src = some i
              · simp only [hc, and_self, ↓reduceIte]; cases b0 <;> trivial
              · simp only [hc, ↓reduceIte]; exact BSt.le_refl b0)
          (fun i _ hsp => by rw [hspK]; exact hsp)
        refine ⟨hok', hle', hszStK, honceK, by rw [hspK], hregK, hnrK, hnotOnce, fun _ => hvd,
          fun hc => (by cases hc), fun hc => (by cases hc),
          fun i _ => by rw [hspK]; simp [BinderMode.isUnique, BinderMode.usage],
          fun i hi => by rw [hstK i hi]; simp [BinderMode.isUnique, BinderMode.usage], ?_⟩
        cases cls <;> rfl
  | once | onceBorrowed =>
    dsimp only at h ⊢
    rw [CM_bind_run] at h
    cases hfl : (flowTo .once v.skel v w).run (σ.toCSt 0) with
    | error e => rw [hfl] at h; cases h
    | ok pf =>
      rcases pf with ⟨⟨⟩, sf⟩
      rw [hfl] at h; dsimp only at h
      rw [CM_pure_run] at h; dsimp only at h
      rw [CM_pure_run] at h; dsimp only at h
      rw [CM_bind_run] at h
      cases hk : (killSrc v).run sf with
      | error e => rw [hk] at h; cases h
      | ok pk =>
        rcases pk with ⟨⟨⟩, sk⟩
        rw [hk] at h; dsimp only at h
        rw [CM_pure_run] at h; cases h
        obtain ⟨honceK, hspK, hregK, hnrK, hstepsK, hszStK, hstK⟩ := CM_killSrc_ok hk
        dsimp only [AState.toCSt] at honceK hspK hregK hnrK hstepsK hszStK hstK
        have hflR : Runs (flowTo .once v.skel v w) σ () (AState.ofCSt sf) := by
          unfold Runs; rw [show (AState.ofCSt sf).toCSt 0 = sf by rw [hstepsK, AState.toCSt_ofCSt]]; exact hfl
        obtain ⟨_, _, hszStF, honceF, hszSpF, hregF, hnrF, hvd, honceFProps, _, hspF, _, _, hstOnceF, _⟩ :=
          Runs_flowTo hok hflR
        dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstOnceF
        have hstPt : ∀ i, i < σ.st.size →
            σ'.st[i]? =
              if v.onceOnly = true ∧ v.src = some i then some .dead
              else if v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live then some .shared
              else σ.st[i]? := by
          intro i hi
          have hiF : i < sf.st.size := by rw [hszStF]; exact hi
          rw [hstK i hiF]
          by_cases hc : v.onceOnly = true ∧ v.src = some i
          · simp only [hc, and_self, ↓reduceIte]
          · simp only [hc, ↓reduceIte]
            have h1 := hstOnceF rfl i hi
            simp only [hc, ↓reduceIte] at h1
            exact h1
        have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok (hszStK.trans hszStF)
          (honceK.trans honceF) (by rw [hspK]; exact hszSpF) (hregK.trans hregF) (hnrK.trans hnrF)
          (fun i hi => by
            rw [hstPt i hi]
            cases h0 : σ.st[i]? with
            | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
            | some b0 =>
              by_cases hc1 : v.onceOnly = true ∧ v.src = some i
              · simp only [hc1, and_self, ↓reduceIte]; cases b0 <;> trivial
              · simp only [hc1, ↓reduceIte]
                by_cases hc2 : v.cls = .val ∧ i ∈ v.deps ∧ some b0 = some .live
                · simp only [hc2, and_self, ↓reduceIte]; cases hc2.2.2; exact trivial
                · simp only [hc2, ↓reduceIte]; exact BSt.le_refl b0)
          (fun i hi hsp => by
            rw [hspK, hspF i hi]; by_cases hc : i ∈ v.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
        refine ⟨hok', hle', hszStK.trans hszStF, honceK.trans honceF, by rw [hspK]; exact hszSpF,
          hregK.trans hregF, hnrK.trans hnrF, hnotOnce, fun _ => hvd,
          fun hc => (by cases hc), fun _ => (honceFProps rfl).2,
          fun i hi => by rw [hspK, hspF i hi]; simp [BinderMode.usage],
          fun i hi => by rw [hstPt i hi]; simp [BinderMode.isUnique, BinderMode.usage], ?_⟩
        cases cls <;> rfl

/-- Complete unpacking of `Check.retCheck` (`Runs (retCheck exp res s r w) σ () σ'`). -/
theorem Runs_retCheck {exp : Skel} {res : ResultMode} {s : Nat} {r : AVal} {w : String}
    {σ σ' : AState} (hok : AStateOk σ) (h : Runs (retCheck exp res s r w) σ () σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent = σ.spent ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    ValidDeps σ r.deps ∧
    exp.admits r.skel = true ∧
    r.onceOnly = false ∧
    ¬ IsOnceSrc σ r ∧
    (r.cls = .val →
      ((res = .shared ∨ res = .unique) → s ∉ r.regs) ∧
      (res = .unique → r.regs = []) ∧
      (res.isUnique = true → r.own = .uniq ∧ ∀ x ∈ r.deps, σ.st[x]? = some .live)) ∧
    (∀ i, i < σ.st.size →
      σ'.st[i]? = if r.cls = .val ∧ res.isUnique = true ∧ i ∈ r.deps then some .dead else σ.st[i]?) := by
  unfold Runs retCheck at h
  rw [CM_bind_run] at h
  cases hval : (valid r w).run (σ.toCSt 0) with
  | error e => rw [hval] at h; cases h
  | ok p1 =>
    rcases p1 with ⟨⟨⟩, s1⟩
    obtain ⟨rfl, hvd⟩ := CM_valid_ok hval
    dsimp only [AState.toCSt] at hvd
    rw [hval] at h; dsimp only at h
    have hadm : exp.admits r.skel = true := by
      cases ha : exp.admits r.skel with
      | true => rfl
      | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
    simp only [hadm, ↓reduceIte] at h
    have hoo : r.onceOnly = false := by
      cases ho : r.onceOnly with
      | false => rfl
      | true => simp only [ho, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
    simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
    rw [CM_bind_run] at h
    cases hno : (notOnceSrc r w).run (σ.toCSt 0) with
    | error e => rw [hno] at h; cases h
    | ok p2 =>
      rcases p2 with ⟨⟨⟩, s2⟩
      obtain ⟨rfl, hnotOnce⟩ := CM_notOnceSrc_ok hno
      rw [hno] at h; dsimp only at h
      cases hcv : (r.cls == .val) with
      | false =>
        simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h
        rw [CM_pure_run] at h
        have hneV : r.cls ≠ .val := fun heq => by rw [heq] at hcv; cases hcv
        have hEq : σ' = σ := (Runs_ok_eq h).2.symm
        subst hEq
        exact ⟨hok, AStateLe.refl _, rfl, rfl, rfl, rfl, rfl, hvd, hadm, hoo, hnotOnce,
          fun hv => absurd hv hneV, fun _ _ => by simp [hneV]⟩
      | true =>
        have hcvEq : r.cls = .val := by
          cases hc : r.cls <;> try rfl
          all_goals (rw [hc] at hcv; cases hcv)
        simp only [hcv, ↓reduceIte] at h
        cases res with
        | shared =>
          dsimp only at h
          have hns : s ∉ r.regs := by
            intro hm
            have hc : r.regs.contains s = true := List.contains_iff_mem.mpr hm
            simp only [hc, ↓reduceIte] at h; rw [CM_refuseM_run] at h; cases h
          have hcf : r.regs.contains s = false := by
            cases hc : r.regs.contains s with
            | false => rfl
            | true => exact absurd (List.contains_iff_mem.mp hc) hns
          simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
          rw [CM_pure_run] at h
          have hEq : σ' = σ := (Runs_ok_eq h).2.symm
          subst hEq
          exact ⟨hok, AStateLe.refl _, rfl, rfl, rfl, rfl, rfl, hvd, hadm, hoo, hnotOnce,
            fun _ => ⟨fun _ => hns, fun hc => (by cases hc), fun hc => (by cases hc)⟩,
            fun _ _ => by simp [ResultMode.isUnique]⟩
        | borrowed =>
          dsimp only at h; rw [CM_pure_run] at h
          have hEq : σ' = σ := (Runs_ok_eq h).2.symm
          subst hEq
          exact ⟨hok, AStateLe.refl _, rfl, rfl, rfl, rfl, rfl, hvd, hadm, hoo, hnotOnce,
            fun _ => ⟨fun hc => (by rcases hc with hc | hc <;> cases hc),
              fun hc => (by cases hc), fun hc => (by cases hc)⟩,
            fun _ _ => by simp [ResultMode.isUnique]⟩
        | unique =>
          dsimp only at h
          have hns : s ∉ r.regs := by
            intro hm
            have hc : r.regs.contains s = true := List.contains_iff_mem.mpr hm
            simp only [hc, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
          have hcf : r.regs.contains s = false := by
            cases hc : r.regs.contains s with
            | false => rfl
            | true => exact absurd (List.contains_iff_mem.mp hc) hns
          simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
          rw [CM_bind_run] at h
          cases hiu : (isUniq r).run (σ.toCSt 0) with
          | error e => rw [hiu] at h; cases h
          | ok pu =>
            rcases pu with ⟨uRes, su⟩
            obtain ⟨rfl, huIff⟩ := CM_isUniq_ok hiu
            rw [hiu] at h; dsimp only at h
            cases uRes with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              rw [CM_bind_run, CM_refuseM_run] at h; cases h
            | true =>
              simp only [↓reduceIte] at h
              have ⟨hownEq, hlive⟩ : r.own = .uniq ∧ ∀ x ∈ r.deps, σ.st[x]? = some .live := by
                rcases huIff.mp rfl with hne | hokU
                · exact absurd hcvEq hne
                · exact hokU
              have hregsNil : r.regs = [] := by
                cases hr : r.regs with
                | nil => rfl
                | cons _ _ =>
                  simp only [hr, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
                  rw [CM_bind_run, CM_refuseM_run] at h; cases h
              simp only [hregsNil, List.isEmpty_nil, ↓reduceIte] at h
              rw [CM_bind_run] at h
              cases hl : StateT.run (forIn (m := CM) r.deps PUnit.unit fun x _ => do
                  setSt x BSt.dead
                  pure (ForInStep.yield PUnit.unit)) (σ.toCSt 0) with
              | error e => rw [hl] at h; cases h
              | ok pk =>
                rcases pk with ⟨⟨⟩, sk⟩
                rw [hl] at h; dsimp only at h; rw [CM_pure_run] at h
                have hskEq : sk = σ'.toCSt 0 := congrArg Prod.snd (Except.ok.inj h)
                subst hskEq
                obtain ⟨honceK, hspK, hregK, hnrK, _, hszStK, hstK⟩ := CM_forIn_killDeps hl
                dsimp only [AState.toCSt] at honceK hspK hregK hnrK hszStK hstK
                have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok hszStK honceK (by rw [hspK]) hregK hnrK
                  (fun i hi => by
                    rw [hstK i hi]
                    cases h0 : σ.st[i]? with
                    | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
                    | some b0 =>
                      by_cases hmem : i ∈ r.deps
                      · simp only [hmem, ↓reduceIte]; cases b0 <;> trivial
                      · simp only [hmem, ↓reduceIte]; exact BSt.le_refl b0)
                  (fun i _ hsp => by rw [hspK]; exact hsp)
                exact ⟨hok', hle', hszStK, honceK, hspK, hregK, hnrK, hvd, hadm, hoo, hnotOnce,
                  fun _ => ⟨fun _ => hns, fun _ => hregsNil, fun _ => ⟨hownEq, hlive⟩⟩,
                  fun i hi => by simpa [hcvEq, ResultMode.isUnique] using hstK i hi⟩
        | uniqueBorrowed =>
          dsimp only at h
          rw [CM_bind_run] at h
          cases hiu : (isUniq r).run (σ.toCSt 0) with
          | error e => rw [hiu] at h; cases h
          | ok pu =>
            rcases pu with ⟨uRes, su⟩
            obtain ⟨rfl, huIff⟩ := CM_isUniq_ok hiu
            rw [hiu] at h; dsimp only at h
            cases uRes with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              rw [CM_bind_run, CM_refuseM_run] at h; cases h
            | true =>
              simp only [↓reduceIte] at h
              have ⟨hownEq, hlive⟩ : r.own = .uniq ∧ ∀ x ∈ r.deps, σ.st[x]? = some .live := by
                rcases huIff.mp rfl with hne | hokU
                · exact absurd hcvEq hne
                · exact hokU
              rw [CM_bind_run] at h
              cases hl : StateT.run (forIn (m := CM) r.deps PUnit.unit fun x _ => do
                  setSt x BSt.dead
                  pure (ForInStep.yield PUnit.unit)) (σ.toCSt 0) with
              | error e => rw [hl] at h; cases h
              | ok pk =>
                rcases pk with ⟨⟨⟩, sk⟩
                rw [hl] at h; dsimp only at h; rw [CM_pure_run] at h
                have hskEq : sk = σ'.toCSt 0 := congrArg Prod.snd (Except.ok.inj h)
                subst hskEq
                obtain ⟨honceK, hspK, hregK, hnrK, _, hszStK, hstK⟩ := CM_forIn_killDeps hl
                dsimp only [AState.toCSt] at honceK hspK hregK hnrK hszStK hstK
                have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok hszStK honceK (by rw [hspK]) hregK hnrK
                  (fun i hi => by
                    rw [hstK i hi]
                    cases h0 : σ.st[i]? with
                    | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hi)
                    | some b0 =>
                      by_cases hmem : i ∈ r.deps
                      · simp only [hmem, ↓reduceIte]; cases b0 <;> trivial
                      · simp only [hmem, ↓reduceIte]; exact BSt.le_refl b0)
                  (fun i _ hsp => by rw [hspK]; exact hsp)
                exact ⟨hok', hle', hszStK, honceK, hspK, hregK, hnrK, hvd, hadm, hoo, hnotOnce,
                  fun _ => ⟨fun hc => (by rcases hc with hc | hc <;> cases hc),
                    fun hc => (by cases hc), fun _ => ⟨hownEq, hlive⟩⟩,
                  fun i hi => by simpa [hcvEq, ResultMode.isUnique] using hstK i hi⟩

/-- Complete unpacking of `Check.anProj` (`Runs (anProj P s i v c) σ res σ'`). -/
theorem Runs_anProj {P : Prog} {s : Ref} {i : Nat} {v res : AVal} {c : Cls} {σ σ' : AState}
    (h : Runs (anProj P s i v c) σ res σ') :
    σ' = σ ∧
    (∀ ctor ind ci nP fields f,
      (P.ctorsOf s)[0]? = some ctor →
      P.ctorOf? ctor = some (ind, ci, nP, fields) →
      fields[i]? = some f →
      f.mode ≠ .erased ∧
      (f.cls = .irr ∨ c = .irr → res = { cls := .irr }) ∧
      (f.cls ≠ .irr → (c = .imm ∨ c = .leaf) → res = { cls := c }) ∧
      (f.cls ≠ .irr → c = .val → v.cls ≠ .val → res = { v with cls := c, src := none }) ∧
      (f.cls ≠ .irr → c = .val → v.cls = .val →
        res = { cls := c, deps := v.deps, regs := v.regs, skel := .unknown })) := by
  unfold Runs anProj at h
  dsimp only at h
  cases hcs0 : (P.ctorsOf s)[0]? with
  | none =>
    simp only [hcs0] at h
    have hnil : (#[] : Array Field)[i]? = none := by simp
    simp only [hnil] at h
    rw [CM_pure_run] at h
    exact ⟨(Runs_ok_eq h).2.symm, fun _ _ _ _ _ _ h1 => by cases h1⟩
  | some ctor =>
    simp only [hcs0] at h
    cases hco : P.ctorOf? ctor with
    | none =>
      simp only [hco] at h
      have hnil : (#[] : Array Field)[i]? = none := by simp
      simp only [hnil] at h
      rw [CM_pure_run] at h
      exact ⟨(Runs_ok_eq h).2.symm, fun _ _ _ _ _ _ h1 h2 => by cases h1; rw [hco] at h2; cases h2⟩
    | some q =>
      rcases q with ⟨ind, ci, nP, fields⟩
      simp only [hco] at h
      cases hf : fields[i]? with
      | none =>
        simp only [hf] at h
        rw [CM_pure_run] at h
        exact ⟨(Runs_ok_eq h).2.symm, fun _ _ _ _ _ _ h1 h2 h3 => by
          cases h1; rw [hco] at h2; cases h2; rw [hf] at h3; cases h3⟩
      | some f =>
        simp only [hf] at h
        have hneEr : f.mode ≠ .erased := by
          intro heq
          have hb : (f.mode == .erased) = true := by rw [heq]; rfl
          simp only [hb, ↓reduceIte] at h
          rw [CM_bind_run, CM_refuseM_run] at h; cases h
        have hneErB : (f.mode == .erased) = false := beq_false_of_ne hneEr
        simp only [hneErB, Bool.false_eq_true, ↓reduceIte] at h
        cases hirr : (f.cls == .irr || c == .irr) with
        | true =>
          simp only [hirr, ↓reduceIte] at h; rw [CM_pure_run] at h
          obtain ⟨h1, h2⟩ := Runs_ok_eq h
          have hdisj : f.cls = .irr ∨ c = .irr := by
            cases hfc : f.cls <;> cases hcc : c <;>
              (rw [hfc, hcc] at hirr; first | exact Or.inl rfl | exact Or.inr rfl | cases hirr)
          refine ⟨h2.symm, fun ctor' ind' ci' nP' fields' f' h1' h2' h3' => ?_⟩
          cases h1'; rw [hco] at h2'; cases h2'; rw [hf] at h3'; cases h3'
          exact ⟨hneEr, fun _ => h1.symm, (fun hnf hcIL => by
              rcases hdisj with hf0 | hc0
              · exact absurd hf0 hnf
              · rcases hcIL with h | h <;> (rw [hc0] at h; cases h)),
            (fun hnf hcV _ => by
              rcases hdisj with hf0 | hc0
              · exact absurd hf0 hnf
              · rw [hc0] at hcV; cases hcV),
            (fun hnf hcV _ => by
              rcases hdisj with hf0 | hc0
              · exact absurd hf0 hnf
              · rw [hc0] at hcV; cases hcV)⟩
        | false =>
          simp only [hirr, Bool.false_eq_true, ↓reduceIte] at h
          have hnfIrr : f.cls ≠ .irr := fun heq => by rw [heq] at hirr; cases hirr
          have hncIrr : c ≠ .irr := fun heq => by rw [heq] at hirr; simp [show (Cls.irr == Cls.irr) = true from rfl] at hirr
          cases hcIL : (c == .imm || c == .leaf) with
          | true =>
            simp only [hcIL, ↓reduceIte] at h; rw [CM_pure_run] at h
            obtain ⟨h1, h2⟩ := Runs_ok_eq h
            have hncV : c ≠ .val := fun heq => by rw [heq] at hcIL; cases hcIL
            refine ⟨h2.symm, fun ctor' ind' ci' nP' fields' f' h1' h2' h3' => ?_⟩
            cases h1'; rw [hco] at h2'; cases h2'; rw [hf] at h3'; cases h3'
            exact ⟨hneEr, fun hd => (by rcases hd with h | h; exact absurd h hnfIrr; exact absurd h hncIrr),
              fun _ _ => h1.symm, fun _ hcV _ => absurd hcV hncV,
              fun _ hcV _ => absurd hcV hncV⟩
          | false =>
            simp only [hcIL, Bool.false_eq_true, ↓reduceIte] at h
            have hcVal : c = .val := by
              cases hc : c <;> try rfl
              · exact absurd hc hncIrr
              · rw [hc] at hcIL; cases hcIL
              · rw [hc] at hcIL; cases hcIL
            cases hvNe : (v.cls != .val) with
            | true =>
              simp only [hvNe, ↓reduceIte] at h; rw [CM_pure_run] at h
              obtain ⟨h1, h2⟩ := Runs_ok_eq h
              have hvN : v.cls ≠ .val := fun heq => by rw [heq] at hvNe; cases hvNe
              refine ⟨h2.symm, fun ctor' ind' ci' nP' fields' f' h1' h2' h3' => ?_⟩
              cases h1'; rw [hco] at h2'; cases h2'; rw [hf] at h3'; cases h3'
              exact ⟨hneEr, fun hd => (by rcases hd with h | h; exact absurd h hnfIrr; exact absurd h hncIrr),
                fun _ hIL => (by rcases hIL with h | h <;> (rw [hcVal] at h; cases h)),
                fun _ _ _ => h1.symm, fun _ _ hvV => absurd hvV hvN⟩
            | false =>
              simp only [hvNe, Bool.false_eq_true, ↓reduceIte] at h
              have hvVal : v.cls = .val := by
                cases hvc : v.cls <;> try rfl
                all_goals (rw [hvc] at hvNe; cases hvNe)
              rw [CM_pure_run] at h
              obtain ⟨h1, h2⟩ := Runs_ok_eq h
              refine ⟨h2.symm, fun ctor' ind' ci' nP' fields' f' h1' h2' h3' => ?_⟩
              cases h1'; rw [hco] at h2'; cases h2'; rw [hf] at h3'; cases h3'
              exact ⟨hneEr, fun hd => (by rcases hd with h | h; exact absurd h hnfIrr; exact absurd h hncIrr),
                fun _ hIL => (by rcases hIL with h | h <;> (rw [hcVal] at h; cases h)),
                fun _ _ hvN => absurd hvVal hvN, fun _ _ _ => h1.symm⟩

end IxC.Resource.Proof
