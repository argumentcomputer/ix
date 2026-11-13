import IxCC.Src.Relevance.Proof.P1.Cases
import IxCC.Src.Relevance.Proof.P1.Basic
import IxCC.Src.Relevance.Proof.P1.Prefix

/-! # P1, relevance preservation: the plumbing cases

The cases of the core (`IxCC.Src.Relevance.Proof.P1.Cases`) that move values without reading
them: E1 (a variable: its slot is `LiveSlot`, since a variable is never shielded in itself and C1
makes its binder relevant; a suspension's value is its `eval`'s, a grandchild's `Post`), E4 (a λ:
`Live.clo` from the frame), E5 (a `let`: the body's environment under the marker or the value's
`Live`, `Whole` value), A1–A3 (`apply`: β under `envOk_lam`, the body's references because the
λ is no proof where β fires; a partial application accumulates or fires with `FireOk`; anything
else is stuck), `applyAll`, `force` and `forceAll` (a slot's own facts, or a suspension's
evaluation). At a term that is neither an application nor a constant, the frame's three tier-C
disjuncts are `TermC` (`frame_termOk`). P1 itself is not proved. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

variable {p : Program} {ann : Ann} {ch : Checked}

/-! ## Frames (to Basic) -/

/-- At a term that is neither an application nor a constant, a frame is a profile, binder
classes, the environment invariant and `TermOk`: the inner-prefix disjunct is `SpineC.head`, and
the bare-constant disjunct is impossible. (to Basic) -/
theorem frame_termOk {ls : Levels} {ρ : Env} {t : Term} (h : Frame p ann ch ls ρ t)
    (happ : ∀ f a m r, t ≠ .app f a m r) (hc : ∀ c us, t ≠ .const c us) :
    ∃ q bs, Agree ls q ∧ EnvOk p ann ch ls bs ρ t ∧ TermOk p ann ch q bs t := by
  obtain ⟨q, bs, hag, henv, hrefs, hu, ht | ⟨_, -, hsp, -⟩ | ⟨c, us, he, -⟩⟩ := h
  · exact ⟨q, bs, hag, henv, ⟨ht, hrefs, hu⟩⟩
  · cases hsp with
    | app => exact (happ _ _ _ _ rfl).elim
    | const => exact (hc _ _ rfl).elim
    | head _ _ ht => exact ⟨q, bs, hag, henv, ⟨ht, hrefs, hu⟩⟩
  · exact (hc c us he).elim

/-- A frame from `TermOk`. (to Basic) -/
theorem frame_of_termOk {ls : Levels} {ρ : Env} {t : Term} {q : Profile} {bs : List Rel}
    (hag : Agree ls q) (he : EnvOk p ann ch ls bs ρ t) (ht : TermOk p ann ch q bs t) :
    Frame p ann ch ls ρ t :=
  ⟨q, bs, hag, he, ht.refs, ht.univs, Or.inl ht.c⟩

/-- A `LiveSlot` suspension's evaluation has its precondition, at any clock, and its term has a
`Whole` value's shape. (to Basic) -/
theorem liveSlot_name_frame {t : Term} {ρ : Env} {ls : Levels}
    (hl : LiveSlot p ann ch (.name t ρ ls)) :
    (∀ k, Pre p ann ch (.eval k ls ρ t)) ∧ WholeTerm p t := by
  cases hl with
  | name q bs hag ht he => exact ⟨fun _ => frame_of_termOk hag he ht, wholeTerm_of_termC ht.c⟩

/-! ## E1, E4, E5 -/

/-- E1: the variable's slot is `LiveSlot` (C1 and `Agree` make its binder relevant at the levels;
a variable is not shielded in itself); its value is the slot's value or, for a suspension, the
value of its `eval` (a grandchild). With no slot the evaluation is stuck. -/
theorem case_var : CaseVar p ann ch := by
  intro k ls ρ i _ _ hpre _ ih
  obtain ⟨q, bs, hag, ⟨hlen, henv⟩, ⟨htc, -, -⟩⟩ :=
    frame_termOk hpre (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
  have hslot : ∀ s, ρ[i]? = some s → LiveSlot p ann ch s := by
    intro s hs
    have hlt : i < bs.length := by
      have := (List.getElem?_eq_some_iff.1 hs).1
      omega
    obtain ⟨r, hr⟩ : ∃ r, bs[i]? = some r := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hirr : r.irrAt ls = false := by
      cases htc with
      | var h => rw [← hag.irr]; exact h r hr
    refine henv i s r hs hr hirr (by simp [mentionsVar]) ?_
    rintro ⟨h, n, s', hh, hne, -⟩
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.var.injEq] at hh
    subst hh
    exact hne rfl
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · cases hs : ρ[i]? with
    | none => simp [eval, hs] at hv
    | some s =>
      simp only [eval, hs] at hv
      have hl := hslot s hs
      cases s with
      | val v' =>
        simp only [force, Sem.Result.ok.injEq] at hv
        subst hv
        cases hl with
        | val hlv hw => exact ⟨hlv, fun _ => hw⟩
      | name t ρ' ls' =>
        cases k with
        | zero => simp [force] at hv
        | succ k =>
          simp only [force] at hv
          obtain ⟨hfr, hwt⟩ := liveSlot_name_frame hl
          have hpost := (ih _ (.tail (.single (Step.var hs)) Step.forceName) (hfr k)).1 v hv
          exact ⟨hpost.1, fun _ => hpost.2 hwt⟩
  · cases hst with
    | var hs => exact Or.inl (hslot _ hs)

/-- E4: a closure, `Live` by the frame's facts; no step. -/
theorem case_lam : CaseLam p ann ch := by
  intro k ls ρ b d body _ _ hpre _ _
  obtain ⟨q, bs, hag, henv, hto⟩ :=
    frame_termOk hpre (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · simp only [eval, Sem.Result.ok.injEq] at hv
    subst hv
    exact ⟨.clo q bs hag hto henv, fun _ _ _ _ he => nomatch he⟩
  · cases hst

/-- E5: no variable is shielded in a `let`, so every relevant slot it mentions is `LiveSlot`; the
body runs under the marker where the `let` is irrelevant, and otherwise under the value's `Live`,
`Whole` value (its `eval`'s `Post`, with `wholeTerm_of_termC`). -/
theorem case_letE : CaseLetE p ann ch := by
  intro k ls ρ c r ty v b _ _ hpre _ ih
  obtain ⟨q, bs, hag, ⟨hlen, henv⟩, ⟨htc, hrefs, hu⟩⟩ :=
    frame_termOk hpre (fun _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
  obtain ⟨hv, hb⟩ : (r.irrP q = false → TermC p ann q bs v) ∧ TermC p ann q (r :: bs) b := by
    cases htc with
    | letE _ h2 h3 => exact ⟨h2, h3⟩
  have hirrq : r.irrP q = r.irrAt ls := hag.irr r
  have hslot : ∀ x s r', ρ[x]? = some s → bs[x]? = some r' → r'.irrAt ls = false →
      mentionsVar x (.letE c r ty v b) = true → LiveSlot p ann ch s := by
    intro x s r' h1 h2 h3 h4
    refine henv x s r' h1 h2 h3 h4 ?_
    rintro ⟨h, -, -, hh, -⟩
    simp [Term.spineL, Term.spine, Term.spine.go] at hh
  have hub : univsOk p b = true := by
    simp only [univsOk, Bool.and_eq_true] at hu
    exact hu.2
  have hrb : RefsHandled p ch q b := by
    intro x hx
    apply hrefs x
    simp only [Term.relevantRefs]
    rw [relevantRefs_append q b]
    exact List.mem_append_left _ hx
  have hwb : WholeTerm p b := wholeTerm_of_termC hb
  -- the body's frame under one more slot
  have hbody : ∀ s, (r.irrAt ls = false → LiveSlot p ann ch s) → Frame p ann ch ls (s :: ρ) b := by
    intro s hs
    refine frame_of_termOk hag ⟨by simp [hlen], ?_⟩ ⟨hb, hrb, hub⟩
    intro x s' r' hx hr hirr hm _
    cases x with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hr
      subst hx
      subst hr
      exact hs hirr
    | succ x =>
      simp only [List.getElem?_cons_succ] at hx hr
      exact hslot x s' r' hx hr hirr (by simp [mentionsVar, hm])
  -- the value's frame where the `let` is relevant
  have hval : r.irrAt ls = false → Frame p ann ch ls ρ v ∧ WholeTerm p v := by
    intro hrel
    have hvq : r.irrP q = false := by rw [hirrq]; exact hrel
    have htv := hv hvq
    refine ⟨frame_of_termOk hag ⟨hlen, ?_⟩ ⟨htv, ?_, ?_⟩, wholeTerm_of_termC htv⟩
    · intro x s r' hx hr hirr hm _
      exact hslot x s r' hx hr hirr (by simp [mentionsVar, hm])
    · intro x hx
      apply hrefs x
      simp only [Term.relevantRefs, hvq, Bool.false_eq_true, ↓reduceIte]
      rw [relevantRefs_append q b]
      exact List.mem_append_right _ hx
    · simp only [univsOk, Bool.and_eq_true, Bool.or_eq_true] at hu
      rcases hu.1 with h | h
      · rw [alwaysIrr_irrAt h ls] at hrel
        cases hrel
      · exact h
  have hbody_irr : r.irrAt ls = true → Frame p ann ch ls (.val (.irr (some v) ρ ls) :: ρ) b :=
    fun hr => hbody _ (fun h => by rw [hr] at h; cases h)
  have hbody_val : ∀ x, r.irrAt ls = false → eval p k ls ρ v = .ok x →
      Frame p ann ch ls (.val x :: ρ) b := by
    intro x hr hx
    obtain ⟨hfv, hwv⟩ := hval hr
    have hpx := (ih _ (.single (Step.letVal hr)) hfv).1 x hx
    exact hbody _ (fun _ => .val hpx.1 (hpx.2 hwv))
  refine ⟨fun w hw => ?_, fun c' hst _ => ?_⟩
  · cases hr : r.irrAt ls with
    | true =>
      simp only [eval, hr, ↓reduceIte] at hw
      have hpost := (ih _ (.single (Step.letIrr hr)) (hbody_irr hr)).1 w hw
      exact ⟨hpost.1, fun _ => hpost.2 hwb⟩
    | false =>
      simp only [eval, hr, Bool.false_eq_true, ↓reduceIte] at hw
      cases hx : eval p k ls ρ v with
      | ok x =>
        rw [hx] at hw
        have hpost := (ih _ (.single (Step.letBody hr hx)) (hbody_val x hr hx)).1 w hw
        exact ⟨hpost.1, fun _ => hpost.2 hwb⟩
      | _ => rw [hx] at hw; cases hw
  · cases hst with
    | letIrr hr => exact hbody_irr hr
    | letVal hr => exact (hval hr).1
    | letBody hr hx => exact hbody_val _ hr hx

/-! ## A1–A3, `applyAll` -/

/-- A1–A3: β runs the body under `envOk_lam` (its references are the λ's, the λ being no proof
where β fires); a partial application accumulates (`Live.pap` from `SlotFits`) or fires with
`FireOk` (`fire`'s `Post`); applying anything else is stuck. -/
theorem case_apply : CaseApply p ann ch := by
  intro k f s _ _ hpre _ ih
  obtain ⟨hlive, hfits⟩ := hpre
  cases f with
  | clo b d body ρ ls =>
    cases hlive with
    | clo q bs hag hto henv =>
      have hfits' : b.rel.irrAt ls = false → LiveSlot p ann ch s := hfits
      have htb : TermC p ann q (b.rel :: bs) body := by
        have htl := hto.c
        cases htl with
        | lam _ h => exact h
      have hframe : b.propWhen.allowsBeta ls = true → Frame p ann ch ls (s :: ρ) body := by
        intro hbeta
        refine frame_of_termOk hag (envOk_lam henv hfits') ⟨htb, ?_, ?_⟩
        · intro x hx
          apply hto.refs x
          have hh : b.propWhen.holdsP q = false := by
            rw [hag.holds]
            simpa [PropWhen.allowsBeta] using hbeta
          simp only [Term.relevantRefs, hh, Bool.false_eq_true, ↓reduceIte]
          exact hx
        · simpa [univsOk] using hto.univs
      refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
      · cases hb : b.propWhen.allowsBeta ls with
        | false => cases k <;> simp [apply, hb] at hv
        | true =>
          cases k with
          | zero => simp [apply, hb] at hv
          | succ k =>
            simp only [apply, hb, ↓reduceIte] at hv
            have hpost := (ih _ (.single (Step.beta hb)) (hframe hb)).1 v hv
            exact ⟨hpost.1, fun _ => hpost.2 (wholeTerm_of_termC htb)⟩
      · cases hst with
        | beta hb => exact hframe hb
  | pap h ls args =>
    cases hlive with
    | pap hseen hargs hmin hlt =>
      obtain ⟨hlast, hmin'⟩ := hfits
      have hlive' : ∀ j s', (args ++ [s])[j]? = some s' → ¬ (HeadIgnores ann h ls j ∧ MarkerSlot s') →
          LiveSlot p ann ch s' := by
        intro j s' hj hn
        by_cases hjl : j < args.length
        · rw [List.getElem?_append_left hjl] at hj
          exact hargs j s' hj hn
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hjl)] at hj
          have hj1 := (List.getElem?_eq_some_iff.1 hj).1
          simp only [List.length_singleton] at hj1
          have hj0 : j = args.length := by omega
          subst hj0
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          exact hlast hn
      refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
      · simp only [apply] at hv
        split at hv
        · rename_i heq
          have harity : (args ++ [s]).length = p.headArity h := beq_iff_eq.mp heq
          have hpost := (ih _ (.single (Step.papFire harity)) ⟨harity, hseen, hlive', hmin'⟩).1 v hv
          exact ⟨hpost.1, fun _ => hpost.2⟩
        · split at hv
          · rename_i hlt'
            simp only [Sem.Result.ok.injEq] at hv
            subst hv
            refine ⟨.pap hseen hlive' hmin' (by simpa using hlt'), ?_⟩
            intro hw h' ls' args' he
            simp only [Value.pap.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            exact hw h ls args rfl
          · cases hv
      · cases hst with
        | papFire harity => exact ⟨harity, hseen, hlive', hmin'⟩
  | lit n =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp [apply] at hv
    · cases hst
  | str s' =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp [apply] at hv
    · cases hst
  | con c ls ps fs =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp [apply] at hv
    · cases hst
  | irr t ρ ls =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp [apply] at hv
    · cases hst

/-- `applyAll`: each `apply` has its precondition (`AllFit`, and the previous `apply`'s `Post`),
and `Whole` threads through the `apply`s' `Post`s. -/
theorem case_applyAll : CaseApplyAll p ann ch := by
  intro k f ss _ _ hpre _ ih
  obtain ⟨hlive, hfit⟩ := hpre
  cases ss with
  | nil =>
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · simp only [applyAll, Sem.Result.ok.injEq] at hv
      subst hv
      exact ⟨hlive, id⟩
    · cases hst
  | cons s ss =>
    obtain ⟨hfits, hrest⟩ := hfit
    have hpa : Pre p ann ch (.apply k f s) := ⟨hlive, hfits⟩
    have hpost := (ih _ (.single Step.allHead) hpa).1
    have hpr : ∀ v, apply p k f s = .ok v → Pre p ann ch (.applyAll k v ss) :=
      fun v hv => ⟨(hpost v hv).1, hrest v hv⟩
    refine ⟨fun w hw => ?_, fun c' hst _ => ?_⟩
    · simp only [applyAll] at hw
      cases hv : apply p k f s with
      | ok v =>
        rw [hv] at hw
        have h2 := (ih _ (.single (Step.allRest hv)) (hpr v hv)).1 w hw
        exact ⟨h2.1, fun hwf => h2.2 ((hpost v hv).2 hwf)⟩
      | _ => rw [hv] at hw; cases hw
    · cases hst with
      | allHead => exact hpa
      | allRest hv => exact hpr _ hv

/-! ## `force`, `forceAll` -/

/-- `force`: a value slot gives its own value (`Live` and `Whole`, or the marker, which is not a
partial application); a suspension its evaluation's `Post`. -/
theorem case_force : CaseForce p ann ch := by
  intro k s _ _ hpre _ ih
  cases s with
  | val v =>
    refine ⟨fun w hw => ?_, fun c' hst _ => ?_⟩
    · simp only [force, Sem.Result.ok.injEq] at hw
      subst hw
      rcases hpre with hl | ⟨t, ρ, ls, he⟩
      · cases hl with
        | val hlv hwh => exact ⟨fun _ => hlv, hwh⟩
      · simp only [Slot.val.injEq] at he
        subst he
        exact ⟨fun h => by simp [Value.isIrr] at h, fun _ _ _ he => nomatch he⟩
    · cases hst
  | name t ρ ls =>
    have hl : LiveSlot p ann ch (.name t ρ ls) := by
      rcases hpre with hl | ⟨_, _, _, he⟩
      · exact hl
      · cases he
    obtain ⟨hfr, hwt⟩ := liveSlot_name_frame hl
    refine ⟨fun w hw => ?_, fun c' hst _ => ?_⟩
    · cases k with
      | zero => simp [force] at hw
      | succ k =>
        simp only [force] at hw
        have hpost := (ih _ (.single Step.forceName) (hfr k)).1 w hw
        exact ⟨fun _ => hpost.1, hpost.2 hwt⟩
    · cases hst with
      | forceName => exact hfr _

/-- `forceAll`: each `force` has its precondition, and the values are the `force`s'. -/
theorem case_forceAll : CaseForceAll p ann ch := by
  intro k ss _ _ hpre _ ih
  cases ss with
  | nil =>
    refine ⟨fun vs hvs => ?_, fun c' hst _ => ?_⟩
    · simp only [forceAll, Sem.Result.ok.injEq] at hvs
      subst hvs
      intro v hv
      cases hv
    · cases hst
  | cons s ss =>
    have hph : Pre p ann ch (.force k s) := hpre s (List.mem_cons_self ..)
    have hpt : Pre p ann ch (.forceAll k ss) := fun s' hs' => hpre s' (List.mem_cons_of_mem _ hs')
    refine ⟨fun vs hvs => ?_, fun c' hst _ => ?_⟩
    · cases hv : force p k s with
      | ok v =>
        cases hr : forceAll p k ss with
        | ok vs' =>
          simp only [forceAll, hv, hr, Sem.Result.ok.injEq] at hvs
          subst hvs
          intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact (ih _ (.single Step.allForce) hph).1 _ hv
          · exact (ih _ (.single (Step.allForceRest hv)) hpt).1 vs' hr w hw
        | _ => simp [forceAll, hv, hr] at hvs
      | _ => simp [forceAll, hv] at hvs
    · cases hst with
      | allForce => exact hph
      | allForceRest _ => exact hpt

end IxCC.Src.Relevance.Proof.P1
