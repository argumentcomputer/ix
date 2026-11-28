import IxCC.Src.Relevance.Proof.P1.Cases
import IxCC.Src.Relevance.Proof.P1.Basic
import IxCC.Src.Relevance.Proof.P1.Prefix

/-! # P1, relevance preservation: δ (E8, `evalConst`, `headValue`, F6, F6w)

The cases of the core (`IxCC.Src.Relevance.Proof.P1.Cases`) at a constant reference and at what δ
makes of it:

* E8 (`case_const`): the reference's instance is handled (`RefsHandled`): out of the program, or
  reached at its normalised profile, which agrees with the evaluated levels (`Agree.inst`, with
  `univsOk`'s count); a bare constant's `WholeTerm` excludes an eliminator over a field written
  erased, every eliminator's arity being positive (`elimShape_arity_pos`).
* δ (`case_evalConst`): out of the program there is no entry and no table entry (`Canonical.dense`),
  so δ is stuck; at a reached instance a run body (`eqn`, a safe definition, an opaque by value) has
  tier C, its references handled and its universe counts at the instance's profile under the empty
  environment; a `csimp` redirect's target is a bare constant that is no eliminator over a field
  written erased (`Canonical.redirects`), its reference handled by `WellAnnotated.closed` through
  `Program.runtimeRefs`; every special head is `specialHead?` of the constant (`HeadSeen`), a word
  operation's from the reached word entry.
* `case_headValue`: a nullary head fires with no argument; any other is a partial application with
  none.
* F6 (`case_prim`): a primitive ignores no argument (`headConst?` is `none`), so every slot is
  `LiveSlot`; the result is a literal or `boolValue`'s field-less constructor.
* F6w (`case_word`): the result is a literal or the tower `mkWord?`, whose one marker is `Fin.mk`'s
  proof field, which the pinned `Fin.mk` drops at the empty profile and which sits in a value of its
  two fields (`Canonical.finProof`, from the reached word entry of `HeadSeen`).

P1 itself is `IxCC.Src.Relevance.Proof.P1.Main`. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

variable {p : Program} {ann : Ann} {ch : Checked}

/-! ## Helpers (to Basic) -/

/-- Every eliminator's arity is positive (its major is an argument). To Basic. -/
theorem elimShape_arity_pos {c : CId} {shape : ElimShape} (h : elimShape? p c = some shape) :
    0 < shape.arity := by
  unfold elimShape? at h
  split at h
  · split at h
    · cases h
      dsimp only
      omega
    · cases h
  · split at h
    · cases h
      dsimp only
      omega
    · cases h
  · cases h

/-- A bare constant whose `WholeTerm` holds is no eliminator over a field written erased. To
Basic. -/
theorem wholeTerm_const_elim {c : CId} {us : List Ixon.Univ} (h : WholeTerm p (.const c us)) :
    ∀ shape, elimShape? p c = some shape → erasedMinors p shape = false := by
  intro shape hsh
  cases he : erasedMinors p shape
  · rfl
  · have h1 := h c us shape (by simp [Term.spineL, Term.spine, Term.spine.go]) hsh he
    have h2 := elimShape_arity_pos hsh
    simp [Term.spineL, Term.spine, Term.spine.go] at h1
    omega

/-- A bare constant that is no eliminator over a field written erased has `WholeTerm`. To Basic. -/
theorem wholeTerm_const {c : CId} {us : List Ixon.Univ}
    (h : ∀ shape, elimShape? p c = some shape → erasedMinors p shape = false) :
    WholeTerm p (.const c us) := by
  intro c' us' shape hhd hsh he
  simp only [Term.spineL, Term.spine, Term.spine.go, Term.const.injEq] at hhd
  obtain ⟨rfl, rfl⟩ := hhd
  rw [h shape hsh] at he
  cases he

/-- A constructor value is `Whole`. To Basic. -/
theorem whole_con {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} :
    Whole p (.con c ls ps fs) := fun _ _ _ he => nomatch he

/-- A literal is `Whole`. To Basic. -/
theorem whole_lit {n : Nat} : Whole p (.lit n) := fun _ _ _ he => nomatch he

/-- A marker is `Whole`. To Basic. -/
theorem whole_irr {t : Option Term} {ρ : Env} {ls : Levels} : Whole p (.irr t ρ ls) :=
  fun _ _ _ he => nomatch he

/-- A constructor value whose fields are all `Live` and `Whole` is `Live`. To Basic. -/
theorem live_con_of_fields {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value}
    (h : ∀ v ∈ fs, Live p ann ch v ∧ Whole p v) : Live p ann ch (.con c ls ps fs) := by
  refine .con (fun i v hi _ => (h v (List.mem_iff_getElem?.2 ⟨i, hi⟩)).1)
    (fun i v hi => (h v (List.mem_iff_getElem?.2 ⟨i, hi⟩)).2) ⟨?_, ?_⟩
  · intro i v hi hirr
    rw [live_not_irr (h v (List.mem_iff_getElem?.2 ⟨i, hi⟩)).1] at hirr
    cases hirr
  · intro v hi hirr
    rw [live_not_irr (h v (List.mem_iff_getElem?.2 ⟨0, hi⟩)).1] at hirr
    cases hirr

/-- A primitive or word operation ignores no argument: every slot of its activation is `LiveSlot`.
To Basic. -/
theorem fireOk_live_of_none {h : Head} {ls : Levels} {args : List Slot}
    (hc : headConst? h = none) (hfire : FireOk p ann ch h ls args) :
    ∀ s ∈ args, LiveSlot p ann ch s := by
  intro s hs
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
  refine hfire.live j s hj ?_
  rintro ⟨⟨c, -, -, hc', -⟩, -⟩
  rw [hc] at hc'
  cases hc'

/-- `boolValue`'s result is a constructor with no parameter and no field. -/
theorem boolValue_ok {b : Bool} {v : Value} (h : p.boolValue b = .ok v) :
    ∃ c, v = .con c [] [] [] := by
  unfold Program.boolValue at h
  repeat' (first | (cases h; exact ⟨_, rfl⟩) | (cases h; done) | split at h)

/-- A word operation's result on its forced arguments is `wordResult`'s. -/
theorem wordValue_ok {w : Width} {op : WordOp} {vs : List Value} {v : Value}
    (h : p.wordValue w op vs = .ok v) : ∃ r, p.wordResult r = .ok v := by
  unfold Program.wordValue at h
  repeat' (first | exact ⟨_, h⟩ | (cases h; done) | (simp only at h) | split at h)

/-! ## E8 -/

/-- E8: δ at the evaluated levels has its precondition (the reference's instance is handled), and
a bare constant whose `WholeTerm` holds is no eliminator over a field written erased. -/
theorem case_const : CaseConst p ann ch := by
  intro k ls ρ c us hf hs hpre hcoh ih
  obtain ⟨q, bs, hag, -, hrefs, hu, -⟩ := hpre
  have hpc : Pre p ann ch (.evalConst k (us.map (evalUniv ls)) c) := by
    have hmem : (c, q.inst us) ∈ (Term.const c us).relevantRefs q [] := by
      simp [Term.relevantRefs]
    rcases hrefs _ hmem with hge | hin
    · exact Or.inl hge
    · refine Or.inr ⟨_, hag.inst us (lvlsOf p c) ?_, hin⟩
      simpa [univsOk] using hu
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · rw [eval_const] at hv
    obtain ⟨hl, hw⟩ := (ih _ (.single Step.const) hpc).1 v hv
    exact ⟨hl, fun hwt => hw (wholeTerm_const_elim hwt)⟩
  · cases hst
    exact hpc

/-! ## δ -/

/-- δ: out of the program, stuck; at a reached instance, every step has its precondition and the
result is the step's. -/
theorem case_evalConst : CaseEvalConst p ann ch := by
  intro k ls c hf hs hpre hcoh ih
  rcases hpre with hge | ⟨q, hag, hinst⟩
  · -- out of the program: no entry and no table entry
    obtain ⟨hent, hres⟩ := hf.canon.dense c hge
    have hd : p.decl? c = none := by simp [Program.decl?, hent]
    clear ih hcoh
    refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
    · rw [evalConst_eq] at hv
      simp [hres, hd] at hv
    · cases hst <;> simp_all
  · have hreached : c ∈ ch.reached := hf.reached (c, q) hinst
    -- a run body of the instance under the empty environment
    have hbody : ∀ key t, key ∈ p.runtimeKeys c → p.termOf key = some t →
        Frame p ann ch ls [] t ∧ WholeTerm p t := by
      intro key t hk ht
      have htc : TermC p ann q [] t := (hf.wa.instsC (c, q) hinst).terms key hk t ht
      exact ⟨⟨q, [], hag, ⟨rfl, fun x s _ hx => by simp at hx⟩, refsHandled_runtime hf hinst hk ht,
        (hf.canon.univs c hreached).1 key hk t ht, Or.inl htc⟩, wholeTerm_of_termC htc⟩
    -- a `csimp` redirect's target
    have hcsimp : ∀ g vs thm, p.table.resolveOf c = some (.csimp g vs thm) →
        Frame p ann ch ls [] (.const g vs) ∧ WholeTerm p (.const g vs) := by
      intro g vs thm hres
      have hred := hf.canon.redirects c hreached g vs thm hres
      refine ⟨⟨q, [], hag, ⟨rfl, fun x s _ hx => by simp at hx⟩, ?_,
        (hf.canon.univs c hreached).2 g vs thm hres, Or.inr (Or.inr ⟨g, vs, rfl, hred⟩)⟩,
        wholeTerm_const hred⟩
      intro x hx
      simp only [Term.relevantRefs, List.mem_singleton] at hx
      subst hx
      apply hf.wa.closed (c, q) hinst
      simp [Program.instRefs, Program.runtimeRefs, hres]
    -- a special head of the constant
    have hseen : ∀ h, specialHead? p c = some h → headConst? h = some c → HeadSeen p ch ls h := by
      intro h hsp hc
      refine ⟨fun c' hc' => ?_, fun w op hw => ?_⟩
      · rw [hc] at hc'
        obtain rfl := Option.some.inj hc'
        exact ⟨hsp, q, hag, hinst⟩
      · subst hw
        simp [headConst?] at hc
    have hseenWord : ∀ w op thm, p.table.resolveOf c = some (.word w op thm) →
        HeadSeen p ch ls (.word w op) := by
      intro w op thm hres
      refine ⟨fun c' hc' => by simp [headConst?] at hc', fun w' op' hw => ?_⟩
      cases hw
      exact ⟨c, hreached, thm, hres⟩
    have hseenPrim : ∀ op, HeadSeen p ch ls (.prim op) := by
      intro op
      refine ⟨fun c' hc' => by simp [headConst?] at hc', fun w' op' hw => ?_⟩
      cases hw
    -- every step has its precondition
    have hstep : ∀ c', Step p (.evalConst k ls c) c' → Pre p ann ch c' := by
      intro c' hst
      cases hst with
      | prim hres => exact hseenPrim _
      | word hres => exact hseenWord _ _ _ hres
      | csimp hres => exact (hcsimp _ _ _ hres).1
      | eqn hres =>
        exact (hbody (.eqn c) _ (by simp [Program.runtimeKeys, hres])
          (by simp [Program.termOf, hres])).1
      | case hres => exact hseen _ (by simp [specialHead?, hres]) rfl
      | ctor hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
      | recr hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
      | quotMk hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
      | quotLift hres hd => exact hseen _ (by simp [specialHead?, hres, hd]) rfl
      | defn hres hd =>
        exact (hbody (.value c) _
          (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd])
          (by simp [Program.termOf, hd])).1
      | opaq hres hd hop =>
        exact (hbody (.value c) _
          (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd, hop])
          (by simp [Program.termOf, hd])).1
    refine ⟨fun v hv => ?_, fun c' hst _ => hstep c' hst⟩
    have hpost : ∀ c', Step p (.evalConst k ls c) c' → Post p ann ch c' :=
      fun c' st => (ih c' (.single st) (hstep c' st)).1
    -- a special head of the constant: its value's facts
    have hhead : ∀ h, headConst? h = some c → Step p (.evalConst k ls c) (.headValue k ls h) →
        headValue p k ls h = .ok v → Live p ann ch v ∧
          ((∀ shape, elimShape? p c = some shape → erasedMinors p shape = false) → Whole p v) := by
      intro h hc st hv'
      obtain ⟨hl, hw⟩ := hpost _ st v hv'
      refine ⟨hl, fun hcw => hw fun c' shape hc' hsh => ?_⟩
      rw [hc] at hc'
      obtain rfl := Option.some.inj hc'
      exact hcw shape hsh
    rw [evalConst_eq] at hv
    cases hres : p.table.resolveOf c with
    | some e =>
      cases e with
      | prim op =>
        simp only [hres] at hv
        obtain ⟨hl, hw⟩ := hpost _ (Step.prim hres) v hv
        exact ⟨hl, fun _ => hw fun c' shape hc' => by simp [headConst?] at hc'⟩
      | word w op thm =>
        simp only [hres] at hv
        obtain ⟨hl, hw⟩ := hpost _ (Step.word hres) v hv
        exact ⟨hl, fun _ => hw fun c' shape hc' => by simp [headConst?] at hc'⟩
      | csimp g vs thm =>
        simp only [hres] at hv
        cases k with
        | zero => cases hv
        | succ k =>
          simp only [Sem.later_succ] at hv
          obtain ⟨hl, hw⟩ := hpost _ (Step.csimp hres) v hv
          exact ⟨hl, fun _ => hw (hcsimp g vs thm hres).2⟩
      | eqn thm body =>
        simp only [hres] at hv
        cases k with
        | zero => cases hv
        | succ k =>
          simp only [Sem.later_succ] at hv
          obtain ⟨hl, hw⟩ := hpost _ (Step.eqn hres) v hv
          exact ⟨hl, fun _ => hw (hbody (.eqn c) body (by simp [Program.runtimeKeys, hres])
            (by simp [Program.termOf, hres])).2⟩
      | case r =>
        simp only [hres] at hv
        exact hhead (.cases c) rfl (Step.case hres) hv
    | none =>
      simp only [hres] at hv
      cases hd : p.decl? c with
      | none => simp [hd] at hv
      | some d =>
        cases d with
        | ctor sf lv ind cidx np nf ty =>
          simp only [hd] at hv
          exact hhead (.ctor c) rfl (Step.ctor hres hd) hv
        | recr sf kk lv np nmot nmin ni ind rules ty =>
          simp only [hd] at hv
          exact hhead (.recr c) rfl (Step.recr hres hd) hv
        | quot kind lv ty =>
          cases kind with
          | ctor =>
            simp only [hd] at hv
            exact hhead (.quotMk c) rfl (Step.quotMk hres hd) hv
          | lift =>
            simp only [hd] at hv
            exact hhead (.quotLift c) rfl (Step.quotLift hres hd) hv
          | type => simp [hd] at hv
          | ind => simp [hd] at hv
        | defn kind safety lv ty body =>
          cases kind with
          | defn =>
            cases safety with
            | safe =>
              simp only [hd] at hv
              cases k with
              | zero => cases hv
              | succ k =>
                simp only [Sem.later_succ] at hv
                obtain ⟨hl, hw⟩ := hpost _ (Step.defn hres hd) v hv
                exact ⟨hl, fun _ => hw (hbody (.value c) body
                  (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd])
                  (by simp [Program.termOf, hd])).2⟩
            | _ => simp [hd] at hv
          | opaq =>
            cases safety with
            | safe =>
              simp only [hd] at hv
              split at hv
              · rename_i hop
                cases k with
                | zero => cases hv
                | succ k =>
                  simp only [Sem.later_succ] at hv
                  obtain ⟨hl, hw⟩ := hpost _ (Step.opaq hres hd hop) v hv
                  exact ⟨hl, fun _ => hw (hbody (.value c) body
                    (by simp [Program.runtimeKeys, Program.isEvaluatedBody, hres, hd, hop])
                    (by simp [Program.termOf, hd])).2⟩
              · cases hv
            | _ => simp [hd] at hv
          | _ => simp [hd] at hv
        | induct => simp [hd] at hv
        | axio => simp [hd] at hv

/-! ## A special head as a value -/

/-- A special head as a value: fired at once when nullary, else a partial application with no
argument. -/
theorem case_headValue : CaseHeadValue p ann ch := by
  intro k ls h hf hs hpre hcoh ih
  have hseen : HeadSeen p ch ls h := hpre
  have hfire : p.headArity h = 0 → Pre p ann ch (.fire k h ls []) := fun h0 =>
    ⟨by simp [h0], hseen, fun j s hj => by simp at hj,
      fun c shape _ _ pos j kidx _ s hs' => by simp at hs'⟩
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · rw [headValue_eq] at hv
    split at hv
    · rename_i e
      have h0 : p.headArity h = 0 := by simpa using e
      obtain ⟨hl, hw⟩ := (ih _ (.single (Step.nullary h0)) (hfire h0)).1 v hv
      exact ⟨hl, fun _ => hw⟩
    · rename_i e
      have h0 : p.headArity h ≠ 0 := by simpa using e
      cases hv
      refine ⟨.pap hseen (fun j s hj => by simp at hj)
        (fun c shape _ _ pos j kidx _ s hs' => by simp at hs') (Nat.pos_of_ne_zero h0), ?_⟩
      intro hcond h' ls' args heq
      cases heq
      exact hcond
  · cases hst with
    | nullary h0 => exact hfire h0

/-! ## F6, F6w -/

/-- F6: every slot is `LiveSlot` (a primitive ignores none), and the result is a literal or a
field-less constructor. -/
theorem case_prim : CasePrim p ann ch := by
  intro k op ls args hf hs hpre hcoh ih
  have hfire : FireOk p ann ch (.prim op) ls args := hpre
  have hlive := fireOk_live_of_none rfl hfire
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · rw [fire_prim] at hv
    obtain ⟨vs, -, hv⟩ := bind_ok_inv hv
    simp only [primValue] at hv
    cases hl : litArgs vs with
    | none => simp [hl] at hv
    | some ns =>
      simp only [hl] at hv
      cases he : op.evalLits ns with
      | none => simp [he] at hv
      | some r =>
        cases r with
        | nat n =>
          simp only [he, Sem.Result.ok.injEq] at hv
          subst hv
          exact ⟨.lit n, whole_lit⟩
        | bool b =>
          simp only [he] at hv
          obtain ⟨c0, rfl⟩ := boolValue_ok hv
          exact ⟨live_con_of_fields (fun v hv => by simp at hv), whole_con⟩
  · cases hst with
    | primArgs => exact fun s hs' => Or.inl (hlive s hs')

/-- F6w: every slot is `LiveSlot` (a word operation ignores none), and the result is a literal or
the tower `mkWord?`, whose marker is the pinned `Fin.mk`'s proof field, dropped at the empty
profile, in a value of its two fields (`Canonical.finProof`). -/
theorem case_word : CaseWord p ann ch := by
  intro k w op ls args hf hs hpre hcoh ih
  have hfire : FireOk p ann ch (.word w op) ls args := hpre
  obtain ⟨c, hc, thm, hres⟩ := hfire.inst.2 w op rfl
  have hlive := fireOk_live_of_none rfl hfire
  -- the tower
  have htower : ∀ w' n t, p.mkWord? w' n = some t → Live p ann ch t ∧ Whole p t := by
    intro w' n t hm
    cases h1 : p.wordCtor? w' with
    | none => simp [Program.mkWord?, h1] at hm
    | some c0 =>
      cases h2 : p.known.bitVecOfFin with
      | none => simp [Program.mkWord?, h1, h2] at hm
      | some bv =>
        cases h3 : p.known.finMk with
        | none => simp [Program.mkWord?, h1, h2, h3] at hm
        | some fin =>
          simp [Program.mkWord?, h1, h2, h3] at hm
          subst hm
          obtain ⟨⟨sf, lv, ind, cidx, np, ty, hdfin⟩, hkeep⟩ :=
            hf.canon.finProof c hc w op thm hres fin h3
          -- `UIntN.ofBitVec`
          refine ⟨live_con_of_fields fun v hv => ?_, whole_con⟩
          simp only [List.mem_singleton] at hv
          subst hv
          -- `BitVec.ofFin`
          refine ⟨live_con_of_fields fun v hv => ?_, whole_con⟩
          simp only [List.mem_singleton] at hv
          subst hv
          -- `Fin.mk`, its proof field the marker
          refine ⟨.con ?_ ?_ ⟨?_, ?_⟩, whole_con⟩
          · intro i v hi hr
            rcases i with _ | _ | i
            · simp at hi
              subst hi
              exact .lit n
            · simp at hi
              subst hi
              simp [ReadsField, hdfin, Checked.keeps, profileOf, hkeep, Value.isIrr] at hr
            · simp at hi
          · intro i v hi
            rcases i with _ | _ | i
            · simp at hi
              subst hi
              exact whole_lit
            · simp at hi
              subst hi
              exact whole_irr
            · simp at hi
          · intro i v _ _ _ sf' lv' ind' cidx' np' nf' ty' hd'
            rw [hdfin] at hd'
            simp only [Option.some.injEq, Decl.ctor.injEq] at hd'
            obtain ⟨-, -, -, -, -, h6, -⟩ := hd'
            simp only [List.length_cons, List.length_nil]
            omega
          · intro v hv hirr
            simp at hv
            subst hv
            simp [Value.isIrr] at hirr
  refine ⟨fun v hv => ?_, fun c' hst _ => ?_⟩
  · rw [fire_word] at hv
    obtain ⟨vs, -, hv⟩ := bind_ok_inv hv
    obtain ⟨r, hr⟩ := wordValue_ok hv
    cases r with
    | word w' n =>
      simp only [Program.wordResult] at hr
      cases hm : p.mkWord? w' n with
      | none =>
        rw [hm] at hr
        cases hr
      | some t =>
        rw [hm] at hr
        simp only [Sem.Result.ofOption, Sem.Result.ok.injEq] at hr
        subst hr
        exact htower w' n t hm
    | nat n =>
      simp only [Program.wordResult, Sem.Result.ok.injEq] at hr
      subst hr
      exact ⟨.lit n, whole_lit⟩
    | dec b =>
      simp only [Program.wordResult] at hr
      cases hr
  · cases hst with
    | wordArgs => exact fun s hs' => Or.inl (hlive s hs')

end IxCC.Src.Relevance.Proof.P1
