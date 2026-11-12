import IxCC.Own.Plain.Proof.Owned.Rhs

/-! # Join declarations and jumps

A declaration saves its body with the context it was checked from (`OwnedEntry`): nothing moves,
the captured list is recorded against the join in `Δ`. A jump hands over the arguments' tokens
and one token of each captured variable that is not an immediate of the declaration; the body
starts from exactly those (`Ctx.enter`), so the counts are the jump's with the vacuous tokens of
immediates added or dropped. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

theorem nodupFrom_spec : ∀ {seen : Src.NatSet} {xs : List Var}, nodupFrom seen xs = true →
    xs.Nodup ∧ ∀ y, y ∈ xs → seen.contains y = false
  | _, [], _ => ⟨List.nodup_nil, fun _ h => by simp at h⟩
  | seen, x :: xs, h => by
    simp only [nodupFrom, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hrest⟩ := h
    obtain ⟨hn, hs⟩ := nodupFrom_spec hrest
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hn⟩, fun y hy => ?_⟩
    · have := hs x hm
      simp [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at this
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have := hs y hy
        simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert] at this ⊢
        split at this
        · simp at this
        · exact this

theorem nodupVars_nodup {xs : List Var} (h : nodupVars xs = true) : xs.Nodup :=
  (nodupFrom_spec h).1

theorem fresh_mono : ∀ {big small ps : List Var}, fresh big ps = true →
    (∀ x, x ∈ small → x ∈ big) → fresh small ps = true
  | _, _, [], _, _ => rfl
  | big, small, p :: ps, h, hs => by
    simp only [fresh, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, fresh_mono h2 (fun x hx => ?_)⟩
    · have hp : p ∉ big := by simpa using h1
      have : p ∉ small := fun hm => hp (hs p hm)
      simpa using this
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (hs x hx)
      · exact List.mem_append_right _ hx

theorem Fir.lookupJ_id {j : Fir.JoinId} : ∀ {J : List Fir.JEntry} {e : Fir.JEntry}
    {rest : List Fir.JEntry}, Fir.lookupJ j J = some (e, rest) → e.id = j
  | [], _, _, h => by simp [Fir.lookupJ] at h
  | e₀ :: J, e, rest, h => by
    simp only [Fir.lookupJ] at h
    split at h
    · next he => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact he
    · exact Fir.lookupJ_id h

theorem Fir.lookupJ_of_arity {j : Fir.JoinId} {n : Nat} : ∀ {J : List Fir.JEntry},
    (stackArities J).lookup j = some n → ∃ e rest, Fir.lookupJ j J = some (e, rest) ∧
      e.params.length = n
  | [], h => by simp [stackArities, List.lookup] at h
  | e₀ :: J, h => by
    by_cases he : e₀.id = j
    · have hb : (j == e₀.id) = true := by simp [he]
      simp only [stackArities, List.map_cons, List.lookup, hb, Option.some.injEq] at h
      exact ⟨e₀, J, by simp [Fir.lookupJ, he], h⟩
    · have hb : (j == e₀.id) = false := beq_eq_false_iff_ne.mpr (fun h => he h.symm)
      have h' : (stackArities J).lookup j = some n := by
        simpa [stackArities, List.lookup, hb] using h
      obtain ⟨e, rest, hl, hn⟩ := Fir.lookupJ_of_arity h'
      exact ⟨e, rest, by simp [Fir.lookupJ, he, hl], hn⟩

/-- Keep the tokens a predicate selects; those dropped hold immediates. -/
theorem EnvRoots.filter {ρ : Own.Env} (p : Var → Bool) :
    ∀ {xs : List Var} {vs : List RVal}, EnvRoots ρ xs vs →
      (∀ x, x ∈ xs → p x = false → ∃ v, ρ.get? x = some v ∧ ImmVal v) →
      ∃ vs', EnvRoots ρ (xs.filter p) vs' ∧ SameRefs vs vs'
  | [], vs, h, _ => ⟨[], rfl, by cases h; exact SameRefs.refl _⟩
  | y :: ys, vs, h, hp => by
    obtain ⟨u, us, hy, hus, rfl⟩ := EnvRoots.cons_iff.mp h
    obtain ⟨vs', hr, hs⟩ := EnvRoots.filter p hus (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    cases hpy : p y with
    | true =>
      refine ⟨u :: vs', ?_, SameRefs.cons u hs⟩
      rw [List.filter_cons_of_pos hpy]
      exact EnvRoots.cons hy hr
    | false =>
      obtain ⟨u', hu', himm⟩ := hp y List.mem_cons_self hpy
      have : u' = u := Option.some.inj (hu'.symm.trans hy)
      subst this
      refine ⟨vs', ?_, (SameRefs.imm_cons himm us).trans hs⟩
      rw [List.filter_cons_of_neg (by simp [hpy])]
      exact hr

theorem Ctx.ownHas_ofList {xs : List Var} {y : Var} (hn : xs.Nodup)
    (h : (Src.NatMap.ofList (xs.map (·, (1 : Nat)))).contains y = true) : y ∈ xs := by
  by_cases hy : y ∈ xs
  · exact hy
  · have hk : ((xs.map (·, (1 : Nat))).map (·.1)).Nodup := by rw [Ctx.map_fst_pairs]; exact hn
    have hnone := Src.NatMap.get?_ofList_none hk (k := y) (by rw [Ctx.map_fst_pairs]; exact hy)
    simp [Src.NatMap.contains, hnone] at h

/-- After a jump, the body continues on its declaration's stack (and, for a recursive join, on
itself, charged). -/
theorem OwnedEntry.after_stack {Δ Δd : JCtx} {Γd : Ctx} {lexd captured : List Var}
    {older : Joins} {restf : List Fir.JEntry} {resto : List JEntry} {ef : Fir.JEntry}
    {eo : JEntry} (entry : OwnedEntry Δ Δd Γd lexd captured restf ef eo)
    (tail : OwnedStack Δ ef.env eo.env lexd older restf resto) (hn : lexd.Nodup)
    (hf : Plain.fresh lexd ef.params = true) (vs : List RVal) (ws : List Fir.Val) :
    OwnedStack (if ef.isRec then Δd.insert ef.id captured else Δd)
      (Fir.bindAll ef.env ef.params ws) (Own.bindAll eo.env eo.params vs) (lexd ++ ef.params)
      (if ef.isRec then (ef.id, lexd) :: older else older) (ef.after restf) (eo.after resto) := by
  have tail' : OwnedStack (if ef.isRec then Δd.insert ef.id captured else Δd) ef.env eo.env lexd
      older restf resto := by
    apply tail.transfer
    intro e he
    rw [← entry.agree e he]
    split
    · exact Src.NatMap.get?_insert_ne _ _ (entry.fresh e he)
    · rfl
  rw [entry.params]
  cases hr : ef.isRec with
  | false =>
    have hro : eo.isRec = false := by rw [entry.isRec]; exact hr
    simp only [Fir.JEntry.after, JEntry.after, hr, hro, Bool.false_eq_true, ↓reduceIte]
    simp only [hr, Bool.false_eq_true, ↓reduceIte] at tail'
    exact tail'.rebind ef.params vs ws hf
  | true =>
    have hro : eo.isRec = true := by rw [entry.isRec]; exact hr
    simp only [Fir.JEntry.after, JEntry.after, if_pos hr, if_pos hro]
    simp only [if_pos hr] at tail'
    have entry' : OwnedEntry (Δd.insert ef.id captured) Δd Γd lexd captured restf
        { ef with charged := true } { eo with charged := true } :=
      ⟨entry.id, rfl, entry.params, entry.isRec, entry.erases, entry.typed, entry.imm,
        entry.immIn, entry.sub, entry.nodup, Src.NatMap.get?_insert_self ..,
        fun e he => (Src.NatMap.get?_insert_ne _ _ (entry.fresh e he)).symm, entry.fresh⟩
    have oview : CaptureView eo.env (Own.bindAll eo.env ef.params vs) lexd (lexd ++ ef.params) :=
      (CaptureView.declare eo.env lexd hn).rebind ef.params vs hf
    exact .cons entry' oview
      (fun x hx => (Fir.Proof.bindAll_get_notin (ρf := ef.env) (ws := ws) (fresh_avoids hf hx)).symm) tail'

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry}

/-- A join declaration: the stack gains the entry, typed as the checker typed its body. -/
theorem OwnedState.declare (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {j : Fir.JoinId} {ps captured : List Var} {rec : Bool} {body : Code}
    (hnd : nodupVars captured = true) (hneed : Γ.needCaptured j captured = .ok ())
    (htyped : checkCode (if rec then Δ.insert j captured else Δ) (Γ.enter captured ps) body = .ok ())
    (hnone : (stackArities Jf).lookup j = none) (hf : fresh live ps = true)
    (hb : scopeOk functions (live ++ ps)
      (if rec then (j, ps.length) :: stackArities Jf else stackArities Jf) (eraseCode body) = true) :
    OwnedState functions H external live Γ ρf ρo owned ((j, live) :: lex) (Δ.insert j captured)
      ({ id := j, charged := false, env := ρf, params := ps, body := eraseCode body,
         isRec := rec } :: Jf)
      ({ id := j, charged := false, env := ρo, params := ps, body, isRec := rec } :: Jo) := by
  have hfresh := lookup_none_fresh hnone
  have hcap := Ctx.needCaptured_avail hneed
  have entry : OwnedEntry (Δ.insert j captured) Δ Γ live captured Jf
      { id := j, charged := false, env := ρf, params := ps, body := eraseCode body, isRec := rec }
      { id := j, charged := false, env := ρo, params := ps, body, isRec := rec } := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, htyped, fun x hx => ?_, fun x hx => st.known x ?_,
      fun c hc => st.known c (Ctx.avail_known (hcap c hc)), nodupVars_nodup hnd,
      Src.NatMap.get?_insert_self .., fun e he => (Src.NatMap.get?_insert_ne _ _ (hfresh e he)).symm,
      hfresh⟩
    · obtain ⟨v, hv, himm⟩ := st.immOk x hx
      obtain ⟨v', w, hv', hw, hd⟩ := st.den x (by simp [Ctx.avail_eq, hx])
      have : v' = v := Option.some.inj (hv'.symm.trans hv)
      subst this
      exact ⟨v', w, hv, hw, himm, fun H' => den_imm himm hd⟩
    · simp [Ctx.known_eq, hx]
  exact { st with
    stack := .cons entry (CaptureView.declare ρo live st.distinct) (fun _ _ => rfl)
      (st.stack.transfer (fun e he => Src.NatMap.get?_insert_ne _ _ (hfresh e he)))
    scope := .cons
      (e := { id := j, charged := false, env := ρf, params := ps, body := eraseCode body, isRec := rec })
      (List.Sublist.refl _) ⟨hf, hb⟩ st.scope }

/-- **A checked jump**: the target found on both stacks, the arguments, and the state its body
starts from — the arguments' tokens and those of the captured variables that are not immediates
of the declaration, exactly the context the body was checked from. -/
theorem jump_body (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {j : Fir.JoinId} {args : List Arg} {captured : List Var} {Γ₁ Γ₂ : Ctx} {what : String}
    (hΔ : Δ.get? j = some captured) (h1 : Γ.takeArgs args = .ok Γ₁)
    (h2 : Γ₁.takeVars captured = .ok Γ₂) (h3 : Γ₂.closed what = .ok ())
    {ef : Fir.JEntry} {restf : List Fir.JEntry} (hl : Fir.lookupJ j Jf = some (ef, restf)) :
    ∃ (vs : List RVal) (ws : List Fir.Val) (eo : JEntry) (resto : List JEntry),
      Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      vs.length = ws.length ∧ lookupJ j Jo = some (eo, resto) ∧ eo.params = ef.params ∧
      eo.charged = ef.charged ∧
      (ws.length = ef.params.length →
        ∃ (Δb : JCtx) (Γb : Ctx) (lexd : List Var) (lexb : Joins) (owned' : List RVal),
          OwnedState functions H external (lexd ++ ef.params) Γb
            (Fir.bindAll ef.env ef.params ws) (Own.bindAll eo.env eo.params vs) owned' lexb Δb
            (ef.after restf) (eo.after resto) ∧
          checkCode Δb Γb eo.body = .ok () ∧ eraseCode eo.body = ef.body ∧
          scopeOk functions (lexd ++ ef.params) (stackArities (ef.after restf)) ef.body = true) := by
  obtain ⟨lexd, captured', older, Δd, Γd, eo, resto, hlo, entry, oview, fview, tail, escope,
    tscope⟩ := st.stack.lookup st.scope hl
  have hid := Fir.lookupJ_id hl
  have hc : captured' = captured := by
    have := entry.here; rw [hid, hΔ] at this; exact (Option.some.inj this).symm
  subst captured'
  obtain ⟨vs, ws, owned₁, hvs, hws, hds, inv₁, hs₁, hw₁⟩ := takeArgs_sem st.takeInv h1
  obtain ⟨cvs, owned₂, hcvs, havail, inv₂, hs₂, _⟩ := takeVars_sem inv₁ h2
  obtain ⟨toks₂, htok₂, hr₂⟩ := inv₂.roots
  have hnil := closed_nil htok₂ h3
  subst hnil
  have ho₂ := EnvRoots.nil_inv hr₂
  subst ho₂
  refine ⟨vs, ws, eo, resto, hvs, hws, hds.length, hlo, entry.params, entry.charged, fun hlen => ?_⟩
  -- The captured variables the body holds tokens for, and their values.
  let p : Var → Bool := fun c => !Γd.isImm c
  have hsubC : ∀ c, c ∈ captured → c ∈ lexd := entry.sub
  have hsav : ∀ c, c ∈ lexd → eo.env.get? c = ρo.get? c := oview.agree
  obtain ⟨cvsF, hcF, hsF⟩ := EnvRoots.filter p hcvs (fun c hc hpc => by
    have hi : Γd.isImm c = true := by simpa [p] using hpc
    obtain ⟨v, _, hv, _, himm, _⟩ := entry.imm c hi
    exact ⟨v, by rw [← hsav c (hsubC c hc)]; exact hv, himm⟩)
  have hfilt : ∀ c, c ∈ captured.filter p → c ∈ lexd := fun c hc => hsubC c ((List.mem_filter.mp hc).1)
  have hnlex : lexd.Nodup := oview.captured_nodup
  have hfreshF : fresh (captured.filter p) ef.params = true := fresh_mono escope.1 hfilt
  have hnodupE : (Γd.entered captured ef.params).Nodup :=
    fresh_nodup_append (entry.nodup.filter p) hfreshF
  have hcF' : EnvRoots eo.env (captured.filter p) cvsF := hcF.congr (fun c hc => hsav c (hfilt c hc))
  have hvlen : vs.length = ef.params.length := hds.length.trans hlen
  have hroots : EnvRoots (Own.bindAll eo.env eo.params vs) (Γd.entered captured ef.params)
      (cvsF ++ vs) := by
    rw [entry.params]; exact hcF'.bindAll ef.params vs hvlen hfreshF
  have hbal : Balance H external (cvsF ++ vs) := by
    have h0 : SameRefs owned (vs ++ cvsF) :=
      hs₁.trans (SameRefs.append (SameRefs.refl vs) (hs₂.trans (by simpa using hsF)))
    exact (h0.trans (SameRefs.comm vs cvsF)).balance st.counts
  -- Denotations of what the body may read.
  have hdenF : EnvDen H (captured.filter p) ef.env eo.env := by
    intro c hc
    have hcC : c ∈ captured := (List.mem_filter.mp hc).1
    obtain ⟨v, w, hv, hw, hd⟩ := inv₁.den c (havail c hcC)
    exact ⟨v, w, by rw [hsav c (hsubC c hcC)]; exact hv, by rw [fview c (hsubC c hcC)]; exact hw, hd⟩
  have hdenB := hdenF.bindAll ef.params hds hvlen
  have hbody : ∀ x, x ∈ lexd → (Own.bindAll eo.env eo.params vs).get? x = eo.env.get? x ∧
      (Fir.bindAll ef.env ef.params ws).get? x = ef.env.get? x := by
    intro x hx
    have hnp : x ∉ ef.params := fresh_avoids escope.1 hx
    refine ⟨?_, Fir.Proof.bindAll_get_notin hnp⟩
    rw [entry.params]; exact get_bindAll_untouched eo.env ef.params vs x hnp
  have htokB := Ctx.Tokens.enter Γd captured ef.params hnodupE
  have hown : ∀ y, (Γd.enter captured ef.params).own.contains y = true →
      y ∈ Γd.entered captured ef.params := fun y hy => Ctx.ownHas_ofList hnodupE hy
  have hbrwB : ∀ y, (Γd.enter captured ef.params).brw.get? y = none := fun _ => rfl
  refine ⟨_, _, lexd, _, cvsF ++ vs, ⟨fun y hy => ?_, ⟨_, htokB, hroots⟩, hbal, fun y hy => ?_,
    fresh_nodup_append hnlex escope.1, fun y hy => ?_, fun y hy => ?_, fun y e hy => ?_,
    entry.after_stack tail hnlex escope.1 vs ws, StackScope.after escope tscope⟩,
    entry.typed, entry.erases, by rw [stackArities_after]; exact escope.2⟩
  · -- avail in the body: an immediate of the declaration, or a token.
    simp only [Ctx.avail_eq, Ctx.borrowed_eq, hbrwB, Bool.or_eq_true, decide_eq_true_eq] at hy
    rcases hy with (hi | hp) | hb
    · obtain ⟨v, w, hv, hw, himm, hall⟩ := entry.imm y hi
      obtain ⟨h1', h2'⟩ := hbody y (entry.immIn y hi)
      exact ⟨v, w, by rw [h1']; exact hv, by rw [h2']; exact hw, hall H⟩
    · have hm : y ∈ Γd.entered captured ef.params := htokB.mem hp
      rw [entry.params]; exact hdenB y hm
    · simp at hb
  · simp only [Ctx.known_eq, hbrwB, Option.isSome_none, Bool.or_false, Bool.or_eq_true] at hy
    rcases hy with hi | ho
    · exact List.mem_append_left _ (entry.immIn y hi)
    · rcases List.mem_append.mp (hown y ho) with hm | hm
      · exact List.mem_append_left _ (hfilt y hm)
      · exact List.mem_append_right _ hm
  · obtain ⟨v, _, hv, _, himm, _⟩ := entry.imm y hy
    exact ⟨v, by rw [(hbody y (entry.immIn y hy)).1]; exact hv, himm⟩
  · simp [Ctx.borrowed_eq, hbrwB] at hy
  · simp [hbrwB] at hy

end

end IxCC.Own.Plain
