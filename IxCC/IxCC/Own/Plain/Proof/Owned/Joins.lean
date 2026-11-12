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
    · have hb : (j == e₀.id) = false := by simpa [eq_comm] using he
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
theorem OwnedStack.after {Δ Δd : JCtx} {Γd : Ctx} {lexd captured : List Var}
    {older : Joins} {restf : List Fir.JEntry} {resto : List JEntry} {ef : Fir.JEntry}
    {eo : JEntry} (entry : OwnedEntry Δ Δd Γd lexd captured restf ef eo)
    (tail : OwnedStack Δ ef.env eo.env lexd older restf resto) (hn : lexd.Nodup)
    (hf : fresh lexd ef.params = true) (vs : List RVal) (ws : List Fir.Val) :
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
    simp only [Fir.JEntry.after, JEntry.after, hr, hro, ↓reduceIte]
    simp only [hr, ↓reduceIte] at tail'
    have entry' : OwnedEntry (Δd.insert ef.id captured) Δd Γd lexd captured restf
        { ef with charged := true } { eo with charged := true } :=
      ⟨entry.id, rfl, entry.params, entry.isRec, entry.erases, entry.typed, entry.imm,
        entry.immIn, entry.sub, entry.nodup, Src.NatMap.get?_insert_self ..,
        fun e he => (Src.NatMap.get?_insert_ne _ _ (entry.fresh e he)).symm, entry.fresh⟩
    have oview : CaptureView eo.env (Own.bindAll eo.env ef.params vs) lexd (lexd ++ ef.params) :=
      (CaptureView.declare eo.env lexd hn).rebind ef.params vs hf
    exact .cons entry' oview
      (fun x hx => (Fir.Proof.bindAll_get_notin (fresh_avoids hf hx)).symm) tail'

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
    scope := .cons (List.Sublist.refl _) ⟨hf, hb⟩ st.scope }

end

end IxCC.Own.Plain
