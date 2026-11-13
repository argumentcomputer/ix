  obtain ⟨q, bs, hag, -, hrefs, -, hterm⟩ := hfr
  have hsp := spineL_app f a m r
  have hmk := mkApps_spineL f
  rw [← hmk, eval_mkApps] at he
  obtain ⟨v0, hv0, he⟩ := bind_ok_inv he
  unfold WrittenErasedArg at hwe
  rw [hsp] at hwe
  have hlen : (f.spineL.2 ++ [(a, m, r)]).length - 1 = f.spineL.2.length := by simp
  have hhead := congrArg Prod.fst hsp
  generalize hH : f.spineL.1 = H at hwe hv0 hhead
  cases H with
  | const c us =>
    obtain ⟨d, hd, hn⟩ := hwe
    rw [hlen] at hn
    -- the head constant is reached
    have hmem := head_mem_relevantRefs q (Term.app f a m r) [] hhead
    have hreach : c ∈ ch.reached := by
      rcases hrefs _ hmem with hge | hin
      · exfalso
        have hent := (hf.canon.dense c hge).1
        simp [Program.decl?, hent] at hd
      · exact hf.reached _ hin
    obtain ⟨cr, hcr⟩ := Option.isSome_iff_exists.1 (hf.canon.reachedRecord c hreach)
    obtain ⟨rr, hrr, hirr⟩ := param_erased_irr (hf.canon.consts c cr hcr) hd hn
    have hrd := hf.canon.reads c hreach
    rw [eval_const] at hv0
    generalize us.map (evalUniv ls) = ls' at hv0
    -- a special head: its partial application, the position below its arity
    have special : ∀ h, specialHead? p c = some h → headConst? h = some c →
        headValue p k ls' h = .ok v0 → IgnoresNext ann fv := by
      intro h hh hc hhv
      have hlt := erased_lt_arity hrd hh hd hn
      rw [headValue_eq] at hhv
      have hne : (p.headArity h == 0) = false := by simp; omega
      rw [hne] at hhv
      simp only [Bool.false_eq_true, ite_false, Sem.Result.ok.injEq] at hhv
      subst hhv
      rw [applySpine_pap_lt p k ls ρ h ls' [] f.spineL.2 (by simpa using hlt)] at he
      obtain ⟨ss, hss, he⟩ := bind_ok_inv he
      simp only [List.nil_append, Sem.Result.ok.injEq] at he
      subst he
      have hl := slotsOf_length p k ls ρ _ _ hss
      exact ⟨c, cr, rr, hc, hcr, by rw [hl]; exact hrr, alwaysIrr_irrAt hirr _⟩
    -- a head reading every argument writes none erased
    have reads : ∀ h, specialHead? p c = some h → readsAt p ann c h f.spineL.2.length = true → False := by
      intro h hh hr
      have := hrd h d hh hd _ hn
      rw [hr] at this
      cases this
    rw [evalConst_eq] at hv0
    cases hres : p.table.resolveOf c with
    | some e =>
      rw [hres] at hv0
      cases e with
      | prim op => exact (reads (.prim op) (by simp [specialHead?, hres]) (by simp [readsAt, headReadsWith])).elim
      | word w op thm => exact (reads (.word w op) (by simp [specialHead?, hres]) (by simp [readsAt, headReadsWith])).elim
      | csimp g vs thm =>
        have := hf.canon.csimp c hreach cr d g vs thm hcr hd hres
        rw [this] at hn
        cases hn
      | eqn thm body =>
        cases k with
        | zero => cases hv0
        | succ k' =>
          simp only [Sem.later_succ] at hv0
          have hb := hf.canon.bodies c hreach cr d hcr hd (.eqn c) body (by simp [runBodies, hres])
          exact body_prefix hb hn hrr hirr rfl hv0 he
      | case r' => exact special (.cases c) (by simp [specialHead?, hres]) rfl hv0
    | none =>
      cases d with
      | ctor sf lv ind cidx np nf ty =>
        simp only [hres, hd] at hv0
        exact special (.ctor c) (by simp [specialHead?, hres, hd]) rfl hv0
      | recr sf kk lv np nmot nmin ni ind rules ty =>
        simp only [hres, hd] at hv0
        exact special (.recr c) (by simp [specialHead?, hres, hd]) rfl hv0
      | quot kind lv ty =>
        cases kind with
        | ctor => simp only [hres, hd] at hv0; exact special (.quotMk c) (by simp [specialHead?, hres, hd]) rfl hv0
        | lift => simp only [hres, hd] at hv0; exact special (.quotLift c) (by simp [specialHead?, hres, hd]) rfl hv0
        | type => simp only [hres, hd] at hv0; cases hv0
        | ind => simp only [hres, hd] at hv0; cases hv0
      | defn kind safety lv ty v =>
        cases kind <;> cases safety <;> simp only [hres, hd] at hv0 <;> try (cases hv0; done)
        all_goals first
          | (cases k with
              | zero => cases hv0
              | succ k' =>
                simp only [Sem.later_succ] at hv0
                have hb := hf.canon.bodies c hreach cr _ hcr hd (.value c) v (by simp [runBodies, hres, hd])
                exact body_prefix hb hn hrr hirr rfl hv0 he)
          | (split at hv0
             · rename_i hop
               cases k with
               | zero => cases hv0
               | succ k' =>
                 simp only [Sem.later_succ] at hv0
                 have hb := hf.canon.bodies c hreach cr _ hcr hd (.value c) v
                   (by simp [runBodies, hres, hd, hop])
                 exact body_prefix hb hn hrr hirr rfl hv0 he
             · cases hv0)
      | induct => simp only [hres, hd] at hv0; cases hv0
      | axio => simp only [hres, hd] at hv0; cases hv0
  | lam b d0 body =>
    obtain ⟨bd, hbd, hwr⟩ := hwe
    rw [hlen] at hbd
    rw [eval_lam] at hv0
    cases hv0
    have htc : TermC p ann q bs (.lam b d0 body) := by
      rcases hterm with ht | ⟨more, -, hsc, -⟩ | ⟨c, us, hc, -⟩
      · cases ht with
        | app _ hsf _ => exact spineC_head_lam hsf hH
      · cases hsc with
        | app hsf _ => exact spineC_head_lam hsf hH
        | head hne _ _ => exact absurd rfl (hne f a m r)
      · cases hc
    have hirrP := termC_lamBinder_erased htc hbd hwr
    have hirr : bd.rel.irrAt ls = true := by
      unfold Rel.irrAt
      unfold Rel.irrP at hirrP
      rw [← hag.holds]
      exact hirrP
    refine (applySpine_lamChain f.spineL.2 b d0 body ρ ls bd.rel fv ?_ hirr he).1
    rw [lamRels_eq, List.getElem?_map, hbd]
    rfl
  | var _ => exact hwe.elim
  | sort _ => exact hwe.elim
  | app => exact hwe.elim
  | pi => exact hwe.elim
  | letE => exact hwe.elim
  | proj => exact hwe.elim
  | natLit _ => exact hwe.elim
  | strLit _ => exact hwe.elim
