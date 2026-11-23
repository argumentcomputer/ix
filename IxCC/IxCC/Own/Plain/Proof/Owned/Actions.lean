import IxCC.Own.Plain.Proof.Owned.Binds

/-! # `inc` and `dec` steps

`inc x 1` adds a token: `inc_root` (owned: the token's own count; borrowed: the projected cell's
live edge, kept as `BorrowVal`; immediate: a no-op). `dec x` takes one and is a release:
`dropAll_retaining` keeps the value of every remaining token, nothing stays epoch-borrowed, and
surviving `@unique` variables, live reset slots, and `priv` locations stay untouched. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var)

theorem mem_of_refsIn_pos {l : Nat} : ∀ {xs : List RVal}, 0 < refsIn l xs → RVal.loc l ∈ xs
  | [], h => by simp [refsIn] at h
  | x :: xs, h => by
    by_cases hx : x = .loc l
    · subst hx; exact List.mem_cons_self
    · simp only [refsIn, hx, ↓reduceIte, Nat.zero_add] at h
      exact List.mem_cons_of_mem _ (mem_of_refsIn_pos h)

/-- Values kept for the remaining tokens and for the external owners are kept for both. -/
theorem preserved_hold {H H' : Heap} {external : Nat → Nat} {held : List RVal}
    (hheld : ∀ root, root ∈ held → H.value? root = H'.value? root)
    (hext : ∀ root, ExternalRoot external root → H.value? root = H'.value? root) :
    ExternalPreserved H H' (holdRoots external held) := by
  intro root w hr hd
  change H'.value? root = some w
  have hv : H.value? root = H'.value? root := by
    cases root with
    | loc l =>
      change 0 < external l + refsIn l held at hr
      by_cases he : 0 < external l
      · exact hext _ he
      · exact hheld _ (mem_of_refsIn_pos (by omega))
    | lit _ | ctor0 _ | erased => exact hext _ trivial
  rw [← hv]; exact hd

theorem asCtor_inc {H H' : Heap} {K : Lam.Known} {u v : RVal} {key : Key.CtorKey} {fs : List RVal}
    (hi : Rc.inc H u 1 = some H') (hac : v.asCtor K H = some (key, fs)) :
    v.asCtor K H' = some (key, fs) := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; exact hac
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.inc, changeCount, hc] at hi
    | some cell =>
      cases cell with
      | dead => simp [Rc.inc, changeCount, hc] at hi
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; exact hac
        | dyn =>
          by_cases hz : rc = 0
          · simp [Rc.inc, changeCount, hc, hz] at hi
          · rw [inc_dyn hc (by omega) 1] at hi
            cases hi
            have hl : l < H.size := Proof.cell?_some hc
            cases v with
            | lit lit => cases lit with | str _ => exact hac | nat n => cases n <;> exact hac
            | ctor0 _ | erased => exact hac
            | loc k =>
              cases hk : H.cell? k with
              | none => simp [RVal.asCtor, hk] at hac
              | some ck =>
                cases ck with
                | dead => simp [RVal.asCtor, hk] at hac
                | live rk mk bk =>
                  simp only [RVal.asCtor, hk] at hac
                  rw [RVal.asCtor, setCell_cell H l _ hl k]
                  by_cases he : l = k
                  · subst he; rw [hc] at hk
                    obtain ⟨-, rfl, rfl⟩ := Cell.live.inj (Option.some.inj hk)
                    simp only [↓reduceIte]; exact hac
                  · rw [ite_eq_right he, hk]; exact hac

theorem asCtor_alloc {H : Heap} {K : Lam.Known} {b : Body} {v : RVal} {key : Key.CtorKey}
    {fs : List RVal} (hac : v.asCtor K H = some (key, fs)) :
    v.asCtor K (H.alloc .rc b).2 = some (key, fs) := by
  cases v with
  | lit lit => cases lit with | str _ => exact hac | nat n => cases n <;> exact hac
  | ctor0 _ | erased => exact hac
  | loc k =>
    cases hk : H.cell? k with
    | none => simp [RVal.asCtor, hk] at hac
    | some ck =>
      have hlt : k < H.size := Proof.cell?_some hk
      have hne : k ≠ H.cells.size := Nat.ne_of_lt hlt
      have hcell : (H.alloc .rc b).2.cell? k = H.cell? k := by
        simp only [Heap.alloc, Heap.cell?, Array.getElem?_push, hne, ↓reduceIte]
      simpa [RVal.asCtor, hcell] using hac

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs} {uniqs : UniqSigs}
  {retUniq : Bool} {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
  {slots : Src.NatMap RVal} {slotVals : List RVal}

/-- Helper: two distinct variables in `toks` cannot both map to `.loc l` when `refsIn l owned ≤ 1`. -/
theorem envRoots_distinct_ne {ρ : Own.Env} {toks : List Var} {vals : List RVal}
    {x y : Var} {l : Nat} (hr : EnvRoots ρ toks vals) (hne : x ≠ y)
    (hx : x ∈ toks) (hy : y ∈ toks) (hxv : ρ.get? x = some (.loc l))
    (hyv : ρ.get? y = some (.loc l)) : 2 ≤ refsIn l vals := by
  obtain ⟨vals₁, hr₁, hs₁⟩ := EnvRoots.erase hxv hr hx
  have hy₁ : y ∈ toks.erase x := (List.mem_erase_of_ne hne.symm).mpr hy
  obtain ⟨vals₂, _, hs₂⟩ := EnvRoots.erase hyv hr₁ hy₁
  have h1 := hs₁ l
  have h2 := hs₂ l
  simp only [refsIn, ↓reduceIte] at h1 h2
  omega

/-- `inc_step` with the facts the native step needs. -/
theorem inc_step_refs (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {Γ' : Ctx} {x : Var} {n : Nat} (hc : Γ.inc x n = .ok Γ') :
    ∃ v H' owned', n = 1 ∧ ρo.get? x = some v ∧ CanDup H v ∧
      evalAction ρo H (.inc x n) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals ∧
      ExternalPreserved H H' external ∧ ReachablePreserved H H' external ∧
      SameRefs owned' (v :: owned) ∧ PrivPreserved H H' priv := by
  obtain ⟨rfl, hcase⟩ := Ctx.inc_ok hc
  obtain ⟨toks, htok, hroots⟩ := st.roots
  obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
  have havail : Γ.avail x = true := by
    rcases hcase with ⟨hi, _⟩ | ⟨_, hp | hpb, _⟩ | ⟨_, _, _, hb, _⟩
    · simp [Ctx.avail_eq, hi]
    · simp [Ctx.avail_eq, hp]
    · simp [Ctx.avail_eq, hpb]
    · simp [Ctx.avail_eq, hb]
  obtain ⟨v, w, hv, hw, hd⟩ := st.den x havail
  have hcan : CanDup H v := by
    rcases hcase with ⟨hi, _⟩ | ⟨_, hp | hpb, _⟩ | ⟨_, _, _, hb, _⟩
    · obtain ⟨v', hv', himm⟩ := st.immOk x hi
      have : v' = v := Option.some.inj (hv'.symm.trans hv); subst this
      cases v' with
      | loc l => exact absurd rfl (himm l)
      | lit _ | ctor0 _ | erased => trivial
    · exact canDup_member st.counts (List.mem_append_left _ (hroots.member (htok.mem hp) hv))
    · obtain ⟨v', hv', hreach⟩ := st.pbrwOk x hpb
      have : v' = v := Option.some.inj (hv'.symm.trans hv); subst this
      exact hreach.canDup st.counts
    · obtain ⟨v', hv', hbv⟩ := st.borrowed x hb
      have : v' = v := Option.some.inj (hv'.symm.trans hv); subst this
      exact hbv.canDup st.counts
  obtain ⟨H', hinc, hb', hvals⟩ := inc_root st.counts hcan
  have hact : evalAction ρo H (.inc x 1) = .ok H' := by
    simp [evalAction, hv, hinc, Result.ofOption]
  have hpres : ExternalPreserved H H' external :=
    ExternalPreserved.of_values (fun root _ => hvals root)
  have hreach : ReachablePreserved H H' external := ReachablePreserved.inc hinc
  have hprivBase : PrivPreserved H H' priv :=
    PrivPreserved.inc st.privNoEdge (fun l hl hEq => st.privNoVar l hl x havail (hEq ▸ hv)) hinc
  rcases hcase with ⟨hi, rfl⟩ | ⟨hi, hp, rfl⟩ | ⟨hi, h0, _, hb, rfl⟩
  · -- Immediate: a no-op
    obtain ⟨v', hv', himm⟩ := st.immOk x hi
    have : v' = v := Option.some.inj (hv'.symm.trans hv); subst this
    have hprivLoc : PrivPreserved H H' st.pre.localPriv :=
      PrivPreserved.inc (fun l hl => (st.pre.localPriv_facts hl).2) (fun l _ hEq => himm l hEq) hinc
    have pre := st.pre.transport (H' := H')
      (fun u w' h => by change H'.value? u = some w'; rw [← hvals u]; exact h)
      (fun u hu => hu.inc hinc) hreach (fun _ _ _ _ _ _ hac => asCtor_inc hinc hac) hprivLoc
    have hbal' : Balance H' external (owned ++ slotVals) :=
      (SameRefs.imm_cons himm (owned ++ slotVals)).balance hb'
    exact ⟨v', H', owned, rfl, hv, hcan, hact, pre.toState hbal', hpres, hreach,
      (SameRefs.imm_cons himm owned).symm, hprivBase⟩
  · -- Owned or caller-backed `pbrw`: clears `uniq x` and adds 1 token of `x`
    have pre₁ := st.pre.weaker (Ctx.clearUniq_weaker Γ x) ⟨toks, htok.same rfl rfl, hroots⟩
      (fun _ => Nat.le_refl _)
    have hneLoc : ∀ l, pre₁.localPriv l → v ≠ .loc l := by
      intro l hl hEq; subst hEq
      rcases hl with hpr | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, huz, hiz, hz⟩
      · exact st.privNoVar l hpr x havail hv
      · obtain ⟨sv, hsv, hrcase⟩ := pre₁.rsetOk s cls u hrs
        have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
        rcases hrcase with ⟨hc0, _⟩ | ⟨l', b, hEq', _, _, _, hext, hedge, hrefs⟩
        · cases hc0
        · cases hEq'
          have hhas : Γ.rset.contains s = true := by
            rw [Ctx.rset_clearUniq] at hrs
            simp [Src.NatMap.contains, hrs]
          have hsmem : RVal.loc l ∈ slotVals := hsroots.member ((hsk.mem s).mpr hhas) hsv
          have hspos := refsIn_pos hsmem
          rw [refsIn_append] at hrefs
          rcases hp with htokx | hpbx
          · have hxpos := refsIn_pos (hroots.member (htok.mem htokx) hv)
            omega
          · obtain ⟨u', hu', hrx⟩ := st.pbrwOk x hpbx
            have : u' = .loc l := Option.some.inj (hu'.symm.trans hv); subst this
            exact ReachableFrom.not_of_zero hext hedge hrx
      · rw [Ctx.isUniq_clearUniq, Bool.and_eq_true] at huz
        have hzx : z ≠ x := by simpa using huz.1
        obtain ⟨hmeta, u', hu', hvu⟩ := st.uniqOk z huz.2
        have : u' = .loc l := Option.some.inj (hu'.symm.trans hz); subst this
        obtain ⟨_, _, hext, hedge, hrefs⟩ := hvu
        have ht1 := (hmeta hiz).1
        rw [refsIn_append] at hrefs
        rcases hp with htokx | hpbx
        · have hge2 := envRoots_distinct_ne hroots hzx (htok.mem (by omega)) (htok.mem htokx) hz hv
          omega
        · obtain ⟨u'', hu'', hrx⟩ := st.pbrwOk x hpbx
          have : u'' = .loc l := Option.some.inj (hu''.symm.trans hv); subst this
          exact ReachableFrom.not_of_zero hext hedge hrx
    have hprivLoc : PrivPreserved H H' pre₁.localPriv :=
      PrivPreserved.inc (fun l hl => (pre₁.localPriv_facts hl).2) hneLoc hinc
    have pre := pre₁.transport (H' := H')
      (fun u w' h => by change H'.value? u = some w'; rw [← hvals u]; exact h)
      (fun u hu => hu.inc hinc) hreach (fun _ _ _ _ _ _ hac => asCtor_inc hinc hac) hprivLoc
    have hroots' : EnvRoots ρo (x :: toks) (v :: owned) := EnvRoots.cons hv hroots
    have hav' : ∀ y, ((Γ.clearUniq x).addOwn x 1).avail y = true → (Γ.clearUniq x).avail y = true := by
      intro y hy
      simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, Ctx.borrowed_eq,
        Ctx.brw_addOwn, Ctx.epoch_addOwn, Ctx.isPbrw_addOwn, Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
      split at hy
      · next he =>
        subst he
        rcases hp with htokx | hpbx
        · exact Or.inl (Or.inl (Or.inr htokx))
        · exact Or.inr hpbx
      · exact hy
    refine ⟨v, H', v :: owned, rfl, hv, hcan, hact, ?_, hpres, hreach, SameRefs.refl _, hprivBase⟩
    refine ⟨fun y hy => pre.den y (hav' y hy),
      ⟨x :: toks, (htok.same (Γ' := Γ.clearUniq x) rfl rfl).addOwn x, hroots'⟩,
      ⟨skeys, hsk.same rfl, hsroots⟩, hb', fun y hy => pre.known y ?_, pre.distinct,
      fun y hy => pre.immOk y hy, fun y hy => pre.borrowed y hy, fun y hy => pre.pbrwOk y hy,
      pre.epochs, pre.ctorOfKnown, pre.projOfKnown,
      fun y key hy hc' => pre.ctorOfOk y key (hav' y hy) hc',
      fun u y key idx hy hu hp' => pre.projOfOk u y key idx (hav' y hy) (hav' u hu) hp',
      fun y hy => ?_, fun s cls u hrs => ?_,
      pre.privBound, pre.privNoEdge,
      fun l hl y hy => pre.privNoVar l hl y (hav' y hy), pre.privNoSlot, pre.stack, pre.scope⟩
    · by_cases he : y = x
      · subst he; exact Ctx.avail_known havail
      · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn,
          Ctx.isPbrw_addOwn, he, decide_false, Bool.false_or] at hy ⊢
        exact hy
    · obtain ⟨hmeta, u, hu, hvu⟩ := pre.uniqOk y hy
      have hyx : y ≠ x := by
        rw [Ctx.isUniq_addOwn, Ctx.isUniq_clearUniq, Bool.and_eq_true] at hy
        simpa using hy.1
      refine ⟨fun hiy => ⟨by rw [Ctx.tokens_addOwn, ite_eq_right hyx]; exact (hmeta hiy).1,
        (hmeta hiy).2⟩, u, hu, ?_⟩
      cases u with
      | lit _ | erased => trivial
      | ctor0 c => exact hvu
      | loc l =>
        cases hiy : (Γ.clearUniq x).isImm y with
        | true =>
          obtain ⟨u', hu', himm⟩ := pre.immOk y hiy
          have : u' = .loc l := Option.some.inj (hu'.symm.trans hu); subst this
          exact absurd rfl (himm l)
        | false =>
          have hne : v ≠ .loc l := hneLoc l (Or.inr (Or.inr ⟨y, hy, hiy, hu⟩))
          obtain ⟨b, hcl, hext, hedge, hrefs⟩ := hvu
          exact ⟨b, hcl, hext, hedge, by
            simp only [List.cons_append, refsIn, hne, ↓reduceIte, Nat.zero_add]; exact hrefs⟩
    · obtain ⟨sv, hsv, hrcase⟩ := pre.rsetOk s cls u hrs
      refine ⟨sv, hsv, ?_⟩
      rcases hrcase with h0 | ⟨l, b, rfl, hcl, hvc, hbf, hext, hedge, hrefs⟩
      · exact Or.inl h0
      · have hne : v ≠ .loc l := hneLoc l (Or.inr (Or.inl ⟨s, cls, u, hrs, hsv⟩))
        exact Or.inr ⟨l, b, rfl, hcl, hvc, hbf, hext, hedge, by
          simp only [List.cons_append, refsIn, hne, ↓reduceIte, Nat.zero_add]; exact hrefs⟩
  · -- Epoch-borrowed: `BorrowVal H v` excludes every `localPriv l` directly!
    obtain ⟨v', hv', hbv⟩ := st.borrowed x hb
    have : v' = v := Option.some.inj (hv'.symm.trans hv); subst this
    have hneLoc : ∀ l, st.pre.localPriv l → v' ≠ .loc l := fun l hl hEq => by
      subst hEq; change 0 < edgeCount H l at hbv
      have := (st.pre.localPriv_facts hl).2; omega
    have hprivLoc : PrivPreserved H H' st.pre.localPriv :=
      PrivPreserved.inc (fun l hl => (st.pre.localPriv_facts hl).2) hneLoc hinc
    have pre := st.pre.transport (H' := H')
      (fun u w' h => by change H'.value? u = some w'; rw [← hvals u]; exact h)
      (fun u hu => hu.inc hinc) hreach (fun _ _ _ _ _ _ hac => asCtor_inc hinc hac) hprivLoc
    have htok' : Ctx.Tokens ({ Γ with brw := Γ.brw.erase x, uniq := Γ.uniq.erase x } : Ctx) toks :=
      htok.same rfl rfl
    have hroots' : EnvRoots ρo (x :: toks) (v' :: owned) := EnvRoots.cons hv hroots
    have hav' : ∀ y, (({ Γ with brw := Γ.brw.erase x, uniq := Γ.uniq.erase x } : Ctx).addOwn x 1).avail y = true →
        Γ.avail y = true := by
      intro y hy
      by_cases he : y = x
      · subst he; exact havail
      · simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, ite_eq_right he,
          Ctx.borrowed_eq, Ctx.brw_addOwn, Ctx.epoch_addOwn, Ctx.isPbrw_addOwn,
          Src.NatMap.get?_erase] at hy ⊢
        exact hy
    refine ⟨v', H', v' :: owned, rfl, hv, hcan, hact, ?_, hpres, hreach, SameRefs.refl _, hprivBase⟩
    refine ⟨fun y hy => pre.den y (hav' y hy),
      ⟨x :: toks, htok'.addOwn x, hroots'⟩, ⟨skeys, hsk.same rfl, hsroots⟩, hb',
      fun y hy => pre.known y ?_, pre.distinct, fun y hy => pre.immOk y hy,
      fun y hy => pre.borrowed y ?_, fun y hy => pre.pbrwOk y hy,
      fun y e hy => pre.epochs y e ?_, pre.ctorOfKnown, pre.projOfKnown,
      fun y key hy hc' => pre.ctorOfOk y key (hav' y hy) hc',
      fun u y key idx hy hu hp' => pre.projOfOk u y key idx (hav' y hy) (hav' u hu) hp',
      fun y hy => ?_, fun s cls u hrs => ?_,
      pre.privBound, pre.privNoEdge,
      fun l hl y hy => pre.privNoVar l hl y (hav' y hy), pre.privNoSlot, pre.stack, pre.scope⟩
    · by_cases he : y = x
      · subst he; exact Ctx.avail_known havail
      · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn,
          Ctx.isPbrw_addOwn, Src.NatMap.get?_erase, he, decide_false, Bool.false_or, ↓reduceIte] at hy ⊢
        exact hy
    · by_cases he : y = x
      · subst he; simp [Ctx.borrowed_eq, Src.NatMap.get?_erase] at hy
      · simpa [Ctx.borrowed_eq, Ctx.brw_addOwn, Ctx.epoch_addOwn, Src.NatMap.get?_erase, he] using hy
    · simp only [Ctx.brw_addOwn, Src.NatMap.get?_erase] at hy
      split at hy
      · cases hy
      · exact hy
    · have hyx : y ≠ x := by
        intro he; subst he
        simp only [Ctx.isUniq, Ctx.uniq_addOwn, Src.NatMap.contains] at hy
        rw [Src.NatMap.get?_erase] at hy
        simp at hy
      have hy0 : Γ.isUniq y = true := by
        simp only [Ctx.isUniq, Ctx.uniq_addOwn, Src.NatMap.contains] at hy ⊢
        rw [Src.NatMap.get?_erase] at hy
        simpa [hyx] using hy
      obtain ⟨hmeta, u, hu, hvu⟩ := pre.uniqOk y hy0
      refine ⟨fun hiy => ⟨by rw [Ctx.tokens_addOwn, ite_eq_right hyx]; exact (hmeta hiy).1,
        (hmeta hiy).2⟩, u, hu, ?_⟩
      cases u with
      | lit _ | erased => trivial
      | ctor0 c => exact hvu
      | loc l =>
        cases hiy : Γ.isImm y with
        | true =>
          obtain ⟨u', hu', himm⟩ := pre.immOk y hiy
          have : u' = .loc l := Option.some.inj (hu'.symm.trans hu); subst this
          exact absurd rfl (himm l)
        | false =>
          have hne : v' ≠ .loc l := hneLoc l (Or.inr (Or.inr ⟨y, hy0, hiy, hu⟩))
          obtain ⟨b, hcl, hext, hedge, hrefs⟩ := hvu
          exact ⟨b, hcl, hext, hedge, by
            simp only [List.cons_append, refsIn, hne, ↓reduceIte, Nat.zero_add]; exact hrefs⟩
    · obtain ⟨sv, hsv, hrcase⟩ := pre.rsetOk s cls u hrs
      refine ⟨sv, hsv, ?_⟩
      rcases hrcase with h0 | ⟨l, b, rfl, hcl, hvc, hbf, hext, hedge, hrefs⟩
      · exact Or.inl h0
      · have hne : v' ≠ .loc l := hneLoc l (Or.inr (Or.inl ⟨s, cls, u, hrs, hsv⟩))
        exact Or.inr ⟨l, b, rfl, hcl, hvc, hbf, hext, hedge, by
          simp only [List.cons_append, refsIn, hne, ↓reduceIte, Nat.zero_add]; exact hrefs⟩

/-- `dec_step` with the facts the native step needs. -/
theorem dec_step_refs (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {Γ' : Ctx} {x : Var} (hc : Γ.dec x = .ok Γ') :
    ∃ v H' owned', ρo.get? x = some v ∧ SameRefs owned (v :: owned') ∧
      evalAction ρo H (.dec x) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals ∧
      ExternalPreserved H H' external ∧ ReachablePreserved H H' external ∧
      PrivPreserved H H' priv := by
  obtain ⟨Γ₁, ht, rfl⟩ := Ctx.dec_ok hc
  obtain ⟨v, w, owned₁, hv, _, _, inv₁, hs, hw⟩ := take_sem st.takeInv ht
  have hb : Balance H external (v :: (owned₁ ++ slotVals)) :=
    ((SameRefs.append hs (SameRefs.refl slotVals)).trans (SameRefs.refl _)).balance st.counts
  obtain ⟨H', hact, hb', hheld, hext⟩ := evalAction_dec_owned hv hb
  have hdrop : Rc.dropAll H [v] = some H' := by
    simp only [evalAction, hv] at hact
    cases hd : Rc.dropAll H [v] with
    | none => rw [hd] at hact; cases hact
    | some H₁ => rw [hd] at hact; cases hact; rfl
  have hreachHold : ReachablePreserved H H' (holdRoots external (owned₁ ++ slotVals)) :=
    ReachablePreserved.dropAll H [v] (balance_hold.mp hb) hdrop
  have hle : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
    have := hs k; simp only [refsIn] at this; omega
  have pre₁ := st.pre.weaker hw inv₁.roots hle
  have hnb := release_borrowed pre₁.epochs
  have pre₁r := pre₁.release
  have hvNe : ∀ l, pre₁r.localPriv l → v ≠ .loc l := by
    intro l hl hEq; subst hEq
    rcases hl with hpr | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, huz, hiz, hz⟩
    · have hav : Γ.avail x = true := by
        rcases Ctx.take_ok ht with ⟨hi, _⟩ | ⟨_, n, hn, _⟩
        · simp [Ctx.avail_eq, hi]
        · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
      exact st.privNoVar l hpr x hav hv
    · obtain ⟨sv, hsv, hrcase⟩ := pre₁.rsetOk s cls u hrs
      have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
      rcases hrcase with ⟨hc0, _⟩ | ⟨l', b, hEq', _, _, _, _, _, hrefs⟩
      · cases hc0
      · cases hEq'
        have hrefs0 : refsIn l (owned ++ slotVals) = 1 := by
          obtain ⟨sv', hsv', hrc'⟩ := st.rsetOk s cls u (by rw [← hw.rset]; exact hrs)
          have : sv' = .loc l := Option.some.inj (hsv'.symm.trans hsl); subst this
          rcases hrc' with ⟨hc0, _⟩ | ⟨l'', _, hEq'', _, _, _, _, _, hr0⟩
          · cases hc0
          · cases hEq''; exact hr0
        rw [refsIn_append, hs l, refsIn, ite_eq_left rfl] at hrefs0
        rw [refsIn_append] at hrefs
        omega
    · obtain ⟨_, u', hu', hvu⟩ := pre₁.uniqOk z huz
      have : u' = .loc l := Option.some.inj (hu'.symm.trans hz); subst this
      obtain ⟨_, _, _, _, hrefs⟩ := hvu
      have hrefs0 : refsIn l (owned ++ slotVals) = 1 := by
        obtain ⟨_, u'', hu'', hvu0⟩ := st.uniqOk z (hw.isUniq z huz)
        have : u'' = .loc l := Option.some.inj (hu''.symm.trans hz); subst this
        obtain ⟨_, _, _, _, hr0⟩ := hvu0; exact hr0
      rw [refsIn_append, hs l, refsIn, ite_eq_left rfl] at hrefs0
      rw [refsIn_append] at hrefs
      omega
  have hprivLoc : PrivPreserved H H' pre₁r.localPriv :=
    PrivPreserved.dropAll H [v] (fun l hl => (pre₁r.localPriv_facts hl).2)
      (fun l hl => by simp [refsIn, hvNe l hl]) hdrop
  have pre' := pre₁r.call hnb hreachHold hprivLoc
  exact ⟨v, H', owned₁, hv, hs, hact, pre'.toState hb', ExternalPreserved.of_values hext,
    hreachHold.of_holdRoots, hprivLoc.mono (fun _ h => Or.inl h)⟩

theorem inc_step (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {Γ' : Ctx} {x : Var} {n : Nat} (hc : Γ.inc x n = .ok Γ') :
    ∃ H' owned', evalAction ρo H (.inc x n) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals ∧
      ReachablePreserved H H' external ∧ PrivPreserved H H' priv := by
  obtain ⟨_, H', owned', _, _, _, hact, st', _, hr, _, hpv⟩ := inc_step_refs st hc
  exact ⟨H', owned', hact, st', hr, hpv⟩

theorem dec_step (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {Γ' : Ctx} {x : Var} (hc : Γ.dec x = .ok Γ') :
    ∃ H' owned', evalAction ρo H (.dec x) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals ∧
      ReachablePreserved H H' external ∧ PrivPreserved H H' priv := by
  obtain ⟨_, H', owned', _, _, hact, st', _, hr, hpv⟩ := dec_step_refs st hc
  exact ⟨H', owned', hact, st', hr, hpv⟩

end

end IxCC.Own.Plain
