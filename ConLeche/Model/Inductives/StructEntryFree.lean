module

public import ConLeche.Model.Inductives.StructEntryKit2
public section

/-!
# Unused fields are invariant (task #175 W4c, P3 module 7, part 10)

The official `infer_proj` guard joins only the earlier fields *a
later field uses* (`structUsedLater`: the field's variable occurs in
the constructor telescope after its binder).  At a squash instance
the structure's members are one point and every earlier projection
reads as the point, so the projection law needs the field's type at
the **point prefix**; the guard makes the used earlier fields proof
fields (their fitting values are the point), and an unused one must
not matter.  This module carries that: an unused binder's variable is
absent from the opened telescope's later annotations
(`openPisAtFvars_leaf_free`), a leaf-free reading is a lift at the
leaf's index (`denoteMeta_liftN_of_leaf_free`), and interpretation and
grading are invariant under a lift's index (`interp_congr_lifts`,
`wellDenotedV_congr_lifts`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The syntax: an unused binder -/

omit [SetTheory V] in
/-- Instantiating a variable-free term above an index leaves the
lower indices' occurrences alone. -/
theorem hasLooseBVar_instantiate1_lt {v : Expr} (hv : ∀ i, v.hasLooseBVar i = false) :
    ∀ (e : Expr) (i k : Nat), i < k →
      (e.instantiate1 v k).hasLooseBVar i = e.hasLooseBVar i := by
  intro e
  induction e with
  | bvar j =>
    intro i k hik
    simp only [Expr.instantiate1]
    split
    · next hj =>
      subst hj
      rw [hv]
      simp only [Expr.hasLooseBVar]
      exact (beq_eq_false_iff_ne.mpr (by omega)).symm
    · split
      · next hj hj' =>
        simp only [Expr.hasLooseBVar]
        rw [beq_eq_false_iff_ne.mpr (show i ≠ j - 1 from by omega),
          beq_eq_false_iff_ne.mpr (show i ≠ j from by omega)]
      · rfl
  | fvar _ _ => intros; rfl
  | sort _ => intros; rfl
  | const _ _ => intros; rfl
  | lit _ => intros; rfl
  | app f a ihf iha =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihf i k hik, iha i k hik]
  | lam ty b _ ihty ihb =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihty i k hik, ihb (i + 1) (k + 1) (by omega)]
  | forallE ty b _ ihty ihb =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihty i k hik, ihb (i + 1) (k + 1) (by omega)]
  | letE t v' b iht ihv ihb =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, iht i k hik, ihv i k hik,
      ihb (i + 1) (k + 1) (by omega)]
  | proj _ _ e ihe =>
    intro i k hik
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihe i k hik]

omit [SetTheory V] in
/-- Instantiating an absent variable introduces no leaf. -/
theorem fvarLeaves_instantiate1_of_not_hasLooseBVar :
    ∀ (e v : Expr) (k : Nat), e.hasLooseBVar k = false →
      ∀ l, l ∈ (e.instantiate1 v k).fvarLeaves → l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | bvar j =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq] at hk
    simp only [Expr.instantiate1] at hl
    rw [if_neg (Ne.symm hk)] at hl
    split at hl <;> simp [Expr.fvarLeaves] at hl
  | fvar _ _ => intro v k _ l hl; exact hl
  | sort _ => intro v k _ l hl; exact hl
  | const _ _ => intro v k _ l hl; exact hl
  | lit _ => intro v k _ l hl; exact hl
  | app f a ihf iha =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihf v k hk.1 l hl)
    · exact Or.inr (iha v k hk.2 l hl)
  | lam ty b _ ihty ihb =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty v k hk.1 l hl)
    · exact Or.inr (ihb v (k + 1) hk.2 l hl)
  | forallE ty b _ ihty ihb =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty v k hk.1 l hl)
    · exact Or.inr (ihb v (k + 1) hk.2 l hl)
  | letE t v' b iht ihv ihb =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · exact Or.inl (Or.inl (iht v k hk.1.1 l hl))
    · exact Or.inl (Or.inr (ihv v k hk.1.2 l hl))
    · exact Or.inr (ihb v (k + 1) hk.2 l hl)
  | proj _ _ e ihe =>
    intro v k hk l hl
    simp only [Expr.hasLooseBVar] at hk
    simp only [Expr.instantiate1, Expr.fvarLeaves] at hl ⊢
    exact ihe v k hk l hl

omit [SetTheory V] in
theorem fvar_hasLooseBVar (idx : Nat) (ty : Expr) (i : Nat) :
    (Expr.fvar idx ty).hasLooseBVar i = false := rfl

omit [SetTheory V] in
/-- **An unused binder is absent from the opening.**  If the telescope
after binder `m` does not mention it, no later opener's annotation and
not the opened body carries the `m`-th opener as a leaf. -/
theorem openPisAtFvars_leaf_free :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr} (m : Nat)
      {bs : List (Expr × BinderMeta)} {rest : Expr},
      openPisAtFvars n e d = some (fvs, o) → m < n →
      e.stripPis (m + 1) = some (bs, rest) → rest.hasLooseBVar 0 = false →
      (∀ l ∈ e.fvarLeaves, l.1 ≠ d + m) →
      (∀ k, m < k → ∀ x, fvs[k]? = some x → ∀ l ∈ x.fvarLeaves, l.1 ≠ d + m) ∧
      (∀ l ∈ o.fvarLeaves, l.1 ≠ d + m)
  | 0, _, _, _, _, m, _, _, _, hm, _, _, _ => absurd hm (Nat.not_lt_zero m)
  | n + 1, e, d, fvs, o, m, bs, rest, hop, hm, hst, hfree, hleaves => by
    match e, hop, hst with
    | .forallE dom body mb, hop, hst =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        -- the openers' leaves are the term's or openers
        have hopen := openPisAtFvars_leaves n hop'
        have hidx := openPisAtFvars_index n _ (d + 1) hop'
        cases m with
        | zero =>
          -- `rest` is the body: the opener at `d` is never substituted
          simp only [Expr.stripPis, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨-, rfl⟩ := hst
          have hsub : ∀ l, l ∈ (body.instantiate1 (.fvar d dom)).fvarLeaves →
              l ∈ body.fvarLeaves :=
            fun l hl => fvarLeaves_instantiate1_of_not_hasLooseBVar body _ 0 hfree l hl
          have hbody : ∀ l ∈ body.fvarLeaves, l.1 ≠ d + 0 := by
            intro l hl
            exact hleaves l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl)
          have key : ∀ l, (l ∈ o'.fvarLeaves ∨ ∃ x ∈ fvs', l ∈ x.fvarLeaves) → l.1 ≠ d + 0 := by
            intro l hl
            rcases hopen l hl with h | h
            · exact hbody l (hsub l h)
            · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
              obtain ⟨ty', heq⟩ := hidx q _ hq
              have : l.1 = d + 1 + q := by
                have := congrArg (fun e => match e with | .fvar i _ => i | _ => 0) heq
                simpa using this
              omega
          refine ⟨?_, fun l hl => key l (Or.inl hl)⟩
          intro k hk x hx l hl
          cases k with
          | zero => exact absurd hk (Nat.lt_irrefl _)
          | succ k =>
            simp only [List.getElem?_cons_succ] at hx
            exact key l (Or.inr ⟨x, List.mem_of_getElem? hx, hl⟩)
        | succ m =>
          -- `rest` is below the head binder: strip it off the instantiated body
          simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
          obtain ⟨⟨bs', rest'⟩, hst', heq⟩ := hst
          simp only [Prod.mk.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          have hsome := Expr.stripPis_instantiate1_isSome (v := .fvar d dom) (m + 1) (e := body) 0
            (by rw [hst']; rfl)
          obtain ⟨⟨bs'', rest''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
          obtain ⟨hr, -⟩ := Expr.stripPis_instantiate1_eq (v := .fvar d dom) (m + 1) 0 hst' hst''
          rw [Nat.zero_add] at hr
          have hfree' : rest''.hasLooseBVar 0 = false := by
            rw [hr, hasLooseBVar_instantiate1_lt (fvar_hasLooseBVar d dom) rest' 0 (m + 1)
              (by omega)]
            exact hfree
          have hleaves' : ∀ l ∈ (body.instantiate1 (.fvar d dom)).fvarLeaves,
              l.1 ≠ d + 1 + m := by
            intro l hl
            rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl | hl
            · exact fun h => hleaves l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl)
                (by rw [h]; omega)
            · simp only [Expr.fvarLeaves, List.mem_cons] at hl
              rcases hl with rfl | hl
              · omega
              · exact fun h => hleaves l
                  (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl) (by rw [h]; omega)
          obtain ⟨h1, h2⟩ := openPisAtFvars_leaf_free n m hop' (by omega) hst'' hfree' hleaves'
          refine ⟨?_, fun l hl => by have := h2 l hl; omega⟩
          intro k hk x hx l hl
          cases k with
          | zero => exact absurd hk (Nat.not_lt_zero _)
          | succ k =>
            simp only [List.getElem?_cons_succ] at hx
            have := h1 k (by omega) x hx l hl
            omega
      · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _ | .const _ _, hop, _
    | .app _ _, hop, _ | .lam _ _ _, hop, _ | .letE _ _ _, hop, _ | .lit _, hop, _
    | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## The reading: a leaf-free term reads as a lift -/

theorem natLitAV_liftN {za sa : AnnotTerm} {k : Nat} (hz : za.liftN 1 k = za)
    (hs : sa.liftN 1 k = sa) : ∀ n, (natLitAV za sa n).liftN 1 k = natLitAV za sa n
  | 0 => hz
  | n + 1 => by
    show (AnnotTerm.app sa (natLitAV za sa n)).liftN 1 k = _
    rw [AnnotTerm.liftN_app, hs, natLitAV_liftN hz hs n]
    rfl


/-- **A leaf-free reading is a lift at the leaf's index.**  A term
without the `q`-th variable as a leaf reads, at depth `d`, as a
reading lifted over index `d - 1 - q` — the slot that variable would
read as. -/
theorem denoteMeta_liftN_of_leaf_free {env : Env} (m : EnvModel V env) {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr), Expr.WScoped d e →
      ∀ {q : Nat}, q < d → (∀ l ∈ e.fvarLeaves, l.1 ≠ q) →
      ∀ {ea : AnnotTerm}, denoteMeta m.acval env φ d e = some ea →
      ∃ X : AnnotTerm, ea = X.liftN 1 (d - 1 - q) := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro _ q _ _ ea h
    rw [denoteMeta] at h
    exact ⟨ea, by rw [← Option.some.inj h]; rfl⟩
  | case2 d idx ty =>
    intro hw q hq hl ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    simp only [Expr.WScoped] at hw
    have hne : idx ≠ q := hl (idx, ty) (by simp [Expr.fvarLeaves])
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨.bvar (d - 2 - idx), ?_⟩
      rw [AnnotTerm.liftN_bvar, if_neg (by omega)]
      congr 1
      omega
    · refine ⟨.bvar (d - 1 - idx), ?_⟩
      rw [AnnotTerm.liftN_bvar, if_pos (by omega)]
  | case3 d n us ci hf hlen =>
    intro _ q _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    exact ⟨_, (m.acval_closed _ _ _).symm⟩
  | case4 d n us ci hf hlen =>
    intro _ q _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro _ q _ _ ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro hw q hq hl ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xt, rfl⟩ := ihty hw.1 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hta
    obtain ⟨Xb, rfl⟩ := ihbody (Expr.WScoped.instantiate1 hw.1 0 hw.2) (q := q) (by omega) (by
      intro l hl'
      rcases Expr.fvarLeaves_instantiate1 body 0 hl' with hl' | hl'
      · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')
      · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact fun h => by simp at h; omega
        · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hba
    refine ⟨.pi 0 (pwBit φ mb.pw) Xt Xb, ?_⟩
    rw [AnnotTerm.liftN_pi, show d + 1 - 1 - q = d - 1 - q + 1 from by omega]
  | case7 d ty body mb ihty ihbody =>
    intro hw q hq hl ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xt, rfl⟩ := ihty hw.1 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hta
    obtain ⟨Xb, rfl⟩ := ihbody (Expr.WScoped.instantiate1 hw.1 0 hw.2) (q := q) (by omega) (by
      intro l hl'
      rcases Expr.fvarLeaves_instantiate1 body 0 hl' with hl' | hl'
      · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')
      · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact fun h => by simp at h; omega
        · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hba
    refine ⟨.lam (pwBit φ mb.pw) Xt Xb, ?_⟩
    rw [AnnotTerm.liftN_lam, show d + 1 - 1 - q = d - 1 - q + 1 from by omega]
  | case8 d f a ihf iha =>
    intro hw q hq hl ea h
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xf, rfl⟩ := ihf hw.1 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hfa
    obtain ⟨Xa, rfl⟩ := iha hw.2 hq (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')) haa
    exact ⟨.app Xf Xa, by rw [AnnotTerm.liftN_app]⟩
  | case9 d ty val body =>
    intro _ q hq hl ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hw q hq hl ea h
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
    simp only [Expr.WScoped] at hw
    obtain ⟨Xe, rfl⟩ := ihe hw hq (fun l hl' => hl l (by simpa [Expr.fvarLeaves] using hl')) hia
    rcases hcase with ⟨entry, -, rfl⟩ | ⟨-, hdec⟩
    · exact ⟨projAV (i + entry.off) Xe, by rw [projAV_liftN]⟩
    · rcases AnnotTerm.projPair?_cases hdec with rfl | rfl
      · exact ⟨.fst Xe, by rw [AnnotTerm.liftN_fst]⟩
      · exact ⟨.snd Xe, by rw [AnnotTerm.liftN_snd]⟩
  | case11 d n hsup =>
    intro _ q _ _ ea h
    rw [denoteMeta, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    exact ⟨_, (natLitAV_liftN (m.acval_closed _ _ _) (m.acval_closed _ _ _) n).symm⟩
  | case12 d n hsup =>
    intro _ q _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ q _ _ ea h
    -- the string literal's reading is closed: its own reading at depth `0`
    have h0 : denoteMeta m.acval env φ 0 (.lit (.strVal s)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    have hcl := bvarsBelow_of_reading (m := m) (d := 0) (e := .lit (.strVal s))
      (Expr.WScoped.of_not_hasFvar rfl) rfl h0
    exact ⟨ea, (AnnotTerm.liftN_eq_self ea (Term.bvarsBelow.mono (Nat.zero_le _) hcl) 1).symm⟩
  | case14 d s hsup =>
    intro _ q _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ q _ _ ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## Invariance under a lift's index -/

omit [SetTheory V] in
theorem shiftE_congr_off {k : Nat} {ρ ρ' : Nat → V} (hag : ∀ i, i ≠ k → ρ i = ρ' i) :
    shiftE 1 k ρ = shiftE 1 k ρ' := by
  funext i
  unfold shiftE
  split
  · exact hag i (by omega)
  · exact hag (i + 1) (by omega)

theorem interp_congr_lift {e X : AnnotTerm} {k : Nat} (h : e = X.liftN 1 k) {ρ ρ' : Nat → V}
    (hag : ∀ i, i ≠ k → ρ i = ρ' i) : interp V ρ e = interp V ρ' e := by
  subst h
  rw [interp_liftN, interp_liftN, shiftE_congr_off hag]

theorem wellDenotedV_congr_lift {e X : AnnotTerm} {k : Nat} (h : e = X.liftN 1 k) {ρ ρ' : Nat → V}
    (hag : ∀ i, i ≠ k → ρ i = ρ' i) : WellDenotedV V ρ e ↔ WellDenotedV V ρ' e := by
  subst h
  unfold WellDenotedV
  rw [WellDenoted_liftN, WellDenoted_liftN, AnnotValid_liftN, AnnotValid_liftN, shiftE_congr_off hag]

/-- **Invariance under the free indices**: two valuations that differ
only below `N`, and only at indices the term is a lift over, interpret
the term alike. -/
theorem interp_congr_lifts :
    ∀ (N : Nat) {e : AnnotTerm} {ρ ρ' : Nat → V},
      (∀ i, i < N → ρ i ≠ ρ' i → ∃ X : AnnotTerm, e = X.liftN 1 i) →
      (∀ i, N ≤ i → ρ i = ρ' i) →
      interp V ρ e = interp V ρ' e := by
  intro N
  induction N with
  | zero =>
    intro e ρ ρ' _ hag
    have : ρ = ρ' := funext fun i => hag i (Nat.zero_le i)
    rw [this]
  | succ N ih =>
    intro e ρ ρ' hfree hag
    let ρ'' : Nat → V := fun i => if i = N then ρ' N else ρ i
    have h1 : interp V ρ e = interp V ρ'' e := by
      by_cases hN : ρ N = ρ' N
      · have : ρ'' = ρ := by
          funext i
          show (if i = N then ρ' N else ρ i) = ρ i
          split
          · next h => rw [h, hN]
          · rfl
        rw [this]
      · obtain ⟨X, hX⟩ := hfree N (Nat.lt_succ_self N) hN
        exact interp_congr_lift hX fun i hi => by
          show ρ i = (if i = N then ρ' N else ρ i)
          rw [if_neg hi]
    rw [h1]
    refine ih ?_ ?_
    · intro i hi hne
      have hiN : i ≠ N := by omega
      refine hfree i (by omega) ?_
      show ρ i ≠ ρ' i
      have : ρ'' i = ρ i := by show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg hiN]
      rw [this] at hne
      exact hne
    · intro i hi
      rcases Nat.lt_or_ge i (N + 1) with hlt | hge
      · have : i = N := by omega
        subst this
        show (if i = i then ρ' i else ρ i) = ρ' i
        rw [if_pos rfl]
      · have : ρ'' i = ρ i := by
          show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg (by omega)]
        rw [this]
        exact hag i hge

theorem wellDenotedV_congr_lifts :
    ∀ (N : Nat) {e : AnnotTerm} {ρ ρ' : Nat → V},
      (∀ i, i < N → ρ i ≠ ρ' i → ∃ X : AnnotTerm, e = X.liftN 1 i) →
      (∀ i, N ≤ i → ρ i = ρ' i) →
      (WellDenotedV V ρ e ↔ WellDenotedV V ρ' e) := by
  intro N
  induction N with
  | zero =>
    intro e ρ ρ' _ hag
    have : ρ = ρ' := funext fun i => hag i (Nat.zero_le i)
    rw [this]
  | succ N ih =>
    intro e ρ ρ' hfree hag
    let ρ'' : Nat → V := fun i => if i = N then ρ' N else ρ i
    have h1 : WellDenotedV V ρ e ↔ WellDenotedV V ρ'' e := by
      by_cases hN : ρ N = ρ' N
      · have : ρ'' = ρ := by
          funext i
          show (if i = N then ρ' N else ρ i) = ρ i
          split
          · next h => rw [h, hN]
          · rfl
        rw [this]
      · obtain ⟨X, hX⟩ := hfree N (Nat.lt_succ_self N) hN
        exact wellDenotedV_congr_lift hX fun i hi => by
          show ρ i = (if i = N then ρ' N else ρ i)
          rw [if_neg hi]
    rw [h1]
    refine ih ?_ ?_
    · intro i hi hne
      have hiN : i ≠ N := by omega
      refine hfree i (by omega) ?_
      show ρ i ≠ ρ' i
      have : ρ'' i = ρ i := by show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg hiN]
      rw [this] at hne
      exact hne
    · intro i hi
      rcases Nat.lt_or_ge i (N + 1) with hlt | hge
      · have : i = N := by omega
        subst this
        show (if i = i then ρ' i else ρ i) = ρ' i
        rw [if_pos rfl]
      · have : ρ'' i = ρ i := by
          show (if i = N then ρ' N else ρ i) = ρ i; rw [if_neg (by omega)]
        rw [this]
        exact hag i hge

/-! ## The point prefix against a fitting prefix -/

/-- The point prefix and a fitting prefix differ only at the slots
whose fitting value is not the point; below the prefix both frames
are the parameters'. -/
theorem consList_prefix_agree {i : Nat} {as : List V} (hlen : as.length = i) (ρ' : Nat → V) :
    (∀ k, k < i → consList (List.replicate i pt) ρ' k ≠ consList as ρ' k →
      as.getD (i - 1 - k) pt ≠ pt) ∧
    (∀ k, i ≤ k → consList (List.replicate i pt) ρ' k = consList as ρ' k) := by
  constructor
  · intro k hk hne
    rw [consList_apply_lt _ _ _ (by rw [List.length_replicate]; exact hk),
      consList_apply_lt _ _ _ (by rw [hlen]; exact hk), List.length_replicate, hlen] at hne
    rw [List.getElem?_replicate, if_pos (by omega), List.getElem?_eq_getElem (by omega)] at hne
    simp only [Option.getD_some] at hne
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    exact fun h => hne h.symm
  · intro k hk
    have h1 := consList_apply_add (List.replicate i pt) ρ' (k - i)
    have h2 := consList_apply_add as ρ' (k - i)
    rw [List.length_replicate, show k - i + i = k from by omega] at h1
    rw [hlen, show k - i + i = k from by omega] at h2
    rw [h1, h2]

/-- **A differing slot is unused**: where the point prefix and a fitting
prefix differ, the fitting value is not the point, so that field is
not a proposition there, so (under the guard) no later field uses it,
so the projected field is a lift over that slot. -/
theorem free_of_diff {nP nF i : Nat} {ds : List (Nat × Nat × AnnotTerm)} {sorts : List Level}
    {ψ : Name → Nat} {ρ' : Nat → V} {used : Nat → Bool}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ j, j < nF → ∀ as : List V,
      SpineFit ρ' (((ds.drop nP).map (·.2.2)).take j) as →
      interp V (consList as ρ') (((ds.drop nP).map (·.2.2)).getD j default)
        ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hguard : ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    {as' : List V} (hspAs : SpineFit ρ' ((ds.drop nP).map (·.2.2)) as') :
    ∀ k, k < i → consList (List.replicate i pt) ρ' k ≠ consList (as'.take i) ρ' k →
      ∃ X : AnnotTerm, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 k := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenTake : (as'.take i).length = i := by
    rw [List.length_take, hspAs.length_eq, hlenFs]; omega
  intro k hk hne
  have hne' := (consList_prefix_agree hlenTake ρ').1 k hk hne
  have hun : used (i - 1 - k) = false := by
    cases hu : used (i - 1 - k)
    · rfl
    · exfalso
      apply hne'
      obtain ⟨hpre, hnext⟩ :=
        spineFit_prefix_next hspAs (i := i - 1 - k) (by rw [hlenFs]; omega)
      have hs := hsorts (i - 1 - k) (by omega) _ hpre
      rw [hguard (i - 1 - k) (by omega) hu] at hs
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
        ← List.getD_eq_getElem?_getD]
      exact mem_univ_zero hs hnext
  obtain ⟨X, hX⟩ := hfree (i - 1 - k) (by omega) hun
  rw [show i - 1 - (i - 1 - k) = k from by omega] at hX
  exact ⟨X, hX⟩

/-- The prefix of a fitting spine has the prefix's length. -/
theorem spineFit_take_length {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) : (as.take i).length = i := by
  rw [List.length_take, h.length_eq]; omega

/-! ## The official guard's spelling -/

omit [SetTheory V] in
/-- The evaluated join over the used slots is zero exactly when the
base and every used joined level are. -/
theorem eval_foldl_max_if_zero_iff (ψ : Name → Nat) (used : Nat → Bool) (s : Nat → Level) :
    ∀ (l : List Nat) (s0 : Level),
      Level.eval ψ (l.foldl (fun acc j => if used j then Level.max acc (s j) else acc) s0) = 0 ↔
        Level.eval ψ s0 = 0 ∧ ∀ j ∈ l, used j = true → Level.eval ψ (s j) = 0
  | [], s0 => by simp
  | a :: l, s0 => by
    rw [List.foldl_cons, eval_foldl_max_if_zero_iff ψ used s l]
    cases hu : used a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, forall_eq_or_imp, hu,
        false_implies, true_and]
    · simp only [↓reduceIte, Level.eval, Nat.max_eq_zero_iff, List.mem_cons, forall_eq_or_imp,
        hu, forall_const]
      constructor
      · rintro ⟨⟨h0, ha⟩, hl⟩; exact ⟨h0, ha, hl⟩
      · rintro ⟨h0, ha, hl⟩; exact ⟨⟨h0, ha⟩, hl⟩

end ConLeche.Model
