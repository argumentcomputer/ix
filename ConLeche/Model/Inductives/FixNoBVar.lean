module

public import ConLeche.Model.Inductives.StructEntryFree
public import ConLeche.Semantics.NoBVar
public section

/-!
# Readings of leaf-free terms mention no excluded variable (task #188)

`denoteMeta_liftN_of_leaf_free` (`ConLeche/Model/Inductives/StructEntryFree.lean`)
for a SET of excluded variables at once: a term none of whose leaves
is an excluded variable reads, at depth `d`, to a term mentioning none
of the slots those variables read as (`NoBVar (exclP Q d)`), so its
interpretation and grading ignore what the frame holds there
(`interp_congr_noBVar`, `WellDenoted_congr_noBVar`).  The recursive
route reads a constructor's ordinary domains at frames whose recursive
slots hold an arbitrary member of a family other than the block's —
the functor's argument — and this is what carries their grading over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- The slots the variables of `Q` read as at depth `d`. -/
@[expose] def exclP (Q : Nat → Prop) (d : Nat) : Nat → Prop :=
  fun i => ∃ q, Q q ∧ q < d ∧ i = d - 1 - q

theorem shiftP_exclP (Q : Nat → Prop) (d : Nat) (hQ : ∀ q, Q q → q < d) :
    ∀ i, shiftP (exclP Q d) i ↔ exclP Q (d + 1) i := by
  intro i
  cases i with
  | zero =>
    simp only [shiftP, exclP, false_iff]
    rintro ⟨q, hq, -, h⟩
    have := hQ q hq
    omega
  | succ i =>
    simp only [shiftP, exclP]
    constructor
    · rintro ⟨q, hq, hlt, rfl⟩
      exact ⟨q, hq, by omega, by omega⟩
    · rintro ⟨q, hq, hlt, h⟩
      exact ⟨q, hq, by have := hQ q hq; omega, by omega⟩

omit [SetTheory V] in
theorem NoBVar_congr {P P' : Nat → Prop} (h : ∀ i, P i ↔ P' i) :
    ∀ (e : AnnotTerm), NoBVar P e → NoBVar P' e := by
  intro e
  induction e generalizing P P' with
  | bvar i => intro hn; exact fun hp => hn ((h i).mpr hp)
  | sort _ => intro; trivial
  | const _ _ => intro; trivial
  | prf => intro; trivial
  | app f a ihf iha => intro hn; exact ⟨ihf h hn.1, iha h hn.2⟩
  | lam _ A b ihA ihb =>
    intro hn
    refine ⟨ihA h hn.1, ihb (P := shiftP P) (P' := shiftP P') ?_ hn.2⟩
    intro i; cases i with
    | zero => exact Iff.rfl
    | succ i => exact h i
  | pi _ _ A B ihA ihB =>
    intro hn
    refine ⟨ihA h hn.1, ihB (P := shiftP P) (P' := shiftP P') ?_ hn.2⟩
    intro i; cases i with
    | zero => exact Iff.rfl
    | succ i => exact h i
  | eqE a b iha ihb => intro hn; exact ⟨iha h hn.1, ihb h hn.2⟩
  | fst e ih => intro hn; exact ih h hn
  | snd e ih => intro hn; exact ih h hn

omit [SetTheory V] in
theorem NoBVar_projAV {P : Nat → Prop} :
    ∀ (i : Nat) (e : AnnotTerm), NoBVar P e → NoBVar P (projAV i e)
  | 0, _, h => h
  | i + 1, e, h => NoBVar_projAV i (.snd e) h

/-- **A leaf-free reading mentions none of the excluded slots.** -/
theorem noBVar_of_leaf_free {env : Env} (m : EnvModel V env) {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr), Expr.WScoped d e →
      ∀ {Q : Nat → Prop}, (∀ q, Q q → q < d) → (∀ l ∈ e.fvarLeaves, ¬ Q l.1) →
      ∀ {ea : AnnotTerm}, denoteMeta m.acval env φ d e = some ea →
      NoBVar (exclP Q d) ea := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro _ Q _ _ ea h
    rw [denoteMeta] at h
    rw [← Option.some.inj h]
    trivial
  | case2 d idx ty =>
    intro hw Q hQ hl ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    simp only [Expr.WScoped] at hw
    have hne : ¬ Q idx := hl (idx, ty) (by simp [Expr.fvarLeaves])
    show ¬ exclP Q d (d - 1 - idx)
    rintro ⟨q, hq, hlt, heq⟩
    have : q = idx := by omega
    exact hne (this ▸ hq)
  | case3 d n us ci hf hlen =>
    intro _ Q _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    exact NoBVar_of_bvarsBelow (m.cval_closedL _ _) (fun i _ => Nat.zero_le i)
  | case4 d n us ci hf hlen =>
    intro _ Q _ _ ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro _ Q _ _ ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro hw Q hQ hl ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    simp only [Expr.WScoped] at hw
    have h1 := ihty hw.1 hQ (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hta
    have h2 := ihbody (Expr.WScoped.instantiate1 hw.1 0 hw.2) (Q := Q)
      (fun q hq => Nat.lt_succ_of_lt (hQ q hq)) (by
        intro l hl'
        rcases Expr.fvarLeaves_instantiate1 body 0 hl' with hl' | hl'
        · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')
        · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
          rcases hl' with rfl | hl'
          · exact fun hq => by have := hQ _ hq; simp at this
          · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hba
    exact ⟨h1, NoBVar_congr (fun i => (shiftP_exclP Q d hQ i).symm) _ h2⟩
  | case7 d ty body mb ihty ihbody =>
    intro hw Q hQ hl ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    simp only [Expr.WScoped] at hw
    have h1 := ihty hw.1 hQ (fun l hl' => hl l (by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hta
    have h2 := ihbody (Expr.WScoped.instantiate1 hw.1 0 hw.2) (Q := Q)
      (fun q hq => Nat.lt_succ_of_lt (hQ q hq)) (by
        intro l hl'
        rcases Expr.fvarLeaves_instantiate1 body 0 hl' with hl' | hl'
        · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')
        · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
          rcases hl' with rfl | hl'
          · exact fun hq => by have := hQ _ hq; simp at this
          · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hba
    exact ⟨h1, NoBVar_congr (fun i => (shiftP_exclP Q d hQ i).symm) _ h2⟩
  | case8 d f a ihf iha =>
    intro hw Q hQ hl ea h
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    simp only [Expr.WScoped] at hw
    exact ⟨ihf hw.1 hQ (fun l hl' => hl l (by
        simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl')) hfa,
      iha hw.2 hQ (fun l hl' => hl l (by
        simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl')) haa⟩
  | case9 d ty val body =>
    intro _ Q hQ hl ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hw Q hQ hl ea h
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
    simp only [Expr.WScoped] at hw
    have h1 := ihe hw hQ (fun l hl' => hl l (by simpa [Expr.fvarLeaves] using hl')) hia
    rcases hcase with ⟨_, -, rfl⟩ | ⟨-, hdec⟩
    · exact NoBVar_projAV _ ia h1
    · rcases AnnotTerm.projPair?_cases hdec with rfl | rfl
      · exact h1
      · exact h1
  | case11 d n hsup =>
    intro _ Q _ _ ea h
    have h0 : denoteMeta m.acval env φ 0 (.lit (.natVal n)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    have hcl := bvarsBelow_of_reading (m := m) (d := 0) (e := .lit (.natVal n))
      (Expr.WScoped.of_not_hasFvar rfl) rfl h0
    exact NoBVar_of_bvarsBelow hcl (fun i _ => Nat.zero_le i)
  | case12 d n hsup =>
    intro _ Q _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ Q _ _ ea h
    have h0 : denoteMeta m.acval env φ 0 (.lit (.strVal s)) = some ea := by
      rw [denoteMeta, if_pos hsup] at h ⊢; exact h
    have hcl := bvarsBelow_of_reading (m := m) (d := 0) (e := .lit (.strVal s))
      (Expr.WScoped.of_not_hasFvar rfl) rfl h0
    exact NoBVar_of_bvarsBelow hcl (fun i _ => Nat.zero_le i)
  | case14 d s hsup =>
    intro _ Q _ _ ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ Q _ _ ea h
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

end ConLeche.Model
