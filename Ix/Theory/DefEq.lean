/-
  Ix.Theory.DefEq: Specification-level definitional equality on SVal.

  Structural comparison without eta: two values are def-eq iff they have
  the same constructor structure, matching heads, and def-eq subterms.
  Closures are opened by applying a shared fresh fvar at the current depth.
-/
import Ix.Theory.Roundtrip

namespace Ix.Theory

variable {L : Type} [BEq L] [LawfulBEq L]

/-! ## Definition -/

mutual
/-- Structural definitional equality on values at binding depth d. -/
def isDefEq_s (fuel : Nat) (v1 v2 : SVal L) (d : Nat) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match v1, v2 with
    | .sort u, .sort v => some (u == v)
    | .lit n, .lit m => some (n == m)
    | .neutral h1 sp1, .neutral h2 sp2 =>
      if h1.beq h2 then isDefEqSpine_s fuel sp1 sp2 d else some false
    | .lam d1 b1 e1, .lam d2 b2 e2 =>
      (isDefEq_s fuel d1 d2 d).bind fun domEq =>
        if !domEq then some false
        else
          let fv := SVal.neutral (.fvar d) []
          (eval_s fuel b1 (fv :: e1)).bind fun bv1 =>
          (eval_s fuel b2 (fv :: e2)).bind fun bv2 =>
          isDefEq_s fuel bv1 bv2 (d + 1)
    | .pi d1 b1 e1, .pi d2 b2 e2 =>
      (isDefEq_s fuel d1 d2 d).bind fun domEq =>
        if !domEq then some false
        else
          let fv := SVal.neutral (.fvar d) []
          (eval_s fuel b1 (fv :: e1)).bind fun bv1 =>
          (eval_s fuel b2 (fv :: e2)).bind fun bv2 =>
          isDefEq_s fuel bv1 bv2 (d + 1)
    | _, _ => some false

/-- Pointwise definitional equality on value spines. -/
def isDefEqSpine_s (fuel : Nat) (sp1 sp2 : List (SVal L)) (d : Nat) : Option Bool :=
  match sp1, sp2 with
  | [], [] => some true
  | v1 :: rest1, v2 :: rest2 =>
    (isDefEq_s fuel v1 v2 d).bind fun eq =>
      if !eq then some false
      else isDefEqSpine_s fuel rest1 rest2 d
  | _, _ => some false
end

/-! ## Sanity checks -/

#guard isDefEq_s 10 (.sort (0 : Nat)) (.sort 0) 0 == some true
#guard isDefEq_s 10 (.sort (0 : Nat)) (.sort 1) 0 == some false
#guard isDefEq_s 10 (.lit 42 : SVal Nat) (.lit 42) 0 == some true
#guard isDefEq_s 10 (.lit 1 : SVal Nat) (.lit 2) 0 == some false
#guard isDefEq_s 10 (.sort (0 : Nat)) (.lit 0) 0 == some false
#guard isDefEq_s 10 (.neutral (.fvar 0) [.lit 1] : SVal Nat) (.neutral (.fvar 0) [.lit 1]) 1 == some true
#guard isDefEq_s 10 (.neutral (.fvar 0) [] : SVal Nat) (.neutral (.fvar 1) []) 0 == some false
#guard isDefEq_s 10 (.neutral (.const 5 []) [] : SVal Nat) (.neutral (.const 5 []) []) 0 == some true
#guard isDefEq_s 20 (.lam (.sort 0) (.bvar 0) [] : SVal Nat) (.lam (.sort 0) (.bvar 0) []) 0 == some true
#guard isDefEq_s 20 (.lam (.sort 0) (.bvar 0) [] : SVal Nat) (.lam (.sort 1) (.bvar 0) []) 0 == some false
#guard isDefEq_s 30 (.lam (.sort 0) (.bvar 0) [] : SVal Nat) (.lam (.sort 0) (.lit 5) []) 0 == some false
#guard isDefEq_s 20 (.pi (.sort 0) (.bvar 0) [] : SVal Nat) (.pi (.sort 0) (.bvar 0) []) 0 == some true
#guard isDefEq_s 30 (.lam (.sort 0) (.bvar 1) [.lit 5] : SVal Nat) (.lam (.sort 0) (.bvar 1) [.lit 5]) 0 == some true
#guard isDefEq_s 0 (.sort (0 : Nat)) (.sort 0) 0 == none
-- Alpha-equivalent closures: same body different env entries that produce same value
#guard isDefEq_s 30
    (.lam (.sort 0) (.app (.bvar 0) (.bvar 1)) [.lit 42] : SVal Nat)
    (.lam (.sort 0) (.app (.bvar 0) (.bvar 1)) [.lit 42]) 0 == some true

/-! ## Helpers -/

-- For Option.bind (used by isDefEq_s/eval_s equation lemmas which reduce by rfl)
private theorem option_bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [Option.bind]

-- For Bind.bind / do notation (used by auto-generated quote_s/quoteSpine_s equation lemmas)
private theorem bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  show x.bind f = some b ↔ _
  cases x <;> simp [Option.bind]

private theorem SHead.beq_refl (h : SHead L) : h.beq h = true := by
  cases h <;> simp [SHead.beq]

private theorem SHead.beq_eq {h1 h2 : SHead L} (h : h1.beq h2 = true) : h1 = h2 := by
  cases h1 <;> cases h2 <;> simp_all [SHead.beq, beq_iff_eq]

private theorem SHead.beq_comm (h1 h2 : SHead L) : h1.beq h2 = h2.beq h1 := by
  cases h1 with
  | fvar l1 => cases h2 <;> simp [SHead.beq, Bool.beq_comm]
  | const id1 ls1 =>
    cases h2 with
    | fvar => simp [SHead.beq]
    | const id2 ls2 =>
      simp only [SHead.beq]
      cases hid : (id1 == id2) <;> cases hls : (ls1 == ls2) <;>
      cases hid' : (id2 == id1) <;> cases hls' : (ls2 == ls1) <;> simp_all [beq_iff_eq]

/-! ## Cross-constructor equation lemma helpers

  The WF-compiled mutual defs can't be reduced by the kernel with free fuel
  variables. We use the auto-generated catch-all equation lemmas to prove
  cross-constructor results, discharging preconditions via `intros; contradiction`. -/

omit [LawfulBEq L] in
private theorem isDefEq_cross {v1 v2 : SVal L} {d n : Nat}
    (h1 : ∀ u v, v1 = .sort u → v2 = .sort v → False)
    (h2 : ∀ n m, v1 = .lit n → v2 = .lit m → False)
    (h3 : ∀ h1 s1 h2 s2, v1 = .neutral h1 s1 → v2 = .neutral h2 s2 → False)
    (h4 : ∀ d1 b1 e1 d2 b2 e2, v1 = .lam d1 b1 e1 → v2 = .lam d2 b2 e2 → False)
    (h5 : ∀ d1 b1 e1 d2 b2 e2, v1 = .pi d1 b1 e1 → v2 = .pi d2 b2 e2 → False) :
    isDefEq_s (n + 1) v1 v2 d = some false :=
  isDefEq_s.eq_7 v1 v2 d n h1 h2 h3 h4 h5

omit [LawfulBEq L] in
private theorem isDefEqSpine_cross {sp1 sp2 : List (SVal L)} {d fuel : Nat}
    (h1 : sp1 = [] → sp2 = [] → False)
    (h2 : ∀ v1 r1 v2 r2, sp1 = v1 :: r1 → sp2 = v2 :: r2 → False) :
    isDefEqSpine_s fuel sp1 sp2 d = some false :=
  isDefEqSpine_s.eq_3 fuel sp1 sp2 d h1 h2

/-! ## Fuel monotonicity -/

omit [LawfulBEq L] in
private theorem isDefEqSpine_fuel_mono_of
    (hq : ∀ (m : Nat) (v1 v2 : SVal L) (d : Nat) (b : Bool),
      isDefEq_s n v1 v2 d = some b → n ≤ m → isDefEq_s m v1 v2 d = some b)
    {sp1 sp2 : List (SVal L)} {d : Nat} {b : Bool}
    (h : isDefEqSpine_s n sp1 sp2 d = some b)
    {m : Nat} (hle : n ≤ m) :
    isDefEqSpine_s m sp1 sp2 d = some b := by
  induction sp1 generalizing sp2 with
  | nil =>
    cases sp2 with
    | nil => rwa [isDefEqSpine_s.eq_1] at h ⊢
    | cons =>
      rw [isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)] at h; cases h
      exact isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)
  | cons v1 rest1 ih =>
    cases sp2 with
    | nil =>
      rw [isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)] at h; cases h
      exact isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)
    | cons v2 rest2 =>
      simp only [isDefEqSpine_s.eq_2, option_bind_eq_some] at h ⊢
      obtain ⟨eqR, heq, hcont⟩ := h
      refine ⟨eqR, hq m v1 v2 d eqR heq hle, ?_⟩
      cases eqR <;> simp_all

omit [LawfulBEq L] in
private theorem isDefEq_fuel_mono_aux (n : Nat) :
    ∀ (m : Nat) (v1 v2 : SVal L) (d : Nat) (b : Bool),
      isDefEq_s n v1 v2 d = some b → n ≤ m → isDefEq_s m v1 v2 d = some b := by
  induction n with
  | zero => intro _ _ _ _ _ h; rw [isDefEq_s.eq_1] at h; exact absurd h nofun
  | succ n0 ih =>
    intro m v1 v2 d b hde hle
    cases m with
    | zero => omega
    | succ m0 =>
      have hle' : n0 ≤ m0 := Nat.le_of_succ_le_succ hle
      cases v1 with
      | sort u =>
        cases v2 with
        | sort => rwa [isDefEq_s.eq_2] at hde ⊢
        | _ =>
          rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
          exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
      | lit l =>
        cases v2 with
        | lit => rwa [isDefEq_s.eq_3] at hde ⊢
        | _ =>
          rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
          exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
      | neutral h1 sp1 =>
        cases v2 with
        | neutral h2 sp2 =>
          simp only [isDefEq_s.eq_4] at hde ⊢
          cases hbeq : h1.beq h2 with
          | true => simp [hbeq] at hde ⊢; exact isDefEqSpine_fuel_mono_of ih hde hle'
          | false => simp [hbeq] at hde ⊢; exact hde
        | _ =>
          rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
          exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
      | lam d1 b1 e1 =>
        cases v2 with
        | lam d2 b2 e2 =>
          rw [isDefEq_s.eq_5] at hde
          simp only [option_bind_eq_some] at hde
          obtain ⟨domEq, h_dom_n, hcont⟩ := hde
          have h_dom_m := ih m0 d1 d2 d domEq h_dom_n hle'
          rw [isDefEq_s.eq_5]
          simp only [option_bind_eq_some]
          refine ⟨domEq, h_dom_m, ?_⟩
          cases domEq with
          | false => exact hcont
          | true =>
            simp [option_bind_eq_some] at hcont ⊢
            obtain ⟨bv1, hev1, bv2, hev2, hbody⟩ := hcont
            exact ⟨bv1, eval_fuel_mono hev1 hle',
                   bv2, eval_fuel_mono hev2 hle',
                   ih m0 bv1 bv2 (d+1) b hbody hle'⟩
        | _ =>
          rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
          exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
      | pi d1 b1 e1 =>
        cases v2 with
        | pi d2 b2 e2 =>
          rw [isDefEq_s.eq_6] at hde
          simp only [option_bind_eq_some] at hde
          obtain ⟨domEq, h_dom_n, hcont⟩ := hde
          have h_dom_m := ih m0 d1 d2 d domEq h_dom_n hle'
          rw [isDefEq_s.eq_6]
          simp only [option_bind_eq_some]
          refine ⟨domEq, h_dom_m, ?_⟩
          cases domEq with
          | false => exact hcont
          | true =>
            simp [option_bind_eq_some] at hcont ⊢
            obtain ⟨bv1, hev1, bv2, hev2, hbody⟩ := hcont
            exact ⟨bv1, eval_fuel_mono hev1 hle',
                   bv2, eval_fuel_mono hev2 hle',
                   ih m0 bv1 bv2 (d+1) b hbody hle'⟩
        | _ =>
          rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
          exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)

omit [LawfulBEq L] in
theorem isDefEq_fuel_mono {n m : Nat} {v1 v2 : SVal L} {d : Nat} {b : Bool}
    (h : isDefEq_s n v1 v2 d = some b) (hle : n ≤ m) :
    isDefEq_s m v1 v2 d = some b :=
  isDefEq_fuel_mono_aux n m v1 v2 d b h hle

omit [LawfulBEq L] in
theorem isDefEqSpine_fuel_mono {n m : Nat} {sp1 sp2 : List (SVal L)} {d : Nat} {b : Bool}
    (h : isDefEqSpine_s n sp1 sp2 d = some b) (hle : n ≤ m) :
    isDefEqSpine_s m sp1 sp2 d = some b :=
  isDefEqSpine_fuel_mono_of (fun _ _ _ _ _ hq hle => isDefEq_fuel_mono hq hle) h hle

/-! ## Symmetry -/

omit [LawfulBEq L] in
private theorem isDefEqSpine_symm_of
    (hq : ∀ (v1 v2 : SVal L) (d : Nat) (b : Bool),
      isDefEq_s fuel v1 v2 d = some b → isDefEq_s fuel v2 v1 d = some b)
    {sp1 sp2 : List (SVal L)} {d : Nat} {b : Bool}
    (h : isDefEqSpine_s fuel sp1 sp2 d = some b) :
    isDefEqSpine_s fuel sp2 sp1 d = some b := by
  induction sp1 generalizing sp2 with
  | nil =>
    cases sp2 with
    | nil => rwa [isDefEqSpine_s.eq_1] at h ⊢
    | cons =>
      rw [isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)] at h; cases h
      exact isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)
  | cons v1 rest1 ih =>
    cases sp2 with
    | nil =>
      rw [isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)] at h; cases h
      exact isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)
    | cons v2 rest2 =>
      simp only [isDefEqSpine_s.eq_2, option_bind_eq_some] at h ⊢
      obtain ⟨eqR, heq, hcont⟩ := h
      refine ⟨eqR, hq v1 v2 d eqR heq, ?_⟩
      cases eqR <;> simp_all

private theorem isDefEq_symm_aux (fuel : Nat) :
    ∀ (v1 v2 : SVal L) (d : Nat) (b : Bool),
      isDefEq_s fuel v1 v2 d = some b → isDefEq_s fuel v2 v1 d = some b := by
  induction fuel with
  | zero => intro _ _ _ _ h; rw [isDefEq_s.eq_1] at h; exact absurd h nofun
  | succ n ih =>
    intro v1 v2 d b hde
    cases v1 with
    | sort u =>
      cases v2 with
      | sort v =>
        simp only [isDefEq_s.eq_2] at hde ⊢
        cases hde; congr 1; exact Bool.beq_comm
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
        exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
    | lit l =>
      cases v2 with
      | lit m =>
        simp only [isDefEq_s.eq_3] at hde ⊢
        cases hde; congr 1; exact Bool.beq_comm
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
        exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
    | neutral h1 sp1 =>
      cases v2 with
      | neutral h2 sp2 =>
        simp only [isDefEq_s.eq_4] at hde ⊢
        rw [SHead.beq_comm h2 h1] at ⊢
        cases hbeq : h1.beq h2 with
        | true => simp [hbeq] at hde ⊢; exact isDefEqSpine_symm_of ih hde
        | false => simp [hbeq] at hde ⊢; exact hde
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
        exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
    | lam d1 b1 e1 =>
      cases v2 with
      | lam d2 b2 e2 =>
        rw [isDefEq_s.eq_5] at hde
        simp only [option_bind_eq_some] at hde
        obtain ⟨domEq, h_dom, hcont⟩ := hde
        rw [isDefEq_s.eq_5]
        simp only [option_bind_eq_some]
        refine ⟨domEq, ih d1 d2 d domEq h_dom, ?_⟩
        cases domEq with
        | false => exact hcont
        | true =>
          simp [option_bind_eq_some] at hcont ⊢
          obtain ⟨bv1, hev1, bv2, hev2, hbody⟩ := hcont
          exact ⟨bv2, hev2, bv1, hev1, ih bv1 bv2 (d+1) b hbody⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
        exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)
    | pi d1 b1 e1 =>
      cases v2 with
      | pi d2 b2 e2 =>
        rw [isDefEq_s.eq_6] at hde
        simp only [option_bind_eq_some] at hde
        obtain ⟨domEq, h_dom, hcont⟩ := hde
        rw [isDefEq_s.eq_6]
        simp only [option_bind_eq_some]
        refine ⟨domEq, ih d1 d2 d domEq h_dom, ?_⟩
        cases domEq with
        | false => exact hcont
        | true =>
          simp [option_bind_eq_some] at hcont ⊢
          obtain ⟨bv1, hev1, bv2, hev2, hbody⟩ := hcont
          exact ⟨bv2, hev2, bv1, hev1, ih bv1 bv2 (d+1) b hbody⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde; cases hde
        exact isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)

theorem isDefEq_symm {fuel : Nat} {v1 v2 : SVal L} {d : Nat} {b : Bool}
    (h : isDefEq_s fuel v1 v2 d = some b) :
    isDefEq_s fuel v2 v1 d = some b :=
  isDefEq_symm_aux fuel v1 v2 d b h

/-! ## Reflexivity (conditional on quotability) -/

omit [LawfulBEq L] in
private theorem isDefEqSpine_refl_of_quotable
    (ih : ∀ (v : SVal L) (e : SExpr L),
      ValWF v d → quote_s fuel v d = some e →
      ∃ fuel', isDefEq_s fuel' v v d = some true)
    {sp : List (SVal L)} {acc : SExpr L}
    (hsp : ListWF sp d) (hqs : quoteSpine_s fuel acc sp d = some e) :
    ∃ fuel', isDefEqSpine_s fuel' sp sp d = some true := by
  induction sp generalizing acc with
  | nil => exact ⟨0, by rw [isDefEqSpine_s.eq_1]⟩
  | cons a rest ih_rest =>
    simp only [quoteSpine_s.eq_2, bind_eq_some] at hqs
    obtain ⟨aE, harg, hrest_qs⟩ := hqs
    cases hsp with | cons ha hsp_rest =>
    obtain ⟨fa, h_deq_a⟩ := ih a aE ha harg
    obtain ⟨fr, h_deq_rest⟩ := ih_rest hsp_rest hrest_qs
    refine ⟨max fa fr, ?_⟩
    simp only [isDefEqSpine_s.eq_2, option_bind_eq_some]
    refine ⟨true, isDefEq_fuel_mono h_deq_a (Nat.le_max_left ..), ?_⟩
    simp
    exact isDefEqSpine_fuel_mono h_deq_rest (Nat.le_max_right ..)

private theorem isDefEq_refl_aux : ∀ (fuel : Nat) (v : SVal L) (d : Nat) (e : SExpr L),
    ValWF v d → quote_s fuel v d = some e →
    ∃ fuel', isDefEq_s fuel' v v d = some true := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ h; rw [quote_s.eq_1] at h; exact absurd h nofun
  | succ n ih =>
    intro v d e hwf hq
    cases v with
    | sort u =>
      rw [quote_s.eq_2] at hq; cases hq
      exact ⟨1, by simp [isDefEq_s.eq_2]⟩
    | lit l =>
      rw [quote_s.eq_3] at hq; cases hq
      exact ⟨1, by simp [isDefEq_s.eq_3]⟩
    | neutral hd sp =>
      rw [quote_s.eq_6] at hq
      cases hwf with | neutral hhd hsp =>
      obtain ⟨fsp, h_deq_sp⟩ := isDefEqSpine_refl_of_quotable (d := d)
        (fun v e hwf hq => ih v d e hwf hq) hsp hq
      exact ⟨fsp + 1, by rw [isDefEq_s.eq_4, SHead.beq_refl]; exact h_deq_sp⟩
    | lam dom body fenv =>
      simp only [quote_s.eq_4, bind_eq_some] at hq
      obtain ⟨domE, hd, bodyV, hb, bodyE, hbe, he⟩ := hq
      cases he
      cases hwf with | lam hwf_dom hclosed hwf_env =>
      obtain ⟨fdom, h_deq_dom⟩ := ih dom d domE hwf_dom hd
      have hwf_bodyV := eval_preserves_wf hb hclosed
        (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_env.mono (by omega)))
      obtain ⟨fbody, h_deq_body⟩ := ih bodyV (d + 1) bodyE hwf_bodyV hbe
      let F := max fdom (max n fbody)
      refine ⟨F + 1, ?_⟩
      rw [isDefEq_s.eq_5, show isDefEq_s F dom dom d = some true from
        isDefEq_fuel_mono h_deq_dom (Nat.le_max_left ..)]
      simp [option_bind_eq_some]
      exact ⟨bodyV, eval_fuel_mono hb (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
             bodyV, eval_fuel_mono hb (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
             isDefEq_fuel_mono h_deq_body (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))⟩
    | pi dom body fenv =>
      simp only [quote_s.eq_5, bind_eq_some] at hq
      obtain ⟨domE, hd, bodyV, hb, bodyE, hbe, he⟩ := hq
      cases he
      cases hwf with | pi hwf_dom hclosed hwf_env =>
      obtain ⟨fdom, h_deq_dom⟩ := ih dom d domE hwf_dom hd
      have hwf_bodyV := eval_preserves_wf hb hclosed
        (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_env.mono (by omega)))
      obtain ⟨fbody, h_deq_body⟩ := ih bodyV (d + 1) bodyE hwf_bodyV hbe
      let F := max fdom (max n fbody)
      refine ⟨F + 1, ?_⟩
      rw [isDefEq_s.eq_6, show isDefEq_s F dom dom d = some true from
        isDefEq_fuel_mono h_deq_dom (Nat.le_max_left ..)]
      simp [option_bind_eq_some]
      exact ⟨bodyV, eval_fuel_mono hb (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
             bodyV, eval_fuel_mono hb (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
             isDefEq_fuel_mono h_deq_body (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..))⟩

theorem isDefEq_refl {v : SVal L} {d fuel : Nat} {e : SExpr L}
    (hwf : ValWF v d) (hq : quote_s fuel v d = some e) :
    ∃ fuel', isDefEq_s fuel' v v d = some true :=
  isDefEq_refl_aux fuel v d e hwf hq

/-! ## Soundness w.r.t. quote

  The main theorem: def-eq values produce the same normal form. -/

omit [LawfulBEq L] in
private theorem isDefEqSpine_sound_of
    (ih : ∀ (v1 v2 : SVal L) (d : Nat),
      isDefEq_s fuel v1 v2 d = some true →
      ValWF v1 d → ValWF v2 d →
      ∃ f1 f2 e, quote_s f1 v1 d = some e ∧ quote_s f2 v2 d = some e)
    {sp1 sp2 : List (SVal L)} {d : Nat} {acc : SExpr L}
    (h : isDefEqSpine_s fuel sp1 sp2 d = some true)
    (hwf1 : ListWF sp1 d) (hwf2 : ListWF sp2 d) :
    ∃ f e, quoteSpine_s f acc sp1 d = some e ∧ quoteSpine_s f acc sp2 d = some e := by
  induction sp1 generalizing sp2 acc with
  | nil =>
    cases sp2 with
    | nil => exact ⟨0, acc, by rw [quoteSpine_s.eq_1], by rw [quoteSpine_s.eq_1]⟩
    | cons =>
      rw [isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)] at h; exact absurd h nofun
  | cons v1 rest1 ih_rest =>
    cases sp2 with
    | nil =>
      rw [isDefEqSpine_cross (by intros; contradiction) (by intros; contradiction)] at h; exact absurd h nofun
    | cons v2 rest2 =>
      simp only [isDefEqSpine_s.eq_2, option_bind_eq_some] at h
      obtain ⟨eqR, heq, hcont⟩ := h
      cases eqR with
      | false => exact absurd hcont nofun
      | true =>
        simp at hcont
        cases hwf1 with | cons ha1 hsp1 =>
        cases hwf2 with | cons ha2 hsp2 =>
        obtain ⟨f1, f2, argE, hq1, hq2⟩ := ih v1 v2 d heq ha1 ha2
        obtain ⟨frest, erest, hqs1, hqs2⟩ := ih_rest hcont hsp1 hsp2
        let F := max (max f1 f2) frest
        exact ⟨F, erest,
               by simp only [quoteSpine_s.eq_2, bind_eq_some]
                  exact ⟨argE, quote_fuel_mono hq1 (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)),
                         quoteSpine_fuel_mono hqs1 (Nat.le_max_right ..)⟩,
               by simp only [quoteSpine_s.eq_2, bind_eq_some]
                  exact ⟨argE, quote_fuel_mono hq2 (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_left ..)),
                         quoteSpine_fuel_mono hqs2 (Nat.le_max_right ..)⟩⟩

private theorem isDefEq_sound_aux : ∀ (fuel : Nat) (v1 v2 : SVal L) (d : Nat),
    isDefEq_s fuel v1 v2 d = some true →
    ValWF v1 d → ValWF v2 d →
    ∃ f1 f2 e, quote_s f1 v1 d = some e ∧ quote_s f2 v2 d = some e := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ h; rw [isDefEq_s.eq_1] at h; exact absurd h nofun
  | succ n ih =>
    intro v1 v2 d hde hwf1 hwf2
    cases v1 with
    | sort u =>
      cases v2 with
      | sort v =>
        simp only [isDefEq_s.eq_2] at hde
        have : u = v := by simpa using hde
        subst this
        exact ⟨1, 1, .sort u, by rw [quote_s.eq_2], by rw [quote_s.eq_2]⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde
        exact absurd hde nofun
    | lit l =>
      cases v2 with
      | lit m =>
        simp only [isDefEq_s.eq_3] at hde
        have : l = m := by simpa using hde
        subst this
        exact ⟨1, 1, .lit l, by rw [quote_s.eq_3], by rw [quote_s.eq_3]⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde
        exact absurd hde nofun
    | neutral h1 sp1 =>
      cases v2 with
      | neutral h2 sp2 =>
        simp only [isDefEq_s.eq_4] at hde
        cases hbeq : h1.beq h2 with
        | false => simp [hbeq] at hde
        | true =>
          simp [hbeq] at hde
          have heq := SHead.beq_eq hbeq; subst heq
          cases hwf1 with | neutral hhd1 hsp1 =>
          cases hwf2 with | neutral hhd2 hsp2 =>
          obtain ⟨f, e, hqs1, hqs2⟩ := isDefEqSpine_sound_of ih hde hsp1 hsp2
          exact ⟨f + 1, f + 1, e,
                 by rw [quote_s.eq_6]; exact hqs1,
                 by rw [quote_s.eq_6]; exact hqs2⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde
        exact absurd hde nofun
    | lam d1 b1 e1 =>
      cases v2 with
      | lam d2 b2 e2 =>
        rw [isDefEq_s.eq_5] at hde
        simp only [option_bind_eq_some] at hde
        obtain ⟨domEq, h_dom, hcont⟩ := hde
        cases domEq with
        | false => exact absurd hcont nofun
        | true =>
          simp [option_bind_eq_some] at hcont
          obtain ⟨bv1, hev1, bv2, hev2, hbody⟩ := hcont
          cases hwf1 with | lam hwf_d1 hcl1 hwf_e1 =>
          cases hwf2 with | lam hwf_d2 hcl2 hwf_e2 =>
          obtain ⟨fd1, fd2, domE, hqd1, hqd2⟩ := ih d1 d2 d h_dom hwf_d1 hwf_d2
          have hwf_bv1 := eval_preserves_wf hev1 hcl1
            (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_e1.mono (by omega)))
          have hwf_bv2 := eval_preserves_wf hev2 hcl2
            (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_e2.mono (by omega)))
          obtain ⟨fb1, fb2, bodyE, hqb1, hqb2⟩ := ih bv1 bv2 (d+1) hbody hwf_bv1 hwf_bv2
          let F1 := max fd1 (max n fb1)
          let F2 := max fd2 (max n fb2)
          exact ⟨F1 + 1, F2 + 1, .lam domE bodyE,
                 by simp only [quote_s.eq_4, bind_eq_some]
                    exact ⟨domE, quote_fuel_mono hqd1 (Nat.le_max_left ..),
                           bv1, eval_fuel_mono hev1 (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
                           bodyE, quote_fuel_mono hqb1 (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)), rfl⟩,
                 by simp only [quote_s.eq_4, bind_eq_some]
                    exact ⟨domE, quote_fuel_mono hqd2 (Nat.le_max_left ..),
                           bv2, eval_fuel_mono hev2 (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
                           bodyE, quote_fuel_mono hqb2 (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)), rfl⟩⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde
        exact absurd hde nofun
    | pi d1 b1 e1 =>
      cases v2 with
      | pi d2 b2 e2 =>
        rw [isDefEq_s.eq_6] at hde
        simp only [option_bind_eq_some] at hde
        obtain ⟨domEq, h_dom, hcont⟩ := hde
        cases domEq with
        | false => exact absurd hcont nofun
        | true =>
          simp [option_bind_eq_some] at hcont
          obtain ⟨bv1, hev1, bv2, hev2, hbody⟩ := hcont
          cases hwf1 with | pi hwf_d1 hcl1 hwf_e1 =>
          cases hwf2 with | pi hwf_d2 hcl2 hwf_e2 =>
          obtain ⟨fd1, fd2, domE, hqd1, hqd2⟩ := ih d1 d2 d h_dom hwf_d1 hwf_d2
          have hwf_bv1 := eval_preserves_wf hev1 hcl1
            (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_e1.mono (by omega)))
          have hwf_bv2 := eval_preserves_wf hev2 hcl2
            (.cons (.neutral (.fvar (by omega : d < d + 1)) .nil) (hwf_e2.mono (by omega)))
          obtain ⟨fb1, fb2, bodyE, hqb1, hqb2⟩ := ih bv1 bv2 (d+1) hbody hwf_bv1 hwf_bv2
          let F1 := max fd1 (max n fb1)
          let F2 := max fd2 (max n fb2)
          exact ⟨F1 + 1, F2 + 1, .forallE domE bodyE,
                 by simp only [quote_s.eq_5, bind_eq_some]
                    exact ⟨domE, quote_fuel_mono hqd1 (Nat.le_max_left ..),
                           bv1, eval_fuel_mono hev1 (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
                           bodyE, quote_fuel_mono hqb1 (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)), rfl⟩,
                 by simp only [quote_s.eq_5, bind_eq_some]
                    exact ⟨domE, quote_fuel_mono hqd2 (Nat.le_max_left ..),
                           bv2, eval_fuel_mono hev2 (by exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)),
                           bodyE, quote_fuel_mono hqb2 (by exact Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)), rfl⟩⟩
      | _ =>
        rw [isDefEq_cross (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)] at hde
        exact absurd hde nofun

/-- **Soundness**: Def-eq values produce the same normal form. -/
theorem isDefEq_sound {fuel : Nat} {v1 v2 : SVal L} {d : Nat}
    (h : isDefEq_s fuel v1 v2 d = some true)
    (hwf1 : ValWF v1 d) (hwf2 : ValWF v2 d) :
    ∃ f1 f2 e, quote_s f1 v1 d = some e ∧ quote_s f2 v2 d = some e :=
  isDefEq_sound_aux fuel v1 v2 d h hwf1 hwf2

end Ix.Theory
