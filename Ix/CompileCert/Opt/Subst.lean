import Ix.CompileCert.Opt.Basic

/-!
# M7 L3-def: simultaneous substitution on erased terms

`msubst σ k t` replaces every loose variable `bvar (k + j)` of `t` (under `k` binders) by `σ j`
lifted over the `k` binders. X1's `Tm.inst` is an instance (`inst_eq_msubst`), and so is the
β-reduct of a telescope (`betaN_eq_msubst`). The point of the module is **composition**
(`msubst_msubst`): two substitutions in a row are one, which gives

* `betaN_betaN`: substituting `Q` into a term over a telescope of `|Q|` variables, then `A` into
  the result, is substituting `Q` with `A` substituted (for a term with no loose variable past
  the telescope): the shape of every "slot term of one telescope is a slot term of another,
  renamed" law (Pass 2's constructions against Lean's, design D-4).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr)
open Ix.CompileCert.Conv

/-- Simultaneous substitution of the loose variables at depth `k`. -/
def msubst (σ : Nat → Tm) : Nat → Tm → Tm
  | k, .bvar i => if i < k then .bvar i else Tm.lift k 0 (σ (i - k))
  | k, .app f a => .app (msubst σ k f) (msubst σ k a)
  | k, .lam t b => .lam (msubst σ k t) (msubst σ (k + 1) b)
  | k, .pi t b => .pi (msubst σ k t) (msubst σ (k + 1) b)
  | k, .letE t v b => .letE (msubst σ k t) (msubst σ k v) (msubst σ (k + 1) b)
  | k, .proj s i e => .proj s i (msubst σ k e)
  | _, .fvar x => .fvar x
  | _, .mvar x => .mvar x
  | _, .sort u => .sort u
  | _, .const c us => .const c us
  | _, .lit l => .lit l

theorem msubst_appN (σ : Nat → Tm) (k : Nat) (f : Tm) (xs : List Tm) :
    msubst σ k (Tm.appN f xs) = Tm.appN (msubst σ k f) (xs.map (msubst σ k)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [Tm.appN_cons, ih, msubst, List.map_cons]

/-- A substitution after a lift sees the variables shifted. -/
theorem msubst_lift (σ : Nat → Tm) (n : Nat) : ∀ (c : Nat) (t : Tm),
    msubst σ c (Tm.lift n c t) = msubst (fun j => σ (j + n)) c t
  | c, .bvar i => by
    simp only [Tm.lift, msubst]
    by_cases hi : c ≤ i
    · have h1 : ¬ i + n < c := by omega
      have h2 : ¬ i < c := by omega
      simp only [hi, ↓reduceIte, h1, h2]
      rw [show i + n - c = i - c + n by omega]
    · have h1 : i < c := by omega
      simp only [hi, ↓reduceIte, h1]
  | c, .app f a => by simp only [Tm.lift, msubst, msubst_lift σ n c f, msubst_lift σ n c a]
  | c, .lam t b => by simp only [Tm.lift, msubst, msubst_lift σ n c t, msubst_lift σ n (c + 1) b]
  | c, .pi t b => by simp only [Tm.lift, msubst, msubst_lift σ n c t, msubst_lift σ n (c + 1) b]
  | c, .letE t v b => by
    simp only [Tm.lift, msubst, msubst_lift σ n c t, msubst_lift σ n c v, msubst_lift σ n (c + 1) b]
  | c, .proj s i e => by simp only [Tm.lift, msubst, msubst_lift σ n c e]
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

/-- A substitution under a lift of its own depth: the lift passes outside. -/
theorem msubst_lift_out (σ : Nat → Tm) (k : Nat) : ∀ (c : Nat) (t : Tm),
    msubst σ (c + k) (Tm.lift k c t) = Tm.lift k c (msubst σ c t)
  | c, .bvar i => by
    simp only [Tm.lift, msubst]
    by_cases hi : c ≤ i
    · have h1 : ¬ i + k < c + k := by omega
      have h2 : ¬ i < c := by omega
      simp only [hi, ↓reduceIte, h1, h2]
      rw [show i + k - (c + k) = i - c by omega,
        Tm.lift_lift_of_le k c 0 c _ (Nat.zero_le _) (by omega), Nat.add_comm k c]
    · have h1 : i < c + k := by omega
      have h2 : i < c := by omega
      simp only [hi, ↓reduceIte, h1, h2, Tm.lift]
  | c, .app f a => by simp only [Tm.lift, msubst, msubst_lift_out σ k c f, msubst_lift_out σ k c a]
  | c, .lam t b => by
    simp only [Tm.lift, msubst, msubst_lift_out σ k c t]
    rw [show c + k + 1 = (c + 1) + k by omega, msubst_lift_out σ k (c + 1) b]
  | c, .pi t b => by
    simp only [Tm.lift, msubst, msubst_lift_out σ k c t]
    rw [show c + k + 1 = (c + 1) + k by omega, msubst_lift_out σ k (c + 1) b]
  | c, .letE t v b => by
    simp only [Tm.lift, msubst, msubst_lift_out σ k c t, msubst_lift_out σ k c v]
    rw [show c + k + 1 = (c + 1) + k by omega, msubst_lift_out σ k (c + 1) b]
  | c, .proj s i e => by simp only [Tm.lift, msubst, msubst_lift_out σ k c e]
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

/-- **Composition**: two simultaneous substitutions at one depth are one. -/
theorem msubst_msubst (σ τ : Nat → Tm) : ∀ (k : Nat) (t : Tm),
    msubst σ k (msubst τ k t) = msubst (fun j => msubst σ 0 (τ j)) k t
  | k, .bvar i => by
    by_cases hi : i < k
    · simp only [msubst, hi, ↓reduceIte]
    · simp only [msubst, hi, ↓reduceIte]
      have := msubst_lift_out σ k 0 (τ (i - k))
      rw [Nat.zero_add] at this
      exact this
  | k, .app f a => by simp only [msubst, msubst_msubst σ τ k f, msubst_msubst σ τ k a]
  | k, .lam t b => by simp only [msubst, msubst_msubst σ τ k t, msubst_msubst σ τ (k + 1) b]
  | k, .pi t b => by simp only [msubst, msubst_msubst σ τ k t, msubst_msubst σ τ (k + 1) b]
  | k, .letE t v b => by
    simp only [msubst, msubst_msubst σ τ k t, msubst_msubst σ τ k v, msubst_msubst σ τ (k + 1) b]
  | k, .proj s i e => by simp only [msubst, msubst_msubst σ τ k e]
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

/-- The identity substitution. -/
theorem msubst_id : ∀ (c : Nat) (t : Tm), msubst (fun j => .bvar j) c t = t
  | c, .bvar i => by
    by_cases hi : i < c
    · simp only [msubst, hi, ↓reduceIte]
    · simp only [msubst, hi, ↓reduceIte, Tm.lift]
      have : 0 ≤ i - c := Nat.zero_le _
      simp only [this, ↓reduceIte]
      congr 1; omega
  | c, .app f a => by simp only [msubst, msubst_id c f, msubst_id c a]
  | c, .lam t b => by simp only [msubst, msubst_id c t, msubst_id (c + 1) b]
  | c, .pi t b => by simp only [msubst, msubst_id c t, msubst_id (c + 1) b]
  | c, .letE t v b => by simp only [msubst, msubst_id c t, msubst_id c v, msubst_id (c + 1) b]
  | c, .proj s i e => by simp only [msubst, msubst_id c e]
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

/-- Substitutions that agree on the loose variables of a term agree on it. -/
theorem msubst_congr {σ σ' : Nat → Tm} : ∀ (c : Nat) (t : Tm),
    (∀ j, c + j < t.range → σ j = σ' j) → msubst σ c t = msubst σ' c t
  | c, .bvar i, h => by
    by_cases hi : i < c
    · simp only [msubst, hi, ↓reduceIte]
    · simp only [msubst, hi, ↓reduceIte]
      rw [h (i - c) (by simp only [Tm.range]; omega)]
  | c, .app f a, h => by
    simp only [msubst]
    rw [msubst_congr c f (fun j hj => h j (by simp only [Tm.range]; omega)),
      msubst_congr c a (fun j hj => h j (by simp only [Tm.range]; omega))]
  | c, .lam t b, h => by
    simp only [msubst]
    rw [msubst_congr c t (fun j hj => h j (by simp only [Tm.range]; omega)),
      msubst_congr (c + 1) b (fun j hj => h j (by simp only [Tm.range]; omega))]
  | c, .pi t b, h => by
    simp only [msubst]
    rw [msubst_congr c t (fun j hj => h j (by simp only [Tm.range]; omega)),
      msubst_congr (c + 1) b (fun j hj => h j (by simp only [Tm.range]; omega))]
  | c, .letE t v b, h => by
    simp only [msubst]
    rw [msubst_congr c t (fun j hj => h j (by simp only [Tm.range]; omega)),
      msubst_congr c v (fun j hj => h j (by simp only [Tm.range]; omega)),
      msubst_congr (c + 1) b (fun j hj => h j (by simp only [Tm.range]; omega))]
  | c, .proj s i e, h => by
    simp only [msubst]
    rw [msubst_congr c e (fun j hj => h j (by simp only [Tm.range]; omega))]
  | _, .fvar _, _ | _, .mvar _, _ | _, .sort _, _ | _, .const _ _, _ | _, .lit _, _ => rfl

/-! ## X1's substitution and the β-reduct of a telescope -/

/-- The substitution `Tm.inst v k` performs, below `c` binders, as a simultaneous one. -/
def instσ (v : Tm) (k : Nat) (j : Nat) : Tm :=
  if j < k then .bvar j else if j = k then Tm.lift k 0 v else .bvar (j - 1)

theorem inst_eq_msubst (v : Tm) (k : Nat) : ∀ (c : Nat) (t : Tm),
    Tm.inst v (c + k) t = msubst (instσ v k) c t
  | c, .bvar i => by
    by_cases h1 : i < c
    · have h2 : i ≠ c + k := by omega
      have h3 : ¬ c + k < i := by omega
      simp only [Tm.inst, msubst, h1, h2, h3, ↓reduceIte]
    · have h1' : ¬ i < c := h1
      simp only [msubst, h1', ↓reduceIte, instσ]
      by_cases h2 : i - c < k
      · have h3 : i ≠ c + k := by omega
        have h4 : ¬ c + k < i := by omega
        simp only [Tm.inst, h2, h3, h4, ↓reduceIte, Tm.lift]
        have : 0 ≤ i - c := Nat.zero_le _
        simp only [this, ↓reduceIte]
        congr 1; omega
      · by_cases h3 : i - c = k
        · have h4 : i = c + k := by omega
          subst h4
          simp only [Tm.inst, h3, Nat.lt_irrefl, ↓reduceIte]
          rw [Tm.lift_lift_of_le c k 0 0 v (Nat.le_refl _) (by omega)]
        · have h4 : i ≠ c + k := by omega
          have h5 : c + k < i := by omega
          simp only [Tm.inst, h2, h3, h4, h5, ↓reduceIte, Tm.lift]
          have : 0 ≤ i - c - 1 := Nat.zero_le _
          simp only [this, ↓reduceIte]
          congr 1; omega
  | c, .app f a => by simp only [Tm.inst, msubst, inst_eq_msubst v k c f, inst_eq_msubst v k c a]
  | c, .lam t b => by
    simp only [Tm.inst, msubst, inst_eq_msubst v k c t]
    rw [show c + k + 1 = (c + 1) + k by omega, inst_eq_msubst v k (c + 1) b]
  | c, .pi t b => by
    simp only [Tm.inst, msubst, inst_eq_msubst v k c t]
    rw [show c + k + 1 = (c + 1) + k by omega, inst_eq_msubst v k (c + 1) b]
  | c, .letE t w b => by
    simp only [Tm.inst, msubst, inst_eq_msubst v k c t, inst_eq_msubst v k c w]
    rw [show c + k + 1 = (c + 1) + k by omega, inst_eq_msubst v k (c + 1) b]
  | c, .proj s i e => by simp only [Tm.inst, msubst, inst_eq_msubst v k c e]
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

/-- The substitution the β-reduct of a telescope performs: telescope position `|as| - 1 - j` is
`as`'s, the variables past the telescope move down. -/
def betaσ (as : List Tm) (j : Nat) : Tm :=
  if j < as.length then as.getD (as.length - 1 - j) (.bvar 0) else .bvar (j - as.length)

theorem betaσ_nil : betaσ [] = fun j => .bvar j := by
  funext j; simp [betaσ]

theorem betaσ_cons (a : Tm) (as : List Tm) :
    (fun j => msubst (betaσ as) 0 (instσ a as.length j)) = betaσ (a :: as) := by
  funext j
  simp only [instσ]
  by_cases h1 : j < as.length
  · simp only [h1, ↓reduceIte, msubst, Nat.not_lt_zero, Nat.sub_zero, Tm.lift_zero, betaσ,
      List.length_cons]
    have h2 : j < as.length + 1 := by omega
    simp only [h2, ↓reduceIte]
    rw [show as.length + 1 - 1 - j = (as.length - 1 - j) + 1 by omega]
    simp only [List.getD_cons_succ]
  · by_cases h2 : j = as.length
    · subst h2
      simp only [Nat.lt_irrefl, ↓reduceIte]
      rw [msubst_lift (betaσ as) as.length 0 a]
      have e : (fun j => betaσ as (j + as.length)) = fun j => .bvar j := by
        funext j
        have hj : ¬ j + as.length < as.length := by omega
        simp only [betaσ, hj, ↓reduceIte, Nat.add_sub_cancel]
      rw [e, msubst_id]
      simp [betaσ]
    · have h3 : ¬ j - 1 < as.length := by omega
      simp only [h1, h2, ↓reduceIte, msubst, Nat.not_lt_zero, Nat.sub_zero, Tm.lift_zero, betaσ,
        List.length_cons, h3]
      have h4 : ¬ j < as.length + 1 := by omega
      simp only [h4, ↓reduceIte]
      congr 1; omega

/-- **The β-reduct of a telescope is a simultaneous substitution.** -/
theorem betaN_eq_msubst : ∀ (as : List Tm) (t : Tm), betaN as t = msubst (betaσ as) 0 t
  | [], t => by rw [betaσ_nil, msubst_id]; rfl
  | a :: as, t => by
    show betaN as (Tm.inst a as.length t) = _
    rw [betaN_eq_msubst as, show as.length = 0 + as.length by omega, inst_eq_msubst a as.length 0 t,
      msubst_msubst, betaσ_cons]

/-- **Two β-reducts in a row**: a term over a telescope of `|Q|` variables (no loose variable past
it), with `Q` substituted and then `A`, is the term with `Q`'s substitution by `A` substituted. -/
theorem betaN_betaN (A Q : List Tm) (t : Tm) (ht : t.range ≤ Q.length) :
    betaN A (betaN Q t) = betaN (Q.map (betaN A)) t := by
  rw [betaN_eq_msubst Q, betaN_eq_msubst A, msubst_msubst, betaN_eq_msubst (Q.map (betaN A))]
  apply msubst_congr 0 t
  intro j hj
  have hjQ : j < Q.length := by omega
  have e1 : betaσ Q j = Q.getD (Q.length - 1 - j) (.bvar 0) := by simp only [betaσ, hjQ, ↓reduceIte]
  have e2 : betaσ (Q.map (betaN A)) j = (Q.map (betaN A)).getD (Q.length - 1 - j) (.bvar 0) := by
    simp only [betaσ, List.length_map, hjQ, ↓reduceIte]
  rw [e1, e2, ← betaN_eq_msubst A, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : Q.length - 1 - j < Q.length), Option.map_some,
    Option.getD_some, Option.getD_some]

end Ix.CompileCert.Opt


namespace Ix.CompileCert.Opt

open Ix (Name Level Expr)
open Ix.CompileCert.Conv

/-! ## Conversions through the β-reduct of a telescope; lists of conversions -/

/-- A conversion survives substituting the same arguments for a telescope. -/
theorem conv_betaN {Γ : Env} (hΓ : Γ.InstClosed) :
    ∀ (A : List Tm) {a b : Tm}, Conv Γ a b → Conv Γ (betaN A a) (betaN A b)
  | [], _, _, h => h
  | x :: A, _, _, h => conv_betaN hΓ A (h.inst hΓ x A.length)

theorem forall2_append {R : Tm → Tm → Prop} : ∀ {a b c d : List Tm},
    Forall2 R a b → Forall2 R c d → Forall2 R (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall2_append h2 h)

theorem forall2_map {R : Tm → Tm → Prop} {α : Type} (f g : α → Tm) :
    ∀ (l : List α), (∀ x ∈ l, R (f x) (g x)) → Forall2 R (l.map f) (l.map g)
  | [], _ => .nil
  | x :: l, h => .cons (h x (List.mem_cons_self ..))
      (forall2_map f g l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem forall2_of_eq {Γ : Env} {a b : List Tm} (h : a = b) : Forall2 (Conv Γ) a b :=
  h ▸ Conv.forall₂_refl a

theorem forall2_symm {Γ : Env} : ∀ {a b : List Tm}, Forall2 (Conv Γ) a b → Forall2 (Conv Γ) b a
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (.symm h1) (forall2_symm h2)

theorem forall2_mapRight {Γ : Env} (F : Tm → Tm) (hF : ∀ {a b}, Conv Γ a b → Conv Γ (F a) (F b)) :
    ∀ {a b : List Tm}, Forall2 (Conv Γ) a b → Forall2 (Conv Γ) (a.map F) (b.map F)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (hF h1) (forall2_mapRight F hF h2)

/-- **δ then β on a telescope, any body**: if the head `h.{us}` δ-reduces to a telescope of
`n ≤ |L|` binders over `c.{ls} K`, then `h.{us} L` converts to `c.{ls}` applied to `K` with the
first `n` arguments substituted, then the rest of `L`. -/
theorem delta_beta {Γ : Env} {h c : Name} {us ls : Array Level} {L : List Tm} {n : Nat}
    {ts K : List Tm} (hn : n ≤ L.length) (hts : ts.length = n)
    (hδ : Γ.ax (.const h us) (lamN ts (Tm.appN (.const c ls) K))) :
    Conv Γ (Tm.appN (.const h us) L) (Tm.appN (.const c ls) (K.map (betaN (L.take n)) ++ L.drop n)) := by
  have hAlen : (L.take n).length = n := by rw [List.length_take]; omega
  have e : Tm.appN (.const h us) L = Tm.appN (.const h us) (L.take n ++ L.drop n) := by
    rw [List.take_append_drop]
  rw [e]
  refine .trans (Conv.appN (.step (.ax hδ)) (Conv.forall₂_refl _)) ?_
  refine .trans (beta_lamN (L.take n) ts _ _ (by rw [hts, hAlen])) ?_
  rw [betaN_appN, betaN_const, ← Tm.appN_append]
  exact .refl _

/-- A telescope position of an argument list, substituted. -/
theorem betaN_tv {A : List Tm} {p : Nat} (hp : p < A.length) :
    betaN A (.bvar (A.length - 1 - p)) = A.getD p (.bvar 0) := by
  apply betaN_bvar
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]

section four
variable {α : Type} {A B C D : List α} {p : Nat} {d : α}

theorem gD4_1 (h : p < A.length) : (A ++ B ++ C ++ D).getD p d = A.getD p d := by
  have h1 : p < (A ++ B ++ C).length := by simp; omega
  have h2 : p < (A ++ B).length := by simp; omega
  rw [getD_append_lt h1, getD_append_lt h2, getD_append_lt h]

theorem gD4_2 (h : p < B.length) : (A ++ B ++ C ++ D).getD (A.length + p) d = B.getD p d := by
  have h1 : A.length + p < (A ++ B ++ C).length := by simp; omega
  have h2 : A.length + p < (A ++ B).length := by simp; omega
  have h3 : A.length ≤ A.length + p := Nat.le_add_right _ _
  rw [getD_append_lt h1, getD_append_lt h2, getD_append_ge h3, Nat.add_sub_cancel_left]

theorem gD4_3 (h : p < C.length) :
    (A ++ B ++ C ++ D).getD (A.length + B.length + p) d = C.getD p d := by
  have h1 : A.length + B.length + p < (A ++ B ++ C).length := by simp; omega
  have h2 : (A ++ B).length ≤ A.length + B.length + p := by simp
  rw [getD_append_lt h1, getD_append_ge h2]
  simp only [List.length_append]
  rw [Nat.add_sub_cancel_left]

theorem gD4_4 : (A ++ B ++ C ++ D).getD (A.length + B.length + C.length + p) d = D.getD p d := by
  have h1 : (A ++ B ++ C).length ≤ A.length + B.length + C.length + p := by simp; omega
  rw [getD_append_ge h1]
  simp only [List.length_append]
  rw [Nat.add_sub_cancel_left]

end four

theorem getD_map_tm {β : Type} {l : List β} {f : β → Tm} {p : Nat} {d : β} {d' : Tm} (h : p < l.length) :
    (l.map f).getD p d' = f (l.getD p d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some, Option.getD_some]

end Ix.CompileCert.Opt
