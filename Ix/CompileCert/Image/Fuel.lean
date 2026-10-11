import Ix.CompileCert.Conv
import Batteries.Tactic.OpenPrivate

/-!
# M7 L2a-syn: the development's fuel, explicitly (decision D-X1-1)

X1 proved that the development (the table-free core `hinstP`/`happP` of
`Ix/Compile/Image/Develop.lean`) terminates on simply typable input from *some* fuel on
(`develop_total`). This module bounds the fuel by the **height** of the input (`hgt`, the
recursion depth of a walk; `mdata` counts, as the development spends fuel on it) for the shapes
the compiler substitutes, so that the constant `defaultFuel = 2 ^ 16` is a theorem on a checkable
domain instead of a measured margin.

Two shapes make the development a plain walk (no hereditary step at all):

* `hinstP_inert`: the substituted value is **inert** (`TmInert`: its spine head is neither a λ
  nor a pair constructor), so no β- or pair-projection redex can form at a substituted
  position; the fuel needed is the height of the term substituted into, and the result is at
  most as high as that term plus the value;
* `hinstP_passive`: the substituted variable is **passive** in the term (`Passive`: it never
  surfaces at the head of an application spine, `Act`), so whatever the value, no redex forms;
  the fuel needed is again the height.

On top of them, one hereditary level:

* `happP_inert`: a call site whose arguments are inert (P3a's rule right-hand sides at the
  telescope's free variables) needs the height of the function plus one;
* `happP_passive`: a call site of a value whose parameters are passive in its body (`FOv`, the
  first-order λs of the census: P3a's motive wrappers) needs the number of arguments plus the
  heights of value and arguments, and computes the plain substitution;
* `hinstP_heads`: a first-order value substituted into a term where its variable occurs only at
  the head of spines whose arguments do not mention it (`HeadsOnly`: the canonical minor types
  of P3a) needs the term's height plus the call's.

What is *not* claimed: a bound `depth ≤ c · height` for every call site of the call-site rewrite
(P3b) with a constant `c`. P3b admits a family of simply typable call sites, with first-order
values at the second level, whose development depth grows as the square of the input's height.
`Tests/Ix/Compile/L2aSyn.lean` includes this family in its fuel census.
-/

open private Ix.Compile.Image.abstractFVars.go from Ix.Compile.Image.Expr

namespace Ix.CompileCert.Img

open Ix (Name Level Expr)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created projCtor?)

/-! ## Heights -/

/-- The height of an expression (leaves `1`). `mdata` counts: the development spends one unit of
fuel on it. -/
def hgt : Expr → Nat
  | .app f a _ => max (hgt f) (hgt a) + 1
  | .lam _ t b _ _ => max (hgt t) (hgt b) + 1
  | .forallE _ t b _ _ => max (hgt t) (hgt b) + 1
  | .letE _ t v b _ _ => max (max (hgt t) (hgt v)) (hgt b) + 1
  | .proj _ _ x _ => hgt x + 1
  | .mdata _ x _ => hgt x + 1
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 1

theorem hgt_pos : ∀ (e : Expr), 0 < hgt e := by
  intro e; cases e <;> simp [hgt]

@[simp] theorem hgt_mkApp (f a : Expr) : hgt (Expr.mkApp f a) = max (hgt f) (hgt a) + 1 := rfl
@[simp] theorem hgt_mkLam (n : Name) (t b : Expr) (bi : Lean.BinderInfo) :
    hgt (Expr.mkLam n t b bi) = max (hgt t) (hgt b) + 1 := rfl
@[simp] theorem hgt_mkForallE (n : Name) (t b : Expr) (bi : Lean.BinderInfo) :
    hgt (Expr.mkForallE n t b bi) = max (hgt t) (hgt b) + 1 := rfl
@[simp] theorem hgt_mkLetE (n : Name) (t v b : Expr) (nd : Bool) :
    hgt (Expr.mkLetE n t v b nd) = max (max (hgt t) (hgt v)) (hgt b) + 1 := rfl
@[simp] theorem hgt_mkProj (n : Name) (i : Nat) (x : Expr) : hgt (Expr.mkProj n i x) = hgt x + 1 :=
  rfl
@[simp] theorem hgt_mkMData (d : Array (Name × Ix.DataValue)) (x : Expr) :
    hgt (Expr.mkMData d x) = hgt x + 1 := rfl
@[simp] theorem hgt_mkBVar (i : Nat) : hgt (Expr.mkBVar i) = 1 := rfl

/-- The head and the arguments of an application spine are lower than the spine. -/
theorem hgt_getAppFnArgs : ∀ (f a : Expr) (h : Address),
    hgt (getAppFnArgs (.app f a h)).1 < hgt (Expr.app f a h) ∧
      ∀ x ∈ (getAppFnArgs (.app f a h)).2.toList, hgt x < hgt (Expr.app f a h)
  | f, a, h => by
    simp only [getAppFnArgs]
    match f with
    | .app f' a' h' =>
      obtain ⟨h1, h2⟩ := hgt_getAppFnArgs f' a' h'
      simp only [hgt] at h1 h2 ⊢
      refine ⟨by omega, fun x hx => ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := h2 x hx; omega
      · omega
    | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lam .. | .forallE .. | .letE ..
    | .lit .. | .mdata .. | .proj .. =>
      simp only [getAppFnArgs, Array.toList_push, List.mem_append, List.mem_singleton, hgt]
      refine ⟨by omega, fun x hx => ?_⟩
      rcases hx with hx | rfl
      · simp at hx
      · omega


theorem hgt_foldl_mkApp (f : Expr) (as : List Expr) :
    hgt (as.foldl Expr.mkApp f) = as.foldl (fun acc a => max acc (hgt a) + 1) (hgt f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons, ih, hgt_mkApp]

theorem hgt_mkAppN (f : Expr) (as : Array Expr) :
    hgt (mkAppN f as) = as.toList.foldl (fun acc a => max acc (hgt a) + 1) (hgt f) := by
  simp only [mkAppN, ← Array.foldl_toList, hgt_foldl_mkApp]

/-- The spine's height is monotone in the head's and the arguments' heights, with a uniform
excess `d`. -/
theorem foldl_hgt_le (d : Nat) : ∀ (as as' : List Expr) (x x' : Nat), x' ≤ x + d →
    EForall2 (fun a' a => hgt a' ≤ hgt a + d) as' as →
    as'.foldl (fun acc a => max acc (hgt a) + 1) x' ≤ as.foldl (fun acc a => max acc (hgt a) + 1) x + d
  | [], [], x, x', hx, .nil => by simpa using hx
  | a :: as, a' :: as', x, x', hx, .cons ha hs => by
    simp only [List.foldl_cons]
    exact foldl_hgt_le d as as' _ _ (by omega) hs

/-- Rebuilding a spine keeps its height. -/
theorem hgt_getAppFnArgs_eq : ∀ (e : Expr),
    hgt (mkAppN (getAppFnArgs e).1 (getAppFnArgs e).2) = hgt e
  | .app f a h => by
    have ih := hgt_getAppFnArgs_eq f
    simp only [getAppFnArgs, hgt_mkAppN, Array.toList_push, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at ih ⊢
    rw [ih]; rfl
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lam .. | .forallE .. | .letE ..
  | .lit .. | .mdata .. | .proj .. => by simp [getAppFnArgs, hgt_mkAppN]

/-! ## Heights under the core's de Bruijn helpers -/

theorem hgt_liftP : ∀ (e : Expr) (n c : Nat), hgt (liftP e n c) = hgt e
  | e, n, c => by
    unfold liftP
    by_cases hn : n = 0
    · simp [hn]
    simp only [beq_iff_eq, hn, ↓reduceIte]
    by_cases hr : looseRangeP e ≤ c
    · simp only [hr, ↓reduceIte]
    simp only [hr, ↓reduceIte]
    match e with
    | .bvar i _ => by_cases hi : i ≥ c <;> simp [hi, hgt]
    | .app f a _ => simp only [hgt_mkApp, hgt, hgt_liftP f n c, hgt_liftP a n c]
    | .lam _ t b _ _ => simp only [hgt_mkLam, hgt, hgt_liftP t n c, hgt_liftP b n (c + 1)]
    | .forallE _ t b _ _ => simp only [hgt_mkForallE, hgt, hgt_liftP t n c, hgt_liftP b n (c + 1)]
    | .letE _ t v b _ _ =>
      simp only [hgt_mkLetE, hgt, hgt_liftP t n c, hgt_liftP v n c, hgt_liftP b n (c + 1)]
    | .proj _ _ s _ => simp only [hgt_mkProj, hgt, hgt_liftP s n c]
    | .mdata _ x _ => simp only [hgt_mkMData, hgt, hgt_liftP x n c]
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => rfl

theorem hgt_lowerP : ∀ (e : Expr) (n c : Nat), hgt (lowerP e n c) = hgt e
  | e, n, c => by
    unfold lowerP
    by_cases hn : n = 0
    · simp [hn]
    simp only [beq_iff_eq, hn, ↓reduceIte]
    by_cases hr : looseRangeP e ≤ c
    · simp only [hr, ↓reduceIte]
    simp only [hr, ↓reduceIte]
    match e with
    | .bvar i _ => by_cases hi : i ≥ c + n <;> simp [hi, hgt]
    | .app f a _ => simp only [hgt_mkApp, hgt, hgt_lowerP f n c, hgt_lowerP a n c]
    | .lam _ t b _ _ => simp only [hgt_mkLam, hgt, hgt_lowerP t n c, hgt_lowerP b n (c + 1)]
    | .forallE _ t b _ _ =>
      simp only [hgt_mkForallE, hgt, hgt_lowerP t n c, hgt_lowerP b n (c + 1)]
    | .letE _ t v b _ _ =>
      simp only [hgt_mkLetE, hgt, hgt_lowerP t n c, hgt_lowerP v n c, hgt_lowerP b n (c + 1)]
    | .proj _ _ s _ => simp only [hgt_mkProj, hgt, hgt_lowerP s n c]
    | .mdata _ x _ => simp only [hgt_mkMData, hgt, hgt_lowerP x n c]
    | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => rfl

/-! ## `List.mapM` in `Except`, constructively -/

/-- Every element succeeds: so does the map, with pointwise related results. -/
theorem mapM_of_forall {f : Expr → Except String Expr} {P : Expr → Expr → Prop} :
    ∀ (l : List Expr), (∀ a ∈ l, ∃ r, f a = .ok r ∧ P a r) →
      ∃ rs, l.mapM f = .ok rs ∧ EForall2 (fun r a => P a r) rs l
  | [], _ => ⟨[], rfl, .nil⟩
  | a :: l, h => by
    obtain ⟨r, hr, hp⟩ := h a List.mem_cons_self
    obtain ⟨rs, hrs, hps⟩ := mapM_of_forall l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨r :: rs, ?_, .cons hp hps⟩
    simp only [List.mapM_cons, hr, hrs]; rfl

theorem forall₂_length {R : Expr → Expr → Prop} : ∀ {l l' : List Expr}, EForall2 R l l' →
    l.length = l'.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall₂_length h]

theorem EForall2.imp {R S : Expr → Expr → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l l' : List Expr}, EForall2 R l l' → EForall2 S l l'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab hs => .cons (h _ _ hab) (EForall2.imp h hs)

theorem EForall2.map_eq {β : Type} {R : Expr → Expr → Prop} {F : Expr → β} {G : Expr → β}
    (h : ∀ a b, R a b → F a = G b) : ∀ {l l' : List Expr}, EForall2 R l l' → l.map F = l'.map G
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab hs => by simp only [List.map_cons, h _ _ hab, EForall2.map_eq h hs]

/-! ## Inert values -/

/-- The head of an application spine of erased terms. -/
def thd : Tm → Tm
  | .app f _ => thd f
  | t => t

/-- **An inert value**: its spine head is neither a λ nor a pair constructor, so substituting it
at a head position forms no β-redex and no projection-of-constructor redex. -/
def TmInert (t : Tm) : Prop :=
  match thd t with
  | .lam .. => False
  | .const c _ => ctorKind c = none
  | _ => True

theorem thd_appN (h : Tm) : ∀ (as : List Tm), thd (Tm.appN h as) = thd h := by
  intro as
  induction as generalizing h with
  | nil => rfl
  | cons a as ih => rw [Tm.appN_cons, ih]; rfl

theorem thd_lift (n : Nat) : ∀ (c : Nat) (t : Tm), thd (Tm.lift n c t) = Tm.lift n c (thd t)
  | c, .app f _ => by simp only [Tm.lift, thd]; exact thd_lift n c f
  | _, .bvar _ | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lam _ _ | _, .pi _ _
  | _, .letE _ _ _ | _, .lit _ | _, .proj _ _ _ => rfl

theorem TmInert.lift {t : Tm} (h : TmInert t) (n c : Nat) : TmInert (Tm.lift n c t) := by
  unfold TmInert at h ⊢
  rw [thd_lift]
  cases hh : thd t <;> rw [hh] at h <;> simp_all [Tm.lift]

theorem TmInert.appN {t : Tm} (h : TmInert t) (as : List Tm) : TmInert (Tm.appN t as) := by
  unfold TmInert at h ⊢; rw [thd_appN]; exact h

theorem TmInert.not_lam {t : Tm} (h : TmInert t) (a b : Tm) : t ≠ .lam a b := by
  rintro rfl; simp [TmInert, thd] at h

theorem TmInert.not_pair4 {t : Tm} (h : TmInert t) {s c : Name} {us : Array Level} {α β a b : Tm}
    (hp : pairName s c = true) : t ≠ pair4 c us α β a b := by
  intro he
  have := congrArg thd he
  rw [thd_appN] at this
  unfold TmInert at h
  rw [this] at h
  obtain ⟨k, hk⟩ := pairName_ctorKind hp
  simp only [thd] at h
  rw [h] at hk; cases hk

/-- Expression-level: an expression whose erasure is inert is not a λ. -/
theorem not_lam_of_inert {e : Expr} (h : TmInert (er e)) : ∀ n t b bi hh, e ≠ .lam n t b bi hh := by
  rintro n t b bi hh rfl
  exact h.not_lam _ _ rfl

/-- **Substituting an inert value is a walk**: from fuel `hgt e` on the development succeeds, its
result is at most `hgt v - 1` higher than `e`, its flag is never `.reduced`, and a `.direct` result
is the value applied to arguments. -/
theorem hinstP_inert {v : Expr} (hv : TmInert (er v)) : ∀ (m k : Nat) (e : Expr), hgt e ≤ m →
    ∃ r c, hinstP m v k e = .ok (r, c) ∧ hgt r + 1 ≤ hgt e + hgt v ∧ c ≠ .reduced ∧
      (c = .direct → ∃ as, er r = Tm.appN (Tm.lift k 0 (er v)) as)
  | 0, _, e, h => absurd h (by have := hgt_pos e; omega)
  | m + 1, k, e, hm => by
    have hvp := hgt_pos v
    by_cases hr : looseRangeP e ≤ k
    · refine ⟨e, .no, ?_, by omega, by simp, by simp⟩
      unfold hinstP; simp only [hr, ↓reduceIte]; rfl
    match e, hm, hr with
    | .bvar i hh, hm, hr =>
      by_cases hik : i = k
      · subst hik
        refine ⟨liftP v i 0, .direct, ?_, ?_, by simp, fun _ => ⟨[], by rw [er_liftP]; rfl⟩⟩
        · unfold hinstP; simp only [hr, ↓reduceIte, beq_self_eq_true]; rfl
        · rw [hgt_liftP]; simp only [hgt]; omega
      · have hb : (i == k) = false := by simp [hik]
        by_cases hgt' : i > k
        · refine ⟨Expr.mkBVar (i - 1), .no, ?_, by simp [hgt]; omega, by simp, by simp⟩
          unfold hinstP; simp only [hr, ↓reduceIte, hb, hgt']; rfl
        · refine ⟨Expr.bvar i hh, .no, ?_, by simp [hgt]; omega, by simp, by simp⟩
          unfold hinstP; simp only [hr, ↓reduceIte, hb, hgt']; rfl
    | .app f₀ a₀ hh, hm, hr =>
      have hsz := hgt_getAppFnArgs f₀ a₀ hh
      obtain ⟨args0, hNa, hA⟩ := mapM_of_forall
        (f := fun a => Prod.fst <$> hinstP m v k a) (P := fun a r => hgt r + 1 ≤ hgt a + hgt v)
        (getAppFnArgs (.app f₀ a₀ hh)).2.toList (fun a ha => by
          obtain ⟨r, c, h1, h2, -, -⟩ := hinstP_inert hv m k a (by have := hsz.2 a ha; omega)
          exact ⟨r, by rw [h1]; rfl, h2⟩)
      obtain ⟨h0, c0, hNh, hH, hHr, hHd⟩ :=
        hinstP_inert hv m k (getAppFnArgs (.app f₀ a₀ hh)).1 (by have := hsz.1; omega)
      have run : ∀ R, (match (generalizing := false) c0, h0 with
          | .no, _ => pure (mkAppN h0 args0.toArray, Created.no)
          | _, .lam .. => do pure ((← happP m h0 args0), Created.reduced)
          | c, _ => pure (mkAppN h0 args0.toArray, c)) = (Except.ok R : Except String (Expr × Created)) →
          hinstP (m + 1) v k (.app f₀ a₀ hh) = .ok R := by
        intro R hR
        unfold hinstP
        simp only [hr, ↓reduceIte]
        rw [hNa, hNh]
        exact hR
      have hheight : hgt (mkAppN h0 args0.toArray) + 1 ≤ hgt (.app f₀ a₀ hh) + hgt v := by
        rw [← hgt_getAppFnArgs_eq (.app f₀ a₀ hh), hgt_mkAppN, hgt_mkAppN, List.toList_toArray]
        have := foldl_hgt_le (hgt v - 1) (getAppFnArgs (.app f₀ a₀ hh)).2.toList args0
          (hgt (getAppFnArgs (.app f₀ a₀ hh)).1) (hgt h0) (by omega) ?_
        · omega
        · exact EForall2.imp (fun _ _ h => by omega) hA
      cases c0 with
      | no => exact ⟨_, .no, run _ rfl, hheight, by simp, by simp⟩
      | reduced => exact absurd rfl hHr
      | direct =>
        obtain ⟨as, has⟩ := hHd rfl
        have hnl : ∀ n t b bi hh', h0 ≠ .lam n t b bi hh' := by
          rintro n t b bi hh' rfl
          simp only [er] at has
          exact (TmInert.appN (hv.lift k 0) as).not_lam _ _ has.symm
        refine ⟨_, .direct, run (mkAppN h0 args0.toArray, .direct) ?_, hheight, by simp, fun _ => ?_⟩
        · cases h0 with
          | lam n t b bi hh' => exact absurd rfl (hnl n t b bi hh')
          | _ => rfl
        · refine ⟨as ++ args0.map er, ?_⟩
          rw [mkAppN_toList, has, Tm.appN_append]
    | .proj s₀ i x hh, hm, hr =>
      obtain ⟨x0, cx, hNx, hX, hXr, hXd⟩ := hinstP_inert hv m k x (by simp [hgt] at hm; omega)
      have run : ∀ R, (match (generalizing := false) cx with
          | .no => pure (Expr.mkProj s₀ i x0, Created.no)
          | _ =>
            match projCtor? s₀ i x0 with
            | some f => pure (f, Created.reduced)
            | none => pure (Expr.mkProj s₀ i x0, Created.no)) =
            (Except.ok R : Except String (Expr × Created)) →
          hinstP (m + 1) v k (.proj s₀ i x hh) = .ok R := by
        intro R hR
        unfold hinstP
        simp only [hr, ↓reduceIte]
        rw [hNx]
        exact hR
      have hheight : hgt (Expr.mkProj s₀ i x0) + 1 ≤ hgt (.proj s₀ i x hh) + hgt v := by
        simp only [hgt_mkProj, hgt]; omega
      cases cx with
      | no => exact ⟨_, .no, run _ rfl, hheight, by simp, by simp⟩
      | reduced => exact absurd rfl hXr
      | direct =>
        obtain ⟨as, has⟩ := hXd rfl
        have hpc : projCtor? s₀ i x0 = none := by
          cases hpc : projCtor? s₀ i x0 with
          | none => rfl
          | some f =>
            obtain ⟨c, us, α, β, a, b, ex, hp, -⟩ := projCtor?_spec hpc
            rw [has] at ex
            exact absurd ex ((TmInert.appN (hv.lift k 0) as).not_pair4 hp)
        refine ⟨_, .no, run (Expr.mkProj s₀ i x0, .no) ?_, hheight, by simp, by simp⟩
        show (match projCtor? s₀ i x0 with
            | some f => pure (f, Created.reduced)
            | none => pure (Expr.mkProj s₀ i x0, Created.no)) = _
        rw [hpc]; rfl
    | .lam nm t b bi hh, hm, hr =>
      have hm' : hgt t ≤ m ∧ hgt b ≤ m := by simp [hgt] at hm; omega
      obtain ⟨t0, ct, hNt, hT, -, -⟩ := hinstP_inert hv m k t hm'.1
      obtain ⟨b0, cb, hNb, hB, hBr, hBd⟩ := hinstP_inert hv m (k + 1) b hm'.2
      have run : ∀ R, (match (generalizing := false) cb, b0 with
          | .direct, .app f (.bvar 0 _) _ =>
            if !(occursP f 0) then pure (lowerP f 1 0, Created.direct)
            else pure (Expr.mkLam nm t0 b0 bi, Created.no)
          | _, _ => pure (Expr.mkLam nm t0 b0 bi, Created.no)) =
            (Except.ok R : Except String (Expr × Created)) →
          hinstP (m + 1) v k (.lam nm t b bi hh) = .ok R := by
        intro R hR
        unfold hinstP
        simp only [hr, ↓reduceIte]
        rw [hNt, hNb]
        exact hR
      have hlam : hgt (Expr.mkLam nm t0 b0 bi) + 1 ≤ hgt (.lam nm t b bi hh) + hgt v := by
        simp only [hgt_mkLam, hgt]; omega
      by_cases hη : ∃ f h1 h2, cb = .direct ∧ b0 = .app f (.bvar 0 h1) h2 ∧ occursP f 0 = false
      · obtain ⟨f, h1, h2, rfl, rfl, hocc⟩ := hη
        obtain ⟨as, eb⟩ := hBd rfl
        simp only [er] at eb
        rcases appN_eq_app eb.symm with ⟨-, ehd⟩ | ⟨as', rfl, ef⟩
        · exfalso
          have h1' := Tm.occ_lift_mid (k + 1) 0 0 (er v) (Nat.le_refl _) (by omega)
          rw [ehd] at h1'
          simp [Tm.occ] at h1'
        · refine ⟨lowerP f 1 0, .direct, run _ ?_, ?_, by simp, fun _ => ⟨as'.map (Tm.lower 1 0), ?_⟩⟩
          · simp only [hocc, Bool.not_false, ↓reduceIte]; rfl
          · rw [hgt_lowerP]; simp only [hgt] at hB ⊢; omega
          · rw [er_lowerP, ef, Tm.lower_appN, lower_lift_succ]
      · refine ⟨Expr.mkLam nm t0 b0 bi, .no, run _ ?_, hlam, by simp, by simp⟩
        split
        · rename_i f h1 h2
          split
          · rename_i hocc
            exfalso
            exact hη ⟨f, h1, h2, rfl, rfl, by simpa using hocc⟩
          · rfl
        · rfl
    | .forallE nm t b bi hh, hm, hr =>
      have hm' : hgt t ≤ m ∧ hgt b ≤ m := by simp [hgt] at hm; omega
      obtain ⟨t0, ct, hNt, hT, -, -⟩ := hinstP_inert hv m k t hm'.1
      obtain ⟨b0, cb, hNb, hB, -, -⟩ := hinstP_inert hv m (k + 1) b hm'.2
      refine ⟨Expr.mkForallE nm t0 b0 bi, .no, ?_, ?_, by simp, by simp⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNt, hNb]; rfl
      · simp only [hgt_mkForallE, hgt]; omega
    | .letE nm t x b nd hh, hm, hr =>
      have hm' : hgt t ≤ m ∧ hgt x ≤ m ∧ hgt b ≤ m := by simp [hgt] at hm; omega
      obtain ⟨t0, ct, hNt, hT, -, -⟩ := hinstP_inert hv m k t hm'.1
      obtain ⟨x0, cx, hNx, hX, -, -⟩ := hinstP_inert hv m k x hm'.2.1
      obtain ⟨b0, cb, hNb, hB, -, -⟩ := hinstP_inert hv m (k + 1) b hm'.2.2
      refine ⟨Expr.mkLetE nm t0 x0 b0 nd, .no, ?_, ?_, by simp, by simp⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNt, hNx, hNb]; rfl
      · simp only [hgt_mkLetE, hgt]; omega
    | .mdata md x hh, hm, hr =>
      obtain ⟨x0, cx, hNx, hX, hXr, hXd⟩ := hinstP_inert hv m k x (by simp [hgt] at hm; omega)
      refine ⟨Expr.mkMData md x0, cx, ?_, ?_, hXr, fun hd => ?_⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNx]; rfl
      · simp only [hgt_mkMData, hgt]; omega
      · obtain ⟨as, ex⟩ := hXd hd; exact ⟨as, by rw [er_mkMData]; exact ex⟩
    | .fvar .., _, hr | .mvar .., _, hr | .sort .., _, hr | .const .., _, hr | .lit .., _, hr =>
      exact absurd (by simp [looseRangeP]) hr

/-! ## Passive variables -/

/-- `bvar k` may surface at the head of `t` under a substitution: the development's flag for `t`
may be other than `.no` (the variable itself, an application or projection whose subject is
active, a λ whose body is active, which the η step can expose). -/
def Act (k : Nat) : Tm → Bool
  | .bvar i => i == k
  | .app f _ => Act k f
  | .proj _ _ x => Act k x
  | .lam _ b => Act (k + 1) b
  | _ => false

mutual
/-- **`bvar k` is passive in `t`**: it never surfaces at the head of an application spine nor as
the subject of a projection, so substituting any value for it forms no redex. -/
def Passive (k : Nat) : Tm → Bool
  | .app f a => Passive k a && PassiveF k f
  | .lam t b => Passive k t && Passive (k + 1) b
  | .pi t b => Passive k t && Passive (k + 1) b
  | .letE t v b => Passive k t && Passive k v && Passive (k + 1) b
  | .proj _ _ x => !Act k x && Passive k x
  | _ => true
/-- `t` is the function part of an application: its spine head must not be active. -/
def PassiveF (k : Nat) : Tm → Bool
  | .app f a => Passive k a && PassiveF k f
  | .lam t b => !Act (k + 1) b && Passive k t && Passive (k + 1) b
  | .pi t b => Passive k t && Passive (k + 1) b
  | .letE t v b => Passive k t && Passive k v && Passive (k + 1) b
  | .proj _ _ x => !Act k x && Passive k x
  | .bvar i => !(i == k)
  | _ => true
end

theorem passiveF_act : ∀ {k : Nat} {t : Tm}, PassiveF k t = true → Act k t = false ∧ Passive k t = true
  | k, .app f a, h => by
    simp only [PassiveF, Bool.and_eq_true] at h
    have := passiveF_act h.2
    simp only [Act, Passive, h.1, this.1, h.2, Bool.and_self, and_self]
  | k, .lam t b, h => by
    simp only [PassiveF, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Act, Passive, h.1.1, h.1.2, h.2, Bool.and_self, and_self]
  | k, .pi t b, h => by simp only [PassiveF] at h; simp only [Act, Passive, h, and_self]
  | k, .letE t v b, h => by simp only [PassiveF] at h; simp only [Act, Passive, h, and_self]
  | k, .proj s i x, h => by
    simp only [PassiveF, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Act, Passive, h.1, h.2, Bool.not_false, Bool.and_self, and_self]
  | k, .bvar i, h => by
    simp only [PassiveF, Bool.not_eq_true'] at h
    simp only [Act, h, Passive, and_self]
  | _, .fvar _, _ | _, .mvar _, _ | _, .sort _, _ | _, .const _ _, _ | _, .lit _, _ =>
    by simp [Act, Passive]

/-- An application spine is passive when its head is (as a function) and its arguments are. -/
theorem passive_appN {k : Nat} : ∀ {h : Tm} {as : List Tm}, as ≠ [] → Passive k (Tm.appN h as) = true →
    PassiveF k h = true ∧ ∀ a ∈ as, Passive k a = true
  | h, [a], _, hp => by
    simp only [Tm.appN_cons, Tm.appN_nil, Passive, Bool.and_eq_true] at hp
    exact ⟨hp.2, fun x hx => by simp at hx; subst hx; exact hp.1⟩
  | h, a :: b :: as, _, hp => by
    rw [Tm.appN_cons] at hp
    obtain ⟨h1, h2⟩ := passive_appN (h := .app h a) (as := b :: as) (by simp) hp
    simp only [PassiveF, Bool.and_eq_true] at h1
    refine ⟨h1.2, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1.1
    · exact h2 x hx

/-- **Substituting for a passive variable is a walk and computes the plain substitution**: from
fuel `hgt e` on, whatever the value. -/
theorem hinstP_passive (v : Expr) : ∀ (m k : Nat) (e : Expr), Passive k (er e) = true → hgt e ≤ m →
    ∃ r c, hinstP m v k e = .ok (r, c) ∧ er r = Tm.inst (er v) k (er e) ∧
      hgt r + 1 ≤ hgt e + hgt v ∧ (c ≠ .no → er e = .bvar k)
  | 0, _, e, _, h => absurd h (by have := hgt_pos e; omega)
  | m + 1, k, e, hp, hm => by
    have hvp := hgt_pos v
    by_cases hr : looseRangeP e ≤ k
    · refine ⟨e, .no, ?_, ?_, by omega, by simp⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rfl
      · rw [Tm.inst_of_range_le _ _ _ (by rw [← looseRangeP_eq]; exact hr)]
    match e, hp, hm, hr with
    | .bvar i hh, hp, hm, hr =>
      by_cases hik : i = k
      · subst hik
        refine ⟨liftP v i 0, .direct, ?_, ?_, ?_, fun _ => rfl⟩
        · unfold hinstP; simp only [hr, ↓reduceIte, beq_self_eq_true]; rfl
        · rw [er_liftP]; simp [er, Tm.inst]
        · rw [hgt_liftP]; simp only [hgt]; omega
      · have hb : (i == k) = false := by simp [hik]
        by_cases hgt' : i > k
        · refine ⟨Expr.mkBVar (i - 1), .no, ?_, ?_, by simp [hgt]; omega, by simp⟩
          · unfold hinstP; simp only [hr, ↓reduceIte, hb, hgt']; rfl
          · simp [er, Tm.inst, hik, show k < i from hgt']
        · refine ⟨Expr.bvar i hh, .no, ?_, ?_, by simp [hgt]; omega, by simp⟩
          · unfold hinstP; simp only [hr, ↓reduceIte, hb, hgt']; rfl
          · simp [er, Tm.inst, hik, show ¬ k < i from hgt']
    | .app f₀ a₀ hh, hp, hm, hr =>
      have hsz := hgt_getAppFnArgs f₀ a₀ hh
      have hsp := er_getAppFnArgs (.app f₀ a₀ hh)
      have hne : (getAppFnArgs (.app f₀ a₀ hh)).2.toList ≠ [] := by
        simp [getAppFnArgs]
      rw [hsp] at hp
      obtain ⟨hpF, hpA⟩ := passive_appN (by simpa using hne) hp
      obtain ⟨hnA, hpH⟩ := passiveF_act hpF
      obtain ⟨args0, hNa, hA⟩ := mapM_of_forall
        (f := fun a => Prod.fst <$> hinstP m v k a)
        (P := fun a r => er r = Tm.inst (er v) k (er a) ∧ hgt r + 1 ≤ hgt a + hgt v)
        (getAppFnArgs (.app f₀ a₀ hh)).2.toList (fun a ha => by
          obtain ⟨r, c, h1, h2, h3, -⟩ := hinstP_passive v m k a
            (hpA _ (List.mem_map.2 ⟨a, ha, rfl⟩)) (by have := hsz.2 a ha; omega)
          exact ⟨r, by rw [h1]; rfl, h2, h3⟩)
      obtain ⟨h0, c0, hNh, hH, hHh, hHc⟩ :=
        hinstP_passive v m k (getAppFnArgs (.app f₀ a₀ hh)).1 hpH (by have := hsz.1; omega)
      have hc0 : c0 = .no := by
        by_contra hc
        have := hHc hc
        rw [this] at hnA; simp [Act] at hnA
      subst hc0
      refine ⟨mkAppN h0 args0.toArray, .no, ?_, ?_, ?_, by simp⟩
      · unfold hinstP
        simp only [hr, ↓reduceIte]
        rw [hNa, hNh]
        rfl
      · rw [mkAppN_toList, hH, hsp, Tm.inst_appN, List.map_map]
        congr 1
        exact EForall2.map_eq (fun _ _ h => h.1) hA
      · rw [← hgt_getAppFnArgs_eq (.app f₀ a₀ hh), hgt_mkAppN, hgt_mkAppN, List.toList_toArray]
        have := foldl_hgt_le (hgt v - 1) (getAppFnArgs (.app f₀ a₀ hh)).2.toList args0
          (hgt (getAppFnArgs (.app f₀ a₀ hh)).1) (hgt h0) (by omega)
          (EForall2.imp (fun _ _ h => by omega) hA)
        omega
    | .proj s₀ i x hh, hp, hm, hr =>
      simp only [er, Passive, Bool.and_eq_true, Bool.not_eq_true'] at hp
      obtain ⟨x0, cx, hNx, hX, hXh, hXc⟩ := hinstP_passive v m k x hp.2 (by simp [hgt] at hm; omega)
      have hcx : cx = .no := by
        by_contra hc
        have := hXc hc
        rw [this] at hp; simp [Act] at hp
      subst hcx
      refine ⟨Expr.mkProj s₀ i x0, .no, ?_, ?_, ?_, by simp⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNx]; rfl
      · simp only [er_mkProj, er, Tm.inst, hX]
      · simp only [hgt_mkProj, hgt]; omega
    | .lam nm t b bi hh, hp, hm, hr =>
      simp only [er, Passive, Bool.and_eq_true] at hp
      have hm' : hgt t ≤ m ∧ hgt b ≤ m := by simp [hgt] at hm; omega
      obtain ⟨t0, ct, hNt, hT, hTh, -⟩ := hinstP_passive v m k t hp.1 hm'.1
      obtain ⟨b0, cb, hNb, hB, hBh, hBc⟩ := hinstP_passive v m (k + 1) b hp.2 hm'.2
      have hnη : ¬ ∃ f h1 h2, cb = .direct ∧ b0 = .app f (.bvar 0 h1) h2 := by
        rintro ⟨f, h1, h2, rfl, rfl⟩
        have eb := hBc (by simp)
        rw [eb] at hB
        simp only [er, Tm.inst, ↓reduceIte] at hB
        have h1' := Tm.occ_lift_mid (k + 1) 0 0 (er v) (Nat.le_refl _) (by omega)
        rw [← hB] at h1'
        simp [Tm.occ] at h1'
      have run : ∀ R, (match (generalizing := false) cb, b0 with
          | .direct, .app f (.bvar 0 _) _ =>
            if !(occursP f 0) then pure (lowerP f 1 0, Created.direct)
            else pure (Expr.mkLam nm t0 b0 bi, Created.no)
          | _, _ => pure (Expr.mkLam nm t0 b0 bi, Created.no)) =
            (Except.ok R : Except String (Expr × Created)) →
          hinstP (m + 1) v k (.lam nm t b bi hh) = .ok R := by
        intro R hR
        unfold hinstP
        simp only [hr, ↓reduceIte]
        rw [hNt, hNb]
        exact hR
      refine ⟨Expr.mkLam nm t0 b0 bi, .no, run _ ?_, ?_, ?_, by simp⟩
      · split
        · rename_i f h1 h2
          exact absurd ⟨f, h1, h2, rfl, rfl⟩ hnη
        · rfl
      · simp only [er_mkLam, er, Tm.inst, hT, hB]
      · simp only [hgt_mkLam, hgt]; omega
    | .forallE nm t b bi hh, hp, hm, hr =>
      simp only [er, Passive, Bool.and_eq_true] at hp
      have hm' : hgt t ≤ m ∧ hgt b ≤ m := by simp [hgt] at hm; omega
      obtain ⟨t0, ct, hNt, hT, hTh, -⟩ := hinstP_passive v m k t hp.1 hm'.1
      obtain ⟨b0, cb, hNb, hB, hBh, -⟩ := hinstP_passive v m (k + 1) b hp.2 hm'.2
      refine ⟨Expr.mkForallE nm t0 b0 bi, .no, ?_, ?_, ?_, by simp⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNt, hNb]; rfl
      · simp only [er_mkForallE, er, Tm.inst, hT, hB]
      · simp only [hgt_mkForallE, hgt]; omega
    | .letE nm t x b nd hh, hp, hm, hr =>
      simp only [er, Passive, Bool.and_eq_true] at hp
      have hm' : hgt t ≤ m ∧ hgt x ≤ m ∧ hgt b ≤ m := by simp [hgt] at hm; omega
      obtain ⟨t0, ct, hNt, hT, hTh, -⟩ := hinstP_passive v m k t hp.1.1 hm'.1
      obtain ⟨x0, cx, hNx, hX, hXh, -⟩ := hinstP_passive v m k x hp.1.2 hm'.2.1
      obtain ⟨b0, cb, hNb, hB, hBh, -⟩ := hinstP_passive v m (k + 1) b hp.2 hm'.2.2
      refine ⟨Expr.mkLetE nm t0 x0 b0 nd, .no, ?_, ?_, ?_, by simp⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNt, hNx, hNb]; rfl
      · simp only [er_mkLetE, er, Tm.inst, hT, hX, hB]
      · simp only [hgt_mkLetE, hgt]; omega
    | .mdata md x hh, hp, hm, hr =>
      simp only [er] at hp
      obtain ⟨x0, cx, hNx, hX, hXh, hXc⟩ := hinstP_passive v m k x hp (by simp [hgt] at hm; omega)
      refine ⟨Expr.mkMData md x0, cx, ?_, ?_, ?_, fun hc => by simpa [er] using hXc hc⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNx]; rfl
      · simp only [er_mkMData, er, hX]
      · simp only [hgt_mkMData, hgt]; omega
    | .fvar .., _, _, hr | .mvar .., _, _, hr | .sort .., _, _, hr | .const .., _, _, hr
    | .lit .., _, _, hr => exact absurd (by simp [looseRangeP]) hr

theorem foldl_hgt_eq : ∀ (as as' : List Expr) (x : Nat),
    EForall2 (fun a' a => hgt a' = hgt a) as' as →
    as'.foldl (fun acc a => max acc (hgt a) + 1) x = as.foldl (fun acc a => max acc (hgt a) + 1) x
  | [], [], x, .nil => rfl
  | a :: as, a' :: as', x, .cons ha hs => by
    simp only [List.foldl_cons, ha]
    exact foldl_hgt_eq as as' _ hs

theorem occ_er_app_of {f₀ a₀ : Expr} {hh : Address} {k : Nat}
    (h : Tm.occ (er (.app f₀ a₀ hh)) k = false) :
    Tm.occ (er (getAppFnArgs (.app f₀ a₀ hh)).1) k = false ∧
      ∀ a ∈ (getAppFnArgs (.app f₀ a₀ hh)).2.toList, Tm.occ (er a) k = false := by
  rw [er_getAppFnArgs] at h
  obtain ⟨h1, h2⟩ := Tm.occ_appN h
  exact ⟨h1, fun a ha => h2 _ (List.mem_map.2 ⟨a, ha, rfl⟩)⟩

theorem forall2_hgt_of_mapM {v : Expr} {m k : Nat}
    (H : ∀ a r c, hinstP m v k a = .ok (r, c) → Tm.occ (er a) k = false → hgt r = hgt a) :
    ∀ {l l' : List Expr}, EForall2 (fun a b => (Prod.fst <$> hinstP m v k a) = .ok b) l l' →
      (∀ a ∈ l, Tm.occ (er a) k = false) → EForall2 (fun a' a => hgt a' = hgt a) l' l
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons hab hs, ho => by
    obtain ⟨⟨b', cb⟩, hb, rfl⟩ := map_ok hab
    exact .cons (H _ _ _ hb (ho _ List.mem_cons_self))
      (forall2_hgt_of_mapM H hs fun a ha => ho a (List.mem_cons_of_mem _ ha))

/-- **Substituting for a variable that does not occur** changes no height and raises no flag. -/
theorem hinstP_noocc (v : Expr) : ∀ (m k : Nat) (e r : Expr) (c : Created),
    hinstP m v k e = .ok (r, c) → Tm.occ (er e) k = false → hgt r = hgt e ∧ c = .no
  | 0, k, e, r, c, h, _ => by rw [hinstP_zero] at h; cases h
  | m + 1, k, e, r, c, h, hocc => by
    unfold hinstP at h
    by_cases hr : looseRangeP e ≤ k
    · simp only [hr, ↓reduceIte] at h
      cases pure_ok h; exact ⟨rfl, rfl⟩
    simp only [hr, ↓reduceIte] at h
    match e, h, hocc with
    | .bvar i _, h, hocc =>
      simp only [er, Tm.occ, beq_eq_false_iff_ne, ne_eq] at hocc
      have hik' : (i == k) = false := by simp [hocc]
      simp only [hik', Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> (cases pure_ok h; exact ⟨rfl, rfl⟩)
    | .app f₀ a₀ hh, h, hocc =>
      obtain ⟨hoH, hoA⟩ := occ_er_app_of hocc
      obtain ⟨args', hargs, h⟩ := bind_ok h
      obtain ⟨⟨h', c'⟩, hh', h⟩ := bind_ok h
      obtain ⟨hH, rfl⟩ := hinstP_noocc v m k _ _ _ hh' hoH
      have hmap := mapM_ok hargs
      have hA := forall2_hgt_of_mapM (fun a r c h1 h2 => (hinstP_noocc v m k a r c h1 h2).1) hmap hoA
      dsimp only at h
      cases pure_ok h
      refine ⟨?_, rfl⟩
      rw [← hgt_getAppFnArgs_eq (.app f₀ a₀ hh), hgt_mkAppN, hgt_mkAppN, List.toList_toArray, hH]
      exact foldl_hgt_eq _ _ _ hA
    | .proj s i x _, h, hocc =>
      simp only [er, Tm.occ] at hocc
      obtain ⟨⟨x', c'⟩, hx, h⟩ := bind_ok h
      obtain ⟨hX, rfl⟩ := hinstP_noocc v m k _ _ _ hx hocc
      dsimp only at h
      cases pure_ok h
      exact ⟨by simp only [hgt_mkProj, hgt, hX], rfl⟩
    | .lam n t b bi _, h, hocc =>
      simp only [er, Tm.occ, Bool.or_eq_false_iff] at hocc
      obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
      obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
      obtain ⟨hT, -⟩ := hinstP_noocc v m k _ _ _ ht hocc.1
      obtain ⟨hB, rfl⟩ := hinstP_noocc v m (k + 1) _ _ _ hb hocc.2
      dsimp only at h
      cases pure_ok h
      exact ⟨by simp only [hgt_mkLam, hgt, hT, hB], rfl⟩
    | .forallE n t b bi _, h, hocc =>
      simp only [er, Tm.occ, Bool.or_eq_false_iff] at hocc
      obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
      obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
      obtain ⟨hT, -⟩ := hinstP_noocc v m k _ _ _ ht hocc.1
      obtain ⟨hB, -⟩ := hinstP_noocc v m (k + 1) _ _ _ hb hocc.2
      cases pure_ok h
      exact ⟨by simp only [hgt_mkForallE, hgt, hT, hB], rfl⟩
    | .letE n t x b nd _, h, hocc =>
      simp only [er, Tm.occ, Bool.or_eq_false_iff] at hocc
      obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
      obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
      obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
      obtain ⟨hT, -⟩ := hinstP_noocc v m k _ _ _ ht hocc.1.1
      obtain ⟨hX, -⟩ := hinstP_noocc v m k _ _ _ hx hocc.1.2
      obtain ⟨hB, -⟩ := hinstP_noocc v m (k + 1) _ _ _ hb hocc.2
      cases pure_ok h
      exact ⟨by simp only [hgt_mkLetE, hgt, hT, hX, hB], rfl⟩
    | .mdata md x _, h, hocc =>
      simp only [er] at hocc
      obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
      obtain ⟨hX, rfl⟩ := hinstP_noocc v m k _ _ _ hx hocc
      cases pure_ok h
      exact ⟨by simp only [hgt_mkMData, hgt, hX], rfl⟩
    | .fvar .., h, _ | .mvar .., h, _ | .sort .., h, _ | .const .., h, _ | .lit .., h, _ =>
      cases pure_ok h; exact ⟨rfl, rfl⟩

/-! ## Occurrences under substitution and lifting -/

theorem act_occ : ∀ {j : Nat} {t : Tm}, Act j t = true → Tm.occ t j = true
  | j, .bvar i, h => by simpa [Act, Tm.occ] using h
  | j, .app f _, h => by simp only [Act] at h; simp [Tm.occ, act_occ h]
  | j, .proj _ _ x, h => by simp only [Act] at h; simp [Tm.occ, act_occ h]
  | j, .lam _ b, h => by simp only [Act] at h; simp [Tm.occ, act_occ h]
  | _, .fvar _, h | _, .mvar _, h | _, .sort _, h | _, .const _ _, h | _, .lit _, h
  | _, .pi _ _, h | _, .letE _ _ _, h => by simp [Act] at h

theorem passive_of_noocc : ∀ {j : Nat} {t : Tm}, Tm.occ t j = false →
    Passive j t = true ∧ PassiveF j t = true
  | j, .app f a, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    have h1 := passive_of_noocc h.1
    have h2 := passive_of_noocc h.2
    simp [Passive, PassiveF, h1.2, h2.1]
  | j, .lam t b, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    have h1 := passive_of_noocc h.1
    have h2 := passive_of_noocc h.2
    have h3 : Act (j + 1) b = false := by
      cases ha : Act (j + 1) b
      · rfl
      · have := act_occ ha; rw [h.2] at this; cases this
    simp [Passive, PassiveF, h1.1, h2.1, h3]
  | j, .pi t b, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    simp [Passive, PassiveF, (passive_of_noocc h.1).1, (passive_of_noocc h.2).1]
  | j, .letE t v b, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    simp [Passive, PassiveF, (passive_of_noocc h.1.1).1, (passive_of_noocc h.1.2).1,
      (passive_of_noocc h.2).1]
  | j, .proj _ _ x, h => by
    simp only [Tm.occ] at h
    have h3 : Act j x = false := by
      cases ha : Act j x
      · rfl
      · have := act_occ ha; rw [h] at this; cases this
    simp [Passive, PassiveF, (passive_of_noocc h).1, h3]
  | j, .bvar i, h => by simpa [Passive, PassiveF, Tm.occ] using h
  | _, .fvar _, _ | _, .mvar _, _ | _, .sort _, _ | _, .const _ _, _ | _, .lit _, _ =>
    by simp [Passive, PassiveF]

theorem occ_lift_ge : ∀ (n c : Nat) (t : Tm) (j : Nat), c ≤ j → Tm.occ (Tm.lift n c t) (j + n) = Tm.occ t j
  | n, c, .bvar i, j, h => by
    simp only [Tm.lift, Tm.occ]
    by_cases hi : c ≤ i
    · simp only [hi, ↓reduceIte]; rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega
    · simp only [hi, ↓reduceIte]; rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega
  | n, c, .app f a, j, h => by simp only [Tm.lift, Tm.occ, occ_lift_ge n c f j h, occ_lift_ge n c a j h]
  | n, c, .lam t b, j, h => by
    simp only [Tm.lift, Tm.occ, occ_lift_ge n c t j h]
    rw [show j + n + 1 = (j + 1) + n by omega, occ_lift_ge n (c + 1) b (j + 1) (by omega)]
  | n, c, .pi t b, j, h => by
    simp only [Tm.lift, Tm.occ, occ_lift_ge n c t j h]
    rw [show j + n + 1 = (j + 1) + n by omega, occ_lift_ge n (c + 1) b (j + 1) (by omega)]
  | n, c, .letE t v b, j, h => by
    simp only [Tm.lift, Tm.occ, occ_lift_ge n c t j h, occ_lift_ge n c v j h]
    rw [show j + n + 1 = (j + 1) + n by omega, occ_lift_ge n (c + 1) b (j + 1) (by omega)]
  | n, c, .proj s i x, j, h => by simp only [Tm.lift, Tm.occ, occ_lift_ge n c x j h]
  | _, _, .fvar _, _, _ | _, _, .mvar _, _, _ | _, _, .sort _, _, _ | _, _, .const _ _, _, _
  | _, _, .lit _, _, _ => rfl

/-- An occurrence in a substitution comes from the term (one binder up) or from the value. -/
theorem occ_inst_gen (a : Tm) : ∀ (t : Tm) (k j : Nat), Tm.occ (Tm.inst a k t) (j + k) = true →
    Tm.occ t (j + k + 1) = true ∨ Tm.occ a j = true
  | .bvar i, k, j, h => by
    simp only [Tm.inst] at h
    by_cases hik : i = k
    · simp only [hik, ↓reduceIte] at h
      rw [Nat.add_comm j k, show k + j = j + k by omega] at h
      have := occ_lift_ge k 0 a j (Nat.zero_le _)
      rw [Nat.add_comm] at this
      right; rw [← this]; rw [Nat.add_comm]; exact h
    · simp only [hik, ↓reduceIte, Tm.occ] at h
      left; simp only [Tm.occ]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte] at h; simp at h ⊢; omega
      · simp only [hki, ↓reduceIte] at h; simp at h; omega
  | .app f x, k, j, h => by
    simp only [Tm.inst, Tm.occ, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases occ_inst_gen a f k j h with h' | h'
      · left; simp [Tm.occ, h']
      · exact .inr h'
    · rcases occ_inst_gen a x k j h with h' | h'
      · left; simp [Tm.occ, h']
      · exact .inr h'
  | .lam t b, k, j, h => by
    simp only [Tm.inst, Tm.occ, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases occ_inst_gen a t k j h with h' | h'
      · left; simp [Tm.occ, h']
      · exact .inr h'
    · rw [show j + k + 1 = j + (k + 1) by omega] at h
      rcases occ_inst_gen a b (k + 1) j h with h' | h'
      · left; simp only [Tm.occ, Bool.or_eq_true]; right
        rw [show j + k + 1 + 1 = j + (k + 1) + 1 by omega]; exact h'
      · exact .inr h'
  | .pi t b, k, j, h => by
    simp only [Tm.inst, Tm.occ, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases occ_inst_gen a t k j h with h' | h'
      · left; simp [Tm.occ, h']
      · exact .inr h'
    · rw [show j + k + 1 = j + (k + 1) by omega] at h
      rcases occ_inst_gen a b (k + 1) j h with h' | h'
      · left; simp only [Tm.occ, Bool.or_eq_true]; right
        rw [show j + k + 1 + 1 = j + (k + 1) + 1 by omega]; exact h'
      · exact .inr h'
  | .letE t v b, k, j, h => by
    simp only [Tm.inst, Tm.occ, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · rcases occ_inst_gen a t k j h with h' | h'
      · left; simp [Tm.occ, h']
      · exact .inr h'
    · rcases occ_inst_gen a v k j h with h' | h'
      · left; simp [Tm.occ, h']
      · exact .inr h'
    · rw [show j + k + 1 = j + (k + 1) by omega] at h
      rcases occ_inst_gen a b (k + 1) j h with h' | h'
      · left; simp only [Tm.occ, Bool.or_eq_true]; right
        rw [show j + k + 1 + 1 = j + (k + 1) + 1 by omega]; exact h'
      · exact .inr h'
  | .proj s i x, k, j, h => by
    simp only [Tm.inst, Tm.occ] at h
    rcases occ_inst_gen a x k j h with h' | h'
    · left; simp [Tm.occ, h']
    · exact .inr h'
  | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h | .const _ _, _, _, h
  | .lit _, _, _, h => by simp [Tm.inst, Tm.occ] at h

theorem occ_appN_or {h : Tm} : ∀ {as : List Tm} {j : Nat}, Tm.occ (Tm.appN h as) j = true →
    Tm.occ h j = true ∨ ∃ a ∈ as, Tm.occ a j = true
  | [], j, e => .inl e
  | a :: as, j, e => by
    rw [Tm.appN_cons] at e
    rcases occ_appN_or (h := .app h a) e with e | ⟨b, hb, e⟩
    · simp only [Tm.occ, Bool.or_eq_true] at e
      rcases e with e | e
      · exact .inl e
      · exact .inr ⟨a, List.mem_cons_self, e⟩
    · exact .inr ⟨b, List.mem_cons_of_mem _ hb, e⟩

/-! ## Passivity under substitution at a higher index -/

mutual
theorem act_inst_lt (a : Tm) : ∀ (t : Tm) (j k : Nat), j < k → Act j (Tm.inst a k t) = Act j t
  | .bvar i, j, k, h => by
    simp only [Tm.inst]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte]
      cases ha : Act j (Tm.lift i 0 a)
      · simp [Act]; omega
      · have := act_occ ha
        rw [Tm.occ_lift_mid i 0 j a (Nat.zero_le _) (by omega)] at this; cases this
    · simp only [hik, ↓reduceIte, Act]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte]; rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega
      · simp only [hki, ↓reduceIte]
  | .app f x, j, k, h => by simp only [Tm.inst, Act, act_inst_lt a f j k h]
  | .proj _ _ x, j, k, h => by simp only [Tm.inst, Act, act_inst_lt a x j k h]
  | .lam t b, j, k, h => by simp only [Tm.inst, Act, act_inst_lt a b (j + 1) (k + 1) (by omega)]
  | .pi _ _, _, _, _ | .letE _ _ _, _, _, _ | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _
  | .const _ _, _, _, _ | .lit _, _, _, _ => rfl

theorem passive_inst_lt (a : Tm) : ∀ (t : Tm) (j k : Nat), j < k →
    Passive j (Tm.inst a k t) = Passive j t ∧ PassiveF j (Tm.inst a k t) = PassiveF j t
  | .bvar i, j, k, h => by
    simp only [Tm.inst]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte]
      have := passive_of_noocc (Tm.occ_lift_mid i 0 j a (Nat.zero_le _) (by omega))
      rw [this.1, this.2]; simp [Passive, PassiveF]; omega
    · simp only [hik, ↓reduceIte, Passive, PassiveF, true_and]
      by_cases hki : k < i
      · simp only [hki, ↓reduceIte]; rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true', beq_eq_false_iff_ne]; omega
      · simp only [hki, ↓reduceIte]
  | .app f x, j, k, h => by
    have h1 := passive_inst_lt a f j k h
    have h2 := passive_inst_lt a x j k h
    simp only [Tm.inst, Passive, PassiveF, h1.2, h2.1, and_self]
  | .lam t b, j, k, h => by
    have h1 := passive_inst_lt a t j k h
    have h2 := passive_inst_lt a b (j + 1) (k + 1) (by omega)
    simp only [Tm.inst, Passive, PassiveF, h1.1, h2.1, act_inst_lt a b (j + 1) (k + 1) (by omega),
      and_self]
  | .pi t b, j, k, h => by
    have h1 := passive_inst_lt a t j k h
    have h2 := passive_inst_lt a b (j + 1) (k + 1) (by omega)
    simp only [Tm.inst, Passive, PassiveF, h1.1, h2.1, and_self]
  | .letE t v b, j, k, h => by
    have h1 := passive_inst_lt a t j k h
    have h3 := passive_inst_lt a v j k h
    have h2 := passive_inst_lt a b (j + 1) (k + 1) (by omega)
    simp only [Tm.inst, Passive, PassiveF, h1.1, h2.1, h3.1, and_self]
  | .proj s i x, j, k, h => by
    have h1 := passive_inst_lt a x j k h
    simp only [Tm.inst, Passive, PassiveF, h1.1, act_inst_lt a x j k h, and_self]
  | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ =>
    ⟨rfl, rfl⟩
end

/-! ## One hereditary level: head β at a call site -/

/-- The sum of the heights of a list of expressions. -/
def hsum (l : List Expr) : Nat := (l.map hgt).sum

theorem hsum_cons (a : Expr) (l : List Expr) : hsum (a :: l) = hgt a + hsum l := by
  simp [hsum]

theorem foldl_hgt_mono : ∀ (l : List Expr) (x y : Nat), x ≤ y →
    l.foldl (fun acc a => max acc (hgt a) + 1) x ≤ l.foldl (fun acc a => max acc (hgt a) + 1) y
  | [], x, y, h => h
  | a :: l, x, y, h => by
    simp only [List.foldl_cons]; exact foldl_hgt_mono l _ _ (by omega)

theorem foldl_hgt_le_sum : ∀ (l : List Expr) (x : Nat), 1 ≤ x →
    l.foldl (fun acc a => max acc (hgt a) + 1) x ≤ x + hsum l
  | [], x, _ => by simp [hsum]
  | a :: l, x, hx => by
    simp only [List.foldl_cons, hsum_cons]
    have := hgt_pos a
    have h1 := foldl_hgt_mono l (max x (hgt a) + 1) (x + hgt a) (by omega)
    have h2 := foldl_hgt_le_sum l (x + hgt a) (by omega)
    omega

theorem hgt_mkAppN_le (f : Expr) (l : List Expr) : hgt (mkAppN f l.toArray) ≤ hgt f + hsum l := by
  rw [hgt_mkAppN, List.toList_toArray]; exact foldl_hgt_le_sum l _ (hgt_pos f)

theorem happP_mkAppN (m : Nat) (f : Expr) (args : List Expr)
    (h : args = [] ∨ ∀ n t b bi hh, f ≠ Expr.lam n t b bi hh) :
    happP (m + 1) f args = .ok (mkAppN f args.toArray) := by
  rcases h with rfl | h
  · rw [happP_succ]; cases f <;> rfl
  · cases args with
    | nil => rw [happP_succ]; cases f <;> rfl
    | cons a rest => exact happP_succ_nonlam m f a rest h

/-- **Head β with inert arguments** (P3a's rule right-hand sides at the telescope's free
variables): from fuel `hgt f + Σ hgt args + 1` on. -/
theorem happP_inert : ∀ (args : List Expr) (f : Expr) (m : Nat), (∀ a ∈ args, TmInert (er a)) →
    hgt f + hsum args + 1 ≤ m → ∃ r, happP m f args = .ok r ∧ hgt r ≤ hgt f + hsum args
  | args, f, 0, _, hm => absurd hm (by omega)
  | [], f, m + 1, _, _ => ⟨_, happP_mkAppN m f [] (.inl rfl), by simpa [hsum] using hgt_mkAppN_le f []⟩
  | a :: rest, f, m + 1, ha, hm => by
    rw [hsum_cons] at hm ⊢
    by_cases hl : ∃ n t b bi hh, f = Expr.lam n t b bi hh
    · obtain ⟨n, t, b, bi, hh, rfl⟩ := hl
      have hb : hgt b + 1 ≤ hgt (Expr.lam n t b bi hh) := by simp [hgt]; omega
      obtain ⟨b', cb, h1, h2, -, -⟩ := hinstP_inert (ha a List.mem_cons_self) m 0 b (by omega)
      obtain ⟨r, h3, h4⟩ := happP_inert rest b' m (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (by omega)
      refine ⟨r, ?_, by omega⟩
      rw [happP_succ]
      show (do let (b', _) ← hinstP m a 0 b; happP m b' rest) = .ok r
      rw [h1]; exact h3
    · refine ⟨_, happP_mkAppN m f _ (.inr fun n t b bi hh e => hl ⟨n, t, b, bi, hh, e⟩), ?_⟩
      have := hgt_mkAppN_le f (a :: rest)
      rw [hsum_cons] at this; exact this

/-- `bvar i` with `i < n`: a parameter of the λ-chain being consumed. -/
def isParam (n : Nat) : Tm → Bool
  | .bvar i => i < n
  | _ => false

/-- **A first-order value**: a λ-chain each of whose binders is passive in the rest (binder
types and body), with a body that is not one of its parameters; consuming its parameters forms
no redex (the census's `fo` and `inert` values). -/
def FOv : Tm → Nat → Bool
  | .lam _ b, n => Passive 0 b && FOv b (n + 1)
  | t, n => !isParam n t

theorem fov_inst (a : Tm) : ∀ (t : Tm) (m : Nat), FOv t (m + 1) = true → FOv (Tm.inst a m t) m = true
  | .lam t b, m, h => by
    simp only [FOv, Bool.and_eq_true] at h
    simp only [Tm.inst, FOv, Bool.and_eq_true]
    exact ⟨by rw [(passive_inst_lt a b 0 (m + 1) (by omega)).1]; exact h.1, fov_inst a b (m + 1) h.2⟩
  | .bvar i, m, h => by
    simp only [FOv, isParam, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at h
    simp only [Tm.inst]
    have h1 : i ≠ m := by omega
    have h2 : m < i := by omega
    simp only [h1, h2, ↓reduceIte, FOv, isParam]; simp; omega
  | .app _ _, _, _ | .pi _ _, _, _ | .letE _ _ _, _, _ | .proj _ _ _, _, _ | .fvar _, _, _
  | .mvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => by simp [Tm.inst, FOv, isParam]

/-- **Head β of a first-order value**: from fuel `hgt f + Σ hgt args + 1` on, whatever the
arguments; the result mentions only what the function or an argument mentions. -/
theorem happP_passive : ∀ (args : List Expr) (f : Expr) (m : Nat), FOv (er f) 0 = true →
    hgt f + hsum args + 1 ≤ m →
    ∃ r, happP m f args = .ok r ∧ hgt r ≤ hgt f + hsum args ∧
      ∀ j, Tm.occ (er r) j = true → Tm.occ (er f) j = true ∨ ∃ a ∈ args, Tm.occ (er a) j = true
  | args, f, 0, _, hm => absurd hm (by omega)
  | [], f, m + 1, _, _ =>
    ⟨_, happP_mkAppN m f [] (.inl rfl), by simpa [hsum] using hgt_mkAppN_le f [],
      fun j h => .inl (by rw [mkAppN_toList, List.map_nil, Tm.appN_nil] at h; exact h)⟩
  | a :: rest, f, m + 1, hf, hm => by
    rw [hsum_cons] at hm ⊢
    by_cases hl : ∃ n t b bi hh, f = Expr.lam n t b bi hh
    · obtain ⟨n, t, b, bi, hh, rfl⟩ := hl
      simp only [er, FOv, Bool.and_eq_true] at hf
      have hb : hgt b + 1 ≤ hgt (Expr.lam n t b bi hh) := by simp [hgt]; omega
      obtain ⟨b', cb, h1, h2, h3, -⟩ := hinstP_passive a m 0 b hf.1 (by omega)
      have hf' : FOv (er b') 0 = true := by rw [h2]; exact fov_inst (er a) (er b) 0 hf.2
      obtain ⟨r, h4, h5, h6⟩ := happP_passive rest b' m hf' (by omega)
      refine ⟨r, ?_, by omega, fun j hj => ?_⟩
      · rw [happP_succ]
        show (do let (b', _) ← hinstP m a 0 b; happP m b' rest) = .ok r
        rw [h1]; exact h4
      · rcases h6 j hj with hj | ⟨x, hx, hj⟩
        · rw [h2] at hj
          rcases occ_inst_gen (er a) (er b) 0 j (by simpa using hj) with hj | hj
          · left; simp only [er, Tm.occ, Bool.or_eq_true]; right; exact hj
          · exact .inr ⟨a, List.mem_cons_self, hj⟩
        · exact .inr ⟨x, List.mem_cons_of_mem _ hx, hj⟩
    · refine ⟨_, happP_mkAppN m f _ (.inr fun n t b bi hh e => hl ⟨n, t, b, bi, hh, e⟩), ?_, ?_⟩
      · have := hgt_mkAppN_le f (a :: rest)
        rw [hsum_cons] at this; exact this
      · intro j hj
        rw [mkAppN_toList] at hj
        rcases occ_appN_or hj with hj | ⟨x, hx, hj⟩
        · exact .inl hj
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact .inr ⟨y, hy, hj⟩

/-! ## Substituting at motive sites (P3a's minor types) -/

theorem occ_lower_one : ∀ (t : Tm) (k j : Nat), Tm.occ t k = false →
    Tm.occ (Tm.lower 1 k t) j = Tm.occ t (if j < k then j else j + 1)
  | .bvar i, k, j, h => by
    simp only [Tm.occ, beq_eq_false_iff_ne, ne_eq] at h
    simp only [Tm.lower, Tm.occ]
    rw [Bool.eq_iff_iff]
    by_cases hi : k + 1 ≤ i <;> by_cases hj : j < k <;> simp [hi, hj] <;> omega
  | .app f a, k, j, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    simp only [Tm.lower, Tm.occ, occ_lower_one f k j h.1, occ_lower_one a k j h.2]
  | .lam t b, k, j, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    simp only [Tm.lower, Tm.occ, occ_lower_one t k j h.1, occ_lower_one b (k + 1) (j + 1) h.2]
    by_cases hj : j < k <;> simp [hj, show (j + 1 < k + 1) = (j < k) by simp [hj]]
  | .pi t b, k, j, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    simp only [Tm.lower, Tm.occ, occ_lower_one t k j h.1, occ_lower_one b (k + 1) (j + 1) h.2]
    by_cases hj : j < k <;> simp [hj, show (j + 1 < k + 1) = (j < k) by simp [hj]]
  | .letE t v b, k, j, h => by
    simp only [Tm.occ, Bool.or_eq_false_iff] at h
    simp only [Tm.lower, Tm.occ, occ_lower_one t k j h.1.1, occ_lower_one v k j h.1.2,
      occ_lower_one b (k + 1) (j + 1) h.2]
    by_cases hj : j < k <;> simp [hj, show (j + 1 < k + 1) = (j < k) by simp [hj]]
  | .proj s i x, k, j, h => by
    simp only [Tm.occ] at h
    simp only [Tm.lower, Tm.occ, occ_lower_one x k j h]
  | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ =>
    rfl

/-- Substituting for a variable that does not occur shifts the variables above it down. -/
theorem occ_inst_noocc (v t : Tm) (k j : Nat) (h : Tm.occ t k = false) :
    Tm.occ (Tm.inst v k t) j = Tm.occ t (if j < k then j else j + 1) := by
  rw [Tm.inst_eq_lower v k t h, occ_lower_one t k j h]

/-- None of `bvar k, …, bvar (k + K - 1)` occurs in `e`. -/
def NoOcc (K k : Nat) (e : Expr) : Prop := ∀ j < K, Tm.occ (er e) (k + j) = false

/-- A **motive site**: an application `bvar i a₁ … aₙ`, `bvar i` one of the `K` variables from
`k`, whose arguments mention none of them and have heights summing to at most `H`. -/
def Site (K H k : Nat) (e : Expr) : Prop :=
  ∃ i hh, (getAppFnArgs e).1 = .bvar i hh ∧ k ≤ i ∧ i < k + K ∧
    (∀ a ∈ (getAppFnArgs e).2.toList, NoOcc K k a) ∧ hsum (getAppFnArgs e).2.toList ≤ H

/-- **Variables `k … k+K-1` occur in `e` only at motive sites**, which stand under `∀`s (in binder
types or bodies) and `mdata` only: the shape of a recursor's minor premise types, where the
motives are applied to indices and a constructor application. -/
def Hd (K H : Nat) : Nat → Expr → Prop
  | k, .forallE _ t b _ _ => Hd K H k t ∧ Hd K H (k + 1) b
  | k, .mdata _ x _ => Hd K H k x
  | k, e => Site K H k e ∨ NoOcc K k e

theorem noOcc_of_er {K k : Nat} {e e' : Expr} (h : er e' = er e) (ho : NoOcc K k e) : NoOcc K k e' :=
  fun j hj => by rw [h]; exact ho j hj

theorem hd_of_noOcc {K H : Nat} : ∀ {k : Nat} {e : Expr}, NoOcc K k e → Hd K H k e
  | k, .forallE _ t b _ _, h => by
    refine ⟨hd_of_noOcc fun j hj => ?_, hd_of_noOcc fun j hj => ?_⟩
    · have := h j hj; simp only [er, Tm.occ, Bool.or_eq_false_iff] at this; exact this.1
    · have := h j hj; simp only [er, Tm.occ, Bool.or_eq_false_iff] at this
      rw [show k + 1 + j = k + j + 1 by omega]; exact this.2
  | k, .mdata _ x _, h => hd_of_noOcc (k := k) (e := x) fun j hj => by simpa [er] using h j hj
  | _, .bvar .., h | _, .fvar .., h | _, .mvar .., h | _, .sort .., h | _, .const .., h
  | _, .app .., h | _, .lam .., h | _, .letE .., h | _, .lit .., h | _, .proj .., h => by
    simp only [Hd]; exact .inr h

theorem hd_of_site {K H k : Nat} {e : Expr} (h : Site K H k e) : Hd K H k e := by
  cases e
  case forallE => obtain ⟨i, hi, hhd, -⟩ := h; simp [getAppFnArgs] at hhd
  case mdata => obtain ⟨i, hi, hhd, -⟩ := h; simp [getAppFnArgs] at hhd
  all_goals (simp only [Hd]; exact .inl h)

theorem noOcc_args {K k : Nat} {f₀ a₀ : Expr} {hh : Address} (h : NoOcc K k (.app f₀ a₀ hh)) :
    NoOcc K k (getAppFnArgs (.app f₀ a₀ hh)).1 ∧
      ∀ a ∈ (getAppFnArgs (.app f₀ a₀ hh)).2.toList, NoOcc K k a :=
  ⟨fun j hj => (occ_er_app_of (h j hj)).1, fun a ha j hj => (occ_er_app_of (h j hj)).2 a ha⟩

/-- Lowering by a substitution at `k` for a term without `bvar k … bvar (k+K)`. -/
theorem noOcc_lower {K k : Nat} {e r v : Expr} (hr : er r = Tm.inst (er v) k (er e))
    (ho : NoOcc (K + 1) k e) : NoOcc K k r := by
  intro j hj
  rw [hr, occ_inst_noocc _ _ _ _ (by simpa using ho 0 (by omega))]
  simp only [show ¬ (k + j < k) by omega, ↓reduceIte]
  rw [show k + j + 1 = k + (j + 1) by omega]; exact ho (j + 1) (by omega)

theorem occ_appN_head {h : Tm} {j : Nat} (hj : Tm.occ h j = true) : ∀ (as : List Tm),
    Tm.occ (Tm.appN h as) j = true
  | [] => hj
  | a :: as => by
    rw [Tm.appN_cons]
    exact occ_appN_head (h := .app h a) (by simp [Tm.occ, hj]) as

theorem occ_appN_of_mem {j : Nat} {a : Tm} (ha : Tm.occ a j = true) : ∀ (h : Tm) (as : List Tm),
    a ∈ as → Tm.occ (Tm.appN h as) j = true
  | h, b :: as, hm => by
    rw [Tm.appN_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · exact occ_appN_head (h := .app h a) (by simp [Tm.occ, ha]) as
    · exact occ_appN_of_mem ha (.app h b) as hm

theorem getAppFnArgs_foldl : ∀ (as : List Expr) (f : Expr),
    getAppFnArgs (as.foldl Expr.mkApp f) = ((getAppFnArgs f).1, (getAppFnArgs f).2 ++ as.toArray)
  | [], f => by simp
  | a :: as, f => by
    rw [List.foldl_cons, getAppFnArgs_foldl as (Expr.mkApp f a)]
    have : getAppFnArgs (Expr.mkApp f a) = ((getAppFnArgs f).1, (getAppFnArgs f).2.push a) := rfl
    rw [this]
    congr 1
    apply Array.toList_inj.1
    simp

theorem getAppFnArgs_mkAppN_bvar (i : Nat) (as : List Expr) :
    getAppFnArgs (mkAppN (Expr.mkBVar i) as.toArray) = (Expr.mkBVar i, as.toArray) := by
  simp only [mkAppN, ← Array.foldl_toList, getAppFnArgs_foldl]
  have : getAppFnArgs (Expr.mkBVar i) = (Expr.mkBVar i, #[]) := rfl
  rw [this]; simp

/-- The development at a variable of the window. -/
theorem hinstP_bvar_ge (v : Expr) (m k i : Nat) (hh : Address) (hik : k ≤ i) :
    hinstP (m + 1) v k (.bvar i hh) =
      .ok (if i = k then (liftP v k 0, .direct) else (Expr.mkBVar (i - 1), .no)) := by
  unfold hinstP
  have hr : ¬ looseRangeP (Expr.bvar i hh) ≤ k := by simp [looseRangeP]; omega
  simp only [hr, ↓reduceIte]
  by_cases h : i = k
  · subst h; simp; rfl
  · have hb : (i == k) = false := by simp [h]
    have hg : i > k := by omega
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hg, h]; rfl

/-- **A closed first-order value substituted at motive sites**: from fuel
`hgt e + hgt v + H + 1` on; each site is replaced by the value's head β at the site's arguments,
so the result is at most `hgt v + H` higher, the remaining variables `k+1 … k+K` (now
`k … k+K-1`) still occur at motive sites only, and no variable is created. -/
theorem hinstP_sites {v : Expr} (hc : looseRangeP v = 0) (hf : FOv (er v) 0 = true) (K H : Nat) :
    ∀ (m k : Nat) (e : Expr), Hd (K + 1) H k e → hgt e + hgt v + H + 1 ≤ m →
    ∃ r c, hinstP m v k e = .ok (r, c) ∧ hgt r ≤ hgt e + hgt v + H ∧ Hd K H k r ∧
      ∀ j, Tm.occ (er r) j = true → Tm.occ (er e) (if j < k then j else j + 1) = true
  | 0, _, e, _, h => absurd h (by omega)
  | m + 1, k, e, hd, hm => by
    have hvp := hgt_pos v
    have hlv : liftP v k 0 = v := by unfold liftP; split <;> simp_all
    have hvc : ∀ j, Tm.occ (er v) j = false := fun j =>
      Tm.occ_of_range_le _ _ (by rw [← looseRangeP_eq, hc]; omega)
    by_cases hr : looseRangeP e ≤ k
    · have hre : Tm.range (er e) ≤ k := by rw [← looseRangeP_eq]; exact hr
      refine ⟨e, .no, ?_, by omega, hd_of_noOcc fun j hj => Tm.occ_of_range_le _ _ (by omega),
        fun j hj => ?_⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rfl
      · have hjk : j < k := by
          by_contra hn
          rw [Tm.occ_of_range_le _ _ (by omega)] at hj; cases hj
        simpa [hjk] using hj
    -- the cases where `bvar k … bvar (k+K)` do not occur: a plain walk
    have plain : NoOcc (K + 1) k e →
        ∃ r c, hinstP (m + 1) v k e = .ok (r, c) ∧ hgt r ≤ hgt e + hgt v + H ∧ Hd K H k r ∧
          ∀ j, Tm.occ (er r) j = true → Tm.occ (er e) (if j < k then j else j + 1) = true := by
      intro ho
      have hk : Tm.occ (er e) k = false := by simpa using ho 0 (by omega)
      obtain ⟨r, c, h1, h2, -, -⟩ := hinstP_passive v (m + 1) k e (passive_of_noocc hk).1 (by omega)
      obtain ⟨h3, -⟩ := hinstP_noocc v (m + 1) k e r c h1 hk
      refine ⟨r, c, h1, by omega, hd_of_noOcc (noOcc_lower h2 ho), fun j hj => ?_⟩
      rw [h2, occ_inst_noocc _ _ _ _ hk] at hj; exact hj
    match e, hd, hm, hr with
    | .forallE nm t b bi hh, hd, hm, hr =>
      simp only [Hd] at hd
      have hm' : hgt t + 1 ≤ hgt (Expr.forallE nm t b bi hh) ∧
          hgt b + 1 ≤ hgt (Expr.forallE nm t b bi hh) := by simp [hgt]; omega
      obtain ⟨t0, ct, hNt, hT, hTd, hTo⟩ := hinstP_sites hc hf K H m k t hd.1 (by omega)
      obtain ⟨b0, cb, hNb, hB, hBd, hBo⟩ := hinstP_sites hc hf K H m (k + 1) b hd.2 (by omega)
      refine ⟨Expr.mkForallE nm t0 b0 bi, .no, ?_, ?_, ⟨hTd, hBd⟩, fun j hj => ?_⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNt, hNb]; rfl
      · simp only [hgt_mkForallE, hgt]; omega
      · simp only [er_mkForallE, Tm.occ, Bool.or_eq_true] at hj
        simp only [er, Tm.occ, Bool.or_eq_true]
        rcases hj with hj | hj
        · exact .inl (hTo j hj)
        · right
          have := hBo (j + 1) hj
          by_cases hjk : j < k
          · simpa [hjk, show j + 1 < k + 1 from by omega] using this
          · simpa [hjk, show ¬ (j + 1 < k + 1) from by omega] using this
    | .mdata md x hh, hd, hm, hr =>
      simp only [Hd] at hd
      obtain ⟨x0, cx, hNx, hX, hXd, hXo⟩ := hinstP_sites hc hf K H m k x hd (by simp [hgt] at hm; omega)
      refine ⟨Expr.mkMData md x0, cx, ?_, ?_, hXd, fun j hj => ?_⟩
      · unfold hinstP; simp only [hr, ↓reduceIte]; rw [hNx]; rfl
      · simp only [hgt_mkMData, hgt]; omega
      · simp only [er_mkMData, er] at hj ⊢; exact hXo j hj
    | .bvar i hh, hd, hm, hr =>
      simp only [Hd] at hd
      rcases hd with ⟨i', hi', hhd, hki, hiK, -, -⟩ | ho
      · have hhd' : Expr.bvar i hh = Expr.bvar i' hi' := hhd
        simp only [Expr.bvar.injEq] at hhd'
        obtain ⟨rfl, rfl⟩ := hhd'
        rw [hinstP_bvar_ge v m k i hh hki]
        by_cases hik : i = k
        · subst hik
          rw [show (if i = i then (liftP v i 0, Created.direct) else (Expr.mkBVar (i - 1), Created.no)) = (liftP v i 0, Created.direct) by simp, hlv]
          refine ⟨v, .direct, rfl, ?_, hd_of_noOcc fun j _ => hvc _, fun j hj => ?_⟩
          · simp only [hgt]; omega
          · rw [hvc] at hj; cases hj
        · rw [show (if i = k then (liftP v k 0, Created.direct) else (Expr.mkBVar (i - 1), Created.no)) = (Expr.mkBVar (i - 1), Created.no) by simp [hik]]
          have hga : getAppFnArgs (Expr.mkBVar (i - 1)) = (Expr.mkBVar (i - 1), #[]) := rfl
          refine ⟨_, _, rfl, by simp only [hgt_mkBVar, hgt]; omega, ?_, fun j hj => ?_⟩
          · exact hd_of_site ⟨i - 1, _, rfl, by omega, by omega, by simp [hga], by simp [hga, hsum]⟩
          · simp only [er_mkBVar, Tm.occ, beq_iff_eq] at hj
            subst hj
            simp only [er, Tm.occ, show ¬ (i - 1 < k) from by omega, ↓reduceIte, beq_iff_eq]
            omega
      · exact plain ho
    | .app f₀ a₀ hh, hd, hm, hr =>
      simp only [Hd] at hd
      rcases hd with ⟨i, hi, hhd, hki, hiK, hargs, hsum'⟩ | ho
      · -- a motive site
        have hsz := hgt_getAppFnArgs f₀ a₀ hh
        have hsp := er_getAppFnArgs (.app f₀ a₀ hh)
        obtain ⟨args0, hNa, hA⟩ := mapM_of_forall
          (f := fun a => Prod.fst <$> hinstP m v k a)
          (P := fun a r => er r = Tm.inst (er v) k (er a) ∧ hgt r = hgt a)
          (getAppFnArgs (.app f₀ a₀ hh)).2.toList (fun a ha => by
            have hk : Tm.occ (er a) k = false := by simpa using hargs a ha 0 (by omega)
            obtain ⟨r, c, h1, h2, -, -⟩ := hinstP_passive v m k a (passive_of_noocc hk).1
              (by have := hsz.2 a ha; omega)
            exact ⟨r, by rw [h1]; rfl, h2, (hinstP_noocc v m k a r c h1 hk).1⟩)
        have hmapA : args0.map er =
            (getAppFnArgs (.app f₀ a₀ hh)).2.toList.map (fun x => Tm.inst (er v) k (er x)) :=
          EForall2.map_eq (fun _ _ h => h.1) hA
        have hsumA : hsum args0 = hsum (getAppFnArgs (.app f₀ a₀ hh)).2.toList := by
          unfold hsum; congr 1; exact EForall2.map_eq (fun _ _ h => h.2) hA
        -- the arguments: no variable of the window, occurrences from the site
        have hoA : ∀ a ∈ args0, NoOcc K k a ∧ ∀ j, Tm.occ (er a) j = true →
            Tm.occ (er (Expr.app f₀ a₀ hh)) (if j < k then j else j + 1) = true := by
          intro a ha
          have hmem : er a ∈ args0.map er := List.mem_map.2 ⟨a, ha, rfl⟩
          rw [hmapA] at hmem
          obtain ⟨b, hb, hba⟩ := List.mem_map.1 hmem
          have hk : Tm.occ (er b) k = false := by simpa using hargs b hb 0 (by omega)
          refine ⟨fun j hj => ?_, fun j hj => ?_⟩
          · rw [← hba, occ_inst_noocc _ _ _ _ hk]
            simp only [show ¬ (k + j < k) by omega, ↓reduceIte]
            rw [show k + j + 1 = k + (j + 1) by omega]; exact hargs b hb (j + 1) (by omega)
          · rw [← hba, occ_inst_noocc _ _ _ _ hk] at hj
            rw [hsp]
            exact occ_appN_of_mem hj _ _ (List.mem_map.2 ⟨b, hb, rfl⟩)
        have hheadocc : Tm.occ (er (Expr.app f₀ a₀ hh)) i = true := by
          rw [hsp, hhd]; exact occ_appN_head (by simp [er, Tm.occ]) _
        have hNh : hinstP m v k (getAppFnArgs (.app f₀ a₀ hh)).1 =
            .ok (if i = k then (v, .direct) else (Expr.mkBVar (i - 1), .no)) := by
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hgt_pos f₀; simp [hgt] at hm; omega⟩
          rw [hhd, hinstP_bvar_ge v m' k i hi hki, hlv]
        have run : ∀ R, (match (generalizing := false)
            (if i = k then (v, Created.direct) else (Expr.mkBVar (i - 1), Created.no)).2,
            (if i = k then (v, Created.direct) else (Expr.mkBVar (i - 1), Created.no)).1 with
            | .no, _ => pure (mkAppN (if i = k then (v, Created.direct) else (Expr.mkBVar (i - 1), Created.no)).1 args0.toArray, Created.no)
            | _, .lam .. => do pure ((← happP m (if i = k then (v, Created.direct) else (Expr.mkBVar (i - 1), Created.no)).1 args0), Created.reduced)
            | c, _ => pure (mkAppN (if i = k then (v, Created.direct) else (Expr.mkBVar (i - 1), Created.no)).1 args0.toArray, c)) =
              (Except.ok R : Except String (Expr × Created)) →
            hinstP (m + 1) v k (.app f₀ a₀ hh) = .ok R := by
          intro R hR
          unfold hinstP
          simp only [hr, ↓reduceIte]
          rw [hNa, hNh]
          exact hR
        have hHH : hgt v + H + 1 ≤ m := by have := hgt_pos (Expr.app f₀ a₀ hh); omega
        by_cases hik : i = k
        · subst hik
          simp only [↓reduceIte] at run
          by_cases hl : ∃ n t b bi hh', v = Expr.lam n t b bi hh'
          · obtain ⟨r, h1, h2, h3⟩ := happP_passive args0 v m hf (by omega)
            refine ⟨r, .reduced, run _ ?_, by omega, hd_of_noOcc fun j hj => ?_, fun j hj => ?_⟩
            · obtain ⟨n, t, b, bi, hh', hv⟩ := hl
              revert h1; rw [hv]; intro h1
              show (do pure ((← happP m _ args0), Created.reduced)) = _
              rw [h1]; rfl
            · cases hrj : Tm.occ (er r) (i + j)
              · rfl
              · rcases h3 _ hrj with h | ⟨a, ha, h⟩
                · rw [hvc] at h; cases h
                · rw [(hoA a ha).1 j hj] at h; cases h
            · rcases h3 j hj with h | ⟨a, ha, h⟩
              · rw [hvc] at h; cases h
              · exact (hoA a ha).2 j h
          · refine ⟨mkAppN v args0.toArray, .direct, run _ ?_, ?_, hd_of_noOcc fun j hj => ?_,
              fun j hj => ?_⟩
            · cases v with
              | lam n t b bi hh' => exact absurd ⟨n, t, b, bi, hh', rfl⟩ hl
              | _ => rfl
            · have := hgt_mkAppN_le v args0; omega
            · cases hrj : Tm.occ (er (mkAppN v args0.toArray)) (i + j)
              · rfl
              · rw [mkAppN_toList] at hrj
                rcases occ_appN_or hrj with h | ⟨a, ha, h⟩
                · rw [hvc] at h; cases h
                · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
                  rw [(hoA a' ha').1 j hj] at h; cases h
            · rw [mkAppN_toList] at hj
              rcases occ_appN_or hj with h | ⟨a, ha, h⟩
              · rw [hvc] at h; cases h
              · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
                exact (hoA a' ha').2 j h
        · simp only [hik, ↓reduceIte] at run
          refine ⟨mkAppN (Expr.mkBVar (i - 1)) args0.toArray, .no, run _ rfl, ?_, ?_, fun j hj => ?_⟩
          · rw [← hgt_getAppFnArgs_eq (.app f₀ a₀ hh), hgt_mkAppN, hgt_mkAppN, List.toList_toArray,
              hhd]
            rw [foldl_hgt_eq _ _ _ (EForall2.imp (fun _ _ h => h.2) hA)]
            simp [hgt]; omega
          · refine hd_of_site ⟨i - 1, _, by rw [getAppFnArgs_mkAppN_bvar]; rfl, by omega, by omega,
              fun a ha => ?_, ?_⟩
            · rw [getAppFnArgs_mkAppN_bvar] at ha; exact (hoA a (by simpa using ha)).1
            · rw [getAppFnArgs_mkAppN_bvar, List.toList_toArray, hsumA]; exact hsum'
          · rw [mkAppN_toList] at hj
            rcases occ_appN_or hj with h | ⟨a, ha, h⟩
            · simp only [er_mkBVar, Tm.occ, beq_iff_eq] at h
              subst h
              simp only [show ¬ (i - 1 < k) from by omega, ↓reduceIte, show i - 1 + 1 = i by omega]
              exact hheadocc
            · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
              exact (hoA a' ha').2 j h
      · exact plain ho
    | .fvar .., hd, hm, hr | .mvar .., hd, hm, hr | .sort .., hd, hm, hr | .const .., hd, hm, hr
    | .lam .., hd, hm, hr | .letE .., hd, hm, hr | .lit .., hd, hm, hr | .proj .., hd, hm, hr =>
      simp only [Hd] at hd
      rcases hd with ⟨i, hi, hhd, -⟩ | ho
      · simp [getAppFnArgs] at hhd
      · exact plain ho

/-! ## Sequential substitutions (`substFVars`) -/

/-- The fold `substFVars` runs: the values substituted one by one at `bvar 0`, the last first. -/
def substChain (F : Nat) (L : List Expr) (acc : Expr) : Except String Expr :=
  L.foldlM (fun acc v => Prod.fst <$> hinstP F v 0 acc) acc

theorem substFVarsP_eq (xs : Array Name) (vs : Array Expr) (e : Expr) (h : xs.size = vs.size) :
    substFVarsP xs vs e =
      substChain Ix.Compile.Image.defaultFuel vs.toList.reverse
        (Ix.Compile.Image.abstractFVars xs e) := by
  unfold substFVarsP substChain
  simp [h]

/-- **Motive sites, all motives in turn** (P3a's minor types): closed first-order values
substituted at `K` motive variables succeed from fuel `hgt acc + K · (V + H) + 1` on (`V` bounds
the values' heights, `H` the sites' arguments). -/
theorem substChain_sites (H V : Nat) : ∀ (L : List Expr) (acc : Expr) (F : Nat),
    (∀ v ∈ L, looseRangeP v = 0 ∧ FOv (er v) 0 = true ∧ hgt v ≤ V) → Hd L.length H 0 acc →
    hgt acc + L.length * (V + H) + 1 ≤ F →
    ∃ r, substChain F L acc = .ok r ∧ hgt r ≤ hgt acc + L.length * (V + H)
  | [], acc, F, _, _, _ => ⟨acc, rfl, by simp⟩
  | v :: L, acc, F, hv, hd, hF => by
    obtain ⟨hc, hf, hV⟩ := hv v List.mem_cons_self
    simp only [List.length_cons] at hd hF
    obtain ⟨r, c, h1, h2, h3, -⟩ := hinstP_sites hc hf L.length H F 0 acc hd
      (by rw [Nat.add_mul] at hF; omega)
    obtain ⟨r', h4, h5⟩ := substChain_sites H V L r F (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      h3 (by rw [Nat.add_mul] at hF; omega)
    refine ⟨r', ?_, by simp only [List.length_cons, Nat.add_mul] at h5 ⊢; omega⟩
    unfold substChain at h4 ⊢
    rw [List.foldlM_cons, h1]
    exact h4

theorem act_inst_above (v : Tm) (hv : Tm.range v = 0) : ∀ (t : Tm) (j k : Nat),
    Act (j + k) (Tm.inst v k t) = Act (j + k + 1) t
  | .bvar i, j, k => by
    simp only [Tm.inst]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, Tm.lift_of_range_le _ _ _ (by omega : Tm.range v ≤ 0)]
      have h1 : Act (j + i) v = false := by
        cases ha : Act (j + i) v
        · rfl
        · have := act_occ ha; rw [Tm.occ_of_range_le _ _ (by omega)] at this; cases this
      rw [h1]; simp [Act]; omega
    · simp only [hik, ↓reduceIte, Act]
      rw [Bool.eq_iff_iff]
      by_cases hki : k < i <;> simp [hki] <;> omega
  | .app f x, j, k => by simp only [Tm.inst, Act, act_inst_above v hv f j k]
  | .proj _ _ x, j, k => by simp only [Tm.inst, Act, act_inst_above v hv x j k]
  | .lam t b, j, k => by
    simp only [Tm.inst, Act]
    rw [show j + k + 1 = j + (k + 1) by omega, act_inst_above v hv b j (k + 1)]
  | .pi _ _, _, _ | .letE _ _ _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _
  | .const _ _, _, _ | .lit _, _, _ => rfl

theorem passive_inst_above (v : Tm) (hv : Tm.range v = 0) : ∀ (t : Tm) (j k : Nat),
    Passive (j + k) (Tm.inst v k t) = Passive (j + k + 1) t ∧
      PassiveF (j + k) (Tm.inst v k t) = PassiveF (j + k + 1) t
  | .bvar i, j, k => by
    simp only [Tm.inst]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, Tm.lift_of_range_le _ _ _ (by omega : Tm.range v ≤ 0)]
      have := passive_of_noocc (j := j + i) (t := v) (Tm.occ_of_range_le _ _ (by omega))
      rw [this.1, this.2]; simp [Passive, PassiveF]; omega
    · simp only [hik, ↓reduceIte, Passive, PassiveF, true_and]
      rw [Bool.eq_iff_iff]
      by_cases hki : k < i <;> simp [hki] <;> omega
  | .app f x, j, k => by
    have h1 := passive_inst_above v hv f j k
    have h2 := passive_inst_above v hv x j k
    simp only [Tm.inst, Passive, PassiveF, h1.2, h2.1, and_self]
  | .lam t b, j, k => by
    have h1 := passive_inst_above v hv t j k
    have h2 := passive_inst_above v hv b j (k + 1)
    have h3 := act_inst_above v hv b j (k + 1)
    simp only [Tm.inst, Passive, PassiveF, h1.1]
    rw [show j + k + 1 = j + (k + 1) by omega, h2.1, h3]
    simp only [show j + (k + 1) + 1 = j + k + 1 + 1 by omega, and_self]
  | .pi t b, j, k => by
    have h1 := passive_inst_above v hv t j k
    have h2 := passive_inst_above v hv b j (k + 1)
    simp only [Tm.inst, Passive, PassiveF, h1.1]
    rw [show j + k + 1 = j + (k + 1) by omega, h2.1]
    simp only [show j + (k + 1) + 1 = j + k + 1 + 1 by omega, and_self]
  | .letE t w b, j, k => by
    have h1 := passive_inst_above v hv t j k
    have h3 := passive_inst_above v hv w j k
    have h2 := passive_inst_above v hv b j (k + 1)
    simp only [Tm.inst, Passive, PassiveF, h1.1, h3.1]
    rw [show j + k + 1 = j + (k + 1) by omega, h2.1]
    simp only [show j + (k + 1) + 1 = j + k + 1 + 1 by omega, and_self]
  | .proj s i x, j, k => by
    have h1 := passive_inst_above v hv x j k
    simp only [Tm.inst, Passive, PassiveF, h1.1, act_inst_above v hv x j k, and_self]
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => ⟨rfl, rfl⟩

/-- **Passive variables, all in turn** (P3a's rule types): closed values substituted for `n`
variables passive in `acc` succeed from fuel `hgt acc + Σ hgt values` on, as the plain
substitution. -/
theorem substChain_passive : ∀ (L : List Expr) (acc : Expr) (F : Nat),
    (∀ v ∈ L, looseRangeP v = 0) → (∀ j < L.length, Passive j (er acc) = true) →
    hgt acc + hsum L ≤ F → ∃ r, substChain F L acc = .ok r ∧ hgt r ≤ hgt acc + hsum L
  | [], acc, F, _, _, _ => ⟨acc, rfl, by simp [hsum]⟩
  | v :: L, acc, F, hv, hp, hF => by
    have hc := hv v List.mem_cons_self
    have hr : Tm.range (er v) = 0 := by rw [← looseRangeP_eq]; exact hc
    simp only [List.length_cons, hsum_cons] at hp hF ⊢
    obtain ⟨r, c, h1, h2, h3, -⟩ := hinstP_passive v F 0 acc (hp 0 (by omega))
      (by have := hgt_pos v; omega)
    have hp' : ∀ j < L.length, Passive j (er r) = true := by
      intro j hj
      rw [h2]
      have := (passive_inst_above (er v) hr (er acc) j 0).1
      simp only [Nat.add_zero] at this
      rw [this]; exact hp (j + 1) (by omega)
    obtain ⟨r', h4, h5⟩ := substChain_passive L r F (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      hp' (by omega)
    refine ⟨r', ?_, by omega⟩
    unfold substChain at h4 ⊢
    rw [List.foldlM_cons, h1]
    exact h4

/-- **Inert arguments at a call site** (P3a's rule right-hand sides), at the executable's fuel. -/
theorem instantiateP_inert {f : Expr} {args : Array Expr} (ha : ∀ a ∈ args.toList, TmInert (er a))
    (hF : hgt f + hsum args.toList + 1 ≤ Ix.Compile.Image.defaultFuel) :
    ∃ r, instantiateP f args = .ok r ∧ hgt r ≤ hgt f + hsum args.toList :=
  happP_inert args.toList f _ ha hF

/-- `abstractFVars` keeps heights. -/
theorem hgt_abstractFVars_go (xs : Array Name) : ∀ (e : Expr) (d : Nat),
    hgt (Ix.Compile.Image.abstractFVars.go xs e d) = hgt e
  | .fvar n h, d => by
    simp only [Ix.Compile.Image.abstractFVars.go]
    cases xs.idxOf? n <;> rfl
  | .app f a _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, hgt_mkApp, hgt, hgt_abstractFVars_go xs f d,
      hgt_abstractFVars_go xs a d]
  | .lam _ t b _ _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, hgt_mkLam, hgt, hgt_abstractFVars_go xs t d,
      hgt_abstractFVars_go xs b (d + 1)]
  | .forallE _ t b _ _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, hgt_mkForallE, hgt, hgt_abstractFVars_go xs t d,
      hgt_abstractFVars_go xs b (d + 1)]
  | .letE _ t v b _ _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, hgt_mkLetE, hgt, hgt_abstractFVars_go xs t d,
      hgt_abstractFVars_go xs v d, hgt_abstractFVars_go xs b (d + 1)]
  | .proj _ _ s _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, hgt_mkProj, hgt, hgt_abstractFVars_go xs s d]
  | .mdata _ x _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, hgt_mkMData, hgt, hgt_abstractFVars_go xs x d]
  | .bvar .., _ | .mvar .., _ | .sort .., _ | .const .., _ | .lit .., _ => rfl

theorem hgt_abstractFVars (xs : Array Name) (e : Expr) :
    hgt (Ix.Compile.Image.abstractFVars xs e) = hgt e := by
  unfold Ix.Compile.Image.abstractFVars
  split
  · rfl
  · exact hgt_abstractFVars_go xs e 0

end Ix.CompileCert.Img
