import Ix.CompileCert.Conv.Core

/-!
# M7 X1: the development lemma

**The developed term is convertible to the plain substitution** (design document §4.3, the
docstring of `Ix/Compile/Image/Develop.lean`: "contracts exactly the redexes that the
substitution forms at the substituted positions"):

* `hinstP_conv`: `hinstP fuel v k e = .ok (r, c) → Conv Γ (er r) (Tm.inst (er v) k (er e))`;
* `happP_conv`: `happP fuel f args = .ok r → Conv Γ (er r) (Tm.appN (er f) (args.map er))`;
* `instantiateP_conv`: the call-site development `instantiateP f args` is convertible to the
  application `f args`;
* `inline_conv`: with the environment's δ-rule for the image constant `n`
  (`Γ.ax (.const n us) (er (substLevels lps us val))`), the inlined occurrence is convertible to
  the occurrence `n.{us} args` itself: the inline rewrite is δ followed by the development
  (§4.5, Def 3.6).

No hypothesis on `Γ` is needed for the development itself: its steps are β, η and the
projection of a pair, and the theorems hold in every environment. Nothing is assumed about the
fuel: an exhausted fuel is an error, never a result.
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)
open Ix.Compile.Image (Created projCtor?)

/-! ## `Except` plumbing -/

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem map_ok {α β : Type} {x : Except String α} {g : α → β} {b : β}
    (h : (g <$> x) = .ok b) : ∃ a, x = .ok a ∧ g a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

theorem pure_ok {α : Type} {a b : α} (h : (pure a : Except String α) = .ok b) : a = b := by
  cases h; rfl

theorem hinstP_zero (v : Expr) (k : Nat) (e : Expr) :
    hinstP 0 v k e = .error "development: out of fuel" := by rw [hinstP]; rfl

theorem happP_zero (f : Expr) (args : List Expr) :
    happP 0 f args = .error "development: out of fuel" := by rw [happP]; rfl

theorem happP_succ (fuel : Nat) (f : Expr) (args : List Expr) : happP (fuel + 1) f args =
    match f, args with
    | .lam _ _ b _ _, a :: rest => do
      let (b', _) ← hinstP fuel a 0 b
      happP fuel b' rest
    | f, args => pure (mkAppN f args.toArray) := by
  cases f <;> cases args <;> rfl

/-- The arguments of a spine, each developed. -/
theorem forall2_of_mapM (Γ : Env) {fuel : Nat}
    (IH : ∀ v k e r c, hinstP fuel v k e = .ok (r, c) → Conv Γ (er r) (Tm.inst (er v) k (er e)))
    {v : Expr} {k : Nat} : ∀ {l l' : List Expr},
    EForall2 (fun a b => (Prod.fst <$> hinstP fuel v k a) = .ok b) l l' →
      Forall2 (Conv Γ) (l'.map er) (l.map fun a => Tm.inst (er v) k (er a))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab hs => by
    obtain ⟨⟨b', cb⟩, hb, rfl⟩ := map_ok hab
    exact .cons (IH _ _ _ _ _ hb) (forall2_of_mapM Γ IH hs)

/-! ## The lemma -/

/-- **The development lemma**, for `hinstP` and `happP` at every fuel. -/
theorem develop_conv (Γ : Env) : ∀ fuel : Nat,
    (∀ v k e r c, hinstP fuel v k e = .ok (r, c) → Conv Γ (er r) (Tm.inst (er v) k (er e))) ∧
    (∀ f args r, happP fuel f args = .ok r → Conv Γ (er r) (Tm.appN (er f) (args.map er)))
  | 0 => ⟨fun v k e r c h => (by rw [hinstP_zero] at h; cases h),
          fun f args r h => (by rw [happP_zero] at h; cases h)⟩
  | fuel + 1 => by
    have IH := develop_conv Γ fuel
    refine ⟨fun v k e r c h => ?_, fun f args r h => ?_⟩
    · unfold hinstP at h
      by_cases hr : looseRangeP e ≤ k
      · simp only [hr, ↓reduceIte] at h
        cases pure_ok h
        rw [Tm.inst_of_range_le _ _ _ (by rw [← looseRangeP_eq]; exact hr)]
        exact .refl _
      simp only [hr, ↓reduceIte] at h
      match e, h with
      | .bvar i _, h =>
        by_cases hik : i = k
        · subst hik
          simp only [beq_self_eq_true, ↓reduceIte] at h
          cases pure_ok h
          simp only [er_liftP, er, Tm.inst, ↓reduceIte]; exact .refl _
        · have hik' : (i == k) = false := by simp [hik]
          simp only [hik', Bool.false_eq_true, ↓reduceIte] at h
          by_cases hgt : i > k
          · simp only [hgt, ↓reduceIte] at h
            cases pure_ok h
            simp only [er, er_mkBVar, Tm.inst, hik, ↓reduceIte, show k < i from hgt]
            exact .refl _
          · simp only [hgt, ↓reduceIte] at h
            cases pure_ok h
            simp only [er, Tm.inst, hik, ↓reduceIte, show ¬ k < i from hgt]
            exact .refl _
      | .app f₀ a₀ hh, h =>
        obtain ⟨args', hargs, h⟩ := bind_ok h
        obtain ⟨⟨h', c'⟩, hh', h⟩ := bind_ok h
        have hmap := mapM_ok hargs
        have hcargs := forall2_of_mapM Γ IH.1 hmap
        have key : Conv Γ (Tm.appN (er h') (args'.map er)) (Tm.inst (er v) k (er (.app f₀ a₀ hh))) := by
          rw [er_getAppFnArgs (.app f₀ a₀ hh), Tm.inst_appN, List.map_map]
          exact Conv.appN (IH.1 _ _ _ _ _ hh') hcargs
        dsimp only at h
        split at h
        · cases pure_ok h
          rw [er_mkAppN, List.toList_toArray]; exact key
        · obtain ⟨r', hr', h⟩ := bind_ok h
          cases pure_ok h
          exact .trans (IH.2 _ _ _ hr') key
        · cases pure_ok h
          rw [er_mkAppN, List.toList_toArray]; exact key
      | .proj s i x hh, h =>
        obtain ⟨⟨x', c'⟩, hx, h⟩ := bind_ok h
        have hcx : Conv Γ (.proj s i (er x')) (Tm.inst (er v) k (er (.proj s i x hh))) := by
          simp only [er, Tm.inst]; exact .proj s i (IH.1 _ _ _ _ _ hx)
        dsimp only at h
        split at h
        · cases pure_ok h; exact hcx
        · split at h
          · rename_i f hf
            cases pure_ok h
            obtain ⟨cc, us, α, β, a, b, hex, hp, hfi⟩ := projCtor?_spec hf
            rw [hex] at hcx
            rcases hfi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact .trans (.symm (.step (.proj0 s cc us _ _ _ _ hp))) hcx
            · exact .trans (.symm (.step (.proj1 s cc us _ _ _ _ hp))) hcx
          · cases pure_ok h; exact hcx
      | .lam n t b bi hh, h =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        have hcl : Conv Γ (.lam (er t') (er b')) (Tm.inst (er v) k (er (.lam n t b bi hh))) := by
          simp only [er, Tm.inst]; exact .lam (IH.1 _ _ _ _ _ ht) (IH.1 _ _ _ _ _ hb)
        dsimp only at h
        split at h
        · rename_i f hb0 hf0
          split at h
          · rename_i hocc
            cases pure_ok h
            have hocc' : Tm.occ (er f) 0 = false := by
              rw [← occursP_eq]; simpa using hocc
            rw [er_lowerP]
            refine .trans (.symm (.step (.eta (er t') (er f) hocc'))) ?_
            simp only [er] at hcl; exact hcl
          · cases pure_ok h; exact hcl
        · cases pure_ok h; exact hcl
      | .forallE n t b bi hh, h =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        simp only [er_mkForallE, er, Tm.inst]; exact .pi (IH.1 _ _ _ _ _ ht) (IH.1 _ _ _ _ _ hb)
      | .letE n t x b nd hh, h =>
        obtain ⟨⟨t', ct⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        cases pure_ok h
        simp only [er_mkLetE, er, Tm.inst]
        exact .letE (IH.1 _ _ _ _ _ ht) (IH.1 _ _ _ _ _ hx) (IH.1 _ _ _ _ _ hb)
      | .mdata md x hh, h =>
        obtain ⟨⟨x', cx⟩, hx, h⟩ := bind_ok h
        cases pure_ok h
        simp only [er_mkMData, er]; exact IH.1 _ _ _ _ _ hx
      | .fvar .., h | .mvar .., h | .sort .., h | .const .., h | .lit .., h =>
        cases pure_ok h; exact .refl _
    · rw [happP_succ] at h
      split at h
      · rename_i b a rest
        obtain ⟨⟨b', cb⟩, hb, h⟩ := bind_ok h
        have h1 := IH.2 _ _ _ h
        have h2 := IH.1 _ _ _ _ _ hb
        refine .trans h1 ?_
        simp only [List.map_cons, er]
        exact .trans (Conv.appN h2 (Conv.forall₂_refl _)) (.symm (Conv.beta_appN _ _ _ _))
      · cases pure_ok h
        rw [er_mkAppN, List.toList_toArray]; exact .refl _

theorem hinstP_conv (Γ : Env) {fuel : Nat} {v : Expr} {k : Nat} {e r : Expr} {c : Created}
    (h : hinstP fuel v k e = .ok (r, c)) : Conv Γ (er r) (Tm.inst (er v) k (er e)) :=
  (develop_conv Γ fuel).1 v k e r c h

theorem happP_conv (Γ : Env) {fuel : Nat} {f : Expr} {args : List Expr} {r : Expr}
    (h : happP fuel f args = .ok r) : Conv Γ (er r) (Tm.appN (er f) (args.map er)) :=
  (develop_conv Γ fuel).2 f args r h

/-- **The call-site development is a conversion** of the application. -/
theorem instantiateP_conv (Γ : Env) {f : Expr} {args : Array Expr} {r : Expr}
    (h : instantiateP f args = .ok r) : ExprConv Γ r (mkAppN f args) := by
  unfold ExprConv; rw [er_mkAppN]; exact happP_conv Γ h

/-- **The inline rewrite is δ then the development** (§4.5, Def 3.6): with the environment's
δ-rule for the image constant `n` at the levels `us`, the inlined occurrence is convertible to
the occurrence. -/
theorem inline_conv (Γ : Env) {n : Name} {lps : Array Name} {val : Expr} {us : Array Level}
    {args : Array Expr} {r : Expr} (hδ : Γ.ax (.const n us) (er (substLevels lps us val)))
    (h : instantiateP (substLevels lps us val) args = .ok r) :
    ExprConv Γ r (mkAppN (Expr.mkConst n us) args) := by
  have := instantiateP_conv Γ h
  unfold ExprConv at this ⊢
  rw [er_mkAppN] at this ⊢
  exact .trans this (Conv.appN (.symm (.step (.ax hδ))) (Conv.forall₂_refl _))

end Ix.CompileCert.Conv
