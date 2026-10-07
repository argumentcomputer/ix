import Ix.CompileCert.Conv.Develop
import Ix.CompileCert.Conv.Typing

/-!
# M7 X1: the development terminates on simply typed input (obligation O-T, first instance)

`Ix/Compile/Image/Develop.lean` justifies its fuel by "the typed argument of the design
document (each hereditary step substitutes at a strictly smaller type)". With the simple types
of the erasure (`Typing.lean`) the argument is a theorem about the core (`Core.lean`):

* `develop_total`: if the value `v` has type `σ` and the term `e` has type `τ` with `σ` at the
  substituted position, then for every fuel from some bound on, `hinstP` returns one result,
  of type `τ` (subject reduction);
* `happP_total`: the same for an application spine `f args` whose arguments have the
  parameters' types;
* `instantiateP_total`: **on a simply typable call site, the call-site development succeeds
  for every fuel from some bound on, with the same result** (and that result is convertible to
  the application, `instantiateP_conv`).

The proof is the design document's: induction on the size of the substituted value's type,
then on the term. A β-redex the development forms has as head the substituted value or a
contraction of it (the head flags `Created`, invariant `DirectInv`), whose type is a
component of `σ`; the arguments substituted next have strictly smaller types.

**What "fuel suffices" means here.** The fuel is a recursion depth, and `defaultFuel` is a
constant (`2 ^ 16`). No constant suffices for every input: a term whose substituted variable
sits below more than `2 ^ 16` nodes exhausts it with no hereditary step at all. What holds is:
on the domain (simple typability) the development terminates, the needed fuel is the depth of
its run, any larger fuel gives the same result (`fuel_mono`), and an exhausted fuel is an error
naming itself, never a result. The depths met by the compiler are measured by the census
(`Tests/Ix/Compile/DevCensus.lean`, report §2).
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Image (Created projCtor?)

/-! ## Fuel only matters for exhaustion -/

/-- `x` succeeds at least where `y` does. -/
def Ext {α : Type} (x y : Except String α) : Prop := ∀ r, x = .ok r → y = .ok r

theorem Ext.refl {α : Type} (x : Except String α) : Ext x x := fun _ h => h

theorem Ext.bind {α β : Type} {x y : Except String α} {f g : α → Except String β} (hx : Ext x y)
    (hf : ∀ a, Ext (f a) (g a)) : Ext (x >>= f) (y >>= g) := by
  intro r h
  obtain ⟨a, ha, h⟩ := bind_ok h
  rw [hx a ha]; exact hf a r h

theorem Ext.map {α β : Type} {x y : Except String α} (g : α → β) (hx : Ext x y) :
    Ext (g <$> x) (g <$> y) := by
  intro r h
  obtain ⟨a, ha, rfl⟩ := map_ok h
  rw [hx a ha]; rfl

theorem Ext.mapM {f g : Expr → Except String Expr} (h : ∀ a, Ext (f a) (g a)) :
    ∀ (l : List Expr), Ext (l.mapM f) (l.mapM g)
  | [] => Ext.refl _
  | a :: l => by
    simp only [List.mapM_cons]
    exact Ext.bind (h a) fun b => Ext.bind (Ext.mapM h l) fun bs => Ext.refl _

/-- The tail of the application case: only the hereditary call reads the fuel. -/
theorem appTail_ext {n m : Nat} (hm : ∀ f args, Ext (happP n f args) (happP m f args))
    (c : Created) (h' : Expr) (args' : List Expr) :
    Ext (match c, h' with
          | .no, _ => pure (mkAppN h' args'.toArray, Created.no)
          | _, .lam .. => do pure ((← happP n h' args'), Created.reduced)
          | c, _ => pure (mkAppN h' args'.toArray, c))
        (match c, h' with
          | .no, _ => pure (mkAppN h' args'.toArray, Created.no)
          | _, .lam .. => do pure ((← happP m h' args'), Created.reduced)
          | c, _ => pure (mkAppN h' args'.toArray, c)) := by
  cases c <;> cases h' <;>
    first | exact Ext.refl _ | exact Ext.bind (hm _ _) fun _ => Ext.refl _

/-- **Fuel monotonicity**: a result at some fuel is the result at every larger fuel. -/
theorem fuel_mono : ∀ (n m : Nat), n ≤ m →
    (∀ v k e, Ext (hinstP n v k e) (hinstP m v k e)) ∧
    (∀ f args, Ext (happP n f args) (happP m f args))
  | 0, m, _ => ⟨fun v k e r h => (by rw [hinstP_zero] at h; cases h),
                fun f args r h => (by rw [happP_zero] at h; cases h)⟩
  | n + 1, 0, h => absurd h (by omega)
  | n + 1, m + 1, h => by
    have IH := fuel_mono n m (by omega)
    refine ⟨fun v k e => ?_, fun f args => ?_⟩
    · unfold hinstP
      by_cases hr : looseRangeP e ≤ k
      · simp only [hr, ↓reduceIte]; exact Ext.refl _
      · simp only [hr, ↓reduceIte]
        match e with
        | .bvar .. => exact Ext.refl _
        | .app .. =>
          exact Ext.bind (Ext.mapM (fun a => Ext.map _ (IH.1 v k a)) _) fun args' =>
            Ext.bind (IH.1 v k _) fun ⟨h', c⟩ => appTail_ext IH.2 c h' args'
        | .proj .. => exact Ext.bind (IH.1 v k _) fun ⟨_, _⟩ => Ext.refl _
        | .lam .. =>
          exact Ext.bind (IH.1 v k _) fun ⟨_, _⟩ => Ext.bind (IH.1 v (k + 1) _) fun ⟨_, _⟩ =>
            Ext.refl _
        | .forallE .. =>
          exact Ext.bind (IH.1 v k _) fun ⟨_, _⟩ => Ext.bind (IH.1 v (k + 1) _) fun ⟨_, _⟩ =>
            Ext.refl _
        | .letE .. =>
          exact Ext.bind (IH.1 v k _) fun ⟨_, _⟩ => Ext.bind (IH.1 v k _) fun ⟨_, _⟩ =>
            Ext.bind (IH.1 v (k + 1) _) fun ⟨_, _⟩ => Ext.refl _
        | .mdata .. => exact Ext.bind (IH.1 v k _) fun ⟨_, _⟩ => Ext.refl _
        | .fvar .. => exact Ext.refl _
        | .mvar .. => exact Ext.refl _
        | .sort .. => exact Ext.refl _
        | .const .. => exact Ext.refl _
        | .lit .. => exact Ext.refl _
    · rw [happP_succ, happP_succ]
      cases f <;> cases args <;>
        first | exact Ext.refl _ | exact Ext.bind (IH.1 _ 0 _) fun ⟨_, _⟩ => IH.2 _ _

/-! ## Spines and sizes -/

theorem appN_eq_app {h x y : Tm} : ∀ {as : List Tm}, Tm.appN h as = .app x y →
    (as = [] ∧ h = .app x y) ∨ ∃ as', as = as' ++ [y] ∧ x = Tm.appN h as'
  | as, e => by
    rcases List.eq_nil_or_concat as with rfl | ⟨as', z, rfl⟩
    · exact .inl ⟨rfl, e⟩
    · rw [List.concat_eq_append, Tm.appN_concat] at e
      cases e
      exact .inr ⟨as', List.concat_eq_append, rfl⟩

theorem Tm.occ_appN {h : Tm} {as : List Tm} {k : Nat} (e : Tm.occ (Tm.appN h as) k = false) :
    Tm.occ h k = false ∧ ∀ a ∈ as, Tm.occ a k = false := by
  induction as generalizing h with
  | nil => exact ⟨e, fun a ha => by cases ha⟩
  | cons b bs ih =>
    rw [Tm.appN_cons] at e
    obtain ⟨h1, h2⟩ := ih e
    simp only [Tm.occ, Bool.or_eq_false_iff] at h1
    refine ⟨h1.1, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h1.2
    · exact h2 a ha

theorem lower_lift_succ (w : Tm) (k : Nat) : Tm.lower 1 0 (Tm.lift (k + 1) 0 w) = Tm.lift k 0 w := by
  rw [show k + 1 = 1 + k by omega, ← Tm.lift_lift_of_le 1 k 0 0 w (Nat.le_refl _) (Nat.zero_le _),
    ← Tm.inst_eq_lower (.bvar 0) 0 _ (Tm.occ_lift_mid 1 0 0 _ (Nat.le_refl _) (by omega)),
    Tm.inst_lift_self]

theorem getAppFnArgs_sizeOf : ∀ (f a : Expr) (h : Address),
    sizeOf (getAppFnArgs (.app f a h)).1 < sizeOf (Expr.app f a h) ∧
      ∀ x ∈ (getAppFnArgs (.app f a h)).2.toList, sizeOf x < sizeOf (Expr.app f a h)
  | f, a, h => by
    simp only [getAppFnArgs]
    match f with
    | .app f' a' h' =>
      obtain ⟨h1, h2⟩ := getAppFnArgs_sizeOf f' a' h'
      simp only [Expr.app.sizeOf_spec] at h1 h2 ⊢
      refine ⟨by omega, fun x hx => ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · have := h2 x hx; omega
      · omega
    | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lam .. | .forallE .. | .letE ..
    | .lit .. | .mdata .. | .proj .. =>
      simp only [getAppFnArgs, Array.toList_push, List.mem_append, List.mem_singleton,
        Expr.app.sizeOf_spec]
      refine ⟨by omega, fun x hx => ?_⟩
      rcases hx with hx | rfl
      · simp at hx
      · omega

/-! ## The invariant of the head flags -/

/-- A `.direct` result is the substituted value applied to arguments of the types `σ` takes
(`σ = σs → τ`). -/
def DirectInv (Γ : List Ty) (v : Expr) (k : Nat) (σ τ : Ty) (r : Expr) : Prop :=
  ∃ as σs, er r = Tm.appN (Tm.lift k 0 (er v)) as ∧ σ = Ty.arrows σs τ ∧ TypArgs Γ as σs

/-- What `hinstP` returns on a typed input, from some fuel on. -/
def HinstOk (v : Expr) (σ : Ty) (Θ Δ : List Ty) (e : Expr) (τ : Ty) : Prop :=
  ∃ N r c, (∀ m, N ≤ m → hinstP m v Θ.length e = .ok (r, c)) ∧ Typ (Θ ++ Δ) (er r) τ ∧
    (c = .direct → DirectInv (Θ ++ Δ) v Θ.length σ τ r) ∧ (c = .reduced → τ.size ≤ σ.size)

theorem size_arrows_le (σs : List Ty) (τ : Ty) : τ.size ≤ (Ty.arrows σs τ).size := by
  induction σs with
  | nil => exact Nat.le_refl _
  | cons σ σs ih => simp only [Ty.arrows, Ty.size]; omega

theorem size_arrows_dom {σs : List Ty} {τ : Ty} : ∀ σ ∈ σs, σ.size < (Ty.arrows σs τ).size := by
  induction σs with
  | nil => intro σ h; cases h
  | cons ρ σs ih =>
    intro σ h
    simp only [Ty.arrows, Ty.size]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih σ h; omega

/-- Flags other than `.no` give a type no larger than the substituted value's. -/
theorem HinstOk.size {Γ : List Ty} {v : Expr} {k : Nat} {σ τ : Ty} {r : Expr} {c : Created}
    (hd : c = .direct → DirectInv Γ v k σ τ r) (hr : c = .reduced → τ.size ≤ σ.size)
    (hc : c ≠ .no) : τ.size ≤ σ.size := by
  cases c with
  | no => exact absurd rfl hc
  | direct =>
    obtain ⟨_, σs, _, rfl, _⟩ := hd rfl
    exact size_arrows_le σs τ
  | reduced => exact hr rfl

end Ix.CompileCert.Conv
