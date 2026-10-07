import Ix.CompileCert.Conv.Tm

/-!
# M7 X1: the conversion relation

`Conv Γ a b`: the least congruence and equivalence on `Tm` containing the root steps `Step Γ`:

* **β** `(λ t. b) a ⟶ b[0 := a]` — design document §4.3 (the development contracts "the
  β-redexes formed by applying the image's own motive and minor λs" and, at a call site, "the
  created β-redex is contracted, and so on hereditarily"), §4.5 (inlining is "`img(a)`'s body with
  the arguments substituted"), and Def 3.6 / §1.6 ("δβ-convertible to Lean's own term");
* **η** `λ t. f (bvar 0) ⟶ f` when `bvar 0 ∉ f` — §4.3 item 1 (the motive and minor wrappers are
  η-contracted with Lean's `Expr.eta`) and item 2 ("η at the substituted variables", Q10); the
  development contracts it (`Ix/Compile/Image/Develop.lean` `hinst`, the `.lam` case), so the
  development lemma is false without it;
* **projection of a pair constructor** `PProd.mk α β a b |>.1 ⟶ a` (and `.2 ⟶ b`, and the same
  for `And.intro`) — §4.3 item 2 ("so are projection-of-constructor redexes `(⟨a, b⟩).1 ↦ a`
  (`PProd`, `And`)"), with exactly the test of `Ix.Compile.Image.projCtor?` (`pairName`);
* **the environment's rules** `Γ.ax`: δ of the image constants and of Def 3.5's expansions
  (§4.5: "Replace the occurrence by `img(a)`'s body with the arguments substituted"; decision 3:
  the Lean name of an image-kind auxiliary denotes its image), and any rule schema a later
  package states (L2a-syn: the canonical recursors' ι as the syntactic `IxBlockLaws`).

Hashes, binder names and infos and `mdata` are not seen (`er`, `Tm.lean`): two expressions with
one erasure are convertible by `refl`.

**Not included**, and why that suffices. ι (a recursor at a constructor): the development never
contracts one (§4.3: "ι-redexes are **not** contracted"), and the image rules' ι-steps are the
canonical recursors' rules, which L2a-syn adds as `Γ.ax` instances (relative to `IxBlockLaws`,
OD5) rather than as a rule of the relation; ζ (`let`), literal and `Nat`/`String` reductions,
structure η, unit η, proof irrelevance and universe-level equivalence: no step of the image path
(Def 3.4–3.6, §4.3, §4.5) uses them, and every one of them is a kernel conversion, so leaving
them out only makes `Conv` finer (every `Conv` is a conversion of the checker; the converse is
not claimed). L2a-syn's statement "the image path's rules hold by conversion" is a `Conv` built
from δ (the image), β (the motives, minors, fields), ι (the canonical recursor, from `Γ.ax`), β
again (into the packed minor), the projection of the packing and η of the wrappers: all of them
are rules here.
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)

/-- `s.i` reduces on `c α β a b`: `PProd`'s projections on `PProd.mk`, `And`'s on `And.intro`
(the test of `Ix.Compile.Image.projCtor?`, with its `==` on names). -/
def pairName (s c : Name) : Bool :=
  (s == Ix.Compile.Image.nPProd && c == Ix.Compile.Image.nPProdMk) ||
    (s == Ix.Compile.Image.nAnd && c == Ix.Compile.Image.nAndIntro)

/-- The environment of a conversion: root rules beyond β, η and the projection of a pair. -/
structure Env where
  ax : Tm → Tm → Prop

/-- No rule of its own: β, η and the projection of a pair only. -/
def Env.empty : Env := ⟨fun _ _ => False⟩

/-- `c α β a b` as a spine. -/
abbrev pair4 (c : Name) (us : Array Level) (α β a b : Tm) : Tm :=
  Tm.appN (.const c us) [α, β, a, b]

/-- The root steps. -/
inductive Step (Γ : Env) : Tm → Tm → Prop
  | beta (t b a : Tm) : Step Γ (.app (.lam t b) a) (Tm.inst a 0 b)
  | eta (t f : Tm) : f.occ 0 = false → Step Γ (.lam t (.app f (.bvar 0))) (f.lower 1 0)
  | proj0 (s c : Name) (us : Array Level) (α β a b : Tm) : pairName s c = true →
      Step Γ (.proj s 0 (pair4 c us α β a b)) a
  | proj1 (s c : Name) (us : Array Level) (α β a b : Tm) : pairName s c = true →
      Step Γ (.proj s 1 (pair4 c us α β a b)) b
  | ax {l r : Tm} : Γ.ax l r → Step Γ l r

/-- **The conversion relation**: the equivalence and congruence closure of `Step Γ`. -/
inductive Conv (Γ : Env) : Tm → Tm → Prop
  | refl (a : Tm) : Conv Γ a a
  | symm {a b : Tm} : Conv Γ a b → Conv Γ b a
  | trans {a b c : Tm} : Conv Γ a b → Conv Γ b c → Conv Γ a c
  | step {a b : Tm} : Step Γ a b → Conv Γ a b
  | app {f f' a a' : Tm} : Conv Γ f f' → Conv Γ a a' → Conv Γ (.app f a) (.app f' a')
  | lam {t t' b b' : Tm} : Conv Γ t t' → Conv Γ b b' → Conv Γ (.lam t b) (.lam t' b')
  | pi {t t' b b' : Tm} : Conv Γ t t' → Conv Γ b b' → Conv Γ (.pi t b) (.pi t' b')
  | letE {t t' v v' b b' : Tm} : Conv Γ t t' → Conv Γ v v' → Conv Γ b b' →
      Conv Γ (.letE t v b) (.letE t' v' b')
  | proj {e e' : Tm} (s : Name) (i : Nat) : Conv Γ e e' → Conv Γ (.proj s i e) (.proj s i e')

/-- Two lists related pointwise. -/
inductive Forall2 (R : Tm → Tm → Prop) : List Tm → List Tm → Prop
  | nil : Forall2 R [] []
  | cons {a b : Tm} {as bs : List Tm} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- Conversion of compiler expressions: of their erasures. -/
def ExprConv (Γ : Env) (e e' : Expr) : Prop := Conv Γ (er e) (er e')

namespace Conv

variable {Γ : Env}

theorem rfl' {a b : Tm} (h : a = b) : Conv Γ a b := h ▸ refl a

theorem equivalence : Equivalence (Conv Γ) := ⟨refl, symm, trans⟩

theorem appN {f f' : Tm} (hf : Conv Γ f f') :
    ∀ {as as' : List Tm}, Forall2 (Conv Γ) as as' → Conv Γ (Tm.appN f as) (Tm.appN f' as')
  | [], [], Forall2.nil => hf
  | _ :: _, _ :: _, Forall2.cons ha hs => by
    simp only [Tm.appN_cons]; exact appN (app hf ha) hs

theorem appN_args (f : Tm) {as as' : List Tm} (h : Forall2 (Conv Γ) as as') :
    Conv Γ (Tm.appN f as) (Tm.appN f as') := appN (refl f) h

theorem forall₂_refl : ∀ (as : List Tm), Forall2 (Conv Γ) as as
  | [] => Forall2.nil
  | a :: as => Forall2.cons (refl a) (forall₂_refl as)

/-- β at the head of a spine. -/
theorem beta_appN (t b a : Tm) (as : List Tm) :
    Conv Γ (Tm.appN (.lam t b) (a :: as)) (Tm.appN (Tm.inst a 0 b) as) := by
  rw [Tm.appN_cons]; exact appN (step (.beta t b a)) (forall₂_refl as)

/-- More rules give more conversions. -/
theorem mono {Γ' : Env} (h : ∀ l r, Γ.ax l r → Γ'.ax l r) {a b : Tm} : Conv Γ a b → Conv Γ' a b := by
  intro hc
  induction hc with
  | refl a => exact refl a
  | symm _ ih => exact symm ih
  | trans _ _ ih1 ih2 => exact trans ih1 ih2
  | step s =>
    cases s with
    | beta t₀ b₀ a₀ => exact step (.beta t₀ b₀ a₀)
    | eta t₀ f₀ hf => exact step (.eta t₀ f₀ hf)
    | proj0 _ _ _ _ _ _ _ hp => exact step (.proj0 _ _ _ _ _ _ _ hp)
    | proj1 _ _ _ _ _ _ _ hp => exact step (.proj1 _ _ _ _ _ _ _ hp)
    | ax hl => exact step (.ax (h _ _ hl))
  | app _ _ ih1 ih2 => exact app ih1 ih2
  | lam _ _ ih1 ih2 => exact lam ih1 ih2
  | pi _ _ ih1 ih2 => exact pi ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact letE ih1 ih2 ih3
  | proj s i _ ih => exact proj s i ih

end Conv

/-! ## Spines under the de Bruijn operations -/

namespace Tm

theorem lift_appN (n c : Nat) (f : Tm) (as : List Tm) :
    lift n c (appN f as) = appN (lift n c f) (as.map (lift n c)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [appN_cons, ih, lift, List.map_cons]

theorem inst_appN (v : Tm) (k : Nat) (f : Tm) (as : List Tm) :
    inst v k (appN f as) = appN (inst v k f) (as.map (inst v k)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [appN_cons, ih, inst, List.map_cons]

theorem lower_appN (n c : Nat) (f : Tm) (as : List Tm) :
    lower n c (appN f as) = appN (lower n c f) (as.map (lower n c)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [appN_cons, ih, lower, List.map_cons]

/-- Substituting for a variable that does not occur is lowering. -/
theorem inst_eq_lower : ∀ (v : Tm) (k : Nat) (t : Tm), occ t k = false → inst v k t = lower 1 k t
  | v, k, bvar i, h => by
    simp only [occ, beq_eq_false_iff_ne, ne_eq] at h
    simp only [inst, h, ↓reduceIte, lower]
    congr 1
  | v, k, app f a, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp only [inst, lower, inst_eq_lower v k f h.1, inst_eq_lower v k a h.2]
  | v, k, lam t b, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp only [inst, lower, inst_eq_lower v k t h.1, inst_eq_lower v (k + 1) b h.2]
  | v, k, pi t b, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp only [inst, lower, inst_eq_lower v k t h.1, inst_eq_lower v (k + 1) b h.2]
  | v, k, letE t w b, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp only [inst, lower, inst_eq_lower v k t h.1.1, inst_eq_lower v k w h.1.2,
      inst_eq_lower v (k + 1) b h.2]
  | v, k, proj s i e, h => by
    simp only [occ] at h
    simp only [inst, lower, inst_eq_lower v k e h]
  | _, _, fvar _, _ | _, _, mvar _, _ | _, _, sort _, _ | _, _, const _ _, _ | _, _, lit _, _ => rfl

/-- A substitution at `k` creates no occurrence below `k`. -/
theorem occ_inst_lt : ∀ (v : Tm) (k j : Nat) (t : Tm), j < k → occ (inst v k t) j = occ t j
  | v, k, j, bvar i, h => by
    simp only [inst]
    by_cases hi : i = k
    · subst hi
      simp only [↓reduceIte, occ]
      rw [occ_lift_mid i 0 j v (Nat.zero_le _) (by omega)]
      simp; omega
    · simp only [hi, ↓reduceIte, occ]
      by_cases hk : k < i
      · simp only [hk, ↓reduceIte]
        have h1 : (i - 1 == j) = false := by simp; omega
        have h2 : (i == j) = false := by simp; omega
        rw [h1, h2]
      · simp only [hk, ↓reduceIte]
  | v, k, j, app f a, h => by simp only [inst, occ, occ_inst_lt v k j f h, occ_inst_lt v k j a h]
  | v, k, j, lam t b, h => by
    simp only [inst, occ, occ_inst_lt v k j t h, occ_inst_lt v (k + 1) (j + 1) b (by omega)]
  | v, k, j, pi t b, h => by
    simp only [inst, occ, occ_inst_lt v k j t h, occ_inst_lt v (k + 1) (j + 1) b (by omega)]
  | v, k, j, letE t w b, h => by
    simp only [inst, occ, occ_inst_lt v k j t h, occ_inst_lt v k j w h,
      occ_inst_lt v (k + 1) (j + 1) b (by omega)]
  | v, k, j, proj s i e, h => by simp only [inst, occ, occ_inst_lt v k j e h]
  | _, _, _, fvar _, _ | _, _, _, mvar _, _ | _, _, _, sort _, _
  | _, _, _, const _ _, _ | _, _, _, lit _, _ => rfl

end Tm

/-! ## Stability under the de Bruijn operations -/

/-- The environment's rules are closed under lifting. -/
def Env.LiftClosed (Γ : Env) : Prop :=
  ∀ n c l r, Γ.ax l r → Γ.ax (l.lift n c) (r.lift n c)

/-- The environment's rules are closed under substitution. -/
def Env.InstClosed (Γ : Env) : Prop :=
  ∀ v k l r, Γ.ax l r → Γ.ax (Tm.inst v k l) (Tm.inst v k r)

theorem Env.empty_liftClosed : Env.empty.LiftClosed := fun _ _ _ _ h => h
theorem Env.empty_instClosed : Env.empty.InstClosed := fun _ _ _ _ h => h

/-- Rules between closed terms are closed under both. -/
theorem Env.liftClosed_of_closed {Γ : Env} (h : ∀ l r, Γ.ax l r → l.range = 0 ∧ r.range = 0) :
    Γ.LiftClosed := by
  intro n c l r hl
  have := h l r hl
  rw [Tm.lift_of_range_le n c l (by omega), Tm.lift_of_range_le n c r (by omega)]
  exact hl

theorem Env.instClosed_of_closed {Γ : Env} (h : ∀ l r, Γ.ax l r → l.range = 0 ∧ r.range = 0) :
    Γ.InstClosed := by
  intro v k l r hl
  have := h l r hl
  rw [Tm.inst_of_range_le v k l (by omega), Tm.inst_of_range_le v k r (by omega)]
  exact hl

section
variable {Γ : Env}

theorem Step.lift (hΓ : Γ.LiftClosed) (n c : Nat) {a b : Tm} (h : Step Γ a b) :
    Step Γ (a.lift n c) (b.lift n c) := by
  cases h with
  | beta t b a =>
    rw [Tm.lift_inst_hi a n c 0 b (Nat.zero_le _), Nat.sub_zero]
    exact .beta _ _ _
  | eta t f hf =>
    have hf' : (Tm.lift n (c + 1) f).occ 0 = false := by
      rw [Tm.occ_lift_lt n (c + 1) 0 f (by omega)]; exact hf
    have e1 : (Tm.lam t (.app f (.bvar 0))).lift n c =
        .lam (t.lift n c) (.app (f.lift n (c + 1)) (.bvar 0)) := by
      simp [Tm.lift]
    have e2 : (f.lower 1 0).lift n c = (f.lift n (c + 1)).lower 1 0 := by
      rw [← Tm.inst_eq_lower (.bvar 0) 0 f hf, ← Tm.inst_eq_lower ((Tm.bvar 0).lift n c) 0 _ hf',
        Tm.lift_inst_hi _ n c 0 f (Nat.zero_le _), Nat.sub_zero]
    rw [e1, e2]; exact .eta _ _ hf'
  | proj0 s c' us α β a b hp =>
    simp only [Tm.lift, Tm.lift_appN, List.map_cons, List.map_nil]
    exact .proj0 _ _ _ _ _ _ _ hp
  | proj1 s c' us α β a b hp =>
    simp only [Tm.lift, Tm.lift_appN, List.map_cons, List.map_nil]
    exact .proj1 _ _ _ _ _ _ _ hp
  | ax hl => exact .ax (hΓ n c _ _ hl)

theorem Conv.lift (hΓ : Γ.LiftClosed) (n c : Nat) {a b : Tm} (h : Conv Γ a b) :
    Conv Γ (a.lift n c) (b.lift n c) := by
  induction h generalizing c with
  | refl a => exact .refl _
  | symm _ ih => exact .symm (ih c)
  | trans _ _ ih1 ih2 => exact .trans (ih1 c) (ih2 c)
  | step s => exact .step (s.lift hΓ n c)
  | app _ _ ih1 ih2 => exact .app (ih1 c) (ih2 c)
  | lam _ _ ih1 ih2 => exact .lam (ih1 c) (ih2 (c + 1))
  | pi _ _ ih1 ih2 => exact .pi (ih1 c) (ih2 (c + 1))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 c) (ih2 c) (ih3 (c + 1))
  | proj s i _ ih => exact .proj s i (ih c)

theorem Step.inst (hΓ : Γ.InstClosed) (v : Tm) (k : Nat) {a b : Tm} (h : Step Γ a b) :
    Step Γ (Tm.inst v k a) (Tm.inst v k b) := by
  cases h with
  | beta t b a =>
    rw [Tm.inst_inst v a 0 k b (Nat.zero_le _), Nat.sub_zero]
    exact .beta _ _ _
  | eta t f hf =>
    have hf' : (Tm.inst v (k + 1) f).occ 0 = false := by
      rw [Tm.occ_inst_lt v (k + 1) 0 f (by omega)]; exact hf
    have e1 : Tm.inst v k (Tm.lam t (.app f (.bvar 0))) =
        .lam (Tm.inst v k t) (.app (Tm.inst v (k + 1) f) (.bvar 0)) := by
      simp [Tm.inst]
    have e2 : Tm.inst v k (f.lower 1 0) = (Tm.inst v (k + 1) f).lower 1 0 := by
      rw [← Tm.inst_eq_lower (.bvar 0) 0 f hf, ← Tm.inst_eq_lower (Tm.inst v k (Tm.bvar 0)) 0 _ hf',
        Tm.inst_inst v _ 0 k f (Nat.zero_le _), Nat.sub_zero]
    rw [e1, e2]; exact .eta _ _ hf'
  | proj0 s c' us α β a b hp =>
    simp only [Tm.inst, Tm.inst_appN, List.map_cons, List.map_nil]
    exact .proj0 _ _ _ _ _ _ _ hp
  | proj1 s c' us α β a b hp =>
    simp only [Tm.inst, Tm.inst_appN, List.map_cons, List.map_nil]
    exact .proj1 _ _ _ _ _ _ _ hp
  | ax hl => exact .ax (hΓ v k _ _ hl)

/-- **Stability under substitution** (the converted term). -/
theorem Conv.inst (hΓ : Γ.InstClosed) (v : Tm) (k : Nat) {a b : Tm} (h : Conv Γ a b) :
    Conv Γ (Tm.inst v k a) (Tm.inst v k b) := by
  induction h generalizing k with
  | refl a => exact .refl _
  | symm _ ih => exact .symm (ih k)
  | trans _ _ ih1 ih2 => exact .trans (ih1 k) (ih2 k)
  | step s => exact .step (s.inst hΓ v k)
  | app _ _ ih1 ih2 => exact .app (ih1 k) (ih2 k)
  | lam _ _ ih1 ih2 => exact .lam (ih1 k) (ih2 (k + 1))
  | pi _ _ ih1 ih2 => exact .pi (ih1 k) (ih2 (k + 1))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 k) (ih2 k) (ih3 (k + 1))
  | proj s i _ ih => exact .proj s i (ih k)

/-- **Stability under substitution** (the substituted value). -/
theorem Conv.inst_val (hΓ : Γ.LiftClosed) {v v' : Tm} (hv : Conv Γ v v') :
    ∀ (k : Nat) (t : Tm), Conv Γ (Tm.inst v k t) (Tm.inst v' k t)
  | k, .bvar i => by
    simp only [Tm.inst]
    by_cases hi : i = k
    · simp only [hi, ↓reduceIte]; exact hv.lift hΓ k 0
    · simp only [hi, ↓reduceIte]; exact .refl _
  | k, .app f a => .app (inst_val hΓ hv k f) (inst_val hΓ hv k a)
  | k, .lam t b => .lam (inst_val hΓ hv k t) (inst_val hΓ hv (k + 1) b)
  | k, .pi t b => .pi (inst_val hΓ hv k t) (inst_val hΓ hv (k + 1) b)
  | k, .letE t w b => .letE (inst_val hΓ hv k t) (inst_val hΓ hv k w) (inst_val hΓ hv (k + 1) b)
  | k, .proj s i e => .proj s i (inst_val hΓ hv k e)
  | _, .fvar _ | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => .refl _

theorem Conv.inst₂ (hΓl : Γ.LiftClosed) (hΓi : Γ.InstClosed) {v v' t t' : Tm} (k : Nat)
    (hv : Conv Γ v v') (ht : Conv Γ t t') : Conv Γ (Tm.inst v k t) (Tm.inst v' k t') :=
  .trans (ht.inst hΓi v k) (Conv.inst_val hΓl hv k t')

/-- Stability under lowering a variable that occurs on neither side. -/
theorem Conv.lower (hΓ : Γ.InstClosed) (k : Nat) {a b : Tm} (ha : a.occ k = false)
    (hb : b.occ k = false) (h : Conv Γ a b) : Conv Γ (a.lower 1 k) (b.lower 1 k) := by
  rw [← Tm.inst_eq_lower (.bvar 0) k a ha, ← Tm.inst_eq_lower (.bvar 0) k b hb]
  exact h.inst hΓ _ k

end

end Ix.CompileCert.Conv
