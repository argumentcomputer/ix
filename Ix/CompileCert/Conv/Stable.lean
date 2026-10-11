import Ix.CompileCert.Conv.Erase
import Batteries.Tactic.OpenPrivate

/-!
# M7 X1: conversion under the compiler's other term operations

Besides lifting and substitution (`Rel.lean`), the image construction and the rewrite move terms
through three more operations, and conversion survives each:

* **constant and level maps** (`Tm.mapC`): `Ix.Compile.Canon.substLevels` (the universe
  instantiation of an image at a call site, `Image.inline`; `er_substLevels`) and
  `canonicalizeConstNames` (the view names of an image mapped back to the compiled ones,
  `BlockView.image`; `er_canonicalizeConstNames`) are both a map on constants and sorts;
  `Conv.mapC`: a conversion stays one when its environment's rules are mapped too and the map
  keeps `PProd.mk`/`And.intro` recognisable (`pairName`);
* **abstraction of free variables** (`Tm.abstractF`, `Ix.Compile.Image.abstractFVars`, behind
  `mkLambda`/`mkForall` and `substFVars`; `er_abstractFVars`): `Conv.abstractF`, for an
  environment whose rules are closed under it (rules between fvar-free terms, as the expansions
  of image constants are).
-/

open private Ix.Compile.Canon.substLevels.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Canon.canonicalizeConstNames.go from Ix.Compile.Canon.Expr
open private Ix.Compile.Image.abstractFVars.go from Ix.Compile.Image.Expr

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)

namespace Tm

/-- A map on constants (name and levels) and on sorts. -/
def mapC (g : Name → Array Level → Name × Array Level) (h : Level → Level) : Tm → Tm
  | bvar i => bvar i
  | fvar x => fvar x
  | mvar x => mvar x
  | sort u => sort (h u)
  | const c us => const (g c us).1 (g c us).2
  | app f a => app (mapC g h f) (mapC g h a)
  | lam t b => lam (mapC g h t) (mapC g h b)
  | pi t b => pi (mapC g h t) (mapC g h b)
  | letE t v b => letE (mapC g h t) (mapC g h v) (mapC g h b)
  | lit l => lit l
  | proj s i e => proj s i (mapC g h e)

section
variable (g : Name → Array Level → Name × Array Level) (h : Level → Level)

theorem mapC_lift : ∀ (n c : Nat) (t : Tm), mapC g h (lift n c t) = lift n c (mapC g h t)
  | n, c, bvar i => rfl
  | n, c, app f a => by simp only [lift, mapC, mapC_lift n c f, mapC_lift n c a]
  | n, c, lam t b => by simp only [lift, mapC, mapC_lift n c t, mapC_lift n (c + 1) b]
  | n, c, pi t b => by simp only [lift, mapC, mapC_lift n c t, mapC_lift n (c + 1) b]
  | n, c, letE t v b => by
    simp only [lift, mapC, mapC_lift n c t, mapC_lift n c v, mapC_lift n (c + 1) b]
  | n, c, proj s i e => by simp only [lift, mapC, mapC_lift n c e]
  | _, _, fvar _ | _, _, mvar _ | _, _, sort _ | _, _, const _ _ | _, _, lit _ => rfl

theorem mapC_inst : ∀ (v : Tm) (k : Nat) (t : Tm),
    mapC g h (inst v k t) = inst (mapC g h v) k (mapC g h t)
  | v, k, bvar i => by
    by_cases hi : i = k
    · subst hi; simp only [inst, mapC, ↓reduceIte, mapC_lift]
    · simp only [inst, hi, ↓reduceIte, mapC]
  | v, k, app f a => by simp only [inst, mapC, mapC_inst v k f, mapC_inst v k a]
  | v, k, lam t b => by simp only [inst, mapC, mapC_inst v k t, mapC_inst v (k + 1) b]
  | v, k, pi t b => by simp only [inst, mapC, mapC_inst v k t, mapC_inst v (k + 1) b]
  | v, k, letE t w b => by
    simp only [inst, mapC, mapC_inst v k t, mapC_inst v k w, mapC_inst v (k + 1) b]
  | v, k, proj s i e => by simp only [inst, mapC, mapC_inst v k e]
  | _, _, fvar _ | _, _, mvar _ | _, _, sort _ | _, _, const _ _ | _, _, lit _ => rfl

theorem occ_mapC : ∀ (t : Tm) (k : Nat), occ (mapC g h t) k = occ t k
  | bvar i, k => rfl
  | app f a, k => by simp only [mapC, occ, occ_mapC f k, occ_mapC a k]
  | lam t b, k => by simp only [mapC, occ, occ_mapC t k, occ_mapC b (k + 1)]
  | pi t b, k => by simp only [mapC, occ, occ_mapC t k, occ_mapC b (k + 1)]
  | letE t v b, k => by simp only [mapC, occ, occ_mapC t k, occ_mapC v k, occ_mapC b (k + 1)]
  | proj s i e, k => by simp only [mapC, occ, occ_mapC e k]
  | fvar _, _ | mvar _, _ | sort _, _ | const _ _, _ | lit _, _ => rfl

theorem mapC_lower (f : Tm) (hf : occ f 0 = false) :
    mapC g h (lower 1 0 f) = lower 1 0 (mapC g h f) := by
  rw [← inst_eq_lower (.bvar 0) 0 f hf, mapC_inst,
    ← inst_eq_lower (mapC g h (.bvar 0)) 0 _ (by rw [occ_mapC]; exact hf)]

theorem mapC_appN (f : Tm) (as : List Tm) :
    mapC g h (appN f as) = appN (mapC g h f) (as.map (mapC g h)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [appN_cons, ih, mapC, List.map_cons]

end

end Tm

/-- **Conversion under a constant and level map**: with the environment's rules mapped and
`PProd.mk`/`And.intro` kept recognisable, a conversion maps to a conversion. -/
theorem Conv.mapC {Γ Γ' : Env} (g : Name → Array Level → Name × Array Level) (h : Level → Level)
    (hp : ∀ s c us, pairName s c = true → pairName s (g c us).1 = true)
    (hax : ∀ l r, Γ.ax l r → Γ'.ax (Tm.mapC g h l) (Tm.mapC g h r)) {a b : Tm} (hc : Conv Γ a b) :
    Conv Γ' (Tm.mapC g h a) (Tm.mapC g h b) := by
  induction hc with
  | refl a => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | step s =>
    cases s with
    | beta t b a =>
      rw [Tm.mapC_inst]; exact .step (.beta _ _ _)
    | eta t f hf =>
      rw [Tm.mapC_lower g h f hf]
      exact .step (.eta _ _ (by rw [Tm.occ_mapC]; exact hf))
    | proj0 s c us α β a b hpn =>
      simp only [Tm.mapC, Tm.mapC_appN, List.map_cons, List.map_nil]
      exact .step (.proj0 _ _ _ _ _ _ _ (hp s c us hpn))
    | proj1 s c us α β a b hpn =>
      simp only [Tm.mapC, Tm.mapC_appN, List.map_cons, List.map_nil]
      exact .step (.proj1 _ _ _ _ _ _ _ (hp s c us hpn))
    | ax hl => exact .step (.ax (hax _ _ hl))
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | pi _ _ ih1 ih2 => exact .pi ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | proj s i _ ih => exact .proj s i ih

/-! ## The compiler's maps are constant and level maps -/

theorem er_substLevels_go (ps : Array Name) (us : Array Level) : ∀ (e : Expr),
    er (Ix.Compile.Canon.substLevels.go ps us e) =
      Tm.mapC (fun c vs => (c, vs.map (Ix.Compile.Canon.substLevel ps us)))
        (Ix.Compile.Canon.substLevel ps us) (er e)
  | .sort .. => rfl
  | .const .. => rfl
  | .app f a _ => by
    simp only [Ix.Compile.Canon.substLevels.go, er_mkApp, er, Tm.mapC, er_substLevels_go ps us f,
      er_substLevels_go ps us a]
  | .lam _ t b _ _ => by
    simp only [Ix.Compile.Canon.substLevels.go, er_mkLam, er, Tm.mapC, er_substLevels_go ps us t,
      er_substLevels_go ps us b]
  | .forallE _ t b _ _ => by
    simp only [Ix.Compile.Canon.substLevels.go, er_mkForallE, er, Tm.mapC,
      er_substLevels_go ps us t, er_substLevels_go ps us b]
  | .letE _ t v b _ _ => by
    simp only [Ix.Compile.Canon.substLevels.go, er_mkLetE, er, Tm.mapC, er_substLevels_go ps us t,
      er_substLevels_go ps us v, er_substLevels_go ps us b]
  | .proj _ _ s _ => by
    simp only [Ix.Compile.Canon.substLevels.go, er_mkProj, er, Tm.mapC, er_substLevels_go ps us s]
  | .mdata _ x _ => by
    simp only [Ix.Compile.Canon.substLevels.go, er_mkMData, er, er_substLevels_go ps us x]
  | .bvar .. | .fvar .. | .mvar .. | .lit .. => rfl

theorem Tm.mapC_id : ∀ (t : Tm), Tm.mapC (fun c vs => (c, vs)) id t = t
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .app f a => by simp only [Tm.mapC, Tm.mapC_id f, Tm.mapC_id a]
  | .lam t b => by simp only [Tm.mapC, Tm.mapC_id t, Tm.mapC_id b]
  | .pi t b => by simp only [Tm.mapC, Tm.mapC_id t, Tm.mapC_id b]
  | .letE t v b => by simp only [Tm.mapC, Tm.mapC_id t, Tm.mapC_id v, Tm.mapC_id b]
  | .proj s i e => by simp only [Tm.mapC, Tm.mapC_id e]

/-- `substLevels` erases to a constant and level map (the identity map when there is nothing
to substitute). -/
theorem er_substLevels (ps : Array Name) (us : Array Level) (e : Expr) :
    er (Ix.Compile.Canon.substLevels ps us e) =
      if ps.isEmpty || us.isEmpty then er e else
        Tm.mapC (fun c vs => (c, vs.map (Ix.Compile.Canon.substLevel ps us)))
          (Ix.Compile.Canon.substLevel ps us) (er e) := by
  unfold Ix.Compile.Canon.substLevels
  split <;> simp_all [er_substLevels_go]

theorem er_canonicalizeConstNames_go (m : Std.HashMap Name Name) : ∀ (e : Expr),
    er (Ix.Compile.Canon.canonicalizeConstNames.go m e) =
      Tm.mapC (fun c vs => ((m.get? c).getD c, vs)) id (er e)
  | .const c us _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go]
    cases hm : m.get? c with
    | none => simp only [Std.HashMap.get?_eq_getElem?] at hm; simp [er, Tm.mapC, hm]
    | some c' => simp only [Std.HashMap.get?_eq_getElem?] at hm; simp [er, Tm.mapC, hm]
  | .app f a _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go, er_mkApp, er, Tm.mapC,
      er_canonicalizeConstNames_go m f, er_canonicalizeConstNames_go m a]
  | .lam _ t b _ _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go, er_mkLam, er, Tm.mapC,
      er_canonicalizeConstNames_go m t, er_canonicalizeConstNames_go m b]
  | .forallE _ t b _ _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go, er_mkForallE, er, Tm.mapC,
      er_canonicalizeConstNames_go m t, er_canonicalizeConstNames_go m b]
  | .letE _ t v b _ _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go, er_mkLetE, er, Tm.mapC,
      er_canonicalizeConstNames_go m t, er_canonicalizeConstNames_go m v,
      er_canonicalizeConstNames_go m b]
  | .proj _ _ s _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go, er_mkProj, er, Tm.mapC,
      er_canonicalizeConstNames_go m s]
  | .mdata _ x _ => by
    simp only [Ix.Compile.Canon.canonicalizeConstNames.go, er_mkMData, er,
      er_canonicalizeConstNames_go m x]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. => rfl

/-- `canonicalizeConstNames` erases to a renaming of constants (nothing is renamed by an empty
map). -/
theorem er_canonicalizeConstNames (m : Std.HashMap Name Name) (e : Expr) :
    er (Ix.Compile.Canon.canonicalizeConstNames m e) =
      if m.isEmpty then er e else Tm.mapC (fun c vs => ((m.get? c).getD c, vs)) id (er e) := by
  unfold Ix.Compile.Canon.canonicalizeConstNames
  split <;> simp_all [er_canonicalizeConstNames_go]

/-! ## Abstraction of free variables -/

namespace Tm

/-- `Ix.Compile.Image.abstractFVars.go`: `xs[i]` ↦ `bvar (d + (|xs| - 1 - i))` under `d`
binders (the first index by `==`, as `Array.idxOf?`). -/
def abstractF (xs : Array Name) : Tm → Nat → Tm
  | fvar n, d =>
    match xs.idxOf? n with
    | some i => bvar (d + (xs.size - 1 - i))
    | none => fvar n
  | app f a, d => app (abstractF xs f d) (abstractF xs a d)
  | lam t b, d => lam (abstractF xs t d) (abstractF xs b (d + 1))
  | pi t b, d => pi (abstractF xs t d) (abstractF xs b (d + 1))
  | letE t v b, d => letE (abstractF xs t d) (abstractF xs v d) (abstractF xs b (d + 1))
  | proj s i e, d => proj s i (abstractF xs e d)
  | bvar i, _ => bvar i
  | mvar x, _ => mvar x
  | sort u, _ => sort u
  | const c us, _ => const c us
  | lit l, _ => lit l

section
variable (xs : Array Name)

theorem abstractF_lift : ∀ (n c d : Nat) (t : Tm), c ≤ d →
    abstractF xs (lift n c t) (d + n) = lift n c (abstractF xs t d)
  | n, c, d, fvar x, h => by
    simp only [lift, abstractF]
    cases xs.idxOf? x with
    | none => rfl
    | some i =>
      simp only [lift]; congr 1
      have : c ≤ d + (xs.size - 1 - i) := by omega
      simp only [this, ↓reduceIte]; omega
  | n, c, d, app f a, h => by
    simp only [lift, abstractF, abstractF_lift n c d f h, abstractF_lift n c d a h]
  | n, c, d, lam t b, h => by
    simp only [lift, abstractF, abstractF_lift n c d t h]
    rw [show d + n + 1 = (d + 1) + n by omega, abstractF_lift n (c + 1) (d + 1) b (by omega)]
  | n, c, d, pi t b, h => by
    simp only [lift, abstractF, abstractF_lift n c d t h]
    rw [show d + n + 1 = (d + 1) + n by omega, abstractF_lift n (c + 1) (d + 1) b (by omega)]
  | n, c, d, letE t v b, h => by
    simp only [lift, abstractF, abstractF_lift n c d t h, abstractF_lift n c d v h]
    rw [show d + n + 1 = (d + 1) + n by omega, abstractF_lift n (c + 1) (d + 1) b (by omega)]
  | n, c, d, proj s i e, h => by simp only [lift, abstractF, abstractF_lift n c d e h]
  | _, _, _, bvar _, _ | _, _, _, mvar _, _ | _, _, _, sort _, _ | _, _, _, const _ _, _
  | _, _, _, lit _, _ => rfl

theorem abstractF_inst : ∀ (v : Tm) (d k : Nat) (t : Tm),
    abstractF xs (inst v k t) (d + k) = inst (abstractF xs v d) k (abstractF xs t (d + k + 1))
  | v, d, k, bvar i => by
    simp only [inst, abstractF]
    by_cases hi : i = k
    · simp only [hi, ↓reduceIte]
      rw [Nat.add_comm d k, show k + d = d + k by omega,
        abstractF_lift xs k 0 d v (Nat.zero_le _)]
    · simp only [hi, ↓reduceIte, abstractF]
  | v, d, k, fvar x => by
    simp only [inst, abstractF]
    cases xs.idxOf? x with
    | none => rfl
    | some j =>
      simp only [inst]
      have h1 : d + k + 1 + (xs.size - 1 - j) ≠ k := by omega
      have h2 : k < d + k + 1 + (xs.size - 1 - j) := by omega
      simp only [h1, h2, ↓reduceIte]; congr 1; omega
  | v, d, k, app f a => by simp only [inst, abstractF, abstractF_inst v d k f, abstractF_inst v d k a]
  | v, d, k, lam t b => by
    simp only [inst, abstractF, abstractF_inst v d k t]
    rw [show d + k + 1 = d + (k + 1) by omega, abstractF_inst v d (k + 1) b]
  | v, d, k, pi t b => by
    simp only [inst, abstractF, abstractF_inst v d k t]
    rw [show d + k + 1 = d + (k + 1) by omega, abstractF_inst v d (k + 1) b]
  | v, d, k, letE t w b => by
    simp only [inst, abstractF, abstractF_inst v d k t, abstractF_inst v d k w]
    rw [show d + k + 1 = d + (k + 1) by omega, abstractF_inst v d (k + 1) b]
  | v, d, k, proj s i e => by simp only [inst, abstractF, abstractF_inst v d k e]
  | _, _, _, mvar _ | _, _, _, sort _ | _, _, _, const _ _ | _, _, _, lit _ => rfl

theorem occ_abstractF : ∀ (t : Tm) (d k : Nat), k < d → occ (abstractF xs t d) k = occ t k
  | fvar x, d, k, h => by
    simp only [abstractF]
    cases xs.idxOf? x with
    | none => rfl
    | some i => simp only [occ]; simp; omega
  | app f a, d, k, h => by simp only [abstractF, occ, occ_abstractF f d k h, occ_abstractF a d k h]
  | lam t b, d, k, h => by
    simp only [abstractF, occ, occ_abstractF t d k h, occ_abstractF b (d + 1) (k + 1) (by omega)]
  | pi t b, d, k, h => by
    simp only [abstractF, occ, occ_abstractF t d k h, occ_abstractF b (d + 1) (k + 1) (by omega)]
  | letE t v b, d, k, h => by
    simp only [abstractF, occ, occ_abstractF t d k h, occ_abstractF v d k h,
      occ_abstractF b (d + 1) (k + 1) (by omega)]
  | proj s i e, d, k, h => by simp only [abstractF, occ, occ_abstractF e d k h]
  | bvar _, _, _, _ | mvar _, _, _, _ | sort _, _, _, _ | const _ _, _, _, _ | lit _, _, _, _ => rfl

theorem abstractF_appN (d : Nat) (f : Tm) (as : List Tm) :
    abstractF xs (appN f as) d = appN (abstractF xs f d) (as.map (abstractF xs · d)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [appN_cons, ih, abstractF, List.map_cons]

end

end Tm

/-- The environment's rules are closed under abstracting free variables. -/
def Env.AbstractClosed (Γ : Env) : Prop :=
  ∀ xs d l r, Γ.ax l r → Γ.ax (Tm.abstractF xs l d) (Tm.abstractF xs r d)

/-- **Conversion under abstraction of free variables.** -/
theorem Conv.abstractF {Γ : Env} (hΓ : Γ.AbstractClosed) (xs : Array Name) {a b : Tm}
    (hc : Conv Γ a b) : ∀ d, Conv Γ (Tm.abstractF xs a d) (Tm.abstractF xs b d) := by
  induction hc with
  | refl a => exact fun _ => .refl _
  | symm _ ih => exact fun d => .symm (ih d)
  | trans _ _ ih1 ih2 => exact fun d => .trans (ih1 d) (ih2 d)
  | step s =>
    intro d
    cases s with
    | beta t b a =>
      have := Tm.abstractF_inst xs a d 0 b
      simp only [Nat.add_zero] at this
      rw [this]; exact .step (.beta _ _ _)
    | eta t f hf =>
      have hf' : Tm.occ (Tm.abstractF xs f (d + 1)) 0 = false := by
        rw [Tm.occ_abstractF xs f (d + 1) 0 (by omega)]; exact hf
      have e1 : Tm.abstractF xs (f.lower 1 0) d = (Tm.abstractF xs f (d + 1)).lower 1 0 := by
        rw [← Tm.inst_eq_lower (.bvar 0) 0 f hf, ← Tm.inst_eq_lower (Tm.abstractF xs (.bvar 0) d) 0 _ hf']
        have := Tm.abstractF_inst xs (.bvar 0) d 0 f
        simpa using this
      simp only [Tm.abstractF]
      rw [e1]; exact .step (.eta _ _ hf')
    | proj0 s c us α β a b hpn =>
      simp only [Tm.abstractF, Tm.abstractF_appN, List.map_cons, List.map_nil]
      exact .step (.proj0 _ _ _ _ _ _ _ hpn)
    | proj1 s c us α β a b hpn =>
      simp only [Tm.abstractF, Tm.abstractF_appN, List.map_cons, List.map_nil]
      exact .step (.proj1 _ _ _ _ _ _ _ hpn)
    | ax hl => exact .step (.ax (hΓ _ _ _ _ hl))
  | app _ _ ih1 ih2 => exact fun d => .app (ih1 d) (ih2 d)
  | lam _ _ ih1 ih2 => exact fun d => .lam (ih1 d) (ih2 (d + 1))
  | pi _ _ ih1 ih2 => exact fun d => .pi (ih1 d) (ih2 (d + 1))
  | letE _ _ _ ih1 ih2 ih3 => exact fun d => .letE (ih1 d) (ih2 d) (ih3 (d + 1))
  | proj s i _ ih => exact fun d => .proj s i (ih d)

theorem er_abstractFVars_go (xs : Array Name) : ∀ (e : Expr) (d : Nat),
    er (Ix.Compile.Image.abstractFVars.go xs e d) = Tm.abstractF xs (er e) d
  | .fvar n h, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er, Tm.abstractF]
    cases xs.idxOf? n <;> rfl
  | .app f a _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er_mkApp, er, Tm.abstractF,
      er_abstractFVars_go xs f d, er_abstractFVars_go xs a d]
  | .lam _ t b _ _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er_mkLam, er, Tm.abstractF,
      er_abstractFVars_go xs t d, er_abstractFVars_go xs b (d + 1)]
  | .forallE _ t b _ _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er_mkForallE, er, Tm.abstractF,
      er_abstractFVars_go xs t d, er_abstractFVars_go xs b (d + 1)]
  | .letE _ t v b _ _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er_mkLetE, er, Tm.abstractF,
      er_abstractFVars_go xs t d, er_abstractFVars_go xs v d, er_abstractFVars_go xs b (d + 1)]
  | .proj _ _ s _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er_mkProj, er, Tm.abstractF,
      er_abstractFVars_go xs s d]
  | .mdata _ x _, d => by
    simp only [Ix.Compile.Image.abstractFVars.go, er_mkMData, er, er_abstractFVars_go xs x d]
  | .bvar .., _ | .mvar .., _ | .sort .., _ | .const .., _ | .lit .., _ => rfl

theorem Tm.abstractF_empty : ∀ (t : Tm) (d : Nat), Tm.abstractF #[] t d = t
  | .fvar x, d => by simp [Tm.abstractF]
  | .app f a, d => by simp only [Tm.abstractF, Tm.abstractF_empty f d, Tm.abstractF_empty a d]
  | .lam t b, d => by simp only [Tm.abstractF, Tm.abstractF_empty t d, Tm.abstractF_empty b (d + 1)]
  | .pi t b, d => by simp only [Tm.abstractF, Tm.abstractF_empty t d, Tm.abstractF_empty b (d + 1)]
  | .letE t v b, d => by
    simp only [Tm.abstractF, Tm.abstractF_empty t d, Tm.abstractF_empty v d,
      Tm.abstractF_empty b (d + 1)]
  | .proj s i e, d => by simp only [Tm.abstractF, Tm.abstractF_empty e d]
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl

/-- `abstractFVars` erases to `Tm.abstractF`. -/
theorem er_abstractFVars (xs : Array Name) (e : Expr) :
    er (Ix.Compile.Image.abstractFVars xs e) = Tm.abstractF xs (er e) 0 := by
  unfold Ix.Compile.Image.abstractFVars
  split
  · rename_i h
    have : xs = #[] := by simpa using h
    subst this; rw [Tm.abstractF_empty]
  · exact er_abstractFVars_go xs e 0

end Ix.CompileCert.Conv
