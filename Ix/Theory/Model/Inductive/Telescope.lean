/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Judgment
import Ix.Theory.Model.Support
import Ix.Theory.Model.SetModel.TupleTower

/-!
Dependent telescopes used by inductive parameters, indices, constructor
fields, and recursive function domains. Curried functions and tuple codes
share the same fitting relation. Computation requires fitting arguments,
including when a function is represented by the proof point.
-/

namespace Ix.Theory.Model.Telescope

open SetTheory SetTheory.Tower SetModel

universe u v
variable {V : Type v} [SetTheory V]

noncomputable def piN (w : Nat) : {n : Nat} → TeleS V n → (List V → V) → V
  | _, .nil, R => R []
  | _, .cons A B, R => piR w A (fun x => piN w (B x) (fun xs => R (x :: xs)))

noncomputable def curry (w : Nat) : {n : Nat} → TeleS V n → (List V → V) → V
  | _, .nil, f => f []
  | _, .cons A B, f => lamR w A (fun x => curry w (B x) (fun xs => f (x :: xs)))

noncomputable def applyN : V → List V → V
  | f, [] => f
  | f, x :: xs => applyN (app f x) xs

theorem applyN_append (f : V) (xs ys : List V) :
    applyN f (xs ++ ys) = applyN (applyN f xs) ys := by
  induction xs generalizing f <;> simp_all [applyN]

theorem curry_mem {w : Nat} : ∀ {n} (T : TeleS V n) {f R : List V → V},
    (∀ xs, FitsS T xs → f xs ∈ˢ R xs) → curry w T f ∈ˢ piN w T R
  | _, .nil, _, _, hf => hf [] trivial
  | _, .cons _ B, _, _, hf =>
    lamR_mem fun x hx => curry_mem (B x) (fun xs hxs => hf (x :: xs) ⟨hx, hxs⟩)

theorem piN_zero_mem : ∀ {n} (T : TeleS V n) {R : List V → V},
    (∀ xs, FitsS T xs → R xs ∈ˢ (univZero : V)) →
      piN 0 T R ∈ˢ (univZero : V)
  | _, .nil, _, hR => hR [] trivial
  | _, .cons _ _, _, _ => piR_zero_mem_univZero

theorem applyN_mem {w : Nat} : ∀ {n} (T : TeleS V n) {f : V} {R : List V → V}
    {xs : List V}, f ∈ˢ piN w T R → FitsS T xs →
    (w = 0 → ∀ ys, FitsS T ys → R ys ∈ˢ (univZero : V)) →
      applyN f xs ∈ˢ R xs
  | _, .nil, _, _, [], hf, _, _ => hf
  | _, .cons _ B, _, R, x :: xs, hf, hxs, hR => by
    apply applyN_mem (B x) (R := fun ys => R (x :: ys))
      (app_mem_piR hf hxs.1 ?_) hxs.2
    · intro hw ys hys
      exact hR hw (x :: ys) ⟨hxs.1, hys⟩
    · intro hw y hy
      subst w
      exact piN_zero_mem (B y) (fun ys hys => hR rfl (y :: ys) ⟨hy, hys⟩)

theorem applyN_curry {w : Nat} : ∀ {n} (T : TeleS V n) {f R : List V → V}
    {xs : List V}, FitsS T xs →
    (∀ ys, FitsS T ys → f ys ∈ˢ R ys) →
    (w = 0 → ∀ ys, FitsS T ys → R ys ∈ˢ (univZero : V)) →
      applyN (curry w T f) xs = f xs
  | _, .nil, _, _, [], _, _, _ => rfl
  | _, .cons _ B, f, R, x :: xs, hxs, hf, hR => by
    change applyN (app (lamR w _ _) x) xs = f (x :: xs)
    rw [app_lamR hxs.1 (B := fun y => piN w (B y) (fun ys => R (y :: ys)))
      (fun y hy => curry_mem (B y) (fun ys hys => hf (y :: ys) ⟨hy, hys⟩))
      (fun hw y hy => by
        subst w
        exact piN_zero_mem (B y) (fun ys hys => hR rfl (y :: ys) ⟨hy, hys⟩))]
    exact applyN_curry (B x) hxs.2
      (fun ys hys => hf (x :: ys) ⟨hxs.1, hys⟩)
      (fun hw ys hys => hR hw (x :: ys) ⟨hxs.1, hys⟩)

theorem curry_congr {w : Nat} : ∀ {n} (T : TeleS V n) {f g : List V → V},
    (∀ xs, FitsS T xs → f xs = g xs) → curry w T f = curry w T g
  | _, .nil, _, _, h => h [] trivial
  | _, .cons _ B, _, _, h =>
    lamR_congr fun x hx => curry_congr (B x) (fun xs hxs => h (x :: xs) ⟨hx, hxs⟩)

theorem piN_zero_agree {w w' : Nat} (hw : w = 0 ↔ w' = 0) :
    ∀ {n} (T : TeleS V n) {R R' : List V → V},
      (∀ xs, FitsS T xs → R xs = R' xs) → piN w T R = piN w' T R'
  | _, .nil, _, _, h => h [] trivial
  | _, .cons _ B, _, _, h =>
    piR_zero_agree hw fun x hx => piN_zero_agree hw (B x) (fun xs hxs => h (x :: xs) ⟨hx, hxs⟩)

theorem piN_congr {w : Nat} {n : Nat} (T : TeleS V n) {R R' : List V → V}
    (h : ∀ xs, FitsS T xs → R xs = R' xs) : piN w T R = piN w T R' :=
  piN_zero_agree Iff.rfl T h

theorem curry_zero_agree {w w' : Nat} (hw : w = 0 ↔ w' = 0) :
    ∀ {n} (T : TeleS V n) {f f' : List V → V},
      (∀ xs, FitsS T xs → f xs = f' xs) → curry w T f = curry w' T f'
  | _, .nil, _, _, h => h [] trivial
  | _, .cons _ B, _, _, h =>
    lamR_zero_agree hw fun x hx => curry_zero_agree hw (B x) (fun xs hxs => h (x :: xs) ⟨hx, hxs⟩)

theorem curry_point : ∀ {n} (T : TeleS V n), curry 0 T (fun _ => (pt : V)) = pt
  | _, .nil => rfl
  | _, .cons _ _ => lamR_zero

theorem curry_applyN {w : Nat} : ∀ {n} (T : TeleS V n) {f : V} {R : List V → V},
    f ∈ˢ piN w T R →
    (w = 0 → ∀ ys, FitsS T ys → R ys ∈ˢ (univZero : V)) →
      curry w T (applyN f) = f
  | _, .nil, _, _, _, _ => rfl
  | _, .cons _ B, _, R, hf, hR => by
    change lamR w _ (fun x => curry w (B x) (applyN (app _ x))) = _
    calc
      _ = lamR w _ (fun x => app _ x) := by
        apply lamR_congr
        intro x hx
        apply curry_applyN (B x) (R := fun ys => R (x :: ys))
          (app_mem_piR hf hx ?_)
        · intro hw ys hys
          exact hR hw (x :: ys) ⟨hx, hys⟩
        · intro hw y hy
          subst w
          exact piN_zero_mem (B y) (fun ys hys => hR rfl (y :: ys) ⟨hy, hys⟩)
      _ = _ := lamR_eta hf

/-- Tuple codes always preserve their fields, even when a family itself is
Prop-valued. The carrier bounds are needed only at positive sorts. -/
theorem tower_graph_mem {w : Nat} (hw : w ≠ 0) : ∀ {n} (T : TeleS V n),
    BoundS w T → towerSet 1 T ∈ˢ (univ w : V)
  | _, .nil, _ => unitSet_mem_univ w
  | _, .cons _ B, hB => by
    change sigmaSet 1 _ _ ∈ˢ (univ w : V)
    rw [sigmaSet_pos (by decide : 1 ≠ 0)]
    exact (univ_isTGUniverse hw).sigmaPairs_mem hB.1
      (fun x hx => tower_graph_mem hw (B x) (hB.2 x hx))

theorem piN_mem_univ {w : Nat} : ∀ {n} (T : TeleS V n) {R : List V → V},
    (w ≠ 0 → BoundS w T) → (∀ xs, FitsS T xs → R xs ∈ˢ (univ w : V)) →
      piN w T R ∈ˢ (univ w : V)
  | _, .nil, _, _, hR => hR [] trivial
  | _, .cons A B, R, hT, hR => by
    by_cases hw : w = 0
    · subst w
      exact univ_zero (V := V) ▸ piR_zero_mem_univZero
    · change piR w A (fun x => piN w (B x) (fun xs => R (x :: xs))) ∈ˢ (univ w : V)
      rw [piR_pos hw]
      apply (univ_isTGUniverse hw).piSet_mem (hT hw).1
      intro x hx
      exact piN_mem_univ (B x) (fun _ => (hT hw).2 x hx)
        (fun xs hxs => hR (x :: xs) ⟨hx, hxs⟩)

def simple : (domains : List V) → TeleS V domains.length
  | [] => .nil
  | A :: rest => .cons A (fun _ => simple rest)

theorem fits_simple_getD : ∀ {domains xs : List V}, FitsS (simple domains) xs →
    ∀ {i A}, domains[i]? = some A → xs.getD i empty ∈ˢ A
  | [], [], _, _, _, h => by simp at h
  | _ :: _, _ :: _, h, 0, _, hA => by
    cases Option.some.inj hA
    exact h.1
  | _ :: _, _ :: _, h, i + 1, _, hA => fits_simple_getD h.2 hA

theorem fits_simple_of_getD : ∀ {domains xs : List V}, xs.length = domains.length →
    (∀ i A, domains[i]? = some A → xs.getD i empty ∈ˢ A) → FitsS (simple domains) xs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, hlen, h =>
    ⟨h 0 _ rfl, fits_simple_of_getD (Nat.succ.inj hlen) (fun i A hA => h (i + 1) A hA)⟩

theorem fits_simple_map {α : Type u} (f : α → V) (domains : List α) (xs : List V)
    (hlen : xs.length = domains.length)
    (h : ∀ i a, domains[i]? = some a → xs.getD i empty ∈ˢ f a) :
    FitsS (simple (domains.map f)) xs := by
  apply fits_simple_of_getD (hlen.trans (List.length_map ..).symm)
  intro i A hA
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp
    ((List.getElem?_map (l := domains) (f := f)).symm.trans hA)
  exact h i a ha

theorem fits_unique_of_prop : ∀ {n} {T : TeleS V n} {xs ys : List V},
    PropS T → FitsS T xs → FitsS T ys → xs = ys
  | _, .nil, [], [], _, _, _ => rfl
  | _, .cons _ B, x :: xs, y :: ys, hT, hx, hy => by
    have he := subsingleton_of_mem_univZero hT.1 hx.1 hy.1
    subst y
    exact congrArg (x :: ·) (fits_unique_of_prop (T := B x) (hT.2 x hx.1) hx.2 hy.2)

variable {β : Type u}

def context (Γ : Context β) : List (AExpr β) → Context β
  | [] => Γ
  | A :: rest => context (Γ.push A) rest

def extend (env : Nat → V) : List V → Nat → V
  | [] => env
  | x :: xs => extend (Valuation.cons x env) xs

omit [SetTheory V] in
theorem extend_beyond (env : Nat → V) (xs : List V) (i : Nat) :
    extend env xs (xs.length + i) = env i := by
  induction xs generalizing env i with
  | nil => simp [extend]
  | cons x xs ih =>
    simpa only [extend, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Valuation.cons_succ] using ih (Valuation.cons x env) (i + 1)

theorem extend_getD (env : Nat → V) (xs : List V) (i : Nat) (hi : i < xs.length) :
    extend env xs (xs.length - 1 - i) = xs.getD i empty := by
  induction xs generalizing env i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simpa only [extend, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero,
        List.getD_cons_zero, Valuation.cons_zero, Nat.add_zero] using
        extend_beyond (Valuation.cons x env) xs 0
    | succ i =>
      have hidx : (x :: xs).length - 1 - (i + 1) = xs.length - 1 - i := by simp; omega
      rw [hidx]
      exact ih (Valuation.cons x env) i (by simpa using hi)

omit [SetTheory V] in
theorem skip_extend (env : Nat → V) (xs : List V) :
    Valuation.skip xs.length 0 (extend env xs) = env := by
  funext i
  simpa only [Valuation.skip, Nat.not_lt_zero, ↓reduceIte] using extend_beyond env xs i

omit [SetTheory V] in
theorem extend_append (env : Nat → V) (xs ys : List V) :
    extend env (xs ++ ys) = extend (extend env xs) ys := by
  induction xs generalizing env <;> simp_all [extend]

omit [SetTheory V] in
theorem skip_extend_at (env : Nat → V) (xs : List V) (count cutoff : Nat) :
    Valuation.skip count (xs.length + cutoff) (extend env xs) =
      extend (Valuation.skip count cutoff env) xs := by
  induction xs generalizing env cutoff with
  | nil => simp only [List.length_nil, Nat.zero_add, extend]
  | cons x xs ih =>
    simpa only [extend, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Valuation.skip_cons] using ih (Valuation.cons x env) (cutoff + 1)

omit [SetTheory V] in
theorem skip_middle (env : Nat → V) (middle tail : List V) :
    Valuation.skip middle.length tail.length (extend (extend env middle) tail) = extend env tail := by
  simpa only [Nat.add_zero, skip_extend] using skip_extend_at (extend env middle) tail middle.length 0

noncomputable def interpret (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) : (domains : List (AExpr β)) → TeleS V domains.length
  | [] => .nil
  | A :: rest => .cons (interp constants levels env A)
    (fun x => interpret constants levels (Valuation.cons x env) rest)

theorem piN_append (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (left right : List (AExpr β)) (w : Nat) (R : List V → V) :
    piN w (interpret constants levels env (left ++ right)) R =
      piN w (interpret constants levels env left) (fun xs =>
        piN w (interpret constants levels (extend env xs) right) (fun ys => R (xs ++ ys))) := by
  induction left generalizing env R with
  | nil => rfl
  | cons A rest ih =>
    change piR w _ _ = piR w _ _
    congr 1
    funext x
    exact ih (Valuation.cons x env) (fun xs => R (x :: xs))

theorem curry_append (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (left right : List (AExpr β)) (w : Nat) (f : List V → V) :
    curry w (interpret constants levels env (left ++ right)) f =
      curry w (interpret constants levels env left) (fun xs =>
        curry w (interpret constants levels (extend env xs) right) (fun ys => f (xs ++ ys))) := by
  induction left generalizing env f with
  | nil => rfl
  | cons A rest ih =>
    change lamR w _ _ = lamR w _ _
    congr 1
    funext x
    exact ih (Valuation.cons x env) (fun xs => f (x :: xs))

def lift (count : Nat) : List (AExpr β) → (cutoff : Nat := 0) → List (AExpr β)
  | [], _ => []
  | A :: rest, k => A.liftN count k :: lift count rest (k + 1)

def inst (arg : AExpr β) : List (AExpr β) → (cutoff : Nat := 0) → List (AExpr β)
  | [], _ => []
  | A :: rest, k => A.inst arg k :: inst arg rest (k + 1)

/-- A telescope of domains that all live in the same outer context. -/
def independent : List (AExpr β) → (offset : Nat := 0) → List (AExpr β)
  | [], _ => []
  | A :: rest, offset => A.liftN offset :: independent rest (offset + 1)

theorem piN_independent (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (domains : List (AExpr β)) (previous : List V) (w : Nat) (R : List V → V) :
    piN w (interpret constants levels (extend env previous) (independent domains previous.length)) R =
      piN w (simple (domains.map (interp constants levels env))) R := by
  induction domains generalizing previous R with
  | nil => rfl
  | cons A rest ih =>
    change piR w (interp constants levels (extend env previous) (A.liftN previous.length)) _ = piR w _ _
    rw [interp_liftN, skip_extend]
    congr 1
    funext x
    have ht := ih (previous ++ [x]) (fun xs => R (x :: xs))
    have hlen : (previous ++ [x]).length = previous.length + 1 := by simp
    rw [hlen] at ht
    simpa only [extend_append, extend] using ht

theorem curry_independent (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (domains : List (AExpr β)) (previous : List V) (w : Nat) (f : List V → V) :
    curry w (interpret constants levels (extend env previous) (independent domains previous.length)) f =
      curry w (simple (domains.map (interp constants levels env))) f := by
  induction domains generalizing previous f with
  | nil => rfl
  | cons A rest ih =>
    change lamR w (interp constants levels (extend env previous) (A.liftN previous.length)) _ = lamR w _ _
    rw [interp_liftN, skip_extend]
    congr 1
    funext x
    have ht := ih (previous ++ [x]) (fun xs => f (x :: xs))
    have hlen : (previous ++ [x]).length = previous.length + 1 := by simp
    rw [hlen] at ht
    simpa only [extend_append, extend] using ht

@[simp] theorem length_lift (count : Nat) (domains : List (AExpr β)) (k : Nat) :
    (lift count domains k).length = domains.length := by
  induction domains generalizing k <;> simp_all [lift]

@[simp] theorem length_inst (arg : AExpr β) (domains : List (AExpr β)) (k : Nat) :
    (inst arg domains k).length = domains.length := by
  induction domains generalizing k <;> simp_all [inst]

theorem fits_lift (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (count : Nat) (domains : List (AExpr β)) (k : Nat) (xs : List V) :
    FitsS (interpret constants levels env (lift count domains k)) xs ↔
      FitsS (interpret constants levels (Valuation.skip count k env) domains) xs := by
  induction domains generalizing env k xs with
  | nil => rfl
  | cons A rest ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [lift, interpret, FitsS, interp_liftN, ih, Valuation.skip_cons]

theorem fits_inst (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (arg : AExpr β) (domains : List (AExpr β)) (k : Nat) (xs : List V) :
    FitsS (interpret constants levels env (inst arg domains k)) xs ↔
      FitsS (interpret constants levels
        (Valuation.insert k (interp constants levels (Valuation.skip k 0 env) arg) env) domains) xs := by
  induction domains generalizing env k xs with
  | nil => rfl
  | cons A rest ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [inst, interpret, FitsS, interp_inst, ih,
        Valuation.skip_succ_cons, Valuation.insert_cons]

theorem piN_lift (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (count : Nat) (domains : List (AExpr β)) (cutoff w : Nat) (R : List V → V) :
    piN w (interpret constants levels env (lift count domains cutoff)) R =
      piN w (interpret constants levels (Valuation.skip count cutoff env) domains) R := by
  induction domains generalizing env cutoff R with
  | nil => rfl
  | cons A rest ih =>
    simp only [lift, interpret, piN, interp_liftN]
    congr 1
    funext x
    simpa only [Valuation.skip_cons] using ih (Valuation.cons x env) (cutoff + 1) (fun xs => R (x :: xs))

theorem curry_lift (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (count : Nat) (domains : List (AExpr β)) (cutoff w : Nat) (f : List V → V) :
    curry w (interpret constants levels env (lift count domains cutoff)) f =
      curry w (interpret constants levels (Valuation.skip count cutoff env) domains) f := by
  induction domains generalizing env cutoff f with
  | nil => rfl
  | cons A rest ih =>
    simp only [lift, interpret, curry, interp_liftN]
    congr 1
    funext x
    simpa only [Valuation.skip_cons] using ih (Valuation.cons x env) (cutoff + 1) (fun xs => f (x :: xs))

theorem piN_instL (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (sourceLevels : List VLevel) (domains : List (AExpr β)) (w : Nat) (R : List V → V) :
    piN w (interpret constants levels env (domains.map (AExpr.instL sourceLevels))) R =
      piN w (interpret constants (sourceLevels.map (VLevel.eval levels)) env domains) R := by
  induction domains generalizing env R with
  | nil => rfl
  | cons A rest ih =>
    change piR w (interp constants levels env (A.instL sourceLevels))
      (fun x => piN w (interpret constants levels (Valuation.cons x env)
        (rest.map (AExpr.instL sourceLevels))) (fun xs => R (x :: xs))) =
      piR w (interp constants (sourceLevels.map (VLevel.eval levels)) env A) _
    rw [interp_instL]
    congr 1
    funext x
    exact ih (Valuation.cons x env) (fun xs => R (x :: xs))

theorem curry_instL (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (sourceLevels : List VLevel) (domains : List (AExpr β)) (w : Nat) (f : List V → V) :
    curry w (interpret constants levels env (domains.map (AExpr.instL sourceLevels))) f =
      curry w (interpret constants (sourceLevels.map (VLevel.eval levels)) env domains) f := by
  induction domains generalizing env f with
  | nil => rfl
  | cons A rest ih =>
    change lamR w (interp constants levels env (A.instL sourceLevels))
      (fun x => curry w (interpret constants levels (Valuation.cons x env)
        (rest.map (AExpr.instL sourceLevels))) (fun xs => f (x :: xs))) =
      lamR w (interp constants (sourceLevels.map (VLevel.eval levels)) env A) _
    rw [interp_instL]
    congr 1
    funext x
    exact ih (Valuation.cons x env) (fun xs => f (x :: xs))

theorem fits_instL (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (sourceLevels : List VLevel) (domains : List (AExpr β)) (xs : List V) :
    FitsS (interpret constants levels env (domains.map (AExpr.instL sourceLevels))) xs ↔
      FitsS (interpret constants (sourceLevels.map (VLevel.eval levels)) env domains) xs := by
  induction domains generalizing env xs with
  | nil => rfl
  | cons A rest ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      change (x ∈ˢ interp constants levels env (A.instL sourceLevels) ∧
        FitsS (interpret constants levels (Valuation.cons x env) (rest.map (AExpr.instL sourceLevels))) xs) ↔ _
      simp only [interp_instL, ih, interpret, FitsS]

/-- Every field sort is derived by the same semantic typing relation as an
ordinary term. The executable producer checks each successive context. -/
inductive Formed (entries : Environment β) : Context β → List (AExpr β) → Prop
  | nil {Γ} : Formed entries Γ []
  | cons {Γ A rest} (level : VLevel)
      (domain : TypingClaim.{u,v} entries Γ A (.sort level))
      (tail : Formed entries (Γ.push A) rest) : Formed entries Γ (A :: rest)

theorem Formed.valid {entries : Environment β} {Γ : Context β} {domains : List (AExpr β)}
    (h : Formed.{u,v} entries Γ domains) (constants : Assignment β V)
    (hM : Realizes constants entries) (levels : List Nat) :
    ∀ {env xs}, Γ.Valid constants levels env → FitsS (interpret constants levels env domains) xs →
      (context Γ domains).Valid constants levels (extend env xs) := by
  induction h with
  | nil =>
    intro env xs hΓ hxs
    cases xs with
    | nil => exact hΓ
    | cons _ _ => exact hxs.elim
  | cons l hA hrest ih =>
    intro env xs hΓ hxs
    cases xs with
    | nil => exact hxs.elim
    | cons x xs =>
      exact ih (env := Valuation.cons x env) (xs := xs)
        (hΓ.push (hA V constants hM levels env hΓ).1 hxs.1) hxs.2

theorem Formed.append {entries : Environment β} {Γ : Context β} {left right : List (AExpr β)}
    (hl : Formed.{u,v} entries Γ left) (hr : Formed.{u,v} entries (context Γ left) right) :
    Formed.{u,v} entries Γ (left ++ right) := by
  induction hl with
  | nil => exact hr
  | cons l hA hrest ih => exact .cons l hA (ih hr)

end Ix.Theory.Model.Telescope

namespace Ix.Theory.Model.AExpr

open Certified
universe u v
variable {β : Type u}

def forallN (p : PropWhen) : List (AExpr β) → AExpr β → AExpr β
  | [], B => B
  | A :: rest, B => .forallE p A (forallN p rest B)

def lamN (p : PropWhen) : List (AExpr β) → AExpr β → AExpr β
  | [], body => body
  | A :: rest, body => .lam p A (lamN p rest body)

def appN (f : AExpr β) : List (AExpr β) → AExpr β
  | [] => f
  | x :: xs => appN (.app f x) xs

theorem forallN_append (p : PropWhen) (left right : List (AExpr β)) (B : AExpr β) :
    forallN p (left ++ right) B = forallN p left (forallN p right B) := by
  induction left <;> simp_all [forallN]

theorem lamN_append (p : PropWhen) (left right : List (AExpr β)) (body : AExpr β) :
    lamN p (left ++ right) body = lamN p left (lamN p right body) := by
  induction left <;> simp_all [lamN]

theorem appN_append (f : AExpr β) (left right : List (AExpr β)) :
    appN f (left ++ right) = appN (appN f left) right := by
  induction left generalizing f <;> simp_all [appN]

theorem ReferencesIn.forallN {entries : Environment β} {p : PropWhen}
    {domains : List (AExpr β)} {B : AExpr β}
    (hD : ∀ A ∈ domains, A.ReferencesIn entries) (hB : B.ReferencesIn entries) :
    (forallN p domains B).ReferencesIn entries := by
  induction domains with
  | nil => exact hB
  | cons A rest ih =>
    have hA := hD A (List.mem_cons_self ..)
    have ht := ih (fun D h => hD D (List.mem_cons_of_mem A h))
    intro r hr
    exact (List.mem_append.mp hr).elim (hA r) (ht r)

theorem ReferencesIn.lamN {entries : Environment β} {p : PropWhen}
    {domains : List (AExpr β)} {body : AExpr β}
    (hD : ∀ A ∈ domains, A.ReferencesIn entries) (hb : body.ReferencesIn entries) :
    (lamN p domains body).ReferencesIn entries := by
  induction domains with
  | nil => exact hb
  | cons A rest ih =>
    have hA := hD A (List.mem_cons_self ..)
    have ht := ih (fun D h => hD D (List.mem_cons_of_mem A h))
    intro r hr
    exact (List.mem_append.mp hr).elim (hA r) (ht r)

@[simp] theorem erase_forallN (p : PropWhen) (domains : List (AExpr β)) (B : AExpr β) :
    (forallN p domains B).erase = VExpr.forallN (domains.map erase) B.erase := by
  induction domains <;> simp_all [forallN, erase, VExpr.forallN]

@[simp] theorem erase_lamN (p : PropWhen) (domains : List (AExpr β)) (B : AExpr β) :
    (lamN p domains B).erase = VExpr.lamN (domains.map erase) B.erase := by
  induction domains <;> simp_all [lamN, erase, VExpr.lamN]

@[simp] theorem erase_appN (f : AExpr β) (args : List (AExpr β)) :
    (appN f args).erase = VExpr.appN f.erase (args.map erase) := by
  induction args generalizing f <;> simp_all [appN, erase, VExpr.appN]

variable {V : Type v} [SetTheory V]

theorem interp_forallN (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (p : PropWhen) (domains : List (AExpr β)) (B : AExpr β) :
    interp constants levels env (forallN p domains B) =
      Telescope.piN (regime p levels) (Telescope.interpret constants levels env domains)
        (fun xs => interp constants levels (Telescope.extend env xs) B) := by
  induction domains generalizing env with
  | nil => rfl
  | cons A rest ih =>
    simp only [forallN, interp, Telescope.interpret, Telescope.piN, Telescope.extend, ih]

theorem interp_lamN (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (p : PropWhen) (domains : List (AExpr β)) (body : AExpr β) :
    interp constants levels env (lamN p domains body) =
      Telescope.curry (regime p levels) (Telescope.interpret constants levels env domains)
        (fun xs => interp constants levels (Telescope.extend env xs) body) := by
  induction domains generalizing env with
  | nil => rfl
  | cons A rest ih =>
    simp only [lamN, interp, Telescope.interpret, Telescope.curry, Telescope.extend, ih]

theorem interp_appN (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (f : AExpr β) (args : List (AExpr β)) :
    interp constants levels env (appN f args) =
      Telescope.applyN (interp constants levels env f) (args.map (interp constants levels env)) := by
  induction args generalizing f <;> simp_all [appN, interp, Telescope.applyN]

end Ix.Theory.Model.AExpr

namespace Ix.Theory.Model.Telescope

open Certified
universe u v
variable {β : Type u}

/-- Formed domains give formation of the entire product telescope. Every
outer binder has the zero condition of the final result sort. -/
theorem Formed.forallN {entries : Environment β} {Γ : Context β} {domains : List (AExpr β)}
    (h : Formed.{u,v} entries Γ domains) {B : AExpr β} {b : VLevel}
    (hB : TypingClaim.{u,v} entries (context Γ domains) B (.sort b)) :
    ∃ l, zeroCondition l = zeroCondition b ∧
      TypingClaim.{u,v} entries Γ (.forallN (zeroCondition b) domains B) (.sort l) := by
  induction h with
  | nil => exact ⟨b, rfl, hB⟩
  | cons a hA hrest ih =>
    obtain ⟨l, hl, htail⟩ := ih hB
    exact ⟨.imax a l, hl, TypingClaim.forallE hA htail hl.symm⟩

end Ix.Theory.Model.Telescope
