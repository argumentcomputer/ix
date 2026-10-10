import Ix.CompileCert.Opt.O4

/-!
# M7 L3-def: totality of the definitional passes (some, or a named decline)

The passes are `Option`-valued: they never fail, they fire or decline. **Totality on the
domain** is the statement that a decline is exactly a failed side condition, the docstring's
list (`O1.Side`, `O3.Side`, `O4.Side`, `O6.Side`):

* `O1_of_side`, `O3_of_side`, `O4_of_side`, `O6_of_side`: the side condition holds ⇒ the pass
  fires (for the selections, given that the block's shapes are within Lean's ranges,
  `ShapesWF`: what `readShape` checks);
* `O1_none_iff`, `O3_none_iff`, `O4_none_iff`, `O6_none_iff`: the pass declines **iff** its
  side condition fails, so every decline has a name: the first conjunct of the side condition
  that fails.

`O4.Side` and `O4_side` are stated here (O4's firing decomposition is `O4_some`). The walk
mirrors the decomposition: `obind_ex` (a bind whose argument succeeded), `oguard_ex` (a guard
that passes).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-! ## The walk forwards -/

theorem obind_ex {α β : Type} {x : Option α} {a : α} {f : α → Option β}
    (hx : x = some a) (hf : ∃ b, f a = some b) : ∃ b, (x >>= f) = some b := by
  subst hx; exact hf

theorem oguard_ex {c : Prop} [Decidable c] {α β : Type} {f : α → Option β} {r : Option β}
    (hc : ¬ c) (hr : ∃ e, r = some e) : ∃ e, (if c then (none >>= f) else r) = some e := by
  simp only [hc, ↓reduceIte]; exact hr

theorem bnot_true_false {b : Bool} (h : b = true) : ¬ (!b) = true := by
  subst h; decide

theorem bool_ne_true {b : Bool} (h : b = false) : ¬ b = true := by
  subst h; decide

theorem not_lt_of_le' {m n : Nat} (h : n ≤ m) : ¬ m < n := Nat.not_lt.2 h

/-! ## Picks in range succeed -/

theorem pick_some_list {xs : Array Expr} : ∀ {src : List Nat}, (∀ p ∈ src, p < xs.size) →
    ∃ ys, src.mapM (xs[·]?) = some ys
  | [], _ => ⟨[], rfl⟩
  | p :: src, h => by
    obtain ⟨ys, hys⟩ := pick_some_list (src := src) (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp : p < xs.size := h p (List.mem_cons_self ..)
    refine ⟨xs[p] :: ys, ?_⟩
    simp only [List.mapM_cons, Array.getElem?_eq_getElem hp, hys]
    rfl

theorem pick_some {xs : Array Expr} {src : Array Nat} (h : ∀ p ∈ src.toList, p < xs.size) :
    ∃ ys, pick xs src = some ys := by
  obtain ⟨ys, hys⟩ := pick_some_list h
  refine ⟨ys.toArray, ?_⟩
  unfold Ix.Compile.Pass.Opt.pick
  rw [Array.mapM_eq_mapM_toList, hys]
  rfl

theorem pick_extract_some {a : Array Expr} {i j : Nat} {src : Array Nat} (hj : j ≤ a.size)
    (h : ∀ p ∈ src.toList, p < j - i) : ∃ ys, pick (a.extract i j) src = some ys :=
  pick_some (fun p hp => by have := h p hp; rw [Array.size_extract]; omega)

/-- The shapes of `env`'s blocks are within Lean's ranges (what `readShape` checks). -/
def ShapesWF (env : OptEnv) : Prop :=
  ∀ h b r s, env.blockOf h = some b → b.shapes.get? r = some s → ShapeWF s

theorem motives_lt {s : RecShape} (hw : ShapeWF s) {i : Nat} :
    ∀ p ∈ s.motiveSrc.toList, p < (i + s.nm) - i :=
  fun p hp => by have := hw.motives p hp; omega

theorem minors_lt {s : RecShape} (hw : ShapeWF s) {i : Nat} :
    ∀ p ∈ (s.minorSrc.filterMap id).toList, p < (i + s.nmin) - i := by
  intro p hp
  rw [Array.toList_filterMap] at hp
  have := hw.minors p hp
  omega

/-! ## O1 -/

theorem O1_of_side {env : OptEnv} {o : Occ} (hwf : ShapesWF env) (h : O1.Side env o) :
    ∃ e, O1.apply env o = some e := by
  obtain ⟨k, r, b, s, ls, hc, hk, hb, hp, hs, hisp, hn, hsz, hls, hon⟩ := h
  have hw := hwf o.head b r s hb hs
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  unfold O1.apply
  refine obind_ex hc ?_
  try dsimp only
  rcases hk with rfl | rfl
  · refine oguard_ex (by decide) ?_
    refine obind_ex hb ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hp) ?_
    refine obind_ex hs ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hisp) ?_
    refine obind_ex hn ?_
    try dsimp only
    refine oguard_ex (not_lt_of_le' hsz) ?_
    refine obind_ex hls ?_
    try dsimp only
    obtain ⟨ms', hms⟩ := pick_extract_some (a := o.args) (i := s.np) (j := s.np + s.nm)
      (by omega) (motives_lt hw)
    obtain ⟨mins', hmins⟩ := pick_extract_some (a := o.args) (i := s.np + s.nm)
      (j := s.np + s.nm + s.nmin) (by omega) (minors_lt hw)
    refine obind_ex hms ?_
    try dsimp only
    refine obind_ex hmins ?_
    exact ⟨_, rfl⟩
  · obtain ⟨ixRecOn, hixa, hres⟩ := hon rfl
    refine oguard_ex (by decide) ?_
    refine obind_ex hb ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hp) ?_
    refine obind_ex hs ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hisp) ?_
    refine obind_ex hn ?_
    try dsimp only
    refine oguard_ex (not_lt_of_le' hsz) ?_
    refine obind_ex hls ?_
    try dsimp only
    refine obind_ex hixa ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hres) ?_
    obtain ⟨ms', hms⟩ := pick_extract_some (a := o.args) (i := s.np) (j := s.np + s.nm)
      (by omega) (motives_lt hw)
    obtain ⟨mins', hmins⟩ := pick_extract_some (a := o.args) (i := s.np + s.nm + s.ni + 1)
      (j := s.arity) (src := s.minorSrc.filterMap id) (by omega)
      (fun p hp => by have := minors_lt hw (i := s.np + s.nm + s.ni + 1) p hp; rw [har]; omega)
    refine obind_ex hms ?_
    try dsimp only
    refine obind_ex hmins ?_
    exact ⟨_, rfl⟩

/-- **O1 declines iff its side condition fails.** -/
theorem O1_none_iff {env : OptEnv} {o : Occ} (hwf : ShapesWF env) :
    O1.apply env o = none ↔ ¬ O1.Side env o := by
  constructor
  · intro h hs
    obtain ⟨e, he⟩ := O1_of_side hwf hs
    rw [h] at he; cases he
  · intro hn
    cases he : O1.apply env o with
    | none => rfl
    | some e => exact absurd (O1_side he) hn

/-! ## O6 -/

theorem O6_of_side {env : OptEnv} {o : Occ} (hwf : ShapesWF env) (h : O6.Side env o) :
    ∃ e, O6.apply env o = some e := by
  obtain ⟨k, r, b, s, ls, hc, hk, hb, hs, hsel, hn, hsz, hls, hon⟩ := h
  have hw := hwf o.head b r s hb hs
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  obtain ⟨ms', hms⟩ := pick_extract_some (a := o.args) (i := s.np) (j := s.np + s.nm)
    (by omega) (motives_lt hw)
  unfold O6.apply
  refine obind_ex hc ?_
  try dsimp only
  rcases hk with rfl | rfl
  · refine oguard_ex (by decide) ?_
    refine obind_ex hb ?_
    try dsimp only
    refine obind_ex hs ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hsel) ?_
    refine obind_ex hn ?_
    try dsimp only
    refine oguard_ex (not_lt_of_le' hsz) ?_
    refine obind_ex hls ?_
    try dsimp only
    refine obind_ex hms ?_
    try dsimp only
    obtain ⟨mins', hmins⟩ := pick_extract_some (a := o.args) (i := s.np + s.nm)
      (j := s.np + s.nm + s.nmin) (by omega) (minors_lt hw)
    simp only [show (AuxKind.kRec == AuxKind.kRec) = true from rfl, ↓reduceIte]
    refine obind_ex hmins ?_
    exact ⟨_, rfl⟩
  · obtain ⟨ixRecOn, hixa, hres⟩ := hon rfl
    refine oguard_ex (by decide) ?_
    refine obind_ex hb ?_
    try dsimp only
    refine obind_ex hs ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hsel) ?_
    refine obind_ex hn ?_
    try dsimp only
    refine oguard_ex (not_lt_of_le' hsz) ?_
    refine obind_ex hls ?_
    try dsimp only
    refine obind_ex hms ?_
    try dsimp only
    obtain ⟨mins', hmins⟩ := pick_extract_some (a := o.args) (i := s.np + s.nm + s.ni + 1)
      (j := s.arity) (src := s.minorSrc.filterMap id) (by omega)
      (fun p hp => by have := minors_lt hw (i := s.np + s.nm + s.ni + 1) p hp; rw [har]; omega)
    simp only [show ¬ (AuxKind.kRecOn == AuxKind.kRec) = true by decide]
    refine obind_ex hixa ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hres) ?_
    refine obind_ex hmins ?_
    exact ⟨_, rfl⟩

/-- **O6 declines iff its side condition fails.** -/
theorem O6_none_iff {env : OptEnv} {o : Occ} (hwf : ShapesWF env) :
    O6.apply env o = none ↔ ¬ O6.Side env o := by
  constructor
  · intro h hs
    obtain ⟨e, he⟩ := O6_of_side hwf hs
    rw [h] at he; cases he
  · intro hn
    cases he : O6.apply env o with
    | none => rfl
    | some e => exact absurd (O6_side he) hn

/-! ## O3 (no shape bound needed: O3 passes the arguments as they are) -/

theorem O3_of_side {env : OptEnv} {o : Occ} (h : O3.Side env o) : ∃ e, O3.apply env o = some e := by
  obtain ⟨r, x, b, s, iv, ls, ixCases, hc, hx, hb, hcol, ⟨cls, hcls, hcs⟩, hs, hiv, hn, hsz, hls,
    hix, hres⟩ := h
  unfold O3.apply
  refine obind_ex hc ?_
  try dsimp only
  refine oguard_ex (by decide) ?_
  refine obind_ex hx ?_
  try dsimp only
  refine obind_ex hb ?_
  try dsimp only
  refine oguard_ex (bool_ne_true hcol) ?_
  refine obind_ex hcls ?_
  try dsimp only
  refine oguard_ex (by simp only [hcs, bne_self_eq_false]; decide) ?_
  refine obind_ex hs ?_
  try dsimp only
  rw [hiv]
  try dsimp only
  refine obind_ex hn ?_
  try dsimp only
  refine oguard_ex (not_lt_of_le' hsz) ?_
  refine obind_ex hls ?_
  try dsimp only
  refine obind_ex hix ?_
  try dsimp only
  refine oguard_ex (bnot_true_false hres) ?_
  exact ⟨_, rfl⟩

/-- **O3 declines iff its side condition fails.** -/
theorem O3_none_iff {env : OptEnv} {o : Occ} : O3.apply env o = none ↔ ¬ O3.Side env o := by
  constructor
  · intro h hs
    obtain ⟨e, he⟩ := O3_of_side hs
    rw [h] at he; cases he
  · intro hn
    cases he : O3.apply env o with
    | none => rfl
    | some e => exact absurd (O3_side he) hn

/-! ## O4 -/

/-- **O4's side condition** (the docstring's list, every check the code makes). -/
def O4.Side (env : OptEnv) (o : Occ) : Prop :=
  ∃ k r b s ls ixA, classify o.head = some (k, r) ∧
    (k = .kBelow ∨ k = .kBRecOn ∨ k = .kGo ∨ k = .kEq) ∧
    env.blockOf o.head = some b ∧ b.change.collapse = false ∧ b.shapes.get? r = some s ∧
    s.isSelection = true ∧ standardTelescope env s k o.head = some (o4Len s (o4Hd k)) ∧
    o4Len s (o4Hd k) ≤ o.args.size ∧ O5.levels s o.us = some ls ∧
    ixAuxOf s.ixRec k = some ixA ∧ env.resolves ixA = true ∧
    (k ≠ .kBelow → ∃ d, env.const? (belowNameOf r) = some (.defnInfo d))

theorem O4_side {env : OptEnv} {o : Occ} {e : Expr} (h : O4.apply env o = some e) : O4.Side env o := by
  obtain ⟨k, r, b, s, ls, ixA, _, _, hc, hk, hb, hcol, hs, hsel, hn, hsz, hls, hix, hres, hbel, -⟩ :=
    O4_some h
  exact ⟨k, r, b, s, ls, ixA, hc, hk, hb, hcol, hs, hsel, hn, hsz, hls, hix, hres, hbel⟩

theorem O4_of_side {env : OptEnv} {o : Occ} (hwf : ShapesWF env) (h : O4.Side env o) :
    ∃ e, O4.apply env o = some e := by
  obtain ⟨k, r, b, s, ls, ixA, hc, hk, hb, hcol, hs, hsel, hn, hsz, hls, hix, hres, hbel⟩ := h
  have hw := hwf o.head b r s hb hs
  obtain ⟨ms', hms⟩ := pick_extract_some (a := o.args) (i := s.np) (j := s.np + s.nm)
    (by cases hd : o4Hd k <;> rw [hd] at hsz <;> simp only [o4Len] at hsz <;> omega) (motives_lt hw)
  unfold O4.apply
  refine obind_ex hc ?_
  try dsimp only
  rcases hk with rfl | rfl | rfl | rfl
  · refine oguard_ex (by decide) ?_
    refine obind_ex hb ?_
    try dsimp only
    refine oguard_ex (bool_ne_true hcol) ?_
    refine obind_ex hs ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hsel) ?_
    refine obind_ex hn ?_
    try dsimp only
    refine oguard_ex (not_lt_of_le' hsz) ?_
    refine obind_ex hls ?_
    try dsimp only
    refine obind_ex hix ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hres) ?_
    simp only [show ¬ (AuxKind.kBelow != AuxKind.kBelow) = true by decide]
    refine obind_ex hms ?_
    try dsimp only
    exact ⟨_, rfl⟩
  all_goals
    obtain ⟨d, hd⟩ := hbel (fun h => nomatch h)
    obtain ⟨hs', hhs⟩ := pick_extract_some (a := o.args) (i := s.np + s.nm + s.ni + 1)
      (j := o4Len s true) (src := s.motiveSrc) (by simp only [o4Hd, o4Len] at hsz ⊢; omega)
      (fun p hp => by have := motives_lt hw (i := s.np + s.nm + s.ni + 1) p hp; simp only [o4Len]; omega)
    refine oguard_ex (by decide) ?_
    refine obind_ex hb ?_
    try dsimp only
    refine oguard_ex (bool_ne_true hcol) ?_
    refine obind_ex hs ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hsel) ?_
    refine obind_ex hn ?_
    try dsimp only
    refine oguard_ex (not_lt_of_le' hsz) ?_
    refine obind_ex hls ?_
    try dsimp only
    refine obind_ex hix ?_
    try dsimp only
    refine oguard_ex (bnot_true_false hres) ?_
    simp only [show (AuxKind.kBRecOn != AuxKind.kBelow) = true from rfl,
      show (AuxKind.kGo != AuxKind.kBelow) = true from rfl,
      show (AuxKind.kEq != AuxKind.kBelow) = true from rfl, ↓reduceIte, hd]
    try dsimp only
    refine obind_ex hms ?_
    try dsimp only
    simp only [show ¬ (AuxKind.kBRecOn == AuxKind.kBelow) = true by decide,
      show ¬ (AuxKind.kGo == AuxKind.kBelow) = true by decide,
      show ¬ (AuxKind.kEq == AuxKind.kBelow) = true by decide]
    refine obind_ex hhs ?_
    exact ⟨_, rfl⟩

/-- **O4 declines iff its side condition fails.** -/
theorem O4_none_iff {env : OptEnv} {o : Occ} (hwf : ShapesWF env) :
    O4.apply env o = none ↔ ¬ O4.Side env o := by
  constructor
  · intro h hs
    obtain ⟨e, he⟩ := O4_of_side hwf hs
    rw [h] at he; cases he
  · intro hn
    cases he : O4.apply env o with
    | none => rfl
    | some e => exact absurd (O4_side he) hn

end Ix.CompileCert.Opt
