import IxVMRefinement.Core.Open
import IxVMRefinement.Core.Loaded
import IxVMRefinement.Core.Specs.Infer
import IxC.Kernel.Rules.Inversion
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.PropWhen

/-! # Closing a binder, and the kernel-term facts inference reads

* **Abstraction commutes with lifting and with capture-avoiding instantiation**
  (`abstract1_liftLooseBVars`, `abstract1_instantiate1Lift`): closing the variable `d` at the
  bound index `k` passes through a lift of the loose bound variables at a cutoff `c ≤ k`, and
  through an instantiation `instantiate1Lift`, the value closed one binder further out.
* **Closing a binder** (`Tm.close`, the inverse of `Tm.open`): a term represented one opening
  depth deeper is represented, one local binder deeper, by its abstraction of the variable `d`
  at `k`.
* **λ-data** (`lamPw_instantiate1_fvar`, `infer_lam_type`, `pw_of_lam_sortPw`): instantiating at
  a variable keeps a term's λ-datum; a λ's inferred type is a `∀` with the λ's binder datum; the
  sort zero-ness of that type is the datum.
* **Positional levels** (`posOf_instantiateLevelParams`): instantiating the positional form of a
  term (`posOf`) at `List.range n` is instantiating the term at its own parameters. -/

namespace IxVM.Refinement.Core.InferAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel (Expr)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Abstraction against lifting and instantiation -/

/-- **Abstraction passes through a lift** of the loose bound variables at a cutoff at or below
the abstraction index. -/
theorem abstract1_liftLooseBVars {n d : Nat} :
    ∀ {V : KExpr} {c k : Nat}, c ≤ k →
      (V.liftLooseBVars n c).abstract1 d (k + n) = (V.abstract1 d k).liftLooseBVars n c := by
  intro V
  induction V with
  | bvar i =>
    intro c k _
    show Expr.abstract1 (if i ≥ c then (.bvar (i + n) : KExpr) else .bvar i) d (k + n) =
      (if i ≥ c then (.bvar (i + n) : KExpr) else .bvar i)
    by_cases h : i ≥ c
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; rfl
  | fvar idx ty _ =>
    intro c k hck
    show (if idx = d then (.bvar (k + n) : KExpr) else .fvar idx ty) =
      Expr.liftLooseBVars n c (if idx = d then (.bvar k : KExpr) else .fvar idx ty)
    by_cases h : idx = d
    · rw [ite_eq_left h, ite_eq_left h]
      show _ = (if k ≥ c then (.bvar (k + n) : KExpr) else .bvar k)
      rw [ite_eq_left (show k ≥ c from hck)]
    · rw [ite_eq_right h, ite_eq_right h]; rfl
  | sort _ | const _ _ | lit _ => intro c k _; rfl
  | app f a ihf iha =>
    intro c k hck
    simp only [Expr.liftLooseBVars, Expr.abstract1, ihf hck, iha hck]
  | lam ty body m iht ihb =>
    intro c k hck
    have hb := ihb (c := c + 1) (k := k + 1) (by omega)
    rw [show k + 1 + n = k + n + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, Expr.abstract1, iht hck, hb]
  | forallE ty body m iht ihb =>
    intro c k hck
    have hb := ihb (c := c + 1) (k := k + 1) (by omega)
    rw [show k + 1 + n = k + n + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, Expr.abstract1, iht hck, hb]
  | letE ty val body l iht ihv ihb =>
    intro c k hck
    have hb := ihb (c := c + 1) (k := k + 1) (by omega)
    rw [show k + 1 + n = k + n + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, Expr.abstract1, iht hck, ihv hck, hb]
  | proj s i e ih =>
    intro c k hck
    simp only [Expr.liftLooseBVars, Expr.abstract1, ih hck]

/-- **Abstraction passes through a capture-avoiding instantiation**: closing `d` at `k + j` after
instantiating the loose variable `j` by `V` is instantiating, after closing `d` one index
further out, by `V` closed at `k`. -/
theorem abstract1_instantiate1Lift {V : KExpr} {d k : Nat} :
    ∀ {B : KExpr} {j : Nat}, (B.instantiate1Lift V j).abstract1 d (k + j) =
      (B.abstract1 d (k + j + 1)).instantiate1Lift (V.abstract1 d k) j := by
  intro B
  induction B with
  | bvar i =>
    intro j
    show Expr.abstract1 (if i = j then Expr.liftLooseBVars j 0 V
        else if i > j then (.bvar (i - 1) : KExpr) else .bvar i) d (k + j) =
      (if i = j then Expr.liftLooseBVars j 0 (V.abstract1 d k)
        else if i > j then (.bvar (i - 1) : KExpr) else .bvar i)
    by_cases h : i = j
    · rw [ite_eq_left h, ite_eq_left h]
      exact abstract1_liftLooseBVars (Nat.zero_le k)
    · rw [ite_eq_right h, ite_eq_right h]
      by_cases h' : i > j
      · rw [ite_eq_left h']; rfl
      · rw [ite_eq_right h']; rfl
  | fvar idx ty _ =>
    intro j
    show (if idx = d then (.bvar (k + j) : KExpr) else .fvar idx ty) =
      Expr.instantiate1Lift (if idx = d then (.bvar (k + j + 1) : KExpr) else .fvar idx ty)
        (V.abstract1 d k) j
    by_cases h : idx = d
    · rw [ite_eq_left h, ite_eq_left h]
      show _ = (if k + j + 1 = j then Expr.liftLooseBVars j 0 (V.abstract1 d k)
        else if k + j + 1 > j then (.bvar (k + j + 1 - 1) : KExpr) else .bvar (k + j + 1))
      rw [ite_eq_right (show ¬(k + j + 1 = j) by omega),
        ite_eq_left (show k + j + 1 > j by omega), Nat.add_sub_cancel]
    · rw [ite_eq_right h, ite_eq_right h]; rfl
  | sort _ | const _ _ | lit _ => intro j; rfl
  | app f a ihf iha =>
    intro j
    simp only [Expr.instantiate1Lift, Expr.abstract1, ihf, iha]
  | lam ty body m iht ihb =>
    intro j
    have hb := @ihb (j + 1)
    rw [show k + (j + 1) = k + j + 1 by omega] at hb
    simp only [Expr.instantiate1Lift, Expr.abstract1, iht, hb]
  | forallE ty body m iht ihb =>
    intro j
    have hb := @ihb (j + 1)
    rw [show k + (j + 1) = k + j + 1 by omega] at hb
    simp only [Expr.instantiate1Lift, Expr.abstract1, iht, hb]
  | letE ty val body l iht ihv ihb =>
    intro j
    have hb := @ihb (j + 1)
    rw [show k + (j + 1) = k + j + 1 by omega] at hb
    simp only [Expr.instantiate1Lift, Expr.abstract1, iht, ihv, hb]
  | proj s i e ih =>
    intro j
    simp only [Expr.instantiate1Lift, Expr.abstract1, ih]

/-! ## λ-data -/

/-- **Instantiating at a variable keeps the λ-datum.** -/
theorem lamPw_instantiate1_fvar {B : KExpr} {i : Nat} {T : KExpr} {k : Nat} :
    (B.instantiate1 (.fvar i T) k).lamPw = B.lamPw := by
  cases B with
  | bvar j =>
    show (if j = k then (.fvar i T : KExpr)
      else if j > k then .bvar (j - 1) else .bvar j).lamPw = none
    by_cases h : j = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]
      by_cases h' : j > k
      · rw [ite_eq_left h']; rfl
      · rw [ite_eq_right h']; rfl
  | _ => rfl

/-- **A λ's inferred type is a `∀`** over the λ's domain, with the λ's binder datum. -/
theorem infer_lam_type {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade} {d : Nat}
    {ty body t : KExpr} {mb : Ix.Kernel.BinderMeta}
    (h : Ix.Kernel.Rules.Infer env g d (.lam ty body mb) t) :
    ∃ bt : KExpr, t = .forallE ty (bt.abstract1 d) mb := by
  cases h
  exact ⟨_, rfl⟩

/-- **The sort zero-ness of a λ's type is the λ's datum**: the type is a `∀` carrying the datum,
whose sort is an `imax` with the codomain sort, and an `imax`'s zero-ness is its right side's. -/
theorem pw_of_lam_sortPw {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade} {d : Nat}
    {T' B' BT : KExpr} {m' : Ix.Kernel.BinderMeta} {pw : Ix.Kernel.PropWhen}
    (hi : Ix.Kernel.Rules.Infer env g d (.lam T' B' m') BT)
    (hs : Specs.Infer.SortPw env d BT pw) : pw = m'.pw := by
  obtain ⟨bt, rfl⟩ := infer_lam_type hi
  obtain ⟨s, v, hinf, hred, hz⟩ := hs
  obtain ⟨_, u, _, v', _, _, _, _, hz', rfl⟩ := Ix.Kernel.Rules.Infer.forallE_inv hinf
  have hv : v = .imax u v' := Ix.Kernel.Rules.Red.sort_eq hred
  subst hv
  exact hz.symm.trans hz'

/-! ## Positional levels -/

/-- **Composition of level-parameter instantiations** on a term whose parameters are covered by
the inner substitution's. -/
theorem instantiateLevelParams_comp {ks : List Ix.Kernel.LevelParam} {us : List KLevel}
    {ps : List Ix.Kernel.LevelParam} {vs : List KLevel} (hl : vs.length = ps.length) :
    ∀ {e : KExpr}, e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps vs).instantiateLevelParams ks us =
        e.instantiateLevelParams ps (vs.map (Ix.Kernel.Level.subst ks us)) := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | fvar idx ty ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]
  | sort u =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams,
      Ix.Kernel.Level.subst_subst (ks := ks) (us := us) hl h]
  | const n ls =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun u hu =>
      Ix.Kernel.Level.subst_subst (ks := ks) (us := us) hl (h u hu)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Ix.Kernel.Level.substPW_comp (ks := ks) (us := us) hl h.2]
  | forallE ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihb h.1.2,
      Ix.Kernel.Level.substPW_comp (ks := ks) (us := us) hl h.2]
  | letE ty val body l iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | lit _ => intro _; rfl
  | proj s i e ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, ih h]

/-- `Level.subst.go` over the positions `s, s+1, …`: position `i` reads the `(i - s)`-th
replacement. -/
theorem getElem?_subst_go_range' :
    ∀ (s : Nat) (us : List KLevel) (i : Nat), s ≤ i → i < s + us.length →
      us[i - s]? = some (Ix.Kernel.Level.subst.go (List.range' s us.length) us i)
  | s, [], i, h1, h2 => by
    have : ([] : List KLevel).length = 0 := rfl
    omega
  | s, u :: us, i, h1, h2 => by
    show _ = some (if s = i then u else Ix.Kernel.Level.subst.go (List.range' (s + 1) us.length) us i)
    have hl : (u :: us).length = us.length + 1 := rfl
    by_cases h : s = i
    · subst h
      rw [ite_eq_left rfl, Nat.sub_self, List.getElem?_cons_zero]
    · rw [ite_eq_right h, show i - s = i - (s + 1) + 1 by omega, List.getElem?_cons_succ]
      exact getElem?_subst_go_range' (s + 1) us i (by omega) (by omega)

/-- `Level.subst.go` over the positions `0, …, n - 1`: position `i` reads the `i`-th
replacement. -/
theorem getElem?_eq_subst_go_range {us : List KLevel} {i : Nat} (hi : i < us.length) :
    us[i]? = some (Ix.Kernel.Level.subst.go (List.range us.length) us i) := by
  have := getElem?_subst_go_range' 0 us i (Nat.zero_le i) (by omega)
  rwa [Nat.sub_zero, ← List.range_eq_range'] at this

/-- **The positional levels, instantiated positionally, are the replacements.** -/
theorem posLevels_map_subst {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hlen : us.length = ps.length) :
    (posLevels ps).map (Ix.Kernel.Level.subst (List.range us.length) us) = us := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < us.length
  · have h1 : (posLevels ps)[i]? = some (Ix.Kernel.Level.param i) := by
      rw [posLevels, List.getElem?_map, List.getElem?_range (by omega)]; rfl
    rw [h1, getElem?_eq_subst_go_range hi]; rfl
  · have h1 : (posLevels ps)[i]? = none := by
      rw [List.getElem?_eq_none_iff, posLevels, List.length_map, List.length_range]
      omega
    have h2 : us[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h1, h2]; rfl

/-- **Instantiating a positional term positionally**: the positional form of `T` (`posOf ps T`)
instantiated at `List.range n` by `us` is `T` instantiated at its own parameters `ps` by `us`. -/
theorem posOf_instantiateLevelParams {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    {T : KExpr} (hnd : ps.Nodup) (hlen : us.length = ps.length)
    (hdef : T.allLevelParamsDefined ps = true) :
    (posOf ps T).instantiateLevelParams (List.range us.length) us =
      T.instantiateLevelParams ps us := by
  have hl : (posLevels ps).length = ps.length := by
    rw [posLevels, List.length_map, List.length_range]
  unfold posOf
  rw [instantiateLevelParams_comp hl hdef, posLevels_map_subst hlen]

end IxVM.Refinement.Core.InferAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel (Expr)

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- **Closing a binder** (the inverse of `Tm.open`): a term represented at opening depth `d + 1`
under a ghost context agreeing with `Γ` below `d` is represented, at opening depth `d` and one
local binder deeper, by its abstraction of the variable `d` at `k`. -/
theorem Tm.close {κ : _root_.Address → KKey} {d : Nat} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (hΓ : ∀ j, j < d → Γ' j = Γ j)
    (rep : Tm κ (d + 1) Γ' h k E p) : Tm κ d Γ h (k + 1) (E.abstract1 d k) p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs (by omega)
  | @bvarFree k addr i cell hs hk hd =>
    show Tm κ d Γ h (k + 1)
      (if fvIdx (d + 1) k (ZMod.val i) = d then .bvar k
        else .fvar (fvIdx (d + 1) k (ZMod.val i)) (Γ' (fvIdx (d + 1) k (ZMod.val i)))) _
    by_cases hik : ZMod.val i = k
    · have e : fvIdx (d + 1) k (ZMod.val i) = d := by unfold fvIdx; omega
      rw [ite_eq_left e]
      have hb := Tm.bvarLocal (κ := κ) (d := d) (Γ := Γ) (k := k + 1) cell hs (by omega)
      rw [hik] at hb
      exact hb
    · have e : ¬(fvIdx (d + 1) k (ZMod.val i) = d) := by unfold fvIdx; omega
      rw [ite_eq_right e]
      have hf := Tm.bvarFree (κ := κ) (d := d) (Γ := Γ) (k := k + 1) cell hs (by omega) (by omega)
      have e2 : fvIdx d (k + 1) (ZMod.val i) = fvIdx (d + 1) k (ZMod.val i) := by
        unfold fvIdx; omega
      rw [e2, ← hΓ (fvIdx (d + 1) k (ZMod.val i)) (by unfold fvIdx; omega)] at hf
      exact hf
  | sort cell rl hu => exact .sort cell rl hu
  | const cell ra rls hus => exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | @letE k addr tp vp bp T V B cell _ _ _ iht ihv ihb =>
    have e : (B.instantiate1Lift V 0).abstract1 d k =
        (B.abstract1 d (k + 1)).instantiate1Lift (V.abstract1 d k) 0 :=
      InferAux.abstract1_instantiate1Lift (V := V) (d := d) (k := k) (B := B) (j := 0)
    show Tm κ d Γ h (k + 1) ((B.instantiate1Lift V 0).abstract1 d k) _
    rw [e]
    exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

end IxVM.Refinement.Core
