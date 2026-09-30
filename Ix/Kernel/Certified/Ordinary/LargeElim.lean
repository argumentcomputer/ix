/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/LargeElim.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `checkLarge` takes the shape and infers.
P01: bounded validators return `Search`, preserving nested exhaustion and
unresolved search; direct validation failures carry specific diagnostics.
A3: a single constructor's field may be exactly one of the result's index
variables instead of a proposition (`LargeEvidence`'s fourth case), as in the
official kernel; such fields agree at a common index (`fits_unique_masked`).
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.Constructors
import Ix.Kernel.Certified.Ordinary.Container
import Ix.Kernel.Model.Inductive.Recursor

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower

universe u v
variable {β : Type u}

/-- A telescope whose unmasked fields are propositions. -/
def PropSMask {V : Type v} [SetTheory V] : {n : Nat} → TeleS V n → List Bool → Prop
  | _, .nil, _ => True
  | _, .cons A B, m :: ms => (m = false → A ∈ˢ (univZero : V)) ∧ ∀ a, a ∈ˢ A → PropSMask (B a) ms
  | _, .cons _ _, [] => False

/-- Values fitting a telescope agree when its unmasked fields are propositions
and they agree at its masked fields. -/
theorem fits_unique_masked {V : Type v} [SetTheory V] :
    ∀ {n} {T : TeleS V n} {mask : List Bool} {xs ys : List V}, PropSMask T mask →
      FitsS T xs → FitsS T ys → (∀ k : Nat, mask[k]? = some true → xs[k]? = ys[k]?) → xs = ys
  | _, .nil, _, [], [], _, _, _, _ => rfl
  | _, .cons _ B, m :: ms, x :: xs, y :: ys, hT, hx, hy, hpin => by
    have hxy : x = y := by
      cases m with
      | true => simpa using hpin 0 rfl
      | false => exact SetModel.subsingleton_of_mem_univZero (hT.1 rfl) hx.1 hy.1
    subst hxy
    exact congrArg (x :: ·) (fits_unique_masked (T := B x) (hT.2 x hx.1) hx.2 hy.2
      fun k hk => by simpa using hpin (k + 1) hk)
  | _, .cons _ _, [], _ :: _, _ :: _, hT, _, _, _ => hT.elim

/-- The unmasked fields of a telescope are propositions wherever `atLevel` is
zero. -/
def TelescopePropMask (entries : Environment β) (Γ : Context β) (domains : List (AExpr β))
    (mask : List Bool) (atLevel : VLevel) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ levels env, Γ.Valid constants levels env → atLevel.eval levels = 0 →
      PropSMask (Telescope.interpret constants levels env domains) mask

/-- Check a masked telescope: every field is a type, and each unmasked one a
proposition wherever `atLevel` is zero. -/
def checkPropTelescopeMask [DecidableEq β] (fuel : Nat) (entries : Environment β) (atLevel : VLevel) :
    (Γ : Context β) → (domains : List (AExpr β)) → (mask : List Bool) →
      Search (CheckedClaim.{u} (TelescopePropMask.{u,v} entries Γ domains mask atLevel))
  | _, [], _ => .ok ⟨fun _ _ _ _ _ _ _ _ => trivial⟩
  | Γ, A :: rest, m :: ms => do
    let ⟨l, hA⟩ ← checkSort.{u,v} fuel entries Γ A
    if hl : m = true ∨ checkZeroImplies atLevel l = true then
      let htail ← checkPropTelescopeMask fuel entries atLevel (Γ.push A) rest ms
      return ⟨by
        intro V _ constants hM levels env hΓ hz
        have htype := hA V constants hM levels env hΓ
        refine ⟨fun hm => ?_, fun x hx => htail.down V constants hM levels _ (hΓ.push htype.1 hx) hz⟩
        have hc : checkZeroImplies atLevel l = true := by
          rcases hl with h | h
          · rw [hm] at h; cases h
          · exact h
        simpa only [interp, checkZeroImplies_sound hc levels hz, univ_zero] using htype.2.2⟩
    else .error (.unresolved "the field was not established to be proposition-valued")
  | _, _ :: _, [] => .error (.unresolved "the field was not established to be proposition-valued")

/-- Large elimination from a possible proposition: a positive sort, no
constructor, or a single constructor whose every field is a proposition or is
exactly one of the result's index variables (the official kernel's
`elim_only_at_universe_zero`), as `Acc.intro`'s `x`. -/
def LargeEvidence (entries : Environment β) (shape : Shape β) : Prop :=
  (∀ levels, shape.level.eval levels ≠ 0) ∨ shape.constructors = [] ∨
    (∃ ctor, shape.constructors = [ctor] ∧
      TelescopeProp.{u,v} entries shape.parameterContext ctor.fields shape.level) ∨
    ∃ ctor mask, shape.constructors = [ctor] ∧ mask.length = ctor.fields.length ∧
      TelescopePropMask.{u,v} entries shape.parameterContext ctor.fields mask shape.level ∧
      ∀ k : Nat, mask[k]? = some true →
        ∃ j : Nat, ctor.indices[j]? = some (AExpr.bvar (ctor.fields.length - 1 - k))

def checkLarge [DecidableEq β] (fuel : Nat) (entries : Environment β) (shape : Shape β) :
    Search (CheckedClaim.{u} (LargeEvidence.{u,v} entries shape)) :=
  if hp : zeroCondition shape.level = .never then
    .ok ⟨Or.inl (by
      intro levels he
      have hz := zeroCondition_correct shape.level levels
      simp only [hp, PropWhen.holds_never, he, beq_self_eq_true, Bool.false_eq_true] at hz)⟩
  else
    match hc : shape.constructors with
    | [] => .ok ⟨Or.inr (Or.inl hc)⟩
    | [ctor] => do
      -- A field that is exactly an index of the result need not be a proposition.
      let n := ctor.fields.length
      let mask := (List.range n).map fun k => ctor.indices.contains (AExpr.bvar (n - 1 - k))
      let fields ← checkPropTelescopeMask.{u,v} fuel entries shape.level shape.parameterContext
        ctor.fields mask
      return ⟨Or.inr (Or.inr (Or.inr ⟨ctor, mask, hc, by simp [mask, n], fields.down, fun k hk => by
        have hlt : k < mask.length := (List.getElem?_eq_some_iff.mp hk).1
        have hv : mask[k] = true := (List.getElem?_eq_some_iff.mp hk).2
        simp only [mask, List.getElem_map, List.getElem_range] at hv
        obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.contains_iff_mem.mp hv)
        exact ⟨j, hj⟩⟩))⟩
    | _ => .error (.malformed "large elimination from a possible proposition with multiple constructors")

theorem checkLarge_sound [DecidableEq β] {fuel : Nat} {entries : Environment β} {shape : Shape β}
    {result} (_ : checkLarge.{u,v} fuel entries shape = .ok result) :
    LargeEvidence.{u,v} entries shape := result.down

variable {V : Type v} [SetTheory V]

theorem Shape.container_large {entries : Environment β} {shape : Shape β}
    (hlarge : LargeEvidence.{u,v} entries shape) {constants : Assignment β V}
    (hM : Realizes constants entries) {levels : List Nat} {env : Nat → V}
    (hΓ : shape.parameterContext.Valid constants levels env) :
    (shape.container constants levels env).LargeElim (shape.level.eval levels) := by
  intro hw i hi a b ha hb
  rcases hlarge with hpos | hempty | ⟨ctor, hsingle, hprop⟩ | ⟨ctor, mask, hsingle, hmlen, hprop, hpin⟩
  · exact (hpos levels hw).elim
  · obtain ⟨j, ctor, xs, hc, _, _⟩ := Shape.mem_allShapes (mem_sep.mp ha).1
    simp only [hempty, List.getElem?_nil] at hc
    contradiction
  · obtain ⟨j, ca, xs, hca, hxs, rfl⟩ := Shape.mem_allShapes (mem_sep.mp ha).1
    obtain ⟨k, cb, ys, hcb, hys, rfl⟩ := Shape.mem_allShapes (mem_sep.mp hb).1
    have hj : j = 0 := by cases j <;> simp_all
    have hk : k = 0 := by cases k <;> simp_all
    subst j k
    have heca : ctor = ca := by simpa only [hsingle, List.getElem?_cons_zero, Option.some.injEq] using hca
    have hecb : ctor = cb := by simpa only [hsingle, List.getElem?_cons_zero, Option.some.injEq] using hcb
    subst ca cb
    have he := Telescope.fits_unique_of_prop (hprop V constants hM levels env hΓ hw) hxs hys
    rw [he]
  · obtain ⟨j, ca, xs, hca, hxs, rfl⟩ := Shape.mem_allShapes (mem_sep.mp ha).1
    obtain ⟨k, cb, ys, hcb, hys, rfl⟩ := Shape.mem_allShapes (mem_sep.mp hb).1
    have hj : j = 0 := by cases j <;> simp_all
    have hk : k = 0 := by cases k <;> simp_all
    subst j k
    have heca : ctor = ca := by simpa only [hsingle, List.getElem?_cons_zero, Option.some.injEq] using hca
    have hecb : ctor = cb := by simpa only [hsingle, List.getElem?_cons_zero, Option.some.injEq] using hcb
    subst ca cb
    have hxl : xs.length = ctor.fields.length := by simpa using hxs.length_eq
    have hyl : ys.length = ctor.fields.length := by simpa using hys.length_eq
    -- Both shapes sit at index `i`, so their result indices agree.
    have hri : shape.resultIndex constants levels env (inj 0 (mkTower xs)) =
        shape.resultIndex constants levels env (inj 0 (mkTower ys)) :=
      ((mem_sep.mp ha).2).trans ((mem_sep.mp hb).2).symm
    rw [Shape.resultIndex_inj constants levels env hca hxl,
      Shape.resultIndex_inj constants levels env hcb hyl] at hri
    have hidx := mkTower_inj (by simp) hri
    have he := fits_unique_masked (hprop V constants hM levels env hΓ hw) hxs hys fun k hk => by
      obtain ⟨j, hj⟩ := hpin k hk
      have hk' : k < ctor.fields.length := hmlen ▸ (List.getElem?_eq_some_iff.mp hk).1
      have hjx := congrArg (fun l => l[j]?) hidx
      simp only [List.getElem?_map, hj, Option.map_some, Option.some.injEq, interp] at hjx
      rw [← hxl] at hjx
      rw [Telescope.extend_getD env xs k (by omega)] at hjx
      rw [hxl, ← hyl, Telescope.extend_getD env ys k (by omega)] at hjx
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < xs.length),
        List.getElem?_eq_getElem (by omega : k < ys.length)] using hjx
    rw [he]

end Ix.Kernel.Certified.Ordinary
