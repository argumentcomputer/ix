import IxVMRefinement.Binding.Steps

/-! # Closing a group: the group's fields and the raise to the next top limit

Every kind of group ends the same way. Once the group's records are installed (its closure, then
its role unit if it has one), the invariant on the groups below `g` at the grown store and
environment becomes the invariant on the groups below `g + 1`: the group-indexed fields of
`TableShape` at `g` (its kept and prelude roles stored as their records declare them), the stored
shapes at `g`, and the prefix invariant raised from `g`'s validation limit (the top carried limit
below `g`) to the top carried limit below `g + 1`.

* `RaiseAt t env g`: what the raise past `g` needs of the environment, by block: below the
  well-founded block, every role of `g` with its companion fact and, if fabricated, its key
  stored; at the end of the well-founded block (group 40), the eight operations stored as pinned;
  at the end of the literal block (group 45), the string literal support and the literal roles'
  keys. Elsewhere the top limit does not change, or (group 76) nothing is needed.
* `prefixInv_top_succ`: the raise, by block (`Raise.lean`).
* `bnd_close`: the invariant below `g + 1` from the invariant below `g` and the group's facts.
* `raiseAt_of_noOps`: `RaiseAt` at a group from 6 on with no operation, from its fabricated
  roles' keys and, at group 45, the literal support (the companion facts are decided).
-/

universe u

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

/-! ## The top limit, by block -/

theorem topLim_le33 {n : Nat} (h : n ≤ 33) : topLim n = some n := by
  simp only [topLim, h, ↓reduceIte]

theorem topLim_wfBlock {n : Nat} (h1 : 33 ≤ n) (h2 : n ≤ 40) : topLim n = some 33 := by
  unfold topLim
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem topLim_litBlock {n : Nat} (h1 : 41 ≤ n) (h2 : n ≤ 45) : topLim n = some 41 := by
  unfold topLim
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem topLim_tailBlock {n : Nat} (h1 : 46 ≤ n) (h2 : n ≤ 76) : topLim n = some 46 := by
  unfold topLim
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-! ## The raise past one group -/

/-- **What the raise past group `g` needs of the environment** (module docstring). -/
structure RaiseAt (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (g : Nat) : Prop where
  succ : g < 33 → ∀ r ∈ roleGroup g, (t.addressOf? r).isSome = true →
    RaiseOk env r ∧ (Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Core.keyOf t a) = some ci)
  wf : g = 40 → ∀ r ∈ wfOpRoles, (t.addressOf? r).isSome = true →
    Ix.Kernel.natOpStoredOk env (.role r) = true
  literal : g = 45 → Ix.Kernel.strLitSupported env = true ∧
    ∀ r ∈ literalRoles, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Core.keyOf t a) = some ci

/-- **The prefix invariant from the top limit below `g` to the top limit below `g + 1`**, by
block. -/
theorem prefixInv_top_succ {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {g : Nat} (hg : g < 77) (h : Decl.PrefixInv.{u} E t (topLim g) env) (hr : RaiseAt t env g) :
    Decl.PrefixInv.{u} E t (topLim (g + 1)) env := by
  by_cases h1 : g < 33
  · rw [topLim_le33 (Nat.le_of_lt h1)] at h
    rw [topLim_le33 (show g + 1 ≤ 33 by omega)]
    exact prefixInv_raise_succ h (hr.succ h1)
  by_cases h2 : g < 40
  · rw [topLim_wfBlock (show 33 ≤ g by omega) (show g ≤ 40 by omega)] at h
    rw [topLim_wfBlock (show 33 ≤ g + 1 by omega) (show g + 1 ≤ 40 by omega)]
    exact h
  by_cases h3 : g = 40
  · subst h3
    rw [topLim_wfBlock (show 33 ≤ 40 by omega) (show 40 ≤ 40 by omega)] at h
    rw [topLim_litBlock (show 41 ≤ 40 + 1 by omega) (show 40 + 1 ≤ 45 by omega)]
    exact prefixInv_raise_wf h (hr.wf rfl)
  by_cases h4 : g < 45
  · rw [topLim_litBlock (show 41 ≤ g by omega) (show g ≤ 45 by omega)] at h
    rw [topLim_litBlock (show 41 ≤ g + 1 by omega) (show g + 1 ≤ 45 by omega)]
    exact h
  by_cases h5 : g = 45
  · subst h5
    rw [topLim_litBlock (show 41 ≤ 45 by omega) (show 45 ≤ 45 by omega)] at h
    rw [topLim_tailBlock (show 46 ≤ 45 + 1 by omega) (show 45 + 1 ≤ 76 by omega)]
    exact prefixInv_raise_literal h (hr.literal rfl).1 (hr.literal rfl).2
  by_cases h6 : g < 76
  · rw [topLim_tailBlock (show 46 ≤ g by omega) (show g ≤ 76 by omega)] at h
    rw [topLim_tailBlock (show 46 ≤ g + 1 by omega) (show g + 1 ≤ 76 by omega)]
    exact h
  · have h7 : g = 76 := by omega
    subst h7
    rw [topLim_tailBlock (show 46 ≤ 76 by omega) (show 76 ≤ 76 by omega)] at h
    rw [topLim_none (show 77 ≤ 76 + 1 by omega)]
    exact prefixInv_raise_tail h none

/-! ## Closing a group -/

/-- **The invariant below `g + 1` from the invariant below `g` and the group's facts** (module
docstring): the group's kept and prelude roles stored as their records declare them, the stored
shapes below `g + 1`, what the raise past `g` needs, and the extra clause carried. -/
theorem bnd_close
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hall : AllBound t) (hg : g < 77) (hb : Bnd.{u} X t (· < g) R env)
    (hkept : ∀ r ∈ roleGroup g, keptRole r → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci))
    (hprel : ∀ r ∈ roleGroup g, r ∈ preludeRoles → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci))
    (hshapes : Shapes (· < g + 1) env) (hraise : RaiseAt t env g)
    (hX : X t (· < g) R env → X t (· < g + 1) R env) :
    Bnd.{u} X t (· < g + 1) R env := by
  have hs := hb.shape
  have hf := hb.facts
  have htop : ∀ E, RecordsFor R E → Decl.PrefixInv.{u} E t (topLim (g + 1)) env := by
    intro E hE
    have h0 : Decl.PrefixInv.{u} E t (topLim g) env := by
      rw [topLim_valLimit hg]
      exact hf.inv E hE _ (carried_valLimit g) (limWithin_below t g)
    exact prefixInv_top_succ hg h0 hraise
  refine ⟨?_, ?_, hX hb.extra⟩
  · exact {
      needsClosed := fun k hk r hr => by
        have h1 := groupNeeded_lt hr
        have h2 : k < g + 1 := hk
        show Ix.SpecDigest.groupOf r < g + 1
        omega
      bound := fun _ _ r _ => hall r
      prelude := hs.prelude
      literals := hs.literals
      hashed := hs.hashed
      usedClosed := hs.usedClosed
      committed := hs.committed
      zeroFree := hs.zeroFree
      kept := fun k r a hk hr hkr ha => by
        by_cases hkg : k < g
        · exact hs.kept k r a hkg hr hkr ha
        · have hk' : k < g + 1 := hk
          have e : k = g := by omega
          rw [e] at hr
          exact hkept r hr hkr a ha
      reading := hs.reading
      pins := hs.pins
      preludeKept := fun k r a hk hr hp ha => by
        by_cases hkg : k < g
        · exact hs.preludeKept k r a hkg hr hp ha
        · have hk' : k < g + 1 := hk
          have e : k = g := by omega
          rw [e] at hr
          exact hprel r hr hp a ha
      model := hs.model }
  · exact {
      inv := bfacts_inv_of_top hall htop
      whole := hf.whole
      opsPinned := hf.opsPinned
      opsAdmitted := fun r hr hst => Nat.lt_succ_of_lt (hf.opsAdmitted r hr hst)
      shapes := hshapes }

/-! ## The raise at a group with no operation -/

set_option maxRecDepth 100000 in
private theorem mid_free_all : Ix.Kernel.Role.all.all (fun r =>
    decide (6 ≤ Ix.SpecDigest.groupOf r → Ix.SpecDigest.groupOf r < 33 →
      r ∉ RoleOps.opRoles →
      r ∉ companionRoles ∧ (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames)) =
    true := by
  decide +kernel

/-- **The roles of the groups 6 to 32 that are no operation are read by no companion field.** -/
theorem mid_free {r : Ix.Kernel.Role} (h1 : 6 ≤ Ix.SpecDigest.groupOf r)
    (h2 : Ix.SpecDigest.groupOf r < 33) (h3 : r ∉ RoleOps.opRoles) :
    r ∉ companionRoles ∧ (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames :=
  of_decide_eq_true (List.all_eq_true.mp mid_free_all r (Ix.Kernel.Role.mem_all r)) h1 h2 h3

set_option maxRecDepth 100000 in
private theorem group40_op : ∃ r ∈ roleGroup 40, r ∈ RoleOps.opRoles := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem groups_own_all : (List.range 77).all (fun g =>
    (roleGroup g).all (fun r => Ix.SpecDigest.groupOf r == g)) = true := by
  decide +kernel

/-- **A role of group `g` is of group `g`** (decided over the 77 groups). -/
theorem groupOf_of_mem_roleGroup {g : Nat} {r : Ix.Kernel.Role} (h : r ∈ roleGroup g) :
    Ix.SpecDigest.groupOf r = g := by
  by_cases hg : g < 77
  · have h1 := List.all_eq_true.mp groups_own_all g (List.mem_range.mpr hg)
    exact beq_iff_eq.mp (List.all_eq_true.mp h1 r h)
  · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at h
    cases h

/-- **`RaiseAt` at a group from 6 on with no operation** (module docstring). -/
theorem raiseAt_of_noOps {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon} {g : Nat}
    (h6 : 6 ≤ g) (hnone : ∀ r ∈ roleGroup g, r ∉ RoleOps.opRoles)
    (hfab : ∀ r ∈ roleGroup g, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Core.keyOf t a) = some ci)
    (hlit : g = 45 → Ix.Kernel.strLitSupported env = true ∧
      ∀ r ∈ literalRoles, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
        ∃ ci, env.find? (Core.keyOf t a) = some ci) :
    RaiseAt t env g where
  succ := fun hg r hr _ => by
    have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hr
    refine ⟨Or.inr (Or.inr (mid_free (by omega) (by omega) (hnone r hr))), hfab r hr⟩
  wf := fun h40 => by
    subst h40
    obtain ⟨r, hr, hop⟩ := group40_op
    exact absurd hop (hnone r hr)
  literal := hlit

end IxVM.Refinement.Binding
