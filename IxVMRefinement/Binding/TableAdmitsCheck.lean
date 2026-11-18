import IxVMRefinement.Core.Roles

/-! # `RoleTable.check` from its clauses

`Ix.Kernel.RoleTable.check` succeeds when its clauses hold: the version, no role and no address
twice, every role bound (so every block and dependency is), no role with two evidence entries,
each entry's role with equations and the entry matching them, and every bound role with
equations having an entry. The converse of the readings in `Core.Roles` and
`RoleVal.check_evidence_nodup_and_eqns`, for a table given by its clauses.
-/

namespace IxVM.Refinement.Binding

set_option linter.unusedVariables false

/-- A loop in `Except` over a body that continues at every element succeeds. -/
theorem forIn_ok_of_yield {ε α : Type} :
    ∀ (l : List α) (f : α → Unit → Except ε (ForInStep Unit)),
      (∀ a ∈ l, f a () = .ok (.yield ())) → forIn l () f = .ok ()
  | [], _, _ => rfl
  | a :: l, f, hf => by
    rw [List.forIn_cons, hf a List.mem_cons_self]
    exact forIn_ok_of_yield l f (fun x hx => hf x (List.mem_cons_of_mem _ hx))

theorem forIn_bind_ok {ε α β : Type} {l : List α} {f : α → Unit → Except ε (ForInStep Unit)}
    {g : Unit → Except ε β} {b : β}
    (hf : ∀ a ∈ l, f a () = .ok (.yield ())) (hg : g () = .ok b) :
    (forIn l () f >>= g) = .ok b := by
  rw [forIn_ok_of_yield l f hf]
  exact hg

private theorem foldl_firstRepeatStep_eq_none :
    ∀ (l pre : List _root_.Address) (s : Std.HashSet _root_.Address),
      (∀ x, s.contains x = true ↔ x ∈ pre) →
      (∀ x ∈ l, x ∉ pre) →
      l.Nodup →
      (l.foldl Ix.Kernel.RoleTable.firstRepeatStep (none, s)).1 = none
  | [], _, _, _, _, _ => rfl
  | x :: l, pre, s, hs, hdisj, hn => by
    rw [List.nodup_cons] at hn
    have hx_not_pre : x ∉ pre := hdisj x List.mem_cons_self
    have hx_false : s.contains x = false :=
      Bool.eq_false_iff.mpr fun hc => hx_not_pre ((hs x).mp hc)
    simp only [List.foldl_cons, Ix.Kernel.RoleTable.firstRepeatStep, hx_false,
      Bool.false_eq_true, ↓reduceIte]
    have hs' : ∀ y, (s.insert x).contains y = true ↔ y ∈ x :: pre := by
      intro y
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs y, beq_iff_eq, List.mem_cons]
      exact ⟨fun h => h.elim (fun h1 => .inl h1.symm) .inr,
        fun h => h.elim (fun h1 => .inl h1.symm) .inr⟩
    have hdisj' : ∀ y ∈ l, y ∉ x :: pre := by
      intro y hy hmem
      rcases List.mem_cons.mp hmem with rfl | hy_pre
      · exact hn.1 hy
      · exact hdisj y (List.mem_cons_of_mem _ hy) hy_pre
    exact foldl_firstRepeatStep_eq_none l (x :: pre) (s.insert x) hs' hdisj' hn.2

/-- No address twice: no first repeat (as `CommittedBase`'s, which is private). -/
theorem firstRepeat_eq_none_of_nodup {as : List _root_.Address} (h : as.Nodup) :
    Ix.Kernel.RoleTable.firstRepeat as = none := by
  rw [Ix.Kernel.RoleTable.firstRepeat_eq]
  exact foldl_firstRepeatStep_eq_none as [] {} (by simp) (by simp) h

/-- **`RoleTable.check` from its clauses.** -/
theorem check_ok_of {t : Ix.Kernel.RoleTable}
    (hv : t.version = Ix.Kernel.specVersion)
    (hr : (t.bound.toList.map (·.1)).Nodup)
    (ha : (t.bound.toList.map (·.2)).Nodup)
    (hall : ∀ r : Ix.Kernel.Role, r ∈ t.bound.toList.map (·.1))
    (he : (t.evidence.toList.map (·.1)).Nodup)
    (hev : ∀ p ∈ t.evidence.toList,
      ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed.isEmpty = false ∧
      (p.2.size == ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed.length &&
        (p.2.toList.zip ((Ix.Kernel.Role.spec (md := .anon)) p.1).evidenceAllowed).all
          (fun x => x.1.allowedBy x.2)) = true)
    (hcov : ∀ r : Ix.Kernel.Role,
      ((Ix.Kernel.Role.spec (md := .anon)) r).evidenceAllowed.isEmpty = false →
      r ∈ t.evidence.toList.map (·.1)) :
    t.check = .ok () := by
  have hv' : (t.version == Ix.Kernel.specVersion) = true := by simp [hv]
  have hfr := firstRepeat_eq_none_of_nodup ha
  have hcon : ∀ r : Ix.Kernel.Role, (t.bound.toList.map (·.1)).contains r = true := by
    intro r
    simpa using hall r
  unfold Ix.Kernel.RoleTable.check
  simp only [hv', hr, hfr, he, ↓reduceIte, ← Array.forIn_toList]
  refine forIn_bind_ok ?_ (forIn_bind_ok ?_ (forIn_bind_ok ?_ rfl))
  · intro x hx
    refine forIn_bind_ok ?_ (forIn_bind_ok ?_ rfl)
    · intro s hs
      simp only [hcon s, ↓reduceIte] <;> rfl
    · intro s hs
      simp only [hcon s, ↓reduceIte] <;> rfl
  · intro x hx
    obtain ⟨h1, h2⟩ := hev x hx
    simp only [hcon x.1, h1, h2, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · intro r hr'
    have hc : (((Ix.Kernel.Role.spec (md := .anon)) r).evidenceAllowed.isEmpty ||
        (t.evidence.toList.map (·.1)).contains r) = true := by
      cases hE : ((Ix.Kernel.Role.spec (md := .anon)) r).evidenceAllowed.isEmpty
      · simpa using hcov r hE
      · rfl
    simp only [hc, ↓reduceIte] <;> rfl

end IxVM.Refinement.Binding
