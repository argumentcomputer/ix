module

public import IxC.Kernel.Ixon.RoleTable
public import IxC.Kernel.Ingress.Records

@[expose] public section

/-!
# A well-formed role table binds distinct roles to distinct addresses

`RoleTable.check` refuses a table that binds one address twice
(`firstRepeat`). This module states what its success gives: the bound
addresses are pairwise distinct, so is the bound roles' list, and a
well-formed table binds two roles to one address only if they are one role
(`RoleTable.addressOf?_inj`). The statements use it to show that no alias
fiber of a compiled artifact holds two roles' names
(`Ix.LeanIngress.FibersRoleFree`).
-/

namespace Ix.Kernel

namespace RoleTable

/-- `firstRepeat`'s step, named. -/
def firstRepeatStep (acc : Option Address × Std.HashSet Address) (a : Address) :
    Option Address × Std.HashSet Address :=
  match acc.1 with
  | some _ => acc
  | none => if acc.2.contains a then (some a, acc.2) else (none, acc.2.insert a)

theorem firstRepeat_eq (as : List Address) :
    firstRepeat as = (as.foldl firstRepeatStep (none, {})).1 := rfl

theorem foldl_firstRepeatStep_some :
    ∀ (l : List Address) (a : Address) (s : Std.HashSet Address),
      (l.foldl firstRepeatStep (some a, s)).1 = some a
  | [], _, _ => rfl
  | _ :: l, a, s => foldl_firstRepeatStep_some l a s

theorem foldl_firstRepeatStep_none :
    ∀ (l pre : List Address) (s : Std.HashSet Address), (∀ x, s.contains x = true ↔ x ∈ pre) →
      pre.Nodup → (l.foldl firstRepeatStep (none, s)).1 = none → (pre ++ l).Nodup
  | [], pre, _, _, hn, _ => by simpa using hn
  | x :: l, pre, s, hs, hn, h => by
    simp only [List.foldl_cons] at h
    by_cases hx : s.contains x = true
    · simp only [firstRepeatStep, hx, if_true] at h
      rw [foldl_firstRepeatStep_some] at h
      cases h
    · have hx' : x ∉ pre := fun hm => hx ((hs x).mpr hm)
      simp only [firstRepeatStep, hx, Bool.false_eq_true, if_false] at h
      have hs' : ∀ y, (s.insert x).contains y = true ↔ y ∈ pre ++ [x] := by
        intro y
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs y, beq_iff_eq, List.mem_append,
          List.mem_singleton]
        constructor
        · rintro (rfl | h)
          · exact Or.inr rfl
          · exact Or.inl h
        · rintro (h | rfl)
          · exact Or.inr h
          · exact Or.inl rfl
      have hn' : (pre ++ [x]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hn, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hx' ha
      have := foldl_firstRepeatStep_none l (pre ++ [x]) (s.insert x) hs' hn' h
      simpa using this

/-- **No repeat found: the addresses are pairwise distinct.** -/
theorem nodup_of_firstRepeat_none {as : List Address} (h : firstRepeat as = none) : as.Nodup := by
  rw [firstRepeat_eq] at h
  simpa using foldl_firstRepeatStep_none as [] {} (by simp) List.nodup_nil h

/-- **A well-formed table's bound addresses are pairwise distinct**, and so are
its bound roles. -/
theorem check_nodup {t : RoleTable} (h : t.check = .ok ()) :
    (t.bound.toList.map (·.1)).Nodup ∧ (t.bound.toList.map (·.2)).Nodup := by
  unfold check at h
  have hroles : (t.bound.toList.map (·.1)).Nodup := by
    refine Classical.byContradiction fun hn => ?_
    simp only [hn, ↓reduceIte] at h
    split at h <;> cases h
  refine ⟨hroles, ?_⟩
  cases hf : firstRepeat (t.bound.toList.map (·.2)) with
  | none => exact nodup_of_firstRepeat_none hf
  | some a =>
    exfalso
    by_cases hv : (t.version == specVersion) = true
    · simp only [hv, hroles, hf, ↓reduceIte] at h
      cases h
    · simp (config := { zeta := false }) only [hv] at h
      cases h

theorem eq_of_nodup_map_snd {α β : Type} :
    ∀ {l : List (α × β)} {p q : α × β}, (l.map (·.2)).Nodup → p ∈ l → q ∈ l → p.2 = q.2 → p = q
  | [], _, _, _, hp, _, _ => nomatch hp
  | x :: l, p, q, hn, hp, hq, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hp with hpx | hpl <;> rcases List.mem_cons.mp hq with hqx | hql
    · rw [hpx, hqx]
    · subst hpx; exact absurd ⟨q, hql, he.symm⟩ hn.1
    · subst hqx; exact absurd ⟨p, hpl, he⟩ hn.1
    · exact eq_of_nodup_map_snd hn.2 hpl hql he

/-- **A well-formed table binds distinct roles to distinct addresses.** -/
theorem addressOf?_inj {t : RoleTable} (h : t.check = .ok ()) {r s : Role} {a : Address}
    (hr : t.addressOf? r = some a) (hs : t.addressOf? s = some a) : r = s := by
  unfold addressOf? at hr hs
  obtain ⟨pr, hpr, rfl⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨ps, hps, hpsa⟩ := Option.map_eq_some_iff.mp hs
  have hpr1 : pr.1 = r := by
    have := Array.find?_some hpr
    simpa using this
  have hps1 : ps.1 = s := by
    have := Array.find?_some hps
    simpa using this
  have hmr := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hpr)
  have hms := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hps)
  have heq := eq_of_nodup_map_snd (check_nodup h).2 hmr hms hpsa.symm
  rw [← hpr1, ← hps1, heq]

end RoleTable

end Ix.Kernel
