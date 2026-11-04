import IxC.Kernel.Ixon.Reader

/-! # A lowered inductive block declares distinct names

`lowerInductive` lowers a block (`lowerInductiveDecls`) and declines the read when its
declarations declare a name twice (`firstRepeatedKey`). This module states what its success
gives: the read is `lowerInductiveDecls`' and the names its declarations declare, in order, are
pairwise distinct (`lowerInductive_ok_iff`). -/

namespace Ix.Cert.LowerDistinct

open Ix.Kernel Ix.Kernel.Reader

variable {md : Mode}

theorem foldl_firstRepeatedKeyStep_some :
    ∀ (l : List (CName md)) (a : CName md) (s : Std.HashSet (CName md)),
      (l.foldl firstRepeatedKeyStep (some a, s)).1 = some a
  | [], _, _ => rfl
  | _ :: l, a, s => foldl_firstRepeatedKeyStep_some l a s

theorem foldl_firstRepeatedKeyStep_none :
    ∀ (l pre : List (CName md)) (s : Std.HashSet (CName md)), (∀ x, s.contains x = true ↔ x ∈ pre) →
      pre.Nodup → ((l.foldl firstRepeatedKeyStep (none, s)).1 = none ↔ (pre ++ l).Nodup)
  | [], pre, _, _, hn => by simpa using hn
  | x :: l, pre, s, hs, hn => by
    simp only [List.foldl_cons]
    by_cases hx : s.contains x = true
    · simp only [firstRepeatedKeyStep, hx, ↓reduceIte]
      rw [foldl_firstRepeatedKeyStep_some]
      have hm : x ∈ pre := (hs x).mp hx
      simp only [reduceCtorEq, false_iff]
      intro hnd
      rw [List.nodup_append] at hnd
      exact hnd.2.2 x hm x List.mem_cons_self rfl
    · have hx' : x ∉ pre := fun hm => hx ((hs x).mpr hm)
      simp only [firstRepeatedKeyStep, hx, Bool.false_eq_true, ↓reduceIte]
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
      rw [foldl_firstRepeatedKeyStep_none l (pre ++ [x]) (s.insert x) hs' hn']
      simp

/-- **No repeat found: the keys are pairwise distinct**, and conversely. -/
theorem firstRepeatedKey_eq_none_iff {ks : List (CName md)} :
    firstRepeatedKey ks = none ↔ ks.Nodup := by
  have h := foldl_firstRepeatedKeyStep_none ks [] {} (by simp) List.nodup_nil
  rw [List.nil_append] at h
  exact h

/-- **What an accepted `lowerInductive` gives**: the block's declarations as
`lowerInductiveDecls` lowers them, which declare pairwise distinct names; and
conversely. -/
theorem lowerInductive_ok_iff {st : State md} {rb : BlockRead md} {r : Read md} :
    lowerInductive st rb = .ok r ↔
      lowerInductiveDecls st rb = .ok r ∧ (r.decls.toList.flatMap Declaration.names).Nodup := by
  unfold lowerInductive
  cases h : lowerInductiveDecls st rb with
  | error e => simp [bind, Except.bind]
  | ok r₀ =>
    simp only [bind, Except.bind, Except.ok.injEq]
    cases hk : firstRepeatedKey (r₀.decls.toList.flatMap Declaration.names) with
    | some k =>
      have hdup : ¬ (r₀.decls.toList.flatMap Declaration.names).Nodup := fun hn => by
        rw [firstRepeatedKey_eq_none_iff.mpr hn] at hk
        cases hk
      simp only [declined, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff]
      rintro ⟨rfl, hn⟩
      exact hdup hn
    | none =>
      have hn := firstRepeatedKey_eq_none_iff.mp hk
      simp only [pure, Except.pure, Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, hn⟩
      · rintro ⟨rfl, -⟩
        rfl

/-- An accepted `lowerInductive` is `lowerInductiveDecls`'. -/
theorem lowerInductiveDecls_of_ok {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) : lowerInductiveDecls st rb = .ok r :=
  (lowerInductive_ok_iff.mp h).1

/-- **An accepted `lowerInductive`'s declarations declare pairwise distinct names.** -/
theorem lowerInductive_names_nodup {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) : (r.decls.toList.flatMap Declaration.names).Nodup :=
  (lowerInductive_ok_iff.mp h).2

/--
info: 'Ix.Cert.LowerDistinct.lowerInductive_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lowerInductive_ok_iff

end Ix.Cert.LowerDistinct
