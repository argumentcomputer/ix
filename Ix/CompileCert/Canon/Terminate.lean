import Ix.CompileCert.Canon.Simulate

/-!
# M7 L1, the refinement terminates

Design document §3.5 (ii), "the refinement terminates": when no comparison of two distinct
members fails (no metavariable, free variable, unknown universe parameter, missing address or
undecodable contract is reached), `sortClasses` returns. The fuel `|K| + 1` of the loop
suffices: every round that does not stop adds a class, and there are at most `|K|` classes
(`sortClassesP_ok`, `sortClasses_ok`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)

section
variable {rules : Rules} {addr? : Name → Option Address} (hA : AddrCongr addr?)
  {xs : List MutConst}
  (hok : ∀ (ctx : MutCtx), ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∃ o, constOrd rules addr? ctx a b = .ok o)
include hA hok

theorem refineClassP_ok (ctx : MutCtx) {C : List MutConst} (hC : ∀ a ∈ C, a ∈ xs) (hn : C.Nodup)
    (hne : C ≠ []) : ∃ G, refineClassP rules addr? ctx C = .ok G := by
  match C, hC, hn, hne with
  | [], _, _, hne => exact absurd rfl hne
  | [x], _, _, _ => exact ⟨[[x]], rfl⟩
  | x :: y :: rest, hC, hn, _ =>
    have hboth : (x :: y :: rest).Pairwise (BothOk (constOrd rules addr? ctx)) :=
      (List.nodup_iff_pairwise_ne.1 hn).imp_of_mem fun {a b} ha hb hab =>
        ⟨hok ctx a (hC a ha) b (hC b hb) hab, hok ctx b (hC b hb) a (hC a ha) (Ne.symm hab)⟩
    have hor := constOrd_oriented rules hA ctx (S := fun _ => True)
    obtain ⟨sorted, hs⟩ := sortByM_ok hor _ hboth
    obtain ⟨psorted, -⟩ := sortByM_spec hor _ (fun _ _ => trivial) sorted hs
    have hboth' := pairwise_bothOk_perm psorted.symm hboth
    obtain ⟨groups, hg⟩ := groupAdjP_ok (eqOf (constOrd rules addr? ctx)) sorted (hboth'.imp fun {a b} hab => by
      obtain ⟨o, ho⟩ := hab.2
      exact ⟨o == .eq, by simp only [eqOf, ho, bind, Except.bind, pure, Except.pure]⟩)
    exact ⟨repOf rules groups, by simp only [refineClassP, hs, hg, bind, Except.bind, pure, Except.pure]⟩

theorem refineClassesP_ok (ctx : MutCtx) : ∀ (P : List (List MutConst)), (∀ a ∈ P.flatten, a ∈ xs) →
    P.flatten.Nodup → (∀ C ∈ P, C ≠ []) → ∃ R, refineClassesP rules addr? ctx P = .ok R
  | [], _, _, _ => ⟨[], rfl⟩
  | C :: P, hP, hn, hne => by
    rw [List.flatten_cons] at hP hn
    obtain ⟨G, hG⟩ := refineClassP_ok hA hok ctx (fun a ha => hP a (List.mem_append_left _ ha))
      (List.nodup_append.1 hn).1 (hne C (List.mem_cons_self ..))
    obtain ⟨R, hR⟩ := refineClassesP_ok ctx P (fun a ha => hP a (List.mem_append_right _ ha))
      (List.nodup_append.1 hn).2.1 (fun D hD => hne D (List.mem_cons_of_mem _ hD))
    exact ⟨G ++ R, by simp only [refineClassesP, hG, hR, bind, Except.bind, pure, Except.pure]⟩

theorem sortLoopP_ok (hk : KeysDistinct xs) : ∀ (fuel round : Nat) (P : List (List MutConst)),
    Partition P xs → xs.length + 1 ≤ P.length + fuel →
    ∃ F n, sortLoopP rules addr? fuel round P = .ok (F, n) ∧ Partition F xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro round P hP hf
    have := length_le_flatten hP.2
    rw [hP.1.length_eq] at this
    omega
  | succ fuel ih =>
    intro round P hP hf
    simp only [sortLoopP]
    obtain ⟨R, hR⟩ := refineClassesP_ok hA hok (MutConst.ctx P) P
      (fun a ha => hP.1.mem_iff.1 ha) (hP.1.nodup_iff.2 hk.nodup) hP.2
    obtain ⟨rp, rne, -, -, -, rlen, -⟩ := refineClassesP_spec rules hA _ P R hP.2 hR
    have hPR : Partition R xs := ⟨rp.trans hP.1, rne⟩
    rw [hR]
    simp only [bind, Except.bind]
    split
    · exact ⟨R, round + 1, rfl, hPR⟩
    · rename_i hc
      have hgt : P.length + 1 ≤ R.length := by
        have : P.length ≠ R.length := by simpa using hc
        omega
      exact ih (round + 1) R hPR (by omega)

/-- **The pure refinement returns** when no comparison of distinct members fails. -/
theorem sortClassesP_ok (hk : KeysDistinct xs) : ∃ F, sortClassesP rules addr? xs = .ok F := by
  unfold sortClassesP
  by_cases he : xs.isEmpty = true
  · simp only [he, ↓reduceIte]; exact ⟨[], rfl⟩
  · have he₁ : xs.isEmpty = false := by simpa using he
    simp only [he₁, Bool.false_eq_true, ↓reduceIte]
    have hP0 : Partition [seedOf rules xs] xs := by
      refine ⟨by simpa using seedOf_perm rules xs, fun C hC => ?_⟩
      simp only [List.mem_singleton] at hC; subst hC
      intro e
      have := (seedOf_perm rules xs).symm
      rw [e] at this
      exact he (by simpa using List.Perm.eq_nil this)
    obtain ⟨F, n, hl, hF⟩ := sortLoopP_ok hA hok hk (xs.length + 1) 0 _ hP0
      (by simp only [List.length_singleton]; omega)
    rw [hl]
    simp only [bind, Except.bind]
    have hany : F.any (·.isEmpty) = false := by
      cases hh : F.any (·.isEmpty) with
      | false => rfl
      | true =>
        obtain ⟨D, hD, hDe⟩ := List.any_eq_true.1 hh
        exact absurd (List.isEmpty_iff.1 hDe) (hF.2 D hD)
    have hlen : ¬ xs.length < F.length := by
      have := length_le_flatten hF.2
      rw [hF.1.length_eq] at this; omega
    simp only [hany, Bool.false_eq_true, ↓reduceIte, hlen, pure, Except.pure]
    exact ⟨F, rfl⟩

/-- **The refinement terminates** (§3.5 (ii)): with the port fixes, `sortClasses` returns when no
comparison of distinct members fails. -/
theorem sortClasses_ok (hpf : rules.portFixes = true) (hk : KeysDistinct xs) :
    ∃ F stats, sortClasses rules addr? xs = .ok (F, stats) := by
  obtain ⟨F, hF⟩ := sortClassesP_ok hA hok hk
  have e := sortClasses_eq hpf hA hk
  rw [hF] at e
  cases h : sortClasses rules addr? xs with
  | error err => rw [h] at e; cases e
  | ok v => exact ⟨v.1, v.2, rfl⟩

end

end Ix.CompileCert.Canon
