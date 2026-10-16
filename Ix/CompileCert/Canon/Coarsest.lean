import Ix.CompileCert.Canon.Round

/-! # Pass 1's refinement computes the coarsest consistent partition

CS-01, ported from the donor `a9cf3607` (`Canon/Coarsest`). A partition `P`
of the members is **consistent** when any two distinct members of one class
compare `eq` under the key read through `P`'s own context
(`MutConst.ctx P`: in-block references by class, constructors by class and
position). The **classes** of the design are the coarsest consistent
partition. `sortClasses_coarsest`: when `sortClasses` returns, its classes
partition the members, are consistent, and every consistent partition
refines them (so they are the coarsest one, unique as a partition). That
last part is a canonicity fact; the reading chain uses the first two
(`MutualProjections.ClassesAgree`, R9b).

The argument: every consistent partition refines every round's classes (the
key under a finer consistent partition's context is `eq` only if it is `eq`
under the coarser round's context, `constOrd_eq_mono`, and the round keeps
`eq` members together); at the fixed point no class splits, so its members
compare `eq` under the final context.

Hypotheses: the members' and constructors' names are pairwise distinct
under `==` (`KeysDistinct`, as Lean's names are), and the names the members
reference lie in a set within which `==` is equality (`Faithful N`; since
CQ2.25 the class context and the compiler's address map compare names
exactly while `compareRef` tests the stored hash). For any rule set: the
seed only permutes the start. -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)
open Ix.CompileCert.Loop (except_bind_ok)

/-- A partition of the members `ms` into nonempty classes. -/
def Partition (P : List (List MutConst)) (ms : List MutConst) : Prop :=
  P.flatten.Perm ms ∧ ∀ C ∈ P, C ≠ []

/-- Distinct members of one class compare `eq` under the partition's own
context. -/
def Consistent (addr? : Name → Option Address) (P : List (List MutConst)) : Prop :=
  ∀ C ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≠ b → constOrd addr? (MutConst.ctx P) a b = .ok .eq

/-- Contexts of refining partitions of the same members: the finer
identifies no more. -/
theorem coarser_ctxOf (addr? : Name → Option Address) {ms : List MutConst} (hk : KeysDistinct ms)
    {P Q : List (List MutConst)} (hP : P.flatten.Perm ms) (hQ : Q.flatten.Perm ms) (href : Refines P Q) :
    Coarser (ctxOf addr? (MutConst.ctx P)) (ctxOf addr? (MutConst.ctx Q)) where
  addr := rfl
  dom n := Bool.eq_iff_iff.2 ((ctx_dom_perm hP n).trans (ctx_dom_perm hQ n).symm)
  merge x y nx ny hx hy he :=
    ctx_merge (hk.perm hP.symm) (hk.perm hQ.symm) href x y nx ny hx hy he

/-- **Equality is kept by a coarser partition's context.** -/
theorem constOrd_eq_mono (addr? : Name → Option Address) {ms : List MutConst}
    (hk : KeysDistinct ms) {P Q : List (List MutConst)} (hP : P.flatten.Perm ms)
    (hQ : Q.flatten.Perm ms) (href : Refines P Q) {a b : MutConst}
    (h : constOrd addr? (MutConst.ctx P) a b = .ok .eq) :
    constOrd addr? (MutConst.ctx Q) a b = .ok .eq := by
  unfold constOrd at h ⊢
  cases hc : constP (ctxOf addr? (MutConst.ctx P)) a b with
  | error err => rw [hc] at h; cases h
  | ok r =>
    rw [hc] at h
    simp only [Except.map, Except.ok.injEq] at h
    obtain ⟨s', e'⟩ := constP_eq_mono (coarser_ctxOf addr? hk hP hQ href) a b
      (s := r.strong) (by rw [hc]; obtain ⟨s, o⟩ := r; simp only at h; rw [h])
    rw [e']; rfl

/-! ## The loop -/

/-- Every consistent partition refines `classes`. -/
def Coarsest (addr? : Name → Option Address) (ms : List MutConst)
    (classes : List (List MutConst)) : Prop :=
  ∀ Q, Partition Q ms → Consistent addr? Q → Refines Q classes

theorem sortLoopP_spec {addr? : Name → Option Address} {N : Name → Prop} (hN : Faithful N)
    {ms : List MutConst} (hin : ∀ m ∈ ms, ConstIn N m) (hk : KeysDistinct ms) :
    ∀ (fuel round : Nat) (classes F : List (List MutConst)) (r : Nat),
      Partition classes ms → Coarsest addr? ms classes →
      sortLoopP addr? fuel round classes = .ok (F, r) →
      Partition F ms ∧ Consistent addr? F ∧ Coarsest addr? ms F := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [sortLoopP] at h
  | succ fuel ih =>
    intro round classes F r hP hC h
    simp only [sortLoopP] at h
    obtain ⟨refined, hr, h⟩ := except_bind_ok.1 h
    have hcin : ∀ C ∈ classes, ∀ x ∈ C, ConstIn N x :=
      fun C hC x hx => hin x (hP.1.mem_iff.1 (List.mem_flatten.2 ⟨C, hC, hx⟩))
    obtain ⟨rp, rne, rref, rsame, req, -, rone⟩ :=
      refineClassesP_spec addr? _ hN classes refined hP.2 hcin hr
    have hPr : Partition refined ms := ⟨rp.trans hP.1, rne⟩
    -- every consistent partition still refines the refined classes
    have hCr : Coarsest addr? ms refined := by
      intro Q hQ hcons D hD m hm m' hm'
      obtain ⟨C, hCm, h1, h2⟩ := hC Q hQ hcons D hD m hm m' hm'
      by_cases e : m = m'
      · subst e
        obtain ⟨g, hg, hmg⟩ := List.mem_flatten.1 (rp.mem_iff.2 (List.mem_flatten.2 ⟨C, hCm, h1⟩))
        exact ⟨g, hg, hmg, hmg⟩
      · have heq := hcons D hD m hm m' hm' e
        have heq' := constOrd_eq_mono addr? hk hQ.1 hP.1 (hC Q hQ hcons) heq
        exact rsame C hCm m h1 m' h2 heq'
    split at h
    · rename_i hl
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hF, -⟩ := h
      subst hF
      refine ⟨hPr, ?_, hCr⟩
      -- the fixed point: no class split, so the classes and the result are one partition
      have hsame : Refines classes refined := by
        intro C hCm m hm m' hm'
        obtain ⟨g, hg, hiff⟩ := rone (by simpa using hl) C hCm
        exact ⟨g, hg, (hiff m).2 hm, (hiff m').2 hm'⟩
      intro g hg a ha b hb hab
      exact constOrd_eq_mono addr? hk hP.1 hPr.1 hsame (req g hg a ha b hb hab)
    · exact ih _ refined F r hPr hCr h

/-- **The classes are the coarsest consistent partition**, for the pure
refinement. -/
theorem sortClassesP_coarsest (rules : Rules) {addr? : Name → Option Address} {N : Name → Prop}
    (hN : Faithful N) {sources : List MutConst} (hin : ∀ m ∈ sources, ConstIn N m)
    (hk : KeysDistinct sources) {F : List (List MutConst)}
    (h : sortClassesP rules addr? sources = .ok F) :
    Partition F sources ∧ Consistent addr? F ∧ Coarsest addr? sources F := by
  unfold sortClassesP at h
  by_cases he : sources.isEmpty = true
  · simp only [he, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h; subst h
    have : sources = [] := by simpa using he
    subst this
    refine ⟨⟨by simp, by simp⟩, by simp [Consistent], fun Q hQ _ D hD m hm => ?_⟩
    have := hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D, hD, hm⟩); simp at this
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨classes, rounds⟩, hl, h⟩ := except_bind_ok.1 h
    have hF : classes = F := by
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h
    subst hF
    have hseed : Partition [seedOf rules sources] sources := by
      refine ⟨by simpa using seedOf_perm rules sources, fun C hC => ?_⟩
      simp only [List.mem_singleton] at hC; subst hC
      intro e
      have := (seedOf_perm rules sources).symm
      rw [e] at this
      exact he (by simpa using List.Perm.eq_nil this)
    have hC0 : Coarsest addr? sources [seedOf rules sources] := by
      intro Q hQ _ D hD m hm m' hm'
      refine ⟨seedOf rules sources, by simp, ?_, ?_⟩
      · exact (seedOf_perm rules sources).mem_iff.2 (hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D, hD, hm⟩))
      · exact (seedOf_perm rules sources).mem_iff.2 (hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D, hD, hm'⟩))
    exact sortLoopP_spec hN hin hk _ _ _ classes rounds hseed hC0 hl

/-- **The classes of `sortClasses` are the coarsest consistent partition**,
for every rule set, members whose member and constructor names are pairwise
distinct under `==`, and members whose references lie in a faithful set of
names. -/
theorem sortClasses_coarsest (rules : Rules) {addr? : Name → Option Address} {N : Name → Prop}
    (hN : Faithful N) {sources : List MutConst} (hin : ∀ m ∈ sources, ConstIn N m)
    (hk : KeysDistinct sources) {F : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? sources = .ok (F, stats)) :
    Partition F sources ∧ Consistent addr? F ∧ Coarsest addr? sources F := by
  have := sortClasses_eq rules hN hin hk (addr? := addr?)
  rw [h] at this
  exact sortClassesP_coarsest rules hN hin hk this.symm

end Ix.CompileCert.Canon
