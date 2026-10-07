import Ix.CompileCert.Canon.Round

/-!
# M7 L1, the refinement computes the coarsest consistent partition

Design document §2.2 and §3.3 (b). A partition `P` of the members is **consistent** when any two
distinct members of one class compare `eq` under the key read through `P`'s own context
(`MutConst.ctx P`: in-block references by class, constructors by class and position). The
**classes** of Def 2.2 are the coarsest consistent partition. `sortClasses_coarsest`: when
`sortClasses` returns, its classes partition the members, are consistent, and every consistent
partition refines them (so they are the coarsest one, unique as a partition).

The argument is the paper's: every consistent partition refines every round's classes (the
key under a finer consistent partition's context is `eq` only if it is `eq` under the coarser
round's context, `constOrd_eq_mono`, and the round keeps `eq` members together); at the fixed
point no class splits, so its members compare `eq` under the final context.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)

/-- A partition of the members `ms` into nonempty classes. -/
def Partition (P : List (List MutConst)) (ms : List MutConst) : Prop :=
  P.flatten.Perm ms ∧ ∀ C ∈ P, C ≠ []

/-- Distinct members of one class compare `eq` under the partition's own context. -/
def Consistent (rules : Rules) (addr? : Name → Option Address) (P : List (List MutConst)) : Prop :=
  ∀ C ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≠ b → constOrd rules addr? (MutConst.ctx P) a b = .ok .eq

/-- Contexts of refining partitions of the same members: the finer identifies no more. -/
theorem coarser_ctxOf (rules : Rules) (addr? : Name → Option Address) (mode : ExtMode)
    {ms : List MutConst} (hk : KeysDistinct ms) {P Q : List (List MutConst)} (hP : P.flatten.Perm ms)
    (hQ : Q.flatten.Perm ms) (href : Refines P Q) :
    Coarser (ctxOf rules addr? mode (MutConst.ctx P)) (ctxOf rules addr? mode (MutConst.ctx Q)) where
  levels := rfl
  mode := rfl
  addr := rfl
  dom n := by
    show ((MutConst.ctx P)[n]?).isSome = ((MutConst.ctx Q)[n]?).isSome
    rw [ctx_dom_perm hP, ctx_dom_perm hQ]
  merge x y nx ny hx hy he :=
    ctx_merge (hk.perm hP.symm) (hk.perm hQ.symm) href x y nx ny hx hy he

/-- **Equality is kept by a coarser partition's context** (§3.3 (b)). -/
theorem constOrd_eq_mono (rules : Rules) (addr? : Name → Option Address) {ms : List MutConst}
    (hk : KeysDistinct ms) {P Q : List (List MutConst)} (hP : P.flatten.Perm ms)
    (hQ : Q.flatten.Perm ms) (href : Refines P Q) {a b : MutConst}
    (h : constOrd rules addr? (MutConst.ctx P) a b = .ok .eq) :
    constOrd rules addr? (MutConst.ctx Q) a b = .ok .eq := by
  have mono : ∀ mode, (constP (ctxOf rules addr? mode (MutConst.ctx P)) a b).map (·.ord) = .ok .eq →
      (constP (ctxOf rules addr? mode (MutConst.ctx Q)) a b).map (·.ord) = .ok .eq := by
    intro mode e
    cases hc : constP (ctxOf rules addr? mode (MutConst.ctx P)) a b with
    | error err => rw [hc] at e; cases e
    | ok r =>
      rw [hc] at e
      simp only [Except.map, Except.ok.injEq] at e
      obtain ⟨s', e'⟩ := constP_eq_mono (coarser_ctxOf rules addr? mode hk hP hQ href) a b
        (s := r.strong) (by rw [hc]; obtain ⟨s, o⟩ := r; simp only at e; rw [e])
      rw [e']; rfl
  unfold constOrd at h ⊢
  cases ht : rules.tieBreak with
  | inline => simp only [ht] at h ⊢; exact mono _ h
  | blind => simp only [ht] at h ⊢; exact mono _ h
  | byAddress =>
    simp only [ht] at h ⊢
    obtain ⟨b', hb, h⟩ := except_bind_ok.1 h
    have hb' : b' = .eq := by
      by_contra hne
      have : (b' != .eq) = true := by simpa using hne
      simp only [this, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      exact hne h
    subst hb'
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    rw [mono _ hb]
    simp only [bind, Except.bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact mono _ h

/-! ## The loop -/

/-- Every consistent partition refines `classes`. -/
def Coarsest (rules : Rules) (addr? : Name → Option Address) (ms : List MutConst)
    (classes : List (List MutConst)) : Prop :=
  ∀ Q, Partition Q ms → Consistent rules addr? Q → Refines Q classes

theorem sortLoopP_spec (rules : Rules) {addr? : Name → Option Address} (hA : AddrCongr addr?)
    {ms : List MutConst} (hk : KeysDistinct ms) :
    ∀ (fuel round : Nat) (classes F : List (List MutConst)) (r : Nat),
      Partition classes ms → Coarsest rules addr? ms classes →
      sortLoopP rules addr? fuel round classes = .ok (F, r) →
      Partition F ms ∧ Consistent rules addr? F ∧ Coarsest rules addr? ms F := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [sortLoopP] at h
  | succ fuel ih =>
    intro round classes F r hP hC h
    simp only [sortLoopP] at h
    obtain ⟨refined, hr, h⟩ := except_bind_ok.1 h
    obtain ⟨rp, rne, rref, rsame, req, -, rone⟩ :=
      refineClassesP_spec rules hA _ classes refined hP.2 hr
    have hPr : Partition refined ms := ⟨rp.trans hP.1, rne⟩
    -- every consistent partition still refines the refined classes
    have hCr : Coarsest rules addr? ms refined := by
      intro Q hQ hcons D hD m hm m' hm'
      obtain ⟨C, hCm, h1, h2⟩ := hC Q hQ hcons D hD m hm m' hm'
      by_cases e : m = m'
      · subst e
        obtain ⟨g, hg, hmg⟩ := List.mem_flatten.1 (rp.mem_iff.2 (List.mem_flatten.2 ⟨C, hCm, h1⟩))
        exact ⟨g, hg, hmg, hmg⟩
      · have heq := hcons D hD m hm m' hm' e
        have heq' := constOrd_eq_mono rules addr? hk hQ.1 hP.1 (hC Q hQ hcons) heq
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
      exact constOrd_eq_mono rules addr? hk hP.1 hPr.1 hsame (req g hg a ha b hb hab)
    · exact ih _ refined F r hPr hCr h

/-- **The classes are the coarsest consistent partition** (Def 2.2; §3.3 (b), old plan Prop 2.1),
for the pure refinement. -/
theorem sortClassesP_coarsest (rules : Rules) {addr? : Name → Option Address} (hA : AddrCongr addr?)
    {sources : List MutConst} (hk : KeysDistinct sources) {F : List (List MutConst)}
    (h : sortClassesP rules addr? sources = .ok F) :
    Partition F sources ∧ Consistent rules addr? F ∧ Coarsest rules addr? sources F := by
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
    have hC0 : Coarsest rules addr? sources [seedOf rules sources] := by
      intro Q hQ _ D hD m hm m' hm'
      refine ⟨seedOf rules sources, by simp, ?_, ?_⟩
      · exact (seedOf_perm rules sources).mem_iff.2 (hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D, hD, hm⟩))
      · exact (seedOf_perm rules sources).mem_iff.2 (hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D, hD, hm'⟩))
    exact sortLoopP_spec rules hA hk _ _ _ classes rounds hseed hC0 hl

/-- **The classes of `sortClasses` are the coarsest consistent partition** (Theorem 4.2's
"classes"; design document §3.3 (b), §3.5 (ii)), for every rule set with `portFixes := true`,
an address map answering alike for `==` names, and members whose member and constructor names
are pairwise distinct under `==`. -/
theorem sortClasses_coarsest {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {sources : List MutConst}
    (hk : KeysDistinct sources) {F : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? sources = .ok (F, stats)) :
    Partition F sources ∧ Consistent rules addr? F ∧ Coarsest rules addr? sources F := by
  have := sortClasses_eq hpf hA hk
  rw [h] at this
  exact sortClassesP_coarsest rules hA hk this.symm

end Ix.CompileCert.Canon
