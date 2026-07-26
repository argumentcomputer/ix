import Ix.Tc.Verify.Subst

/-!
# Intern-table frame lemmas

The expression walkers in `Ix.Tc.Subst` mutate only the expression side of
`InternTable`.  Their semantic master theorems establish expression support
and table well-formedness, but the run-scoped invariant also tracks the finite
universe range.  This file proves the missing operational frame directly from
the walker definitions: every persistent write is `internExpr`, whose universe
map is unchanged.

The small effect predicates make sequential state threading explicit.  They
are intentionally restricted to anon mode, matching the verified kernel.
-/

namespace Ix.Tc

/-- An `InternM` action leaves the universe intern map unchanged. -/
def InternPreservesUnivs (x : InternM .anon α) : Prop :=
  ∀ it, (x it).2.univs = it.univs

/-- A cached walker leaves the universe intern map unchanged (scratch is
irrelevant and may change). -/
def WalkPreservesUnivs (x : WalkM .anon α) : Prop :=
  ∀ it sc, (x (it, sc)).2.1.univs = it.univs

namespace InternPreservesUnivs

theorem pure (a : α) : InternPreservesUnivs (pure a) := by
  intro it
  rfl

theorem runWalk {x : WalkM .anon α} (h : WalkPreservesUnivs x) :
    InternPreservesUnivs (Ix.Tc.runWalk x) := by
  intro it
  exact h it {}

end InternPreservesUnivs

namespace WalkPreservesUnivs

theorem pure (a : α) : WalkPreservesUnivs (pure a) := by
  intro it sc
  rfl

theorem bind {x : WalkM .anon α} {f : α → WalkM .anon β}
    (hx : WalkPreservesUnivs x)
    (hf : ∀ a, WalkPreservesUnivs (f a)) :
    WalkPreservesUnivs (x >>= f) := by
  intro it sc
  change (f (x (it, sc)).1 (x (it, sc)).2).2.1.univs = it.univs
  exact (hf _ _ _).trans (hx _ _)

theorem scratchGet (key : Address × UInt64) :
    WalkPreservesUnivs (Ix.Tc.scratchGet? key) := by
  intro it sc
  rfl

theorem scratchInsert (key : Address × UInt64) (e : KExpr .anon) :
    WalkPreservesUnivs (Ix.Tc.scratchInsert key e) := by
  intro it sc
  rfl

theorem liftIntern {x : InternM .anon α} (h : InternPreservesUnivs x) :
    WalkPreservesUnivs (liftInternW x) := by
  intro it sc
  exact h it

theorem internExpr (e : KExpr .anon) :
    WalkPreservesUnivs (liftInternW (internExprM e)) := by
  intro it sc
  exact InternTable.internExpr_univs (it := it) e

end WalkPreservesUnivs

/-! ## Lift -/

private theorem liftCached_preservesUnivs (e : KExpr .anon)
    (shift cutoff : UInt64) :
    WalkPreservesUnivs (liftCached e shift cutoff) := by
  induction e generalizing cutoff with
  | var i name info =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ => by
              split
              · exact .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
              · exact .bind (.scratchInsert _ _) fun _ => .pure _
  | fvar id name info =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | sort u info =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | const id us info =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | app f a info ihf iha =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihf cutoff) fun rf =>
                .bind (iha cutoff) fun ra =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | lam name bi ty body info ihty ihbody =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty cutoff) fun rty =>
                .bind (ihbody (cutoff + 1)) fun rbody =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | all name bi ty body info ihty ihbody =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty cutoff) fun rty =>
                .bind (ihbody (cutoff + 1)) fun rbody =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | letE name ty val body nd info ihty ihval ihbody =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty cutoff) fun rty =>
                .bind (ihval cutoff) fun rval =>
                  .bind (ihbody (cutoff + 1)) fun rbody =>
                    .bind (.pure _) fun result =>
                      .bind (.internExpr result) fun interned =>
                        .bind (.scratchInsert _ interned) fun _ => .pure interned
  | prj id field val info ihval =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihval cutoff) fun rval =>
                .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
  | nat v blob info =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | str v blob info =>
      rw [liftCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _

theorem lift_preservesUnivs (e : KExpr .anon) (shift cutoff : UInt64) :
    InternPreservesUnivs (lift e shift cutoff) := by
  rw [lift]
  split
  · exact .pure _
  · exact .runWalk (liftCached_preservesUnivs e shift cutoff)

/-! ## Single substitution -/

private theorem substCached_preservesUnivs (body arg : KExpr .anon)
    (depth : UInt64) :
    WalkPreservesUnivs (substCached body arg depth) := by
  induction body generalizing depth with
  | var i name info =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ => by
              split
              · exact .bind (.liftIntern (lift_preservesUnivs arg depth 0))
                  fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
              · split
                · exact .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
                · exact .bind (.scratchInsert _ _) fun _ => .pure _
  | fvar id name info =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | sort u info =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | const id us info =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | app f a info ihf iha =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihf depth) fun rf =>
                .bind (iha depth) fun ra =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | lam name bi ty inner info ihty ihinner =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | all name bi ty inner info ihty ihinner =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | letE name ty val inner nd info ihty ihval ihinner =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihval depth) fun rval =>
                  .bind (ihinner (depth + 1)) fun rinner =>
                    .bind (.pure _) fun result =>
                      .bind (.internExpr result) fun interned =>
                        .bind (.scratchInsert _ interned) fun _ => .pure interned
  | prj id field val info ihval =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihval depth) fun rval =>
                .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
  | nat v blob info =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | str v blob info =>
      rw [substCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _

theorem subst_preservesUnivs (body arg : KExpr .anon) (depth : UInt64) :
    InternPreservesUnivs (subst body arg depth) := by
  rw [subst]
  split
  · exact .pure _
  · exact .runWalk (substCached_preservesUnivs body arg depth)

/-! ## Simultaneous substitution -/

private theorem simulSubstCached_preservesUnivs (body : KExpr .anon)
    (substs : Array (KExpr .anon)) (depth : UInt64) :
    WalkPreservesUnivs (simulSubstCached body substs depth) := by
  induction body generalizing depth with
  | var i name info =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ => by
              split
              · exact .bind (.liftIntern (lift_preservesUnivs _ depth 0))
                  fun result =>
                    .bind (.scratchInsert _ result) fun _ => .pure result
              · split
                · exact .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
                · exact .bind (.scratchInsert _ _) fun _ => .pure _
  | fvar id name info =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | sort u info =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | const id us info =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | app f a info ihf iha =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihf depth) fun rf =>
                .bind (iha depth) fun ra =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | lam name bi ty inner info ihty ihinner =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | all name bi ty inner info ihty ihinner =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | letE name ty val inner nd info ihty ihval ihinner =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihval depth) fun rval =>
                  .bind (ihinner (depth + 1)) fun rinner =>
                    .bind (.pure _) fun result =>
                      .bind (.internExpr result) fun interned =>
                        .bind (.scratchInsert _ interned) fun _ => .pure interned
  | prj id field val info ihval =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihval depth) fun rval =>
                .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
  | nat v blob info =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | str v blob info =>
      rw [simulSubstCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _

theorem simulSubst_preservesUnivs (body : KExpr .anon)
    (substs : Array (KExpr .anon)) (depth : UInt64) :
    InternPreservesUnivs (simulSubst body substs depth) := by
  rw [simulSubst]
  split
  · exact .pure _
  · exact .runWalk (simulSubstCached_preservesUnivs body substs depth)

/-! ## Reverse instantiation -/

private theorem instantiateRevCached_preservesUnivs (body : KExpr .anon)
    (fvars : Array (KExpr .anon)) (depth : UInt64) :
    WalkPreservesUnivs (instantiateRevCached body fvars depth) := by
  induction body generalizing depth with
  | var i name info =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ => by
              split
              · exact .bind (.scratchInsert _ _) fun _ => .pure _
              · split
                · exact .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
                · exact .bind (.scratchInsert _ _) fun _ => .pure _
  | fvar id name info =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | sort u info =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | const id us info =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | app f a info ihf iha =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihf depth) fun rf =>
                .bind (iha depth) fun ra =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | lam name bi ty inner info ihty ihinner =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | all name bi ty inner info ihty ihinner =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | letE name ty val inner nd info ihty ihval ihinner =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihval depth) fun rval =>
                  .bind (ihinner (depth + 1)) fun rinner =>
                    .bind (.pure _) fun result =>
                      .bind (.internExpr result) fun interned =>
                        .bind (.scratchInsert _ interned) fun _ => .pure interned
  | prj id field val info ihval =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihval depth) fun rval =>
                .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
  | nat v blob info =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | str v blob info =>
      rw [instantiateRevCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _

theorem instantiateRev_preservesUnivs (body : KExpr .anon)
    (fvars : Array (KExpr .anon)) :
    InternPreservesUnivs (instantiateRev body fvars) := by
  rw [instantiateRev]
  split
  · exact .pure _
  · exact .runWalk (instantiateRevCached_preservesUnivs body fvars 0)

/-! ## Free-variable abstraction -/

private theorem abstractFVarsCached_preservesUnivs (body : KExpr .anon)
    (pos : Std.HashMap FVarId UInt64) (n depth : UInt64) :
    WalkPreservesUnivs (abstractFVarsCached body pos n depth) := by
  induction body generalizing depth with
  | var i name info =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ => by
              split
              · exact .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
              · exact .bind (.scratchInsert _ _) fun _ => .pure _
  | fvar id name info =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ => by
              split
              · exact .bind (.internExpr _) fun interned =>
                  .bind (.scratchInsert _ interned) fun _ => .pure interned
              · exact .bind (.scratchInsert _ _) fun _ => .pure _
  | sort u info =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | const id us info =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | app f a info ihf iha =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihf depth) fun rf =>
                .bind (iha depth) fun ra =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | lam name bi ty inner info ihty ihinner =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | all name bi ty inner info ihty ihinner =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihinner (depth + 1)) fun rinner =>
                  .bind (.pure _) fun result =>
                    .bind (.internExpr result) fun interned =>
                      .bind (.scratchInsert _ interned) fun _ => .pure interned
  | letE name ty val inner nd info ihty ihval ihinner =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihty depth) fun rty =>
                .bind (ihval depth) fun rval =>
                  .bind (ihinner (depth + 1)) fun rinner =>
                    .bind (.pure _) fun result =>
                      .bind (.internExpr result) fun interned =>
                        .bind (.scratchInsert _ interned) fun _ => .pure interned
  | prj id field val info ihval =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (ihval depth) fun rval =>
                .bind (.pure _) fun result =>
                  .bind (.internExpr result) fun interned =>
                    .bind (.scratchInsert _ interned) fun _ => .pure interned
  | nat v blob info =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _
  | str v blob info =>
      rw [abstractFVarsCached]
      simp only
      split
      · exact .pure _
      · exact .bind (.pure _) fun _ =>
          .bind (.scratchGet _) fun
            | some cached => .pure cached
            | none => .bind (.pure _) fun _ =>
              .bind (.scratchInsert _ _) fun _ => .pure _

theorem abstractFVars_preservesUnivs (body : KExpr .anon)
    (fvars : Array FVarId) :
    InternPreservesUnivs (abstractFVars body fvars) := by
  rw [abstractFVars]
  split
  · exact .pure _
  · exact .runWalk (abstractFVarsCached_preservesUnivs body _ _ 0)

end Ix.Tc
