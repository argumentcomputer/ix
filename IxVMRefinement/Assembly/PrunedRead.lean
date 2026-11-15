import IxVMRefinement.Assembly.Closure
import IxVMRefinement.Assembly.ReadBare

/-! # Restricting a reader order to a smaller set of seeds

The public reading starts from the claim and evidence seeds. Filtering an already ordered
closure by reachability from those seeds gives its exact order, including projection owners
that are supplied only by the committed fallback. No cache or store mutation is involved.
-/

namespace IxVM.Refinement.Assembly

open IxVM.Consistency

theorem usedCompiledReachAt_mono {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S T : _root_.Address → Prop} (hST : ∀ a, S a → T a)
    {a : _root_.Address} (h : UsedCompiledReachAt t E S a) :
    UsedCompiledReachAt t E T a := by
  induction h with
  | seed hs hstored => exact .seed (hST _ hs) hstored
  | step _ hedge ih => exact .step ih hedge
  | ground _ hedge ih => exact .ground ih hedge
  | recursor _ hedge ih => exact .recursor ih hedge

/-- The part of `order` reachable from `S`, retaining its original relative order. -/
noncomputable def pruneClosureOrder (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (S : _root_.Address → Prop) (order : List _root_.Address) : List _root_.Address :=
  order.filter fun a =>
    @decide (UsedCompiledReachAt t E S a) (Classical.propDecidable _)

theorem mem_pruneClosureOrder {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S : _root_.Address → Prop} {order : List _root_.Address} {a : _root_.Address} :
    a ∈ pruneClosureOrder t E S order ↔ a ∈ order ∧ UsedCompiledReachAt t E S a := by
  simp only [pruneClosureOrder, List.mem_filter,
    @decide_eq_true_eq _ (Classical.propDecidable _)]

/-- Pruning constructs the exact smaller closure, preserving the dependency order. -/
theorem usedClosureOrderAt_prune {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S T : _root_.Address → Prop} {order : List _root_.Address}
    (horder : UsedClosureOrderAt t E T order) (hST : ∀ a, S a → T a) :
    UsedClosureOrderAt t E S (pruneClosureOrder t E S order) := by
  refine ⟨horder.nodup.filter _, ?_, horder.ordered.filter _⟩
  intro a
  rw [mem_pruneClosureOrder]
  exact ⟨And.right, fun h => ⟨(horder.complete a).mpr (usedCompiledReachAt_mono hST h), h⟩⟩

theorem pruneClosureOrder_append (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (S : _root_.Address → Prop) (xs ys : List _root_.Address) :
    pruneClosureOrder t E S (xs ++ ys) =
      pruneClosureOrder t E S xs ++ pruneClosureOrder t E S ys := by
  simp only [pruneClosureOrder, List.filter_append]

/-- The retained part of an original prefix remains a prefix of the pruned order. -/
theorem pruneClosureOrder_prefix {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S : _root_.Address → Prop} {order front suffix : List _root_.Address}
    (hsplit : order = front ++ suffix) :
    pruneClosureOrder t E S order =
      pruneClosureOrder t E S front ++ pruneClosureOrder t E S suffix := by
  rw [hsplit, pruneClosureOrder_append]

/-- An edge out of the pruned closure remains in it, whether it is an explicit reference,
an implicit ground dependency, or a recursor edge. -/
theorem pruneClosureOrder_closed {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S T : _root_.Address → Prop} {order : List _root_.Address}
    (horder : UsedClosureOrderAt t E T order) (hST : ∀ a, S a → T a)
    {a b : _root_.Address} (ha : a ∈ pruneClosureOrder t E S order)
    (hedge : UsedRecordEdge E a b ∨ Ix.Cert.GroundEdgeAt t E a b ∨ Ix.Cert.RecursorEdge E a b) :
    b ∈ pruneClosureOrder t E S order := by
  have hp := usedClosureOrderAt_prune horder hST
  have hreach := (hp.complete a).mp ha
  apply (hp.complete b).mpr
  rcases hedge with h | h | h
  · exact .step hreach h
  · exact .ground hreach h
  · exact .recursor hreach h

/-- The claim-and-evidence closure required by `ReadIn`, obtained from a role-aware order. -/
theorem usedClosureOrderAt_readSeeds {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {S : _root_.Address → Prop} {order : List _root_.Address}
    (horder : UsedClosureOrderAt t E (fun a => S a ∨ IxVM.Refinement.BindingSeeds t a) order) :
    UsedClosureOrderAt t E
      (fun a => S a ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList)
      (pruneClosureOrder t E
        (fun a => S a ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList) order) := by
  apply usedClosureOrderAt_prune horder
  intro a h
  rcases h with hseed | hevidence
  · exact .inl hseed
  · exact .inr (.inr hevidence)

end IxVM.Refinement.Assembly
