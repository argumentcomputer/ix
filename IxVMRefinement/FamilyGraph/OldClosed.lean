import IxVMRefinement.FamilyGraph.Check
import IxVMRefinement.Claim.RoleTable

/-! # The earlier closure clause has no inhabitant at a nested family

`FamGraph.famClosed` (`Assembly/FamilyFold.lean`) asks of every reference a family record uses
that it be top-walked below the block, covered, or a constant address of the block or of the
record. A nested family's record uses the constructors of the container it nests through. They
are constant addresses of the container's block; the walk checks that block's members and does
not reach its constructors' addresses, and no role covers them.

`OldClosedFailsP d t E₀` is the bounded statement that some family record of the data uses a
reference that is not top-walked, not covered, and a constant address of neither the block nor
the record. `not_famGraph_of_fails` refutes `FamGraph` from it, at the predicates the data
defines, for every witness environment and every advice relation. -/

namespace IxVM.Refinement.Typing.GraphCheck

open IxVM.Consistency
open IxVM.Refinement.Typing

set_option linter.unusedVariables false

/-- No walked role is bound to `x`, bounded over the table. -/
theorem not_covered_of_bound {t : Ix.Kernel.RoleTable} {x : Addr}
    (h : ∀ q ∈ t.bound.toList, q.2 = x → walkedRole q.1 = false) : ¬ Covered t x := by
  rintro ⟨r, ha, hw⟩
  have hm := IxVM.Refinement.Claim.mem_bound_of_addressOf_eq_some ha
  have h2 : walkedRole r = false := h (r, x) hm rfl
  rw [h2] at hw
  cases hw

/-- **Some family record uses a reference the earlier closure clause does not allow**:
not top-walked, not covered, a constant address of neither the block nor the record. -/
abbrev OldClosedFailsP (d : GraphData) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop :=
  ∃ p ∈ d.fam, assoc d.fam p.1 = some p.2 ∧
    ∃ c ∈ recordOf E₀ p.2, ∃ i ∈ usedRefIdxs c, ∃ x ∈ c.refs[i]?,
      x ∉ d.tops ∧ (∀ q ∈ t.bound.toList, q.2 = x → walkedRole q.1 = false) ∧
      (∀ cb ∈ recordOf E₀ p.1, ¬ ConstAddrP p.1 cb x) ∧ ¬ ConstAddrP p.2 c x

/-- **The earlier graph has no inhabitant** where a family record uses such a reference. -/
theorem not_famGraph_of_fails {d : GraphData} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {adv : Addr → Addr → Prop} (h : OldClosedFailsP d t E₀) :
    ¬ FamGraph t envT E₀ d.Top d.rank d.famOf adv := by
  intro hF
  obtain ⟨p, hp, hfp, c, hc, i, hi, x, hx, hnt, hncov, hnB, hnrb⟩ := h
  rcases hF.famClosed p.1 p.2 x hfp ⟨c, i, Option.mem_def.mp hc, hi, Option.mem_def.mp hx⟩ with
    ⟨hT, -⟩ | hcov | ⟨cb, hcb, hxB⟩ | ⟨crb, hcrb, hxr⟩
  · exact hnt hT
  · exact not_covered_of_bound hncov hcov
  · exact hnB cb (Option.mem_def.mpr hcb) (constAddrP_of hxB)
  · have hcc : crb = c := Option.some.inj (hcrb.symm.trans (Option.mem_def.mp hc))
    rw [hcc] at hxr
    exact hnrb (constAddrP_of hxr)

end IxVM.Refinement.Typing.GraphCheck
