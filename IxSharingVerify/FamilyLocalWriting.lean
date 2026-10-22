import IxSharingVerify.FamilyResidual

/-! Concrete local writings for the residual-forest bridge.
Continuing a telescope through an inline child may cross the non-subadditive
TagN boundary. We charge at most nine bytes for the new header instead of
assuming subadditivity. The actual writing is valid without `SpinesFit`.

This checkpoint justifies the local payload allowance in `residualCharge`.
The global flow cancellation, complete-encoding bound, wire representability
and materializer/guard success remain separate. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel

/-- A model header is at most nine bytes for every natural count. This
does not assert that that count is encodable by a UInt64 field. -/
theorem tag4Size_le_nine (n : Nat) : tag4Size n ≤ 9 := by
  unfold tag4Size Ixon.tagNByteWidth
  repeat' split
  all_goals omega

/-- Continue a legal telescope prefix with any valid writing of its cut
node. An inline continuation is merged structurally, with a fresh-header
allowance rather than the old `SpinesFit` exchange bound. -/
theorem telescope_graft {p : Prep} (hp : PrepWF p) (width : Nat) {avail : Nat → Bool}
    {x j : Nat} (bound : x < p.dag.size) (tele : p.family[x]! ≠ .none)
    (positive : 1 ≤ j) (before : j < p.spineLen[x]!) {sides : List WTree} {tail : WTree}
    (length : sides.length = j)
    (sideValid : ∀ k (hk : k < sides.length), Valid p avail (sideAt p x k) sides[k])
    (tailValid : Valid p avail (spineAt p x j) tail) :
    ∃ out, Valid p avail x out ∧ out.isShare = false ∧
      out.cost p width ≤ 9 + j * (p.dag.node x).sideExtra +
        WTree.costs p width sides + tail.cost p width := by
  by_cases share : tail.isShare = true
  · cases tail with
    | share y =>
      have same : y = spineAt p x j := label_eq tailValid
      subst y
      have available : avail (spineAt p x j) = true := by cases tailValid; assumption
      refine ⟨.tele x j sides (.share (spineAt p x j)),
        .teleCut tele positive before length sideValid available, rfl, ?_⟩
      have header := tag4Size_le_nine j
      simp only [WTree.cost]
      omega
    | node => cases share
    | tele => cases share
  · have inline : tail.isShare = false := Bool.eq_false_iff.mpr share
    obtain ⟨nextBound, nextFamily, nextLength, nextTail, shift, sideShift, sideExtra⟩ :=
      hp.spine_shift bound tele before
    have nextTele : p.family[spineAt p x j]! ≠ .none := by rw [nextFamily]; exact tele
    obtain ⟨k, more, last, rfl, moreLength, moreValid, ending⟩ :=
      valid_tele_inv tailValid inline nextTele
    have combinedLength : (sides ++ more).length = j + k := by simp [length, moreLength]
    have combinedValid : ∀ i (hi : i < (sides ++ more).length),
        Valid p avail (sideAt p x i) (sides ++ more)[i] := by
      intro i hi
      rw [List.getElem_append]
      split
      · rename_i first
        exact sideValid i first
      · rename_i after
        have rest : i - sides.length < more.length := by
          simp only [List.length_append] at hi
          omega
        have valid := moreValid (i - sides.length) rest
        rw [sideShift] at valid
        have index : j + (i - sides.length) = i := by omega
        rwa [index] at valid
    have valid : Valid p avail x (.tele x (j + k) (sides ++ more) last) := by
      rcases ending with ⟨_, cut, lastEq, available⟩ | ⟨full, lastValid⟩
      · have atCut : spineAt p (spineAt p x j) k = spineAt p x (j + k) := shift k
        rw [lastEq, atCut]
        exact .teleCut tele (by omega) (by omega) combinedLength combinedValid
          (by rwa [← atCut])
      · have fullLength : j + k = p.spineLen[x]! := by omega
        rw [fullLength]
        exact .teleFull tele (by rwa [fullLength] at combinedLength)
          combinedValid (by rwa [← nextTail])
    refine ⟨.tele x (j + k) (sides ++ more) last, valid, rfl, ?_⟩
    have header := tag4Size_le_nine (j + k)
    simp only [WTree.cost, WTree.costs_eq, List.map_append, List.sum_append, Nat.add_mul]
    rw [sideExtra]
    omega

/-- Attach one telescope node to valid writings of its side and next
children. The witness is inline, including when the next child is a Share. -/
theorem telescope_one_node {p : Prep} (hp : PrepWF p) (width : Nat) {avail : Nat → Bool}
    {x : Nat} (bound : x < p.dag.size) (tele : p.family[x]! ≠ .none)
    {side next : WTree} (sideValid : Valid p avail (p.dag.node x).sideChild side)
    (nextValid : Valid p avail (snext p x) next) :
    ∃ out, Valid p avail x out ∧ out.isShare = false ∧
      out.cost p width ≤ 9 + (p.dag.node x).sideExtra + side.cost p width + next.cost p width := by
  have sideOne : ∀ k (hk : k < [side].length), Valid p avail (sideAt p x k) [side][k] := by
    intro k hk
    have zero : k = 0 := by simpa using hk
    subst k
    exact sideValid
  rcases hp.spine_step bound tele with ⟨same, length, _⟩ | ⟨_, length, last⟩
  · have nextBound : snext p x < p.dag.size := Nat.lt_trans (hp.snext_lt bound tele) bound
    have nextTele : p.family[snext p x]! ≠ .none := by rw [same]; exact tele
    have nextPositive := (hp.spine (snext p x) nextBound nextTele).1
    obtain ⟨out, valid, inline, cost⟩ := telescope_graft hp width bound tele
      (j := 1) (by decide) (by omega) rfl sideOne nextValid
    refine ⟨out, valid, inline, ?_⟩
    simpa only [Nat.one_mul, WTree.costs, Nat.add_zero] using cost
  · refine ⟨.tele x 1 [side] next, ?_, rfl, ?_⟩
    · have valid : Valid p avail x (.tele x p.spineLen[x]! [side] next) :=
        .teleFull tele (by simpa only [List.length_singleton] using length.symm)
          sideOne (by rwa [last])
      rwa [length] at valid
    · have header := tag4Size_le_nine 1
      simp only [WTree.cost, WTree.costs, Nat.one_mul, Nat.add_zero]
      omega

/-- The two telescope children include exactly one side and one next
child; their order may differ between App and Lam/All. -/
theorem telescope_child_costs {p : Prep} (hp : PrepWF p) (cost : Nat → Nat) {x : Nat}
    (bound : x < p.dag.size) (tele : p.family[x]! ≠ .none) :
    ((p.dag.node x).children.toList.map cost).sum =
      cost (p.dag.node x).sideChild + cost (snext p x) := by
  have headTele : (p.dag.node x).head.family ≠ .none := by
    rwa [hp.family x bound] at tele
  rw [children_toList (hp.dag.children_size bound), List.map_map]
  cases head : (p.dag.node x).head <;>
    simp_all [Head.family, Head.arity, Node.sideChild, snext, Node.spineNext, List.range_succ] <;>
    omega

/-- A concrete valid inline writing realizes the local allowance using
attained minimum-cost writings of the children. No output bound is assumed. -/
theorem inline_local_writing {p : Prep} (hp : PrepWF p) (width : Nat) (avail : Nat → Bool)
    {x : Nat} (bound : x < p.dag.size) :
    ∃ out, Valid p avail x out ∧ out.isShare = false ∧
      out.cost p width ≤ (p.dag.node x).head.ownBytes + 9 + (p.dag.node x).sideExtra +
        ((p.dag.node x).children.toList.map (uCost p width avail)).sum := by
  by_cases tele : p.family[x]! = .none
  · obtain ⟨out, valid, inline, cost⟩ := (hp.exists_opt width avail x bound).2
    refine ⟨out, valid, inline, ?_⟩
    rw [cost]
    unfold uInl inlOf
    rw [ite_eq_left tele, ← Array.foldl_toList, foldl_add_eq_sum]
    omega
  · have sideBound : (p.dag.node x).sideChild < p.dag.size :=
      Nat.lt_trans (hp.sideChild_lt bound tele) bound
    have nextBound : snext p x < p.dag.size := Nat.lt_trans (hp.snext_lt bound tele) bound
    obtain ⟨side, sideValid, sideCost⟩ := (hp.exists_opt width avail _ sideBound).1
    obtain ⟨next, nextValid, nextCost⟩ := (hp.exists_opt width avail _ nextBound).1
    obtain ⟨out, valid, inline, cost⟩ := telescope_one_node hp width bound tele sideValid nextValid
    refine ⟨out, valid, inline, ?_⟩
    rw [sideCost, nextCost] at cost
    rw [telescope_child_costs hp _ bound tele]
    omega

/-- The semantic inline minimum is below the same concrete local charge.
This is the one-node inequality needed by the later residual-flow proof. -/
theorem uInl_le_local {p : Prep} (hp : PrepWF p) (width : Nat) (avail : Nat → Bool)
    {x : Nat} (bound : x < p.dag.size) :
    uInl p width avail x ≤ (p.dag.node x).head.ownBytes + 9 + (p.dag.node x).sideExtra +
      ((p.dag.node x).children.toList.map (uCost p width avail)).sum := by
  obtain ⟨out, valid, inline, cost⟩ := inline_local_writing hp width avail bound
  exact Nat.le_trans ((hp.valid_cost width avail valid bound).2 inline) cost

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.tag4Size_le_nine [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.telescope_graft [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.telescope_one_node [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.telescope_child_costs [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.inline_local_writing [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.uInl_le_local [propext, Classical.choice, Quot.sound]
