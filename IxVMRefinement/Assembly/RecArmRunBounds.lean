import IxC.Ixon.Types

/-! # The count bounds an accepted run gives at a standalone native recursor

A standalone recursor record `rc` whose major premise is member `ind` of the block named by the
inductive projection `ip` is checked by `check_const`'s `Rec` arm. The run that accepts it loads
both records, and the loads themselves bound the counts the comparison's generators compute
with:

* `Convert::lvls_to_field` asserts a record's level count below `2^32`, on the recursor and on
  the member;
* `UInt64::to_field` asserts the member's parameter and index counts and the projection's
  member index below `2^56` (the top byte is zero), and the converted constructor count is
  below `2^56`;
* a loaded record is below `2^32` bytes, so the recursor has fewer than `2^33` rules.

`RecArmRunBounds` is their conjunction. It mentions no registered family, no role table and no
validation limit, and every conjunct is a fact of the two loads; the module
`TypingRecLateRunBounds` derives it from the observations of the arm. The per-constructor
field count is not here: a run bounds it where it loads the constructor
(`Decl.NatCtorLoadCountT`), and the lengths of the telescopes of recursive fields are bounded
where the run passes the telescope it built to a callee (`Decl.teleRep_length_lt`).

The definition is kept apart from the theorems about runs so that an executable can evaluate
it on a compiled record.
-/

namespace IxVM.Refinement.Typing

/-- **The count bounds of an accepted native recursor's two loads** (module docstring): the
recursor's level count and rule count, and the member's level, parameter, index and constructor
counts with the projection's member index. -/
def RecArmRunBounds (rc : Ixon.Recursor) (ip : Ixon.InductiveProj) (ind : Ixon.Inductive) :
    Prop :=
  rc.lvls.toNat < 4294967296 ∧
  rc.rules.size < 8589934592 ∧
  ind.lvls.toNat < 4294967296 ∧
  ind.params.toNat < 72057594037927936 ∧
  ind.indices.toNat < 72057594037927936 ∧
  ind.ctors.size < 72057594037927936 ∧
  ip.idx.toNat < 72057594037927936

instance (rc : Ixon.Recursor) (ip : Ixon.InductiveProj) (ind : Ixon.Inductive) :
    Decidable (RecArmRunBounds rc ip ind) := by
  unfold RecArmRunBounds
  infer_instance

/-- **The recursor's binder count is below `2^58`**: parameters, the motive, one minor premise
per constructor, indices and the major premise. A represented bound variable admits indices
below `2^63` (`Core.Tm.bvarLocal`), and a natural below the field's modulus is its own cast. -/
theorem RecArmRunBounds.depth_lt {rc : Ixon.Recursor} {ip : Ixon.InductiveProj}
    {ind : Ixon.Inductive} (hb : RecArmRunBounds rc ip ind) :
    ind.params.toNat + 1 + ind.ctors.size + ind.indices.toNat + 1 < 288230376151711744 := by
  obtain ⟨-, -, -, h4, h5, h6, -⟩ := hb
  omega

/-- **The binder count inside a minor premise and inside an induction hypothesis is below
`2^59`**, for a constructor whose field count `nF` the run bounded at its load, with `l`
recursive fields among them and an induction-hypothesis telescope of length `tele` that the
run built as a list. -/
theorem RecArmRunBounds.minor_depth_lt {rc : Ixon.Recursor} {ip : Ixon.InductiveProj}
    {ind : Ixon.Inductive} (hb : RecArmRunBounds rc ip ind) {nF l tele : Nat}
    (hnF : nF < 72057594037927936) (hl : l ≤ nF) (ht : tele < 549755813888) :
    ind.params.toNat + 1 + ind.ctors.size + nF + l + tele < 576460752303423488 := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := hb
  omega

end IxVM.Refinement.Typing
