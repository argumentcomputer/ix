module

public import ConLeche.Verify.Inductives.StructInv
import ConLeche.Verify.FastOps

public section

/-!
# The direct recogniser and the projection slots, inverted (task #175 W4c, P3 module 7, part 7)

V-free facts the direct install's assembly reads off the kernel's
recogniser and slot decision:

* `structParts?_inv`: the block's shape facts the recogniser pins —
  the propositionality datum is the result sort's, the recursor is
  `T.rec` at the block's level parameters (plus the large eliminator's
  fresh one), the constructor carries the former's;
* `structProjGuards_getD`: the coarse guard's spelling at a slot.
  (Task #175 S1: the per-slot run and the slot-prefix lemmas went with
  the per-field entries — the table stage is one cons,
  `checkStructProjTable_inv`.)
-/

namespace ConLeche

/-! ## The recogniser -/

/-! ## The guard's spelling -/

theorem structProjGuards_getD (cty : Expr) (nP nF : Nat) (sorts : List Level) {i : Nat}
    (hi : i < nF) :
    (structProjGuards cty nP nF sorts).getD i .zero
      = (List.range i).foldl
          (fun acc j => if structUsedLater cty nP j then Level.max acc (sorts.getD j .zero)
            else acc)
          (sorts.getD i .zero) := by
  unfold structProjGuards
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end ConLeche
