import Ix.Compiler.IxIR2.Liveness

/-!
# Checked liveness examples

The fixture deliberately places value uses in an instruction, the
terminator scrutinee, a constructor edge, and both literal-peel edges.  It
checks exact inference, conservative over-approximation, uncovered-use
rejection, and both resource gates exposed by the block-local checker.
-/

namespace Ix.Compiler.IxIR2.Liveness.Examples

open Ix.Compiler.IxIR2

private def edge (target : BlockId) (values : Array Atom) : Edge :=
  { target, values, credits := #[] }

def mixedBlock : Block :=
  { valueParams := #[.scalar, .scalar]
    creditParams := #[]
    instructions := #[
      .move (.reg 0),
      .apply (.reg 1) #[.reg 2]]
    terminator := .switchValue (.reg 3) #[
      { cid := default, edge := edge 1 #[.reg 0] }]
      (some {
        zero := edge 2 #[.reg 1]
        succ := edge 3 #[.reg 3] }) }

def expectedUses : Array Use := #[
  { value := 0, position := 0 },
  { value := 1, position := 1 },
  { value := 2, position := 1 },
  { value := 3, position := 2 },
  { value := 0, position := 2 },
  { value := 1, position := 2 },
  { value := 3, position := 2 }]

def exactSummary : BlockSummary := { lastUses := #[3, 3, 2, 3] }

/-- Extra liveness is accepted: each claimed bound may exceed the exact
last-use position by an arbitrary amount. -/
def conservativeSummary : BlockSummary := { lastUses := #[4, 5, 3, 4] }

/-- Register two is last used by the `apply` instruction at position one;
the checked certificate rules out a later use even though other values occur
on successor edges. -/
theorem registerTwoNoUseAfter (checked : CheckedBlock mixedBlock)
    (last : checked.summary.lastUse? 2 = some 1) :
    ∀ index, (bound : index < (blockUses mixedBlock).size) →
      (blockUses mixedBlock)[index].value = 2 →
      (blockUses mixedBlock)[index].position ≤ 1 :=
  checked.no_use_after last

def suite : Bool :=
  blockUses mixedBlock == expectedUses &&
  inferBlock mixedBlock == exactSummary &&
  (match inferChecked mixedBlock with
   | .ok checked =>
       checked.summary == exactSummary &&
         checked.stats == { uses := 7, valueSlots := 4 }
   | .error _ => false) &&
  (match checkBlock mixedBlock conservativeSummary with
   | .ok checked => checked.summary == conservativeSummary
   | .error _ => false) &&
  (match checkBlock mixedBlock { lastUses := #[3, 3, 1, 3] } with
   | .error .uncoveredUse => true
   | _ => false) &&
  (match checkBlock mixedBlock { lastUses := #[3, 3, 2] } with
   | .error .uncoveredUse => true
   | _ => false) &&
  (match checkBlockWith
      { Validate.defaultLimits with maxFlowWork := 6 }
      mixedBlock exactSummary with
   | .error (.limit .uses 7 6) => true
   | _ => false) &&
  (match checkBlockWith
      { Validate.defaultLimits with maxValueRegisters := 3 }
      mixedBlock exactSummary with
   | .error (.limit .valueSlots 4 3) => true
   | _ => false)

#guard suite

/-- Proof-carrying result of the executable certificate/rejection suite. -/
structure CheckedSuite : Type where
  accepted : suite = true

def checkSuite : Except String CheckedSuite :=
  if accepted : suite = true then
    .ok { accepted }
  else
    .error "checked block-liveness suite failed"

end Ix.Compiler.IxIR2.Liveness.Examples
