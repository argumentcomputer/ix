module

public import IxC.Kernel.Roles

@[expose] public section

/-! # The validation schedule

IxVM validates a binding's roles group by group
(`IxVM/IxVM/Modules/KernelRoles.lean`). A group's roles are bound together
(`Role.block`), and every role a group needs (`Role.deps`) is in an earlier
group. A group is validated under a context that admits only groups before
it, so a native rule never takes part in its own validation. The order and
its two boundaries decide which native rules each validation may use, so the
specification digest commits to them (`Ix.SpecDigest.specBytes`), and the
rendered circuit (`IxVM.RoleSpecGen`) reads them from here.

The axioms come before the well-founded operations, whose certificates use
`propext`. The tail comes last: the well-founded operations' groups, the
groups of the definitions specified by their equations, and the groups that
need them. The well-founded groups occupy a contiguous block before the first
equation group. The circuit validates that block under the groups before it
(`first_well_founded_group`), and later groups under the prefix before the
equation groups (`first_equation_group`). Thus the well-founded operations
cannot validate each other through native rules, while later checks can use
them after admission. Equation definitions cannot validate each other through
their native rules. `Schedule.ofGroups` checks the order and computes both
boundaries. -/

namespace Ix.SpecDigest

open Ix.Kernel

/-- The groups, by their first role, in validation order. -/
def groupOrder : List Role :=
  [.nat, .eq, .punit, .empty, .false, .quot, .char, .string, .list, .charOfNat,
   .stringOfList, .bool, .natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq,
   .natBle, .true, .and, .iff, .nonempty, .propext, .choice, .sorryAx,
   .notProp, .decidable, .natLe, .int, .intLe, .bitVec, .byteArray,
   .natDiv, .natMod, .natGcd, .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight,
   .decidableDecide, .ofDecideEqTrue, .ofDecideEqFalse, .natDecEq, .natDecLe, .natDecLt,
   .intNegOfNat, .intSubNatNat, .intNeg, .intAdd, .intSub, .intMul, .intNatAbs, .intEdiv,
   .intEmod, .intPow, .bitVecToNat, .bitVecUlt, .stringDecEq, .stringToByteArray,
   .listAppend, .stringAppend, .ifThenElse, .intDecEq, .intDecLe, .intDecLt, .intBmod, .intBdiv,
   .charUtf8Size, .stringUtf8ByteSize, .stringBack]

/-- The groups, in validation order. -/
def groups : List (List Role) := groupOrder.map Role.block

/-- The position of `r`'s group in `orderedGroups`; their count when no group
holds `r`. -/
def groupOf (r : Role) (orderedGroups : List (List Role) := groups) : Nat :=
  (orderedGroups.findIdx? (·.contains r)).getD orderedGroups.length

/-- The roles a group needs outside itself. -/
def groupNeeds (g : List Role) : List Role :=
  (g.flatMap Role.deps).eraseDups.filter (!g.contains ·)

/-- A well-founded operation: its equations are certificates, which carry
hypotheses. -/
def isWellFoundedOp (r : Role) : Bool :=
  match r.spec (md := .anon) with
  | .ops _ eqs => eqs.any (!·.1.isEmpty)
  | _ => false

/-- A definition specified by its equations (`Spec.eqns`). -/
def isEquationDef (r : Role) : Bool :=
  match r.spec (md := .anon) with
  | .eqns .. => true
  | _ => false

/-- A group of well-founded operations. -/
def wellFounded (g : List Role) : Bool := g.any isWellFoundedOp

/-- A group that must follow the initial structural prefix: a well-founded
operation's, or a definition's specified by its equations. -/
def tailOnly (g : List Role) : Bool := wellFounded g || g.any isEquationDef

/-- The order covers every role once, each group is a block, and every role a
group needs is in an earlier group. -/
def checkOrder (orderedGroups : List (List Role)) : Except String Unit := do
  let flat := orderedGroups.flatten
  unless flat.length == Role.all.length && Role.all.all flat.contains do
    throw "role groups do not cover every role exactly once"
  for (g, i) in orderedGroups.zipIdx do
    for r in g do
      unless Role.block r == g do throw s!"role group {i} is not {r.leanName}'s block"
    for r in groupNeeds g do
      unless groupOf r orderedGroups < i do
        throw s!"role group {i} needs {r.leanName}, which is not earlier"

/-- The index of the first group of the tail. Every group that must be in
the tail is (`tailOnly`), and so is every group that needs a tail group;
no other group is. `firstEquationGroup` additionally checks that its initial
block consists exactly of the well-founded operations. -/
def firstWellFoundedGroup (orderedGroups : List (List Role) := groups) : Except String Nat := do
  let some first := orderedGroups.findIdx? tailOnly
    | throw "no well-founded operation's group"
  for (g, i) in orderedGroups.zipIdx do
    let needsTail := (groupNeeds g).any fun r => first ≤ groupOf r orderedGroups
    unless (tailOnly g || needsTail) == decide (first ≤ i) do
      throw s!"role group {i}: the tail must be exactly the groups that need it"
  pure first

/-- The first equation group follows a nonempty contiguous block containing
every well-founded group. This preserves the well-founded validation context
and excludes equation definitions' native rules from later validation.
Coverage and dependency order are checked separately (`checkOrder`). -/
def firstEquationGroup (orderedGroups : List (List Role) := groups) : Except String Nat := do
  let some firstWf := orderedGroups.findIdx? wellFounded
    | throw "no well-founded operation's group"
  let some firstEquation := orderedGroups.findIdx? (·.any isEquationDef)
    | throw "no definition-equation group"
  unless firstWf < firstEquation do
    throw "equation groups must follow the well-founded validation block"
  for (group, index) in orderedGroups.zipIdx do
    unless wellFounded group == decide (firstWf ≤ index ∧ index < firstEquation) do
      throw s!"role group {index}: well-founded groups must form the block before the equation groups"
  return firstEquation

/-- **A validation schedule**: the groups in validation order and the two
boundaries the circuit validates them under (`first_well_founded_group`,
`first_equation_group`). -/
structure Schedule where
  groups : List (List Role)
  firstWellFounded : Nat
  firstEquation : Nat
  deriving BEq

/-- The schedule of `orderedGroups`, with its boundaries, once the order is
checked (`checkOrder`, `firstWellFoundedGroup`, `firstEquationGroup`). -/
def Schedule.ofGroups (orderedGroups : List (List Role)) : Except String Schedule := do
  checkOrder orderedGroups
  let firstWellFounded ← firstWellFoundedGroup orderedGroups
  let firstEquation ← firstEquationGroup orderedGroups
  return { groups := orderedGroups, firstWellFounded, firstEquation }

/-- A schedule is valid when its boundaries are its order's own. -/
def Schedule.check (s : Schedule) : Except String Unit := do
  unless (← Schedule.ofGroups s.groups) == s do
    throw "the schedule's boundaries are not its order's"

/-- **The current schedule**: `groups`, checked, with its boundaries. -/
def Schedule.current : Except String Schedule := Schedule.ofGroups Ix.SpecDigest.groups

end Ix.SpecDigest

end
