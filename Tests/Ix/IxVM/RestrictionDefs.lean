import Lean

/-! # Positive controls for the rule-shaped core's restrictions (fixtures)

IxVM's moves are restricted to instances of the certified kernel's rules
(`IxC/Kernel/Rules/Rel.lean`). Nothing in the `ci:ixvm` tier reached the restricted
cases, so each restriction gets a small case it now refuses, next to a control it
must still accept. These are ordinary, kernel-checked Lean declarations.

* Structure-η ι (`Red.rescueEta`) needs the structure's sort to be never zero
  (`capsNeverZero`). Lean's kernel also fires it at a `Sort u` structure; IxVM, like
  IxC, no longer does. `etaIotaSortU` holds in Lean only by that move;
  `etaIotaType` is the same statement at a `Type` structure.

The other two restrictions (`.proj` on an indexed family; structure η at a
recursive one-constructor type) are refused by Lean's kernel as well: their cases
are records Lean cannot produce, so they have no control here. -/

namespace Tests.Ix.IxVM.RestrictionDefs

universe u

set_option bootstrap.inductiveCheckResultingUniverse false in
/-- A one-constructor, field-less, index-free inductive at `Sort u` (structure-like; a
proposition at `u = 0`, like `PUnit`). Lean refuses a possibly-`Prop` result sort unless
`bootstrap.inductiveCheckResultingUniverse` is off, as it is for `PUnit` itself. -/
inductive PU : Sort u where
  | mk : PU

/-- The same at `Type`: never a proposition. -/
inductive PT : Type where
  | mk : PT

/-- Holds in Lean only by structure-η ι at a `Sort u` structure: the major `x` is a
variable. -/
theorem etaIotaSortU (x : PU.{u}) : @PU.rec.{1, u} (fun _ => Nat) 5 x = 5 := rfl

/-- The control: the same at a `Type` structure, where structure-η ι is a rule. -/
theorem etaIotaType (x : PT) : @PT.rec.{1} (fun _ => Nat) 5 x = 5 := rfl

end Tests.Ix.IxVM.RestrictionDefs
