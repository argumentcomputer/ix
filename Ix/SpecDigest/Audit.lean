import Ix.SpecDigest

/-! The frozen-value guards live in a classic module so their
interpreter sees imported definition bodies. Both the established certificate
audit and the host-admission audit import this module. -/

/-! ## The frozen value

`specVersion` 3 specifies `Iff` and `Nonempty` as blocks and gives the inert
`sorryAx` its type. It adds the `eqns` kind, 44 native definitions and their
anchors, and `Role.usedImplicitly`. A change to the
specification set changes these lines; it
is made on purpose, with `specVersion` (`IxC/Kernel/Audit/Roles.lean`).
`specVersion` 4 makes the decision procedures depend on the `of_decide_eq_*`
roles their native rules answer with (`Role.deps`): 9 more dependency entries,
19436 bytes. `specVersion` 5 adds the compiler-trust roles: three inert axioms of
their exact types and the two opaques their types mention, as anchors; the
schedule gains their five groups after `sorryAx`'s (77 groups): 19730 bytes.

`encodingVersion` 2 commits, beside the specifications, to what IxVM reads
off each role's identity (its name, inertness, quotient kind and native rule)
and to the validation schedule (the 72 groups in order and the two
boundaries). The specification set is unchanged, so `specVersion` and every
role table are too. Under version 1 (no version field, the roles alone) the
encoding was 17727 bytes, with digest
6d02153ea311f3efd1778c49b2ee5f31e79a0bae95e533a08d4914fc05572d33; version 2
adds 1700 bytes, with digest
e6f717602b5c3d293803bcc6165dddcbf2c6163b49bc4e5704505cf286856fa9 (19730 bytes).
Version 3 drops the binder and let contracts from the encoding (kernel terms
carry no modes): 1384 bytes fewer. -/

/-- info: "18346 bytes" -/
#guard_msgs in
#eval match Ix.SpecDigest.specBytes with
  | .ok b => s!"{b.size} bytes"
  | .error e => s!"error: {e}"

/-- info: "43b34c7a1e95e869697f5d99839ea13aa50241c311228fe3a19454f7bb942aa1" -/
#guard_msgs in
#eval match Ix.SpecDigest.specDigest with
  | .ok a => toString a
  | .error e => s!"error: {e}"

/-! ## The schedule

The current schedule, and the digest's commitment to it: the current schedule
with one change at a time gives other bytes. Swapping the first two groups
(`Nat` and `Eq`, which need nothing) is itself a valid order, so a circuit
validating in that order could be sound, and it would carry another digest.
Moving either boundary gives a schedule that `Schedule.check` refuses, and
other bytes as well. -/

namespace Ix.SpecDigest.Audit

open Ix.SpecDigest

/-- `xs` with its first two entries swapped. -/
def swapFirstTwo {α : Type} : List α → List α
  | a :: b :: rest => b :: a :: rest
  | xs => xs

/-- Each change to the current schedule: its name, whether `Schedule.check`
accepts the changed schedule, and whether its bytes differ from `specBytes`. -/
def mutants : Except String (List (String × Bool × Bool)) := do
  let s ← Schedule.current
  let bytes ← specBytes
  let swapped ← Schedule.ofGroups (swapFirstTwo s.groups)
  let changed : List (String × Schedule) :=
    [("first two groups swapped", swapped),
     ("well-founded boundary moved", { s with firstWellFounded := s.firstWellFounded + 1 }),
     ("equation boundary moved", { s with firstEquation := s.firstEquation - 1 })]
  changed.mapM fun (name, m) => do
    return (name, (Schedule.check m).isOk, (← specBytesWith m) != bytes)

end Ix.SpecDigest.Audit

/-- info: "77 groups; well-founded from 38, equations from 46" -/
#guard_msgs in
#eval match Ix.SpecDigest.Schedule.current with
  | .ok s => s!"{s.groups.length} groups; well-founded from {s.firstWellFounded}, equations from {s.firstEquation}"
  | .error e => s!"error: {e}"

/-- info: [("first two groups swapped", true, true), ("well-founded boundary moved", false, true),
 ("equation boundary moved", false, true)] -/
#guard_msgs (whitespace := lax) in
#eval match Ix.SpecDigest.Audit.mutants with
  | .ok ms => ms
  | .error e => [(s!"error: {e}", false, false)]

#guard match Ix.SpecDigest.Audit.mutants with
  | .ok ms => ms.map (·.2) == [(true, true), (false, true), (false, true)]
  | .error _ => false
