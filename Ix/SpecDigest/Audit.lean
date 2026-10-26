import Ix.SpecDigest

/-! The unchanged frozen-value guards live in a classic module so their
interpreter sees imported definition bodies. Both the established certificate
audit and the host-admission audit import this module. -/

/-! ## The frozen value

`specVersion` 2 (re-frozen 2026-10-20, `ALPHA-COLLAPSE.md` §8.2: the five
compiler-trust roles and the `identity` kind removed). A change to the
specification set changes these lines; it
is made on purpose, with `specVersion` (`IxC/Kernel/Audit/Roles.lean`). -/

/-- info: "8696 bytes" -/
#guard_msgs in
#eval match Ix.SpecDigest.specBytes with
  | .ok b => s!"{b.size} bytes"
  | .error e => s!"error: {e}"

/-- info: "52049b9d09530c92cd2b02115a00ef79f64d99e8b279ee14c42b8b3dc9a94b3f" -/
#guard_msgs in
#eval match Ix.SpecDigest.specDigest with
  | .ok a => toString a
  | .error e => s!"error: {e}"
