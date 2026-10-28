import Ix.SpecDigest

/-! The unchanged frozen-value guards live in a classic module so their
interpreter sees imported definition bodies. Both the established certificate
audit and the host-admission audit import this module. -/

/-! ## The frozen value

`specVersion` 3 specifies `Iff` and `Nonempty` as blocks and gives the inert
`sorryAx` its type. It adds the `eqns` kind, 44 native definitions and their
anchors, and `Role.usedImplicitly`. A change to the
specification set changes these lines; it
is made on purpose, with `specVersion` (`IxC/Kernel/Audit/Roles.lean`). -/

/-- info: "17058 bytes" -/
#guard_msgs in
#eval match Ix.SpecDigest.specBytes with
  | .ok b => s!"{b.size} bytes"
  | .error e => s!"error: {e}"

/-- info: "2fc3874462090c7e652d69497d8bf1fb31f2c36ba5c36d500072f3e8d0d8d950" -/
#guard_msgs in
#eval match Ix.SpecDigest.specDigest with
  | .ok a => toString a
  | .error e => s!"error: {e}"
