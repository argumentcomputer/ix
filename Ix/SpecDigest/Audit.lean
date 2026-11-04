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

The composed encoding adds 669 bytes to the earlier 103-role specification:
the six Iff/Nonempty family rows now carry complete blocks, and sorryAx carries
its exact type and Bool dependency. Replacing only those rows reproduces the
earlier 17058-byte encoding and digest; every other role row is unchanged. -/

/-- info: "17727 bytes" -/
#guard_msgs in
#eval match Ix.SpecDigest.specBytes with
  | .ok b => s!"{b.size} bytes"
  | .error e => s!"error: {e}"

/-- info: "6d02153ea311f3efd1778c49b2ee5f31e79a0bae95e533a08d4914fc05572d33" -/
#guard_msgs in
#eval match Ix.SpecDigest.specDigest with
  | .ok a => toString a
  | .error e => s!"error: {e}"
