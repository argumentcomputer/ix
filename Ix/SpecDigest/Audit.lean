import Ix.SpecDigest

/-! The unchanged frozen-value guards live in a classic module so their
interpreter sees imported definition bodies. Both the established certificate
audit and the host-admission audit import this module. -/

/-! ## The frozen value

`specVersion` 3: `Iff`, `Nonempty` and their constructors and recursors are
block roles, and `sorryAx` has its type (version 2, 2026-10-20, removed the
five compiler-trust roles and the `identity` kind). A change to the
specification set changes these lines; it
is made on purpose, with `specVersion` (`IxC/Kernel/Audit/Roles.lean`). -/

/-- info: "9365 bytes" -/
#guard_msgs in
#eval match Ix.SpecDigest.specBytes with
  | .ok b => s!"{b.size} bytes"
  | .error e => s!"error: {e}"

/-- info: "f09825902503729718c7ab437405b9f87efb97024085f8f2ea10e1e3ca378ba3" -/
#guard_msgs in
#eval match Ix.SpecDigest.specDigest with
  | .ok a => toString a
  | .error e => s!"error: {e}"
