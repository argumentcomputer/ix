module
public import ConLeche.Kernel.Expr

@[expose] public section

/-!
# One toolchain's Nat-operation pins (task #273)

A **pin variant**: the pinned defining expressions and certificate
proof blobs of the eight pin-certified `Nat` operations as ONE
toolchain's generator produced them (`pins/<toolchain>.json`, see
`pins/README.md`).  `ConLeche/Kernel/NatOpPins.lean` splices one such
record per committed dump and lists them in `natOpPinSets`; the install
gate (`checkDivModPin`, `ConLeche/Kernel/Checker.lean`) tries the
variants of the list it is **given** — a parameter threaded from the
fold since task #304, `natOpPinSets` in the shipped checker — in that
order, and enables the operation's literal fast path on the first
whose guards pass, whose pin is definitionally equal to the stream's
stored value and whose certificates check.

The record is data the checker reads; the model never inspects a pin
or a proof blob (the certificate *statements* it consumes are
hand-pinned in `Checker.lean` and shared by every variant).
-/

namespace ConLeche

/-- The pins of one toolchain: eight pinned defining expressions and
eight certificate-proof lists, in the order of `natDivModNames`'
family (`div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`,
`shiftRight`), plus the toolchain string for diagnostics. -/
structure NatOpPinSet where
  /-- The generating toolchain (`lean-toolchain` at generation time),
  named in the decline message when no variant matches. -/
  toolchain : String
  divPin : Expr
  modPin : Expr
  gcdPin : Expr
  landPin : Expr
  lorPin : Expr
  xorPin : Expr
  shiftLeftPin : Expr
  shiftRightPin : Expr
  divProofs : List Expr
  modProofs : List Expr
  gcdProofs : List Expr
  landProofs : List Expr
  lorProofs : List Expr
  xorProofs : List Expr
  shiftLeftProofs : List Expr
  shiftRightProofs : List Expr

end ConLeche
