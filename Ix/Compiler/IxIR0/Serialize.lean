import Ix.Compiler.IxIR.Encoding
import Ix.Compiler.IxIR0.Basic

/-!
# IxIR₀ canonical hash preimages

Every constructor of the erased semantic IR has an explicit byte spelling.
The top-level declaration preimage is domain-separated as
`compilatrix/ixir0/decl/1`, followed by NUL and the declaration payload.
References retain their exact 32-byte address; recursive recursor calls remain
cycle-free because `RecRule.rhs` uses the rule environment's self binder.

This module defines artifact identity, not an ingress decoder. A later store
format may frame the same payloads, but changing these bytes requires an
explicit address-version roll.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR

namespace Literal

/-- Canonical literal payload. -/
def bytes : Literal → ByteArray
  | .nat value => Encoding.tag 0 ++ Encoding.nat value
  | .str value => Encoding.tag 1 ++ Encoding.string value

end Literal

namespace Expr

/-- Canonical recursive expression payload. -/
def bytes : Expr → ByteArray
  | .var index => Encoding.tag 0 ++ Encoding.nat index
  | .ref address => Encoding.tag 1 ++ Encoding.address address
  | .app fn arg => Encoding.tag 2 ++ bytes fn ++ bytes arg
  | .lam uses body =>
      Encoding.tag 3 ++ Encoding.tag uses.toBits ++ bytes body
  | .letE uses value body =>
      Encoding.tag 4 ++ Encoding.tag uses.toBits ++ bytes value ++ bytes body
  | .proj index struct => Encoding.tag 5 ++ Encoding.nat index ++ bytes struct
  | .lit literal => Encoding.tag 6 ++ literal.bytes
  | .erased => Encoding.tag 7

end Expr

namespace RecRule

/-- Canonical recursor-rule payload. -/
def bytes (rule : RecRule) : ByteArray :=
  Encoding.nat rule.fields ++ rule.rhs.bytes

end RecRule

namespace Decl

/-- The versioned domain prefix for IxIR₀ declaration identities. -/
def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir0/decl/1" ++ Encoding.tag 0

/-- Canonical declaration payload, without the address domain. -/
def payloadBytes : Decl → ByteArray
  | .defn result body =>
      Encoding.tag 0 ++ Encoding.tag result.toBits ++ body.bytes
  | .ctor tag arity =>
      Encoding.tag 1 ++ Encoding.nat tag ++ Encoding.nat arity
  | .recursor numArgs natLit rules =>
      Encoding.tag 2 ++ Encoding.nat numArgs ++ Encoding.bool natLit ++
        Encoding.array RecRule.bytes rules
  | .extern arity => Encoding.tag 3 ++ Encoding.nat arity

/-- Complete canonical hash preimage for one IxIR₀ declaration. -/
def preimage (decl : Decl) : ByteArray :=
  addressDomain ++ payloadBytes decl

/-- BLAKE3 content address of an IxIR₀ declaration. -/
def address (decl : Decl) : Address :=
  Address.blake3 decl.preimage

/-- Pair a declaration with its computed content address. -/
def addressed (decl : Decl) : Address × Decl :=
  (decl.address, decl)

/-- Address equality exposes byte identity under exactly the pairwise
collision premise for these two preimages. -/
theorem address_eq_iff_preimage_eq (left right : Decl)
    (hcollision : Address.Blake3NoCollision left.preimage right.preimage) :
    left.address = right.address ↔ left.preimage = right.preimage := by
  constructor
  · exact hcollision
  · intro h
    simp only [address]
    rw [h]

@[simp] theorem addressed_fst (decl : Decl) : decl.addressed.1 = decl.address :=
  rfl

@[simp] theorem addressed_snd (decl : Decl) : decl.addressed.2 = decl :=
  rfl

end Decl

/-! Small format-freezing structural vectors; BLAKE3 vectors live in the
compiled test executable because the current hash implementation is FFI. -/

#guard Literal.bytes (.nat 128) == ByteArray.mk #[0, 128, 1]
#guard Expr.bytes (.lam .many (.var 0)) == ByteArray.mk #[3, 3, 0, 0]
#guard Decl.payloadBytes (.defn .shared (.lam .many (.var 0))) ==
  ByteArray.mk #[0, 1, 3, 3, 0, 0]
#guard Decl.payloadBytes (.recursor 1 true #[⟨0, .erased⟩]) ==
  ByteArray.mk #[2, 1, 1, 1, 0, 7]

end Ix.Compiler.IxIR0
