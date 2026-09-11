import Ix.Compiler.IxIR.Encoding
import Ix.Compiler.IxIR0.Serialize
import Ix.Compiler.IxIR1.Basic

/-!
# IxIR₁ canonical hash preimages

Every first-order operation, branch, and declaration has an explicit byte
spelling. The top-level declaration preimage is domain-separated as
`compilatrix/ixir1/decl/2`, followed by NUL and the declaration payload. Version
2 commits the owner-sensitive dynamic-PAP-entry bit on function declarations.
`callSelf` prevents an ordinary recursive function from placing its own digest
inside its preimage; other call and PAP edges retain exact 32-byte addresses.

The mutually nested `Code`/`Alt` grammar is encoded with an explicit list walk,
matching the generated nested recursor while remaining executable by Lean's
code generator.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR

namespace Atom

/-- Canonical atom payload. -/
def bytes : Atom → ByteArray
  | .var index => Encoding.tag 0 ++ Encoding.nat index
  | .lit literal => Encoding.tag 1 ++ literal.bytes
  | .erased => Encoding.tag 2

end Atom

namespace CtorId

/-- Canonical constructor identity. -/
def bytes (cid : CtorId) : ByteArray :=
  Encoding.address cid.block ++ Encoding.nat cid.indIdx ++
    Encoding.nat cid.cidx

end CtorId

namespace Op

/-- Canonical primitive-operation payload. -/
def bytes : Op → ByteArray
  | .pure atom => Encoding.tag 0 ++ atom.bytes
  | .alloc world cid args =>
      Encoding.tag 1 ++ Encoding.tag world.toBits ++ cid.bytes ++
        Encoding.array Atom.bytes args
  | .reuse target cid args =>
      Encoding.tag 2 ++ target.bytes ++ cid.bytes ++
        Encoding.array Atom.bytes args
  | .free target => Encoding.tag 3 ++ target.bytes
  | .dup target => Encoding.tag 4 ++ target.bytes
  | .drop target => Encoding.tag 5 ++ target.bytes
  | .dropU target => Encoding.tag 6 ++ target.bytes
  | .fetch target field =>
      Encoding.tag 7 ++ target.bytes ++ Encoding.nat field
  | .call function args =>
      Encoding.tag 8 ++ Encoding.address function ++
        Encoding.array Atom.bytes args
  | .callSelf args => Encoding.tag 9 ++ Encoding.array Atom.bytes args
  | .papp function args =>
      Encoding.tag 10 ++ Encoding.address function ++
        Encoding.array Atom.bytes args
  | .apply function args =>
      Encoding.tag 11 ++ function.bytes ++ Encoding.array Atom.bytes args
  | .extern function args =>
      Encoding.tag 12 ++ Encoding.address function ++
        Encoding.array Atom.bytes args

end Op

mutual

/-- Canonical code payload. -/
def Code.bytes : Code → ByteArray
  | .ret atom => Encoding.tag 0 ++ atom.bytes
  | .letOp op rest => Encoding.tag 1 ++ op.bytes ++ rest.bytes
  | .case scrut peelNat alts =>
      Encoding.tag 2 ++ scrut.bytes ++ Encoding.bool peelNat ++
        Encoding.nat alts.size ++ AltList.bytes alts.toList

/-- Canonical case-alternative payload. -/
def Alt.bytes : Alt → ByteArray
  | .mk cidx fields body =>
      Encoding.nat cidx ++ Encoding.nat fields ++ body.bytes

/-- Executable order-preserving walk beneath an alternative array. -/
def AltList.bytes : List Alt → ByteArray
  | [] => ByteArray.empty
  | head :: tail => head.bytes ++ AltList.bytes tail

end

namespace FnDef

/-- Canonical saturated-function payload. -/
def bytes (fn : FnDef) : ByteArray :=
  Encoding.nat fn.arity ++ Encoding.tag fn.result.toBits ++
    Encoding.bool fn.papSafe ++ fn.body.bytes

end FnDef

namespace Decl

/-- The versioned domain prefix for IxIR₁ declaration identities. -/
def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/decl/2" ++ Encoding.tag 0

/-- Canonical declaration payload, without the address domain. -/
def payloadBytes : Decl → ByteArray
  | .fn definition => Encoding.tag 0 ++ definition.bytes
  | .extern arity => Encoding.tag 1 ++ Encoding.nat arity

/-- Complete canonical hash preimage for one IxIR₁ declaration. -/
def preimage (decl : Decl) : ByteArray :=
  addressDomain ++ payloadBytes decl

/-- BLAKE3 content address of an IxIR₁ declaration. -/
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

#guard Atom.bytes (.lit (.nat 128)) == ByteArray.mk #[1, 0, 128, 1]
#guard Code.bytes (.case .erased false #[.mk 0 0 (.ret .erased)]) ==
  ByteArray.mk #[2, 2, 0, 1, 0, 0, 0, 2]
#guard Decl.payloadBytes (.fn ⟨1, .shared, true, .ret (.var 0)⟩) ==
  ByteArray.mk #[0, 1, 1, 1, 0, 0, 0]
#guard Decl.payloadBytes (.extern 128) == ByteArray.mk #[1, 128, 1]

end Ix.Compiler.IxIR1
