import IxCK.Kernel.Key
import IxCC.Ixon.Address

/-! # The role binding of a role-bound environment

A role-bound environment (`.ixe` envelope version 5, header byte `0xE5`;
`IxCC/docs/byte-contract.md`) carries, after its assumptions, the role table
that binds the certified kernel's roles (`Ix.Kernel.Role`,
`IxCK/Kernel/Key.lean`) to constants of the environment: a 32-byte address, a
TagN(0) length and that many bytes, the table's *binding section*, whose pure
BLAKE3 hash is the address. That address is the binding hash a typing claim
about the environment names, and the section is what the kernel's admission
decodes (`Ix.Kernel.RoleTable.ofBytes`, `IxCK/Kernel/Ixon/RoleTable.lean`)
and checks against its specifications.

This module reads the section as the kernel's decoder does. All integers are
single bytes:

| bytes | field |
| --- | --- |
| `E8 03` | the section's tag |
| `v` | the specification version the table was made for |
| `n` | the number of bound roles |
| `n × (r, a)` | a role's index and the 32-byte address bound to it, indices strictly increasing |
| `m` | the number of evidence entries |
| `m × (r, k, e₁ … e_k)` | a role's index, its evidence count and its evidence, indices strictly increasing |
| `e` | `00` for definitional evidence, `01` and a 32-byte address for a proof |

A role's index is its position in the kernel's `Ix.Kernel.Role.all`, which
this module imports rather than copies, so the roles IxCC reads are the
kernel's of the same build. The decoder accepts exactly what the kernel's
`RoleTable.ofBytes` accepts (the same grammar, strictly increasing indices, no
trailing byte) and reads the same table; the tests check it against tables
`ix` wrote.

IxCC does not check the table against the specifications (its version, its
closure under blocks and dependencies, its evidence): that is the kernel's
admission, which every grounded statement takes as a premise. It does refuse
a table that binds one address to two roles, since pins read from such a table
would name one constant twice. The decoder recurses on the counts it reads,
each a byte, so its depth is at most 255. -/

namespace IxCC.Ixon.V3

open IxCC.Ixon

/-- The kernel's roles. -/
abbrev Role := Ix.Kernel.Role

/-- The role at a binding-section index: position `i` of `Ix.Kernel.Role.all`. -/
def roleOfIdx? (i : Nat) : Option Role := Ix.Kernel.Role.all[i]?

/-- A role's binding-section index. -/
def roleIdx (r : Role) : Nat := Ix.Kernel.Role.all.idxOf r

/-- One piece of evidence for an equation of a role's specification:
definitional, or the address of a theorem that proves it. -/
inductive RoleEvidence where
  | defeq
  | proof (thm : Address)
  deriving BEq, Repr, Inhabited

/-- A decoded binding section: the specification version it names, the bound
roles with their addresses, and the evidence entries, each in strictly
increasing role order. -/
structure RoleTable where
  version : Nat
  bound : List (Role × Address)
  evidence : List (Role × List RoleEvidence)
  deriving Repr, Inhabited

namespace RoleTable

/-- The 32 bytes of an address, and the rest. -/
def decAddr (bs : List UInt8) : Option (Address × List UInt8) := do
  let a ← Address.ofBytes? ⟨(bs.take 32).toArray⟩
  pure (a, bs.drop 32)

/-- `n` bound roles. -/
def decBound : Nat → List UInt8 → Option (List (Role × Address) × List UInt8)
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: bs => do
    let r ← roleOfIdx? b.toNat
    let (a, bs) ← decAddr bs
    let (rest, bs) ← decBound n bs
    pure ((r, a) :: rest, bs)

/-- One piece of evidence. -/
def decEvidence : List UInt8 → Option (RoleEvidence × List UInt8)
  | 0 :: bs => some (.defeq, bs)
  | 1 :: bs => do
    let (a, bs) ← decAddr bs
    pure (.proof a, bs)
  | _ => none

/-- `n` pieces of evidence. -/
def decEvidences : Nat → List UInt8 → Option (List RoleEvidence × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (e, bs) ← decEvidence bs
    let (rest, bs) ← decEvidences n bs
    pure (e :: rest, bs)

/-- `n` evidence entries. -/
def decEntries : Nat → List UInt8 → Option (List (Role × List RoleEvidence) × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, b :: k :: bs => do
    let r ← roleOfIdx? b.toNat
    let (es, bs) ← decEvidences k.toNat bs
    let (rest, bs) ← decEntries n bs
    pure ((r, es) :: rest, bs)
  | _ + 1, _ => none

/-- Role indices strictly increasing. -/
def ascending : List Role → Bool
  | a :: b :: rest => decide (roleIdx a < roleIdx b) && ascending (b :: rest)
  | _ => true

/-- Decode a binding section, exactly: the whole input. -/
def decode : List UInt8 → Option RoleTable
  | 0xE8 :: 0x03 :: v :: n :: bs =>
    match decBound n.toNat bs with
    | some (bound, m :: bs) =>
      match decEntries m.toNat bs with
      | some (evidence, []) =>
        if ascending (bound.map (·.1)) && ascending (evidence.map (·.1)) then
          some { version := v.toNat, bound, evidence }
        else none
      | _ => none
    | _ => none
  | _ => none

/-- The address bound twice, if any (the bound list is at most 255 long). -/
def repeatedAddress : List (Role × Address) → Option Address
  | [] => none
  | (_, a) :: rest => if rest.any (·.2 == a) then some a else repeatedAddress rest

/-- The address bound to a role, if the table binds it. -/
def addressOf? (t : RoleTable) (r : Role) : Option Address :=
  (t.bound.find? (·.1 == r)).map (·.2)

/-- The most bytes a binding section can have: 255 bound roles and 255
evidence entries of 255 proofs each. -/
def maxBytes : Nat := 4 + 255 * 33 + 1 + 255 * (2 + 255 * 33)

end RoleTable

/-- A role binding as the envelope carries it: the binding section's address
and bytes, and the table they decode to. -/
structure Binding where
  /-- The binding hash: the pure BLAKE3 hash of `bytes`. -/
  address : Address
  /-- The binding section. -/
  bytes : ByteArray
  /-- The section, decoded. -/
  table : RoleTable
  deriving Inhabited

/-- Decode a binding section whose address the caller has authenticated, and
refuse one that binds an address twice. -/
def Binding.ofSection (address : Address) (bytes : ByteArray) : Except String Binding := do
  if bytes.size > RoleTable.maxBytes then
    throw "role binding: the section exceeds the format's size"
  let some table := RoleTable.decode bytes.data.toList
    | throw "role binding: not a canonical binding section"
  if let some a := RoleTable.repeatedAddress table.bound then
    throw s!"role binding: address {a} is bound to two roles"
  return { address, bytes, table }

end IxCC.Ixon.V3
