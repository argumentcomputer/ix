import Ix.Compiler.Ixon.Hash

/-!
# Canonical ix Merkle roots

This is the small canonical-set Merkle construction used by ix environment
and catalog roots.  Leaves are sorted lexicographically and deduplicated,
then domain-separated as `BLAKE3(0x00 || address)`.  Internal nodes are
`BLAKE3(0x01 || left || right)`; an odd node is paired with the fixed
32-byte zero sentinel rather than duplicated.
-/

namespace Ix.Compiler.Ixon.Merkle

def leafDomain : UInt8 := 0x00
def nodeDomain : UInt8 := 0x01

/-- The empty-set root and odd-level padding value used by ix. -/
def zeroAddress : Address := Address.replicate 0

/-- Allocation-free lexicographic comparison of the 32 address bytes. -/
def compareAddress (left right : Address) : Ordering := Id.run do
  for index in [:32] do
    let leftByte := left.hash[index]!
    let rightByte := right.hash[index]!
    if leftByte < rightByte then return .lt
    if rightByte < leftByte then return .gt
  return .eq

def addressLT (left right : Address) : Bool :=
  compareAddress left right == .lt

def sortAddresses (addresses : Array Address) : Array Address :=
  addresses.qsort addressLT

/-- Collapse adjacent equal entries in an already sorted address array. -/
def dedupSorted (addresses : Array Address) : Array Address := Id.run do
  let mut result := #[]
  for address in addresses do
    match result.back? with
    | some previous =>
      if previous != address then
        result := result.push address
    | none => result := result.push address
  return result

def leafHash (address : Address) : Address :=
  Address.blake3 (ByteArray.mk #[leafDomain] ++ address.hash)

def nodeHash (left right : Address) : Address :=
  Address.blake3
    (ByteArray.mk #[nodeDomain] ++ left.hash ++ right.hash)

private def reduceLevel (level : Array Address) : Array Address := Id.run do
  let mut next := #[]
  let mut index := 0
  while index < level.size do
    let left := level[index]!
    let right := if index + 1 < level.size then
      level[index + 1]!
    else
      zeroAddress
    next := next.push (nodeHash left right)
    index := index + 2
  return next

private def buildTree (initial : Array Address) : Address := Id.run do
  let mut level := initial
  while level.size > 1 do
    level := reduceLevel level
  return level[0]!

/-- Canonical root over a set of addresses.  The empty set uses ix's fixed
zero sentinel; all nonempty leaves are hashed before tree construction. -/
def rootCanonical (addresses : Array Address) : Address :=
  let unique := dedupSorted (sortAddresses addresses)
  if unique.isEmpty then
    zeroAddress
  else if unique.size == 1 then
    leafHash unique[0]!
  else
    buildTree (unique.map leafHash)

end Ix.Compiler.Ixon.Merkle
