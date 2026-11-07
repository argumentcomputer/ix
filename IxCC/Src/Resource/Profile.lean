import IxCK.Ixon.Codec
import IxCC.Ixon.Address
import IxCC.Ixon.V3.Contracts

/-! Canonical resource-v1 profile framing, independent of either resource
checker. This module validates data, not the external assumptions it names. -/

namespace IxCC.Src.Resource

open IxCC.Ixon IxCC.Ixon.V3

structure Profile where
  assumptions : Array IxCC.Ixon.Address := #[]
  shareableTypes : Array IxCC.Ixon.Address := #[]
  choices : Array IxCC.Ixon.Address := #[]
  natType : Option IxCC.Ixon.Address := none
  stringType : Option IxCC.Ixon.Address := none
  depth : Nat := 256
  steps : Nat := 100000
  cases : Bool := false
  interfaces : Array (IxCC.Ixon.Address × ByteArray) := #[]
  eqType : Option IxCC.Ixon.Address := none
  equations : Array (IxCC.Ixon.Address × IxCC.Ixon.Address) := #[]
  caseDefinitions : Array IxCC.Ixon.Address := #[]
  crossing : Bool := false
  linearTypes : Array IxCC.Ixon.Address := #[]
  scalarTypes : Array IxCC.Ixon.Address := #[]
  deriving Inhabited

private def ordered (xs : List IxCC.Ixon.Address) : Bool :=
  (xs.zip xs.tail).all fun (a, b) => Id.run do
    for i in [:32] do
      if a.hash[i]! < b.hash[i]! then return true
      if b.hash[i]! < a.hash[i]! then return false
    return false

private abbrev DecodeM := _root_.Ixon.GetM

private def getAddress : DecodeM IxCC.Ixon.Address := do
  let some a := IxCC.Ixon.Address.ofBytes? (← _root_.Ixon.getBytes 32)
    | throw "resource profile: truncated address"
  return a

private def getNat : DecodeM Nat := return (← _root_.Ixon.getTagN 0).value.toNat

private def getBoundedCount (limit width : Nat) : DecodeM Nat := do
  let n ← getNat
  let s ← get
  unless n ≤ limit && n ≤ (s.bytes.size - s.idx) / width do
    throw "resource profile: count exceeds remaining bytes or budget"
  return n

private def getOptionalAddress : DecodeM (Option IxCC.Ixon.Address) := do
  match ← _root_.Ixon.getU8 with
  | 0 => return none
  | 1 => some <$> getAddress
  | _ => throw "resource profile: invalid optional address tag"

def Profile.validate (p : Profile) : Except String Unit := do
  for xs in [p.assumptions.toList, p.shareableTypes.toList, p.choices.toList,
      p.interfaces.toList.map (·.1), p.equations.toList.map (·.1),
      p.caseDefinitions.toList, p.linearTypes.toList, p.scalarTypes.toList] do
    unless ordered xs do throw "resource profile: addresses are not strictly ordered"
  unless p.depth > 0 && p.steps > 0 && p.depth < UInt64.size && p.steps < UInt64.size do
    throw "resource profile: invalid limits"
  for a in p.choices.toList do
    unless p.assumptions.toList.contains a do throw "resource profile: choice is not assumed"
  for (a, mask) in p.interfaces.toList do
    unless p.assumptions.toList.contains a && !mask.isEmpty do throw "resource profile: invalid interface"
    unless mask.data.toList.all (fun byte => (unpackAllContract? byte).isSome) do throw "resource profile: invalid interface mask"
  unless p.eqType.isSome == !p.equations.isEmpty do throw "resource profile: equality/equation mismatch"
  unless p.caseDefinitions.isEmpty || p.cases do throw "resource profile: case definitions without cases"

private def littleEndian : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, value => value.toUInt8 :: littleEndian n (value / 256)

/-- The flag-free TagN framing as lists. The rung offsets match the pinned
codec; this encoder avoids repeated ByteArray copies during kernel recheck. -/
private def tagN0 (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else if n < 16512 then [(128 + (n - 128) / 256).toUInt8, (n - 128).toUInt8]
  else if n < 82048 then 192 :: littleEndian 2 (n - 16512)
  else if n < 16859264 then 193 :: littleEndian 3 (n - 82048)
  else if n < 4311826560 then 194 :: littleEndian 4 (n - 16859264)
  else 195 :: littleEndian 8 (n - 4311826560)

/-- Canonical bytes for the recheck path, constructed and compared as lists.
`bytes` below remains the independent native codec writer. -/
def Profile.byteList (p : Profile) : List UInt8 := Id.run do
  let address := fun (a : IxCC.Ixon.Address) => a.hash.data.toList
  let addresses := fun (xs : Array IxCC.Ixon.Address) =>
    tagN0 xs.size ++ xs.toList.flatMap address
  let optional := fun (a : Option IxCC.Ixon.Address) =>
    match a with | none => [0] | some a => 1 :: address a
  let base := "ixon-v4/resource-v1/profile\x00".toUTF8.data.toList ++
    [p.assumptions, p.shareableTypes, p.choices].flatMap addresses ++
    [p.natType, p.stringType].flatMap optional ++ tagN0 p.depth ++ tagN0 p.steps
  let flags := (if p.cases then 1 else 0) + (if p.equations.isEmpty then 0 else 2) +
    (if p.caseDefinitions.isEmpty then 0 else 4) + (if p.crossing then 8 else 0) +
    (if p.linearTypes.isEmpty then 0 else 16) + (if p.scalarTypes.isEmpty then 0 else 32)
  if flags == 0 && p.interfaces.isEmpty then return base
  let interfaces := p.interfaces.toList.flatMap fun (a, mask) =>
    address a ++ tagN0 mask.size ++ mask.data.toList
  let equations := match p.eqType with
    | none => []
    | some eq => address eq ++ tagN0 p.equations.size ++
      p.equations.toList.flatMap (fun (f, t) => address f ++ address t)
  let tail := [p.caseDefinitions, p.linearTypes, p.scalarTypes].flatMap fun xs =>
    if xs.isEmpty then [] else addresses xs
  return base ++ tagN0 flags ++ tagN0 p.interfaces.size ++ interfaces ++ equations ++ tail

def Profile.bytes (p : Profile) : ByteArray :=
  "ixon-v4/resource-v1/profile\x00".toUTF8 ++ _root_.Ixon.runPut do
    for xs in #[p.assumptions, p.shareableTypes, p.choices] do
      _root_.Ixon.putTagN 0 0 xs.size.toUInt64
      for a in xs do _root_.Ixon.putBytes a.hash
    for a in #[p.natType, p.stringType] do
      match a with
      | none => _root_.Ixon.putU8 0
      | some a => _root_.Ixon.putU8 1; _root_.Ixon.putBytes a.hash
    _root_.Ixon.putTagN 0 0 p.depth.toUInt64
    _root_.Ixon.putTagN 0 0 p.steps.toUInt64
    let flags : UInt64 := (if p.cases then 1 else 0) ||| (if p.equations.isEmpty then 0 else 2) |||
      (if p.caseDefinitions.isEmpty then 0 else 4) ||| (if p.crossing then 8 else 0) |||
      (if p.linearTypes.isEmpty then 0 else 16) ||| (if p.scalarTypes.isEmpty then 0 else 32)
    if flags != 0 || !p.interfaces.isEmpty then
      _root_.Ixon.putTagN 0 0 flags
      _root_.Ixon.putTagN 0 0 p.interfaces.size.toUInt64
      for (a, mask) in p.interfaces do
        _root_.Ixon.putBytes a.hash
        _root_.Ixon.putTagN 0 0 mask.size.toUInt64
        _root_.Ixon.putBytes mask
      if let some eq := p.eqType then
        _root_.Ixon.putBytes eq.hash
        _root_.Ixon.putTagN 0 0 p.equations.size.toUInt64
        for (f, t) in p.equations do
          _root_.Ixon.putBytes f.hash
          _root_.Ixon.putBytes t.hash
      for xs in #[p.caseDefinitions, p.linearTypes, p.scalarTypes] do
        unless xs.isEmpty do
          _root_.Ixon.putTagN 0 0 xs.size.toUInt64
          for a in xs do _root_.Ixon.putBytes a.hash

private def addresses : DecodeM (Array IxCC.Ixon.Address) := do
  let n ← getBoundedCount 32768 32
  let mut xs := #[]
  for _ in [:n] do xs := xs.push (← getAddress)
  return xs

private def readProfile : DecodeM Profile := do
  let header := "ixon-v4/resource-v1/profile\x00".toUTF8
  unless (← _root_.Ixon.getBytes header.size) == header do throw "resource profile: invalid header"
  let assumptions ← addresses
  let shareableTypes ← addresses
  let choices ← addresses
  let natType ← getOptionalAddress
  let stringType ← getOptionalAddress
  let depth ← getNat
  let steps ← getNat
  let mut p : Profile := { assumptions, shareableTypes, choices, natType, stringType, depth, steps }
  let s ← get
  if s.idx == s.bytes.size then return p
  let flags := (← _root_.Ixon.getTagN 0).value
  unless flags ≤ 63 do throw "resource profile: unknown flags"
  let n ← getBoundedCount 32768 33
  let mut interfaces := #[]
  for _ in [:n] do
    let a ← getAddress
    let n ← getBoundedCount (1024 * 1024) 1
    interfaces := interfaces.push (a, ← _root_.Ixon.getBytes n)
  unless flags != 0 || !interfaces.isEmpty do throw "resource profile: empty extension"
  p := { p with interfaces, cases := flags &&& 1 != 0, crossing := flags &&& 8 != 0 }
  if flags &&& 2 != 0 then
    let eq ← getAddress
    let n ← getBoundedCount 16384 64
    unless n > 0 do throw "resource profile: empty equations"
    let mut equations := #[]
    for _ in [:n] do equations := equations.push (← getAddress, ← getAddress)
    p := { p with eqType := some eq, equations }
  if flags &&& 4 != 0 then
    let xs ← addresses
    unless !xs.isEmpty do throw "resource profile: empty case definitions"
    p := { p with caseDefinitions := xs }
  if flags &&& 16 != 0 then
    let xs ← addresses
    unless !xs.isEmpty do throw "resource profile: empty linear types"
    p := { p with linearTypes := xs }
  if flags &&& 32 != 0 then
    let xs ← addresses
    unless !xs.isEmpty do throw "resource profile: empty scalar types"
    p := { p with scalarTypes := xs }
  return p

def Profile.ofBytes (bytes : ByteArray) : Except String Profile := do
  unless bytes.size ≤ 1024 * 1024 do throw "resource profile: byte budget exceeded"
  let p ← _root_.Ixon.runGetExact readProfile bytes
  p.validate
  unless p.byteList == bytes.data.toList do throw "resource profile: noncanonical encoding"
  return p

end IxCC.Src.Resource
