import IxCC.Ixon.V3.Catalog.Basic

namespace IxCC.Ixon.V3.Catalog

def constantAddresses (env : Env) : Array Address :=
  Merkle.sortAddresses env.consts.keys.toArray

/-- Authenticate the full original membership of overlapping members. A chunk
contains only its first owner's slice, which cannot reconstruct that member. -/
def checkMemberSets (limits : Limits) (m : Manifest) (env : Env)
    (sets : MemberSets) : Except Error (Std.HashMap Address Nat × Nat) := do
  unless sets.size == m.members.size do throw (.coverage "member-set count differs")
  let mut owners : Std.HashMap Address Nat := {}
  let mut entries := 0
  for i in [:sets.size] do
    let addresses := sets[i]!
    entries := entries + addresses.size
    requireLimit "member entries" entries limits.memberEntries
    unless addresses.size == m.members[i]!.constCount.toNat do
      throw (.coverage s!"member {i}: constant count differs")
    let mut previous := none
    for address in addresses do
      if let some before := previous then
        unless Merkle.addressLT before address do
          throw (.coverage s!"member {i}: addresses are not strictly increasing")
      previous := some address
      unless env.consts.contains address do
        throw (.coverage s!"member {i}: constant absent from union")
      if !owners.contains address then owners := owners.insert address i
    unless Merkle.rootCanonical addresses == m.members[i]!.envRoot do
      throw (.coverage s!"member {i}: address list does not match committed root")
  unless owners.size == env.consts.size do
    throw (.coverage "member sets do not cover the union")
  return (owners, entries)

def checkCoverage (limits : Limits) (m : Manifest) (pieces : Array Env)
    (env : Env) (supplied : Option MemberSets) : Except Error (MemberSets × Nat) := do
  let sets ← match m.storage with
    | .fat _ =>
      if supplied.isSome then throw (.coverage "fat members derive their own address sets")
      else pure (pieces.map constantAddresses)
    | .chunked _ => match supplied with
      | some sets => pure sets
      | none => throw (.coverage "chunked catalogs require complete member address lists")
  let (owners, entries) ← checkMemberSets limits m env sets
  if let .chunked rows := m.storage then
    for i in [:pieces.size] do
      for address in constantAddresses pieces[i]! do
        unless owners[address]? == some rows[i]!.owner.toNat do
          throw (.coverage s!"chunk {i}: constant is not assigned to its first owner")
  return (sets, entries)

end IxCC.Ixon.V3.Catalog
