module

public import Ix.Ixon
public import Ix.LeanIngress.Expr
public import IxC.Kernel.Ixon.RoleTable
public import IxC.Kernel.Ixon.Reader

/-! # Role addresses from an artifact's published names

This is the publication step shared with the role-table generator. Source
spellings are compared structurally, independently of Ix.Name's stored hash.
The caller explicitly supplies the required roles. A missing role is an error;
there is no substitution from the driver's resolution map or a default table.

The result contains addresses and their actual resolved members. It does not
assert that the declarations meet the role specifications or that their proof
evidence is present. Those checks belong to binding admission and the fold.
-/

@[expose] public section

namespace Ix.RoleBinding

open Ix.Kernel (Role ConstRef RoleTable)
open Ix.Kernel.Reader (Store resolveSource)

structure Publication where
  bound : Array (Role × Address)
  refs : Std.HashMap Role (ConstRef Address)

/-- Resolve exactly the requested roles from published structural names,
returning roles in the canonical Role.all order. Two roles may not designate
the same member, even through different projection records. -/
def publication (env : Ixon.Env) (store : Store) (required : List Role) :
    Except String Publication := do
  unless required.Nodup do throw "role publication: a required role occurs twice"
  let mut published : Std.HashMap Role Address := {}
  for (name, named) in env.named.toList do
    let some role := Role.ofLeanName? (Ix.LeanIngress.ingressName name) | continue
    unless required.contains role do continue
    if published.contains role then
      throw s!"role publication: multiple published spellings of {repr role}"
    published := published.insert role named.addr
  let mut bound : Array (Role × Address) := #[]
  let mut refs : Std.HashMap Role (ConstRef Address) := {}
  let mut roleOfRef : Std.HashMap (ConstRef Address) Role := {}
  for role in Role.all do
    unless required.contains role do continue
    let some address := published[role]?
      | throw s!"role publication: no published constant for {repr role}"
    let some record := store address
      | throw s!"role publication: {repr role} has no record at {address}"
    let some ref := resolveSource store address record
      | throw s!"role publication: {repr role} at {address} does not resolve"
    if let some other := roleOfRef[ref]? then
      throw s!"role publication: {repr role} and {repr other} resolve to the same member"
    roleOfRef := roleOfRef.insert ref role
    refs := refs.insert role ref
    bound := bound.push (role, address)
  return { bound, refs }

/-- Actual prelude records selected by role groups, with each owner before its
projection. Every requested role and record must be present. The groups supply
the prelude order; this function does not claim that the order or shape admits. -/
def preludeRecords (table : RoleTable) (store : Store) (groups : List (List Role)) :
    Except String (Array (Address × Ixon.Constant)) := do
  let mut addresses : Array Address := #[]
  let mut records : Array (Address × Ixon.Constant) := #[]
  for group in groups do
    for role in group do
      let some address := table.addressOf? role
        | throw s!"role prelude: no binding for {repr role}"
      let some record := store address
        | throw s!"role prelude: no record for {repr role} at {address}"
      let some ref := resolveSource store address record
        | throw s!"role prelude: {repr role} at {address} does not resolve"
      for selected in #[ref.block, address] do
        unless addresses.contains selected do
          let some value := store selected
            | throw s!"role prelude: missing owner {selected} for {repr role}"
          addresses := addresses.push selected
          records := records.push (selected, value)
  return records

end Ix.RoleBinding
