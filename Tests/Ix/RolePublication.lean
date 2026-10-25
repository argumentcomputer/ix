module

public import Ix.RoleBinding.Publication
public import Ix.Address.Admission
public import LSpec

namespace Tests.Ix.RolePublication

open Ixon
open Ix.RoleBinding
open Ix.Kernel (RoleTable)

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

/-- These are publication controls, before specification/evidence admission.
The supplied definition intentionally does not assert any role's semantics. -/
private def checks (record : Constant) : Except String Unit := do
  let address := Address.admissionHash (serConstant record)
  let store := fun a => if a == address then some record else none
  let natName := Ix.Name.fromLeanName `Nat
  let boolName := Ix.Name.fromLeanName `Bool
  let nat : Named := { addr := address }
  let env : Env := { named := ({} : Std.HashMap Ix.Name Named).insert natName nat }
  let result ← publication env store [.nat]
  need "actual publication address and resolved member"
    (result.bound == #[(.nat, address)] &&
      result.refs.get? Ix.Kernel.Role.nat == some (Ix.Kernel.ConstRef.member address 0))
  need "explicit empty role request" (← publication env store []).bound.isEmpty
  need "required missing role fails" (!(publication env store [.bool]).isOk)
  need "duplicate required role fails" (!(publication env store [.nat, .nat]).isOk)
  need "published record must exist" (!(publication env (fun _ => none) [.nat]).isOk)
  let aliases := { env with named := env.named.insert (Ix.Name.fromLeanName `Alias.Nat) nat }
  need "non-role alias keeps the real source publication"
    ((← publication aliases store [.nat]).bound == result.bound)
  let collidingRoles := { env with named := env.named.insert boolName nat }
  need "two roles cannot share one resolved member"
    (!(publication collidingRoles store [.nat, .bool]).isOk)

  let forgedName := Ix.Name.str .mkAnon "Unrelated" natName.getHash
  let forged : Env := { named := ({} : Std.HashMap Ix.Name Named).insert forgedName nat }
  need "a stored name hash cannot impersonate a structural role"
    (!(publication forged store [.nat]).isOk)
  let duplicateName := Ix.Name.str .mkAnon "Nat" boolName.getHash
  let duplicate := { env with named := env.named.insert duplicateName nat }
  need "duplicate structural role names with distinct stored hashes fail"
    (!(publication duplicate store [.nat]).isOk)
  let dotted : Env := {
    named := ({} : Std.HashMap Ix.Name Named).insert (Ix.Name.mkStr .mkAnon "Nat.zero") nat
  }
  need "display text is not structural source identity"
    (!(publication dotted store [.natZero]).isOk)

  let other := { record with univs := record.univs.push (.succ .zero) }
  let otherAddress := Address.admissionHash (serConstant other)
  let bothStore := fun a => if a == otherAddress then some other else store a
  let both := { env with named := env.named.insert boolName { addr := otherAddress } }
  need "canonical role order is independent of request order"
    ((← publication both bothStore [.bool, .nat]).bound == #[(.nat, address), (.bool, otherAddress)])

  let .defn definition := record.info | throw "fixture must be a definition"
  let block := { record with info := .muts #[.defn definition] }
  let blockAddress := Address.admissionHash (serConstant block)
  let projection : Constant := {
    sharing := #[], refs := #[], univs := #[], info := .dPrj { block := blockAddress, idx := 0 }
  }
  let projectionAddress := Address.admissionHash (serConstant projection)
  let projectionStore := fun a =>
    if a == projectionAddress then some projection else if a == blockAddress then some block else none
  let projected : Env := { named := ({} : Std.HashMap Ix.Name Named).insert natName { addr := projectionAddress } }
  let resolved ← publication projected projectionStore [.nat]
  need "published projection address is retained"
    (resolved.bound == #[(.nat, projectionAddress)] &&
      resolved.refs.get? Ix.Kernel.Role.nat == some (Ix.Kernel.ConstRef.member blockAddress 0))
  let table : RoleTable := { version := Ix.Kernel.specVersion, bound := resolved.bound, evidence := #[] }
  need "prelude owner precedes projection and repeated groups deduplicate"
    ((← preludeRecords table projectionStore [[.nat], [.nat]]).map (·.1) == #[blockAddress, projectionAddress])
  need "missing prelude role cannot use a default address"
    (!(preludeRecords table projectionStore [[.bool]]).isOk)
  need "missing owner fails before publication"
    (!(publication projected (fun a => if a == projectionAddress then some projection else none) [.nat]).isOk)

public def units (record : Constant) : LSpec.TestSeq :=
  .individualIO "role publication: structural names, aliases, explicit absence and actual prelude owners" none (do
    let result ← IO.lazyPure fun _ => checks record
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

end Tests.Ix.RolePublication
