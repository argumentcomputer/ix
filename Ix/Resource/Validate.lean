module

public import Ix.Resource.Addressed
public import Ix.Resource.Typing
public import Ix.PrimAddrs

/-! The combined native validation boundary. Both validators consume the same
addressed constant bytes and bound artifacts use their admitted identities.
Kernel typechecking alone has no resource meaning.

The typing half is `Ix.Resource.typeCheck` (`Ix.Resource.Typing`): IxC's
tiered Ixon entry, with its theorem, over everything it admits, and beside it,
uncertified, IxC's typing of the unsafe inductives and assumption axioms it
declines by design and of the records that depend on them. The claim string
stays `resource-v1`: re-based on IxC, still uncertified as a resource claim
(`Ix.Resource.Claim`). -/

@[expose] public section

namespace Ix.Resource

/-- Bound artifacts supply literal identities through their authenticated
table. The legacy unbound route retains its explicit primitive table. -/
def literalIdentities (env : Ixon.Env) : Except String (Option Address × Option Address × Option Address) := do
  if let some raw := env.roleBinding then
    let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash
      ⟨raw.address, raw.bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e)
    return (table.addressOf? .nat, table.addressOf? .bool, table.addressOf? .string)
  let primitives := Ix.Tc.PrimAddrs.canonical
  return (some primitives.nat, some primitives.boolType, some primitives.string)

/-- A minimal profile restricted to actual interfaces present in the closure.
A malformed binding proposes no literal identities; validation reports the
binding error before using this profile. No default identity replaces it. -/
def standardProfile (env : Ixon.Env) : Profile :=
  let (natType, boolType, stringType) := (literalIdentities env).toOption.getD (none, none, none)
  let present := fun address => address.filter env.consts.contains
  { natType := present natType
    stringType := present stringType
    shareableTypes := (#[natType, boolType, stringType].filterMap present).qsort
      (fun a b => Address.cmpBytes a b == .lt) }

/-- Literal interpretation is fixed by the typechecker, not chosen by the
profile. A profile may omit unused literal types, but cannot redirect them. -/
def checkLiteralProfile (env : Ixon.Env) (profile : Profile) : Except String Unit := do
  let (natType, _, stringType) ← literalIdentities env
  for (selected, actual) in #[(profile.natType, natType), (profile.stringType, stringType)] do
    if let some selected := selected then
      unless some selected == actual do throw "resource validator: literal type differs from the kernel primitive identity"

def validate (env : Ixon.Env) (profile : Profile) : Except String AddressedProgram := do
  checkLiteralProfile env profile
  let resolved ← Addressed.checkResources env profile
  typeCheck env
  return resolved

end Ix.Resource

end
