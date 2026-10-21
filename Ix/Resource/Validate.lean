module

public import Ix.Resource.Addressed
public import Ix.Resource.Typing
public import Ix.PrimAddrs

/-! The combined native validation boundary. Both validators consume the same
addressed v4 bytes. Kernel typechecking alone has no resource meaning.

The typing half is `Ix.Resource.typeCheck` (`Ix.Resource.Typing`): IxC's
tiered Ixon entry, with its theorem, over everything it admits, and beside it,
uncertified, IxC's typing of the unsafe inductives and assumption axioms it
declines by design and of the records that depend on them. The claim string
stays `resource-v1`: re-based on IxC, still uncertified as a resource claim
(`Ix.Resource.Claim`). -/

@[expose] public section

namespace Ix.Resource

/-- A minimal built-in profile, restricted to actual interfaces present in
the supplied closure. All assumptions are explicit in its committed bytes. -/
def standardProfile (env : Ixon.Env) : Profile :=
  let primitives := Ix.Tc.PrimAddrs.canonical
  let present := fun address => if env.consts.contains address then some address else none
  { natType := present primitives.nat
    stringType := present primitives.string
    shareableTypes := (#[primitives.nat, primitives.boolType, primitives.string].filter
      env.consts.contains).qsort (fun a b => Address.cmpBytes a b == .lt) }

/-- Literal interpretation is fixed by the typechecker, not chosen by the
profile. A profile may omit unused literal types, but cannot redirect them. -/
def checkLiteralProfile (profile : Profile) : Except String Unit := do
  let primitives := Ix.Tc.PrimAddrs.canonical
  for (selected, actual) in #[(profile.natType, primitives.nat), (profile.stringType, primitives.string)] do
    if let some selected := selected then
      unless selected == actual do throw "resource validator: literal type differs from the kernel primitive identity"

def validate (env : Ixon.Env) (profile : Profile) : Except String AddressedProgram := do
  checkLiteralProfile profile
  let resolved ← Addressed.checkResources env profile
  typeCheck env
  return resolved

end Ix.Resource

end
