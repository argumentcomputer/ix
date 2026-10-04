module

public import Ix.Resource.Addressed
public import Ix.Resource.Transport.Prepare
public import Ix.Tc.Driver

/-! The combined native validation boundary. Ownership admission, erased
typing, and source-contract transport consume the same addressed v4 bytes.
Kernel typechecking alone has no resource meaning. -/

@[expose] public section

namespace Ix.Resource

/-- A minimal built-in profile, restricted to actual interfaces present in
the supplied closure. All assumptions are explicit in its committed bytes.
Its shareable types (Nat, Bool, String) make usage contracts cross call and
closure boundaries on those types, so it relies on the named assumption that
the linearity of a shareable immediate has no run-time meaning
(docs/resource-checking.md); the strict profile source
(profiles/lean-core-strict.profile, `literals` in place of `standard`) has
no shareable type. -/
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
  for (selected, actual) in #[(profile.natType, primitives.nat), (profile.stringType, primitives.string),
      (profile.eqType, primitives.eq)] do
    if let some selected := selected then
      unless selected == actual do throw "resource validator: literal type differs from the kernel primitive identity"

/-- Rebuild the anonymous input from bounded raw byte windows. Lean's public
LazyConstant record permits constructing a conflicting materialized cache;
neither validator may trust that cache as a replacement for committed bytes. -/
def rawTypingEnv (env : Ixon.Env) : Ixon.Env := {
  consts := env.consts.fold (init := {}) fun result address lazy =>
    let bytes := lazy.rawBytes
    result.insert address (Ixon.LazyConstant.ofSlice bytes 0 bytes.size)
  blobs := env.blobs
  anonHints := env.anonHints }

def validate (env : Ixon.Env) (profile : Profile) : Except String AddressedProgram := do
  checkLiteralProfile profile
  let resolved ← Addressed.checkResources env profile
  let checked ← Ix.Tc.checkEnvAnon (rawTypingEnv env) { verifyHashes := true }
  for result in checked do
    if let some error := result.err? then
      throw s!"resource validator: erased typing failed at {result.addr}: {error}"
  Transport.checkAdmitted env resolved profile.limits
  return resolved

end Ix.Resource

end
