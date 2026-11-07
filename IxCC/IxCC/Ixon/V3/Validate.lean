import IxCC.Ixon.V3.Source
import IxCC.Ixon.V3.Tc.Driver

/-! Combined native admission: both resource and erased typing checks consume
the same decoded, hash-checked v3 bytes. The record certifies execution of
these algorithms; it is not a whole-checker semantic soundness theorem. -/

namespace IxCC.Ixon.V3

def literalPinAllowed (selected : Option Address) (actual : Address) : Bool :=
  match selected with
  | none => true
  | some selected => selected == actual

/-- Literal interpretation belongs to the pinned kernel primitive inventory.
A profile may omit unused literal types, but cannot select different ones. -/
def checkLiteralProfile (profile : Resource.Profile) : Except String Unit :=
  if literalPinAllowed profile.natType Tc.PrimAddrs.canonical.nat &&
      literalPinAllowed profile.stringType Tc.PrimAddrs.canonical.string then .ok ()
  else .error "ixon-v3: literal type differs from the kernel primitive identity"

theorem literalPinAllowed_sound {selected : Option Address} {actual : Address}
    (h : literalPinAllowed selected actual = true) :
    selected = none ∨ selected = some actual := by
  cases selected with
  | none => exact Or.inl rfl
  | some selected => exact Or.inr (congrArg some (Address.eq_of_beq h))

theorem checkLiteralProfile_sound {profile : Resource.Profile}
    (h : checkLiteralProfile profile = .ok ()) :
    (profile.natType = none ∨ profile.natType = some Tc.PrimAddrs.canonical.nat) ∧
    (profile.stringType = none ∨ profile.stringType = some Tc.PrimAddrs.canonical.string) := by
  unfold checkLiteralProfile at h
  split at h
  next accepted =>
    have both := Bool.and_eq_true_iff.mp accepted
    exact ⟨literalPinAllowed_sound both.1, literalPinAllowed_sound both.2⟩
  next => contradiction

/-- The upstream minimal profile, restricted to primitives actually present
in the addressed closure. Assumptions still require explicit selection. -/
def standardProfile (env : Env) : Resource.Profile :=
  let primitives := Tc.PrimAddrs.canonical
  let present := fun address => if env.consts.contains address then some address else none
  { natType := present primitives.nat
    stringType := present primitives.string
    shareableTypes := (#[primitives.nat, primitives.boolType, primitives.string].filter
      env.consts.contains).qsort (fun a b => a.cmpBytes b == .lt) }

structure ValidatedInput (bytes profileBytes : ByteArray) where
  resource : ResourceInput bytes profileBytes
  literalProfileChecked : checkLiteralProfile resource.profile = .ok ()
  typingChecked : Tc.checkEnv resource.env = .ok ()

/-- Combined validation over exactly the bytes retained by resource ingress.
No materialized environment or caller-supplied typing verdict is accepted. -/
def validate (bytes profileBytes : ByteArray) :
    Except String (ValidatedInput bytes profileBytes) := do
  let resource ← admitResources bytes profileBytes
  match literalProfileChecked : checkLiteralProfile resource.profile with
  | .error error => throw error
  | .ok () =>
    match typingChecked : Tc.checkEnv resource.env with
    | .error error => throw error
    | .ok () => return { resource, literalProfileChecked, typingChecked }

/-- Check the native Resource claim against a successfully validated source.
IxVM resource proof variants remain unsupported. -/
def ValidatedInput.checkClaim {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) (claimBytes : ByteArray) : Except String Unit :=
  input.resource.checkClaimBinding claimBytes

theorem ValidatedInput.typing_checked {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) : Tc.checkEnv input.resource.env = .ok () :=
  input.typingChecked

theorem ValidatedInput.literal_profile_checked {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) : checkLiteralProfile input.resource.profile = .ok () :=
  input.literalProfileChecked

theorem ValidatedInput.resources_checked {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) :
    Resource.Addressed.checkResources input.resource.env input.resource.profile =
      .ok input.resource.resolved :=
  input.resource.admitted

theorem ValidatedInput.source_decoded {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) :
    decodeAnonymousEnv bytes = .ok input.resource.env :=
  input.resource.decoded

theorem ValidatedInput.profile_decoded {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) :
    Resource.Profile.ofBytes profileBytes = .ok input.resource.profile :=
  input.resource.profileDecoded

theorem ValidatedInput.literal_types {bytes profileBytes : ByteArray}
    (input : ValidatedInput bytes profileBytes) :
    (input.resource.profile.natType = none ∨
      input.resource.profile.natType = some Tc.PrimAddrs.canonical.nat) ∧
    (input.resource.profile.stringType = none ∨
      input.resource.profile.stringType = some Tc.PrimAddrs.canonical.string) :=
  checkLiteralProfile_sound input.literalProfileChecked

end IxCC.Ixon.V3
