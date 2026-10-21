module

public import Ix.Resource.Addressed
public import Ix.PrimAddrs
public import Ix.Address.Admission
public import Ix.Ixon.CheckOrder
public import IxC.Kernel.Admission.Tier

/-! The combined native validation boundary. Both validators consume the same
addressed v4 bytes. Kernel typechecking alone has no resource meaning.

**The typing half** (`typeCheck`) is IxC's tiered Ixon entry at BLAKE3,
`Ix.Kernel.Admission.checkBytesTiered Address.admissionHash` (the logical
check, then the typing tier), over every record of the environment as
committed: its exact bytes (never a materialized cache), in an executable
whole-environment check order (`Ixon.CheckOrder.wholeEnv`), with every blob,
the compiler's reducibility hints and the default role table. An accept is
what `Ix.Kernel.Admission.checkBytesTiered_ok` states: every record and blob
authenticated, the logical environment model-backed, and the tier's `partial`
and `unsafe` definitions, unsafe opaques and unsafe axioms typed with every
tier constant opaque. The order and the hints are untrusted: a wrong one is a
decline, never an accept.

**Unsafe inductives decline** (the recorded divergence Q2 from `Ix.Tc`, which
accepted them): the tiered entry keeps their records on the logical side,
where the reader declines them. So do **assumption axioms** (a safe axiom
other than the role table's standard ones): the certified theory is Lean's
with its three standard axioms. Until step 10d types both uncertified beside
the batch tier, an environment holding one does not validate.

The claim string stays `resource-v1`: re-based on IxC, still uncertified as a
resource claim (`Ix.Resource.Claim`). -/

@[expose] public section

namespace Ix.Resource

open Ix.Kernel (ConstRef)

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

/-- Bounds wide enough for a whole compiled library (as `kernel-check-ixe
--entry` sets them). They are coverage bounds: an input past one declines. -/
def typingLimits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- A shipped reducibility hint as the kernel's (`Ix.Cert.hintOf`, copied). -/
def hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- What the typing half submits: the records' committed bytes in check
order, every blob, and the hints with the projection map they are read
through. -/
structure TypingInput where
  records : Ix.Kernel.Admission.Records
  blobs : Ix.Kernel.Ingress.Blobs
  /-- each definition block member's projection record -/
  projections : Std.HashMap (ConstRef Address) Address
  hints : Std.HashMap Address Lean.ReducibilityHints

/-- **The compiler's reducibility hints**, read as `Ix.Cert.hintsOf` reads
them (copied, so that `Ix.Resource` does not import `Ix.Cert`; the test
`resource-hints` checks that the two agree): the hint the artifact ships at
a definition block member's projection record, otherwise at the record. The
projection map is built once, with the input: a lookup returned as a closure
from a function of the environment would be compiled at its full arity and
rebuild the map at every call. -/
def TypingInput.hint (input : TypingInput) (r : ConstRef Address) : Option Ix.Kernel.ReducibilityHint :=
  hintOf <$> input.hints.get? ((input.projections.get? r).getD r.block)

/-- The typing half's input. Every record is decoded from its committed
bytes (`lazy.rawBytes`: Lean's public `LazyConstant` record permits a
conflicting materialized cache, which neither validator may trust in place of
the committed bytes) by the entry's own canonical decoder, for the order and
the projection map only; the entry decodes the same bytes again itself. -/
def typingInput (env : Ixon.Env) : Except String TypingInput := do
  let table ← Ix.Kernel.Reader.defaultTable
  let pre : Ix.Kernel.Reader.Prelude .anon ← Ix.Kernel.Reader.preludeFor table
  let committed : Array (Address × ByteArray) :=
    (env.consts.toArray.map fun (a, lazy) => (a, lazy.rawBytes)).qsort fun x y => x.1.cmpBytes y.1 == .lt
  let constants ← (Ix.Kernel.Admission.decodeRecords typingLimits committed.toList).mapError
    (toString ∘ Ix.Kernel.Admission.Error.ofBytes)
  let bytes : Std.HashMap Address ByteArray := committed.foldl (fun m (a, b) => m.insert a b) {}
  let ordered := Ixon.CheckOrder.wholeEnv table pre constants.toArray
  let records := ordered.toList.filterMap fun a => (bytes[a]?).map (a, ·)
  let projections : Std.HashMap (ConstRef Address) Address := constants.foldl (init := {}) fun m (a, c) =>
    match c.info with
    | .dPrj p => m.insert (.member p.block p.idx.toNat) a
    | _ => m
  return { records, projections, hints := env.anonHints
           blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList }

/-- The record a failure of the tiered entry is reported at, by its position
in `records`, when the failure has one. -/
def failureRecord (records : Ix.Kernel.Admission.Records) :
    Ix.Kernel.Admission.TierError → Option Address
  | .entry (.read p _) | .read p _ | .tier _ p => (records[p]?).map (·.1)
  | .entry (.decode _ a _) | .fence a _ => some a
  | _ => none

/-- **The typing half**: IxC's tiered entry at BLAKE3 over the whole
environment (`typingInput`), under the default role table. A logical decline
(an unsafe inductive's record among them, until 10d), a fence refusal or a
tier failure is `resource validator: erased typing failed`, with IxC's error
and, where it has one, the failing record. -/
def typeCheck (env : Ixon.Env) : Except String Unit := do
  let fail (e : String) : String := s!"resource validator: erased typing failed: {e}"
  let input ← (typingInput env).mapError fail
  let binding ← Ix.Kernel.Admission.defaultBinding.mapError fail
  match Ix.Kernel.Admission.checkBytesTiered Address.admissionHash binding typingLimits input.records
      input.blobs input.hint with
  | .ok _ => pure ()
  | .error e =>
    let site := match failureRecord input.records e with
      | some a => s!" at {a}"
      | none => ""
    throw s!"resource validator: erased typing failed{site}: {e}"

def validate (env : Ixon.Env) (profile : Profile) : Except String AddressedProgram := do
  checkLiteralProfile profile
  let resolved ← Addressed.checkResources env profile
  typeCheck env
  return resolved

end Ix.Resource

end
