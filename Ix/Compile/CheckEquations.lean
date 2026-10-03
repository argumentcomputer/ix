/-
  Re-verify the checked unfolding equations an `ix compile` sidecar records.

  Under resource admission the equation sidecar (`ix/compile-equations/1`)
  lists, under `resourceChecked`, every `(definition, equation)` pair through
  which admission checked a definition: the consumer must run each such
  definition by the bound equation's right-hand side, fetched by address.
  `verify` establishes, from the closure and the sidecar alone, that the list
  is exactly what admission checked:

  * the sidecar's `resourceProfile.bytes` decode to a valid canonical profile
    whose BLAKE3 hash is `resourceProfile.address`, the address every entry
    names, and `root` is the closure's canonical root;
  * the closure is admitted under that profile (resources and erased typing,
    `Ix.Resource.checkClaim`), which is the resource claim `(root, profile)`;
  * the entries are exactly the bound pairs of resource-relevant, unassumed
    definitions — the pairs admission checked through equations — each named
    by the definition's and the theorem's addresses in the closure;
  * each theorem is a theorem of the closure whose statement has the shape
    `∀ xs, f xs = rhs` for the stated definition `f` (`Ix.Resource.equationBody`),
    and carries the stated contracts at the stated telescope positions.
-/
module
public import Lean.Data.Json
public import Ix.Resource.Claim

public section

namespace Ix.Compile.CheckEquations

open Lean Ix.Resource

/-- A carried contract as the sidecar states it. -/
structure Contract where
  position : Nat
  uses : Ixon.Uses
  value : Ixon.ValueContract
  deriving Inhabited, Repr, BEq

/-- One `resourceChecked` entry. -/
structure Entry where
  definition : String
  equation : String
  definitionAddress : Address
  equationAddress : Address
  profile : Address
  contracts : Array Contract := #[]
  deriving Inhabited, Repr

/-- What a successful verification establishes. -/
structure Report where
  root : Address
  profile : Address
  claim : Ix.Claim
  entries : Array Entry
  deriving Inhabited

private def field (j : Json) (key : String) : Except String Json :=
  (j.getObjVal? key).mapError fun _ => s!"check-equations: missing `{key}`"

private def string (j : Json) (key : String) : Except String String := do
  match ← field j key with
  | .str s => pure s
  | _ => throw s!"check-equations: `{key}` must be a string"

private def address (j : Json) (key : String) : Except String Address := do
  match Address.fromString (← string j key) with
  | some a => pure a
  | none => throw s!"check-equations: `{key}` must be a 64-digit hex address"

private def array (j : Json) (key : String) : Except String (Array Json) := do
  match ← field j key with
  | .arr xs => pure xs
  | _ => throw s!"check-equations: `{key}` must be an array"

def parseUses : String → Except String Ixon.Uses
  | "erased" => pure .erased
  | "linear" => pure .linear
  | "affine" => pure .affine
  | "many" => pure .many
  | other => throw s!"check-equations: unknown uses `{other}`"

def parseContract (j : Json) : Except String Contract := do
  let position ← match ← field j "position" with
    | .num n => match n.mantissa.toNat?, n.exponent with
      | some p, 0 => pure p
      | _, _ => throw "check-equations: `position` must be a natural number"
    | _ => throw "check-equations: `position` must be a natural number"
  let uses ← parseUses (← string j "uses")
  let owned : Ixon.Owned ← match ← string j "owned" with
    | "unique" => pure .unique
    | "shared" => pure .shared
    | other => throw s!"check-equations: unknown ownership `{other}`"
  let locality : Ixon.Locality ← match ← string j "locality" with
    | "local" => pure .local
    | "unrestricted" => pure .unrestricted
    | other => throw s!"check-equations: unknown locality `{other}`"
  return { position, uses, value := { owned, locality } }

def parseEntry (j : Json) : Except String Entry := do
  return {
    definition := ← string j "definition"
    equation := ← string j "equation"
    definitionAddress := ← address j "definitionAddress"
    equationAddress := ← address j "equationAddress"
    profile := ← address j "profile"
    contracts := ← (← array j "contracts").mapM parseContract }

/-- The binder contracts of an equation statement's telescope, peeled as
`equationBody` peels it. -/
def statementBinders (program : Program) (fuel : Nat) (equation : UInt64) :
    CheckM (Array Ixon.BinderContract) := do
  let mut statement := (← declaration program equation).type
  let mut binders := #[]
  repeat
    match ← whnf program fuel statement with
    | .all c _ _ body =>
      binders := binders.push c
      statement := body
    | _ => break
  return binders

private def runCheck (limits : Limits) (action : CheckM α) : Except String α :=
  match action.run { remaining := limits.steps } with
  | .ok value _ => .ok value
  | .error error _ => .error s!"{repr error}"

private def indexOf (resolved : AddressedProgram) (a : Address) : Option Nat :=
  resolved.addresses.findIdx? (· == a)

/-- Verify a sidecar against the closure it describes (see the module
docstring). -/
def verify (env : Ixon.Env) (sidecar : Json) : Except String Report := do
  unless (← string sidecar "format") == "ix/compile-equations/1" do
    throw "check-equations: not an `ix/compile-equations/1` sidecar"
  let resourceProfile ← (field sidecar "resourceProfile").mapError fun _ =>
    "check-equations: the sidecar records no resource profile (no resource admission ran)"
  let stated ← address resourceProfile "address"
  let some bytes := bytesOfHex (← string resourceProfile "bytes")
    | throw "check-equations: `bytes` must be hex"
  let profile ← Profile.ofBytes bytes
  let profileAddress ← profile.address
  unless profileAddress == stated do
    throw s!"check-equations: the profile bytes hash to {profileAddress}, not the stated {stated}"
  let some root := env.merkleRoot | throw "check-equations: empty closure"
  unless (← address sidecar "root") == root do
    throw s!"check-equations: the sidecar's root is not the closure's root {root}"
  let claim := Ix.Claim.resource root profileAddress
  let resolved ← checkClaim env profile claim
  let program := resolved.program
  let marked ← (relevance program profile.limits).mapError fun e =>
    s!"check-equations: relevance: {repr e}"
  -- The pairs admission checked a definition through: bound, relevant, not assumed.
  let mut checked : Array (Address × Address) := #[]
  for (d, t) in program.equations do
    if marked[d.toNat]?.getD false && !resolved.policy.assumptions.contains d.toNat then
      checked := checked.push (resolved.addresses[d.toNat]!, resolved.addresses[t.toNat]!)
  let entries ← (← array sidecar "resourceChecked").mapM parseEntry
  let listed := entries.map fun e => (e.definitionAddress, e.equationAddress)
  for pair in listed do
    unless checked.contains pair do
      throw s!"check-equations: {pair.1} ↦ {pair.2} is not a pair resource admission checked under the profile"
  for pair in checked do
    unless listed.contains pair do
      throw s!"check-equations: the checked pair {pair.1} ↦ {pair.2} is missing from the sidecar"
  unless listed.size == checked.size do
    throw "check-equations: a checked pair is listed more than once"
  for e in entries do
    unless e.profile == profileAddress do
      throw s!"check-equations: {e.definition}: profile {e.profile} is not the stated {profileAddress}"
    unless env.consts.contains e.definitionAddress && env.consts.contains e.equationAddress do
      throw s!"check-equations: {e.definition}: an address is not in the closure"
    let some d := indexOf resolved e.definitionAddress
      | throw s!"check-equations: {e.definition}: the definition is not a declaration"
    let some t := indexOf resolved e.equationAddress
      | throw s!"check-equations: {e.equation}: the theorem is not a declaration"
    unless program.declarations[t]!.kind == .theorem do
      throw s!"check-equations: {e.equation} is not a theorem"
    -- The statement shape `∀ xs, f xs = rhs` for this definition.
    let _ ← (runCheck profile.limits (equationBody program profile.limits.depth d.toUInt64 t.toUInt64)).mapError
      fun m => s!"check-equations: {e.equation} does not unfold {e.definition}: {m}"
    let binders ← runCheck profile.limits (statementBinders program profile.limits.depth t.toUInt64)
    for c in e.contracts do
      let some b := binders[c.position]?
        | throw s!"check-equations: {e.equation}: no binder at position {c.position}"
      unless b.uses == c.uses && b.value == c.value do
        throw s!"check-equations: {e.equation}: the binder at position {c.position} does not carry the stated contract"
  return { root, profile := profileAddress, claim, entries }

end Ix.Compile.CheckEquations

end
