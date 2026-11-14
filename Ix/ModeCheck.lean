module

public import Ix.Typing
public import IxC.Resource

/-!
# Mode checking of a compiled artifact (uncertified)

`checkArtifact` runs the mode checker (`IxC.Resource.check`) on an artifact:
every record of it is a seed. Every record in the subject closure must carry a
complete binder-data section (`Ixon.Constant.bindersComplete`) and canonical
mode bytes (`Ixon.Constant.modesCanonical`). An artifact whose every mode is
the default is accepted without typing (the checker's fast path). Otherwise the
checker reads its run program with the kernel as class oracle, over the
environment the artifact's certified typing installs (`Ix.Typing.checkCertified`,
with the tier-owner fallback when batch tier checking refuses a `partial` or
`unsafe` definition), and accepts, refuses with a witness, or declines at a
limit.

**Definition assertions (`Ixon.DefAsserts`)**: backend assertions (`noRc`,
`noAlloc`, `boundedStack`) are committed by reveal and compile claims for
downstream codegen backends and are **not** verified by `ModeCheck`, except for
structural admissibility: theorems carry none (`modesCanonical`), role-bound
records must carry default (`{}`) assertions, and constants without a safe run
body outside the extern set must carry default (`{}`) assertions. A safe
runnable definition carrying non-default `DefAsserts` skips the untyped fast
path so certified typing still runs before `IxC.Resource.check`.

**The checker is uncertified**: nothing proves its verdict (`IxC.Resource.CheckSound`
is a definition, the statement left to prove), and every message here says so.
-/

@[expose] public section

namespace Ix.ModeCheck

/-- A verdict's message. -/
def describe : IxC.Resource.Verdict → String
  | .accept _ true => "mode checking (uncertified): every mode is the default"
  | .accept n false => s!"mode checking (uncertified): {n} run bodies checked, accepted"
  | .refuse at_ w => s!"mode checking (uncertified) refuses {at_}: {w}"
  | .decline r => s!"mode checking (uncertified) declines: {r}"

/-- Validate closure completeness, canonical mode invariants, and `DefAsserts`
placement on `s`, returning `true` iff every record in the closure carries only
default modes and default `DefAsserts` (eligible for the fast path). -/
def checkSubject (s : IxC.Resource.Subject) : Except String Bool := do
  let rd := IxC.Resource.Reading.make s
  rd.complete
  let roleBlocks : Std.HashSet Address :=
    s.table.bound.foldl (init := {}) fun acc (_, x) =>
      let b := match Ix.Kernel.Reader.resolve s.store x with
        | some r => r.block
        | none => x
      acc.insert b
  let mut hasAsserts := false
  for a in rd.closure do
    let some c := s.store a | continue
    unless c.modesCanonical do
      throw s!"record {a}: a theorem carries definition assertions"
    let defs : Array (Nat × Ixon.Definition) := match c.info with
      | .defn d => #[(0, d)]
      | .muts ms => ms.zipIdx.filterMap fun
        | (.defn d, i) => some (i, d)
        | _ => none
      | _ => #[]
    for (i, d) in defs do
      if d.asserts != {} then
        hasAsserts := true
        if roleBlocks.contains a then
          throw "a constant the role table binds sits in a record that carries modes"
        let ref : IxC.Resource.Ref := .member a i
        let runnable := d.kind == .defn && d.safety == .safe
        unless runnable || IxC.Resource.isExtern s ref do
          throw "an annotated constant with no run body is not in the extern set: its modes are promises nothing checks"
  let defaultModes ← IxC.Resource.allDefault s
  return defaultModes && !hasAsserts

/-- **Mode checking of an artifact** (uncertified): the message of an accept,
or the refusal or decline as the error. -/
def checkArtifact (ixe : Ixon.Env) : Except String String := do
  let input ← Ix.Typing.typingInput ixe
  let records : Std.HashMap Address Ixon.Constant :=
    input.ordered.foldl (fun m (a, c, _) => m.insert a c) {}
  let prelude : Std.HashMap Address Ixon.Constant :=
    (input.pre.records ++ input.pre.evidence).foldl (fun m (a, c) => m.insert a c) {}
  let blobs : Std.HashMap Address ByteArray :=
    (input.blobs ++ input.pre.blobs).foldl (fun m (a, b) => m.insert a b) {}
  let s : IxC.Resource.Subject :=
    { table := input.table, store := fun a => records[a]? <|> prelude[a]?, blob := fun a => blobs[a]?,
      seeds := input.ordered.toList.map (·.1) }
  -- the fast path needs no typing once closure completeness and assertions are verified
  match checkSubject s with
  | .error e => throw s!"mode checking (uncertified) refuses: malformed modes: {e}"
  | .ok true => return describe (.accept 0 true)
  | .ok false => pure ()
  let note := if !input.bound && input.ordered.any (fun (_, c, _) => Ix.Typing.isUndecidedSafeRecord c) then
      Ix.Typing.undecidedRoleNote true
    else ""
  let unc := Ix.Typing.splitOf input
  let env ← match Ix.Typing.checkCertified input unc with
    | .ok env₀ =>
      unless unc.isEmpty do
        (Ix.Typing.typeUncertified input unc env₀).mapError fun e =>
          s!"mode checking (uncertified): the typing it reads with failed: {e}{note}"
      pure env₀
    | .error (e, isTier) =>
      unless isTier do
        throw s!"mode checking (uncertified): the typing it reads with failed: {e}{note}"
      let unc := (Ix.Typing.tierOwnersOf input).fold (·.insert ·) unc
      let env₀ ← (Ix.Typing.checkCertified input unc).mapError fun (e', _) =>
        s!"mode checking (uncertified): the typing it reads with failed: {e'}{note}"
      (Ix.Typing.typeUncertified input unc env₀).mapError fun e' =>
        s!"mode checking (uncertified): the typing it reads with failed: {e'}{note}"
      pure env₀
  let v := IxC.Resource.check {} env s
  match v with
  | .accept .. => return describe v
  | _ => throw (describe v)

end Ix.ModeCheck

end
