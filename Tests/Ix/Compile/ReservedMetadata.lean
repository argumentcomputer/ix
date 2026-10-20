/-
  compile-reserved-mdata: both compilers refuse reserved input (
  `Ix.Compile.Pass.Names`): an input constant whose metadata key has the
  reserved component `_ix` (Rust `compile_env`, Lean
  `Ix.CompileM.reservedMetadataRefusal?`), and an input name with that
  component (Rust `pass3::names::reserved_input_in`, Lean
  `Ix.CompileM.reservedInputRefusal?`). Otherwise source metadata could
  impersonate a Pass 3 placeholder (`[(_ix.inline, n)]`) or decompile record
  (`[(_ix.inline, s), (_ix.inline_meta, m)]`), and a source name an Ix
  auxiliary's display name.

  Cases, each the closure of one definition `d` (with the aux-gen seeds,
  `IndFlags.closureOf`): `d`'s value wrapped in the placeholder form and in
  the record form; `d` renamed `Fixture._ix.d`; and both at once, where the
  metadata refusal comes first in both compilers. The valid neighbour, an
  ordinary key, compiles in both, byte-identically. The legs are the Rust
  compiler (`ix compile`'s FFI) and the IO pipeline (`compile-lean`).

  The drivers' case of `reserved-input` (D14, ported from the donor's
  `pass3` unit `ReservedIx`): three definitions renamed `Fixture._ix.f`,
  `Fixture.Z._ix.h` and `Fixture.A._ix.g` (the last declared is the least
  by its text); both drivers refuse naming exactly the least, as
  `reserved-input` checks of `reservedInputRefusal?` on synthetic
  condensations.

  Run with: `lake test -- --ignored compile-reserved-mdata`.
-/
import Tests.Ix.Compile.IndFlags

open Lean

namespace Tests.Ix.Compile.ReservedMetadata

namespace Fixture

/-- The definition whose value carries the metadata. -/
def d : Nat := 0

/-- Definitions that `severalReserved` renames to reserved names. -/
def r1 : Nat := 1
def r2 : Nat := 2
def r3 : Nat := 3

end Fixture

def dName : Name := ``Fixture.d

/-- `d` under a reserved name. -/
def reservedName : Name := dName.getPrefix ++ `_ix.d

/-- The closure of `d`, with `d`'s value wrapped in `kvs` (when there are
    any) and `d` renamed `name`. -/
def closure (env : Environment) (kvs : List (Name × DataValue)) (name : Name := dName) :
    Except String (List (Name × ConstantInfo)) := do
  let base := IndFlags.closureOf env [dName]
  let some (.defnInfo v) := env.find? dName | throw "d missing"
  let value := if kvs.isEmpty then v.value else .mdata { entries := kvs } v.value
  return base.map fun (n, ci) =>
    if n == dName then (name, .defnInfo { v with name, value, all := [name] })
    else (n, ci)

/-- A name's display form, as both compilers print it. -/
def pretty (n : Name) : String := (Ix.Name.fromLeanName n).pretty

/-- The metadata refusal's text, without the error-kind prefix. -/
def metadataMessage (n : Name) : String :=
  s!"input constant '{pretty n}' has a metadata key with the reserved component `_ix` \
(`_ix` names the Ix auxiliaries and images of the faithful rewrite)"

/-- The name refusal's text, without the error-kind prefix. -/
def nameMessage (n : Name) : String :=
  s!"input name '{pretty n}' contains the reserved component `_ix` \
(`_ix` names the Ix auxiliaries and images of the faithful rewrite)"

def placeholder : List (Name × DataValue) := [(`_ix.inline, .ofNat 0)]

def record : List (Name × DataValue) := [(`_ix.inline, .ofNat 0), (`_ix.inline_meta, .ofNat 0)]

/-- `r1`, `r2`, `r3` and their reserved names, in declaration order. -/
def severalRenames : List (Name × Name) :=
  let p := dName.getPrefix
  [(p ++ `r1, p ++ `_ix.f), (p ++ `r2, p ++ `Z._ix.h), (p ++ `r3, p ++ `A._ix.g)]

/-- The least of `severalRenames`' reserved names by their text. -/
def leastReserved : Name := dName.getPrefix ++ `A._ix.g

/-- The closure of `r1`, `r2`, `r3`, each renamed by `severalRenames`. -/
def severalReserved (env : Environment) : List (Name × ConstantInfo) :=
  (IndFlags.closureOf env (severalRenames.map (·.1))).map fun (n, ci) =>
    match severalRenames.lookup n, ci with
    | some m, .defnInfo v => (m, .defnInfo { v with name := m, all := [m] })
    | _, _ => (n, ci)

/-- Label, metadata, name, expected refusal. -/
def cases : List (String × List (Name × DataValue) × Name × String) :=
  [("placeholder", placeholder, dName, metadataMessage dName),
   ("record", record, dName, metadataMessage dName),
   ("reserved name", [], reservedName, nameMessage reservedName),
   ("reserved name and metadata", placeholder, reservedName, metadataMessage reservedName)]

def run : IO UInt32 := do
  let env ← get_env!
  let dir ← IO.FS.createTempDir
  let mut failures := 0
  try
    -- valid neighbour: an ordinary key compiles in both, byte-identically
    let good ← IO.ofExcept (closure env [(`userKey, .ofNat 0)])
    match ← IndFlags.rust env good (dir / "good.ixe"), ← IndFlags.lean env good with
    | .ok r, .ok l =>
      if r == l then
        IO.println s!"[reserved-mdata] ordinary key: both compile, byte-identical ({r.size} bytes)"
      else
        failures := failures + 1
        IO.println s!"[reserved-mdata] ordinary key: FAIL: outputs differ \
(rust {r.size}, lean {l.size} bytes)"
    | r, l =>
      failures := failures + 1
      IO.println s!"[reserved-mdata] ordinary key: FAIL: rust {IndFlags.showLeg r}; \
lean {IndFlags.showLeg l}"
    for (label, kvs, name, message) in cases do
      let bad ← IO.ofExcept (closure env kvs name)
      let legs := [("rust", ← IndFlags.rust env bad (dir / s!"{label}.ixe")),
        ("lean", ← IndFlags.lean env bad)]
      for (leg, result) in legs do
        match result with
        | .ok _ =>
          failures := failures + 1
          IO.println s!"[reserved-mdata] {label}: {leg}: FAIL: compiled"
        | .error e =>
          if (e.splitOn message).length > 1 then
            IO.println s!"[reserved-mdata] {label}: {leg} refuses: {message}"
          else
            failures := failures + 1
            IO.println s!"[reserved-mdata] {label}: {leg}: FAIL: other refusal: {e}"
    -- several reserved names: both drivers name exactly the least
    let several := severalReserved env
    let message := nameMessage leastReserved
    let others := (severalRenames.map (·.2)).filter (· != leastReserved)
    let legs := [("rust", ← IndFlags.rust env several (dir / "several.ixe")),
      ("lean", ← IndFlags.lean env several)]
    for (leg, result) in legs do
      match result with
      | .ok _ =>
        failures := failures + 1
        IO.println s!"[reserved-mdata] several reserved names: {leg}: FAIL: compiled"
      | .error e =>
        let named := others.filter fun n => (e.splitOn s!"'{pretty n}'").length > 1
        if (e.splitOn message).length > 1 && named.isEmpty then
          IO.println s!"[reserved-mdata] several reserved names: {leg} names the least: {message}"
        else
          failures := failures + 1
          IO.println s!"[reserved-mdata] several reserved names: {leg}: FAIL: not exactly the \
least ({pretty leastReserved}): {e}"
  finally
    IO.FS.removeDirAll dir
  IO.println s!"[reserved-mdata] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ReservedMetadata
