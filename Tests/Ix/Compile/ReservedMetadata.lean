/-
  compile-reserved-mdata: an input expression whose metadata key has the
  reserved component `_ix` (D14) is refused by both compilers, as an input
  name with that component is. Otherwise source metadata could impersonate a
  Pass 3 placeholder (`[(_ix.inline, n)]`) or a decompile record
  (`[(_ix.inline, s), (_ix.inline_meta, m)]`), and decompilation would put
  another occurrence in place of the source subterm.

  Cases, each a closure of one definition `d` whose value is wrapped in the
  metadata: the placeholder form, the record form, and the valid neighbour,
  an ordinary key, which both compilers compile byte-identically.

  Run with: `lake test -- --ignored compile-reserved-mdata`.
-/
import Tests.Ix.Compile.IndFlags

open Lean

namespace Tests.Ix.Compile.ReservedMetadata

namespace Fixture

/-- The definition whose value carries the metadata. -/
def d : Nat := 0

end Fixture

def dName : Name := ``Fixture.d

/-- The closure of `d`, with `d`'s value wrapped in `kvs`. -/
def closure (env : Environment) (kvs : List (Name × DataValue)) :
    Except String (List (Name × ConstantInfo)) := do
  let base := Tests.Ix.Compile.Twins.closeWithRecursors env
    (Ix.EnvScope.collectDeps env [dName])
  let some (.defnInfo v) := env.find? dName | throw "d missing"
  return base.map fun (n, ci) =>
    if n == dName then (n, .defnInfo { v with value := .mdata { entries := kvs } v.value })
    else (n, ci)

/-- The expected refusal's text, without the error-kind prefix. -/
def message : String :=
  s!"input constant '{dName}' has a metadata key with the reserved component `_ix` \
(D14: `_ix` names the Ix auxiliaries and images of the faithful rewrite)"

def cases : List (String × List (Name × DataValue)) :=
  [("placeholder", [(`_ix.inline, .ofNat 0)]),
   ("record", [(`_ix.inline, .ofNat 0), (`_ix.inline_meta, .ofNat 0)])]

def run : IO UInt32 := do
  let env ← get_env!
  let dir ← IO.FS.createTempDir
  let mut failures := 0
  try
    -- valid neighbour: an ordinary key compiles in both, byte-identically
    let good ← IO.ofExcept (closure env [(`userKey, .ofNat 0)])
    match ← IndFlags.rust env good (dir / "good.ixe"), ← IndFlags.lean env good with
    | .ok r, .ok l =>
      if r == l then IO.println "[reserved-mdata] ordinary key: both compile, byte-identical"
      else
        failures := failures + 1
        IO.println "[reserved-mdata] ordinary key: FAIL: outputs differ"
    | r, l =>
      failures := failures + 1
      IO.println s!"[reserved-mdata] ordinary key: FAIL: rust {r.isOk}, lean {l.isOk}"
    for (label, kvs) in cases do
      let bad ← IO.ofExcept (closure env kvs)
      let out := dir / s!"{label}.ixe"
      for (leg, result) in [("rust", ← IndFlags.rust env bad out), ("lean", ← IndFlags.lean env bad)] do
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
  finally
    IO.FS.removeDirAll dir
  IO.println s!"[reserved-mdata] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ReservedMetadata
