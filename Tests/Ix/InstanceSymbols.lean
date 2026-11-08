import IxVM.Program
import MultiStark.Program

/-! Instance symbols are unchanged by the structural encoding.
`Aiur.Generic.Instance.symbol` used to be `"$" ++ (Lean.toJson key).compress`;
it is now written out character by character so that the kernel computes it
and its inverse is proved (`Aiur.Generic.Instance.ofSymbol_symbol`). Names,
and so the deployed programs and their digests, must not move. For every
instance symbol of every deployed program's specialized circuit program (its
function and enum names), this suite checks that

* the JSON parser reads it as some instance `key`;
* the new encoder gives back the same string, and so does the JSON encoder;
* the new parser reads the same `key`.

It also checks the escapes on instances the programs do not contain. -/

namespace Tests.Ix.InstanceSymbols

open Aiur

/-- The symbol as it was computed before. -/
def jsonSymbol (key : Generic.Instance) : String :=
  if key.types.isEmpty then key.name else "$" ++ (Lean.toJson key).compress

/-- The symbol's instance as it was parsed before. -/
def jsonOfSymbol (name : String) : Except String Generic.Instance :=
  if name.startsWith "$" then do
    Lean.fromJson? (← Lean.Json.parse (name.drop 1).toString)
  else return ⟨name, []⟩

/-- The `$` names of the specialized program for `entries`. -/
def symbolsOf {F : Type} [Field F] [DecidableEq F] (p : Modules.Program F) (entries : List String) :
    Except String (List String) := do
  let prepared ← Modules.prepare p entries
  let specialized ← Generic.specialize prepared.environment.source prepared.entries
  let names := specialized.program.functions.map (·.name) ++
    specialized.program.enums.map (·.name)
  return (names.filter (·.startsWith "$")).eraseDups

def agrees (key : Generic.Instance) (s : String) : Bool :=
  key.symbol == s && jsonSymbol key == s &&
    match Generic.Instance.ofSymbol s with
    | .ok parsed => parsed == key
    | .error _ => false

/-- Synthetic instances: every escape class, every type constructor. -/
def synthetic : List Generic.Instance := [
  ⟨"Lists::Node", [.field]⟩,
  ⟨"q\"uote\\back\nnl\rcr\x01ctl\x1ftab\tend é∀", [.param "x\"y", .tuple []]⟩,
  ⟨"Deep", [.array (.named "N" [.ptr .field, .tuple [.field, .param "T"]]) 0,
    .array .field 1234567890, .named "M::K" []]⟩]

def run : IO UInt32 := do
  let programs : List (String × Except String (List String)) := [
    ("IxVM verify_claim", symbolsOf IxVM.program ["IxVM::verify_claim"]),
    ("IxVM export entries", symbolsOf IxVM.program ["IxVM::verify_transitive",
      "IxVM::verify_constant", "IxVM::verify_serde", "IxVM::check_primitives",
      "IxVM::check_port_cases"]),
    ("MultiStark recursion", symbolsOf MultiStark.recursionProgram
      ["MultiStark::verify_multi_stark_proof"]),
    ("MultiStark aggregate", symbolsOf MultiStark.aggregateProgram ["MultiStark::ix_aggr"])]
  let mut failures := 0
  for (label, result) in programs do
    match result with
    | .error e =>
      IO.eprintln s!"[instance-symbols] FAIL {label}: {e}"
      failures := failures + 1
    | .ok symbols =>
      if symbols.isEmpty then
        IO.eprintln s!"[instance-symbols] FAIL {label}: no instance symbols"
        failures := failures + 1
      for s in symbols do
        match jsonOfSymbol s with
        | .error e =>
          IO.eprintln s!"[instance-symbols] FAIL {label}: JSON cannot read {s}: {e}"
          failures := failures + 1
        | .ok key =>
          unless agrees key s do
            IO.eprintln s!"[instance-symbols] FAIL {label}: {s} re-encodes as {key.symbol}"
            failures := failures + 1
      IO.println s!"[instance-symbols] {label}: {symbols.length} instance symbols checked"
  for key in synthetic do
    unless agrees key (jsonSymbol key) do
      IO.eprintln s!"[instance-symbols] FAIL synthetic {repr key}: {key.symbol} vs {jsonSymbol key}"
      failures := failures + 1
  IO.println s!"[instance-symbols] synthetic: {synthetic.length} instances checked"
  return if failures == 0 then 0 else 1

end Tests.Ix.InstanceSymbols
