import Aiur.Plonk.Lower
import Aiur.Tiling.Ixa
import Lean.Data.Json

/-!
# Reading `ix-aiur-plonk-terminal-v1` schemas

The terminal stage description (`ix-aiur-plonk-terminal-v1`, written by
`plonk::scs::stage` in `aiur_backend/plonk/scs.rs` through
`aiur_narrow_terminal_prove --stage-only`) as a `Source`. `plonk_export` and
`plonk_check_stage` read only its table names and row counts (and
`plonk_export` the public and output counts); every circuit's expressions come from the
`.ixa` (`WideIxa.stageOf`), so the description's own `nodes`, `constraints`
and `lookups` are empty and nothing in it is trusted beyond those shapes.

The root table's entry is the callable the schema names (`entryOf`), never
the first listed circuit: it must be an exported entry of the package, a
listed circuit, and receive `public_inputs` argument words and
`private_outputs` output words.
-/

namespace Aiur.Plonk.Schema

open Lean (Json)
open Aiur.Plonk.Lower (Fr)

def hexNat (s : String) : Except String Nat := do
  let digits : String := if s.startsWith "0x" then (s.drop 2).toString else s
  digits.toList.foldlM (fun acc ch => do
    let d ← if '0' ≤ ch && ch ≤ '9' then pure (ch.toNat - '0'.toNat)
      else if 'a' ≤ ch && ch ≤ 'f' then pure (ch.toNat - 'a'.toNat + 10)
      else if 'A' ≤ ch && ch ≤ 'F' then pure (ch.toNat - 'A'.toNat + 10)
      else throw s!"bad hex digit in {s}"
    pure (16 * acc + d)) 0

def field (j : Json) : Except String Fr := do
  match j with
  | .str s => return ((← hexNat s : Nat) : Fr)
  | .num n => return ((n.mantissa.toNat : Nat) : Fr)
  | _ => throw "expected a field element"

def natD (j : Json) (k : String) : Nat := ((j.getObjValAs? Nat k).toOption).getD 0
def boolD (j : Json) (k : String) : Bool := ((j.getObjValAs? Bool k).toOption).getD false

def node (j : Json) : Except String (Node Fr) := do
  match ← j.getObjValAs? String "op" with
  | "constant" => return .const (← field (← j.getObjVal? "value"))
  | "main" => return .main (natD j "column") (boolD j "next")
  | "fixed" => return .fixed (natD j "column") (boolD j "next")
  | "first" => return .first
  | "last" => return .last
  | "transition" => return .transition
  | "add" => return .add (natD j "a") (natD j "b")
  | "sub" => return .sub (natD j "a") (natD j "b")
  | "mul" => return .mul (natD j "a") (natD j "b")
  | "neg" => return .neg (natD j "a")
  | op => throw s!"unsupported node {op}"

def table (j : Json) : Except String (Table Fr) := do
  let nodes ← (← j.getObjValAs? (Array Json) "nodes").mapM node
  let fixed ← (← j.getObjValAs? (Array Json) "fixed").mapM field
  let lookups ← (← j.getObjValAs? (Array Json) "lookups").mapM fun l => do
    return { negative := boolD l "negative", count := natD l "count",
             args := (← l.getObjValAs? (List Nat) "args") }
  return { name := ← j.getObjValAs? String "name", rows := natD j "rows",
           width := natD j "main_width", fixedWidth := natD j "fixed_width", fixed, nodes,
           constraints := ← j.getObjValAs? (List Nat) "constraints", lookups := lookups.toList }

def source (j : Json) : Except String (Source Fr) := do
  let fmt ← j.getObjValAs? String "format"
  unless fmt == "ix-aiur-plonk-terminal-v1" || fmt == "ix-aiur-plonk-v1" do
    throw s!"unsupported schema format {fmt}"
  unless boolD j "boolean_requests" do
    throw "schemas without boolean requests need range-checked counts (not supported)"
  let tables ← (← j.getObjValAs? (Array Json) "circuits").mapM table
  return { callable := (natD j "callable" : Fr), publics := natD j "public_inputs",
           outputs := natD j "private_outputs", tables := tables.toList }

/-- The entry chip named by the schema's `callable`: the callable with that
index, listed in `pkg.entries` under it, among `circuits`, whose receive
message (`CALL :: id :: inputs ++ output`) has `public_inputs` argument words
and `private_outputs` output words. The root table's cells are that
message's words, so this pins which function the terminal proves. -/
def entryOf {F : Type} (pkg : Tiling.Ixa.Package F) (circuits : List (String × Nat)) (j : Json) :
    Except String String := do
  let nat (k : String) := (j.getObjValAs? Nat k).mapError (s!"schema {k}: {·}")
  let callable ← nat "callable"
  let publics ← nat "public_inputs"
  let outputs ← nat "private_outputs"
  let some name := pkg.callables[callable]? | throw s!"callable {callable} is not in the package"
  unless pkg.idOf name == callable do throw s!"callable {callable} ({name}) is not its name's first index"
  unless pkg.entries.any (· == (name, callable)) do
    throw s!"callable {callable} ({name}) is not an exported entry"
  unless circuits.any (·.1 == name) do throw s!"the entry {name} is not a listed circuit"
  let some chip := pkg.chips.find? (·.name == name) | throw s!"no chip {name} in the artifact"
  unless chip.inputs.length == publics && chip.output.length == outputs do
    throw s!"the entry {name} takes {chip.inputs.length} argument and {chip.output.length} output words, the schema {publics} and {outputs}"
  return name

end Aiur.Plonk.Schema
