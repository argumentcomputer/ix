import Ix.IxVM.Toplevel
import Ix.IxVM.FunctionGroups
import Ix.Aggr
import Ix.Aiur.Statistics
import Lean.Data.Json

/-! Native function-group validation and cost comparison without Rust/CUDA
regeneration. `check ixvm|aggr` checks the production partition and preserves
the complete function library. `measure KIND BEFORE AFTER PROFILE OUTPUT`
compares two JSON arrays of `(groupName, memberNames)` pairs; `-` selects the
production groups. PROFILE contains the per-function rows, names and layouts
reported by the execution profiler. It must describe the same function
library; its digest, indices, names and layouts are checked. The digest is
a stale-profile diagnostic, separate from the function-preservation checks.

The report uses actual synthesized AIR shapes, raw and power-of-two padded
function FFT costs, active committed width and serialized VK size. Function
heights are unchanged by grouping; memory/gadget costs are unchanged and are
excluded from the function cost totals. Proofs and security parameters are
not modified by this fixture.
-/

namespace FunctionGrouping

open Aiur Lean

private abbrev Groups := Array (String × Array String)

private structure FunctionProfile where
  index : Nat
  names : Array String
  rows : Nat
  inputs : Nat
  selectors : Nat
  auxiliaries : Nat
  lookups : Nat
  constrained : Bool
  deriving FromJson, Inhabited

private structure Profile where
  libraryDigest : String
  functions : Array FunctionProfile
  deriving FromJson

private def libraryDigest (compiled : CompiledToplevel) : String :=
  toString (Address.blake3 (reprStr (compiled.bytecode.functions, compiled.bytecode.memorySizes)).toUTF8)

private def compileProgram (kind : String) : IO (CompiledToplevel × Groups) := do
  let (top, groups) ← match kind with
    | "ixvm" => do
      let top ← IO.ofExcept (IxVM.ixVM.mapError toString)
      pure (top, IxVM.functionGroups)
    | "aggr" => do
      let top ← IO.ofExcept (Aggr.ixAggr.mapError toString)
      pure (top, Aggr.functionGroups)
    | _ => throw (IO.userError "expected ixvm or aggr")
  return (← IO.ofExcept top.compile, groups)

private def readGroups (path : String) (production : Groups) : IO Groups := do
  if path == "-" then return production
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (fromJson? json)

private def validate (raw grouped : CompiledToplevel) : IO Unit := do
  unless raw.bytecode.memorySizes == grouped.bytecode.memorySizes &&
      raw.bytecode.functions.size == grouped.bytecode.functions.size &&
      raw.nameMap.size == grouped.nameMap.size do
    throw (IO.userError "grouping changed the program interface")
  for (name, index) in raw.nameMap do
    unless grouped.nameMap.get? name == some index do
      throw (IO.userError s!"grouping changed function index {name}")
  for (before, after) in raw.bytecode.functions.zip grouped.bytecode.functions do
    unless before.body == after.body && before.layout == after.layout &&
        before.entry == after.entry && before.constrained == after.constrained do
      throw (IO.userError "grouping changed a function body, layout or execution flag")
  let mut seen : Std.HashSet Nat := {}
  for circuit in grouped.bytecode.circuits do
    unless !circuit.members.isEmpty do throw (IO.userError "empty circuit")
    for index in circuit.members do
      let some func := grouped.bytecode.functions[index]?
        | throw (IO.userError "circuit member is outside the function library")
      unless func.constrained && !seen.contains index &&
          (!func.entry || circuit.members.size == 1) do
        throw (IO.userError "duplicate, unconstrained or grouped entry function")
      seen := seen.insert index
  for index in [:raw.bytecode.functions.size] do
    unless seen.contains index == raw.bytecode.functions[index]!.constrained do
      throw (IO.userError "the partition does not cover exactly the constrained functions")

private def readRows (raw : CompiledToplevel) (path : String) : IO (Array Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let profile : Profile ← IO.ofExcept (fromJson? json)
  unless profile.libraryDigest == libraryDigest raw do
    throw (IO.userError "profile function-library digest does not match the compiled program")
  unless profile.functions.size == raw.bytecode.functions.size do
    throw (IO.userError "profile has a different function count")
  let byName := raw.nameMap.fold (init := ({} : Std.HashMap String Nat))
    fun map name index => map.insert (toString name) index
  for index in [:profile.functions.size] do
    let row := profile.functions[index]!
    let func := raw.bytecode.functions[index]!
    unless row.index == index && !row.names.isEmpty &&
        row.names.all (fun name => byName.get? name == some index) &&
        row.inputs == func.layout.inputSize && row.selectors == func.layout.selectors &&
        row.auxiliaries == func.layout.auxiliaries && row.lookups == func.layout.lookups &&
        row.constrained == func.constrained do
      throw (IO.userError s!"profile index, names or layout differ at function {index}")
  return profile.functions.map (·.rows)

private def reportGroups (raw : CompiledToplevel) (groups : Groups)
    (rows : Option (Array Nat)) : IO Json := do
  let compiled ← IO.ofExcept (raw.groupFunctions groups)
  validate raw compiled
  let system ← IO.lazyPure fun _ => AiurSystem.build compiled.bytecode
    defaultCommitmentParameters defaultFriParameters
  let shapes := system.circuitShapes
  let mut activeWidth := 0
  let mut cost := 0.0
  let mut paddedCost := 0.0
  let mut circuits : Array Json := #[]
  for index in [:compiled.bytecode.circuits.size] do
    let circuit := compiled.bytecode.circuits[index]!
    let shape := shapes[index]!
    let height := rows.map fun counts => circuit.members.foldl (fun n i => n + counts[i]!) 0
    if let some h := height then
      if h > 0 then activeWidth := activeWidth + shape.committedWidth
      cost := cost + fftCost shape h defaultCommitmentParameters.logBlowup
      let padded := if h == 0 then 0 else Nat.nextPowerOfTwo h
      paddedCost := paddedCost + fftCost shape padded defaultCommitmentParameters.logBlowup
    circuits := circuits.push (Json.mkObj [
      ("name", toJson circuit.name), ("members", toJson circuit.members),
      ("height", toJson height), ("mainWidth", toJson shape.mainWidth),
      ("stage2Width", toJson shape.stage2Width), ("quotientDegree", toJson shape.quotientDegree),
      ("committedWidth", toJson shape.committedWidth)])
  return Json.mkObj [
    ("libraryDigest", toJson (libraryDigest raw)),
    ("functionLibraryUnchanged", toJson true), ("functionCount", toJson raw.bytecode.functions.size),
    ("circuitCount", toJson circuits.size), ("vkBytes", toJson system.vkBytes.size),
    ("totalCommittedWidth", toJson (shapes.foldl (fun n s => n + s.committedWidth) 0)),
    ("hasProfile", toJson rows.isSome), ("activeFunctionWidth", toJson activeWidth),
    ("functionFftCost", toJson cost), ("paddedFunctionFftCost", toJson paddedCost),
    ("circuits", toJson circuits)]

def run (args : List String) : IO Unit := do
  match args with
  | ["check", kind] =>
    let (raw, groups) ← compileProgram kind
    let report ← reportGroups raw groups none
    IO.println report.compress
  | ["measure", kind, before, after, profile, output] =>
    let (raw, production) ← compileProgram kind
    let rows ← readRows raw profile
    let baseline ← reportGroups raw (← readGroups before production) (some rows)
    let candidate ← reportGroups raw (← readGroups after production) (some rows)
    IO.FS.writeFile output (Json.mkObj [("baseline", baseline), ("candidate", candidate)]).pretty
    IO.println s!"Grouping comparison written to {output}; function library and partition validated"
  | _ => throw (IO.userError
      "expected check ixvm|aggr, or measure KIND BEFORE_GROUPS AFTER_GROUPS PROFILE OUTPUT")

end FunctionGrouping

def main (args : List String) : IO Unit := FunctionGrouping.run args
