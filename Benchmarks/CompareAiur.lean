import LegacyIxVM
import LegacyIxVM.Toplevel
import LegacyAiur.Compiler
import LegacyMultiStark

open Lean LegacyAiur

@[extern "rs_aiur_benchmark"]
opaque benchmark (top : @& Bytecode.Toplevel) (function : @& Nat)
    (input : @& ByteArray) (samples : @& Nat) (prove : Bool) : Except String String

def main (args : List String) : IO Unit := do
  let app := args[0]?.getD ""
  unless ["ixvm", "recursion"].contains app do
    throw (IO.userError "usage: bench-compare-aiur ixvm|recursion INPUT.json OUTPUT.json SAMPLES [--ungrouped] [--prove]")
  let input ← IO.FS.readBinFile (System.FilePath.mk (args[1]?.getD "input.json"))
  let source ← IO.ofExcept ((if app == "ixvm" then LegacyIxVM.ixVM else LegacyMultiStark.multiStark).mapError toString)
  let groups := if args.contains "--ungrouped" then #[] else
    if app == "ixvm" then LegacyIxVM.functionGroups else LegacyMultiStark.verifierFunctionGroups
  let compiled ← IO.ofExcept ((source.compileWithGroups groups).mapError toString)
  let entry := if app == "ixvm" then `verify_claim else `verify_multi_stark_proof
  let some idx := compiled.getFuncIdx entry | throw (IO.userError "missing benchmark entry")
  let samples := (args[3]?.getD "5").toNat?.getD 5
  let report ← IO.ofExcept (benchmark compiled.bytecode idx input samples (args.contains "--prove"))
  let names := compiled.bytecode.circuits.map (·.name) ++
    compiled.bytecode.memorySizes.map (fun width => s!"ROM:{width}") ++ #["Bytes1", "Bytes2"]
  let report ← IO.ofExcept (Json.parse report)
  let report := report.setObjVal! "circuit_names" (toJson names)
  IO.FS.writeFile (System.FilePath.mk (args[2]?.getD "legacy-bench.json")) report.pretty
  IO.println s!"Wrote {args[2]?.getD "legacy-bench.json"}"
