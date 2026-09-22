import Tests.Aiur.TraceCodegen
import Ix.Aiur.Stages.TraceCuda

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty || args == ["--check"] do
    IO.eprintln "Expected no arguments or --check"
    return 1
  let files : Except String (Array (String × String)) := do
    let mut files := #[]
    let mut units := #[]
    for (unit, top) in #[("fixtures", ← AiurTests.TraceCodegen.fixtureProgram),
        ("blake3", ← AiurTests.TraceCodegen.blake3Program)] do
      let stem := if unit == "fixtures" then "generated" else "blake3"
      let cuda ← Aiur.TraceCuda.emit top unit
      let digest := (Blake3.Rust.hash cuda.toUTF8).val.data.map fun n => Lean.toJson n.toNat
      let path := s!"cuda/generated/{unit}.cu"
      units := units.push (Lean.Json.mkObj [("source", Lean.toJson path), ("digest", Lean.Json.arr digest)])
      files := files ++ #[
        (s!"crates/aiur/src/trace_codegen/tests/{stem}.rs", ← Aiur.TraceCodegen.emit top "crate"),
        (s!"crates/aiur/src/trace_codegen/tests/{stem}_cuda.rs", ← Aiur.TraceCuda.registry top unit "crate"),
        (s!"crates/aiur/{path}", cuda)]
    let manifest := Lean.Json.mkObj [("abi", Lean.toJson (2 : Nat)), ("units", Lean.Json.arr units)]
    pure (files.push ("crates/aiur/cuda/trace-manifest.json", manifest.pretty ++ "\n"))
  let files ← match files with
    | .ok files => pure files
    | .error error => IO.eprintln error; return 1
  for (path, source) in files do
    if args == ["--check"] then
      if (← IO.FS.readFile path) != source then
        IO.eprintln s!"{path} is stale"
        return 1
    else
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path source
    IO.println s!"{path}: {source.utf8ByteSize} bytes"
  return 0
