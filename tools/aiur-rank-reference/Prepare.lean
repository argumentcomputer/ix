import IxCC.Tools.Check

open Lean System IxCC.Tools.Check

private def pins : List (String × String) := [
  ("lib.rs", "88d605423f79e310b73a643e122babae76a87407571edee7a1887faeb9a7f142"),
  ("constraints.rs", "f9c8d433e4c49987b21b8e33be0533eb1f2b6e8b75ab26d8ffaf2f7fe9889fa9"),
  ("gadgets.rs", "bd755d8f39675004fdc5434e66344c4ed8849de9ad91a58f86e121b5a522baeb"),
  ("gadgets/bytes2.rs", "f0fc58ec29c758b3b398977311efb6e3b1df8b01f6916e9ebd464a34ed8e866a"),
  ("call_order.rs", "8660340043b03c728f72431f86f8d5244056363a71fb4f5fba1478deb7207c73"),
  ("bytecode.rs", "f3b2ac1a00db49f964313010a63b39906a6b8c30f51b1e1087edf782be6d8cb6")]

def main (args : List String) : IO UInt32 := cli "rank reference preparation failed" do
  let [upstream, output] := args | throw (IO.userError "usage: Prepare.lean PINNED_IX OUTPUT_DIRECTORY")
  let upstream ← IO.FS.realPath upstream
  let repository ← IO.FS.realPath "."
  let source := upstream / "crates/aiur/src"
  for (path, expected) in pins do
    need ((← sha256 (source / path)) == expected) s!"pinned Rust source differs: {path}"
  let tool := repository / "tools/aiur-rank-reference"
  let manifest ← IO.FS.readFile (tool / "Cargo.toml.in")
  let libPath := (toJson (source / "lib.rs").toString).compress
  let exportPath := (toJson (tool / "Export.rs").toString).compress
  let wrapper := s!"include!({libPath});\n#[path = {exportPath}]\nmod reference;\n" ++
    "fn main() {\n    let output = std::env::args().nth(1).expect(\"output directory required\");\n" ++
    "    reference::run(std::path::Path::new(&output));\n}\n"
  let output := FilePath.mk output
  IO.FS.createDirAll (output / "src")
  IO.FS.writeFile (output / "Cargo.toml") manifest
  IO.FS.writeFile (output / "src/main.rs") wrapper
  IO.println s!"prepared independent rank reference in {output}"
