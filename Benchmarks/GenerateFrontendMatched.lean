import Benchmarks.FrontendWire
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Ix.Frontend Ix.Frontend.Elab FrontendWire
-- Run with: lake env lean Benchmarks/GenerateFrontendMatched.lean
-- Then: python3 Benchmarks/GenerateFrontendMatched.py
#eval show IO Unit from do
  let env ← IO.ofExcept (FrontendRepresentative.elaborate FrontendRepresentative.sourceText)
  let pre ← IO.ofExcept (elabSource "")
  let dir := ".lake/frontend-benchmark"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/matched-expected.json") ((json (ofEnv env)).compress)
  IO.FS.writeFile (dir ++ "/matched-prelude.json") ((json (ofEnv pre)).compress)
  let digest := Address.blake3Pure FrontendRepresentative.sourceText.toUTF8
  IO.FS.writeFile (dir ++ "/matched-digest.json") (Lean.toJson (digest.hash.data.map UInt8.toNat)).compress
  IO.println s!"Exported {pre.constOrder.length} prelude and {env.constOrder.length} total constants"
