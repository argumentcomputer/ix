/-
  `ix decompile <path.ixe>`: decompile a serialized `.ixe` environment back to
  Lean constants — the inverse of `ix compile`. This is the decompile
  benchmark's measured tool (env-keyed row, mirroring `ix compile --json`).

  With `--json` the run records one env-keyed results row (decompile-time,
  file-size, constants, throughput, peak-rss). A malformed decompile is a hard
  error (nonzero exit → red cell). Deeper compile→decompile roundtrip fidelity
  is gated by the canonical roundtrip checks (`ix validate` / the roundtrip
  tests), which need the original Lean env a `.ixe` can't supply — so this
  performance tool does not reproduce them.
-/
module
public import Cli
public import Ix.Common
public import Ix.TracingTexray
public import Ix.Benchmark.Results

public section

open System (FilePath)

namespace Ix.Cli.DecompileCmd

/-- Decompile a `.ixe` from disk, returning the decompiled constant
    count. A malformed decompile throws (hard error). Implemented in
    `crates/ffi/src/compile.rs::rs_decompile_env`. -/
@[extern "rs_decompile_env"]
opaque rsDecompileEnvFFI : @& String → IO Nat

def runDecompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return Ix.Benchmark.Results.exitUsage
  let envPath := pathArg.as! String

  -- Window the tree-RSS sampler around the decompile, mirroring
  -- `ix compile --json` so the two rows share measurement
  -- infrastructure and peak-rss semantics.
  let benched := (p.flag? "json").isSome
  if benched then
    TracingTexray.startSampler
    TracingTexray.resetPeakTreeRss

  IO.println s!"Decompiling {envPath}"
  let start ← IO.monoMsNow
  let constants ← rsDecompileEnvFFI envPath
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"[decompile] {constants} constants in {elapsed.formatMs}"

  if let some flag := p.flag? "json" then
    let key := (p.flag? "json-name").map (·.as! String)
      |>.getD ((FilePath.mk envPath).fileStem.getD "env")
    let secs := elapsed.toFloat / 1000.0
    let tput := if elapsed > 0
      then constants.toFloat * 1000.0 / elapsed.toFloat else 0.0
    let peakRss ← TracingTexray.peakTreeRssBytes
    -- `file-size` is the INPUT `.ixe` the decompile consumed (the byte
    -- counterpart to compile's output `.ixe`).
    let size := (← (FilePath.mk envPath).metadata).byteSize.toNat
    Ix.Benchmark.Results.writeRow (flag.as! String) key "ok"
      [ ("decompile-time", Ix.Benchmark.Results.jsonRound 3 secs)
      , ("file-size", Lean.toJson size)
      , ("constants", Lean.toJson constants)
      , ("throughput", Ix.Benchmark.Results.jsonRound 2 tput)
      , ("peak-rss", Lean.toJson peakRss) ]

  return 0

end Ix.Cli.DecompileCmd

open Ix.Cli.DecompileCmd in
def decompileCmd : Cli.Cmd := `[Cli|
  decompile VIA runDecompileCmd;
  "Decompile a serialized `.ixe` env back to Lean constants (inverse of `ix compile`). Measures the decompile pass; a malformed decompile exits nonzero. Deep roundtrip fidelity is gated by `ix validate` / the roundtrip tests."

  FLAGS:
    json        : String; "Write the decompile's benchmark results row (decompile-time, file-size, constants, throughput, peak-rss) to this path, merging into any existing rows object."
    "json-name" : String; "Row key for the --json row (default: the input `.ixe` file's stem)."

  ARGS:
    path : String; "Path to the serialized `.ixe` environment to decompile."
]
