/-
  `ix store <subcommand>`: CLI interface to the principled `IxStore`
  content-addressed storage engine (`.ixs` "Ix Store" + `.ixsp` "Ix Store Pointer"):
  - `ix store stats`: Show hot cache, memory-mapped `.ixs`/`.ixsp`, and loose object statistics.
  - `ix store compact [--cold]`: Compact all 1-level sharded loose objects into a single
    memory-mapped `.ixs` + `.ixsp` pair (Warm 8B-aligned mmap or Cold `zstd`-compressed).
  - `ix store put <file>`: Content-address `<file>` (`blake3`) and store it.
  - `ix store get <address> [--out <file>] [--verify]`: Read an object from the store
    (with optional cryptographic verification).
  - `ix store ingest <ixe-file> [--cold]`: Hardlink `<ixe-file>` as `env-<root>.ixe`
    and pack its deduplicated constants and blobs into a Warm or Cold `.ixs` + `.ixsp` pair.
-/
module

public import Cli
public import Ix.Common
public import Ix.Store
public import Ix.Ixon

public section

open System (FilePath)

namespace Ix.Cli.StoreCmd

def runStoreStats (_p : Cli.Parsed) : IO UInt32 := do
  let root ← StoreIO.toIO Store.storeDir
  let st ← StoreIO.toIO Store.stats
  IO.println s!"Store root:      {root}"
  IO.println s!"Hot cache:       {st.hotEntries} objects"
  IO.println s!"Store packs:     {st.packCount} .ixs/.ixsp packs ({st.packedObjects} objects, {st.packedBytes} bytes)"
  IO.println s!"Loose objects:   {st.looseObjects} objects ({st.looseBytes} bytes)"
  return 0

def runStoreCompact (p : Cli.Parsed) : IO UInt32 := do
  let cold := p.hasFlag "cold"
  let tierName := if cold then "cold (zstd)" else "warm (mmap)"
  let (packed, unlinked) ← StoreIO.toIO (Store.compact cold)
  IO.println s!"Compacted {packed} loose object(s) (unlinked {unlinked}) into {tierName} .ixs + .ixsp"
  return 0

def runStorePut (p : Cli.Parsed) : IO UInt32 := do
  let pathStr := p.positionalArg! "file" |>.as! String
  let bytes ← IO.FS.readBinFile ⟨pathStr⟩
  let addr ← StoreIO.toIO (Store.write bytes)
  IO.println s!"{addr}"
  return 0

def runStoreGet (p : Cli.Parsed) : IO UInt32 := do
  let addrStr := p.positionalArg! "address" |>.as! String
  let some addr := Address.fromString addrStr
    | do
      p.printError s!"error: invalid 64-hex address '{addrStr}'"
      return 1
  let verify := p.hasFlag "verify"
  let bytes ←
    if verify then
      StoreIO.toIO (Store.readVerified addr)
    else
      StoreIO.toIO (Store.read addr)
  if let some outFlag := p.flag? "out" then
    let outPath := outFlag.as! String
    IO.FS.writeBinFile ⟨outPath⟩ bytes
    IO.println s!"Wrote {bytes.size} bytes to {outPath}"
  else
    IO.println s!"{addr} ({bytes.size} bytes)"
  return 0

def runStoreIngest (p : Cli.Parsed) : IO UInt32 := do
  let ixePath := p.positionalArg! "ixe" |>.as! String
  let cold := p.hasFlag "cold"
  let tierName := if cold then "cold (zstd)" else "warm (mmap)"
  let (envRoot, count) ← StoreIO.toIO (Store.ingestIxe ⟨ixePath⟩ cold)
  IO.println s!"Ingested '{ixePath}' into {tierName} .ixs + .ixsp (env-{envRoot}.ixe, {count} newly packed object(s))"
  return 0

def storeStatsCmd : Cli.Cmd := `[Cli|
  stats VIA runStoreStats;
  "Show store statistics (hot cache, .ixs/.ixsp files, and loose objects)"
]

def storeCompactCmd : Cli.Cmd := `[Cli|
  compact VIA runStoreCompact;
  "Compact all loose objects into a memory-mapped .ixs + .ixsp store pack"

  FLAGS:
    "cold"; "Compress entries with zstd (Cold tier) instead of uncompressed 8B-aligned Warm mmap"
]

def storePutCmd : Cli.Cmd := `[Cli|
  put VIA runStorePut;
  "Content-address a file with BLAKE3 and write it to the store"

  ARGS:
    file : String; "File path to store"
]

def storeGetCmd : Cli.Cmd := `[Cli|
  get VIA runStoreGet;
  "Read an object by 64-hex address from the store"

  FLAGS:
    o, out : String; "Write raw object bytes to this file path"
    "verify"; "Verify BLAKE3(bytes) == address on read"

  ARGS:
    address : String; "64-hex BLAKE3 content address"
]

def storeIngestCmd : Cli.Cmd := `[Cli|
  ingest VIA runStoreIngest;
  "Ingest an .ixe environment or .ixc catalog into a deduplicated .ixs + .ixsp store pack"

  FLAGS:
    "cold"; "Compress entries with zstd (Cold tier) instead of uncompressed 8B-aligned Warm mmap"

  ARGS:
    ixe : String; "Path to .ixe environment file or .ixc catalog directory"
]

def runStore (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.StoreCmd

open Ix.Cli.StoreCmd in
def storeCmd : Cli.Cmd := `[Cli|
  store VIA runStore;
  "Inspect, compact, and manage the content-addressed IxStore (.ixs/.ixsp + loose shards)"

  SUBCOMMANDS:
    storeStatsCmd;
    storeCompactCmd;
    storePutCmd;
    storeGetCmd;
    storeIngestCmd
]

end
