import Cli
import Ix.Cronos
import Ix.Common
import Ix.CompileM
import Ix.Store
import Ix.Address
import Lean

-- ix store <lean file>
-- ix store get <address>
def runStore (p : Cli.Parsed) : IO UInt32 := do
  let source : String       := p.positionalArg! "source" |>.as! String
  let mut cronos ← Cronos.new.clock "Lean-frontend"
  Lean.setLibsPaths source
  --StoreIO.toIO ensureStoreDir
  let path := ⟨source⟩
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile path) path
  cronos ← cronos.clock "Lean-frontend"
  -- Start content-addressing
  cronos ← cronos.clock "content-address"
  let stt ← Ix.Compile.compileEnvIO leanEnv
  stt.names.forM fun name (const, meta) => do
     IO.println <| s!"{name}:"
     IO.println <| s!"  #{const}"
     --IO.println <| s!"  {repr <| stt.store.find! const}"
     --IO.println <| s!"  {hexOfBytes (Ixon.Serialize.put (stt.store.find! const))}"
     IO.println <| s!"  #{meta}"
     --IO.println <| s!"  {repr <| stt.store.find! meta}"
     --IO.println <| s!"  {hexOfBytes (Ixon.Serialize.put (stt.store.find! meta))}"
  --stt.store.forM fun adr const => do
  --   IO.println <| s!"adr' {adr}"
  --   IO.println <| s!"const {repr const}"
  --   let adr' <- StoreIO.toIO (writeConst const)
  --   IO.println <| s!"adr' {adr}"
  --   let const' <- StoreIO.toIO (readConst adr')
  --   IO.println <| s!"const' {repr const'}"
  cronos ← cronos.clock "content-address"
  IO.println cronos.summary
  return 0

def runGet (p : Cli.Parsed) : IO UInt32 := do
  let input : String       := p.positionalArg! "address" |>.as! String
  let address : Address <- IO.ofExcept $
    match Address.fromString input with
    | .some a => .ok a
    | .none => .error "bad address"
  let const <- StoreIO.toIO (Store.readConst address)
  IO.println <| s!"{repr const}"
  return 0

def storeGetCmd : Cli.Cmd := `[Cli|
  get VIA runGet;
  "print a store entry"
  ARGS:
    address  : String; "Ix address"
]

def storeCmd : Cli.Cmd := `[Cli|
  store VIA runStore;
  "Interact with the Ix store"

  FLAGS:
    cron, "cronos"   : String; "enable Cronos timings"

  ARGS:
    source : String; "Source file input"

  SUBCOMMANDS:
    storeGetCmd
]

