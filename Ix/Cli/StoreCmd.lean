module
public import Cli
public import Ix.Store

public section

/-- `ix store put <file>...`: copy files into the content-addressed store,
    each under the BLAKE3 hash of its bytes, and print `<address>  <file>`. -/
def runStorePut (p : Cli.Parsed) : IO UInt32 := do
  let files := (p.variableArgsAs! String).toList
  if files.isEmpty then
    p.printError "error: must specify at least one file"
    return 1
  for file in files do
    let addr ← StoreIO.toIO (Store.write (← IO.FS.readBinFile file))
    IO.println s!"{addr}  {file}"
  return 0

def storePutCmd : Cli.Cmd := `[Cli|
  put VIA runStorePut;
  "Copy files into the store (`~/.ix/store/`) under their BLAKE3 address"

  ARGS:
    ...files : String; "Files to add, e.g. downloaded `Ixon.Proof` wrappers"
]

def runStore (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

def storeCmd : Cli.Cmd := `[Cli|
  store VIA runStore;
  "Interact with the content-addressed store"

  SUBCOMMANDS:
    storePutCmd
]

end
