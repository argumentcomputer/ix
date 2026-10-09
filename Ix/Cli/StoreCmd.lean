module
public import Cli
public import Ix.Store
public import Ix.Claim

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

/-- Describe a store object: the address it was requested by, its size, and,
    when it decodes as an `Ixon.Proof` or a bare claim, the claim. The first
    byte's flag distinguishes the two, so only the matching decoder runs. -/
private def describe (addr : Address) (bytes : ByteArray) : String :=
  let header := s!"address: {addr}\nsize: {bytes.size} bytes"
  match Ixon.Proof.de bytes with
  | .ok wrapper =>
    s!"{header}\nkind: Ixon.Proof\nclaim: {wrapper.claim}\n\
      claim digest: {Ix.Claim.commit wrapper.claim}\nproof bytes: {wrapper.proof.size}"
  | .error _ => match Ix.Claim.de bytes with
    | .ok claim =>
      s!"{header}\nkind: claim\nclaim: {claim}\nclaim digest: {Ix.Claim.commit claim}"
    | .error _ =>
      let first := bytes[0]?.map (fun b => s!", first byte 0x{hexOfBytes ⟨#[b]⟩}") |>.getD ""
      s!"{header}\nkind: not a proof or claim{first}"

/-- `ix store get <object>`: check that a store object's bytes hash to its
    address, then write them unchanged to a file or stdout, or with `--show`
    describe it. A file path is accepted in place
    of an address, which lets `--show` describe downloaded objects. -/
def runStoreGet (p : Cli.Parsed) : IO UInt32 := do
  let arg := p.positionalArg! "object" |>.as! String
  let (addr, bytes) ← match Address.fromString arg with
    | some addr =>
      let path ← StoreIO.toIO (Store.storePath addr)
      if !(← path.pathExists) then
        p.printError s!"error: {addr} is not in the store"
        return 1
      pure (addr, ← IO.FS.readBinFile path)
    | none =>
      let path : System.FilePath := arg
      if !(← path.pathExists) || (← path.isDir) then
        p.printError s!"error: {arg} is neither a 64-char hex address nor a file"
        return 1
      let bytes ← IO.FS.readBinFile path
      pure (Address.blake3 bytes, bytes)
  let actual := Address.blake3 bytes
  if actual != addr then
    IO.eprintln s!"error: store object {addr} is corrupted: its bytes hash to {actual}"
    return 1
  if let some out := p.flag? "output" then
    IO.FS.writeBinFile (out.as! String) bytes
  if p.hasFlag "show" then
    IO.println (describe addr bytes)
  else if !p.hasFlag "output" then
    let stdout ← IO.getStdout
    stdout.write bytes
    stdout.flush
  return 0

def storeGetCmd : Cli.Cmd := `[Cli|
  get VIA runStoreGet;
  "Write a store object's bytes to stdout or a file, or describe it with --show"

  FLAGS:
    o, output : String; "Write the bytes to this file instead of stdout"
    "show";             "Print the object's address, size and, for proofs and claims, the claim"

  ARGS:
    object : String; "32-byte hex address in `~/.ix/store/`, or a file path"
]

def runStore (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

def storeCmd : Cli.Cmd := `[Cli|
  store VIA runStore;
  "Interact with the content-addressed store"

  SUBCOMMANDS:
    storeGetCmd;
    storePutCmd
]

end
