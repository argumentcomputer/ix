import Cli
import Ix.Iroh.Connect

open Iroh.Connect

-- Use the `RUST_LOG` env var to specify Iroh log level in Rust
def runPutCmd (p : Cli.Parsed) : IO UInt32 := do
  if !p.hasFlag "node-id" || !p.hasFlag "addrs" || !p.hasFlag "relay-url" then
    p.printError "error: must specify --node-id, --addrs, and --relay-url"
    return 1
  let nodeId : String := p.flag! "node-id" |>.as! String
  let addrs : Array String := p.flag! "addrs" |>.as! (Array String)
  let relayUrl : String := p.flag! "relay-url" |>.as! String
  let input ← do
    match (p.flag? "input", p.flag? "file") with
    | (.some input, .none) => pure <| input.as! String
    | (.none, .some file) => IO.FS.readFile <| file.as! String
    | _ => throw <| IO.userError "must specify --input or --file but not both"

  putBytes nodeId addrs relayUrl input
  return 0

def put : Cli.Cmd := `[Cli|
  put VIA runPutCmd;
  "Put bytes onto Iroh storage server"

  FLAGS:
    "node-id"  : String; "ID (public key) of the server node"
    addrs  : Array String; "Direct UDP addresses for the server node"
    "relay-url" : String; "URL of the relay server at which the server node can also be reached"
    i, input : String; "Input to send send as bytes to server node"
    f, file : String; "Path to local file to parse into bytes and send to server node"
]

def runGetCmd (p : Cli.Parsed) : IO UInt32 := do
  if !p.hasFlag "node-id" || !p.hasFlag "addrs" || !p.hasFlag "relay-url" then
    p.printError "error: must specify --node-id, --addrs, and --relay-url"
    return 1
  let nodeId : String := p.flag! "node-id" |>.as! String
  let addrs : Array String := p.flag! "addrs" |>.as! (Array String)
  let relayUrl : String := p.flag! "relay-url" |>.as! String
  let writeToDisk := p.hasFlag "write-to-disk"
  let hash : String := p.positionalArg! "hash" |>.as! String
  getBytes nodeId addrs relayUrl hash writeToDisk
  return 0

def get : Cli.Cmd := `[Cli|
  get VIA runGetCmd;
  "Get bytes from Iroh storage server"

  FLAGS:
    "node-id"  : String; "ID (public key) of the server node"
    addrs  : Array String; "Direct UDP addresses for the server node"
    "relay-url" : String; "URL of the relay server at which the server node can also be reached"
    w, "write-to-disk"; "Optionally write the retrieved bytes to disk"

  ARGS:
    hash : String; "Hash of bytes to retrieve from server node"
]

-- TODO: Figure out how to inherit flags from the parent command, rather than re-declaring for each subcommand
def runConnect (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

def connectCmd : Cli.Cmd := `[Cli|
  connect VIA runConnect;
  "Connect to an Iroh storage server"

  SUBCOMMANDS:
    put;
    get
]
