import Cli
import Ix.Iroh.Connect

open Iroh.Connect

def runPutCmd (p : Cli.Parsed) : IO UInt32 := do
  let nodeId : String := p.flag! "nodeId" |>.as! String
  let addrs : Array String := p.flag! "addrs" |>.as! (Array String)
  let relayUrl : String := p.flag! "relayUrl" |>.as! String
  let filePath : String := p.flag! "filePath" |>.as! String
  putBytes nodeId addrs relayUrl filePath
  return 0

def put : Cli.Cmd := `[Cli|
  put VIA runPutCmd;
  "Put bytes onto Iroh storage server"

  FLAGS:
    nodeId  : String; "ID (public key) of the server node"
    addrs  : Array String; "Direct UDP addresses for the server node"
    relayUrl : String; "URL of the relay server at which the server node can also be reached"
    filePath : String; "Path to local file to parse into bytes and send to server node"
]

def runGetCmd (p : Cli.Parsed) : IO UInt32 := do
  let nodeId : String := p.flag! "nodeId" |>.as! String
  let addrs : Array String := p.flag! "addrs" |>.as! (Array String)
  let relayUrl : String := p.flag! "relayUrl" |>.as! String
  let hash : String := p.flag! "hash" |>.as! String
  getBytes nodeId addrs relayUrl hash
  return 0

def get : Cli.Cmd := `[Cli|
  get VIA runGetCmd;
  "Get bytes from Iroh storage server"

  FLAGS:
    nodeId  : String; "ID (public key) of the server node"
    addrs  : Array String; "Direct UDP addresses for the server node"
    relayUrl : String; "URL of the relay server at which the server node can also be reached"
    hash : String; "Hash of bytes to retrieve from server node"
]

-- TODO: Figure out how to inherit flags from the parent command, rather than re-declaring for each subcommand
def runConnect (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

-- TODO: Set RUST_LOG via `--verbose` flag
def connectCmd : Cli.Cmd := `[Cli|
  connect VIA runConnect;
  "Connect to an Iroh storage server"

  SUBCOMMANDS:
    put;
    get
]
