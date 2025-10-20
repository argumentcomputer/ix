import Cli
import Ix.Iroh.Serve

open Iroh.Serve

def runServe (_p : Cli.Parsed) : IO UInt32 := do
  serve
  return 0

def serveCmd : Cli.Cmd := `[Cli|
  serve VIA runServe;
  "Start an Iroh byte storage server"
]
