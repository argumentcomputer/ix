import Cli
import Ix.Iroh.Serve

open Iroh.Serve

-- Use the `RUST_LOG` env var to specify Iroh log level in Rust
def runServe (_p : Cli.Parsed) : IO UInt32 := do
  serve
  return 0

def serveCmd : Cli.Cmd := `[Cli|
  serve VIA runServe;
  "Start an Iroh byte storage server"
]
