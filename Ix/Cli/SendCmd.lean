import Cli
import Ix.Iroh.Transfer

open Iroh.Transfer

def runSend (p : Cli.Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  IO.println <| "Sending bytes of input: " ++ input
  sendBytes input.toUTF8
  return 0

def sendCmd : Cli.Cmd := `[Cli|
  send VIA runSend;
  "Sends given string to peers using Iroh"

  ARGS:
    input  : String; "String input"
]
