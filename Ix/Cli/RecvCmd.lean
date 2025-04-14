import Cli
import Ix.Iroh.Transfer

open Iroh.Transfer

def runRecv (p : Cli.Parsed) : IO UInt32 := do
  let ticket   : String       := p.positionalArg! "ticket" |>.as! String
  let limit : Nat := (p.flag? "limit").map (·.as! Nat) |>.getD 1024
  IO.println <| s!"Retrieving bytes for ticket: {ticket} with limit {limit}"
  let bytes ← recvBytes ticket limit.toUSize
  IO.println <| "Received bytes: " ++ (String.fromUTF8? bytes |>.get!)
  return 0

def recvCmd : Cli.Cmd := `[Cli|
  recv VIA runRecv;
  "Receive string associated with given ticket from Iroh network"

  FLAGS:
    limit : Nat; "Buffer capacity for received bytes, default 1024"

  ARGS:
    ticket  : String; "Ticket to request"
]
