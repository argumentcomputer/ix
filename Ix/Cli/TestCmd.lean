import Cli
import Blake3
import Ix.Address

def runTest (p : Cli.Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  IO.println s!"Input: {input}"
  let inputBA : ByteArray := input.toUTF8
  IO.println s!"Input UTF8: {byteArrayToHex inputBA}"
  let hashBA : ByteArray := (Blake3.hash inputBA).val
  let hashHex : String := byteArrayToHex hashBA
  IO.println s!"Hash (hex): {hashHex}"
  return 0

def testCmd : Cli.Cmd := `[Cli|
  test VIA runTest;
  "run a test"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
    input  : String; "Source file input"
]
