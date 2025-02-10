import Cli
import Blake3

/-- Convert a byte (UInt8) to a two‐digit hex string. -/
def byteToHex (b : UInt8) : String :=
  let hexDigits := 
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let hi := hexDigits.get! (UInt8.toNat (b >>> 4))
  let lo := hexDigits.get! (UInt8.toNat (b &&& 0xF))
  String.mk [hi, lo]

/-- Convert a ByteArray to a hexadecimal string. -/
def byteArrayToHex (ba : ByteArray) : String :=
  (ba.toList.map byteToHex).foldl (· ++ ·) ""

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
