import Cli
import Blake3
import Ix.Address
import Ix.Store
import Ix.Ixon.Expr
import Ix.Ixon.Const
import Ix.Ixon.Serialize
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError

def runTest (p : Cli.Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  IO.println s!"Input: {input}"
  let inputBA := input.toUTF8
  IO.println s!"Input UTF8: {byteArrayToHex inputBA}"
  let const : Ixon.Const := .defn
    { lvls := 0, type := .strl "BAD", value := .strl input, part := .true}
  IO.println s!"Const: {repr const}"
  let bytes := Ixon.Serialize.put const
  IO.println s!"Bytes: {byteArrayToHex bytes}"
  let addr := Address.blake3 bytes
  IO.println s!"Address: {byteArrayToHex addr.hash}"
  let home ← EIO.toIO storeErrorToIOError getHomeDir
  IO.println s!"HOME at {home}"
  let store ← EIO.toIO storeErrorToIOError storeDir
  IO.println s!"Store at {store}"
  EIO.toIO storeErrorToIOError ensureStoreDir
  IO.println s!"write entry at {store / (byteArrayToHex addr.hash)}"
  EIO.toIO storeErrorToIOError (writeConst const)
  IO.println s!"read entry at {store / (byteArrayToHex addr.hash)}"
  let const' ← EIO.toIO storeErrorToIOError (readConst addr)
  IO.println s!"Const': {repr const'}"
  IO.println s!"matching {const == const'}"
  return 0

def testCmd : Cli.Cmd := `[Cli|
  test VIA runTest;
  "run a test"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
    input  : String; "Source file input"
]
