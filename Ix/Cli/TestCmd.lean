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
--  let input   : String       := p.positionalArg! "input" |>.as! String
--  IO.println s!"Input: {input}"
--  let inputBA := input.toUTF8
--  IO.println s!"Input UTF8: {hexOfBytes inputBA}"
--  let const : Ixon.Const := .defn
--    { lvls := 0, type := .strl "BAD", value := .strl input, part := .true}
--  IO.println s!"Const: {repr const}"
--  let bytes := Ixon.Serialize.put const
--  IO.println s!"Bytes: {hexOfBytes bytes}"
--  let addr := Address.blake3 bytes
--  IO.println s!"Address: {hexOfBytes addr.hash}"
--  let home ← StoreIO.toIO getHomeDir
--  IO.println s!"HOME at {home}"
--  let store ← StoreIO.toIO storeDir
--  IO.println s!"Store at {store}"
--  StoreIO.toIO ensureStoreDir
--  IO.println s!"write entry at {store / (hexOfBytes addr.hash)}"
--  let _ <- StoreIO.toIO (writeConst const)
--  IO.println s!"read entry at {store / (hexOfBytes addr.hash)}"
--  let const' ← StoreIO.toIO (readConst addr)
--  IO.println s!"Const': {repr const'}"
--  IO.println s!"matching {const == const'}"
  return 0

def testCmd : Cli.Cmd := `[Cli|
  test VIA runTest;
  "run a test"

  FLAGS:
    e, "example"   : String; "Example flag"

  ARGS:
    input  : String; "Source file input"
]
