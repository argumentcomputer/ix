module
public import Aiur.Ixon
public import Ix.Aiur.Protocol

/-! Invocations and case files of the formal Aiur hosts, in Ixon.

An invocation names an entry point with its public arguments and its input
streams; it is the input of every Rust host (`ixvm-proof`, `stark-verifier`,
`ix-prover`) and of the compression FFI. A case file holds labelled
invocations with their expected verdicts, for `ixvm-proof test` and
`stark-verifier cases`. The grammar is documented with its Rust reader,
`aiur::artifact`:

```text
invocation = "IXAIURI\0" nat(1) string(entry) nats(args)
             list(nat(channel) nats(key) nats(values))
cases      = "IXAIURT\0" nat(1) (1 case)* 0
case       = string(label) bool(accept) option(string(rejects_with))
             option(string(exercises)) invocation
```

The writers here are total: field elements and counts always fit TagN. A case
file is written a case at a time (`casesHeader`, `Case.encode`,
`casesTrailer`), so a suite never holds more than one witness. -/

public section
namespace Ix.AiurInvocation

def invocationMagic : ByteArray := "IXAIURI\x00".toUTF8
def casesMagic : ByteArray := "IXAIURT\x00".toUTF8
def version : Nat := 1

/-! ## Writing -/

@[inline] private def pushNat (out : ByteArray) (n : Nat) : ByteArray :=
  Aiur.Ixon.tagN0 out n.toUInt64

private def pushBytes (out bytes : ByteArray) : ByteArray :=
  (pushNat out bytes.size).append bytes

private def pushStr (out : ByteArray) (s : String) : ByteArray := pushBytes out s.toUTF8

private def pushGs (out : ByteArray) (xs : Array Aiur.G) : ByteArray :=
  xs.foldl (fun out x => Aiur.Ixon.tagN0 out x.val) (pushNat out xs.size)

private def pushNats (out : ByteArray) (xs : Array Nat) : ByteArray :=
  xs.foldl pushNat (pushNat out xs.size)

private def pushOption (out : ByteArray) (s : Option String) : ByteArray :=
  match s with
  | none => out.push 0
  | some s => pushStr (out.push 1) s

private def header (magic : ByteArray) : ByteArray := pushNat magic version

/-- The invocation of `entry` with public arguments `input` and the streams of
`buffer`: one per key, each its channel, key and the values stored under it. -/
def ofBuffer (input : Array Aiur.G) (buffer : Aiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : ByteArray := Id.run do
  let streams := buffer.map.toArray
  let mut out := pushGs (pushStr (header invocationMagic) entry) input
  out := pushNat out streams.size
  for ((channel, key), info) in streams do
    out := Aiur.Ixon.tagN0 out channel.val
    out := pushGs out key
    out := pushGs out ((buffer.data.getD channel #[]).extract info.idx (info.idx + info.len))
  return out

/-- One stream of a decoded invocation. -/
structure Stream where
  channel : Nat
  key : Array Nat
  values : Array Nat
  deriving BEq, Repr, Inhabited

/-- A decoded invocation, for the drivers that inspect or alter one. -/
structure Invocation where
  entry : String
  args : Array Nat
  streams : Array Stream := #[]
  deriving BEq, Repr, Inhabited

/-- The invocation's bytes. Values must be below `2^64`. -/
def Invocation.encode (i : Invocation) : Except String ByteArray := do
  let values := i.args ++ i.streams.foldl (fun acc s => acc ++ #[s.channel] ++ s.key ++ s.values) #[]
  unless values.all (· < 2 ^ 64) do throw "invocation value exceeds UInt64"
  let mut out := pushNats (pushStr (header invocationMagic) i.entry) i.args
  out := pushNat out i.streams.size
  for s in i.streams do
    out := pushNats (pushNats (pushNat out s.channel) s.key) s.values
  return out

/-- The header of a case file. -/
def casesHeader : ByteArray := header casesMagic

/-- A case: a label, the verdict it must get, for a rejection text the error
must contain, for an acceptance a function the execution must call, and the
invocation's bytes (`ofBuffer`, `Invocation.encode`). -/
structure Case where
  label : String
  accept : Bool
  rejectsWith : Option String := none
  exercises : Option String := none
  invocation : ByteArray

/-- A case as it follows the header of a case file. -/
def Case.encode (c : Case) : ByteArray :=
  let out := pushStr (ByteArray.empty.push 1) c.label
  let out := pushOption (pushOption (out.push (if c.accept then 1 else 0)) c.rejectsWith) c.exercises
  out.append c.invocation

/-- The byte that ends a case file. -/
def casesTrailer : ByteArray := ByteArray.empty.push 0

/-- A complete case file. -/
def encodeCases (cases : Array Case) : ByteArray :=
  (cases.foldl (fun out c => out.append c.encode) casesHeader).append casesTrailer

/-! ## Reading -/

open Aiur.Ixon in
private def getHeader (magic : ByteArray) (what : String) : GetM Unit := do
  unless (← getRaw magic.size).data == magic.data do fail s!"not {what}"
  let v ← getNat
  unless v == version do fail s!"unsupported {what} version {v}"

open Aiur.Ixon in
private def getNats : GetM (Array Nat) := getArray getNat

open Aiur.Ixon in
def getInvocation : GetM Invocation := do
  getHeader invocationMagic "an invocation"
  let entry ← getString
  let args ← getNats
  let streams ← getArray do
    let channel ← getNat
    let key ← getNats
    let values ← getNats
    return ({ channel, key, values } : Stream)
  return { entry, args, streams }

def Invocation.decode (bytes : ByteArray) : Except String Invocation :=
  Aiur.Ixon.decode getInvocation bytes

/-- A decoded case: its invocation both decoded and as its bytes. -/
structure DecodedCase where
  label : String
  accept : Bool
  rejectsWith : Option String
  exercises : Option String
  invocation : Invocation
  bytes : ByteArray

open Aiur.Ixon in
def decodeCases (bytes : ByteArray) : Except String (Array DecodedCase) :=
  Aiur.Ixon.decode (do
    getHeader casesMagic "a case file"
    let mut cases := #[]
    while (← getTag "case continuation" 2) == 1 do
      let label ← getString
      let accept ← getBool
      let rejectsWith ← getOption getString
      let exercises ← getOption getString
      let start := (← get).pos
      let invocation ← getInvocation
      let stop := (← get).pos
      let raw := bytes.extract start stop
      let decoded : DecodedCase := {
        label := label, accept := accept, rejectsWith := rejectsWith,
        exercises := exercises, invocation := invocation, bytes := raw }
      cases := cases.push decoded
    return cases) bytes

end Ix.AiurInvocation
end
