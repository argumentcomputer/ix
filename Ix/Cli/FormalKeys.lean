module
public import FormalAiurKeys
public import Ix.FormalProver
public import Ix.Aggr.Protocol

/-! The pinned identities and verifying keys of the certified formal Aiur
programs (`tools/formal-aiur.keys`, embedded as `Ix.FormalAiurKeys.text`).

Each pin names a program (`ixvm`, `verifier` or `aggregation`), its identity
(the content digest of its compiled artifact) and the BLAKE3 digest of its
verifying key under the default STARK parameters, which the file states; the
IxVM and aggregation pins also name the entry function index their claims
carry. Acceptance compares the keys and entry indices it derives from the
programs it loaded with the pins (`check`, `checkEntry`, `pinnedAllowed`), so
a proof is accepted only against the pinned circuits and the pinned entry
functions, whichever artifact was selected. `formal-keys` derives the file
from the checkout's programs, and `Scripts/CheckFormalKeys.lean` fails when it
differs from the committed one. -/

public section
namespace Ix.Cli.FormalKeys

/-- One pinned program, its digests as lowercase hex, and the entry function
index its claims carry (pinned for the IxVM and aggregation programs). -/
structure Pin where
  program : String
  identity : String
  key : String
  entry : Option Nat := none
  deriving BEq, Inhabited

/-- The `parameters` line: the STARK parameters the keys were derived under. -/
def parametersLine (params : FormalProver.ProtocolParameters := {}) : String :=
  s!"parameters log_blowup {params.logBlowup} num_queries {params.numQueries}"

/-- The pins of a pin file. Comments start with `#`; the `parameters` line
must state the default STARK parameters, under which systems are prepared. -/
def parse (text : String) : Except String (Array Pin) := do
  let mut pins : Array Pin := #[]
  let mut parameters := false
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    if line.startsWith "parameters " then
      unless line == parametersLine do
        throw s!"the pins were derived under `{line}`, not `{parametersLine}`"
      parameters := true
      continue
    let (program, identity, key, entry) ← match line.splitOn " " with
      | [program, identity, key] => pure (program, identity, key, (none : Option Nat))
      | [program, identity, key, entry] =>
        match entry.toNat? with
        | some n => pure (program, identity, key, some n)
        | none => throw s!"malformed entry index for {program}"
      | _ => throw s!"malformed pin line `{line}`"
    unless identity.length == 64 && key.length == 64 do
      throw s!"malformed pin for {program}"
    if pins.any (·.program == program) then throw s!"{program} is pinned twice"
    pins := pins.push { program, identity, key, entry }
  unless parameters do throw "the pins do not state their STARK parameters"
  return pins

/-- The committed pin of `program`. -/
def pinned (program : String) : IO Pin := do
  let pins ← IO.ofExcept ((parse Ix.FormalAiurKeys.text).mapError
    fun e => s!"tools/formal-aiur.keys: {e}")
  let some pin := pins.find? (·.program == program)
    | throw (IO.userError s!"tools/formal-aiur.keys pins no {program} program")
  return pin

/-- The BLAKE3 digest of verifying-key bytes, as the pins state it. -/
def keyDigest (key : ByteArray) : String :=
  hexOfBytes (Address.blake3 key).hash

/-- Require that `key`, derived from the loaded `program`, is the pinned
verifying key. -/
def check (program : String) (key : ByteArray) : IO Unit := do
  let pin ← pinned program
  let derived := keyDigest key
  unless derived == pin.key do
    throw (IO.userError s!"the {program} verifying key is not the pinned one: \
      tools/formal-aiur.keys pins {pin.key}, the loaded program derives {derived}. \
      Proofs are accepted only against the pinned circuits.")

/-- `check` for the key of `system`. -/
def checkSystem (program : String) (system : FormalProver.System) : IO Unit := do
  check program (← system.key)

/-- Require that `index`, the entry function index derived from the loaded
`program`, is the pinned one. A claim names its entry by this index into the
artifact's function table, which the verifying key does not fix. -/
def checkEntry (program : String) (index : Nat) : IO Unit := do
  let pin ← pinned program
  let some entry := pin.entry
    | throw (IO.userError s!"tools/formal-aiur.keys pins no entry index for {program}")
  unless index == entry do
    throw (IO.userError s!"the {program} entry function index is not the pinned one: \
      tools/formal-aiur.keys pins {entry}, the loaded program derives {index}. \
      Proofs are accepted only for the pinned entry function.")

/-- The identity blob aggregate proofs commit to, built from the pinned
IxVM and aggregation key digests and entry indices. The derived keys and
entry indices must be the pinned ones, and the blob they give must equal it. -/
def pinnedAllowed (ixvmKey : ByteArray) (ixvmIndex : Nat) (aggrKey : ByteArray)
    (aggrIndex : Nat) : IO ByteArray := do
  check "ixvm" ixvmKey
  check "aggregation" aggrKey
  checkEntry "ixvm" ixvmIndex
  checkEntry "aggregation" aggrIndex
  let digest (program : String) : IO ByteArray := do
    let some address := Address.fromString (← pinned program).key
      | throw (IO.userError s!"malformed {program} key pin")
    return address.hash
  let allowed := Aggr.allowedOfDigests (← digest "ixvm") ixvmIndex (← digest "aggregation") aggrIndex
  unless allowed == Aggr.allowedBlob ixvmKey ixvmIndex aggrKey aggrIndex do
    throw (IO.userError "the aggregate identity blob differs from the pinned keys'")
  return allowed

/-- A pin file stating `pins`. -/
def render (pins : Array Pin) : String :=
  let header := [
    "# Pinned identities and verifying keys of the certified formal Aiur programs.",
    "#",
    "# Each line: program, program identity (the content digest of its compiled",
    "# artifact), BLAKE3 digest of its verifying key under the parameters below,",
    "# and, for the IxVM and aggregation programs, the entry function index.",
    "# `ix verify` and the aggregate acceptance check require the keys and entry",
    "# indices they derive to equal these, and aggregate proofs commit to the",
    "# IxVM and aggregation keys and entry indices.",
    "# A change means the compiled circuits changed: review it, then regenerate",
    "# with tools/check-formal-keys.sh --update in a commit of its own.",
    parametersLine]
  let line (p : Pin) : String :=
    match p.entry with
    | some entry => s!"{p.program} {p.identity} {p.key} {entry}"
    | none => s!"{p.program} {p.identity} {p.key}"
  "\n".intercalate (header ++ (pins.map line).toList) ++ "\n"

end Ix.Cli.FormalKeys
