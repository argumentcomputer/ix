module
public import FormalAiurKeys
public import Ix.FormalProver
public import Ix.Aggr.Protocol

/-! The pinned identities and verifying keys of the certified formal Aiur
programs (`tools/formal-aiur.keys`, embedded as `Ix.FormalAiurKeys.text`).

Each pin names a program (`ixvm`, `verifier` or `aggregation`), its identity
(the content digest of its compiled artifact) and the BLAKE3 digest of its
verifying key under the default STARK parameters, which the file states.
Acceptance compares the keys it derives from the programs it loaded with
the pins (`check`, `pinnedAllowed`), so a proof is accepted only against the
pinned circuits, whichever artifact was selected. `formal-keys` derives the
file from the checkout's programs, and `tools/check-formal-keys.sh` fails
when it differs from the committed one. -/

public section
namespace Ix.Cli.FormalKeys

/-- One pinned program, its digests as lowercase hex. -/
structure Pin where
  program : String
  identity : String
  key : String
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
    match line.splitOn " " with
    | [program, identity, key] =>
      unless identity.length == 64 && key.length == 64 do
        throw s!"malformed pin for {program}"
      if pins.any (·.program == program) then throw s!"{program} is pinned twice"
      pins := pins.push { program, identity, key }
    | _ => throw s!"malformed pin line `{line}`"
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

/-- The identity blob aggregate proofs commit to, built from the pinned
IxVM and aggregation key digests and the derived entry indices. The derived
keys must be the pinned ones, and the blob they give must equal it. -/
def pinnedAllowed (ixvmKey : ByteArray) (ixvmIndex : Nat) (aggrKey : ByteArray)
    (aggrIndex : Nat) : IO ByteArray := do
  check "ixvm" ixvmKey
  check "aggregation" aggrKey
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
    "# artifact), BLAKE3 digest of its verifying key under the parameters below.",
    "# `ix verify` and the aggregate acceptance check require the keys they derive",
    "# to equal these, and aggregate proofs commit to the IxVM and aggregation keys.",
    "# A change means the compiled circuits changed: review it, then regenerate",
    "# with tools/check-formal-keys.sh --update in a commit of its own.",
    parametersLine]
  "\n".intercalate (header ++ (pins.map fun p => s!"{p.program} {p.identity} {p.key}").toList) ++ "\n"

end Ix.Cli.FormalKeys
