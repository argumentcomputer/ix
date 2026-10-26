module

public import Cli
public import Ix.Cli.CheckLeanCmd
public import Ix.HostAdmission
public import Ix.Store

public section

namespace Ix.Cli.VerifyHostCmd

/-- A stored host statement is untrusted input. Both read paths authenticate
the requested address and replay admission of the complete supplied artifact. -/
def runVerifyHostCmd (p : Cli.Parsed) : IO UInt32 := do
  let some expected := p.positionalArg? "statement" | return 2
  let some address := Address.fromString (expected.as! String) | do
    IO.eprintln "[verify-host] statement address must be 64 hexadecimal characters"
    return 2
  let some path := p.positionalArg? "path" | return 2
  try
    let bytes ← match p.flag? "statement-file" with
      | some file => IO.FS.readBinFile (file.as! String)
      | none => StoreIO.toIO (Store.read address)
    let raw ← IO.FS.readBinFile (path.as! String)
    let parts ← match Ixon.deEnvVerifiedLazy raw with
      | .ok value => pure value
      | .error message => IO.eprintln s!"[verify-host] {message}"; return 3
    let job := IO.lazyPure fun _ =>
      Ix.HostAdmission.verifyAddressed address bytes parts.env CheckLeanCmd.artifactLimits
    Ix.Tc.setLeanThreadStackSize (USize.ofNat ({} : CheckLeanCmd.CheckCfg).stackBytes)
    let result ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) job))
    match result with
    | .error error => IO.eprintln s!"[verify-host] {error}"; return 3
    | .ok ⟨statement, checked⟩ =>
      let count := checked.run.prepared.records.length
      match statement.kind with
      | .logical => IO.println s!"[verify-host] {address}: logical admission replayed for all {count} records"
      | .tiered .. =>
        IO.println s!"[verify-host] {address}: admission replayed for all {count} records; {checked.run.typed.length} tier constants typed only"
      return 0
  catch error => IO.eprintln s!"[verify-host] {error}"; return 1

end Ix.Cli.VerifyHostCmd

open Ix.Cli.VerifyHostCmd in
def verifyHostCmd : Cli.Cmd := `[Cli|
  "verify-host" VIA runVerifyHostCmd;
  "Authenticate a host admission statement and replay complete artifact admission"
  FLAGS:
    "statement-file" : String; "Read expected statement bytes from this file instead of the store; its address is still checked"
  ARGS:
    statement : String; "Content address of the expected host admission statement"
    path : String; "Path to the complete .ixe artifact to admit again"
]

end
