module

public import Cli
public import Ix.Cli.CheckLeanCmd
public import Ix.Cli.KernelLimits
public import Ix.HostAdmission
public import Ix.Store

public section

namespace Ix.Cli.VerifyHostCmd

open Ix.Cli.KernelLimits in
/-- The replay, on the thread `runVerifyHostCmd` sized for it: the artifact
loaded (every record scanned before it is decoded) and admitted again under the
settings. -/
def replay (address : Address) (bytes raw : ByteArray) (settings : Ix.Kernel.Host.Resolved) :
    IO UInt32 := do
  let decline (r : Ix.Kernel.Admission.Resource) : IO UInt32 := do
    IO.eprintln s!"[verify-host] {Ix.Kernel.Host.declineMessage settings r}"
    return Ix.Kernel.Host.exitDeclined
  let parts ← match Ixon.deEnvVerifiedLazy raw settings.limits.maxDepth with
    | .ok value => pure value
    | .error message =>
      if let some r := loaderLimitOf message then return (← decline r)
      IO.eprintln s!"[verify-host] {message}"; return 3
  match ← IO.lazyPure fun _ => Ix.HostAdmission.verifyAddressed address bytes parts.env settings.limits with
  | .error error =>
    if let some r := hostLimitOf error then return (← decline r)
    IO.eprintln s!"[verify-host] {error}"; return 3
  | .ok ⟨statement, checked⟩ =>
    let count := checked.run.prepared.records.length
    match statement.kind with
    | .logical => IO.println s!"[verify-host] {address}: logical admission replayed for all {count} records"
    | .tiered .. =>
      IO.println s!"[verify-host] {address}: admission replayed for all {count} records; {checked.run.typed.length} tier constants typed only"
    return 0

/-- A stored host statement is untrusted input. Both read paths authenticate
the requested address and replay admission of the complete supplied artifact,
under the kernel's limits (`--max-*`, `--workers`, `IX_KERNEL_*`; `ix check-lean`'s
defaults), on a thread sized from them. A host statement does not record the
limits it was issued under: a replay under smaller ones may decline (exit 6)
what the issuing run accepted. -/
def runVerifyHostCmd (p : Cli.Parsed) : IO UInt32 := do
  let some expected := p.positionalArg? "statement" | return 2
  let some address := Address.fromString (expected.as! String) | do
    IO.eprintln "[verify-host] statement address must be 64 hexadecimal characters"
    return 2
  let some path := p.positionalArg? "path" | return 2
  let settings ← match ← Ix.Cli.KernelLimits.resolveCli CheckLeanCmd.artifactLimits p with
    | .ok s => pure s
    | .error e => IO.eprintln s!"[verify-host] {e}"; return 2
  try
    if let some h := Ix.Kernel.Host.header settings then IO.eprintln s!"[verify-host] {h}"
    if let some why ← Ix.Cli.KernelLimits.prepareThreads settings then
      IO.eprintln s!"[verify-host] {why}"; return 2
    let bytes ← match p.flag? "statement-file" with
      | some file => IO.FS.readBinFile (file.as! String)
      | none => StoreIO.toIO (Store.read address)
    let raw ← IO.FS.readBinFile (path.as! String)
    Ix.Cli.KernelLimits.onKernelThread (replay address bytes raw settings)
  catch error => IO.eprintln s!"[verify-host] {error}"; return 1

end Ix.Cli.VerifyHostCmd

open Ix.Cli.VerifyHostCmd in
def verifyHostCmd : Cli.Cmd := `[Cli|
  "verify-host" VIA runVerifyHostCmd;
  "Authenticate a host admission statement and replay complete artifact admission. Exit 0: replayed; 3: the statement or the artifact was refused; 6: declined by a kernel limit, which the message names with the flag and variable that raise it; 2: usage, including a malformed limit and a run whose threads cannot fit the address-space limit; 1: infrastructure"
  FLAGS:
    "statement-file" : String; "Read expected statement bytes from this file instead of the store; its address is still checked"
    workers : String; "Bound on the tasks of the entry's phase B (else IX_KERNEL_WORKERS; default unbounded)"
    "max-records" : String; "Kernel limit: records in the artifact (else IX_KERNEL_MAX_RECORDS; default 4194304)"
    "max-blobs" : String; "Kernel limit: blobs in the artifact (else IX_KERNEL_MAX_BLOBS; default 4194304)"
    "max-total-bytes" : String; "Kernel limit: payload bytes of records and blobs (else IX_KERNEL_MAX_TOTAL_BYTES; default 17179869184)"
    "max-record-bytes" : String; "Kernel limit: one record's payload bytes (else IX_KERNEL_MAX_RECORD_BYTES; default 268435456)"
    "max-record-univ-nodes" : String; "Kernel limit: one record's universe nodes, expanded (else IX_KERNEL_MAX_RECORD_UNIV_NODES; default 67108864)"
    "max-depth" : String; "Kernel limit: how deep a record nests, as stored and with shares expanded (else IX_KERNEL_MAX_DEPTH; default 16384); the threads get 16 KiB of stack per level, at least 256 MiB"
  ARGS:
    statement : String; "Content address of the expected host admission statement"
    path : String; "Path to the complete .ixe artifact to admit again"
]

end
