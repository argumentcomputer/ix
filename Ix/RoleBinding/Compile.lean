module

public import Ix.RoleBinding.Generate
public import Ix.CompileResource
public import Ix.EnvScope
public import Ix.Meta
public import IxC.Kernel.PinGen.Certs

/-! Artifact-specific support and evidence for the production compiler.

The original request is compiled separately and retains its accounting and
failure policy. Support and certificate inputs use the same raw backend;
they never recursively enter this finalizer. Emission supplies untrusted
binding/evidence bytes. Certified consumers must check the resulting artifact.
-/

@[expose] public section

namespace Ix.RoleBinding.Compile

open Ix.Kernel (Role)

/-- A raw backend must report any incomplete internal compilation as an error.
The finalizer also checks every requested support/certificate publication. -/
abbrev Backend := Lean.Environment → Ix.Compile.CompileInput → IO Ixon.Env

def leanBackend (workers : Nat) (opts : Ix.CompileM.DriverOptions) : Backend := fun _ input => do
  let out ← IO.ofExcept (← Ix.CompileM.compileLeanInputValidated input (numWorkers := workers) (opts := opts))
  unless out.cenv.ungrounded.isEmpty && out.ungroundedCount == 0 do
    throw (IO.userError "artifact support: incomplete Lean compilation")
  return out.env

def rustBackend : Backend := fun _ input => IO.FS.withTempDir fun dir => do
  let path := dir / "support.ixe"
  let constants ← IO.ofExcept input.prepare
  let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString false
  unless status.ungrounded.isEmpty do
    throw (IO.userError "artifact support: incomplete Rust compilation")
  IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))

def roleName (role : Role) : Lean.Name :=
  Ix.RoleEvidence.toLeanName (Ix.Kernel.roleKey (md := .source) role)

def publishedRoles (artifact : Ixon.Env) : List Role :=
  let found : Std.HashSet Role := artifact.named.fold (init := {}) fun roles name _ =>
    match Role.ofLeanName? (Ix.LeanIngress.ingressName name) with
    | some role => roles.insert role
    | none => roles
  Role.all.filter found.contains

def closeRoles (roles : List Role) : List Role :=
  Role.all.filter (roles ++ roles.flatMap Role.block ++ roles.flatMap Role.deps).contains

/-- Explicitly check mandatory sources before the selected-closure collector,
which intentionally ignores unavailable seed names in other callers. -/
def supportInput (source : Lean.Environment) (artifact : Ixon.Env) :
    Except String (List Role × Ix.Compile.CompileInput) := do
  let mut required := closeRoles (Ix.Kernel.preludeShape.flatten ++ publishedRoles artifact)
  for _ in [:Role.all.length + 1] do
    let roots := required.map roleName
    for name in roots do
      unless source.contains name do throw s!"artifact support: source has no {name}"
    let constants := Ix.EnvScope.collectSelectedDeps source roots
    let found := constants.filterMap fun (name, _) => Role.ofLeanName? (Ix.Kernel.Name.ofLeanName name)
    let next := closeRoles (required ++ found)
    if next == required then
      let input ← (Ix.Compile.compileInputFromEnv source constants).mapError toString
      return (required, input)
    unless required.length < next.length do
      throw "artifact support: role closure failed to grow"
    required := next
  throw "artifact support: role closure exceeded its finite domain"

/-- Merge authenticated support without replacing any original publication or
its metadata. The support is authenticated here; the original is authenticated
with the merged artifact (`finalize`). Structural names, rather than stored name
hashes, decide overlap.
A reducibility hint the support carries at an address the original already
hints is refused when merging it would change the original's hint (the reader
checks a definition at the hint stored at its address, so a changed hint would
change how the original's definitions are checked); otherwise the original's
hint is kept. -/
def mergeSupport (limits : Ix.Kernel.Admission.Limits) (original support : Ixon.Env) :
    Except String Ixon.Env := do
  let _ ← recordStore limits support
  unless support.main.isNone && support.assumptions.isEmpty do
    throw "artifact support: internal compilation produced a bundle"
  let originalNames ← sourceAddresses original
  let _ ← sourceAddresses support
  let mut out := original
  for (address, value) in support.consts.toList do
    if let some old := out.consts[address]? then
      unless old.rawBytes == value.rawBytes do throw s!"artifact support: conflicting record {address}"
    else out := { out with consts := out.consts.insert address value }
  for (address, bytes) in support.blobs.toList do
    if let some old := out.blobs[address]? then
      unless old == bytes do throw s!"artifact support: conflicting blob {address}"
    else out := { out with blobs := out.blobs.insert address bytes }
  for (name, named) in support.named.toList do
    if let some old := originalNames[Ix.LeanIngress.ingressName name]? then
      unless old == named.addr do throw s!"artifact support: published address changed for {name.pretty}"
    else
      out := { out with named := out.named.insert name named }
  for (address, name) in support.names.toList do
    if let some old := out.names[address]? then
      unless Ix.LeanIngress.ingressName old == Ix.LeanIngress.ingressName name do
        throw s!"artifact support: conflicting name bytes at {address}"
    else out := { out with names := out.names.insert address name }
  for (address, commitment) in support.comms.toList do
    if let some old := out.comms[address]? then
      unless Ixon.serComm old == Ixon.serComm commitment do
        throw s!"artifact support: conflicting commitment {address}"
    else out := { out with comms := out.comms.insert address commitment }
  for (address, name) in support.addrToName.toList do
    unless out.addrToName.contains address do
      out := { out with addrToName := out.addrToName.insert address name }
  for (address, hint) in support.anonHints.toList do
    match out.anonHints[address]? with
    | some old =>
      unless Ixon.mergeHints old hint == old do
        throw s!"artifact support: the support's reducibility hint at {address} would change \
          the artifact's hint there"
    | none => out := { out with anonHints := out.anonHints.insert address hint }
  return out

/-- **The finalized artifact keeps the original's artifact-level checks.**
`finalize` adds support records, certificate records, evidence records and a
binding after the compile's checks (`Ix.Cert.checkReport`) ran on `original`.
This runs again, on the finalized artifact `final`, every check of
`checkReport` that reads the artifact alone, and checks that the original's
publications and hints are unchanged:

* every name `original` publishes is published at the same address, and every
  reducibility hint `original` stores is stored unchanged. With the records
  only ever added, the checks that read the input as well as the artifact
  (published input definitions hinted, published input names at readable
  records, resolved names published where they resolve) carry over from
  `original`;
* every record and blob is stored at the admission hash of its bytes
  (`Ix.Cert.unauthentic`);
* no record is on a reference cycle (`Ix.Cert.referenceCycle`);
* no two published names share a stored hash (`Ix.Cert.nameHashCollision`);
* every `Muts` entry agrees with its block's projections (`Ix.Cert.mutsMismatch`);
* no member has two stored definition projection records
  (`Ix.Cert.projectionCollision`);
* no address holds both a blob and a record (`Ix.Cert.blobRecordCollision`);
* every stored recursor member is filed at a slot of its own
  (`Ix.Cert.recursorSlotError`);
* the record at an address the default role table binds has its role's kind
  (`Ix.Cert.roleRecordKind`). -/
def checkFinalized (original final : Ixon.Env) : Except String Unit := do
  for (name, named) in original.named.toList do
    unless (final.named.get? name).map (·.addr) == some named.addr do
      throw s!"artifact finalization: the published address of {name.pretty} changed"
  for (address, hint) in original.anonHints.toList do
    unless final.anonHints[address]? == some hint do
      throw s!"artifact finalization: the reducibility hint at {address} changed"
  if let some a := (Ix.Cert.unauthentic final).head? then
    throw s!"artifact finalization: the record or blob at {a} is not stored at the hash of its bytes"
  if let some cycle := Ix.Cert.referenceCycle final then
    throw s!"artifact finalization: the records {cycle.take 4} are on a reference cycle"
  if let some (n, m) := Ix.Cert.nameHashCollision { consts := {} } final then
    throw s!"artifact finalization: the published names {n.pretty} and {m.pretty} share a stored hash"
  if let some (entry, i, _) := Ix.Cert.mutsMismatch final then
    throw s!"artifact finalization: class {i} of the Muts entry {entry.pretty} lists a name not \
      published at its member's projection"
  if let some (block, i) := Ix.Cert.projectionCollision final then
    throw s!"artifact finalization: member {i} of the block at {block} has more than one stored \
      definition projection record"
  if let some a := Ix.Cert.blobRecordCollision final then
    throw s!"artifact finalization: the address {a} holds both a stored blob and a stored record"
  if let some e := Ix.Cert.recursorSlotError final then
    throw s!"artifact finalization: {e.message}"
  if let some (role, address) := Ix.Cert.roleRecordKind final then
    throw s!"artifact finalization: the record at {address}, the default role table's address of \
      {repr role}, is not of its role's kind"

/-- Adding internal support cannot hide a failed original request, change an
original address, or replace its source contract input. -/
def preserveRequested (input : Ix.Compile.CompileInput) (before after : Ixon.Env) :
    Except String Unit := do
  let old ← sourceAddresses before
  let current ← sourceAddresses after
  for (name, _) in input.constants do
    let key := Ix.Kernel.Name.ofLeanName name
    unless old[key]? == current[key]? do
      throw s!"artifact support: changed original publication/failure for {name}"

def compileRequired (backend : Backend) (source : Lean.Environment)
    (input : Ix.Compile.CompileInput) : IO Ixon.Env := do
  let out ← backend source input
  let published ← IO.ofExcept (sourceAddresses out)
  for (name, _) in input.constants do
    unless published.contains (Ix.Kernel.Name.ofLeanName name) do
      throw (IO.userError s!"artifact support: internal compilation did not publish {name}")
  return out

/-- The certificate theorems of the toolchain ix runs on: its own
`IxC.Kernel.PinGen.Certs`, elaborated against its own `Init`. -/
def nativeCertSource : IO Lean.Environment :=
  getCompileEnv #[`IxC.Kernel.PinGen.Certs]

/-- Generate from real certificate source, compiled by the same raw backend.
No committed/default role table or certificate store supplies missing inputs.

The certificate theorems are read from `certSource`, which must be the same
toolchain's environment as `source`: `nativeCertSource` for a compile of ix's own
toolchain, and the imported environment itself for a compile of another
toolchain's export (`Ix.LeanExport`). It is only run when a role with
certificate evidence (a well-founded operation, or a definition specified by
equations that hold by a certificate) is published. -/
def finalize (backend : Backend) (source : Lean.Environment)
    (certSource : IO Lean.Environment)
    (input : Ix.Compile.CompileInput) (artifact : Ixon.Env)
    (limits : Ix.Kernel.Admission.Limits) : IO Ixon.Env := do
  let (required, selected) ← IO.ofExcept (supportInput source artifact)
  let support ← compileRequired backend source selected
  let merged ← IO.ofExcept (mergeSupport limits artifact support)
  -- Validate the whole artifact, including records outside the role closure.
  -- Emission reuses the store associated with these exact bytes and limits.
  let store ← IO.ofExcept (checkedStore limits merged)
  IO.ofExcept (preserveRequested input artifact merged)
  let actual := publishedRoles merged
  unless actual == required do
    throw (IO.userError "artifact support: compiled role publications differ from the selected closure")
  let theorems := (Ix.RoleEvidence.allCertTheorems.filter (fun (role, _) => required.contains role)).flatMap (·.2)
  let certificates ← if theorems.isEmpty then pure ({} : Ixon.Env) else do
    let certSource ← certSource
    for name in theorems do
      match certSource.find? name with
      | some (.thmInfo _) => pure ()
      | _ => throw (IO.userError s!"artifact evidence: source theorem unavailable: {name}")
    let constants := Ix.EnvScope.collectSelectedDeps certSource theorems
    let selected ← IO.ofExcept ((Ix.Compile.compileInputFromEnv certSource constants).mapError toString)
    compileRequired backend certSource selected
  IO.ofExcept (checkCertificateContent merged certificates)
  -- The support already contains every selected role and its source closure.
  -- Evidence generation needs only that closure and the certificate closure;
  -- emission below checks its binding against the complete merged artifact.
  let generated ← IO.ofExcept (generate limits support certificates required Ix.Kernel.preludeShape)
  let emitted ← IO.ofExcept (generated.emit limits merged (store? := some store))
  IO.ofExcept (preserveRequested input artifact emitted)
  IO.ofExcept (checkFinalized artifact emitted)
  return emitted

/-- Publish only after finalization and serialization succeed. The temporary
file is beside the destination so rename is atomic on that filesystem. -/
def writeAtomic (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let nonce ← IO.rand 0 18446744073709551615
  let temporary := System.FilePath.mk (path.toString ++ s!".binding-{nonce}")
  let handle ← IO.FS.Handle.mk temporary .writeNew
  try
    handle.write bytes
    handle.flush
    IO.FS.rename temporary path
  finally
    if ← temporary.pathExists then IO.FS.removeFile temporary

end Ix.RoleBinding.Compile
