module

public import Ix.RoleBinding.Generate
public import Ix.CompileResource
public import Ix.AuxGen.LiteralSupport
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

def leanBackend (workers : Nat) (opts : Ix.CompileM.DriverOptions) : Backend := fun source input => do
  let opts := { opts with serviceSupport := Ix.AuxGen.literalSupportFor source input.constants }
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

/-- Canonical original payloads retain their own channel unless the identical
bytes are now carried by the checked store. Their named associations stay put. -/
def mergeOriginals (limits : Ix.Kernel.Admission.Limits) (out : Ixon.Env)
    (extra : Std.HashMap Address Ixon.LazyConstant) : Except String Ixon.Env := do
  let mut originals := out.originals
  for (address, value) in extra.toList ++ out.originals.toList do
    let bytes := value.rawBytes
    unless Address.admissionHash bytes == address do
      throw s!"artifact support: original payload has bad address {address}"
    let decoded ← Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes
    unless Ixon.serConstant decoded == bytes do
      throw s!"artifact support: noncanonical original payload {address}"
    if let some old := originals[address]? then
      unless old.rawBytes == bytes do throw s!"artifact support: conflicting original payload {address}"
    if let some checked := out.consts[address]? then
      unless checked.rawBytes == bytes do throw s!"artifact support: original/checked bytes differ at {address}"
      originals := originals.erase address
    else originals := originals.insert address value
  return { out with originals }

/-- Merge authenticated support without replacing any original publication or
its metadata. Structural names, rather than stored name hashes, decide overlap. -/
def mergeSupport (limits : Ix.Kernel.Admission.Limits) (original support : Ixon.Env) :
    Except String Ixon.Env := do
  let _ ← recordStore limits original
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
      if let some hint := support.originalHintOverrides[name]? then
        out := { out with originalHintOverrides := out.originalHintOverrides.insert name hint }
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
    let hint := match out.anonHints[address]? with
      | some old => Ixon.mergeHints old hint
      | none => hint
    out := { out with anonHints := out.anonHints.insert address hint }
  mergeOriginals limits out support.originals

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

/-- Keep every internal compiler trace, delimiting its invocation so callers
can distinguish repeated blocks from duplicate work within one compilation. -/
def internalTrace (label : String) (action : IO α) : IO α := do
  let traced := (← IO.getEnv "IX_AUXGEN_IXC").isSome
  if traced then IO.eprintln s!"[artifact-compile] begin {label}"
  try action
  finally
    if traced then IO.eprintln s!"[artifact-compile] end {label}"

/-- Generate from real certificate source, compiled by the same raw backend.
No committed/default role table or certificate store supplies missing inputs. -/
def finalize (backend : Backend) (source : Lean.Environment)
    (input : Ix.Compile.CompileInput) (artifact : Ixon.Env)
    (limits : Ix.Kernel.Admission.Limits) : IO Ixon.Env := do
  let (required, selected) ← IO.ofExcept (supportInput source artifact)
  let support ← internalTrace "support" (compileRequired backend source selected)
  let merged ← IO.ofExcept (mergeSupport limits artifact support)
  IO.ofExcept (preserveRequested input artifact merged)
  let actual := publishedRoles merged
  unless actual == required do
    throw (IO.userError "artifact support: compiled role publications differ from the selected closure")
  let theorems := (Ix.RoleEvidence.certTheorems.filter (fun (role, _) => required.contains role)).flatMap (·.2)
  let certificates ← if theorems.isEmpty then pure ({} : Ixon.Env) else do
    let certSource ← getCompileEnv #[`IxC.Kernel.PinGen.Certs]
    for name in theorems do
      match certSource.find? name with
      | some (.thmInfo _) => pure ()
      | _ => throw (IO.userError s!"artifact evidence: source theorem unavailable: {name}")
    let constants := Ix.EnvScope.collectSelectedDeps certSource theorems
    let selected ← IO.ofExcept ((Ix.Compile.compileInputFromEnv certSource constants).mapError toString)
    internalTrace "certificates" (compileRequired backend certSource selected)
  let generated ← IO.ofExcept (generate limits merged certificates required Ix.Kernel.preludeShape)
  let emitted ← IO.ofExcept (generated.emit limits merged)
  let emitted ← IO.ofExcept (mergeOriginals limits emitted {})
  IO.ofExcept (preserveRequested input artifact emitted)
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
