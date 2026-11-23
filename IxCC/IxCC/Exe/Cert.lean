import IxCC.Exe
import IxCC.X86.Exe.Cert
import IxCC.CompileClaim

/-! # End-to-End Certified Executable Builder & Verifier (`ixcc verify-exe`)

Connects `CompileClaim` (with `KF-4` + `SP-0` logical seed-closure kernel
acceptance and `N5` resource mode checking) to hardened `.ix.cert` v1
standalone Linux x86-64 executables (`X86.Exe.Cert`):

- `buildCertifiedExe`: wraps a checked standalone executable core (`Exe.build`
  or `Exe.buildMachine`) with a hardened `.ix.cert` v1 trailer (strict `0xCC`
  RX page-tail trap sled, page-aligned non-alloc `.ix.cert` section, exact
  `.shstrtab`, flush 3-entry ELF64 section header table).
- `verifyExeBytes`: deterministically validates a certified executable from its
  bytes alone (or with optional external `--closure` / `--equations`):
  1. Strictly parses the 3-section ELF64 trailer and `0xCC` RX page-tail sled
     (`X86.Exe.Cert.extractTrailer`).
  2. Decodes the canonical `.ix.cert` v1 payload (`Payload.decode`) and
     `CompileClaim` wire bytes (`CompileClaim.ofClaimBytes`).
  3. Runs full `Recheck.ingress`, `KF-4` pure logical seed-closure checking
     under committed `preludeFor` + committed `defaultBinding` + `N5` mode
     checking (`CompileClaim.checkCertSeedClosure`), canonical relevance
     (`Stage A`), Ixon v5 `Definition.asserts` (`EM-0`), and `Recheck.run` /
     `runWithContracts` / `RcReplay.run` + `CompileClaim.verifyProgram`.
  4. Deterministically re-assembles `expectedCore` via `Exe.build` or
     `Exe.buildMachine` (`planFor` + `assembleFor` + `checkFor` + `Shell.check`).
  5. Checks exact whole-image equality via `X86.Exe.Cert.checkTrailer` (blocking
     ANY core modification, RX page-tail code smuggling, header forgery, or
     trailing garbage).

End-to-end soundness theorems live in `IxCC.Exe.Cert.Proof`. -/

set_option autoImplicit false

namespace IxCC.Exe.Cert

open IxCC.Recheck
open IxCC.X86.Exe.Cert

/-- Policy classification for a verified CLI certificate (`immortal`, `zeroRc`, or `plainRc`). -/
def policyOfArtifact (cfg : Recheck.Config) (inp : Recheck.Input) (a : Recheck.Artifact)
    (isPlainRc : Bool) (certText : String) : CompilePolicy :=
  if isPlainRc then .plainRc
  else
    match Recheck.Cert.ofText certText with
    | .ok cert =>
      if Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc &&
          (Recheck.runWithContracts cfg inp.program cert).isOk then
        .zeroRc
      else .immortal
    | .error _ => .immortal

/-- Result of building a certified standalone executable. -/
structure BuiltCertifiedExe where
  bytes : ByteArray
  claim : CompileClaim
  coreSize : Nat
  payloadSize : Nat
  placement : X86.Exe.Placement
  deriving Inhabited

/-- Build a hardened `.ix.cert` v1 certified standalone executable from a verified
artifact `a`, its certificate text `certText`, its policy, and the `.ixe` /
equations bytes to embed in `.ix.cert`. -/
def buildCertifiedExe (inp : Recheck.Input) (rootSelection : List String)
    (policy : CompilePolicy) (certText : String) (a : Recheck.Artifact)
    (exeKind : ExeKind) (layout : X86.Exe.Layout)
    (envBytes eqBytes : ByteArray) : Except Err BuiltCertifiedExe := do
  let some (target, _) := inp.program.roots.head?
    | throw (Exe.err "exe.cert.root" "ingested program has no root")
  let some root := a.roots.head?
    | throw (Exe.err "exe.cert.root" "artifact has no root")
  let (core, placement) ← match exeKind with
    | .plain =>
      let ⟨_, certExe⟩ ← Exe.build a layout
      pure (certExe.bytes, certExe.plan.placement)
    | .machine =>
      let L : X86.Exe.Machine.Layout := { stack := layout.stack, region := layout.region }
      let ⟨_, certExe⟩ ← Exe.buildMachine a L
      pure (certExe.checked.bytes, certExe.checked.plan.placement)
  let claim : CompileClaim := {
    env := inp.env.root
    roleTable := inp.env.bindingAddress
    target
    policy
    abiArity := root.params
    elfHash := Ixon.Address.blake3Pure a.object
  }
  let payload : Payload := {
    exeKind
    stack := layout.stack
    region := layout.region
    rootNames := rootSelection
    claimBytes := claim.toClaimBytes
    certBytes := certText.toUTF8
    envBytes
    eqBytes
  }
  let payloadBytes := payload.encode
  let bytes ← (attachTrailer core payloadBytes).mapError fun e =>
    Exe.err "exe.cert.attach" e.render
  unless checkTrailer core payloadBytes bytes do
    throw (Exe.err "exe.cert.attach" "certified executable failed trailer self-check")
  pure { bytes, claim, coreSize := core.size, payloadSize := payloadBytes.size, placement }

/-- Summary of a successfully verified certified executable. -/
structure VerifiedExe where
  claim : CompileClaim
  exeKind : ExeKind
  layout : X86.Exe.Layout
  rootNames : List String
  coreSize : Nat
  payloadSize : Nat
  objectSize : Nat
  deriving Repr, Inhabited

/-- Resolve `.ixe` closure bytes from `.ix.cert` and optional external `--closure`. -/
def resolveEnvBytes (payload : Payload) (extEnv? : Option ByteArray) : Except Err ByteArray :=
  match extEnv? with
  | some ext =>
    if payload.envBytes.isEmpty || payload.envBytes == ext then .ok ext
    else .error (Exe.err "exe.cert.env" "external --closure disagrees with embedded closure bytes")
  | none =>
    if payload.envBytes.isEmpty then
      .error (Exe.err "exe.cert.env" ".ix.cert omits closure bytes; supply --closure")
    else .ok payload.envBytes

/-- Resolve equations JSON bytes from `.ix.cert` and optional external `--equations`. -/
def resolveEqBytes (payload : Payload) (extEq? : Option ByteArray) : Except Err ByteArray :=
  match extEq? with
  | some ext =>
    if payload.eqBytes.isEmpty || payload.eqBytes == ext then .ok ext
    else .error (Exe.err "exe.cert.eq" "external --equations disagrees with embedded equations bytes")
  | none =>
    if payload.eqBytes.isEmpty then
      .error (Exe.err "exe.cert.eq" ".ix.cert omits equations bytes; supply --equations")
    else .ok payload.eqBytes

/-- Parse and validate equations JSON bytes. -/
def parseEquationsJson (eqRaw : ByteArray) : Except Err Lean.Json :=
  match String.fromUTF8? eqRaw with
  | none => .error (Exe.err "exe.cert.utf8" "invalid UTF-8 in equations JSON")
  | some eqText =>
    match Src.Hints.checkJsonText eqText >>= fun () => Lean.Json.parse eqText with
    | .ok j => .ok j
    | .error e => .error (Exe.err "exe.cert.eq" s!"invalid equations JSON: {e}")

/-- Replay the certificate according to `policy` to obtain the checked `Recheck.Artifact`. -/
def replayArtifact (cfg : Recheck.Config) (prog : Src.Program)
    (policy : CompilePolicy) (certText : String) : Except Err Recheck.Artifact :=
  match policy with
  | .immortal => do
    let cert ← Recheck.Cert.ofText certText
    Recheck.run cfg prog cert
  | .zeroRc => do
    let cert ← Recheck.Cert.ofText certText
    let art ← Recheck.runWithContracts cfg prog cert
    unless Own.Plain.selectRcPolicyForSrc art.src art.front.fir == .zeroRc do
      throw (Exe.err "exe.cert.policy" "program does not select zeroRc policy")
    pure art
  | .plainRc => do
    let cert ← (Recheck.RcReplay.Cert.ofText certText).mapError fun e =>
      Exe.err "exe.cert.parse" e
    let rcArt ← Recheck.RcReplay.run cfg prog cert
    rcArt.toRecheckArtifact cert

/-- Deterministically re-assemble the checked ELF core bytes for `kind` and `layout`. -/
def rebuildExpectedCore (a : Recheck.Artifact) (kind : ExeKind)
    (layout : X86.Exe.Layout) : Except Err ByteArray :=
  match kind with
  | .plain => do
    let ⟨_, certExe⟩ ← Exe.build a layout
    pure certExe.bytes
  | .machine => do
    let L : X86.Exe.Machine.Layout := { stack := layout.stack, region := layout.region }
    let ⟨_, certExe⟩ ← Exe.buildMachine a L
    pure certExe.checked.bytes

/-- Convert an `Option` to `Except Err` using error `e`. -/
def optionToExcept {α : Type} (e : Err) : Option α → Except Err α
  | some a => .ok a
  | none => .error e

/-- Require a boolean predicate, returning `e` when `false`. -/
def requireBool (cond : Bool) (e : Err) : Except Err Unit :=
  if cond then .ok () else .error e

/-- Deterministically verify a hardened `.ix.cert` v1 certified executable from
its raw file bytes (plus optional external `.ixe` closure and equations JSON
bytes when omitted from or cross-checked against `.ix.cert`). -/
def verifyExeBytes (exeBytes : ByteArray)
    (extEnv? : Option ByteArray := none)
    (extEq? : Option ByteArray := none)
    (limits : Ix.Kernel.Admission.Limits := Src.KernelFront.defaultLimits) :
    Except Err VerifiedExe := do
  let (coreSz, payloadBytes) ← (extractTrailer exeBytes).mapError fun e =>
    Exe.err "exe.cert.trailer" e.render
  let payload ← (Payload.decode payloadBytes).mapError fun e =>
    Exe.err "exe.cert.payload" e.render
  let claim ← optionToExcept
    (Exe.err "exe.cert.claim" "malformed CompileClaim bytes in .ix.cert")
    (CompileClaim.ofClaimBytes payload.claimBytes)
  let envBytes ← resolveEnvBytes payload extEnv?
  let eqRaw ← resolveEqBytes payload extEq?
  let certText ← optionToExcept
    (Exe.err "exe.cert.utf8" "invalid UTF-8 in embedded certificate text")
    (String.fromUTF8? payload.certBytes)
  let equations ← parseEquationsJson eqRaw
  let selCfg : Recheck.Config := { names := payload.rootNames }
  let roots := CompileClaim.selectTargetRoots selCfg equations claim.target
  let inp ← Recheck.ingress envBytes equations roots limits
  let cfg := Recheck.Config.forInput selCfg inp
  let () ← requireBool (inp.env.root == claim.env && inp.env.bindingAddress == claim.roleTable)
    (Exe.err "exe.cert.env" "environment root or roleTable does not match CompileClaim")
  let _ ← (CompileClaim.checkCertSeedClosure inp claim.target claim.policy certText limits).mapError fun e =>
    Exe.err "exe.cert.kf4" e
  let () ← requireBool (CompileClaim.checkCertCanonicalRelevance cfg inp claim.policy certText)
    (Exe.err "exe.cert.relevance" "canonical relevance check failed")
  let () ← requireBool (CompileClaim.checkCertDefAsserts cfg inp claim.policy certText)
    (Exe.err "exe.cert.asserts" "Definition.asserts check failed")
  let a ← replayArtifact cfg inp.program claim.policy certText
  let () ← requireBool (CompileClaim.verifyProgram cfg inp.program claim certText)
    (Exe.err "exe.cert.claim" "CompileClaim.verifyProgram failed")
  let layout : X86.Exe.Layout := { stack := payload.stack, region := payload.region }
  let expectedCore ← rebuildExpectedCore a payload.exeKind layout
  let () ← requireBool (coreSz == expectedCore.size && checkTrailer expectedCore payloadBytes exeBytes)
    (Exe.err "exe.cert.trailer" CertError.trailerMismatch.render)
  pure {
    claim
    exeKind := payload.exeKind
    layout
    rootNames := payload.rootNames
    coreSize := expectedCore.size
    payloadSize := payloadBytes.size
    objectSize := a.object.size
  }

end IxCC.Exe.Cert
