import IxCC.Recheck
import IxCC.Recheck.Linked
import IxCC.Recheck.Rc.Produce
import IxCC.Recheck.Rc.Linked
import IxCC.Recheck.Rc.Bytes
import IxCC.Ixon.PureHash

/-! # `CompileClaim`: End-to-End `Ixon.Address` ↔ ELF64 Hash Bridge

Connects an Ixon environment Merkle root `Address` and target constant `Address`
under a `CompilePolicy` (`immortal`, `zeroRc`, `plainRc`) and ABI parameter arity
to the pure BLAKE3 digest (`Ixon.Address.blake3Pure`) of the emitted x86-64 ELF64
object bytes, matching the host `Ix.Claim.compile` wire format byte-for-byte:

1. **Wire Format Alignment (`S12`, `A1-4`, `A1-10`, `A8-2`, `A8-11`)**:
   - `CompileClaim.toClaimBytes` serializes the exact 4-byte `Ix.Claim.put (.compile ...)`
     header `#[0xE8, 0x03, 0x04, 0x06]` (`putTagN 4 0xE 11` ++ `putScope VALIDATOR_COMPILE_V1`)
     followed by `toPayloadBytes` (`env` 32B ++ `target` 32B ++ `[policy.toUInt8]` 1B ++
     `putTag0 abiArity` 1..9B ++ `elfHash` 32B), totaling 102 bytes when `abiArity < 128`.
   - `CompileClaim.ofClaimBytes` parses and validates the canonical wire envelope
     via `Ixon.runGet`, rejecting non-canonical `Tag0` headers and trailing bytes.
   - Global `Coe (List UInt8) ByteArray` has been removed (`A8-11`).

2. **Verified Ingress, Policy Unification & Root Observability (`S4`, `S7`, `A1-3`, `A1-6`, `A4-10`, `A4-12`)**:
   - `verifyBytes`, `checkClaim`, and `makeClaim` default to `typecheck := true`,
     running `Ixon.V3.Tc.checkEnv` during `Recheck.ingress`.
   - `verifyProgram` requires `c.abiArity < 2 ^ 64`, verifies that the target root
     declaration is monomorphic with all-`Nat` parameters (`rootParamsAllNat`),
     and requires a non-vacuous readback type (`isImmortalViewType` on the
     `.immortal` and `.zeroRc` paths; `root.ty.isSome` on the `.plainRc` path).
   - `.zeroRc` verification uses `Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc`
     (matching `produceAuto` and `produce`), and `makeClaim` / `produce` avoid
     redundant re-ingress and double recheck.
   - With the default `.auto` mode, `produce` and `makeClaim` compile under the
     immortal policy when plain RC is selected but its certificate cannot be
     produced or is refused (`produceAuto`'s `.immortal` fallback); the claim's
     `policy` is the policy actually compiled under.

3. **Proof Separation (`A8-5`)**:
   - This module contains only executable definitions, checkers, and wire codecs.
   - End-to-end soundness theorems (`verifyProgram_*_sound`, `verifyBytes_*_sound`,
     and wire roundtrip proofs) live in `IxCC.CompileClaim.Proof`. -/

set_option autoImplicit false

namespace IxCC.Compiler

/-- Reference-counting compilation policy mode for `CompileClaim.produce`. -/
inductive RcMode where
  | auto
  | off
  | on
  | immortal
  | zeroRc
  | plainRc
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Alias for `Recheck.RcReplay.produceAuto`. -/
abbrev produceAuto := Recheck.RcReplay.produceAuto

end IxCC.Compiler

namespace IxCC

/-- Memory-management policy under which an x86-64 ELF object was compiled. -/
inductive CompilePolicy where
  | immortal
  | zeroRc
  | plainRc
  deriving BEq, Repr, Inhabited, DecidableEq

namespace CompilePolicy

/-- Wire tag for `CompilePolicy` (`immortal => 0, zeroRc => 1, plainRc => 2`). -/
def toUInt8 : CompilePolicy → UInt8
  | .immortal => 0
  | .zeroRc   => 1
  | .plainRc  => 2

/-- Decode a `CompilePolicy` from its wire tag (`0..2`). -/
def ofUInt8? : UInt8 → Option CompilePolicy
  | 0 => some .immortal
  | 1 => some .zeroRc
  | 2 => some .plainRc
  | _ => none

@[simp] theorem ofUInt8?_toUInt8 (p : CompilePolicy) :
    ofUInt8? p.toUInt8 = some p := by
  cases p <;> rfl

end CompilePolicy

/-- Certified compilation claim connecting an Ixon environment Merkle root `env`
and target constant `target` under `policy` and `abiArity` to `elfHash`. -/
structure CompileClaim where
  env      : Ixon.Address
  target   : Ixon.Address
  policy   : CompilePolicy
  abiArity : Nat
  elfHash  : Ixon.Address
  deriving BEq, Repr, Inhabited, DecidableEq

namespace CompileClaim

/-- Well-formedness predicate for a `CompileClaim`: `abiArity < 2 ^ 64` so its
`Tag0` encoding is canonical (`Ixon.Address` fields already carry `hash_size : hash.size = 32`). -/
def WellFormed (c : CompileClaim) : Prop :=
  c.abiArity < 2 ^ 64

/-- Decidable check for `CompileClaim.WellFormed`. -/
def checkWellFormed (c : CompileClaim) : Bool :=
  decide (c.abiArity < 2 ^ 64)

/-- `Ix.Claim.put (.compile ...)` Tag4 header bytes (`putTagN 4 0xE 11 = #[0xE8, 0x03]`). -/
def CLAIM_TAG4_COMPILE : ByteArray := ByteArray.mk #[0xE8, 0x03]

/-- Scope domain tag for object format claims (`OBJECT_FORMAT = 4`). -/
def OBJECT_FORMAT : UInt8 := 0x04

/-- Validator ID for `CompileClaim` v1 (`6`, matching `Ix.Claim.VALIDATOR_COMPILE_V1`). -/
def VALIDATOR_COMPILE_V1 : UInt8 := 0x06

/-- Claim variant index (`11`, encoded in `CLAIM_TAG4_COMPILE`). -/
def VARIANT_COMPILE_CLAIM : UInt8 := 11

/-- The exact 4-byte `Ix.Claim.put (.compile ...)` wire header:
`#[0xE8, 0x03, 0x04, 0x06]` (`putTagN 4 0xE 11` ++ `putScope VALIDATOR_COMPILE_V1`). -/
def validatorHeader : ByteArray :=
  ByteArray.mk #[0xE8, 0x03, OBJECT_FORMAT, VALIDATOR_COMPILE_V1]

/-- Canonical Ixon Tag0 (`Ixon.tag0Bytes`) variable-length integer encoding for `v < 2 ^ 64`. -/
def putTag0 (v : Nat) : List UInt8 :=
  (Ixon.tag0Bytes ⟨UInt64.ofNat v⟩).data.toList

/-- Monadic payload reader in `Ixon.GetM` for `CompileClaim`. -/
def getPayloadM : Ixon.GetM CompileClaim := do
  let env ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
  let target ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
  let polByte ← Ixon.getU8
  let some policy := CompilePolicy.ofUInt8? polByte |
    throw "CompileClaim: invalid policy byte"
  let arityTag ← Ixon.getTag0
  let elfHash ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
  return {
    env
    target
    policy
    abiArity := arityTag.size.toNat
    elfHash
  }

/-- Monadic full-envelope reader in `Ixon.GetM` for `CompileClaim`. -/
def getClaimM : Ixon.GetM CompileClaim := do
  let hdr ← Ixon.getBytes 4
  if hdr != validatorHeader then
    throw "CompileClaim: invalid validator header"
  getPayloadM

/-- Serialize the `CompileClaim` payload (`env ++ target ++ [policy.toUInt8] ++ putTag0 abiArity ++ elfHash`),
matching `Ix.Claim.CompileClaim.put` byte-for-byte (98 bytes when `abiArity < 128`). -/
def toPayloadBytes (c : CompileClaim) : ByteArray :=
  c.env.hash ++
    c.target.hash ++
    Ixon.u8Bytes c.policy.toUInt8 ++
    Ixon.tag0Bytes ⟨UInt64.ofNat c.abiArity⟩ ++
    c.elfHash.hash

/-- Deserialize a `CompileClaim` payload produced by `toPayloadBytes`. -/
def ofPayloadBytes (bs : ByteArray) : Option CompileClaim :=
  (Ixon.runGet getPayloadM bs).toOption

/-- Serialize the full `CompileClaim` wire envelope (`#[0xE8, 0x03, 0x04, 0x06] ++ c.toPayloadBytes`),
matching `Ix.Claim.ser (.compile ...)` byte-for-byte (102 bytes when `abiArity < 128`). -/
def toClaimBytes (c : CompileClaim) : ByteArray :=
  validatorHeader ++ c.toPayloadBytes

/-- Deserialize a full `CompileClaim` wire envelope produced by `toClaimBytes`. -/
def ofClaimBytes (bs : ByteArray) : Option CompileClaim :=
  (Ixon.runGet getClaimM bs).toOption

/-- Pure BLAKE3 commitment digest over `c.toClaimBytes`. -/
def commit (c : CompileClaim) : Ixon.Address :=
  Ixon.Address.blake3Pure c.toClaimBytes

/-- Check that a readback type is a scalar (`Nat`) or a nullary-constructor enum
supported by `Rt.tagify` (`Front.view` on the `.immortal` / `.zeroRc` path). -/
def isImmortalViewType (sig : Rt.Sig) : Rt.FoTy → Bool
  | .nat => true
  | .ind idx =>
    match sig.inds[idx]? with
    | some ctors => !ctors.isEmpty && ctors.all List.isEmpty
    | none => false

/-- Check that `dom` is the `Nat` constant in `src`. -/
def isNatType (src : Src.Program) (dom : Src.Term) : Bool :=
  some dom == src.known.nat.map (Src.Term.const · [])

/-- Check that a root declaration in `src` is monomorphic (`d.lvls == 0`), its
Π-telescope length matches `root.params`, and every parameter in its Π-telescope
has domain `Nat`, matching the `(Nat × List Nat)` ABI of `CheckedProgram` and
`X86.Linked`. -/
def rootParamsAllNat (src : Src.Program) (root : Recheck.Root) : Bool :=
  match src.decl? root.const with
  | some d =>
    d.lvls == 0 &&
      d.type.pis.1.length == root.params &&
      (d.type.pis.1.take root.params).all fun (_, dom) => isNatType src dom
  | none => false

/-- Check that a root on the `.immortal` / `.zeroRc` path has all-`Nat` parameters
and a non-vacuous scalar/enum readback type (`isImmortalViewType`). -/
def checkImmortalRoot (src : Src.Program) (root : Recheck.Root) : Bool :=
  rootParamsAllNat src root &&
    match root.ty with
    | some (sig, ty) => isImmortalViewType sig ty
    | none => false

/-- Check that a root on the `.plainRc` path has all-`Nat` parameters and a
discovered first-order readback signature (`root.ty.isSome`). -/
def checkPlainRcRoot (src : Src.Program) (root : Recheck.Root) : Bool :=
  rootParamsAllNat src root && root.ty.isSome

/-- Verify a `CompileClaim` against an ingested `Src.Program` and serialized
certificate `certText` using pure BLAKE3 (`Ixon.Address.blake3Pure`). -/
def verifyProgram (cfg : Recheck.Config) (P : Src.Program) (c : CompileClaim) (certText : String) : Bool :=
  c.checkWellFormed &&
    match P.roots.head? with
    | some (rootAddr, _) =>
      if rootAddr == c.target then
        match c.policy with
        | .immortal =>
          match Recheck.Cert.ofText certText with
          | .ok cert =>
            match Recheck.run cfg P cert with
            | .ok a =>
              match a.roots.head? with
              | some root =>
                checkImmortalRoot a.src root &&
                  (root.params == c.abiArity) &&
                  (Ixon.Address.blake3Pure a.object == c.elfHash)
              | none => false
            | .error _ => false
          | .error _ => false
        | .zeroRc =>
          match Recheck.Cert.ofText certText with
          | .ok cert =>
            match Recheck.runWithContracts cfg P cert with
            | .ok a =>
              match a.roots.head? with
              | some root =>
                checkImmortalRoot a.src root &&
                  (Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc) &&
                  (root.params == c.abiArity) &&
                  (Ixon.Address.blake3Pure a.object == c.elfHash)
              | none => false
            | .error _ => false
          | .error _ => false
        | .plainRc =>
          match Recheck.RcReplay.Cert.ofText certText with
          | .ok cert =>
            match Recheck.RcReplay.run cfg P cert with
            | .ok a =>
              match a.roots.head? with
              | some root =>
                checkPlainRcRoot a.front.src root &&
                  (root.params == c.abiArity) &&
                  (Ixon.Address.blake3Pure a.backend.object == c.elfHash)
              | none => false
            | .error _ => false
          | .error _ => false
      else false
    | none => false

/-- Select the root names for `verifyBytes`: use `cfg.names` when provided, or
the sidecar root matching `target` when the sidecar lists multiple roots. -/
def selectTargetRoots (cfg : Recheck.Config) (equations : Lean.Json) (target : Ixon.Address) : List String :=
  if !cfg.names.isEmpty then cfg.names
  else
    match Src.Hints.ofK1Json equations with
    | .ok hints =>
      if hints.roots[0]?.map (·.1) == some target then []
      else
        match hints.roots.find? (·.1 == target) with
        | some (_, some name) => [name]
        | _ => []
    | .error _ => []

/-- Verify that the serialized certificate's relevance annotation equals the
canonical output of `Src.Relevance.annotate` on `inp.env` and the validated
table (`Stage A`). -/
def checkCertCanonicalRelevance (cfg : Recheck.Config) (inp : Recheck.Input)
    (policy : CompilePolicy) (certText : String) : Bool :=
  match policy with
  | .immortal | .zeroRc =>
    match Recheck.Cert.ofText certText with
    | .ok cert => Recheck.checkCanonicalRelevance cfg inp cert.table cert.relevance
    | .error _ => false
  | .plainRc =>
    match Recheck.RcReplay.Cert.ofText certText with
    | .ok cert => Recheck.checkCanonicalRelevance cfg inp cert.base.table cert.base.relevance
    | .error _ => false

/-- Verify a `CompileClaim` from raw `.ixe` environment bytes, sidecar equations
JSON, and serialized certificate `certText`. Defaults to `typecheck := true` so
`Ixon.V3.Tc.checkEnv` validates the decoded environment at ingress (`S4`, `A1-6`)
and `checkCertCanonicalRelevance` validates canonical relevance (`Stage A`). -/
def verifyBytes (cfg : Recheck.Config) (envBytes : ByteArray) (equations : Lean.Json)
    (c : CompileClaim) (certText : String) (typecheck : Bool := true) : Bool :=
  let roots := selectTargetRoots cfg equations c.target
  match Recheck.ingress envBytes equations roots typecheck with
  | .ok inp =>
    (inp.env.root == c.env) &&
      checkCertCanonicalRelevance cfg inp c.policy certText &&
      verifyProgram cfg inp.program c certText
  | .error _ => false

/-- Produce `(claim, certText, elfBytes)` from `Recheck.Input` and `Compiler.RcMode`
(defaulting to `.auto` via `Compiler.produceAuto`). -/
def produce (cfg : Recheck.Config) (input : Recheck.Input) (mode : Compiler.RcMode := .auto) :
    Except Recheck.Err (CompileClaim × String × ByteArray) := do
  let some (target, _) := input.program.roots.head?
    | throw { stage := .ingress, code := "roots", message := "program has no root" }
  let inp := { input with names := cfg.names }
  match mode with
  | .auto =>
    match ← Compiler.produceAuto cfg inp with
    | .zeroRc cert a _ =>
      unless a.checkContractOwn do
        throw { stage := .cert, code := "own.plain", message := "contract ownership domain check failed" }
      let some root := a.roots.head?
        | throw { stage := .rt, code := "roots", message := "artifact has no root" }
      unless checkImmortalRoot a.src root do
        throw { stage := .cert, code := "roots", message := "root parameters must be Nat and result type must be scalar/enum for zeroRc" }
      let elfBytes := a.backend.object
      let claim : CompileClaim :=
        { env := input.env.root
          target
          policy := .zeroRc
          abiArity := root.params
          elfHash := Ixon.Address.blake3Pure elfBytes }
      return (claim, cert.toText, elfBytes)
    | .plainRc cert a _ =>
      let some root := a.roots.head?
        | throw { stage := .rt, code := "roots", message := "artifact has no root" }
      unless checkPlainRcRoot a.front.src root do
        throw { stage := .cert, code := "roots", message := "root parameters must be Nat and result type must be observable for plainRc" }
      let elfBytes := a.backend.object
      let claim : CompileClaim :=
        { env := input.env.root
          target
          policy := .plainRc
          abiArity := root.params
          elfHash := Ixon.Address.blake3Pure elfBytes }
      return (claim, cert.toText, elfBytes)
    | .immortal cert a _ _ =>
      -- plain RC was selected but refused: the claim binds the immortal policy it compiled under
      let some root := a.roots.head?
        | throw { stage := .rt, code := "roots", message := "artifact has no root" }
      unless checkImmortalRoot a.src root do
        throw { stage := .cert, code := "roots", message := "root parameters must be Nat and result type must be scalar/enum for immortal" }
      let elfBytes := a.backend.object
      let claim : CompileClaim :=
        { env := input.env.root
          target
          policy := .immortal
          abiArity := root.params
          elfHash := Ixon.Address.blake3Pure elfBytes }
      return (claim, cert.toText, elfBytes)
  | .off | .immortal =>
    let cert ← Recheck.produce cfg inp
    let a ← Recheck.run cfg input.program cert
    let some root := a.roots.head?
      | throw { stage := .rt, code := "roots", message := "artifact has no root" }
    unless checkImmortalRoot a.src root do
      throw { stage := .cert, code := "roots", message := "root parameters must be Nat and result type must be scalar/enum for immortal" }
    let elfBytes := a.backend.object
    let claim : CompileClaim :=
      { env := input.env.root
        target
        policy := .immortal
        abiArity := root.params
        elfHash := Ixon.Address.blake3Pure elfBytes }
    return (claim, cert.toText, elfBytes)
  | .zeroRc =>
    let cert ← Recheck.produce cfg inp
    let a ← Recheck.runWithContracts cfg input.program cert
    unless Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc do
      throw { stage := .cert, code := "own.plain", message := "program does not select zeroRc policy" }
    let some root := a.roots.head?
      | throw { stage := .rt, code := "roots", message := "artifact has no root" }
    unless checkImmortalRoot a.src root do
      throw { stage := .cert, code := "roots", message := "root parameters must be Nat and result type must be scalar/enum for zeroRc" }
    let elfBytes := a.backend.object
    let claim : CompileClaim :=
      { env := input.env.root
        target
        policy := .zeroRc
        abiArity := root.params
        elfHash := Ixon.Address.blake3Pure elfBytes }
    return (claim, cert.toText, elfBytes)
  | .on | .plainRc =>
    let (cert, a) ← Recheck.RcReplay.produce cfg inp
    let some root := a.roots.head?
      | throw { stage := .rt, code := "roots", message := "artifact has no root" }
    unless checkPlainRcRoot a.front.src root do
      throw { stage := .cert, code := "roots", message := "root parameters must be Nat and result type must be observable for plainRc" }
    let elfBytes := a.backend.object
    let claim : CompileClaim :=
      { env := input.env.root
        target
        policy := .plainRc
        abiArity := root.params
        elfHash := Ixon.Address.blake3Pure elfBytes }
    return (claim, cert.toText, elfBytes)

/-- Check a `CompileClaim` against an ingested `Src.Program` and serialized certificate. -/
def checkClaimProgram (cfg : Recheck.Config) (P : Src.Program) (c : CompileClaim)
    (certText : String) : Except String Unit := do
  unless verifyProgram cfg P c certText do
    throw "CompileClaim.checkClaimProgram: claim verification failed"

/-- Check a `CompileClaim` from raw `.ixe` environment bytes, sidecar equations JSON,
and serialized certificate `certText`. Defaults to `typecheck := true` (`S4`, `A1-6`). -/
def checkClaim (cfg : Recheck.Config) (envBytes : ByteArray) (equations : Lean.Json)
    (c : CompileClaim) (certText : String) (typecheck : Bool := true) : Except String Unit := do
  unless verifyBytes cfg envBytes equations c certText typecheck do
    throw "CompileClaim.checkClaim: byte-level claim verification failed"

theorem checkClaim_ok_iff {cfg : Recheck.Config} {envBytes : ByteArray}
    {equations : Lean.Json} {c : CompileClaim} {certText : String} {typecheck : Bool} :
    checkClaim cfg envBytes equations c certText typecheck = .ok () ↔
      verifyBytes cfg envBytes equations c certText typecheck = true := by
  unfold checkClaim
  cases verifyBytes cfg envBytes equations c certText typecheck <;> simp [pure, Except.pure]

/-- Construct a `CompileClaim` from raw `.ixe` environment bytes and sidecar equations JSON
in a single ingress + compilation pass without redundant re-ingress or double recheck (`A4-12`).
Defaults to `typecheck := true` (`S4`, `A1-6`). -/
def makeClaim (cfg : Recheck.Config) (envBytes : ByteArray) (equations : Lean.Json)
    (mode : Compiler.RcMode := .auto) (typecheck : Bool := true) :
    Except String (CompileClaim × String × ByteArray) := do
  let input ← (Recheck.ingress envBytes equations cfg.names typecheck).mapError (·.render)
  (produce cfg input mode).mapError (·.render)

end CompileClaim

end IxCC
