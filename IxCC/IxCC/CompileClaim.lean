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

1. **Wire Format Alignment**:
   - `CompileClaim.toClaimBytes` serializes the exact 4-byte `Ix.Claim.put (.compile ...)`
     header `#[0xE8, 0x05, 0x04, 0x06]` (`putTagN 4 0xE 13` ++ `putScope VALIDATOR_COMPILE_V1`)
     followed by `toPayloadBytes` (`env` 32B ++ `target` 32B ++ `[policy.toUInt8]` 1B ++
     `n0Bytes abiArity` 1..9B ++ `elfHash` 32B), totaling 102 bytes when `abiArity < 128`.
     `abiArity` uses ix's TagN code at flag width 0 (`Ixon.putTagN 0 0`), so the
     bytes agree with `Ix.Claim.ser` for every arity below `2 ^ 64`.
   - `CompileClaim.ofClaimBytes` parses and validates the canonical wire envelope
     via `Ixon.runGet`, rejecting invalid or overflowing arity codes and trailing bytes.
   - Global `Coe (List UInt8) ByteArray` has been removed.

2. **Verified Ingress, Policy Unification & Root Observability**:
   - `verifyBytes`, `checkClaim`, and `makeClaim` default to `typecheck := true`,
     running `Ixon.V3.Tc.checkEnv` during `Recheck.ingress`.
   - `verifyProgram` requires `c.abiArity < 2 ^ 64`, verifies that the target root
     declaration is monomorphic with all-`Nat` parameters (`rootParamsAllNat`),
     and requires a readback type, so the value clause observes the root's result
     (`isImmortalViewType` on the `.immortal` and `.zeroRc` paths; `root.ty.isSome`
     on the `.plainRc` path).
   - `.zeroRc` verification uses `Own.Plain.selectRcPolicyForSrc a.src a.front.fir == .zeroRc`
     (matching `produceAuto` and `produce`), and `makeClaim` / `produce` avoid
     redundant re-ingress and double recheck.
   - With the default `.auto` mode, `produce` and `makeClaim` compile under the
     immortal policy when plain RC is selected but its certificate cannot be
     produced or is refused (`produceAuto`'s `.immortal` fallback); the claim's
     `policy` is the policy actually compiled under.

3. **Proof Separation**:
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

/-- Well-formedness predicate for a `CompileClaim`: `abiArity < 2 ^ 64`, the range of
ix's `UInt64` field and of its `N0` code (`Ixon.Address` fields already carry
`hash_size : hash.size = 32`). -/
def WellFormed (c : CompileClaim) : Prop :=
  c.abiArity < 2 ^ 64

/-- Decidable check for `CompileClaim.WellFormed`. -/
def checkWellFormed (c : CompileClaim) : Bool :=
  decide (c.abiArity < 2 ^ 64)

/-- `Ix.Claim.put (.compile ...)` Tag4 header bytes (`putTagN 4 0xE 13 = #[0xE8, 0x05]`).
Values 11 (`E8 03`) and 12 (`E8 04`) of the claim tag space are ix's role-binding
section and literal-class preimage, not claims. -/
def CLAIM_TAG4_COMPILE : ByteArray := ByteArray.mk #[0xE8, 0x05]

/-- Scope domain tag for object format claims (`OBJECT_FORMAT = 4`). -/
def OBJECT_FORMAT : UInt8 := 0x04

/-- Validator ID for `CompileClaim` v1 (`6`, matching `Ix.Claim.VALIDATOR_COMPILE_V1`). -/
def VALIDATOR_COMPILE_V1 : UInt8 := 0x06

/-- Claim variant index (`13`, encoded in `CLAIM_TAG4_COMPILE`). -/
def VARIANT_COMPILE_CLAIM : UInt8 := 13

/-- The exact 4-byte `Ix.Claim.put (.compile ...)` wire header:
`#[0xE8, 0x05, 0x04, 0x06]` (`putTagN 4 0xE 13` ++ `putScope VALIDATOR_COMPILE_V1`). -/
def validatorHeader : ByteArray :=
  ByteArray.mk #[0xE8, 0x05, OBJECT_FORMAT, VALIDATOR_COMPILE_V1]

/-! ### `abiArity`: ix's `N0` integer code

`Ix.Claim` writes `abiArity` with the Ixon v4 TagN code at flag width 0
(`putTagN 0 0`, `getTagN 0`), so this module writes and reads that code, not
the v2 `Tag0` of `IxCC.Ixon.Serialize` (the two agree only below 128). The
rungs are: one byte below 128; a header `0x80 + (v - 128) / 256` and one byte
below 16512; then a header `0xC0`–`0xC3` and 2, 3, 4 or 8 little-endian bytes
of `v` minus the rung's start (16512, 82048, 16859264, 4311826560). Headers
`0xC4`–`0xFF` and values reaching `2 ^ 64` are refused. -/

/-- `width` little-endian bytes of `x`, low byte first. -/
def leBytes (x : Nat) : Nat → List UInt8
  | 0 => []
  | w + 1 => UInt8.ofNat x :: leBytes (x / 256) w

/-- The value of little-endian bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- Header byte of the `N0` code of `v`. -/
def n0Header (v : Nat) : UInt8 :=
  if v < 128 then UInt8.ofNat v
  else if v < 16512 then UInt8.ofNat (128 + (v - 128) / 256)
  else if v < 82048 then 0xC0
  else if v < 16859264 then 0xC1
  else if v < 4311826560 then 0xC2
  else 0xC3

/-- Bytes after the header of the `N0` code of `v`. -/
def n0Payload (v : Nat) : List UInt8 :=
  if v < 128 then []
  else if v < 16512 then leBytes ((v - 128) % 256) 1
  else if v < 82048 then leBytes (v - 16512) 2
  else if v < 16859264 then leBytes (v - 82048) 3
  else if v < 4311826560 then leBytes (v - 16859264) 4
  else leBytes (v - 4311826560) 8

/-- The `N0` code of `v`: `Ixon.runPut (Ixon.putTagN 0 0 v)` for `v < 2 ^ 64`. -/
def n0Bytes (v : Nat) : ByteArray :=
  Ixon.u8Bytes (n0Header v) ++ ⟨(n0Payload v).toArray⟩

/-- Payload width of an `N0` header byte; `none` for the invalid codes `C4`–`FF`. -/
def n0Width (header : UInt8) : Option Nat :=
  if header.toNat < 128 then some 0
  else if header.toNat < 192 then some 1
  else if header.toNat = 192 then some 2
  else if header.toNat = 193 then some 3
  else if header.toNat = 194 then some 4
  else if header.toNat = 195 then some 8
  else none

/-- The value an `N0` header and payload denote. -/
def n0Value (header : UInt8) (payload : List UInt8) : Nat :=
  if header.toNat < 128 then header.toNat
  else if header.toNat < 192 then 128 + (header.toNat - 128) * 256 + leValue payload
  else if header.toNat = 192 then 16512 + leValue payload
  else if header.toNat = 193 then 82048 + leValue payload
  else if header.toNat = 194 then 16859264 + leValue payload
  else 4311826560 + leValue payload

/-- The end of `getN0`, after its header and payload: values reaching `2 ^ 64`
are refused. The re-encoding check never fails for this bijective code; it
makes canonicity immediate. -/
def n0Finish (header : UInt8) (payload : ByteArray) : Ixon.GetM Nat :=
  if n0Value header payload.data.toList < 2 ^ 64 ∧
      n0Bytes (n0Value header payload.data.toList) = Ixon.u8Bytes header ++ payload then
    pure (n0Value header payload.data.toList)
  else throw "CompileClaim: abiArity exceeds UInt64"

/-- Strict reader of the `N0` code (`Ixon.getTagN 0`). -/
def getN0 : Ixon.GetM Nat :=
  Ixon.getU8 >>= fun header =>
    match n0Width header with
    | some width => Ixon.getBytes width >>= n0Finish header
    | none => throw "CompileClaim: invalid abiArity code"

/-- Monadic payload reader in `Ixon.GetM` for `CompileClaim`. -/
def getPayloadM : Ixon.GetM CompileClaim := do
  let env ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
  let target ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
  let polByte ← Ixon.getU8
  let some policy := CompilePolicy.ofUInt8? polByte |
    throw "CompileClaim: invalid policy byte"
  let abiArity ← getN0
  let elfHash ← (Ixon.Serialize.get : Ixon.GetM Ixon.Address)
  return {
    env
    target
    policy
    abiArity
    elfHash
  }

/-- Monadic full-envelope reader in `Ixon.GetM` for `CompileClaim`. -/
def getClaimM : Ixon.GetM CompileClaim := do
  let hdr ← Ixon.getBytes 4
  if hdr != validatorHeader then
    throw "CompileClaim: invalid validator header"
  getPayloadM

/-- Serialize the `CompileClaim` payload (`env ++ target ++ [policy.toUInt8] ++ n0Bytes abiArity ++ elfHash`),
matching `Ix.Claim.CompileClaim.put` byte-for-byte (98 bytes when `abiArity < 128`). -/
def toPayloadBytes (c : CompileClaim) : ByteArray :=
  c.env.hash ++
    c.target.hash ++
    Ixon.u8Bytes c.policy.toUInt8 ++
    n0Bytes c.abiArity ++
    c.elfHash.hash

/-- Deserialize a `CompileClaim` payload produced by `toPayloadBytes`. -/
def ofPayloadBytes (bs : ByteArray) : Option CompileClaim :=
  (Ixon.runGet getPayloadM bs).toOption

/-- Serialize the full `CompileClaim` wire envelope (`#[0xE8, 0x05, 0x04, 0x06] ++ c.toPayloadBytes`),
matching `Ix.Claim.ser (.compile ...)` byte-for-byte (102 bytes when `abiArity < 128`). -/
def toClaimBytes (c : CompileClaim) : ByteArray :=
  validatorHeader ++ c.toPayloadBytes

/-- Deserialize a full `CompileClaim` wire envelope produced by `toClaimBytes`. -/
def ofClaimBytes (bs : ByteArray) : Option CompileClaim :=
  (Ixon.runGet getClaimM bs).toOption

/-- Pure BLAKE3 commitment digest over `c.toClaimBytes`. -/
def commit (c : CompileClaim) : Ixon.Address :=
  Ixon.Address.blake3Pure c.toClaimBytes

/-- Check that a readback type is a scalar (`Nat`) or an enumeration whose
signature row lists only field-less constructors: the shapes `Rt.tagify`
(`Front.view` on the `.immortal` / `.zeroRc` path) can read back. No theorem
states that `Rt.tagify` succeeds on every value of such a type: a constructor
must also be in the table with a tag inside the row (`Recheck.view_ctor0`). -/
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
and a scalar/enum readback type (`isImmortalViewType`), so that the value clause
observes its result. -/
def checkImmortalRoot (src : Src.Program) (root : Recheck.Root) : Bool :=
  rootParamsAllNat src root &&
    match root.ty with
    | some (sig, ty) => isImmortalViewType sig ty
    | none => false

/-- Check that a root on the `.plainRc` path has all-`Nat` parameters and a
discovered first-order readback signature (`root.ty.isSome`). -/
def checkPlainRcRoot (src : Src.Program) (root : Recheck.Root) : Bool :=
  rootParamsAllNat src root && root.ty.isSome

/-- Verify a `CompileClaim` against a `Src.Program` (precondition: ingested, or passed
`Recheck.checkSrc`, as for `Recheck.run`) and serialized
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
`Ixon.V3.Tc.checkEnv` validates the decoded environment at ingress
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

/-- Check a `CompileClaim` against a `Src.Program` (precondition: ingested, or passed
`Recheck.checkSrc`, as for `Recheck.run`) and serialized certificate. -/
def checkClaimProgram (cfg : Recheck.Config) (P : Src.Program) (c : CompileClaim)
    (certText : String) : Except String Unit := do
  unless verifyProgram cfg P c certText do
    throw "CompileClaim.checkClaimProgram: claim verification failed"

/-- Check a `CompileClaim` from raw `.ixe` environment bytes, sidecar equations JSON,
and serialized certificate `certText`. Defaults to `typecheck := true`. -/
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
in a single ingress + compilation pass without redundant re-ingress or double recheck.
Defaults to `typecheck := true`. -/
def makeClaim (cfg : Recheck.Config) (envBytes : ByteArray) (equations : Lean.Json)
    (mode : Compiler.RcMode := .auto) (typecheck : Bool := true) :
    Except String (CompileClaim × String × ByteArray) := do
  let input ← (Recheck.ingress envBytes equations cfg.names typecheck).mapError (·.render)
  (produce cfg input mode).mapError (·.render)

end CompileClaim

end IxCC
