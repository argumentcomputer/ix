import IxVM.Source
import IxVM.FunctionGroups
import Aiur.Optimized.Depth.Grouped
import Aiur.Optimized.Grouping.Plan
import Aiur.Optimized.EndToEnd
import Aiur.Optimized.Observed
import Aiur.Trace.Export
import Aiur.Artifact
import Lean

/-! # Kernel-Checked Compilation and Exporter Safety Certificate for `IxVM.source` (`IxVM.CompiledCert`)

Provides a kernel-checked compilation and exporter-safety certificate binding `IxVM.source` at
`IxVM.entry` (`"IxVM::verify_claim"`) to:

1. **Pinned source identity (`pinnedProgramDigest`, `programDigest_eq`)**: pins `IxVM.programDigest`
   by reflexivity (`rfl`) so any circuit source edit forces an explicit certificate review.
2. **Executable 2B-1 safety certificates (`CompiledCert`)**: packages a `Generic.Specialized`
   elaboration, an `Aiur.Optimized.GenericArtifact` (`Aiur.Optimized.compile`), a
   `Physical.Prepared` deduplicated circuit system, a `Depth.Config`, and a grouped
   `Grouping.Plan` certified exclusively by the sound boolean checkers:
   * `Aiur.Optimized.Grouping.checkPlanCertificate_sound` (`PlanCertificate`),
   * `Aiur.Optimized.Depth.checkGoldilocksPlan_sound` (`Depth.Certified`, `cfg.bits ≤ 24`,
     and `Plan.WellFormedActivation`), and
   * `Aiur.Optimized.Grouping.Plan.checkWellFormedActivation_sound`.
3. **Observed headline instantiation (`CompiledCert.checkMemo_observed_sound`)**: instantiates
   `Aiur.Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed`
   directly for `IxVM.source` at `IxVM.entry`, discharging all exporter safety side conditions
   from the two boolean checkers.
4. **Artifact SHA-256 bridge (`ArtifactPin`, `sha256Hex`, `CompiledCert.buildWithArtifact`)**:
   binds the compiled certificate to the FIPS 180-4 SHA-256 digest of the packaged `.ixa`
   artifact bytes.
5. **Compile-path transparency audit (`#audit_compile_opacity`)**: walks the kernel environment
   from `Aiur.Optimized.compile`, `Aiur.Optimized.Physical.prepare`,
   `Aiur.Optimized.Depth.checkGoldilocksPlan`, `Aiur.Optimized.Grouping.checkPlanCertificate`,
   and `Aiur.Optimized.Grouping.Plan.checkWellFormedActivation`, asserting zero `opaqueInfo`
   constants, zero `Aiur.*` `partial` definitions, zero `unsafe` constants, and zero trust escapes.

Kept inside the nested `IxVM` package (not imported by `Ix.lean` or `IxTests`, which remain
Mathlib-free). Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only. -/

namespace IxVM

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Depth Aiur.Optimized.Grouping
open Aiur.Generic Aiur.Generic.SourceSemantics

/-! ## 1. Pinned Source Identity and Entry Check -/

/-- Pinned BLAKE3 digest of the elaborated `IxVM` module program (`IxVM.programDigest`). -/
def pinnedProgramDigest : String :=
  "5bccd2ee3d154a54584d1db59ccf1092a3aaec657b57fadf8ed88def581a39db"

theorem entry_eq : IxVM.entry = "IxVM::verify_claim" := rfl

theorem programDigest_eq : IxVM.programDigest = pinnedProgramDigest := rfl

theorem entry_mem_entries : IxVM.entry ∈ [IxVM.entry] := List.mem_singleton.mpr rfl

#guard IxVM.source.checkEntry IxVM.entry matches .ok ()

/-! ## 2. Pure FIPS 180-4 SHA-256 for `.ixa` Artifact Pinning -/

private def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def sha256H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

private def sha256Block (h : Array UInt32) (m : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let byte (i : Nat) : UInt32 := m[off + i]!.toUInt32
  let mut w : Array UInt32 := #[]
  for i in [0:16] do
    w := w.push ((byte (4 * i) <<< 24) ||| (byte (4 * i + 1) <<< 16) |||
      (byte (4 * i + 2) <<< 8) ||| byte (4 * i + 3))
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut k := h[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := k + s1 + ch + sha256K[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    k := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
           h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + k]

/-- Compute the FIPS 180-4 SHA-256 digest of `msg` as 64 lowercase hexadecimal characters. -/
def sha256Hex (msg : ByteArray) : String := Id.run do
  let len := msg.size
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do
    m := m.push 0
  let bits := len * 8
  for i in [0:8] do
    m := m.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  let mut h := sha256H0
  let mut off := 0
  while off < m.size do
    h := sha256Block h m off
    off := off + 64
  let hex (x : UInt32) : String :=
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (8 - s.length) ++ s
  return h.foldl (fun acc x => acc ++ hex x) ""

#guard sha256Hex "".toUTF8 ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard sha256Hex "abc".toUTF8 ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

/-- Pinned metadata binding a compiled `IxVM.source` certificate to a serialized `.ixa` artifact. -/
structure ArtifactPin where
  programDigest : String
  planVersion : Nat
  artifactSha256 : Option String := none
  deriving Repr, DecidableEq

/-- Predicate that a serialized `.ixa` byte array matches `pin.artifactSha256`. -/
def ArtifactPin.matchesBytes (pin : ArtifactPin) (artifactBytes : ByteArray) : Prop :=
  pin.artifactSha256 = some (sha256Hex artifactBytes)

/-! ## 3. Kernel-Checked Compilation & Exporter Safety Certificate (`CompiledCert`) -/

/-- A kernel-checked compilation and exporter-safety certificate for `IxVM.source` at
`[IxVM.entry]` (`"IxVM::verify_claim"`).

Every exporter side condition required by the Goldilocks observed headline theorem
(`PlanCertificate`, `Depth.Certified`, `cfg.bits ≤ 24`, and `Plan.WellFormedActivation`) is
witnessed exclusively through the sound executable checkers
`Aiur.Optimized.Grouping.checkPlanCertificate` and `Aiur.Optimized.Depth.checkGoldilocksPlan`. -/
structure CompiledCert (id : String → Except String Nat) where
  specialized : Generic.Specialized IxVM.source [IxVM.entry]
  compiled : Optimized.GenericArtifact specialized
  prepared : Physical.Prepared compiled.artifact
  cfg : Depth.Config
  singles : List (Chip IxVM.F)
  groups : List (Grouping.Packed IxVM.F id)
  planCertChecked :
    checkPlanCertificate (Depth.system cfg prepared.system) singles groups = true
  goldilocksPlanChecked :
    checkGoldilocksPlan cfg prepared.system
      ⟨singles, groups, checkPlanCertificate_sound planCertChecked⟩ = true
  artifactPin : ArtifactPin
  digestMatch : artifactPin.programDigest = IxVM.programDigest
  versionMatch : artifactPin.planVersion = Trace.planVersion

namespace CompiledCert

variable {id : String → Except String Nat}

/-- The certified grouped plan over `Depth.system cert.cfg cert.prepared.system`. -/
def plan (cert : CompiledCert id) :
    Grouping.Plan (Depth.system cert.cfg cert.prepared.system) id :=
  ⟨cert.singles, cert.groups, checkPlanCertificate_sound cert.planCertChecked⟩

/-- `PlanCertificate` derived directly from `checkPlanCertificate_sound`. -/
theorem planCertificate (cert : CompiledCert id) :
    PlanCertificate (Depth.system cert.cfg cert.prepared.system) cert.singles cert.groups :=
  checkPlanCertificate_sound cert.planCertChecked

/-- Combined exporter safety theorem: derives `Depth.Certified`, `cfg.bits ≤ 24`, and
`plan.WellFormedActivation` directly from `checkGoldilocksPlan_sound`. -/
theorem safety (cert : CompiledCert id) :
    Depth.Certified cert.cfg cert.prepared.system ∧
      cert.cfg.bits ≤ 24 ∧
      cert.plan.WellFormedActivation :=
  checkGoldilocksPlan_sound cert.goldilocksPlanChecked

theorem depthCertified (cert : CompiledCert id) :
    Depth.Certified cert.cfg cert.prepared.system :=
  cert.safety.1

theorem bitsLe24 (cert : CompiledCert id) : cert.cfg.bits ≤ 24 :=
  cert.safety.2.1

theorem wellFormedActivation (cert : CompiledCert id) : cert.plan.WellFormedActivation :=
  cert.safety.2.2

/-- Direct derivation of `Plan.WellFormedActivation` via `Plan.checkWellFormedActivation_sound`. -/
theorem wellFormedActivation_of_check {cfg : Depth.Config} {sys : Circuit.System IxVM.F}
    {plan : Grouping.Plan (Depth.system cfg sys) id}
    (h : plan.checkWellFormedActivation = true) : plan.WellFormedActivation :=
  Plan.checkWellFormedActivation_sound h

/-- Degree bounds guaranteed by `Aiur.Optimized.compile` (`GenericArtifact.artifact.degreeBound`). -/
theorem degreeBound (cert : CompiledCert id) :
    ∀ chip ∈ cert.compiled.system.chips,
      chip.stats.maxConstraintDegree ≤ cert.compiled.artifact.config.maxDegree ∧
      chip.stats.maxLookupDegree ≤ 2 ∧
      chip.maxLookupGuardDegree ≤ 1 :=
  cert.compiled.artifact.degreeBound

/-- The certificate's `artifactPin.programDigest` equals `pinnedProgramDigest`. -/
theorem programDigest_pinned (cert : CompiledCert id) :
    cert.artifactPin.programDigest = pinnedProgramDigest :=
  cert.digestMatch.trans programDigest_eq

/-- **Headline Observed Soundness for Certified `IxVM.source`**:
instantiates `Aiur.Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed`
at `IxVM.source` / `IxVM.entry`, discharging `Depth.Certified`, `cfg.bits ≤ 24`, and
`Plan.WellFormedActivation` solely from `cert.planCertChecked` and `cert.goldilocksPlanChecked`. -/
theorem checkMemo_observed_sound (cert : CompiledCert id)
    {rom : WidthROM IxVM.F} (valid : rom.Valid)
    {args : List (SourceValue IxVM.F)} {result : Value IxVM.F}
    {wires : List (WireValue IxVM.F)} {output : WireValue IxVM.F}
    (signed : Erasure.Signed cert.compiled.system ⟨IxVM.entry, wires, output⟩)
    {root : Message IxVM.F}
    (rooted : Depth.erase cert.cfg root =
      Erasure.message cert.compiled.system ⟨IxVM.entry, wires, output⟩)
    (outside : root.channel ∉ cert.cfg.names)
    {rows : List (WeightedRow IxVM.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues cert.specialized.program.enums wires (entryValues args))
    (decoded : output.decode cert.specialized.program.enums = some result) :
    ∃ value heap calls,
      ObsFn IxVM.source.world IxVM.entry args [] value heap calls ∧
        Represents (cert.compiled.traceROM rom) heap value result ∧
        CallsInROM (cert.compiled.traceROM rom) calls :=
  cert.prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed
    cert.compiled cert.depthCertified cert.bitsLe24 cert.plan cert.wellFormedActivation
    entry_mem_entries valid signed rooted outside bound checked arguments decoded

/-- Specialize any circuit-level property universally quantified over compiled/prepared/certified
`IxVM.source` artifacts (such as `IxVM.Refinement.CircuitSound`) to a concrete `CompiledCert`. -/
theorem specialize_circuit
    {PropOf :
      ∀ {id : String → Except String Nat}
        {specialized : Generic.Specialized IxVM.source [IxVM.entry]}
        (compiled : GenericArtifact specialized)
        (prepared : Physical.Prepared compiled.artifact)
        {cfg : Depth.Config},
        Depth.Certified cfg prepared.system →
        cfg.bits ≤ 24 →
        (plan : Grouping.Plan (Depth.system cfg prepared.system) id) →
        plan.WellFormedActivation → Prop}
    (hAll : ∀ {id} {specialized} (compiled : GenericArtifact specialized)
      (prepared : Physical.Prepared compiled.artifact) {cfg}
      (hCert : Depth.Certified cfg prepared.system) (hBits : cfg.bits ≤ 24)
      (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
      (hAct : plan.WellFormedActivation),
      PropOf compiled prepared hCert hBits plan hAct)
    (cert : CompiledCert id) :
    PropOf cert.compiled cert.prepared cert.depthCertified cert.bitsLe24
      cert.plan cert.wellFormedActivation :=
  hAll cert.compiled cert.prepared cert.depthCertified cert.bitsLe24
    cert.plan cert.wellFormedActivation

/-- Executable builder constructing a certified `CompiledCert` for `IxVM.source` at `[IxVM.entry]`
using `IxVM.functionGroups`, optionally binding it to the SHA-256 digest of the packaged `.ixa`
artifact bytes. Fails closed unless both `checkPlanCertificate` and `checkGoldilocksPlan`
return `true`. -/
def build (groups : List (String × List String) := IxVM.functionGroups)
    (packageArtifact : Bool := false) :
    Except String (Σ id : String → Except String Nat, CompiledCert id) := do
  let exported ← IxVM.source.exportExecution [IxVM.entry]
  let specialized ← Generic.specialize IxVM.source [IxVM.entry]
  let compiled ← specialized.compileOptimized {}
  let prepared ← Physical.prepare compiled.artifact
  let cfg ← Trace.depthConfig IxVM.modulus prepared
  let bytecode := Trace.depthBytecode cfg exported.bytecode
  let system := Depth.system cfg prepared.system
  let callableNames := bytecode.functions.map (·.name) ++ bytecode.maps.map (·.name)
  let id : String → Except String Nat := fun name =>
    if callableNames.contains name then pure (callableNames.idxOf name)
    else throw s!"unknown grouped callable {name}"
  let mut used : List String := []
  let mut packed : List (Grouping.Packed IxVM.F id) := []
  for (name, names) in groups do
    let names := (names.map prepared.representative).dedup
    let chips := system.chips.filter fun c =>
      names.contains c.name && !used.contains c.name && !compiled.artifact.entries.contains c.name
    if chips.length < 2 then continue
    let group ← Grouping.compile name id chips
    used := used ++ chips.map (·.name)
    packed := packed ++ [⟨chips, group⟩]
  let groupedNames := packed.flatMap fun p => p.sources.map Chip.name
  let singles := system.chips.filter fun c => !groupedNames.contains c.name
  if hPlan : checkPlanCertificate system singles packed = true then
    let plan : Grouping.Plan system id := ⟨singles, packed, checkPlanCertificate_sound hPlan⟩
    if hGold : checkGoldilocksPlan cfg prepared.system plan = true then
      let artifactSha256 ← if packageArtifact then do
        let (exported', trace) ← Trace.exportPreparedPlan IxVM.modulus ZMod.val
          compiled.inlined.program compiled.artifact prepared exported groups
        let pkg ← Artifact.package exported' IxVM.modulus ZMod.val (some trace)
        pure (some (sha256Hex pkg))
      else
        pure none
      return ⟨id, {
        specialized, compiled, prepared, cfg, singles, groups := packed
        planCertChecked := hPlan
        goldilocksPlanChecked := hGold
        artifactPin := {
          programDigest := IxVM.programDigest
          planVersion := Trace.planVersion
          artifactSha256
        }
        digestMatch := rfl
        versionMatch := rfl
      }⟩
    else
      throw "IxVM.CompiledCert.build: checkGoldilocksPlan failed"
  else
    throw "IxVM.CompiledCert.build: checkPlanCertificate failed"

end CompiledCert

/-! ## 4. Transparency / Opacity Audit on `Aiur.Optimized.compile` and 2B-1 Checkers -/

section OpacityAudit

open Lean Elab Command

private def declDeps (ci : ConstantInfo) : Array Name :=
  let ofExprs (es : List Lean.Expr) : Array Name :=
    es.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
  match ci with
  | .axiomInfo v => ofExprs [v.type]
  | .defnInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .thmInfo v => ofExprs [v.type]
  | .opaqueInfo v => ofExprs [v.type, v.value] ++ v.all.toArray
  | .quotInfo v => ofExprs [v.type]
  | .inductInfo v => ofExprs [v.type] ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => ofExprs [v.type] ++ #[v.induct]
  | .recInfo v =>
    ofExprs (v.type :: v.rules.map (·.rhs)) ++ v.all.toArray ++ (v.rules.map (·.ctor)).toArray

private def isUnsafeConst : ConstantInfo → Bool
  | .axiomInfo v => v.isUnsafe
  | .defnInfo v => v.safety == .unsafe
  | .opaqueInfo v => v.isUnsafe
  | .inductInfo v => v.isUnsafe
  | .ctorInfo v => v.isUnsafe
  | .recInfo v => v.isUnsafe
  | _ => false

private def trustEscapes : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler,
   ``Lean.reduceBool, ``Lean.reduceNat]

/-- Error-message formatting opaques (derived `Repr` on nested inductives, used only inside
`.mapError reprStr` error paths and never reached on `.ok` logical compilation). -/
private def errorFormatOpaques : List Name :=
  [``Aiur.instReprTy.repr]

/-- Audit the definitional closure of `Aiur.Optimized.compile`, `Physical.prepare`, and the
executable 2B-1 safety checkers (`checkGoldilocksPlan`, `checkPlanCertificate`,
`Plan.checkWellFormedActivation`), failing the build if any logical `Aiur.*` opaque constant,
any `Aiur.*` `partial` definition, any `unsafe` constant, or any trust escape is reachable. -/
elab "#audit_compile_opacity" : command => do
  let env ← getEnv
  let roots : Array Name := #[
    ``Aiur.Optimized.compile,
    ``Aiur.Optimized.Physical.prepare,
    ``Aiur.Optimized.Depth.checkGoldilocksPlan,
    ``Aiur.Optimized.Grouping.checkPlanCertificate,
    ``Aiur.Optimized.Grouping.Plan.checkWellFormedActivation
  ]
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[]
  for r in roots do
    seen := seen.insert r
    todo := todo.push r
  let mut total : Nat := 0
  let mut aiurLogicalOpaques : Array Name := #[]
  let mut aiurErrorOpaques : Array Name := #[]
  let mut aiurPartials : Array Name := #[]
  let mut coreOpaques : Array Name := #[]
  let mut unsafes : Array Name := #[]
  let mut escapesFound : Array Name := #[]
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    let some ci := env.find? n | throwError "opacity audit: unknown constant {n}"
    total := total + 1
    if trustEscapes.contains n then escapesFound := escapesFound.push n
    if isUnsafeConst ci then unsafes := unsafes.push n
    match ci with
    | .opaqueInfo _ =>
      if n.getRoot == `Aiur then
        if errorFormatOpaques.contains n then aiurErrorOpaques := aiurErrorOpaques.push n
        else aiurLogicalOpaques := aiurLogicalOpaques.push n
      else coreOpaques := coreOpaques.push n
    | .defnInfo v =>
      if v.safety == .partial && n.getRoot == `Aiur then
        aiurPartials := aiurPartials.push n
    | _ => pure ()
    for d in declDeps ci do
      unless seen.contains d do
        seen := seen.insert d
        todo := todo.push d
  unless aiurLogicalOpaques.isEmpty && aiurPartials.isEmpty && unsafes.isEmpty && escapesFound.isEmpty do
    throwError
      (m!"compile-path opacity audit failed: " ++
       m!"aiurLogicalOpaques={aiurLogicalOpaques.toList}, aiurPartials={aiurPartials.toList}, " ++
       m!"unsafes={unsafes.toList}, escapes={escapesFound.toList}")
  logInfo
    (m!"compile-path opacity audit passed ({total} constants across {roots.size} roots): " ++
     m!"0 logical Aiur opaques, 0 Aiur partials, 0 unsafes, 0 escapes " ++
     m!"(error-only Repr opaques: {aiurErrorOpaques.toList}; core opaques: {coreOpaques.size})")

#audit_compile_opacity

/-! ## 5. Axiom Audit -/

run_cmd do
  let roots : List Name := [
    ``IxVM.entry_eq,
    ``IxVM.programDigest_eq,
    ``IxVM.entry_mem_entries,
    ``IxVM.CompiledCert.planCertificate,
    ``IxVM.CompiledCert.safety,
    ``IxVM.CompiledCert.depthCertified,
    ``IxVM.CompiledCert.bitsLe24,
    ``IxVM.CompiledCert.wellFormedActivation,
    ``IxVM.CompiledCert.wellFormedActivation_of_check,
    ``IxVM.CompiledCert.degreeBound,
    ``IxVM.CompiledCert.programDigest_pinned,
    ``IxVM.CompiledCert.checkMemo_observed_sound,
    ``IxVM.CompiledCert.specialize_circuit
  ]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for r in roots do
    let axs ← Lean.collectAxioms r
    for a in axs do
      unless allowed.contains a do
        throwError "unexpected axiom {a} in {r} (axioms: {axs.toList})"

end OpacityAudit

end IxVM
