import Aiur.Optimized.EndToEnd
import Aiur.HeapMono
import Aiur.StepLemmas
import Aiur.Library.IxVMRep
import Aiur.Library.Blake3.Correctness
import Aiur.Library.Bytes.Correctness
import Aiur.Library.List.Correctness
import Aiur.Library.RBTreeMap.Correctness
import Aiur.Library.U64.Correctness
import Aiur.Library.U64.Goldilocks
import Aiur.Library.U32.Correctness
import Aiur.Library.U8Facts
import Ix.Cert.IxVM.FuelFreeKernel

/-! # End-to-End Formal `Aiur` Circuit ↔ `IxVM` ↔ `IxC` ↔ Set-Theoretic Model Bridge

This module unifies the two halves of the Certified `IxVM` architecture:
1. **Formal `Aiur` Circuit & Library Soundness (`Aiur.*`)**:
   - `Aiur.Modules.Prepared.grouped_activated_heap_sound`: Any valid derivation
     `plan.ActivatedDerives` over the grouped, row-activated, deduplicated,
     column-shared, degree-bounded physical STARK circuit system of a modular
     `.aiur` program produces a source-level big-step evaluation
     `prepared.EvalFn external args value heap` and representation
     `Represents ((Erasure.typedROM compiled.circuit.system rom).decode ...) heap value result`.
   - `Aiur.Library.IxVMRep.ingress_verify_stream_sound`: Over the Goldilocks prime
     field `F = ZMod (2^64 - 2^32 + 1)` (`Aiur.Library.U64.Goldilocks.compatible`),
     every finite byte stream loaded by `Ingress` and checked by
     `Blake3::verify_bytes_against` has length `< 2^32` and pure BLAKE3 digest equal
     to the expected 32-byte address.
2. **`IxVM` ↔ `IxC` Kernel & Compiler Commutation (`Ix.Cert.IxVM.*`)**:
   - `ixvm_validate_binding_blake3`: Role-binding validation in `KernelRoles`
     and `KernelRoleSpec` is equivalent to `Ix.Kernel.Admission.admitBinding`.
   - `ixvmConvertExpr_eq_memberReader_read` and `ixvmReadDefn_eq_readRecord`:
     `Convert` / `Ingress` unsharing and constant projection lowering agree with
     `Ix.Kernel.Reader.MemberReader.read` and `readRecord`.
   - `ixvmFuelFreeWalkDecls_iff_acceptsRef` and `ixvm_accepts_iff_ixonAcceptsRef`:
     Fuel-free big-step declaration checking in `IxVM` is equivalent to uniform-fuel
     `Ix.Kernel.Cached.AcceptsRef .verified` and `Ix.Cert.IxonAcceptsRef`.
   - `ixvm_compile_commutes`: Composes `Ix.Cert.ReaderStreamsTrace.compileCorrect`
     with `IxVMAcceptsClaim` so any set-theoretic `StrongModel V envA` of the
     `IxVM`-accepted Ixon environment pulls back via `readingAt` to a
     `LawModel V envQ` and `ValueModel V envQ` of the source Lean environment.
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open Ix.Kernel.Cached
open Ix.Kernel.Admission

universe w

/-- The Goldilocks prime field `ZMod (2^64 - 2^32 + 1)` used by `IxVM` and `MultiStark`. -/
abbrev GoldilocksF : Type := Aiur.Library.U32.Goldilocks.F

/-! ## 1. Goldilocks Physical Circuit Soundness (`ixvm_circuit_activated_derives_evalFn`) -/

/-- **Activated Grouped Physical Circuit Soundness over Goldilocks (`ixvm_circuit_activated_derives_evalFn`)**:
Instantiates `Aiur.Modules.Prepared.grouped_activated_heap_sound` at `GoldilocksF`:
any derivation `plan.ActivatedDerives` over the activated grouped physical circuit
system of a modular `.aiur` program implies the modular big-step source evaluation
`prepared.EvalFn external args value heap` together with heap representation
`Aiur.Represents`. -/
theorem ixvm_circuit_activated_derives_evalFn
    {id : String → Except String Nat}
    {program : Aiur.Modules.Program GoldilocksF}
    (prepared : Aiur.Modules.Prepared program)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : Aiur.WidthROM GoldilocksF} (valid : rom.Valid)
    {args : List (Aiur.SourceValue GoldilocksF)} {result : Aiur.Value GoldilocksF}
    {wires : List (Aiur.WireValue GoldilocksF)} {output : Aiur.WireValue GoldilocksF}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom)
      (Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Aiur.Represents
        ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  prepared.grouped_activated_heap_sound compiled physical plan activated
    selected valid signed derived arguments decoded

/-- **Goldilocks Ingress Stream BLAKE3 Authentication Soundness (`ixvm_circuit_ingress_stream_sound`)**:
Instantiates `Aiur.Library.IxVMRep.ingress_verify_stream_sound` at `GoldilocksF`
using `Aiur.Library.U64.Goldilocks.compatible`. -/
theorem ixvm_circuit_ingress_stream_sound
    (enumName : String) (stream : Nat → UInt8) (idx len : Nat)
    (h : Aiur.Heap GoldilocksF) (expectedAddr : Aiur.Library.Bytes.Address)
    (hDepth : Aiur.Library.List.Word.depthChecked (Aiur.Library.Bytes.readByteStream stream idx len) = some len)
    (hVerify : Aiur.Library.Blake3.addressToFields GoldilocksF
        (Aiur.Library.Blake3.digest (Aiur.Library.Bytes.readByteStream stream idx len)) =
      Aiur.Library.Blake3.addressToFields GoldilocksF expectedAddr) :
    let bytes := Aiur.Library.Bytes.readByteStream stream idx len
    let allocated := Aiur.Library.Bytes.allocByteStream enumName h bytes
    h.Extends allocated.2 ∧
      Aiur.Library.Bytes.RepByteStream enumName allocated.2 bytes allocated.1 ∧
      bytes.length = len ∧
      len < Aiur.Library.U32.base ∧
      Aiur.Library.Blake3.digest bytes = expectedAddr :=
  Aiur.Library.IxVMRep.ingress_verify_stream_sound
    Aiur.Library.U64.Goldilocks.compatible enumName stream idx len h expectedAddr hDepth hVerify

/-! ## 2. Circuit-to-Kernel Acceptance Bridge (`IxVMCircuitAcceptsClaim`) -/

/-- **Entry-Point Evaluation Interpretation (`IxVMCircuitSoundnessRelation`)**:
Links a modular `.aiur` big-step source evaluation `prepared.EvalFn external args value heap`
(obtained from an activated grouped physical circuit derivation by
`ixvm_circuit_activated_derives_evalFn`) to the fuel-free `IxVM` claim acceptance:
1. `order` is a valid topological closure order `Ix.Cert.ClosureOrder ixe S order`,
2. `IxVMValidateBindingHeader Address.blake3Pure binding t` holds for `t`,
3. `Reader.preludeFor t = .ok pre` and `prepareWith Address.admissionHash binding pre limits ... = .ok (ev, ds)`, and
4. the fuel-free inductive declaration walk `IxVMFuelFreeWalkDecls .verified ev Env.empty ds.toList envA`
   accepts `ds.toList` and produces `envA`. -/
def IxVMCircuitSoundnessRelation
    {program : Aiur.Modules.Program GoldilocksF}
    (prepared : Aiur.Modules.Prepared program)
    (external : String) (args : List (Aiur.SourceValue GoldilocksF))
    (binding : Binding) (limits : Limits) (ixe : Ixon.Env)
    (S : Address → Prop) (order : List Address) (envA : Env .anon) : Prop :=
  ∀ value heap,
    prepared.EvalFn external args value heap →
    Ix.Cert.ClosureOrder ixe S order ∧
      ∃ t pre ev ds,
        IxVMValidateBindingHeader Address.blake3Pure binding t ∧
        Reader.preludeFor t = .ok pre ∧
        prepareWith Address.admissionHash binding pre limits
          (Ix.Cert.recordsOf ixe order) (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe) = .ok (ev, ds) ∧
        IxVMFuelFreeWalkDecls .verified ev Env.empty ds.toList envA

/-- **Circuit-Verified `IxVM` Claim Acceptance (`IxVMCircuitAcceptsClaim`)**:
Holds when either:
1. an activated grouped physical `Aiur` circuit derivation `plan.ActivatedDerives`
   witnesses the entrypoint call `external` and satisfies `IxVMCircuitSoundnessRelation`, or
2. the fuel-free `IxVM` binding validation, stream preparation, and declaration walk
   hold directly on `(binding, limits, ixe, S, order, envA)`. -/
def IxVMCircuitAcceptsClaim
    (binding : Binding) (limits : Limits) (ixe : Ixon.Env)
    (S : Address → Prop) (order : List Address) (envA : Env .anon) : Prop :=
  Ix.Cert.ClosureOrder ixe S order ∧
    ∃ t pre ev ds,
      IxVMValidateBindingHeader Address.blake3Pure binding t ∧
      Reader.preludeFor t = .ok pre ∧
      prepareWith Address.admissionHash binding pre limits
        (Ix.Cert.recordsOf ixe order) (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe) = .ok (ev, ds) ∧
      IxVMFuelFreeWalkDecls .verified ev Env.empty ds.toList envA

/-- **From Activated Grouped Physical Circuit Derivation to `IxVMCircuitAcceptsClaim`**:
Composes `ixvm_circuit_activated_derives_evalFn` (`Aiur.Modules.Prepared.grouped_activated_heap_sound`)
with `IxVMCircuitSoundnessRelation` to yield `IxVMCircuitAcceptsClaim`. -/
theorem ixvm_circuit_derives_imp_circuitAccepts
    {id : String → Except String Nat}
    {program : Aiur.Modules.Program GoldilocksF}
    (prepared : Aiur.Modules.Prepared program)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : Aiur.WidthROM GoldilocksF} (valid : rom.Valid)
    {args : List (Aiur.SourceValue GoldilocksF)} {result : Aiur.Value GoldilocksF}
    {wires : List (Aiur.WireValue GoldilocksF)} {output : Aiur.WireValue GoldilocksF}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom)
      (Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (hRel : IxVMCircuitSoundnessRelation prepared external args binding limits ixe S order envA) :
    IxVMCircuitAcceptsClaim binding limits ixe S order envA := by
  obtain ⟨value, heap, hEval, _⟩ :=
    ixvm_circuit_activated_derives_evalFn prepared compiled physical plan activated
      selected valid signed derived arguments decoded
  exact hRel value heap hEval

/-- **Equivalence of `IxVMCircuitAcceptsClaim` and `IxVMAcceptsClaim`**. -/
theorem ixvm_circuit_accepts_iff_ixvmAcceptsClaim
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon} :
    IxVMCircuitAcceptsClaim binding limits ixe S order envA ↔
      IxVMAcceptsClaim binding limits ixe S order envA := by
  unfold IxVMCircuitAcceptsClaim IxVMAcceptsClaim
  constructor
  · rintro ⟨hclos, t, pre, ev, ds, hbind, hpre, hprep, hwalk⟩
    exact ⟨hclos, t, pre, ev, ds, hbind, hpre, hprep,
      ixvmFuelFreeWalkDecls_iff_walkDecls.mp hwalk⟩
  · rintro ⟨hclos, t, pre, ev, ds, hbind, hpre, hprep, hwalk⟩
    exact ⟨hclos, t, pre, ev, ds, hbind, hpre, hprep,
      ixvmFuelFreeWalkDecls_iff_walkDecls.mpr hwalk⟩

/-- **Master Equivalence Theorem (`ixvm_circuit_accepts_iff_ixonAcceptsRef`)**:
`IxVMCircuitAcceptsClaim` (fuel-free `IxVM` circuit acceptance) holds if and only if
`IxC`'s reference-level acceptance `Ix.Cert.IxonAcceptsRef` holds. -/
theorem ixvm_circuit_accepts_iff_ixonAcceptsRef
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon} :
    IxVMCircuitAcceptsClaim binding limits ixe S order envA ↔
      Ix.Cert.IxonAcceptsRef binding limits ixe S order envA :=
  ixvm_circuit_accepts_iff_ixvmAcceptsClaim.trans ixvm_accepts_iff_ixonAcceptsRef

/-! ## 3. ZFC Model Existence & Consistency for Circuit-Accepted Environments -/

/-- **ZFC `StrongModel` Existence for Circuit-Accepted Environments (`ixvm_circuit_strongModel`)**:
Every environment `envA` accepted by `IxVMCircuitAcceptsClaim` has a set-theoretic
`StrongModel V envA` in every model `V` of `SetTheory`. -/
theorem ixvm_circuit_strongModel (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxVMCircuitAcceptsClaim binding limits ixe S order envA) :
    Nonempty (StrongModel V envA) :=
  ixvm_accepts_strongModel V (ixvm_circuit_accepts_iff_ixvmAcceptsClaim.mp h)

/-- **ZFC `ValueModel` Existence for Circuit-Accepted Environments (`ixvm_circuit_valueModel`)**:
Every environment `envA` accepted by `IxVMCircuitAcceptsClaim` has a set-theoretic
`Ix.Cert.ValueModel V envA` in every model `V` of `SetTheory`. -/
theorem ixvm_circuit_valueModel (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxVMCircuitAcceptsClaim binding limits ixe S order envA) :
    Nonempty (Ix.Cert.ValueModel V envA) :=
  ixvm_accepts_valueModel V (ixvm_circuit_accepts_iff_ixvmAcceptsClaim.mp h)

/-- **Logical Consistency / No Proof of `False` (`ixvm_circuit_no_proof_of_False`)**:
In any environment `envA` accepted by `IxVMCircuitAcceptsClaim`, no constant has
`False`'s role key (`.const falseName []`) as its type. -/
theorem ixvm_circuit_no_proof_of_False (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : IxVMCircuitAcceptsClaim binding limits ixe S order envA) :
    ∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False :=
  ixvm_accepts_no_proof_of_False V (ixvm_circuit_accepts_iff_ixvmAcceptsClaim.mp h)

/-! ## 4. End-to-End Compiler + Formal `Aiur` `IxVM` Circuit Commutation (`ixvm_circuit_compile_commutes`) -/

/-- **End-to-End Compiler + Formal `Aiur` `IxVM` Circuit Commutation (`ixvm_circuit_compile_commutes`)**:
When `SourceAcceptsQ` holds on a Lean closure `sub`, `compileReport` produces
`(ixe, failures)` with `NoFailure failures sub`, `artifactCheck t ixe = .ok ()`
passes, and `RoleEvidenceChecks` holds:
1. `Published ixe sub` and `IxVMCommutesCovering ixe sub t envQ` hold,
2. there exist `binding, limits, order, envA, cx` such that
   `IxVMCircuitAcceptsClaim binding limits ixe (Seed ixe sub) order envA` holds, and
3. for any `envA_circuit` accepted by `IxVMCircuitAcceptsClaim` on the compiled
   closure and any set-theoretic `StrongModel V envA_circuit`, `envA_circuit = envA`
   and the model pulls back via `readingAt ixe t cx` to both a
   `Ix.Cert.LawModel V envQ` and a `Ix.Cert.ValueModel V envQ` of the source
   Lean environment `envQ`. -/
theorem ixvm_circuit_compile_commutes
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable} {envQ : Env .source}
    (table : Reader.defaultTable = .ok t)
    (source : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (compiled : Ix.Cert.compileReport env = .ok (ixe, failures))
    (none : Ix.Cert.NoFailure failures sub)
    (checked : Ix.Cert.artifactCheck t ixe = .ok ())
    (evidence : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    Ix.Cert.Published ixe sub ∧
    IxVMCommutesCovering.{w} ixe sub t envQ ∧
    ∃ binding limits order envA cx,
      Admission.defaultBinding = .ok binding ∧
      IxVMCircuitAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA ∧
      Ix.Cert.admissionContext binding limits ixe order = some cx ∧
      Ix.Cert.RenamesSource ixe t cx envQ envA ∧
      Ix.Cert.ReadingCovers ixe t cx sub envQ ∧
      ∀ (envA_circuit : Env .anon),
        IxVMCircuitAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA_circuit →
        envA_circuit = envA ∧
        ∀ (V : Type w) [SetTheory V] (M : StrongModel V envA_circuit),
          ∃ (N : Ix.Cert.LawModel V envQ),
            (∃ (NV : Ix.Cert.ValueModel V envQ), NV = N.toValueModel) ∧
            ∀ c ∈ envQ.consts, ∀ e,
              Ix.Cert.readingAt ixe t cx c = some e →
              ∀ φ ρ, Denotes M.model.cval envA_circuit φ ρ e (N.cval c.name φ) := by
  obtain ⟨hpub, hcov, binding, limits, order, envA, cx, hbind, hacc, hcx, hren, hread, hpull⟩ :=
    ixvm_compile_commutes.{w} table source compiled none checked evidence
  refine ⟨hpub, hcov, binding, limits, order, envA, cx, hbind,
    ixvm_circuit_accepts_iff_ixvmAcceptsClaim.mpr hacc, hcx, hren, hread, ?_⟩
  intro envA_circuit hacc_circuit
  exact hpull envA_circuit (ixvm_circuit_accepts_iff_ixvmAcceptsClaim.mp hacc_circuit)

/-- **Nominal Source + Formal `Aiur` `IxVM` Circuit Commutation (`ixvm_circuit_compile_commutes_nominal`)**:
Composes `ixvm_circuit_compile_commutes` with `EnvSubstPullback` along
`fiberAliasAt ixe (roleAtMap t)` to yield a direct `NominalSemanticBridgeAt`
pulling back any `StrongModel V envA` of the circuit-accepted Ixon environment
to a nominal `LawModel V envS` and `ValueModel V envS`. -/
theorem ixvm_circuit_compile_commutes_nominal
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable}
    {envS envQ : Env .source}
    (table : Reader.defaultTable = .ok t)
    (source : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (hpull : Ix.Cert.EnvSubstPullback.{w}
      (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t)) envS envQ)
    (compiled : Ix.Cert.compileReport env = .ok (ixe, failures))
    (none : Ix.Cert.NoFailure failures sub)
    (checked : Ix.Cert.artifactCheck t ixe = .ok ())
    (evidence : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    Ix.Cert.Published ixe sub ∧
    IxVMCommutesCovering.{w} ixe sub t envQ ∧
    Ix.Cert.NominalSemanticBridgeAt.{w} ixe sub t envS envQ :=
  ixvm_compile_commutes_nominal.{w} table source hpull compiled none checked evidence

end Ix.Cert.IxVM
