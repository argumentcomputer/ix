import Aiur.Generic.Observe
import Aiur.Optimized.Depth.Grouped

/-!
# Observed headlines: the calls are carried by the trace's memory

The backend headlines conclude `Modules.Prepared.EvalFn`: some source
derivation of the entry, and the result represented in the trace's decoded ROM.
The observed headlines conclude, in addition, an *observed* derivation
(`Modules.Prepared.ObsFn`, `Generic.Observe`) whose every recorded call has its
arguments represented in that same ROM (`CallsInROM`), relative to the heap at
the call. Calls to inline functions (`Blake3::hash` in IxVM) have no chip, so
the tie goes through the ROM rather than through rows.

Chain: the heap realization of the circuit evaluation allocates only cells the
ROM holds (`ROMEvalCall.realizeCells`, `HeapInROM`); the source derivation and
the core derivation of the inlined program share their final heap
(`GenericArtifact.native_entry_iff`); every value of an observed derivation
whose final heap is in the ROM is represented (`ObsFn.callsInROM`).

* `ModulesArtifact.grouped_activated_heap_sound_observed`: from the finite
  derivation `plan.ActivatedDerives` (the assumption-based headline).
* `Modules.Prepared.depth_grouped_activated_heap_sound_observed` and
  `…_goldilocks_observed`: from the grouped, activated memo checker over the
  depth pass and the `2^39` row bound (no acyclicity assumption).
-/

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F] {program : Program F} {system : System F}

/-- `ProvenanceModel.heap_sound`, also giving that the realized heap's cells
are ROM cells and that the entry arguments are pointer-free. -/
theorem System.ProvenanceModel.heap_sound_cells (model : system.ProvenanceModel program)
    {rom : WireROM F} (valid : rom.Valid) {name : String} {args : List (SourceValue F)}
    {result : Value F} (entry : checkEntry program name = .ok ())
    {wires : List (WireValue F)} {output : WireValue F}
    (derived : CircuitEvaluates system rom name wires output)
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result ∧
      HeapInROM (rom.decode program.enums) heap ∧ ∀ value ∈ args, value.pointerFree = true := by
  have publicArgs := model.publicArguments entry derived
  have encodedFree : ∀ value ∈ entryValues args, value.pointerFree = true := by
    intro value member
    have typeMember : value.type ∈ wires.map WireValue.type := by
      rw [← arguments.types]
      exact List.mem_map.mpr ⟨value, member, rfl⟩
    obtain ⟨wire, wireMember, same⟩ := List.mem_map.mp typeMember
    exact Value.pointerFree_of_type (same ▸ publicArgs wire wireMember) (arguments.wellFormed value member)
  have trusted : ∀ value ∈ entryValues args, (rom.decode program.enums).Provenance value :=
    fun value member => .of_pointerFree value (encodedFree value member)
  have evaluated := model.sound_encoded valid derived arguments decoded trusted
  have free : ∀ value ∈ args, value.pointerFree = true := by
    intro value member
    have formed := evaluated.publicArguments entry (value.mapAddress (fun _ => 0))
      (List.mem_map.mpr ⟨value, member, rfl⟩)
    exact Value.pointerFree_of_type (by simpa using formed.1) (by simpa using formed.2)
  have relatedArgs : RepresentsArgs (rom.decode program.enums) [] args (entryValues args) := by
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun value member => Represents.of_pointerFree value (free value member) _)
  obtain ⟨source, heap, evaluated, _, related, cells⟩ :=
    evaluated.realizeCells (WireROM.decode_valid valid) relatedArgs
  exact ⟨source, heap, evaluated, related, cells, free⟩

end Aiur.Circuit

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F] {source : Generic.Source F} {entries : List String}

theorem GenericArtifact.heap_sound_cells {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (derived : Circuit.CircuitEvaluates compiled.system rom name wires output)
    (arguments : DecodesValues prepared.program.enums wires (entryValues args))
    (decoded : output.decode prepared.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents (rom.decode prepared.program.enums) heap value result ∧
      HeapInROM (rom.decode prepared.program.enums) heap ∧ ∀ v ∈ args, v.pointerFree = true := by
  have stages := compile_stages compiled.compiled
  have original :=
    (compiled.artifact.dedup_derives_iff (by simpa only [stages.2.2.1] using selected)).mpr derived
  obtain ⟨value, heap, evaluated, related, cells, free⟩ :=
    (compile_semanticModel compiled.compiled).heap_sound_cells valid
      (compiled.inlined.valid.2.2 name selected).2 original arguments decoded
  exact ⟨value, heap, (compiled.native_entry_iff selected).mpr evaluated, related, cells, free⟩

end Aiur.Optimized

namespace Aiur.Optimized.Physical

open Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- `Prepared.native_heap_sound`, observed: some observed source derivation of
the entry, with the result and every call's arguments represented in the
trace's decoded ROM. -/
theorem Prepared.native_heap_sound_observed {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) {name : String} (entry : name ∈ entries)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    (derived : Derives prepared.system (Erasure.rawROM rom)
      (Erasure.message compiled.system ⟨name, wires, output⟩))
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap calls, Generic.SourceSemantics.ObsFn source.world name args [] value heap calls ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums)
        heap value result ∧
      Generic.SourceSemantics.CallsInROM
        ((Erasure.typedROM compiled.system rom).decode specialized.program.enums) calls := by
  obtain ⟨value, heap, evaluated, related, cells, free⟩ :=
    compiled.heap_sound_cells entry (rom.toWireROM_valid valid _ _)
      ((prepared.derives_iff (by simpa only [(compile_stages compiled.compiled).2.2.1] using entry)
        signed).mpr derived) arguments decoded
  obtain ⟨calls, observed⟩ := evaluated.observe
  exact ⟨value, heap, calls, observed, related,
    observed.callsInROM (Generic.Source.world_preparesFromArgs source) cells free⟩

end Aiur.Optimized.Physical

namespace Aiur.Optimized

open Circuit

variable {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}

/-- **The trace's memory**, decoded: the ROM the headlines represent values in. -/
abbrev ModulesArtifact.traceROM {program : Modules.Program F} {prepared : Modules.Prepared program}
    (compiled : ModulesArtifact prepared) (rom : WidthROM F) : ROM F :=
  (Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums

theorem ModulesArtifact.physical_heap_sound_observed {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : Derives physical.system (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap calls, prepared.ObsFn external args value heap calls ∧
      Represents (compiled.traceROM rom) heap value result ∧
      Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls := by
  obtain ⟨value, heap, calls, observed, related, carried⟩ :=
    physical.native_heap_sound_observed compiled.circuit (Modules.Prepared.entry_mem selected)
      valid signed derived arguments decoded
  exact ⟨value, heap, calls, ⟨entry, selected, observed⟩, related, carried⟩

/-- **The observed assumption-based headline**: `grouped_activated_heap_sound`,
concluding an observed derivation whose calls the trace's memory carries.
This is the shape of Track B's `ObservedHeadline`. -/
theorem ModulesArtifact.grouped_activated_heap_sound_observed {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    (plan : Grouping.Plan physical.system id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.ActivatedDerives (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap calls, prepared.ObsFn external args value heap calls ∧
      Represents (compiled.traceROM rom) heap value result ∧
      Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls :=
  compiled.physical_heap_sound_observed physical selected valid signed
    (plan.derives_sound (plan.activatedDerives_sound_plan activated derived)) arguments decoded

end Aiur.Optimized

namespace Aiur.Modules

open Circuit Optimized

variable {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}

/-- `Prepared.grouped_activated_heap_sound`, observed. -/
theorem Prepared.grouped_activated_heap_sound_observed {program : Modules.Program F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    (plan : Grouping.Plan physical.system id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.ActivatedDerives (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap calls, prepared.ObsFn external args value heap calls ∧
      Represents (compiled.traceROM rom) heap value result ∧
      Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls :=
  compiled.grouped_activated_heap_sound_observed physical plan activated selected valid signed derived
    arguments decoded

/-- **The observed headline without the derivation hypothesis**: rows accepted
by the grouped, activated memo checker over the certified depth pass, with at
most `2^39` rows, give an observed derivation whose calls the trace's memory
carries. -/
theorem Prepared.depth_grouped_activated_heap_sound_observed {program : Modules.Program F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} (certified : Depth.Certified cfg physical.system)
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message F}
    (rooted : Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (checked : plan.checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap calls, prepared.ObsFn external args value heap calls ∧
      Represents (compiled.traceROM rom) heap value result ∧
      Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls :=
  compiled.physical_heap_sound_observed physical selected valid signed
    (rooted ▸ Depth.plan_checkMemo_sound certified plan activated bound characteristic checked outside)
    arguments decoded

/-- The same over Goldilocks with `k = 24` (`cfg.bits = 24`). -/
theorem Prepared.depth_grouped_activated_heap_sound_goldilocks_observed
    {program : Modules.Program Library.U32.Goldilocks.F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} (certified : Depth.Certified cfg physical.system) (bits : cfg.bits = 24)
    (plan : Grouping.Plan (Depth.system cfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Library.U32.Goldilocks.F)} {result : Value Library.U32.Goldilocks.F}
    {wires : List (WireValue Library.U32.Goldilocks.F)} {output : WireValue Library.U32.Goldilocks.F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Message Library.U32.Goldilocks.F}
    (rooted : Depth.erase cfg root =
      Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow Library.U32.Goldilocks.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap calls, prepared.ObsFn external args value heap calls ∧
      Represents (compiled.traceROM rom) heap value result ∧
      Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls :=
  prepared.depth_grouped_activated_heap_sound_observed compiled physical certified plan activated
    selected valid signed rooted outside bound (Depth.goldilocks_bound bits) checked arguments decoded

end Aiur.Modules
