import Aiur.Optimized.Observed

/-! Track B's backend obligation `ObservedHeadline`
(`Ix/IxVM/Refinement/Statement.lean` on `jcb/certified-ixvm-refinement`), restated
over this package's definitions (`Generic.SourceSemantics.Call`, `CallsInROM`,
`Modules.Prepared.ObsFn`, `Optimized.ModulesArtifact.traceROM`) with its
hypothesis `AcyclicDerivation` unfolded, is discharged as written. -/

open Aiur Aiur.Generic.SourceSemantics

namespace AiurObservedTests

def ObservedHeadline : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}
    {program : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared program}
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id),
    plan.WellFormedActivation →
    ∀ {external : String}
      {entry : Aiur.Modules.Selection program prepared.environment.assembly.instances},
      prepared.find? external = some entry →
    ∀ {rom : Aiur.WidthROM F}, rom.Valid →
    ∀ {args : List (Aiur.SourceValue F)} {result : Aiur.Value F} {wires : List (Aiur.WireValue F)}
      {output : Aiur.WireValue F},
      Aiur.Circuit.Erasure.Signed compiled.circuit.system
          { channel := entry.resolved.name, args := wires, result := output } →
      plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom)
          (Aiur.Circuit.Erasure.message compiled.circuit.system
            { channel := entry.resolved.name, args := wires, result := output }) →
      Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args) →
      Aiur.WireValue.decode compiled.specialized.program.enums output = some result →
      ∃ (value : Aiur.SourceValue F) (heap : Aiur.Heap F) (calls : List (Call F)),
        prepared.ObsFn external args value heap calls ∧
          Aiur.Represents (Aiur.WireROM.decode compiled.specialized.program.enums
            (Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom)) heap value result ∧
          CallsInROM (Aiur.WireROM.decode compiled.specialized.program.enums
            (Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom)) calls

theorem observedHeadline : ObservedHeadline := by
  intro F _ _ id program prepared compiled physical plan activated external entry selected rom valid
    args result wires output signed derived arguments decoded
  exact Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound_observed compiled physical plan
    activated selected valid signed derived arguments decoded

/-- info: 'AiurObservedTests.observedHeadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms observedHeadline

end AiurObservedTests
