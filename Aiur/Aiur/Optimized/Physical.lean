import Aiur.Circuit.Erasure
import Aiur.Optimized.NativeCorrectness

namespace Aiur.Optimized.Physical

open Circuit
variable {F : Type} [Field F] [DecidableEq F]

/-- Erase static interfaces, then reuse the certified recursive partitioning
pass. The original typed artifact remains the source-level proof interface. -/
structure Prepared (artifact : Artifact F) where
  compatible : Erasure.Compatible artifact.system
  merged : Dedup.CheckedResult (Erasure.system artifact.system) artifact.entries

def prepare (artifact : Artifact F) : Except String (Prepared artifact) := do
  if compatible : Erasure.Compatible artifact.system then
    let source := Erasure.system artifact.system
    let merged ← if artifact.config.deduplicate then Dedup.run source artifact.entries
      else Dedup.certify source artifact.entries (Dedup.identity source)
    return ⟨compatible, merged⟩
  else throw "physical circuit interfaces failed their type-erasure certificate"

def Prepared.system {artifact : Artifact F} (prepared : Prepared artifact) : Circuit.System F :=
  prepared.merged.system

def Prepared.representative {artifact : Artifact F} (prepared : Prepared artifact) (name : String) : String :=
  Dedup.rename prepared.merged.representatives (Dedup.rename artifact.representatives name)

/-- Fixed tables retain their existing channels and typed proof interface. -/
theorem table_separated (artifact : Artifact F) (claim : Message F)
    (member : artifact.system.MapClaim claim) : artifact.system.findChip? claim.channel = none := by
  have oldMember : artifact.unmerged.MapClaim claim := by
    simpa only [System.MapClaim, artifact.deduplication.2.2.2.1] using member
  have absent := artifact.deduplication.2.2.2.2.1 claim oldMember
  have found := artifact.deduplication.lookup claim.channel
  simpa only [artifact.deduplication.outside absent, absent, Option.map_none] using found

theorem Prepared.derives_iff {artifact : Artifact F} (prepared : Prepared artifact)
    {rom : WidthROM F} {root : Message F} (entry : root.channel ∈ artifact.entries)
    (signed : Erasure.Signed artifact.system root) :
    Derives artifact.system (Erasure.typedROM artifact.system rom) root ↔
      Derives prepared.system (Erasure.rawROM rom) (Erasure.message artifact.system root) := by
  rw [Erasure.derives_iff artifact.system prepared.compatible (table_separated artifact) signed]
  have fixed := prepared.merged.certificate.entry_fixed
    (root := Erasure.message artifact.system root) (by simpa using entry)
  simpa only [fixed, Prepared.system] using prepared.merged.certificate.derives_iff
    (rom := Erasure.rawROM rom) (root := Erasure.message artifact.system root)

theorem Prepared.acyclic_iff {artifact : Artifact F} (prepared : Prepared artifact)
    {rom : WidthROM F} {root : Message F} (entry : root.channel ∈ artifact.entries)
    (signed : Erasure.Signed artifact.system root) :
    (∃ graph : MemoDerivation artifact.system (Erasure.typedROM artifact.system rom) root, graph.Acyclic) ↔
      (∃ graph : MemoDerivation prepared.system (Erasure.rawROM rom) (Erasure.message artifact.system root),
        graph.Acyclic) := by
  rw [← derives_iff_acyclic_memo, ← derives_iff_acyclic_memo]
  exact prepared.derives_iff entry signed

/-- Source soundness includes type-erased merging. Canonicality is still
established by entry/hint constraints and the existing provenance induction.
`signed` specifies the public claim's static interface, without checking values. -/
theorem Prepared.entry_sound {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : compile program entries config = .ok artifact)
    (prepared : Prepared artifact) {rom : WidthROM F} (valid : rom.Valid)
    {root : Message F} (entry : root.channel ∈ entries)
    (signed : Erasure.Signed artifact.system root) (free : root.PublicArguments program.enums)
    (derived : Derives prepared.system (Erasure.rawROM rom) (Erasure.message artifact.system root)) :
    root.Evaluates program (Erasure.typedROM artifact.system rom) := by
  apply compiler_entry_sound compiled entry
    (rom.toWireROM_valid valid _ _) free
  exact (prepared.derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry) signed).mpr derived

theorem Prepared.memo_entry_sound {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : compile program entries config = .ok artifact)
    (prepared : Prepared artifact) {rom : WidthROM F} (valid : rom.Valid)
    {root : Message F} (entry : root.channel ∈ entries)
    (signed : Erasure.Signed artifact.system root) (free : root.PublicArguments program.enums)
    (graph : MemoDerivation prepared.system (Erasure.rawROM rom) (Erasure.message artifact.system root))
    (acyclic : graph.Acyclic) : root.Evaluates program (Erasure.typedROM artifact.system rom) :=
  prepared.entry_sound compiled valid entry signed free (graph.derives_of_acyclic acyclic)

/-- The reference compiler and the physical merged circuits accept the same
finite entry derivations over the corresponding views of width-local ROM. -/
theorem Prepared.reference_derives_iff {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact) (prepared : Prepared artifact)
    {rom : WidthROM F} (valid : rom.Valid) {root : Message F} (entry : root.channel ∈ entries)
    (signed : Erasure.Signed artifact.system root) (free : root.PublicArguments program.enums) :
    Derives reference (Erasure.typedROM artifact.system rom) root ↔
      Derives prepared.system (Erasure.rawROM rom) (Erasure.message artifact.system root) :=
  (Optimized.reference_derives_iff original compiled entry (rom.toWireROM_valid valid _ _) free).trans
    (prepared.derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry) signed)

/-- Compose physical merging with specialization, inlining, compilation, and
heap realization, reaching the independent source evaluation predicate. -/
theorem Prepared.native_heap_sound {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) {name : String} (entry : name ∈ entries)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    (derived : Derives prepared.system (Erasure.rawROM rom)
      (Erasure.message compiled.system ⟨name, wires, output⟩))
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums) heap value result :=
  compiled.heap_sound entry (rom.toWireROM_valid valid _ _)
    ((prepared.derives_iff (by simpa only [(compile_stages compiled.compiled).2.2.1] using entry) signed).mpr derived)
    arguments decoded

def Prepared.checkMemo {artifact : Artifact F} (prepared : Prepared artifact)
    (rom : WidthROM F) (root : Message F) (rows : List (WeightedRow F)) : Except String Unit := do
  unless artifact.entries.contains root.channel do throw s!"unselected entrypoint {root.channel}"
  -- The schema is public/static. Canonical enum checks remain in the circuit.
  let some original := artifact.system.findChip? root.channel | throw "missing entrypoint circuit"
  unless Erasure.messageShape root == Erasure.signature original do throw "wrong entrypoint signature"
  (prepared.system.checkMemo (Erasure.rawROM rom) (Erasure.message artifact.system root) rows).mapError reprStr

end Aiur.Optimized.Physical
