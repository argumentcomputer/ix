import Aiur.Optimized.Depth.EndToEnd
import Aiur.Optimized.Grouping.Memo
import Aiur.Library.U32.Goldilocks

/-!
# Headline soundness from the grouped, activated memo checker

The deployed circuits are the grouped, activated plan over the depth pass of
the physical circuits: `Grouping.Plan (Depth.system cfg physical.system) id`.
Acceptance of `Plan.checkMemo` over that plan, the certified depth
configuration and the row bound `rows.length ≤ 2^39` give the independent
source evaluation predicate. These theorems replace the hypothesis
`derived : plan.ActivatedDerives …` of `Modules.Prepared.grouped_activated_heap_sound`;
no finite derivation and no acyclicity is assumed.

Chain: `Plan.checkMemo_graph` (transport through activation and grouping, one
row node per row) → `Depth.acyclic` (row bound) → `derives_of_acyclic` →
`Depth.derives_erase` (depth words) → `Physical.Prepared.native_heap_sound`
(dedup, erasure, compilation, inlining, specialization).
-/

namespace Aiur.Optimized.Depth

open Circuit

variable {F : Type} [Field F] [DecidableEq F] {cfg : Config} {source : System F} {rom : WireROM F}
variable {id : String → Except String Nat}

/-- The plan checker over the certified depth system and the row bound give a
finite derivation of the erased root in the source system. -/
theorem plan_checkMemo_sound (certified : Certified cfg source)
    (plan : Grouping.Plan (system cfg source) id) (activated : plan.WellFormedActivation)
    {root : Message F} {rows : List (WeightedRow F)} {N : Nat} (bound : rows.length ≤ N)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ N * 2 ^ cfg.bits → (n : F) ≠ 0)
    (checked : plan.checkMemo rom root rows = .ok ()) (outside : root.channel ∉ cfg.names) :
    Derives source rom (erase cfg root) := by
  obtain ⟨graph, card⟩ := Grouping.Plan.checkMemo_graph activated checked
  exact derives_erase certified.facts
    (graph.derives_of_acyclic (acyclic certified.facts graph (card.trans bound) characteristic))
    outside

/-- The row bound with at most `k = 24` limb bits fits Goldilocks. -/
theorem goldilocks_bound (bits : cfg.bits ≤ 24) :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : Library.U32.Goldilocks.F) ≠ 0 := by
  intro n positive small
  exact goldilocks_characteristic n positive
    (small.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) bits)))

end Aiur.Optimized.Depth

namespace Aiur.Optimized.Physical

open Circuit

variable {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}

/-- Source evaluation from rows accepted by the grouped, activated memo checker
over the certified depth pass, with at most `2^39` rows. -/
theorem Prepared.depth_grouped_activated_heap_sound {source : Generic.Source F}
    {entries : List String} {specialized : Generic.Specialized source entries}
    (compiled : GenericArtifact specialized) (prepared : Prepared compiled.artifact)
    {cfg : Depth.Config} (certified : Depth.Certified cfg prepared.system)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    {root : Message F}
    (rooted : Depth.erase cfg root = Erasure.message compiled.system ⟨name, wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → (n : F) ≠ 0)
    (checked : plan.checkMemo (Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums)
        heap value result :=
  prepared.native_heap_sound compiled entry valid signed
    (rooted ▸ Depth.plan_checkMemo_sound certified plan activated bound characteristic checked outside)
    arguments decoded

end Aiur.Optimized.Physical

namespace Aiur.Modules

open Circuit Optimized

variable {F : Type} [Field F] [DecidableEq F] {id : String → Except String Nat}

/-- The headline theorem without the derivation hypothesis: rows accepted by the
grouped, activated memo checker over the certified depth pass of the physical
circuits, with at most `2^39` rows, give `Modules.Prepared.EvalFn`. The STARK
side is trusted to deliver exactly such rows (see `Optimized.EndToEnd`). -/
theorem Prepared.depth_grouped_activated_heap_sound {program : Modules.Program F}
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
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  compiled.physical_heap_sound physical selected valid signed
    (rooted ▸ Depth.plan_checkMemo_sound certified plan activated bound characteristic checked outside)
    arguments decoded

/-- The same over Goldilocks with at most `k = 24` limb bits (`cfg.bits ≤ 24`: the exporter
uses `[16, 8]`, or no limbs when the plan has no gap slot): the characteristic side condition
is discharged. -/
theorem Prepared.depth_grouped_activated_heap_sound_goldilocks
    {program : Modules.Program Library.U32.Goldilocks.F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {cfg : Depth.Config} (certified : Depth.Certified cfg physical.system) (bits : cfg.bits ≤ 24)
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
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  prepared.depth_grouped_activated_heap_sound compiled physical certified plan activated selected
    valid signed rooted outside bound (Depth.goldilocks_bound bits) checked arguments decoded

end Aiur.Modules
