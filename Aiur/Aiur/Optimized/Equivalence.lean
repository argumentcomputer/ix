import Aiur.Optimized.SemanticModel
import Aiur.Optimized.Correctness
import Aiur.Circuit.MemoTree

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]
  {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}

/-- Removing internal validation preserves every reference derivation, even for
internal pointer arguments and before requiring a functional ROM. -/
theorem reference_derives {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (derived : Circuit.Derives reference rom root) : Circuit.Derives artifact.system rom root :=
  (artifact.dedup_derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry)).mp
    (((Circuit.compile_semanticModel original).supportRefinesProvenance
      (compile_semanticModel compiled)).derives derived)

/-- Entry validation starts the canonical-value/provenance induction. The
result's canonical encoding is proved here, with no decoded-return premise. -/
theorem compiler_entry_sound (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (valid : rom.Valid) (free : root.PublicArguments program.enums)
    (derived : Circuit.Derives artifact.system rom root) : root.Evaluates program rom := by
  obtain ⟨tree⟩ := (artifact.dedup_derives_iff
    (by simpa only [(compile_stages compiled).2.2.1] using entry)).mpr derived
  obtain ⟨rule, _, same⟩ := tree.root_instance
  have canonical := compile_entry_arguments compiled rule (by simpa only [same] using entry)
  rw [same] at canonical
  exact (compile_semanticModel compiled).derivation_evaluates valid free canonical tree

/-- Finite entry derivations recover every omitted internal validation.
The statement covers all layout passes and recursive chip deduplication. -/
theorem reference_derives_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (valid : rom.Valid) (free : root.PublicArguments program.enums) :
    Circuit.Derives reference rom root ↔ Circuit.Derives artifact.system rom root := by
  refine ⟨reference_derives original compiled entry, ?_⟩
  intro derived
  obtain ⟨args, result, arguments, decoded, evaluated⟩ :=
    compiler_entry_sound compiled entry valid free derived
  exact (Circuit.compile_semanticModel original).complete_encoded evaluated arguments decoded

/-- Cyclic memoized completeness is preserved. Soundness in the reverse
 direction requires an acyclic graph. -/
theorem reference_memoDerives {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (derived : Circuit.MemoDerives reference rom root) : Circuit.MemoDerives artifact.system rom root :=
  (artifact.dedup_memoDerives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry)).mp
    (((Circuit.compile_semanticModel original).supportRefinesProvenance
      (compile_semanticModel compiled)).memoDerives derived)

theorem reference_acyclic_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (valid : rom.Valid) (free : root.PublicArguments program.enums) :
    (∃ graph : Circuit.MemoDerivation reference rom root, graph.Acyclic) ↔
      (∃ graph : Circuit.MemoDerivation artifact.system rom root, graph.Acyclic) := by
  rw [← Circuit.derives_iff_acyclic_memo, ← Circuit.derives_iff_acyclic_memo]
  exact reference_derives_iff original compiled entry valid free

private theorem reference_context_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    (rom : WireROM F) (root : Circuit.Message F) :
    reference.checkContext rom root = .ok () ↔ artifact.system.checkContext rom root = .ok () := by
  simp only [Circuit.System.checkContext_iff, Circuit.compile_wellFormed original, artifact.wellFormed, and_true,
    (Circuit.compile_stages original).2.2.2.1, compile_enums compiled]

/-- The integer checker already enforces the public input and functional-ROM
conditions needed by provenance soundness. Its generic tree bridge is unchanged. -/
theorem reference_check_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    (∃ rows, reference.check rom root rows = .ok ()) ↔
      (∃ rows, artifact.system.check rom root rows = .ok ()) := by
  constructor
  · rintro ⟨rows, accepted⟩
    have context := (reference_context_iff original compiled rom root).mp
      (Circuit.System.check_iff.mp accepted).1
    exact (artifact.system.check_derives_iff context).mpr
      (reference_derives original compiled entry (reference.check_sound accepted))
  · rintro ⟨rows, accepted⟩
    have context := (reference_context_iff original compiled rom root).mpr
      (Circuit.System.check_iff.mp accepted).1
    have facts := Circuit.System.checkContext_iff.mp (Circuit.System.check_iff.mp accepted).1
    have free : root.PublicArguments program.enums := by
      simpa only [compile_enums compiled] using facts.2.1
    exact (reference.check_derives_iff context).mpr
      ((reference_derives_iff original compiled entry facts.2.2.1 free).mpr
        (artifact.system.check_sound accepted))

/-- Every accepted reference LogUp witness remains accepted after deleting
load checks. No acyclicity restriction is needed for this direction. -/
theorem reference_checkMemo_complete {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries)
    (accepted : ∃ rows, reference.checkMemo rom root rows = .ok ()) :
    ∃ rows, artifact.system.checkMemo rom root rows = .ok () := by
  obtain ⟨rows, accepted⟩ := accepted
  have context := (reference_context_iff original compiled rom root).mp
    (Circuit.System.checkMemo_iff.mp accepted).1
  exact (artifact.system.checkMemo_derives_iff context).mpr
    (reference_memoDerives original compiled entry (reference.checkMemo_sound accepted))

/-- Memoized checker equivalence holds for claims admitting acyclic support.
Arbitrary cyclic proofs retain the intended possibility of self-justification. -/
theorem reference_checkMemo_acyclic_iff {reference : Circuit.System F}
    (original : Circuit.compile program = .ok reference)
    (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} {root : Circuit.Message F} (entry : root.channel ∈ entries) :
    ((∃ rows, reference.checkMemo rom root rows = .ok ()) ∧
      ∃ graph : Circuit.MemoDerivation reference rom root, graph.Acyclic) ↔
    ((∃ rows, artifact.system.checkMemo rom root rows = .ok ()) ∧
      ∃ graph : Circuit.MemoDerivation artifact.system rom root, graph.Acyclic) := by
  constructor
  · rintro ⟨⟨rows, accepted⟩, graph, acyclic⟩
    have context := (reference_context_iff original compiled rom root).mp
      (Circuit.System.checkMemo_iff.mp accepted).1
    have facts := Circuit.System.checkContext_iff.mp context
    have free : root.PublicArguments program.enums := by
      simpa only [compile_enums compiled] using facts.2.1
    exact ⟨reference_checkMemo_complete original compiled entry ⟨rows, accepted⟩,
      (reference_acyclic_iff original compiled entry facts.2.2.1 free).mp ⟨graph, acyclic⟩⟩
  · rintro ⟨⟨rows, accepted⟩, graph, acyclic⟩
    have context := (reference_context_iff original compiled rom root).mpr
      (Circuit.System.checkMemo_iff.mp accepted).1
    have facts := Circuit.System.checkContext_iff.mp (Circuit.System.checkMemo_iff.mp accepted).1
    have free : root.PublicArguments program.enums := by
      simpa only [compile_enums compiled] using facts.2.1
    have tree := (reference_derives_iff original compiled entry facts.2.2.1 free).mpr
      (graph.derives_of_acyclic acyclic)
    exact ⟨(reference.checkMemo_derives_iff context).mpr tree.memo, tree.acyclic⟩

/-- Source ROM evaluation and the optimized entry circuit agree on inputs
with provenance. Pointer-free inputs satisfy this precondition automatically. -/
theorem compiler_correct (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} (valid : rom.Valid) {name : String} (entry : name ∈ entries)
    {args : List (Value F)} {result : Value F}
    (trusted : ∀ value ∈ args, (rom.decode program.enums).Provenance value) :
    ROMEvalCall (rom.decode program.enums) program name args result ↔
      Circuit.EncodedEvaluates program.enums artifact.system rom name args result := by
  rw [(compile_semanticModel compiled).evaluates_iff valid trusted]
  unfold Circuit.EncodedEvaluates
  constructor <;> rintro ⟨wires, output, arguments, decoded, derived⟩
  · exact ⟨wires, output, arguments, decoded,
      (artifact.dedup_derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry)).mp derived⟩
  · exact ⟨wires, output, arguments, decoded,
      (artifact.dedup_derives_iff (by simpa only [(compile_stages compiled).2.2.1] using entry)).mpr derived⟩

end Aiur.Optimized
