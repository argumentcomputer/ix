/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.BoundVerifier
import Ix.Aiur.Proofs.KeyCodec

/-! The backend's selected native key has a checked canonical v5 meaning.
This establishes byte interpretation and decoded graph evaluation. Equality
with the compiler's graph, native verifier execution and cryptographic
acceptance-to-satisfaction are separate obligations. -/

namespace Aiur.BoundVerifier
open NativeAIR

theorem Backend.key_decodes {selection : Selection} (backend : Backend selection) :
    KeyCodec.decode selection.key = some backend.keyData :=
  (KeyCodec.decodeCanonical_success backend.keyDecoded).1

theorem Backend.native_key_decodes {selection : Selection} (backend : Backend selection) :
    KeyCodec.decodeCanonical backend.system.vkBytes = some backend.keyData := by
  rw [backend.keyBound]
  exact backend.keyDecoded

theorem Backend.native_key_encoding {selection : Selection} (backend : Backend selection) :
    KeyCodec.encode backend.keyData = backend.system.vkBytes := by
  rw [backend.keyBound]
  exact (KeyCodec.decodeCanonical_success backend.keyDecoded).2

theorem Backend.key_commitment {selection : Selection} (backend : Backend selection) :
    KeyCodec.CommitmentValid backend.keyData.preprocessedCommitment :=
  KeyCodec.decode_commitment backend.key_decodes

theorem Backend.key_graph_valid {selection : Selection} (backend : Backend selection)
    {circuit : KeyCodec.Circuit} (member : circuit ∈ backend.keyData.circuits) :
    circuit.graph.Valid circuit.widths :=
  (KeyCodec.Circuit.valid_graph ((KeyCodec.decode_valid backend.key_decodes).1 circuit member)).2.2.1

theorem Backend.key_graph_reflects {selection : Selection} (backend : Backend selection)
    {circuit : KeyCodec.Circuit} (member : circuit ∈ backend.keyData.circuits)
    (ops : EvalOps W) (values : Values W) (fits : values.Fits circuit.widths) :
    ∃ trees full lookupValues,
      circuit.graph.unfold = some trees ∧ circuit.graph.sweep ops values = some full ∧
      circuit.graph.sweepLookupPrefix ops values = some lookupValues ∧
      trees.size = circuit.graph.nodes.length ∧ full.size = circuit.graph.nodes.length ∧
      lookupValues.size = circuit.graph.lookupPrefix ∧ Reflects ops values trees full ∧
      readNodes full circuit.graph.zeros = evalRoots ops values trees circuit.graph.zeros ∧
      ∀ lookup ∈ circuit.graph.lookups,
        readLookup lookupValues lookup = readLookup full lookup ∧
        readLookup lookupValues lookup = evalLookup ops values trees lookup := by
  have valid := backend.key_graph_valid member
  obtain ⟨trees, unfolded, treesSize⟩ := valid.unfold_defined
  obtain ⟨full, swept, fullSize⟩ := valid.sweep_defined ops values fits
  obtain ⟨lookupValues, lookupSwept, lookupSize⟩ := valid.lookup_sweep_defined ops values fits
  have reflected := circuit.graph.sweep_reflects ops values unfolded swept
  refine ⟨trees, full, lookupValues, unfolded, swept, lookupSwept, treesSize, fullSize,
    lookupSize, reflected, reflected.readNodes _, ?_⟩
  intro lookup present
  exact ⟨(valid.lookup_values_agree ops values swept lookupSwept lookupSize lookup present).symm,
    valid.lookup_values_reflect ops values unfolded swept lookupSwept lookupSize lookup present⟩

end Aiur.BoundVerifier
