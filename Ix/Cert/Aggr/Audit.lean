import Ix.Cert.Aggr.EndToEnd

/-! # Workstreams `1B` & `5A`/`5B` Audit Surface (`Ix.Cert.Aggr.Audit`)

Verifies that every headline theorem in the certified 19-shape aggregation & dynamic-linking
stack (`Ix.Cert.Aggr`) depends ONLY on the three standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `native_decide`, zero `bv_decide`,
zero custom axioms).
-/

-- 1. Deployed MultiStark.aggregateProgram 19-shape AST pins
#check @Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms
#check @Ix.Cert.Aggr.aggregateSource_core_helpers_present
#check @Ix.Cert.Aggr.aggregateSource_ast_pinned
#check @Ix.Cert.Aggr.aggregateProgram_ast_pinned
/-- info: 'Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms
/-- info: 'Ix.Cert.Aggr.aggregateProgram_ast_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateProgram_ast_pinned

-- 2. Range telescoping, Shape 17 security envelope, and M-node ROM error union bound
#check @Ix.Cert.Aggr.aggr_range_telescoping
#check @Ix.Cert.Aggr.securityEnvelopeOk_iff
#check @Ix.Cert.Aggr.tree_rom_error_bound
#check @Ix.Cert.Aggr.tree_rom_error_merge
/-- info: 'Ix.Cert.Aggr.aggr_range_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggr_range_telescoping
/-- info: 'Ix.Cert.Aggr.securityEnvelopeOk_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.securityEnvelopeOk_iff
/-- info: 'Ix.Cert.Aggr.tree_rom_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.tree_rom_error_bound

-- 3. Conditional shard companion (`A7` axioms, Shape 18 all 3 discharge modes, `ComposedSpec` bridge)
#check @Ix.Cert.Aggr.evalLeafSound_of_eqProof
#check @Ix.Cert.Aggr.evalLeafSound_of_closedDefEq
#check @Ix.Cert.Aggr.evalLeafSound_of_dynamicLink
#check @Ix.Cert.Aggr.conditionalChecked_mono_ax
#check @Ix.Cert.Aggr.conditionalChecked_discharge_eval
#check @Ix.Cert.Aggr.conditionalChecked_unconditional
#check @Ix.Cert.Aggr.composedModelConclusion_of_composedSpec
#check @Ix.Cert.Aggr.composedModelConclusion_no_false
/-- info: 'Ix.Cert.Aggr.evalLeafSound_of_eqProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.evalLeafSound_of_eqProof
/-- info: 'Ix.Cert.Aggr.composedModelConclusion_no_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.composedModelConclusion_no_false

-- 4. 19-Shape Tree Refinement & End-to-End `aggregated_root_sound` Headlines
#check @Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19
#check @Ix.Cert.Aggr.aggregated_root_sound
#check @Ix.Cert.Aggr.aggregated_root_checkEnv_sound
#check @Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model
#check @Ix.Cert.Aggr.aggregated_root_catalog_sound
#check @Ix.Cert.Aggr.aggregated_root_dynamicLink_sound
/-- info: 'Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19
/-- info: 'Ix.Cert.Aggr.aggregated_root_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_checkEnv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_checkEnv_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model
/-- info: 'Ix.Cert.Aggr.aggregated_root_catalog_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_catalog_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_dynamicLink_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_dynamicLink_sound

-- 5. Negative Controls (Weak Envelope, `A7` Dropped Axiom, Shape 18 Undischarged Eval)
#check @Ix.Cert.Aggr.negative_control_weak_security_envelope
#check @Ix.Cert.Aggr.negative_control_a7_dropped_axiom
#check @Ix.Cert.Aggr.negative_control_shape18_undischarged_eval
/-- info: 'Ix.Cert.Aggr.negative_control_weak_security_envelope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_weak_security_envelope
/-- info: 'Ix.Cert.Aggr.negative_control_a7_dropped_axiom' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_a7_dropped_axiom
/-- info: 'Ix.Cert.Aggr.negative_control_shape18_undischarged_eval' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_shape18_undischarged_eval
