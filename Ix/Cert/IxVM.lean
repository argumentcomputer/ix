import IxC.Kernel.Audit.Axioms
import Ix.Cert.IxVM.RoleSpec
import Ix.Cert.IxVM.RoleAdmission
import Ix.Cert.IxVM.ConvertBridge
import Ix.Cert.IxVM.KernelBridge
import Ix.Cert.IxVM.CodecBridge
import Ix.Cert.IxVM.FuelFreeKernel
import Ix.Cert.IxVM.CircuitCorrespondence

/-! # Certified `IxVM` ↔ `IxC` Correspondence Bridge & Axiom Audit

This umbrella module exports the certified `IxVM` ↔ `IxC` correspondence suite:
- `IxC.Kernel.Ixon.RoleSpecTable` and `Ix.Cert.IxVM.RoleSpec`:
  Pure DAG specification table generation (`buildSpecUniv`, `buildSpecExpr`,
  `buildAnchorType`, `buildAxiomType`, `buildEqnType`, `buildOpEqs`, `buildEqnList`,
  `buildRoleBlockExpected`), exact reconstruction proofs (`evalSpecUniv`, `evalSpecExpr`)
  under any `RoleTable` resolver `t.keyOf`, and Formal Aiur `KernelRoleSpec.aiur`
  code generation (`IxVM.RoleSpecGen.renderFormalAiur`).
- `Ix.Cert.IxVM.RoleAdmission`:
  Bridge between `IxVM`'s eager role binding admission/validation (`validate_binding`,
  `validate_role`) and `IxC`'s `Ix.Kernel.Admission.admitBinding`,
  `Ix.Kernel.Admission.BindingAdmitted`, and `Ix.Kernel.Role.spec`.
- `Ix.Cert.IxVM.ConvertBridge`:
  Bridge between `IxVM`'s `Convert` / `Ingress` (`convert_univ`, `unshare`,
  `expand_sharing_vec` + `subst_refs_univs`, `get_ci` projection resolution
  `dPrj`/`iPrj`/`rPrj`/`cPrj`, `projection_addr`, and constant lowering) and `IxC`'s
  `Ix.Kernel.Reader` (`convUniv`, `unshare`, `MemberReader.read`, `resolveSource`,
  `Admission.projectionAddress`, `readRecord`).
- `Ix.Cert.IxVM.KernelBridge`:
  Fuel-existence and simulation lemmas connecting `IxVM`'s operational checks
  (`whnf`, `NatPrim`, `k_is_def_eq`, `k_infer`, `k_infer_only`, `check_const`,
  `walk_refs_transitive`, `env_walk_all`) to `Ix.Kernel.CoreFns`, `Ix.Kernel.checkDecl`,
  `Ix.Kernel.Cached.AcceptsRef .verified`, `Ix.Cert.IxonAcceptsRef`, `StrongModel`,
  `ValueModel`, and `No Proof of False`.
- `Ix.Cert.IxVM.CodecBridge`:
  Wire codec and claim deserialization correspondence connecting `IxVM`'s
  `get_tagn4/2/0`, `put_tagn4/2/0`, `get_univ`, `get_expr`, `get_constant`,
  `put_constant`, `run_claim`, channel-6 role binding parser, and Blake3-authenticated
  record/blob streams to `Ixon.getTagN`, `Ixon.putTagN`, `Ixon.deConstantExact`,
  `Ixon.serConstant`, `Ixon.Canonical.deConstant`, `Ix.Claim.de`,
  `RoleTable.ofBytes_eq_some_iff`, and `Admission.authenticate_ok_iff`.
- `Ix.Cert.IxVM.FuelFreeKernel`:
  Fuel-free big-step inductive `IxVM` kernel semantics (`IxVMWhnfCoreStep`,
  `IxVMWhnfStep`, `IxVMDefEqStep`, `IxVMInferStep`, `IxVMInferIOStep`,
  `IxVMEnsureSortStep`, `IxVMAnnotateStep`, `IxVMCheckDeclStep`,
  `IxVMFuelFreeWalkDecls`), multi-call fuel composition via `max`, and the
  end-to-end compiler + `IxVM` commutation theorems (`ixvm_compile_commutes`,
  `ixvm_compile_commutes_nominal`).
- `Ix.Cert.IxVM.CircuitCorrespondence`:
  Unified top-level bridge connecting Formal `Aiur` activated grouped physical
  circuit derivations (`Aiur.Modules.Prepared.grouped_activated_heap_sound`) and
  Goldilocks `Ingress` BLAKE3 stream authentication (`ingress_verify_stream_sound`)
  with `IxVMCircuitAcceptsClaim`, `Ix.Cert.IxonAcceptsRef`, ZFC `StrongModel` /
  `ValueModel` / consistency, and end-to-end compiler + Formal `Aiur` `IxVM`
  circuit commutation (`ixvm_circuit_compile_commutes`,
  `ixvm_circuit_compile_commutes_nominal`).

Every theorem is verified below with `#guard_kernel_axioms` and `#guard_module_axioms`
to depend only on `[propext, Classical.choice, Quot.sound]`.
-/

#guard_module_axioms
  IxC.Kernel.Ixon.RoleSpecTable
  Ix.Cert.IxVM.RoleSpec
  Ix.Cert.IxVM.RoleAdmission
  Ix.Cert.IxVM.ConvertBridge
  Ix.Cert.IxVM.KernelBridge
  Ix.Cert.IxVM.CodecBridge
  Ix.Cert.IxVM.FuelFreeKernel
  Ix.Cert.IxVM.CircuitCorrespondence

-- 1. RoleSpec & DAG Table Reconstruction Theorems
#guard_kernel_axioms Ix.Kernel.buildSpecUniv_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildSpecUnivList_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildSpecExpr_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.substRoleKeysM_roleKeyOf [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildSpecExpr_eval_roleKeyOf [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildAnchorType_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildAxiomType_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildEqnType_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildOpEqEntry_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildEqnStatementEntry_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.buildRoleBlockMember_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Role.specAllClosedWF_eq_true [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Role.all_specAllClosedWF [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.checkGroups_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.role_spec_dag_sound [propext, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.role_spec_dag_roleKeyOf [propext, Quot.sound]

-- 2. Role Admission & Validation Bridge Theorems
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_validate_binding_iff_bindingAdmitted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_validate_binding_admitBinding [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_validate_binding_blake3 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.roleTable_check_properties [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.validate_anchor_role_bridge [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.validate_axiom_role_bridge [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.validate_eqn_type_role_bridge [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.validate_op_eq_entry_bridge [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.validate_eqn_statement_entry_bridge [propext, Classical.choice, Quot.sound]

-- 3. Unsharing & Constant Lowering Bridge Theorems
#guard_kernel_axioms Ix.Cert.IxVM.ixvmConvertUniv_eq_convUniv [propext]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmUnshare_eq_unshare [propext]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmConvertExpr_eq_memberReader_read [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmResolveSource_eq_resolveSource [propext]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmProjectionAddr_eq_projectionAddress [propext, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmCtorProjectionAddr_eq_projectionAddress [propext, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmReadProj_eq_readRecord [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmReadAxiom_eq_readRecord [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmReadQuot_eq_readRecord [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmReadDefn_eq_readRecord [propext, Classical.choice, Quot.sound]

-- 4. Kernel Evaluator, Typechecker & Claim Walk Bridge Theorems
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_whnfCore_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_whnf_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_defeq_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_infer_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_infer_only_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_annotate_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_ensureSort_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_whnf_step [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_defeq_step [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_infer_step [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_infer_only_step [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_natPrim_succ_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_natPrim_binOp_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.IxVMCheckConstRef.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.IxVMWalkDecls.append [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_walk_decls_iff_foldlM [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_env_walk_all_iff_acceptsRef [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_accepts_iff_ixonAcceptsRef [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_accepts_strongModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_accepts_valueModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_accepts_no_proof_of_False [propext, Classical.choice, Quot.sound]

-- 5. Wire Codec & Claim Deserialization Bridge Theorems
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_getTagN_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_getTagN4_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_getTagN2_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_getTagN0_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_putTagN_inj [propext, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_getTagN_inj [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_parseUniv_serUniv [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_parseExpr_serExpr [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_parseConstant_serConstant [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_parseConstant_noTrailing [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_validConstant_iff_wireWF [propext, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_canonical_deConstant_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_canonical_imp_parseConstantExact [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_canonical_deConstant_noTrailing [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_parseConstantExact_resource_bound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_channel6_roleTable_ofBytes_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_authenticate_stream_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_decodeRecords_iff [propext, Classical.choice, Quot.sound]

-- 6. Fuel-Free Inductive Kernel Semantics & End-to-End Compiler Commutation Theorems
#guard_kernel_axioms Ix.Cert.IxVM.ixvmWhnfCoreStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmWhnfStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmDefEqStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmEnsureSortStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmInferStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmInferIOStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmAnnotateStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmCheckConstantValStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmCheckDefnValStep_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmCheckDeclStep_iff_checkConstRef [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmFuelFreeWalkDecls_iff_walkDecls [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmFuelFreeWalkDecls_iff_acceptsRef [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_accepts_unique_env [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvmCommutesCovering_iff_ixonCommutesCovering [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_compile_commutes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_compile_commutes_nominal [propext, Classical.choice, Quot.sound]

-- 7. Unified Formal Aiur Circuit ↔ IxVM ↔ IxC ↔ Set-Theoretic Model Bridge Theorems
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_activated_derives_evalFn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_ingress_stream_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_derives_imp_circuitAccepts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_accepts_iff_ixvmAcceptsClaim [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_accepts_iff_ixonAcceptsRef [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_strongModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_valueModel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_compile_commutes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxVM.ixvm_circuit_compile_commutes_nominal [propext, Classical.choice, Quot.sound]
