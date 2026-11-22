import IxC.Resource.Proof.CheckSound
import IxC.Kernel.Audit.Axioms

/-!
# Mode-Soundness Certification Audit (`IxC.Resource.Audit`)

Pins the exact transitive axiom boundaries of every certified mode-soundness
deliverable (`defaultOk`, `readsRespectErasure`, `check_sound_modeOk`, `f4`,
and `checkSound`), and audits every safe declaration under `IxC.Resource.Proof`
against the standard logical axioms `[propext, Classical.choice, Quot.sound]`.
-/

#guard_module_axioms_under IxC.Resource.Proof

#guard_kernel_axioms IxC.Resource.Proof.defaultOk [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxC.Resource.Proof.readsRespectErasure [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxC.Resource.Proof.check_sound_modeOk [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxC.Resource.Proof.f4 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxC.Resource.Proof.checkSound [propext, Classical.choice, Quot.sound]

/-- info: 'IxC.Resource.Proof.defaultOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxC.Resource.Proof.defaultOk

/-- info: 'IxC.Resource.Proof.readsRespectErasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxC.Resource.Proof.readsRespectErasure

/-- info: 'IxC.Resource.Proof.check_sound_modeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxC.Resource.Proof.check_sound_modeOk

/-- info: 'IxC.Resource.Proof.f4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxC.Resource.Proof.f4

/-- info: 'IxC.Resource.Proof.checkSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxC.Resource.Proof.checkSound
