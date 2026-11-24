import IxCK.Resource.Proof.CheckSound
import IxCK.Kernel.Audit.Axioms

/-!
# Mode-Soundness Certification Audit (`IxCK.Resource.Audit`)

Pins the exact transitive axiom boundaries of every certified mode-soundness
deliverable (`defaultOk`, `readsRespectErasure`, `check_sound_modeOk`, `f4`,
and `checkSound`), and audits every safe declaration under `IxCK.Resource.Proof`
against the standard logical axioms `[propext, Classical.choice, Quot.sound]`.
-/

#guard_module_axioms_under IxCK.Resource.Proof

#guard_kernel_axioms IxCK.Resource.Proof.defaultOk [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxCK.Resource.Proof.readsRespectErasure [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxCK.Resource.Proof.check_sound_modeOk [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxCK.Resource.Proof.f4 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxCK.Resource.Proof.checkSound [propext, Classical.choice, Quot.sound]

/-- info: 'IxCK.Resource.Proof.defaultOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxCK.Resource.Proof.defaultOk

/-- info: 'IxCK.Resource.Proof.readsRespectErasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxCK.Resource.Proof.readsRespectErasure

/-- info: 'IxCK.Resource.Proof.check_sound_modeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxCK.Resource.Proof.check_sound_modeOk

/-- info: 'IxCK.Resource.Proof.f4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxCK.Resource.Proof.f4

/-- info: 'IxCK.Resource.Proof.checkSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IxCK.Resource.Proof.checkSound
