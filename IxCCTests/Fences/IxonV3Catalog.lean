import IxCC.Ixon.V3.Catalog

/-! Catalog admission preserves the existing logical and native BLAKE3 basis.
These fences certify execution and binding, not whole-checker soundness. -/

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.source_loaded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.source_loaded

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.scope_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.scope_checked

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.content_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.content_root

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.typing_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.typing_checked
