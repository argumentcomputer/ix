import IxCC.Ixon.V3.Catalog

/-! Catalog admission rests on the standard axioms (its hashes are pure BLAKE3).
These fences certify execution and binding, not whole-checker soundness. -/

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.source_loaded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.source_loaded

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.scope_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.scope_checked

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.content_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.content_root

/-- info: 'IxCC.Ixon.V3.Catalog.Admitted.typing_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ixon.V3.Catalog.Admitted.typing_checked
