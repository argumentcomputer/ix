import IxCC.Recheck.Rc.Proof.Reentry

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.HeapState.numeric_reentry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.HeapState.numeric_reentry

/-- info: 'IxCC.Cfg.Rc.Native.Spec.recycled_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.recycled_entry

/-- info: 'IxCC.Cfg.Rc.Native.Spec.recycled_call_and_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.recycled_call_and_release

/-- info: 'IxCC.Cfg.Rc.Native.Spec.recycled_call_and_release_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.recycled_call_and_release_idle

/-- info: 'IxCC.Cfg.Rc.Native.Spec.RecycledPrefix.final_heapState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.RecycledPrefix.final_heapState

/-- info: 'IxCC.Cfg.Rc.Native.Spec.RecycledPrefix.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.RecycledPrefix.append

/-- info: 'IxCC.Cfg.Rc.Native.Spec.RecycledPrefix.next_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.RecycledPrefix.next_entry

/-- info: 'IxCC.Cfg.Rc.Native.Spec.recycled_session' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.recycled_session

/-- info: 'IxCC.Cfg.Rc.Native.Spec.recycled_session_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.recycled_session_idle
