import IxCC.Cfg.Proof.Fuel

/-! Required axiom fences for Cfg's run loop (M2.5): under `Cfg.Ordered`
the frames' positions are a step-bound potential, so every `Cfg.run` is the
clocked outcome of its steps (`runs_run`) and clock monotone (`run_mono`).
Generated from the proof module's public theorems; expected messages are
preserved verbatim. -/

/-- info: 'IxCC.Cfg.foldl_add_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.foldl_add_eq

/-- info: 'IxCC.Cfg.Fun.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Fun.size_eq

/-- info: 'IxCC.Cfg.sum_drop_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.sum_drop_le

/-- info: 'IxCC.Cfg.sum_drop_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.sum_drop_eq

/-- info: 'IxCC.Cfg.le_sum_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.le_sum_of_mem

/-- info: 'IxCC.Cfg.Fun.block?_positions' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Fun.block?_positions

/-- info: 'IxCC.Cfg.Fun.fresh_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Fun.fresh_le

/-- info: 'IxCC.Cfg.Fun.fresh_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Fun.fresh_lt

/-- info: 'IxCC.Cfg.takeEdge_next' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.takeEdge_next

/-- info: 'IxCC.Cfg.mem_edges_of_select' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.mem_edges_of_select

/-- info: 'IxCC.Cfg.potential_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.potential_next

/-- info: 'IxCC.Cfg.size_le_instrs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.size_le_instrs

/-- info: 'IxCC.Cfg.potential_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.potential_step

/-- info: 'IxCC.Cfg.fuel_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.fuel_enough

/-- info: 'IxCC.Cfg.runs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.runs_run

/-- info: 'IxCC.Cfg.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.run_mono
