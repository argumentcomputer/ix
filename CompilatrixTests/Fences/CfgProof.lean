import Compilatrix.Cfg.Proof.Fuel

/-! Required axiom fences for Cfg's run loop (M2.5): under `Cfg.Ordered`
the frames' positions are a step-bound potential, so every `Cfg.run` is the
clocked outcome of its steps (`runs_run`) and clock monotone (`run_mono`).
Generated from the proof module's public theorems; expected messages are
preserved verbatim. -/

/-- info: 'Compilatrix.Cfg.foldl_add_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.foldl_add_eq

/-- info: 'Compilatrix.Cfg.Fun.size_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Fun.size_eq

/-- info: 'Compilatrix.Cfg.sum_drop_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.sum_drop_le

/-- info: 'Compilatrix.Cfg.sum_drop_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.sum_drop_eq

/-- info: 'Compilatrix.Cfg.le_sum_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.le_sum_of_mem

/-- info: 'Compilatrix.Cfg.Fun.block?_positions' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Fun.block?_positions

/-- info: 'Compilatrix.Cfg.Fun.fresh_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Fun.fresh_le

/-- info: 'Compilatrix.Cfg.Fun.fresh_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.Fun.fresh_lt

/-- info: 'Compilatrix.Cfg.takeEdge_next' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Cfg.takeEdge_next

/-- info: 'Compilatrix.Cfg.mem_edges_of_select' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.mem_edges_of_select

/-- info: 'Compilatrix.Cfg.potential_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.potential_next

/-- info: 'Compilatrix.Cfg.size_le_instrs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.size_le_instrs

/-- info: 'Compilatrix.Cfg.potential_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.potential_step

/-- info: 'Compilatrix.Cfg.fuel_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.fuel_enough

/-- info: 'Compilatrix.Cfg.runs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.runs_run

/-- info: 'Compilatrix.Cfg.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Cfg.run_mono
