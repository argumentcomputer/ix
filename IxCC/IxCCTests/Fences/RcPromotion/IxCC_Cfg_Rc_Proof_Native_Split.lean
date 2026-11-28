import IxCC.Cfg.Rc.Proof.Native.Split

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Public.Spec.accepted_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.accepted_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.assemble_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.assemble_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.drop_split' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.drop_split

/-- info: 'IxCC.Cfg.Rc.Public.Spec.program_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Public.Spec.program_split

/-- info: 'IxCC.Cfg.Rc.InlineWrappers.inlineProgram_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.InlineWrappers.inlineProgram_sim

/-- info: 'IxCC.Cfg.Rc.InlineWrappers.inlineProgram_sim_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.InlineWrappers.inlineProgram_sim_clock

/-- info: 'IxCC.Cfg.Rc.FastDec.install_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.FastDec.install_sim

/-- info: 'IxCC.Cfg.Rc.FastDec.install_forward_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.FastDec.install_forward_eq

/-- info: 'IxCC.Cfg.Rc.Prune.pruneDeadRuntime_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Prune.pruneDeadRuntime_eval_eq

/-- info: 'IxCC.Cfg.Rc.Prune.pruneDeadRuntime_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Prune.pruneDeadRuntime_sim
