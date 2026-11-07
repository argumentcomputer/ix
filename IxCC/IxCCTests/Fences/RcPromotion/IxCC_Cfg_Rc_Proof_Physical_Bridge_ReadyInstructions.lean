import IxCC.Cfg.Rc.Proof.Physical.Bridge.ReadyInstructions

/-! Exact accepted RC axiom inventory. -/

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.decrement_ready_instruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.decrement_ready_instruction

/-- info: 'IxCC.Cfg.Rc.Proof.Physical.Bridge.increment_ready_instruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Proof.Physical.Bridge.increment_ready_instruction
