import IxCC.Lir.Operands

/-! Required axiom fences for Lir: the operand metadata and frame lemmas the
allocator's validator will rely on. Expected messages are preserved
verbatim. -/

/-- info: 'IxCC.Lir.Term.setEdges_edges' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lir.Term.setEdges_edges

/-- info: 'IxCC.Lir.Stmt.operandUses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Stmt.operandUses_eq

/-- info: 'IxCC.Lir.Stmt.operandDefs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Stmt.operandDefs_eq

/-- info: 'IxCC.Lir.Term.operandUses_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Term.operandUses_eq

/-- info: 'IxCC.Lir.Term.operandDefs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Term.operandDefs_eq

/-- info: 'IxCC.Lir.Agree.append_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Agree.append_left

/-- info: 'IxCC.Lir.Agree.append_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Agree.append_right

/-- info: 'IxCC.Lir.Arg.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Arg.eval_congr

/-- info: 'IxCC.Lir.evalArgs_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.evalArgs_congr

/-- info: 'IxCC.Lir.Addr.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Addr.eval_congr

/-- info: 'IxCC.Lir.Rhs.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Rhs.eval_congr

/-- info: 'IxCC.Lir.Stmt.exec_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lir.Stmt.exec_frame
