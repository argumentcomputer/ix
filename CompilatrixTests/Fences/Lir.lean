import Compilatrix.Lir.Operands

/-! Required axiom fences for Lir: the operand metadata and frame lemmas the
allocator's validator will rely on. Expected messages are preserved
verbatim. -/

/-- info: 'Compilatrix.Lir.Term.setEdges_edges' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Lir.Term.setEdges_edges

/-- info: 'Compilatrix.Lir.Stmt.operandUses_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Stmt.operandUses_eq

/-- info: 'Compilatrix.Lir.Stmt.operandDefs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Stmt.operandDefs_eq

/-- info: 'Compilatrix.Lir.Term.operandUses_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Term.operandUses_eq

/-- info: 'Compilatrix.Lir.Term.operandDefs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Term.operandDefs_eq

/-- info: 'Compilatrix.Lir.Agree.append_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Agree.append_left

/-- info: 'Compilatrix.Lir.Agree.append_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Agree.append_right

/-- info: 'Compilatrix.Lir.Arg.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Arg.eval_congr

/-- info: 'Compilatrix.Lir.evalArgs_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.evalArgs_congr

/-- info: 'Compilatrix.Lir.Addr.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Addr.eval_congr

/-- info: 'Compilatrix.Lir.Rhs.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Rhs.eval_congr

/-- info: 'Compilatrix.Lir.Stmt.exec_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lir.Stmt.exec_frame
