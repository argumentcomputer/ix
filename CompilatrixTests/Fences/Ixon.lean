import Compilatrix.Ixon.Address
import Compilatrix.Ixon.Const
import Compilatrix.Ixon.Eval
import Compilatrix.Ixon.Expr
import Compilatrix.Ixon.Sharing.Indexed
import Compilatrix.Ixon.Univ
import Compilatrix.Ixon.UsageCheck

/-! Required axiom fences for Ixon; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Ixon.Eval.projectValue_ok_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Eval.projectValue_ok_of_strict

/-- info: 'Compilatrix.Ixon.UsageCheck.closureWorld_shared_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixon.UsageCheck.closureWorld_shared_iff

/-- info: 'Compilatrix.Ixon.UsageCheck.check_lam_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.UsageCheck.check_lam_shared

/-- info: 'Compilatrix.Ixon.Address.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Address.roundtripLaw

/-- info: 'Compilatrix.Ixon.Address.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Address.canonicalLaw

/-- info: 'Compilatrix.Ixon.Univ.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Univ.roundtripLaw

/-- info: 'Compilatrix.Ixon.Univ.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Univ.canonicalLaw

/-- info: 'Compilatrix.Ixon.Expr.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Expr.roundtripLaw

/-- info: 'Compilatrix.Ixon.Expr.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Expr.canonicalLaw

/-- info: 'Compilatrix.Ixon.ConstantInfo.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.ConstantInfo.roundtripLaw

/-- info: 'Compilatrix.Ixon.ConstantInfo.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.ConstantInfo.canonicalLaw

/-- info: 'Compilatrix.Ixon.Constant.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Constant.roundtripLaw

/-- info: 'Compilatrix.Ixon.Constant.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Constant.canonicalLaw

/-- info: 'Compilatrix.Ixon.Sharing.Indexed.compress_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Sharing.Indexed.compress_eq

/-- info: 'Compilatrix.Ixon.Sharing.Indexed.canonicalWith_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Sharing.Indexed.canonicalWith_eq

/-- info: 'Compilatrix.Ixon.Sharing.Indexed.compile_ixonV2CanonicalWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Sharing.Indexed.compile_ixonV2CanonicalWith
