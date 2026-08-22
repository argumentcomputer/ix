import Compilatrix.Sim
import Compilatrix.IxIR1.Sim
import Compilatrix.IxIR1.LowerSim
import Compilatrix.SimInstance
import Compilatrix.Ixon.Address

/-!
# Sorry/axiom fence (roadmap M0)

The mechanical fence for the roadmap's M0 "sorry/axiom fence" row: each
flagship theorem's axiom set is pinned with a `#guard_msgs`-checked
`#print axioms`, so `lake build` fails if a `sorryAx` or any new axiom
enters its dependency cone. Every pinned set is a subset of the intended
triple `propext`/`Classical.choice`/`Quot.sound`, spelled exactly as
reported (`invoke_fn_result_hasWorld` happens not to use
`Classical.choice`; a pin that widens is as much a diff as one that
breaks).

Deliberately **not** pinned: the codec laws for `Univ`, `Expr`,
`ConstantInfo`, and `Constant` (`roundtripLaw`/`canonicalLaw`). Their
proofs use `bv_decide`, and on this toolchain every `bv_decide` call
records a per-invocation native-reflection axiom
(`<thm>._native.bv_decide.ax_*` :
`Std.Tactic.BVDecide.Reflect.verifyBVExpr expr cert = true`) — compiler
trust outside the triple, with content-derived names too unstable to
pin. Fencing those eight requires first evicting the trust, e.g. by
replacing `bv_decide` with kernel-checked `decide` at the eight-bit
widths involved. Of the codec laws only `Address`'s two are
`bv_decide`-free and fenced here.
-/

/-! ## Erasure simulation (`Compilatrix/Sim.lean`) -/

/-- info: 'Compilatrix.Sim.erasure_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim

/-- info: 'Compilatrix.Sim.erasure_sim_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_closed

/-- info: 'Compilatrix.Sim.erasure_sim_inlineSharing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_inlineSharing

/-- info: 'Compilatrix.Sim.erasure_sim_inlineSharing_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Sim.erasure_sim_inlineSharing_closed

/-! ## IxIR₀ → IxIR₁ lowering soundness (`Compilatrix/IxIR1/Sim.lean`) -/

/-- info: 'Compilatrix.IxIR1.Sim.reuse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.reuse_sound

/-- info: 'Compilatrix.IxIR1.Sim.invoke_fn_result_hasWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.Sim.invoke_fn_result_hasWorld

/-! ## Whole-pass lowering instance (`Compilatrix/SimInstance.lean`)

The two boundaries the M2b ledger claims for the actual compiled
`add 2̂ 3̂` output: exact ownership contracts, and the source-to-target
`ValueGraph` forward simulation. Pinning them here is what makes
"without `native_decide`" mechanical rather than editorial. -/

/-- info: 'Compilatrix.SimInstance.addIxIR1CompilerContracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1CompilerContracts

/-- info: 'Compilatrix.SimInstance.addIxIR1SemanticForwardSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.SimInstance.addIxIR1SemanticForwardSimulation

/-! ## Semantic projection (`Compilatrix/IxIR1/LowerSim.lean`)

The premise-free member of the projection value pipeline: variable-target
projection needs no compiler-induction hypothesis, so its cone is the whole
borrow/fetch/retain/release argument. -/

/-- info: 'Compilatrix.IxIR1.LowerSim.lowerE_proj_var_run_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.LowerSim.lowerE_proj_var_run_value_sound

/-! ## Codec laws (`Compilatrix/Ixon/Address.lean`) -/

/-- info: 'Compilatrix.Ixon.Address.roundtripLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Address.roundtripLaw

/-- info: 'Compilatrix.Ixon.Address.canonicalLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixon.Address.canonicalLaw
