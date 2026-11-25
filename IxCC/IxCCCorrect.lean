import IxCCCorrect.Claim
import IxCCCorrect.Process
import IxCCCorrect.Tiers
import IxCCCorrect.Routes
import IxCCCorrect.Today
import IxCCCorrect.Progress
import IxCCCorrect.Shape
import IxCCCorrect.Shape1
import IxCCCorrect.Shape1Check
import IxCCCorrect.Shape2
import IxCCCorrect.Shape2Check
import IxCCCorrect.Shape2Produce
import IxCCCorrect.ShapeHook
import IxCCCorrect.ShapeTree
import IxCCCorrect.Compile
import IxCCCorrect.CompileCertified
import IxCCCorrect.GroundRoot
import IxCCCorrect.GroundCheck
import IxCCCorrect.Compose
import IxCCCorrect.ComposeExe
import IxCCCorrect.GroundShape
import IxCCCorrect.ComposeExit
import IxCCCorrect.UniqueIota
import IxCCCorrect.UniqueNat
import IxCCCorrect.Unique
import IxCCCorrect.Fence

/-!
# `IxCCCorrect`: the target statements of IxCC

What a compiled executable's argument has to establish, written as Lean
propositions that elaborate, and what the existing theorems establish today.

* `IxCCCorrect.Claim`: the public claim (`Claim`), its ABI and its binding to a
  shipped file (`Claim.Binds`).
* `IxCCCorrect.Process`: the process of a shipped file over the existing
  processor and system-call specifications (`LoadedFile`, `execImage`), and what a
  trace shows (`stdout`, `exitStatus`, `SysAllowed`, `Kept`, `Ended`).
* `IxCCCorrect.Tiers`: kernel meaning (`Admits`, `Agrees`), the three tiers
  (`Tier1`, `Tier2`, `Tier3`) and `Correct`.
* `IxCCCorrect.Routes`: the certified and the certifying route as statements
  (`CertifiedRoute`, `CertifyingRoute`).
* `IxCCCorrect.Today`: `CorrectToday`, and the proof that today's verifier
  establishes it (`correctToday_of_accepts`).
* `IxCCCorrect.Progress`: source progress in the two strengths the tiers need
  (`NeverStuck`, `NeverWrong`), the targets (`SafetyProgress`,
  `FunctionalProgress`), and the proofs that each strength removes the
  "source goes wrong" disjunct from `Recheck.sound`, `RcReplay.sound` and the plain
  executable theorems.
* `IxCCCorrect.Shape`: the first program class with progress proved (`allOk`,
  `neverWrong_of_shape`), by a syntactic typing of SrcEval's values.
* `IxCCCorrect.Shape1`, `IxCCCorrect.Shape1Check`: the second class, first-order
  `Nat` and enumeration programs with irrelevant positions, `case` and recursors,
  with its decision (`certOk`, `neverWrong_of_cert_nat`).
* `IxCCCorrect.Shape2`, `IxCCCorrect.Shape2Check`: the third class, with data
  (constructors with parameters and fields, `case` at data, projections), its decision,
  and `run_ok_vals`, the unviewed statement at any shaped argument values.
* `IxCCCorrect.Shape2Produce`: an untrusted producer of shape certificates from a
  checked source program (run on the committed closures by `tests-shape`).
* `IxCCCorrect.ShapeHook`: the shape check beside the recheck path (`runShaped`), and
  `Recheck.sound` with no "source goes wrong" case from its acceptance alone
  (`runShaped_sound`); `neverStuck_checked`, the unviewed statement.
* `IxCCCorrect.ShapeTree`: results with fields on the reference-counted path: the
  decision that the tree view reads a result shape (`mapReads`, `reads_val`), and
  `rcRunShaped_sound`, `RcReplay.sound` with no "source goes wrong" case for `Nat` and
  constructor-tree results.
* `IxCCCorrect.Compile`: the certified route as it stands. `CompiledToday`, the
  proposition of `CorrectToday`'s strength about the pure compiler's output
  (`IxCC.Compile.compile`), with the proof that every output meets it
  (`compile_today`, `compile_route`), and `compileWith`, the compiler with the two
  further checks of the route between its stages.
* `IxCCCorrect.CompileCertified`: the certified route's compiler, `compile`
  followed by the untrusted shape producer and the hook's shape decision
  (`compileCertified`, declining with a typed reason), and its theorem with no
  "source goes wrong" escape (`CompiledSound`, `compileCertified_sound`).
* `IxCCCorrect.GroundRoot`, `IxCCCorrect.GroundCheck`: the grounding root theorem at a
  canonical result in the existence form `SameDenotation` asks for (`Grounded.same`), and
  `groundCheck`, the Denotes-free pipeline decision that establishes its hypotheses on what the
  certificate checker checked (`groundCheck_sound`).
* `IxCCCorrect.Compose`, `IxCCCorrect.ComposeExe`: the compiled object, and what the plain
  executable prints, agree with the kernel meaning of the claimed address
  (`recheck_agrees`, `plain_exe_tier1Stdout`), under `NeverWrong` and `ReturnsCanon`.
* `IxCCCorrect.GroundShape`: the same with the shape check deciding both hypotheses
  (`groundShapeCheck_sound`, `recheck_agrees_shaped`, `plain_exe_tier1Stdout_shaped`), and the
  check a `compile` calls (`tier1Check`, `tier1Check_sound`: `Admits` and the first clause of
  `Tier1` for the checked core).
* `IxCCCorrect.ComposeExit`: the second clause of `Tier1` (a trace that exits with status 0 wrote
  the whole rendering of an agreeing answer), and `tier1Check_sound_core`: `Admits` and both
  clauses for the checked core (`Tier1Core`), all but the shipped-file link of `Tier1`.
* `IxCCCorrect.Unique`: two answers that agree are equal, at a `Nat` result, where a set theory
  exists and the environment stores what separates numerals (`agrees_unique`).
* `IxCCCorrect.UniqueIota`: the same with `Bool.true ≠ Bool.false` from the `Bool` recursor's
  ι-law, so no stored witness theorem is needed (`agrees_unique_iota`).
* `IxCCCorrect.UniqueNat`: the same through `Nat.rec`'s ι-law (zero is no successor, the
  successor is injective), with neither `Nat.beq` nor `Bool` read (`agrees_unique_rec`).
* `IxCCCorrect.Fence`: the library's axiom fence, an exact `#print axioms`
  assertion for every theorem above (each within `propext`, `Classical.choice`,
  `Quot.sound`).

The tiers, the routes and the two progress targets are definitions: nothing here
proves them. The library
imports the compiler (`IxCC`), the grounding library (`IxCCGrounding`) and
the kernel's model statement (`IxCK.Kernel.Denotes`), so it is outside the
production import root (`IxCC` must not import the grounding library, the
kernel's model or this library, `IxCC.Tools.BuildGraph`). It is built, with its
fence, by the required check `ixcc-grounding`, beside the grounding library.
-/
