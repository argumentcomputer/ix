import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.Cli.FormalAiur
import Tests.Ix.IxVM.Harness

/-!
# The circuit's verdict in execution

Ordinary execution skips the assertions the IxVM program exports with
`runtimeCheck := false` (`constrain_eq!`, `Aiur.Library.U32`, `Aiur.Library.U64`,
`KernelNatPrim`'s `split_u32`): `dead_code::eliminate` makes each a no-op in the
execution copy of the program (`crates/aiur/src/bytecode/dead_code.rs`). The
circuit enforces them. So a witness can be accepted by execution and have no
circuit trace. Circuit-verdict mode (`IX_AIUR_CIRCUIT_VERDICT=1`,
`Tests.Ix.IxVM.Harness`) checks every assertion in execution.

This suite shows a witness on which the two verdicts differ, and that the mode
gives the circuit's. The reducibility hint of a definition is prover advice
(channel 3, `Ingress::load_constant_hint`), compared by
`UInt32::less_than_fields` when lazy delta unfolds two definitions
(`KernelDefEq::lazy_delta_step_const_const`). A hint at or above `2^32` cannot
be decomposed into four bytes, so the circuit has no trace for that witness
("u32 comparison right"). The honest hint answer truncates the operand
(`crates/aiur/src/library/u32.rs`), the comparison's other assertions are
skipped, and default execution takes the `_` arm and accepts.

Cases, each a `check` of `hintEq : hintA = hintB := rfl`:
- the compiled witness: accepted in both modes, through lazy delta;
- the same witness with `hintA`'s hint replaced by `2^32 + 7`: accepted by
  default execution, rejected in circuit-verdict mode at "u32 comparison right".

With `$IX_TEST_OUTPUT_DIR` set, both witnesses are also written as host inputs
(`circuit-verdict-honest.ixi`, `circuit-verdict-wide-hint.ixi`) so that a box job
can prove them: the honest one proves and verifies; the wide-hint one must fail
to prove, which is the circuit's own verdict on it.
-/

namespace Tests.Ix.IxVM.CircuitVerdict

-- Two distinct definitions (distinct content addresses) that are nonetheless
-- definitionally equal, so checking `hintEq` by `rfl` makes lazy delta unfold
-- both constants and compare their reducibility-hint ranks with
-- `UInt32::less_than_fields` — the gadget whose range checks are deferred.
def hintA : Nat := 5
def hintB : Nat := Nat.succ 4
theorem hintEq : hintA = hintB := rfl

open IxVM.ClaimHarness

/-- The channel-3 key of `a` (`addEntries`). -/
def hintKey (a : Address) : Array Aiur.G := a.hash.data.map .ofUInt8

/-- A hint no four-byte decomposition represents. -/
def wideHint : Nat := 2 ^ 32 + 7

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let env ← loadSharedIxonEnv #[``hintEq, ``hintA, ``hintB] leanEnv
  let target ← lookupAddr env ``hintEq
  let aAddr ← lookupAddr env ``hintA
  unless env.anonHints.contains aAddr do
    IO.eprintln s!"[ixvm-circuit-verdict] hintA has no reducibility hint in the compiled environment"
    return 1
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let honest ← IO.ofExcept (buildClaimWitness env (.check ctx target none))
  let wide : ClaimWitness :=
    { honest with inputIOBuffer := honest.inputIOBuffer.extend 3 (hintKey aAddr) #[.ofNat wideHint] }
  if let some dir ← IO.getEnv "IX_TEST_OUTPUT_DIR" then
    IO.FS.createDirAll dir
    for (name, w) in [("honest", honest), ("wide-hint", wide)] do
      IO.FS.writeBinFile (System.FilePath.mk dir / s!"circuit-verdict-{name}.ixi")
        (Ix.Cli.FormalAiur.invocation w.input w.inputIOBuffer)
  let lazy := some "KernelDefEq::lazy_delta_step_const_const"
  let mkCase (label : String) (w : ClaimWitness) (accept : Bool)
      (rejectsWith exercises : Option String := none) : Builder := fun _ =>
    .ok { label, accept, rejectsWith, exercises, witness := w }
  let execution ← runCases "ixvm-circuit-verdict (execution)" (circuit := some false) #[
    mkCase "compiled hints, execution verdict" honest true (exercises := lazy),
    mkCase "hint 2^32+7, execution verdict (accepted: the deferred range check is skipped)"
      wide true (exercises := lazy)]
  let circuit ← runCases "ixvm-circuit-verdict (circuit)" (circuit := some true) #[
    mkCase "compiled hints, circuit verdict" honest true (exercises := lazy),
    mkCase "hint 2^32+7, circuit verdict (no trace: the operand has no u32 decomposition)"
      wide false (rejectsWith := some "u32 comparison")]
  return if execution == 0 && circuit == 0 then 0 else 1

end Tests.Ix.IxVM.CircuitVerdict
