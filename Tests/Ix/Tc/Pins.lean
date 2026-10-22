module

public import LSpec
public import Ix.Cli.CheckLeanCmd
public import Tests.Ix.Tc.ParityEnv

/-!
`tc-pins` (ignored runner): regression pins for the pure-Lean kernel
against a real serialized env (compiled on demand — see `Tests.Tc.ParityEnv`).
Each pin is a constant that previously OOMed, was falsely rejected at
depth 2001, or blew the worker stack (see the short-circuit note in
`Ix/Tc/DefEq.lean`; the host CheckCfg retains its stack reservation); the suite authenticates
the input once and checks each pin's producer under its original budget,
with complete supporting checks measured separately.
Budgets are generous — the pins guard ∞/OOM regression classes, not
micro-perf. Known-slow pins (open perf issues) run only with
`IX_PINS_SLOW=1`.
-/

namespace Tests.Tc.Pins

open LSpec

public structure Pin where
  /-- Fail-out-style label (meta-mode Lean name rendering). -/
  label : String
  /-- Budget for the selected producer's checker work, excluding reading/support. -/
  budgetMs : Nat := 60_000
  /-- Known-slow (open issue): skipped unless `IX_PINS_SLOW=1`. -/
  slow : Bool := false

/-- Regression classes from the 2026-07 check-lean debugging arc. -/
def pins : List Pin := [
  -- OOM class: the non-short-circuiting `(← a) && (← b)` port bug compared
  -- proof pairs whose value pair had already failed, materializing ~55k-step
  -- `Nat.le` derivations.
  { label := "Std.DTreeMap.Internal.Impl.minEntry!_eq_get!_minEntry?" },
  { label := "Std.DTreeMap.Internal.Impl.Const.minEntry!_eq_get!_minEntry?" },
  -- v4.33 moved this lemma out of `DTreeMap.Internal.Impl`; same statement
  -- shape, so the OOM-class coverage is unchanged.
  { label := "Std.Internal.List.minKey!_eq_get!_minKey?" },
  { label := "Std.Internal.List.minKey!_eq_head!_keys" },
  -- depth-2001 false-rejection class (same root cause); the first also
  -- exercises `«0»`-component label matching end to end.
  { label := "_private.Init.Data.Char.Ordinal.«0».Char.succ?_eq._proof_1_8" },
  { label := "Std.DHashMap.Internal.Raw₀.insertMany_cons" },
  { label := "Std.Tactic.BVDecide.BVExpr.Cache.Inv_insert" },
  -- Exponential-subst class: the `return`-skips-memo-tail bug in the
  -- Subst.lean/instUnivInner cached walkers turned shared-DAG
  -- instantiation into full tree walks (>25 min here pre-fix; ~0.6s
  -- fixed — see the `pure`-not-`return` notes in `liftCached`).
  { label := "Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q" },
]

/-- Check a fresh supporting closure over shared authenticated preparation.
The existing per-subject budget measures its actual producer's checker time;
input, preparation, reading and support checking are reported separately. -/
public def checkPin (prepared : Ix.Cli.CheckLeanCmd.PreparedInput) (pin : Pin) : IO TestSeq := do
  let expected ← match Ix.Cli.CheckLeanTargets.findCandidate prepared.inventory pin.label with
    | .ok c => pure c
    | .error _ => return test s!"{pin.label}: resolves unambiguously in the input" false
  let cfg : Ix.Cli.CheckLeanCmd.CheckCfg :=
    { workers := 1, silent := true, progressMs := 0, slowMs := 0 }
  match ← Ix.Cli.CheckLeanCmd.runPrepared prepared cfg (.only #[pin.label]) with
  | .error e => return test s!"{pin.label}: driver failed: {e.message}" false
  | .ok report =>
    if report.targets.size != 1 || report.targets.any (fun r => r.target.label != expected.label || r.target.address != expected.address || r.outcome != "accept") then
      return test s!"{pin.label}: exact accepted coverage (got {report.failures})" false
    let subjectMs := report.subjectMicros / 1000
    IO.println s!"tc-pins: {pin.label}: selected checker {subjectMs}ms; preparation {report.prepareMs}ms; \
      reading {report.readMicros / 1000}ms; support checker {report.supportMicros / 1000}ms; run {report.elapsedMs}ms"
    return test s!"{pin.label}: producer checked in {subjectMs}ms (budget {pin.budgetMs}ms)"
      (report.subjectMicros ≤ pin.budgetMs * 1000)

public def run : IO UInt32 := do
  IO.println "tc-pins"
  let path ← Tests.Tc.ParityEnv.ensureSelected
  let includeSlow := (← IO.getEnv "IX_PINS_SLOW").isSome
  let bytes ← IO.FS.readBinFile path
  match ← Ix.Cli.CheckLeanCmd.prepareInput bytes with
  | .error e => IO.eprintln s!"tc-pins: {e.message}"; return e.exitCode
  | .ok prepared =>
    IO.println s!"tc-pins: authenticated input ready in {prepared.prepareMs}ms ({prepared.inventory.size} labels)"
    let mut seq : TestSeq := .done
    for pin in pins do
      if pin.slow && !includeSlow then
        IO.println s!"tc-pins: skipping known-slow {pin.label} (set IX_PINS_SLOW=1 to include)"
      else seq := seq ++ (← checkPin prepared pin)
    lspecIO (.ofList [("tc-pins", [seq])]) []

end Tests.Tc.Pins
