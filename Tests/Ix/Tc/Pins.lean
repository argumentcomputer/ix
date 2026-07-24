module

public import LSpec
public import Ix.Tc
public import Ix.Cli.CheckLeanCmd

/-!
`tc-pins` (ignored runner): regression pins for the pure-Lean kernel
against a real serialized env (`IX_PINS_IXE`, e.g. `compileinitstd.ixe`).
Each pin is a constant that previously OOMed, was falsely rejected at
depth 2001, or blew the worker stack (see the short-circuit note in
`Ix/Tc/DefEq.lean` and `ParCheckCfg.stackBytes`); the suite ingresses
the env once and checks each pin subject-only under a wall-clock budget.
Budgets are generous — the pins guard ∞/OOM regression classes, not
micro-perf. Skips (passing) when `IX_PINS_IXE` is unset so `--ignored`
sweeps don't require the env file; known-slow pins (open perf issues)
run only with `IX_PINS_SLOW=1`.
-/

namespace Tests.Tc.Pins

open LSpec
open Ix.Tc

structure Pin where
  /-- Fail-out-style label (meta-mode Lean name rendering). -/
  label : String
  /-- Wall-clock budget for the subject-only check. -/
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
  { label := "Std.DTreeMap.Internal.Impl.minKey!_eq_get!_minKey?" },
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

/-- Check one pin subject-only over the shared ingressed env (fresh
    single worker per pin: per-pin cache isolation, deterministic
    budget). -/
def checkPin (kenv : MetaEnv) (prims : Primitives .meta)
    (work : Array (CheckWorkItem .meta)) (pin : Pin) : IO TestSeq := do
  let (sel, unmatched) := Ix.Cli.CheckLeanCmd.selectWork work
    (fun id => toString id.name) #[pin.label]
  if !unmatched.isEmpty || sel.isEmpty then
    return test s!"{pin.label}: resolves in env" false
  let cfg : ParCheckCfg :=
    { workers := 1, silent := true, progressMs := 0, stuckMs := 0,
      slowMs := 0, clearEvery := 0 }
  let report ← checkEnvParallel kenv prims sel
    (labelOf := toString) (failLabelOf := fun id => toString id.name) cfg
  if !report.failures.isEmpty then
    let (_, msg) := report.failures[0]!
    return test s!"{pin.label}: passes (got: {msg})" false
  return test
    s!"{pin.label}: passes in {report.elapsedMs}ms (budget {pin.budgetMs}ms)"
    (report.elapsedMs ≤ pin.budgetMs)

public def run : IO UInt32 := do
  IO.println "tc-pins"
  let some path ← IO.getEnv "IX_PINS_IXE"
    | IO.println "tc-pins: IX_PINS_IXE unset — skipping (point it at a \
                  compileinitstd-style .ixe to run the pins)"
      return 0
  let includeSlow := (← IO.getEnv "IX_PINS_SLOW").isSome
  if !(← System.FilePath.pathExists path) then
    IO.eprintln s!"tc-pins: IX_PINS_IXE file not found: {path}"
    return 1
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile path
  match Ixon.deEnv bytes with
  | .error e => IO.eprintln s!"tc-pins: deserialize failed: {e}"; return 1
  | .ok ixonEnv =>
    match ingressMetaEnvParallel ixonEnv with
    | .error e => IO.eprintln s!"tc-pins: ingress failed: {e}"; return 1
    | .ok kenv =>
      let work := buildCheckWork kenv
      let prims := Primitives.fromEnv kenv
      IO.println s!"tc-pins: env ready in {(← IO.monoMsNow) - t0}ms \
                    ({kenv.consts.size} consts, {work.size} work items)"
      let mut seq : TestSeq := .done
      for pin in pins do
        if pin.slow && !includeSlow then
          IO.println s!"tc-pins: skipping known-slow {pin.label} \
                        (set IX_PINS_SLOW=1 to include)"
        else
          seq := seq ++ (← checkPin kenv prims work pin)
      lspecIO (.ofList [("tc-pins", [seq])]) []

end Tests.Tc.Pins
