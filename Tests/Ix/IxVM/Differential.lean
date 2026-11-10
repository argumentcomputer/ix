import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.CompileCertified
import Lean.Replay
import Ix.EnvScope
import Tests.Ix.IxVM.Harness

/-!
# Differential harness: IxVM against Lean's official kernel on a real corpus

For each constant of a corpus, compare IxVM's verdict (a `check` claim through
the program in circuit-verdict mode, `Tests.Ix.IxVM.Harness`) with Lean's
official kernel's. The records come from the certified compiler
(`Ix.CompileM.compileCertified`, which `ix compile` and `loadSharedIxonEnv`
use). The kernel is driven from this `Tests` module, by
`Lean.Kernel.Environment.replay`, which sends each declaration to the kernel
and checks that constructors and recursors match those it regenerates.

A corpus is a set of source-module prefixes (`IX_DIFF_MODULES`, comma-separated;
default `Init`), selecting the constants whose source module has one of those
prefixes, closed under dependencies. `IX_DIFF_LIMIT` caps how many constants the
IxVM side submits (0 = all), so a run fits a budget; the Lean side replays the
whole set regardless. `IX_DIFF_SEED` and `IX_DIFF_LIMIT` together take an evenly
spaced sample when the corpus exceeds the cap.

Output: a per-constant verdict table (printed by the host per case and
summarized here) and a summary line. Expected: agreement everywhere except the
known divergences — none for an honest corpus, since every constant Lean
accepts IxVM should accept, and the corpus holds nothing Lean rejects. An IxVM
rejection of a Lean-accepted constant, or the reverse, is a finding, recorded
with its Ixon fixture.

Lean's kernel replay skips unsafe and partial constants (it cannot check them);
those are reported as `lean-skipped` and compared only when IxVM also declines
to treat them as checked.
-/

namespace Tests.Ix.IxVM.Differential

open IxVM.ClaimHarness

/-- The corpus module prefixes (`IX_DIFF_MODULES`, default `Init`). -/
def corpusPrefixes : IO (List Lean.Name) := do
  let raw := (← IO.getEnv "IX_DIFF_MODULES").getD "Init"
  return (raw.splitOn ",").filterMap fun s =>
    let s := s.trimAscii.toString
    if s.isEmpty then none else some s.toName

/-- The constants of `leanEnv` whose source module has one of `prefixes`,
closed under dependencies (`collectSelectedDeps`). -/
def corpusConstants (leanEnv : Lean.Environment) (prefixes : List Lean.Name) :
    List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let moduleNames := leanEnv.allImportedModuleNames
  let mut seeds : List Lean.Name := []
  for (n, _) in leanEnv.constants.toList do
    if let some idx := leanEnv.getModuleIdxFor? n then
      let mod := moduleNames[idx.toNat]!
      if prefixes.any (·.isPrefixOf mod) then seeds := n :: seeds
  return Ix.EnvScope.collectSelectedDeps leanEnv seeds

/-- Lean's official verdict on the corpus, by replay into a fresh kernel env:
`accept` for each installed constant, `skip` for the unsafe and partial ones
replay omits. Replay throws on the first rejection, naming the constant. -/
def leanVerdicts (_leanEnv : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) :
    IO (Std.HashMap Lean.Name Bool × Except String Unit) := do
  let newConstants : Std.HashMap Lean.Name Lean.ConstantInfo := constants.foldl
    (fun m (n, ci) => m.insert n ci) {}
  let verdicts : Std.HashMap Lean.Name Bool := constants.foldl
    (fun m (n, ci) => m.insert n (!ci.isUnsafe && !ci.isPartial)) {}
  let base := (← Lean.mkEmptyEnvironment).toKernelEnv
  try
    let _ ← Lean.Kernel.Environment.replay newConstants base
    return (verdicts, .ok ())
  catch e =>
    return (verdicts, .error (toString e))

/-- A constant is a leaf IxVM checks with a `check` claim (not a projection
wrapper: those are checked transitively with their block). -/
def isCheckTarget (c : Ixon.Constant) : Bool :=
  match c.info with
  | .iPrj _ | .cPrj _ | .rPrj _ | .dPrj _ => false
  | _ => true

/-- An evenly spaced sample of `xs` of size at most `limit` (0 = all). -/
def sample [Inhabited α] (xs : Array α) (limit seed : Nat) : Array α :=
  if limit == 0 || xs.size ≤ limit then xs
  else
    let step := xs.size / limit
    (Array.range limit).map fun i => xs[(seed + i * step) % xs.size]!

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let prefixes ← corpusPrefixes
  let limit := ((← IO.getEnv "IX_DIFF_LIMIT").bind String.toNat?).getD 0
  let seed := ((← IO.getEnv "IX_DIFF_SEED").bind String.toNat?).getD 0
  let constants := corpusConstants leanEnv prefixes
  IO.println s!"[ixvm-differential] corpus {prefixes}: {constants.length} constants (closed)"
  let started ← IO.monoMsNow
  let (lean, replayed) ← leanVerdicts leanEnv constants
  let leanOk ← match replayed with
    | .ok _ => pure true
    | .error e => do
      IO.eprintln s!"[ixvm-differential] Lean replay rejected a corpus constant: {e}"
      pure false
  let names := constants.map Prod.fst
  let ixon ← loadSharedIxonEnv names.toArray leanEnv
  IO.println s!"[ixvm-differential] compiled and replayed in {(← IO.monoMsNow) - started} ms"
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixon true)
  -- The check targets whose address is known and whose Lean verdict is accept.
  let mut targets : Array (Lean.Name × Address) := #[]
  for n in names do
    match ixon.getAddr? (Ix.Name.fromLeanName n) with
    | none => pure ()
    | some a =>
      match ixon.getConst? a with
      | some c => if isCheckTarget c && lean.getD n false then targets := targets.push (n, a)
      | none => pure ()
  let chosen := sample targets limit seed
  IO.println s!"[ixvm-differential] IxVM checks {chosen.size} of {targets.size} Lean-accepted check targets"
  -- A rejection by IxVM is a divergence: build each as a REQUIRED acceptance,
  -- so the host reports every constant it refuses.
  let builders : Array Builder := chosen.map fun (n, a) => fun _ => do
    return { label := s!"diff {n}", accept := true, witness := ← buildClaimWitness ixon (.check ctx a none) }
  let code ← Tests.Ix.IxVM.runCases "ixvm-differential" (circuit := some true) builders
  if code != 0 then
    IO.eprintln "[ixvm-differential] FINDING: IxVM diverged from Lean on a corpus constant \
      (an IxVM rejection of a Lean-accepted constant); see the FAILED lines above. Its fixture is \
      the compiled Ixon of the named constant's closure."
  IO.println s!"[ixvm-differential] summary: corpus {constants.length}, \
    Lean-accepted check targets {targets.size}, IxVM-checked {chosen.size}, \
    Lean replay {if leanOk then "ok" else "REJECTED"}, IxVM divergences {if code == 0 then 0 else 1}+"
  return if code == 0 && leanOk then 0 else 1

end Tests.Ix.IxVM.Differential
