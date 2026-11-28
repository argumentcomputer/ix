import Ix.Meta
import Ix.CompileCertified
import Ix.IxVM.ClaimHarness
import Tests.Ix.IxVM.Harness
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.TutorialDefs
import Tests.Ix.Kernel.NatReduction

/-!
  Drives the IxVM program through every lean-kernel-arena tutorial fixture
  (`Tests.Ix.Kernel.TutorialDefs` + `NatReduction`): each good fixture must be
  accepted, and each `bad_*` fixture rejected by the program.

  Each fixture is a production `Check` claim on its constant whose assumption
  set is the rest of its closure: the claim checks the subject (and the block
  it belongs to) and assumes its dependencies, as the legacy suite's
  subject-only `verify_const` entry point did, so shared dependencies are not
  revalidated per fixture and a `bad_*` fixture is rejected for itself, not for
  a dependency. A rejection must come from the program's logic: a witness that
  lacks data the program asks for (`missing hint`) is not a verdict.

  Raw-const fixtures (`good_raw_consts` / `bad_raw_consts`, whose decls live in
  `TutorialMeta.rawConstsExt` rather than `env.constants`) are compiled into
  the shared Ixon env via `collectDepsWithExtras`, as the Rust tutorial suite
  does.

  Skips:
  - renaming test cases (collision tests, not single-constant typechecks);
  - constants filtered by the compile (ungrounded blocks);
  - constants in `knownIncompatible` (meta-only Lean kernel checks the IxVM
    kernel structurally cannot see).
-/

open Tests.Ix.Kernel.TutorialMeta
open IxVM.ClaimHarness

namespace Tests.Ix.Kernel.Arena

structure ArenaCheck where
  name : Lean.Name
  expectPass : Bool

/-- Constants the IxVM kernel structurally cannot adjudicate. Skipped rather
than counted as pass/fail. -/
def knownIncompatible : Array (Lean.Name × String) := #[
  -- Duplicate `levelParams` is a meta-mode hygiene check (Lean's
  -- `Level.Param` is name-keyed). Ixon Anon erases the structural
  -- duplication pattern (only `lvls : UInt64` count survives) and the
  -- Ixon compiler resolves `Param u` via first-occurrence, silently
  -- making the second binder dead.
  (`tut06_bad01, "duplicate levelParams: Anon-mode hygiene check"),
  -- AdvNat.rec is a malformed raw recursor payload. Tests.Ix.Kernel.Tutorial
  -- checks it through a dedicated path that injects the bad rule into Ixon.
  (`Tests.Ix.Kernel.TutorialDefs.AdvNat.rec, "malformed rec rule; Tutorial uses bespoke FFI"),
  -- Same reason as tut06_bad01.
  (`inductLevelParam, "duplicate levelParams: Anon-mode hygiene check")
]

/-- Fixtures proved by `native_decide`, which the tutorial expects Lean's kernel
to accept by native evaluation. A claim's theory has none: `Lean.reduceBool`
never reduces, so IxVM rejects them. -/
def nativeEvaluationFixtures : Array Lean.Name := #[
  `natBleTrue, `natBleFalse, `natBeqTrue, `natBeqFalse,
  `Tests.Ix.Kernel.TutorialDefs.natBleTrue, `Tests.Ix.Kernel.TutorialDefs.natBleFalse,
  `Tests.Ix.Kernel.TutorialDefs.natBeqTrue, `Tests.Ix.Kernel.TutorialDefs.natBeqFalse]

/-- Fixtures the modeled route refuses because the kernel's modeller has no
model for them (decision D7). `nestedSpecLocalF`'s nested occurrence takes a
constructor field as its parametric argument, so no auxiliary type can be formed:
IxCK declines it (`Tests.Ix.Kernel.Tutorial.cornerCases`), and IxVM, which checks a
nested block against a model, finds none ("no model advice"). Lean's elaborator
rejects the declaration; the arena's outcome for its nearest test is `either`. -/
def modeledDeclines : Array Lean.Name :=
  #[`nestedSpecLocalF, `nestedSpecLocalF.mk, `nestedSpecLocalF.rec]

/-- Fixtures the native route declines because a constructor field domain
mentions the block in a non-syntactic occurrence (`id (reduceCtorParam A)`
and its reflexive variants), which would require rewriting the stored
constructor's field domains to classify positivity. -/
def nativeDeclines : Array Lean.Name := #[
  `reduceCtorParam, `reduceCtorParam.mk, `reduceCtorParam.rec,
  `reduceCtorParamRefl, `reduceCtorParamRefl.mk, `reduceCtorParamRefl.rec,
  `reduceCtorParamRefl2, `reduceCtorParamRefl2.mk, `reduceCtorParamRefl2.rec]

private def collectChecks (env : Lean.Environment) : Array ArenaCheck := Id.run do
  let skipSet : Std.HashSet Lean.Name :=
    knownIncompatible.foldl (init := {}) (fun s (n, _) => s.insert n)
  let rawNames : Std.HashSet Lean.Name :=
    (getRawConsts env).foldl (fun s ci => s.insert ci.name) {}
  let mut out : Array ArenaCheck := #[]
  let mut seen : Std.HashSet Lean.Name := {}
  for tc in getTestCases env do
    if tc.renamings.size > 0 then continue
    let pass := tc.outcome == .good
    for n in tc.decls do
      if seen.contains n then continue
      seen := seen.insert n
      if !env.constants.contains n && !rawNames.contains n then continue
      if skipSet.contains n then continue
      let expectPass := pass && !nativeEvaluationFixtures.contains n &&
        !modeledDeclines.contains n && !nativeDeclines.contains n
      out := out.push { name := n, expectPass := expectPass }
  return out

/-- The block a projection names. -/
private def blockOf : Ixon.ConstantInfo → Option Address
  | .iPrj p => some p.block
  | .cPrj p => some p.block
  | .rPrj p => some p.block
  | .dPrj p => some p.block
  | _ => none

/-- Precompute the constant closure graph and projection-to-block map once for
the shared arena environment so `subjectClaim` never re-deserializes constants
per fixture. -/
private def buildArenaGraph (env : Ixon.Env) : EnvGraph × Std.HashMap Address Address := Id.run do
  let mut closureRefs : Std.HashMap Address (Array Address) :=
    Std.HashMap.emptyWithCapacity env.consts.size
  let mut blockMap : Std.HashMap Address Address := {}
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      let edges := closureEdgesOf a c
      unless edges.isEmpty do
        closureRefs := closureRefs.insert a edges
      if let some b := blockOf c.info then
        blockMap := blockMap.insert a b
  return ({ closureRefs }, blockMap)

/-- The subject-only claim on `target`: its closure is assumed, except the
target, the block it projects from, and that block's other projections. -/
private def subjectClaim (env : Ixon.Env) (graph : EnvGraph)
    (blockMap : Std.HashMap Address Address) (ctx : Ix.ClaimContext) (target : Address) :
    Except String (Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  unless env.consts.contains target do throw s!"{target} is not in the environment"
  let block := blockMap[target]?
  let isSubject (a : Address) : Bool :=
    a == target || some a == block ||
      (block.isSome && blockMap[a]? == block)
  let deps := (closureFromRootsWithGraph env graph #[target]).toArray.filter fun a =>
    env.consts.contains a && !isSubject a
  match Ix.AssumptionTree.canonical deps with
  | none => return (.check ctx target none, {})
  | some tree => return (.check ctx target (some tree.root), ({} : Std.HashMap _ _).insert tree.root tree)

/-- Every fixture as a claim over one shared Ixon env. A fixture the compile
filtered (no Ixon address) is reported and skipped. -/
def arenaCases (env : Lean.Environment) (includeAllBad : Bool := true) :
    IO (Array Tests.Ix.IxVM.Builder) := do
  let checks := collectChecks env
  let rawConsts := getRawConsts env
  let rawMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
    rawConsts.foldl (fun m ci => m.insert ci.name ci)
      (Std.HashMap.emptyWithCapacity rawConsts.size)
  let (_, closed) := collectDepsWithExtras env rawMap
    ((checks.map (·.name)).toList ++ (rawConsts.toList.map (·.name)))
  let allConsts := closed ++ rawConsts.toList.map fun ci => (ci.name, ci)
  -- with the compile's binder-data annotator, so that each record carries its data
  let input ← IxVM.ClaimHarness.withKernelAnnotator (Ix.CompileM.canonInput allConsts.toArray 32)
  let (rawEnv, _, _) ← IO.ofExcept <| Ix.Cert.compileUnchecked input
  let ixonEnv ← IO.ofExcept (withDefaultRoleBinding rawEnv)
  let (graph, blockMap) := buildArenaGraph ixonEnv
  -- The fixtures' own axioms are assumed like any other dependency, so the
  -- claims carry no user axioms; and the claims assume their role binding
  -- (validator 4), as an aggregate's claims do, which keeps the witnesses to
  -- the fixtures' closures and the bound roles.
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixonEnv (bindingAssumed := true))
  let ctx := { ctx with axioms := none }
  let mut out : Array Tests.Ix.IxVM.Builder := #[]
  let mut badSmokes : Nat := 0
  for c in checks do
    let isNative := nativeEvaluationFixtures.contains c.name
    if !includeAllBad && !c.expectPass && !isNative then
      if badSmokes ≥ 3 then continue
      badSmokes := badSmokes + 1
    let label := s!"arena {if c.expectPass then "GOOD" else "BAD"} {c.name}"
    match ixonEnv.getAddr? (Ix.Name.fromLeanName c.name) with
    | none => IO.println s!"{label}: skipped (ungrounded by the compile)"
    | some addr =>
      -- A `native_decide` proof cites an auxiliary axiom asserting the native
      -- result: assumed, it makes the claim a vacuous conditional one, so the
      -- claim checks the closure and the axiom policy must refuse it.
      if isNative then
        out := out.push fun _ =>
          Tests.Ix.IxVM.Case.ofClaim s!"{label}, its closure checked" ixonEnv (.check ctx addr none)
            {} false (some "an axiom that is not one of Lean's standard axioms")
      else
        out := out.push fun _ => do
          let (claim, trees) ← subjectClaim ixonEnv graph blockMap ctx addr
          Tests.Ix.IxVM.Case.ofClaim label ixonEnv claim trees c.expectPass
  return out

/-- PR fast suite: all `good_*` completeness fixtures, `native_decide` checks,
and 3 representative `bad_*` host smokes (`bad_*` soundness is proved by
`CircuitComposed` and exercised in IxCK by `kernel-tutorial`). -/
def run (env : Lean.Environment) : IO UInt32 := do
  Tests.Ix.IxVM.runCases "ixvm-arena" (← arenaCases env (includeAllBad := false))

/-- Full nightly suite: every `good_*` and `bad_*` arena fixture through IxVM. -/
def runFull (env : Lean.Environment) : IO UInt32 := do
  Tests.Ix.IxVM.runCases "ixvm-arena-full" (← arenaCases env (includeAllBad := true))

end Tests.Ix.Kernel.Arena
