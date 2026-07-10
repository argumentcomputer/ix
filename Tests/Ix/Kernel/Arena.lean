/-
  Drives the Aiur kernel through every lean-kernel-arena tutorial
  fixture (`Tests.Ix.Kernel.TutorialDefs` + `NatReduction`) using the
  shared `IxVM.ixVM` toplevel + `verify_const` entrypoint.

  Each fixture's outcome is classified against the test case's expected
  outcome (good must typecheck; bad must be rejected via Aiur execution
  error, where the error originates from an `assert_eq!` failure inside
  the Aiur kernel source).

  `verify_const` is a DEBUG entrypoint, not a claim — it
  type-checks only the target and trusts transitive deps. Arena uses
  it for the per-fixture speed advantage (shared deps would otherwise
  be revalidated N times). Verifier policy must never accept this
  funcidx as a production claim.

  Raw-const fixtures (`good_raw_consts` / `bad_raw_consts`, whose decls
  live in `TutorialMeta.rawConstsExt` rather than `env.constants`) are
  compiled into the shared Ixon env via `collectDepsWithExtras`, same
  as the Rust tutorial suite.

  Skips:
  - renaming test cases (collision tests, not single-constant
    typechecks);
  - constants filtered by `compile_env` (ungrounded blocks);
  - constants in `knownIncompatible` (meta-only Lean kernel checks the
    Aiur kernel structurally cannot see).
-/
import Ix.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.IxVM
import Ix.IxVM.ClaimHarness
import Tests.Aiur.Common
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.TutorialDefs
import Tests.Ix.Kernel.NatReduction
import LSpec

open LSpec
open Tests.Ix.Kernel.TutorialMeta
open IxVM.ClaimHarness

namespace Tests.Ix.Kernel.Arena

structure ArenaCheck where
  name : Lean.Name
  expectPass : Bool

/-- Constants the Aiur kernel structurally cannot adjudicate. Skipped
    rather than counted as pass/fail. -/
def knownIncompatible : Array (Lean.Name × String) := #[
  -- Duplicate `levelParams` is a meta-mode hygiene check (Lean's
  -- `Level.Param` is name-keyed). Ixon Anon erases the structural
  -- duplication pattern (only `lvls : UInt64` count survives) and the
  -- Ixon compiler resolves `Param u` via first-occurrence, silently
  -- making the second binder dead. Rejection happens only in the Rust
  -- kernel via `has_duplicate_level_params` (Meta-mode only).
  (`tut06_bad01,
   "duplicate levelParams: Anon-mode hygiene check, see src/ix/kernel/check.rs:107"),
  -- AdvNat.rec is a malformed raw recursor payload that aux-gen would
  -- sanitize before it reaches Ixon. Tests.Ix.Kernel.Tutorial uses a
  -- dedicated FFI (`rs_kernel_check_malformed_rec_rule_ixon`) to inject
  -- the bad rule post-aux-gen. Standard Lean→Ixon→Aiur path never
  -- exposes the malformed rule.
  (`Tests.Ix.Kernel.TutorialDefs.AdvNat.rec,
   "malformed rec rule sanitized by aux-gen; Tutorial uses bespoke FFI"),
  -- Same reason as tut06_bad01: duplicate levelParams is Meta-mode
  -- hygiene; Ixon Anon stores only the `lvls` COUNT, so the duplication
  -- pattern is erased before the Aiur kernel can see it.
  (`inductLevelParam,
   "duplicate levelParams: Anon-mode hygiene check, see src/ix/kernel/check.rs:107")
]

private def collectChecks (env : Lean.Environment) : Array ArenaCheck := Id.run do
  let skipSet : Std.HashSet Lean.Name :=
    knownIncompatible.foldl (init := {}) (fun s (n, _) => s.insert n)
  -- Raw consts (`good_raw_consts` / `bad_raw_consts`) never enter
  -- `env.constants` (the Lean kernel refused them); they are compiled
  -- into the shared Ixon env via `collectDepsWithExtras` below. Consts
  -- `compile_env` refuses to ground surface as skips in `buildInput`.
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
      out := out.push { name := n, expectPass := pass }
  return out

/-- Build the `verify_const` input for `name` against the shared
    `ixonEnv`. Returns `error` when `compile_env` filtered the
    constant (no Ixon address) — caller treats that as a skip. -/
private def buildInput (ixonEnv : Ixon.Env) (name : Lean.Name) :
    Except String (Array Aiur.G × Aiur.IOBuffer) :=
  match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
  | none => .error "ungrounded by compile_env"
  | some addr =>
    -- Subject-only check via `verify_const`. Each fixture runs in
    -- isolation; we don't revalidate transitive deps N times.
    let witness := buildVerifyConst ixonEnv addr
    .ok (witness.input, witness.inputIOBuffer)

/-- Run the arena suite against `compiled` (already-compiled Aiur
    `IxVM.ixVM` toplevel) using a single shared Ixon env. Returns one
    `TestSeq` entry per fixture. -/
def arenaTests (env : Lean.Environment)
    (compiled : Aiur.CompiledToplevel) : IO TestSeq := do
  let funIdx ← match compiled.getFuncIdx `verify_const with
    | some i => pure i
    | none => throw <| IO.userError "verify_const entrypoint missing"
  let checks := collectChecks env
  -- Raw fixtures don't live in `env.constants`; close over the check
  -- names with the raw consts as extra lookups, then append the raw
  -- consts themselves so `compile_env` grounds them (mirrors the Rust
  -- tutorial suite's env build).
  let rawConsts := getRawConsts env
  let rawMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
    rawConsts.foldl (fun m ci => m.insert ci.name ci)
      (Std.HashMap.emptyWithCapacity rawConsts.size)
  let (_, closed) := collectDepsWithExtras env rawMap
    (checks.map (·.name)).toList
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI
    (closed ++ rawConsts.toList.map fun ci => (ci.name, ci))
  let ixonEnv := rawEnv.toEnv
  let mut tests : TestSeq := .done
  for c in checks do
    let label := s!"arena {if c.expectPass then "GOOD" else "BAD"} {c.name}"
    match buildInput ixonEnv c.name with
    | .error reason => tests := tests ++ test s!"{label}: skipped ({reason})" true
    | .ok (input, ioBuffer) =>
      match compiled.bytecode.execute funIdx input ioBuffer with
      | .ok _ =>
        tests := tests ++
          test label (c.expectPass)
      | .error e =>
        tests := tests ++
          test s!"{label} ({e})" (!c.expectPass)
  return tests

end Tests.Ix.Kernel.Arena
