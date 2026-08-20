/-
  The shared benchmark constant set: the single source of truth for which
  constants every per-constant benchmark backend (aiur, zisk, sp1, ooc,
  lean4lean) runs. Every backend runs this same set — spanning the cheap →
  heavy cost range across the registry envs — so their numbers stay
  comparable per constant; the only per-backend carve-outs are the hard
  feasibility exclusions in `Ix.Cli.BenchCmd.benchExclusions`.

  `env` names the registry env (`Ix.Cli.BenchCmd.envSpecs` /
  `<env>.ixe`) the constant resolves in. Whether a zisk execution runs
  whole or as a closure-shard partition is decided at bench runtime by
  the shard planner's budget, not declared here.
-/
module

public section

namespace Ix.BenchConstants

/-- One benchmark constant: a fully-qualified Lean name and the registry
    env it resolves in. -/
structure BenchConstant where
  name : String
  env : String

def benchConstants : Array BenchConstant := #[
  { name := "Nat.add_comm",                      env := "InitStd" },
  { name := "String.append",                     env := "InitStd" },
  { name := "Array.extract_append",              env := "InitStd" },
  { name := "ByteArray.utf8DecodeChar?_utf8EncodeChar_append",
    env := "InitStd" },
  { name := "_private.Init.Data.Range.Polymorphic.SInt.0.Int64.instRxcHasSize_eq",
    env := "InitStd" },
  { name := "Char.ofOrdinal_le_of_le",           env := "InitStd" },
  { name := "Std.HashMap",                       env := "InitStd" },
  -- TODO: re-add bitblast once a prover can carry it. Its ~18B-step
  -- atomic mutual block crashes the zkVM executors (`benchExclusions`)
  -- and exceeds any current host's RAM on the Aiur prove, so a scheduled
  -- run could only re-document the same OOM every push. Until then it
  -- runs on demand via `--consts` / BENCH_CONSTS, which bypass the
  -- curated set.
  -- { name := "Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual",
  --   env := "InitStd" },
  { name := "Lean.Json",                         env := "Lean" },
  { name := "Multiset.sort",                     env := "Mathlib" }
]

end Ix.BenchConstants
