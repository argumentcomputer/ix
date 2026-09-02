/-
  `ix shard refine <path.ixe> --ixes M.ixes --out M2.ixes [--shards SEL]
  [--max-ram G] [--jobs N] [--report R.json] [--no-index]`: the local
  refinement of an existing partition. Every selected leaf (default: all) is
  executed and its analytic prover peak measured; a leaf over the budget is
  cut into the part count the peak model projects will fit and the parts
  re-executed, wave by wave, until everything fits or is a single block. The
  result is written as a refinement of the source manifest: untouched leaves
  keep their records, ids and tree positions, and each split leaf becomes a
  balanced subtree over its parts (part 0 keeps the leaf's id, later parts
  take fresh ids after the last existing one). A leaf whose claim already
  has a verified proof in the shard-proof index is never split, whatever its
  peak: refinement must never orphan a proof. Failures leave their leaf
  unchanged, are listed in the report, and make the exit code 2.
-/
module
public import Cli
public import Ix.Common
public import Ix.Aiur.Protocol
public import Ix.Cli.CheckCmd
public import Ix.Cli.ShardProofIndex
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness

public section

namespace Ix.Cli.RefineCmd

/-- The budget the refinement gates on: `--max-ram G` (GiB), or the machine's
    detected 85 % of `MemAvailable` when omitted or `0`. `none` when nothing
    can be detected — the caller fails closed. -/
def resolveBudget (maxRam? : Option Nat) : IO (Option (Nat × String)) := do
  match maxRam? with
  | some g => if g > 0 then return some (g * gibBytes, "flag") else detect
  | none => detect
where
  detect : IO (Option (Nat × String)) := do
    let b ← Aiur.detectedRamBudgetBytes
    if b == 0 then return none
    IO.println s!"[refine] budget {toGib b} GiB (detected: 85% of MemAvailable)"
    pure (some (b, "detected"))

def runShardRefineCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"; return 1
  let ixePath := pathArg.as! String
  let some manifest := (p.flag? "ixes").map (·.as! String)
    | p.printError "error: --ixes <manifest.ixes> is required"; return 1
  let some out := (p.flag? "out").map (·.as! String)
    | p.printError "error: --out <refined.ixes> is required"; return 1
  let selection? ← match (p.flag? "shards").map (·.as! String) with
    | none => pure none
    | some s => match Ix.Cli.CheckCmd.parseShardSelection s with
      | .error e => p.printError s!"error: {e}"; return 1
      | .ok ids => pure (some ids)
  let some (maxRamBytes, budgetSource) ← resolveBudget ((p.flag? "max-ram").map (·.as! Nat))
    | p.printError "error: cannot detect MemAvailable (/proc/meminfo unreadable); pass --max-ram G"
      return 1
  let jobs? := (p.flag? "jobs").map (·.as! Nat)
  let report? := (p.flag? "report").map (·.as! String)
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"compilation failed: {e}"; return 1
    | .ok c => pure c
  -- The proven-leaf guard: a selected leaf whose claim already has a
  -- verified proof in the index is kept exactly as it is.
  let guard? ← if p.hasFlag "no-index" then pure none else do
    let aiurSystem := Aiur.AiurSystem.build compiled.bytecode
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
    let dir ← Ix.Cli.ShardProofIndex.indexDir
    pure (some fun (ixonEnv : Ixon.Env) (_ : Array (Array Address))
        (ownedAll : Array (Array Address)) (selected : Array Nat) => do
      let mut kept : Std.HashMap Nat Address := {}
      for k in selected do
        let some owned := ownedAll[k]? | continue
        match IxVM.ClaimHarness.shardCheckEnvClaimTrees ixonEnv owned with
        | .error _ => continue
        | .ok (claim, _) =>
          if let some addr ← Ix.Cli.ShardProofIndex.verifiedProof aiurSystem compiled dir claim then
            IO.println s!"[refine] shard {k}: verified proof {addr} in the index — kept"
            kept := kept.insert k addr
      pure kept)
  let command := String.intercalate " " (#["ix shard refine", ixePath, "--ixes", manifest, "--out", out]
    ++ (match (p.flag? "shards").map (·.as! String) with | some s => #["--shards", s] | none => #[])
    ++ (match (p.flag? "max-ram").map (·.as! Nat) with | some g => #["--max-ram", toString g] | none => #[])
    ++ (match jobs? with | some j => #["--jobs", toString j] | none => #[])
    ++ (match report? with | some r => #["--report", r] | none => #[])
    ++ (if p.hasFlag "no-index" then #["--no-index"] else #[])).toList
  Ix.Cli.CheckCmd.runShardBatchNative manifest ixePath jobs? compiled false none none
    maxRamBytes (some out)
    { selection := selection?, provenGuard := guard?, report := report?,
      emitOnFailure := true, command, budgetSource }

end Ix.Cli.RefineCmd

open Ix.Cli.RefineCmd in
def shardRefineCmd : Cli.Cmd := `[Cli|
  "refine" VIA runShardRefineCmd;
  "Refine an existing `.ixes` partition against a prover-RAM budget: execute the selected leaves, cut every over-budget one into parts the peak model says will fit (recursively), and write the result as a refinement of the source manifest — untouched leaves keep their records, ids and aggregation-tree positions; a leaf that already has a verified proof in the shard-proof index is never split"

  FLAGS:
    ixes       : String; "The source `.ixes` manifest (required)."
    out        : String; "Where to write the refined `.ixes` manifest (required). Written even when some leaves failed (they stay unchanged; exit 2)."
    shards     : String; "Leaves to audit: `K`, `a-b`, or a comma list of those. Default: every leaf. Unselected leaves are carried over unchanged."
    "max-ram"  : Nat;    "Per-shard prover-RAM budget, GiB, in `ix prove --max-ram` units. Omitted or 0: detect 85% of this machine's MemAvailable (an error if that cannot be read)."
    jobs       : Nat;    "Rayon threads for the execution batch (default: all cores; admission is bounded by the RAM gate, not by thread count)."
    report     : String; "Write the provisional JSON audit report (`ix-refine/0`: per-leaf status, predicted peaks, claim digests, split parts with their new ids, failures) to this path."
    "no-index";          "Do not consult `~/.ix/cache/shard-proofs`: split over-budget leaves even when a verified proof of their claim exists (testing only)."

  ARGS:
    path : String; "Path to the serialized `.ixe` environment the manifest partitions."
]
