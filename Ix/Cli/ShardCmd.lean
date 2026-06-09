/-
  `ix shard <path.ixesp> --shards N`: partition a profiled environment into `N`
  shards via recursive balanced min-cut bisection, minimizing cross-shard
  delta-unfold ingress (see `plans/sharding.md`).

  Reads the `.ixesp` produced by `ix profile` (pure offline graph work, so `N`
  is cheap to re-tune without re-running the kernel). Writes a `.ixes` manifest
  and prints a what-if report (per-shard heartbeat balance + total cross-shard
  ingress). The partitioner is self-contained — no external graph-library
  dependency.
-/
module
public import Cli
public import Ix.KernelCheck

public section

open Ix.KernelCheck

namespace Ix.Cli.ShardCmd

def runShardCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixesp file"
      return 1
  let espPath := pathArg.as! String
  let numShards : Nat :=
    match p.flag? "shards" with
    | some flag => flag.as! Nat
    | none      => 1
  let balancePct : Nat :=
    match p.flag? "balance" with
    | some flag => flag.as! Nat
    | none      => 5
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    | none      => espPath ++ ".ixes"

  IO.println s!"Sharding {espPath} into {numShards} shards (balance ±{balancePct}%)"
  rsShardEspFFI espPath (toString numShards) (toString balancePct) outPath
  if !outPath.isEmpty then
    IO.println s!"[shard] wrote {outPath}"
  return 0

end Ix.Cli.ShardCmd

open Ix.Cli.ShardCmd in
def shardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runShardCmd;
  "Partition a `.ixesp` into N balanced shards minimizing cross-shard delta"

  FLAGS:
    shards  : Nat;    "Number of shards N (default 1 = a single shard)"
    balance : Nat;    "Per-bisection balance tolerance, percent (default 5)"
    out     : String; "Output .ixes manifest path (default: <path>.ixes)"

  ARGS:
    path : String; "Path to a .ixesp produced by `ix profile`"
]

end
