import Ix.Cli.AddrOfCmd
import Ix.FormalCompiler
import Ix.Cli.AggregateCmd
import Ix.Cli.BenchReport
import Ix.Cli.CheckCmd
import Ix.Cli.CodegenCmd
import Ix.Cli.CheckLeanCmd
import Ix.Cli.CompileLeanCmd
import Ix.Cli.CompileExportCmd
import Ix.Cli.ValidateLeanCmd
import Ix.Cli.ClaimCmd
import Ix.Cli.CatalogCmd
import Ix.Cli.CompileCmd
import Ix.Cli.DecompileCmd
import Ix.Cli.DiffCmd
import Ix.Cli.MergeCmd
import Ix.Cli.NameOfCmd
import Ix.Cli.PackCmd
import Ix.Cli.CompressCmd
import Ix.Cli.ProveCmd
import Ix.Cli.ProveBindingCmd
import Ix.Cli.ShardCmd
import Ix.Cli.TreeCmd
import Ix.Cli.VerifyCmd
import Ix.Cli.VerifyHostCmd
import Ix.Cli.ServeCmd
import Ix.Cli.ConnectCmd
import Ix

/-! CLI entry point for the `ix` executable. -/

def VERSION : String := Ix.versionString

def ixCmd : Cli.Cmd := `[Cli|
  ix NOOP; [VERSION]
  "A tool for generating content-addressed ZK proofs of Lean 4 code"

  SUBCOMMANDS:
    benchCmd;
    aggregateCmd;
    catalogCmd;
    compileCmd;
    decompileCmd;
    mergeCmd;
    checkCmd;
    checkLeanCmd;
    compileLeanCmd;
    compileExportCmd;
    validateLeanCmd;
    claimCmd;
    diffCmd;
    packCmd;
    treeCmd;
    proveCmd;
    proveBindingCmd;
    compressCmd;
    shardCmd;
    codegenCmd;
    verifyCmd;
    verifyHostCmd;
    addrOfCmd;
    nameOfCmd;
    serveCmd;
    connectCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    ixCmd.printHelp
    return 0
  ixCmd.validate args
