--import Ix.Cli.StoreCmd
import Ix.Cli.AddrOfCmd
import Ix.Cli.BenchReport
import Ix.Cli.CheckCmd
import Ix.Cli.CodegenCmd
import Ix.Cli.CheckRsCmd
import Ix.Cli.ClaimCmd
import Ix.Cli.CompileCmd
import Ix.Cli.CompressCmd
import Ix.Cli.DecompileCmd
import Ix.Cli.DiffCmd
import Ix.Cli.IngressCmd
import Ix.Cli.PackCmd
import Ix.Cli.ProfileCmd
import Ix.Cli.ProveCmd
import Ix.Cli.ShardCmd
import Ix.Cli.TreeCmd
import Ix.Cli.ValidateCmd
import Ix.Cli.VerifyCmd
import Ix.Cli.ServeCmd
import Ix.Cli.ConnectCmd
import Ix

def VERSION : String :=
  s!"{Lean.versionString}|0.0.1"

def ixCmd : Cli.Cmd := `[Cli|
  ix NOOP; [VERSION]
  "A tool for generating content-addressed ZK proofs of Lean 4 code"

  SUBCOMMANDS:
    --storeCmd;
    benchCmd;
    compileCmd;
    decompileCmd;
    checkCmd;
    checkRsCmd;
    claimCmd;
    diffCmd;
    packCmd;
    treeCmd;
    profileCmd;
    proveCmd;
    compressCmd;
    shardCmd;
    codegenCmd;
    verifyCmd;
    addrOfCmd;
    ingressCmd;
    validateCmd;
    serveCmd;
    connectCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    ixCmd.printHelp
    return 0
  ixCmd.validate args
