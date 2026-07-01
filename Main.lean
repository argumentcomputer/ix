--import Ix.Cli.StoreCmd
import Ix.Cli.AddrOfCmd
import Ix.Cli.NameOfCmd
import Ix.Cli.CheckCmd
import Ix.Cli.CodegenCmd
import Ix.Cli.CheckRsCmd
import Ix.Cli.ClaimCmd
import Ix.Cli.CompileCmd
import Ix.Cli.IngressCmd
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
    compileCmd;
    checkCmd;
    checkRsCmd;
    claimCmd;
    treeCmd;
    profileCmd;
    proveCmd;
    shardCmd;
    codegenCmd;
    verifyCmd;
    addrOfCmd;
    nameOfCmd;
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
