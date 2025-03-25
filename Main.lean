import Ix.Cli.ProveCmd
import Ix.Cli.HashCmd
import Ix.Cli.TestCmd
import Ix.Cli.StoreCmd
import Ix

def VERSION : String :=
  s!"{Lean.versionString}|0.0.1"

def ixCmd : Cli.Cmd := `[Cli|
  ix NOOP; [VERSION]
  "A tool for generating content-addressed ZK proofs of Lean 4 code"

  SUBCOMMANDS:
    proveCmd;
    hashCmd;
    testCmd;
    storeCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    ixCmd.printHelp
    return 0
  ixCmd.validate args
