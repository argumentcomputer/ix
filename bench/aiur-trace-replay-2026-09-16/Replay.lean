import Ix.Cli.AggregateCmd

def main (args : List String) : IO UInt32 :=
  aggregateCmd.validate args
