import Ix.Compiler.Tools.TrustLedger

open Ix.Compiler.Tools.Check Ix.Compiler.Tools.TrustLedger

def main (args : List String) : IO UInt32 := cli "trusted-extern ledger check failed" do
  let args ← checked (parseArgs ["--root", "--dependency-root"]
    args ["--dependency-root"])
  let mut overrides := []
  for (_, value) in args.filter (·.1 == "--dependency-root") do
    let parts := value.splitOn "="
    let name := parts.headD ""
    let path := "=".intercalate (parts.drop 1)
    need (!name.isEmpty && !path.isEmpty) s!"bad --dependency-root {value}; use NAME=PATH"
    need (!(optional overrides name).isSome) s!"duplicate dependency root for {name}"
    overrides := (name, path) :: overrides
  audit (option args "--root" ".") overrides
