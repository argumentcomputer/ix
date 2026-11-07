import IxCC.Tools.TrustLedger

open IxCC.Tools.Check IxCC.Tools.TrustLedger

/-- `check-trusted-externs [--root DIR] [--dependency-root NAME=PATH]…
[--gmp-version V] [--repository-root DIR] [--flake-lock FILE]`: the last two
replace the ledger's repository root (`policy.repository.root`, default the
project) and the `flake.lock` in it. -/
def main (args : List String) : IO UInt32 := cli "trusted-extern ledger check failed" do
  let args ← checked (parseArgs ["--root", "--dependency-root", "--gmp-version",
    "--repository-root", "--flake-lock"] args ["--dependency-root"])
  let mut overrides := []
  for (_, value) in args.filter (·.1 == "--dependency-root") do
    let parts := value.splitOn "="
    let name := parts.headD ""
    let path := "=".intercalate (parts.drop 1)
    need (!name.isEmpty && !path.isEmpty) s!"bad --dependency-root {value}; use NAME=PATH"
    need (!(optional overrides name).isSome) s!"duplicate dependency root for {name}"
    overrides := (name, path) :: overrides
  audit (option args "--root" ".") overrides (optional args "--gmp-version")
    ((optional args "--repository-root").map System.FilePath.mk)
    ((optional args "--flake-lock").map System.FilePath.mk)
