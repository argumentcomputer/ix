/-
  Shared name-resolution helpers for the `ix` CLI commands.

  Turning a user-supplied dotted name (`Nat.add_comm`, `_private.M.0.foo`)
  into either a `Lean.Name` or a content `Address` is needed by several
  commands (`addr-of`, `check`, …) and by benchmark drivers. These helpers
  live here — depending only on `Address`/`Environment`/`Ixon` — so callers
  don't have to pull in the Aiur typecheck machinery just to resolve a name.
-/
module
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon

public section

namespace Ix.Cli.NameResolve

/-- Parse a dotted CLI argument into a `Lean.Name`, treating all-digit
    components as numeric (`Nat`) name parts and everything else as string
    parts. Naive: components that don't round-trip through `.`-splitting
    (private markers, macro scopes) won't reconstruct — see `resolveName`
    / `resolveIxeAddr` for the `toString` fallback that covers those. -/
def parseName (arg : String) : Lean.Name :=
  arg.splitOn "." |>.foldl (init := .anonymous)
    fun acc s => match s.toNat? with
      | some n => Lean.Name.mkNum acc n
      | none   => Lean.Name.mkStr acc s

/-- Resolve a CLI name argument against the env. `parseName` can't rebuild
    private names (`_private.M.0.foo`) — the marker/scope-index components
    don't round-trip through naive dot-splitting. So if the parsed name
    isn't present, fall back to matching the arg against each constant's
    `toString` (the displayed form the user copied). -/
def resolveName (env : Lean.Environment) (arg : String) : Option Lean.Name :=
  let parsed := parseName arg
  if env.constants.contains parsed then some parsed
  else (env.constants.toList.find? (fun (k, _) => toString k == arg)).map (·.1)

/-- Reverse of `Ix.Name.fromLeanName`. Drops the per-node hash. -/
partial def ixNameToLeanName : Ix.Name → Lean.Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixNameToLeanName p) s
  | .num p n _ => .num (ixNameToLeanName p) n

/-- Resolve a CLI name argument against a `.ixe` env's named map. Like
    `resolveName` for the compiled-in env: `parseName` can't rebuild private
    names, so when the direct lookup misses, fall back to matching the arg
    against each named constant's displayed `toString`. -/
def resolveIxeAddr (ixonEnv : Ixon.Env) (arg : String) : Option Address :=
  match ixonEnv.getAddr? (Ix.Name.fromLeanName (parseName arg)) with
  | some a => some a
  | none =>
    (ixonEnv.named.toList.find? (fun (k, _) => toString (ixNameToLeanName k) == arg)).map (·.2.addr)

end Ix.Cli.NameResolve

end
