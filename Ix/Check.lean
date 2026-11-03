module
public import Ix.Address
public import Ix.Aiur.Protocol
public import Ix.AssumptionTree
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Meta
public import Ix.Store
public import Ix.Cli.NameResolve

/-! IxVM claim target selection and witness preparation shared by check and prove. -/

public section

open IxVM.ClaimHarness
open Ix.Cli.NameResolve

namespace Ix.Check

def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Load a persisted claim from the content-addressed store and resolve
    every tree root it references. Shared between `ix check --claim`
    and `ix prove --claim`. -/
def loadClaimAndTrees (claimHex : String) :
    IO (Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  let claimAddr ← addrOfHex! "claim" claimHex
  let claimBytes ← StoreIO.toIO (Store.read claimAddr)
  let claim ← IO.ofExcept (Ix.Claim.de claimBytes)
  let computed := Address.blake3 (Ix.Claim.ser claim)
  if computed != claimAddr then
    throw <| IO.userError
      s!"error: claim bytes at {claimAddr} re-hash to {computed}"
  let treeRoots : Array Address := match claim with
    | .check _ _ (some r)      => #[r]
    | .eval _ _ _ (some r)     => #[r]
    | .checkEnv _ root none    => #[root]
    | .checkEnv _ root (some r) => #[root, r]
    | .contains tree _         => #[tree]
    | _                        => #[]
  let mut trees : Std.HashMap Address Ix.AssumptionTree := {}
  for r in treeRoots do
    let tbytes ← StoreIO.toIO (Store.read r)
    let tree ← match Ix.AssumptionTree.de tbytes with
      | .error e => throw <| IO.userError s!"error: tree at {r}: deserialize failed: {e}"
      | .ok t => pure t
    if tree.root != r then
      throw <| IO.userError s!"error: tree stored at {r} has merkle root {tree.root}"
    trees := trees.insert r tree
  return (claim, trees)

/-- The `Check` claim on `addr` (full transitive typecheck of the target's
    closure), relative to `ixonEnv`'s role binding. -/
def checkClaimOf (ixonEnv : Ixon.Env) (addr : Address)
    (assumeBinding : Bool := false) : IO Ix.Claim := do
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv ixonEnv assumeBinding)
  return Ix.Claim.check ctx addr none

/-- Build a `ClaimWitness` for the `verify_claim` entrypoint against
    `checkClaimOf ixonEnv addr`. -/
def mkWitness (addr : Address) (ixonEnv : Ixon.Env)
    (assumeBinding : Bool := false) :
    IO IxVM.ClaimHarness.ClaimWitness := do
  let claim ← checkClaimOf ixonEnv addr assumeBinding
  IO.ofExcept <|
    IxVM.ClaimHarness.buildClaimWitness ixonEnv claim {}

/-- Load an `.ixe` for IxVM claims: its environment, given the default role
    binding when the file carries none (`withDefaultRoleBinding`), and a
    Rust handle over that same environment. -/
def loadBoundIxe (path : String) : IO (Ixon.Env × Aiur.EnvHandle) := do
  let bytes ← IO.FS.readBinFile path
  let env ← match Ixon.deEnvAnon bytes with
    | .error e => throw <| IO.userError s!"Failed to deserialize {path}: {e}"
    | .ok env => pure env
  if env.roleBinding.isSome then
    match Aiur.EnvHandle.fromIxe path with
    | .error e => throw <| IO.userError s!"EnvHandle.fromIxe {path}: {e}"
    | .ok h => return (env, h)
  let env ← IO.ofExcept (withDefaultRoleBinding env)
  let envBytes ← match Ixon.serEnv env with
    | .error e => throw <| IO.userError s!"serEnv {path}: {e}"
    | .ok b => pure b
  match Aiur.EnvHandle.fromBytes envBytes with
  | .error e => throw <| IO.userError s!"EnvHandle.fromBytes {path}: {e}"
  | .ok h => return (env, h)

/-- What a single `runOne` invocation is targeting. -/
inductive Target where
  | addr  (a : Address)
  | shard (owned : Array Address)
  | leanW (w : IxVM.ClaimHarness.ClaimWitness)

/-- The environment a claim about `name` is checked against when no `.ixe` is
    given: the closure of `name`, with the constants the kernel fabricates
    during reduction and the roles' constants, compiled by the certified Lean
    compiler (`Ix.CompileM.compileCertified`) and bound to the default role
    table. -/
def loadNamedIxonEnv (name : Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env :=
  IxVM.ClaimHarness.loadIxonEnv name leanEnv

/-- Shared driver for `ix check` / `ix prove`. -/
def forEachClaim
    (ixePath : Option String) (claimHex : Option String) (names : List String)
    (keepGoing : Bool) (logTag : String) (forceLeanWitness : Bool)
    (runOne : Ix.Claim → Option Aiur.EnvHandle → Target → String → IO UInt32)
    (assumeBinding : Bool := false)
    : IO UInt32 := do
  let mut failures : Array String := #[]
  match ixePath with
  | some path =>
    let (ixonEnv, envHandle) ← loadBoundIxe path
    IO.println s!"Loaded {path}: {ixonEnv.namedCount} named, \
      {ixonEnv.constCount} consts, {ixonEnv.blobCount} blobs"
    if let some hex := claimHex then
      let (claim, trees) ← loadClaimAndTrees hex
      let label := s!"claim {hex}"
      let target : Target ← match claim with
        | .check _ addr none =>
          if forceLeanWitness then
            let witness ← IO.ofExcept <|
              IxVM.ClaimHarness.buildClaimWitness ixonEnv claim trees
            pure (.leanW witness)
          else pure (.addr addr)
        | _ =>
          let witness ← IO.ofExcept <|
            IxVM.ClaimHarness.buildClaimWitness ixonEnv claim trees
          pure (.leanW witness)
      if (← runOne claim (some envHandle) target label) ≠ 0 then
        failures := failures.push label
    else if names.isEmpty then
      let sorted := ixonEnv.named.toArray.qsort
        (fun a b => toString a.1 < toString b.1)
      for (ixName, named) in sorted do
        let leanName := ixNameToLeanName ixName
        let label := toString leanName
        let claim ← checkClaimOf ixonEnv named.addr assumeBinding
        let target : Target ←
          if forceLeanWitness then
            let w ← mkWitness named.addr ixonEnv assumeBinding
            pure (.leanW w)
          else pure (.addr named.addr)
        if (← runOne claim (some envHandle) target label) ≠ 0 then
          failures := failures.push label
          if !keepGoing then break
    else
      for arg in names do
        match resolveIxeAddr ixonEnv arg with
        | none =>
          IO.eprintln s!"{arg} not found in {path}"
          failures := failures.push arg
          if !keepGoing then break
        | some addr =>
          let label := arg
          let claim ← checkClaimOf ixonEnv addr assumeBinding
          let target : Target ←
            if forceLeanWitness then
              let w ← mkWitness addr ixonEnv assumeBinding
              pure (.leanW w)
            else pure (.addr addr)
          if (← runOne claim (some envHandle) target label) ≠ 0 then
            failures := failures.push label
            if !keepGoing then break
  | none =>
    if claimHex.isSome then
      IO.eprintln "error: --claim requires --ixe <path>"; return 1
    let env ← get_env!
    let runOneByName (name : Lean.Name) (label : String) : IO UInt32 := do
      let ixonEnv ← loadNamedIxonEnv name env
      let addr ← IxVM.ClaimHarness.lookupAddr ixonEnv name
      let claim ← checkClaimOf ixonEnv addr assumeBinding
      if forceLeanWitness then
        let w ← mkWitness addr ixonEnv assumeBinding
        runOne claim none (.leanW w) label
      else
        let envBytes ← match Ixon.serEnv ixonEnv with
          | .error e => throw (IO.userError s!"serEnv failed for {label}: {e}")
          | .ok b => pure b
        let envHandle ← match Aiur.EnvHandle.fromBytes envBytes with
          | .error e => throw (IO.userError s!"EnvHandle.fromBytes failed for {label}: {e}")
          | .ok h => pure h
        runOne claim (some envHandle) (.addr addr) label
    if names.isEmpty then
      let sorted := env.constants.toList.toArray.qsort
        (fun a b => toString a.1 < toString b.1)
      for (name, _) in sorted do
        let label := toString name
        if (← runOneByName name label) ≠ 0 then
          failures := failures.push label
          if !keepGoing then break
    else
      for arg in names do
        match resolveName env arg with
        | none =>
          IO.eprintln s!"{arg} not found"
          failures := failures.push arg
          if !keepGoing then break
          else continue
        | some name =>
          let label := toString name
          if (← runOneByName name label) ≠ 0 then
            failures := failures.push label
            if !keepGoing then break

  if failures.isEmpty then pure 0
  else
    IO.eprintln s!"[{logTag}] {failures.size} failure(s):"
    for n in failures do IO.eprintln s!"  {n}"
    pure 1

end Ix.Check
end
