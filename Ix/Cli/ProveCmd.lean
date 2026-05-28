/-
  `ix prove <claim-hex> <ixe-path>`: read a persisted claim from the
  content-addressed store at `~/.ix/store/<claim-hex>`, load the env
  from a serialized `.ixe` on disk, build the kernel witness via
  `IxVM.ClaimHarness.buildClaimWitness`, run the Aiur backend's
  `prove`, wrap the resulting opaque proof bytes into an `Ixon.Proof`
  (alongside the claim), and persist the wrapper back to the store.
  Prints the resulting proof blake3 hex on stdout.

  The Ixon.Proof wrapper carries the claim, so `ix verify` only
  needs the proof hex.

  MVP supports `Check addr none` only — other claim variants either
  need tree resolution (deferred) or different witness shapes.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.AssumptionTree
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Store

public section

open System (FilePath)
open IxVM.ClaimHarness

namespace Ix.Cli.ProveCmd

private def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Canonical aiur params shared between prove and verify. Matches
    `Tests.Aiur.Common`. Until these become flags / commit to the
    proof header, they MUST stay in sync between `prove` and
    `verify`. -/
private def commitmentParameters : Aiur.CommitmentParameters :=
  { logBlowup := 1, capHeight := 0 }

private def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  let some claimArg := p.positionalArg? "claim"
    | p.printError "error: must specify <claim-hex>"; return 1
  let some ixeArg := p.positionalArg? "ixe"
    | p.printError "error: must specify <ixe-path>"; return 1
  let claimAddr ← addrOfHex! "claim" (claimArg.as! String)
  let ixePath := ixeArg.as! String

  -- 1. Load + decode claim from the content-addressed store.
  let claimBytes ← StoreIO.toIO (Store.read claimAddr)
  let claim ← IO.ofExcept (Ixon.runGet Ix.Claim.get claimBytes)
  -- Sanity-check the digest is internally consistent.
  let computed := Address.blake3 (Ix.Claim.ser claim)
  if computed != claimAddr then
    IO.eprintln s!"error: claim bytes at {claimAddr} re-hash to {computed}"
    return 1

  -- 2. Load env from .ixe.
  let envBytes ← IO.FS.readBinFile ixePath
  let ixonEnv ← match Ixon.rsDeEnv envBytes with
    | .error e =>
      IO.eprintln s!"error: failed to deserialize {ixePath}: {e}"; return 1
    | .ok env => pure env

  -- NOTE(big envs): `Claim.checkEnv` over the full arena env
  -- (~980 consts) currently exhausts proving memory. The CLI shape
  -- is correct — the IxVM kernel / prover need work before
  -- unconditional CheckEnv on large envs is feasible. Speed-up
  -- path for callers in the meantime: conditional proofs, i.e.
  -- build an asm tree (via `ix tree canonical <addr,addr,...>`)
  -- over constants the prover assumes are well-typed, then pass
  -- `--asm <asm_root>` to the claim so the kernel skips
  -- `check_const` on those leaves.

  -- 3. Resolve assumption / env / contains trees from the store.
  --    Every tree root referenced by the claim must already be
  --    persisted (build with `ix tree canonical`).
  let treeRoots : Array Address := match claim with
    | .check _ (some r)            => #[r]
    | .eval _ _ (some r)           => #[r]
    | .checkEnv root none          => #[root]
    | .checkEnv root (some r)      => #[root, r]
    | .contains tree _             => #[tree]
    | _                            => #[]
  let mut trees : Std.HashMap Address Ix.AssumptionTree := {}
  for r in treeRoots do
    let tbytes ← StoreIO.toIO (Store.read r)
    let tree ← match Ix.AssumptionTree.de tbytes with
      | .error e =>
        IO.eprintln s!"error: tree at {r}: deserialize failed: {e}"
        return 1
      | .ok t => pure t
    -- Sanity-check the stored bytes correspond to the claimed root.
    if tree.root != r then
      IO.eprintln s!"error: tree stored at {r} has merkle root {tree.root}"
      return 1
    trees := trees.insert r tree

  -- 4. Build Aiur backend with the verifying (non-fast) loaders.
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"compilation failed: {e}"; return 1
    | .ok c => pure c
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

  -- 5. Build the per-claim witness against the loaded env.
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv claim trees
  let funIdx ← match compiled.getFuncIdx witness.funcName with
    | some i => pure i
    | none =>
      IO.eprintln s!"error: entrypoint `{witness.funcName}` missing from compiled toplevel"
      return 1

  -- 6. Prove.
  let (_aiurClaim, proof, _outIO) :=
    aiurSystem.prove friParameters funIdx witness.input witness.inputIOBuffer

  -- 7. Wrap + persist. `Ixon.Proof.ser` blake3 is the proof address
  -- returned to the user. The wrapper carries the claim, so
  -- `ix verify` only needs the proof hex.
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
  IO.println (toString proofAddr)
  return 0

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate a STARK proof for a persisted claim against a `.ixe`"

  ARGS:
    claim : String; "32-byte hex address of the persisted claim in `~/.ix/store/`."
    ixe   : String; "Path to a serialized Ixon env (`.ixe`) carrying the claim's referenced constants."
]

end
