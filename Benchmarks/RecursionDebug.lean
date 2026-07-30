import Ix.IxVM
import Ix.IxVM.ClaimHarness
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Interpret
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.Cli.NameResolve

/-!
# Recursive-verifier debugging harness

Proves the IxVM typecheck of a single constant (same recipe as
`bench-typecheck --recursive`'s inner prove), SAVES the proof/vk/claims blobs
to disk, and re-runs the in-circuit recursive verifier
(`verify_multi_stark_proof`) from the saved blobs — so an expensive prove
(e.g. `Array.extract_append`) runs once and the recursive-verification step
can be replayed cheaply under different execution backends:

```
lake exe bench-recursion-debug --ixe init.ixe --const Nat.add_comm
lake exe bench-recursion-debug --ixe init.ixe --const Array.extract_append --mode interp

  --ixe <path>     serialized `Ixon.Env` (default: init.ixe)
  --const <name>   fully-qualified constant to typecheck-prove (required)
  --dir <path>     blob directory (default: recursion-debug); blobs are
                   `<dir>/<const>.{proof,vk,claims}.bin` — if all three exist
                   the prove is skipped and blobs are loaded instead
  --reprove        force a fresh prove even when blobs exist
  --skip-deps      subject-only check (`verify_const`) instead of the
                   full-closure `verify_claim` default
  --queries N      FRI numQueries (default 100 — matches bench-typecheck
                   --recursive); must match between prove and replay!
  --mode M         how to run the recursive verifier over the saved proof:
                     native    codegen'd Rust verifier (default; the
                               production path bench-typecheck uses)
                     bytecode  generic Rust Aiur bytecode interpreter
                     interp    Lean debug interpreter — call-stack trace +
                               pretty-printed values on failure (slow)
  --depth N        interp: pointer-deref depth in the pp (default 2)
  --stack N        interp: max call-stack frames shown (default 40)
```
-/

open Lean (Name)

def argNat (args : List String) (flag : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def argStr (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

def commitParams : Aiur.CommitmentParameters := { logBlowup := 2, capHeight := 0 }

def friParams (numQueries : Nat) : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 20 }

def secs (t0 t1 : Nat) : Float := (Float.ofNat (t1 - t0)) / 1e9

/-- Prove `constName`'s typecheck and return `(proofBytes, vkBytes, claimBytes)`. -/
def proveConst (ixePath constName : String) (skipDeps : Bool)
    (fri : Aiur.FriParameters) : IO (Option (ByteArray × ByteArray × ByteArray)) := do
  let .ok toplevel := IxVM.ixVM
    | IO.eprintln "IxVM toplevel merge failed"; return none
  let .ok compiled := toplevel.compile
    | IO.eprintln "IxVM compile failed"; return none
  let entrypoint := if skipDeps then `verify_const else `verify_claim
  let some funIdx := compiled.getFuncIdx entrypoint
    | IO.eprintln s!"{entrypoint} entrypoint missing"; return none
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitParams fri
  let ixonEnv ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return none
    | .ok env => pure env
  let some addr := Ix.Cli.NameResolve.resolveIxeAddr ixonEnv constName
    | IO.eprintln s!"{constName} not found in {ixePath}"; return none
  IO.println s!"proving {constName} ({if skipDeps then "subject-only" else "full closure"}, \
    numQueries={fri.numQueries}) …"
  (← IO.getStdout).flush
  let t0 ← IO.monoNanosNow
  let (claim, proof) ←
    if skipDeps then
      let witness := IxVM.ClaimHarness.buildVerifyConst ixonEnv addr
      let (claim, proof, _) := aiurSystem.proveIxVM funIdx witness.input witness.inputIOBuffer
      pure (claim, proof)
    else do
      let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe: {e}"; return none
        | .ok h => pure h
      match aiurSystem.proveAddrWithEnv funIdx envHandle addr.hash with
      | .error e => IO.eprintln s!"proveAddrWithEnv failed: {e}"; return none
      | .ok (claimBytes, proof, _) =>
        -- `verify_claim`'s public input is the 32-G blake3 digest of the
        -- serialized `Ix.Claim` (same recipe as `ix verify` / bench-typecheck).
        let digest := Address.blake3 claimBytes
        pure (Aiur.buildClaim funIdx (digest.hash.data.map .ofUInt8) #[], proof)
  let t1 ← IO.monoNanosNow
  let proofBytes := proof.toBytes
  IO.println s!"inner prove: {secs t0 t1} s, proof {proofBytes.size} bytes"
  -- Sanity: the inner proof must verify out-of-circuit before we chase the
  -- recursive verifier.
  match aiurSystem.verify claim proof with
  | .ok () => IO.println "inner proof verifies out-of-circuit: ok"
  | .error e => IO.eprintln s!"⚠ inner proof FAILS out-of-circuit verify: {e}"
  return some (proofBytes, aiurSystem.vkBytes, MultiStark.serializeClaims #[claim])

def main (args : List String) : IO UInt32 := do
  let ixePath := (argStr args "--ixe").getD "init.ixe"
  let some constName := argStr args "--const"
    | IO.eprintln "usage: bench-recursion-debug --const <name> [--ixe <path>] \
        [--dir <path>] [--mode native|bytecode|interp] [--skip-deps] [--reprove]"
      return 1
  let dir := (argStr args "--dir").getD "recursion-debug"
  let mode := (argStr args "--mode").getD "native"
  let skipDeps := args.contains "--skip-deps"
  let fri := friParams (argNat args "--queries" 100)
  let depth := argNat args "--depth" 2
  let stackLimit := argNat args "--stack" 40
  IO.FS.createDirAll dir
  let tag := if skipDeps then s!"{constName}.skipdeps" else constName
  let tag := s!"{tag}.q{fri.numQueries}"
  let proofPath : System.FilePath := s!"{dir}/{tag}.proof.bin"
  let vkPath : System.FilePath := s!"{dir}/{tag}.vk.bin"
  let claimsPath : System.FilePath := s!"{dir}/{tag}.claims.bin"
  let allSaved := (← proofPath.pathExists) && (← vkPath.pathExists)
    && (← claimsPath.pathExists)
  let (proofBytes, vkBytes, claimBytes) ←
    if allSaved && !args.contains "--reprove" then do
      IO.println s!"loading saved blobs {dir}/{tag}.*.bin"
      pure (← IO.FS.readBinFile proofPath, ← IO.FS.readBinFile vkPath,
            ← IO.FS.readBinFile claimsPath)
    else do
      let some blobs ← proveConst ixePath constName skipDeps fri | return 1
      let (p, v, c) := blobs
      IO.FS.writeBinFile proofPath p
      IO.FS.writeBinFile vkPath v
      IO.FS.writeBinFile claimsPath c
      IO.println s!"saved blobs to {dir}/{tag}.*.bin"
      pure (p, v, c)
  IO.println s!"proof {proofBytes.size} bytes, vk {vkBytes.size} bytes, \
    claims {claimBytes.size} bytes"

  -- ── the recursive verifier over the saved blobs ───────────────────────────
  let .ok vTop := MultiStark.multiStark
    | IO.eprintln "multi-stark verifier toplevel merge failed"; return 1
  -- `--list-funcs`: dump the compiled verifier's funIdx → name table (for
  -- decoding fun_idx stacks printed by the Rust bytecode interpreter).
  if args.contains "--list-funcs" then
    let .ok vCompiled := vTop.compile
      | IO.eprintln "multi-stark verifier compile failed"; return 1
    let entries := vCompiled.nameMap.toArray.qsort (·.2 < ·.2)
    for (g, i) in entries do
      IO.println s!"{i} {g}"
    return 0
  let pubInput := MultiStark.verifierPubInput vkBytes claimBytes
  if mode == "interp" then
    -- Lean debug interpreter: call-stack + pretty-printed values on failure.
    let decls ← match vTop.mkDecls with
      | .error e => IO.eprintln s!"mkDecls failed: {e}"; return 1
      | .ok d => pure d
    let gName := Aiur.Global.mk `verify_multi_stark_proof
    let inputTypes ← match decls.getByKey gName with
      | some (.function f) => pure (f.inputs.map (·.2))
      | _ => IO.eprintln "verify_multi_stark_proof not in decls"; return 1
    let inputs := Aiur.unflattenInputs decls pubInput inputTypes
    let toGs := fun (b : ByteArray) => b.data.map Aiur.G.ofUInt8
    let io := (((default : Aiur.IOBuffer).extend 0 #[Aiur.G.ofNat 0] (toGs proofBytes)).extend
        1 #[Aiur.G.ofNat 0] (toGs vkBytes)).extend
        2 #[Aiur.G.ofNat 0] (toGs claimBytes)
    IO.println "running verify_multi_stark_proof under the Lean debug interpreter …"
    (← IO.getStdout).flush
    let t0 ← IO.monoNanosNow
    match Aiur.runFunction decls gName inputs io with
    | (.error e, s) =>
      let t1 ← IO.monoNanosNow
      IO.eprintln s!"REJECTED after {secs t0 t1} s:\n{e.ppDeref s.store depth stackLimit}"
      return 1
    | (.ok v, s) =>
      let t1 ← IO.monoNanosNow
      IO.println s!"ACCEPTED in {secs t0 t1} s: {Aiur.Value.ppDeref s.store depth v}"
      return 0
  else
    let .ok vCompiled := vTop.compile
      | IO.eprintln "multi-stark verifier compile failed"; return 1
    let some vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof
      | IO.eprintln "verify_multi_stark_proof entrypoint missing"; return 1
    let useBytecode := mode == "bytecode"
    IO.println s!"executing verify_multi_stark_proof \
      ({if useBytecode then "Rust bytecode interpreter" else "codegen'd native"}) …"
    (← IO.getStdout).flush
    let t0 ← IO.monoNanosNow
    match vCompiled.bytecode.executeMultiStark vIdx pubInput proofBytes vkBytes
        claimBytes useBytecode with
    | .error e =>
      let t1 ← IO.monoNanosNow
      IO.eprintln s!"REJECTED after {secs t0 t1} s: {e}"
      return 1
    | .ok (out, qc) =>
      let t1 ← IO.monoNanosNow
      let stats := Aiur.computeStats vCompiled qc
      IO.println s!"ACCEPTED in {secs t0 t1} s, output {out}, \
        fft-cost {stats.totalFftCost}"
      return 0
