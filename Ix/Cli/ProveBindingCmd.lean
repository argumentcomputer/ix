/-
  `ix prove-binding <ixe>`: prove the `binding` claim for an environment's
  role binding: the table binds every role and each bound constant meets its
  specification in this specification set.

  The claim depends only on the specification digest and the table's hash,
  so one proof serves every aggregate over that binding (in practice one per
  toolchain). Its claims assume the binding (`ix claim check --assume-binding`,
  `ix prove --ixe --ixes --binding-proof`), and `ix aggregate --binding-proof`
  verifies this proof once, at the root, to discharge that condition.
-/
module
public import Cli
public import Ix.Cli.FormalAiur
public import Ix.Claim
public import Ix.ClaimContext
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Store

public section

namespace Ix.Cli.ProveBindingCmd

def runProveBinding (p : Cli.Parsed) : IO UInt32 := do
  let some ixeArg := p.positionalArg? "ixe"
    | p.printError "error: must specify <ixe>"; return 1
  let path := ixeArg.as! String
  let bytes ← IO.FS.readBinFile path
  let env ← match Ixon.deEnvAnon bytes with
    | .error e => IO.eprintln s!"Failed to deserialize {path}: {e}"; return 1
    | .ok env => pure env
  let some binding := env.roleBinding
    | IO.eprintln s!"{path} carries no role binding; a binding claim names one"; return 1
  -- The table's own support (its roles' records, the evidence theorems and
  -- their closures) wherever the environment lacks it.
  let env ← match IxVM.ClaimHarness.withRoleTable env binding.bytes with
    | .error e => IO.eprintln s!"role table support: {e}"; return 1
    | .ok env => pure env
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofBinding binding.address)
  let claim := Ix.Claim.binding ctx.spec ctx.binding
  let witness ← match IxVM.ClaimHarness.buildClaimWitness env claim {} with
    | .error e => IO.eprintln s!"binding claim witness: {e}"; return 1
    | .ok w => pure w
  let artifactPath ← FormalAiur.artifact p
  let options ← FormalAiur.hostOptions p
  let binary ← FormalAiur.rustHost "ixvm" "ixvm-proof" "IX_AIUR_HOST" options.device
  IO.println s!"Proving the binding claim for {binding.address}"
  (← IO.getStdout).flush
  let result ← FormalAiur.one p artifactPath binary options "prove" claim (.leanW witness)
    s!"binding claim for {binding.address}"
  let some address := result.address
    | IO.eprintln s!"binding claim failed with status {result.code}"; return 1
  let wrapperBytes ← StoreIO.toIO (Store.read address)
  let out : String := match p.flag? "out" with
    | some flag => flag.as! String
    | none => s!"binding-{binding.address}.proof"
  IO.FS.writeBinFile out wrapperBytes
  IO.println s!"{address} written to {out}"
  return 0

end Ix.Cli.ProveBindingCmd

open Ix.Cli.ProveBindingCmd in
def proveBindingCmd : Cli.Cmd := `[Cli|
  "prove-binding" VIA runProveBinding;
  "Prove the `binding` claim for the role binding an .ixe carries: the table binds every role and each bound constant meets its specification. One proof serves every aggregate over that binding; pass it to `ix aggregate --binding-proof` or `ix prove --ixe --ixes --binding-proof`."

  FLAGS:
    out : String; "Where to write the proof (an `Ixon.Proof`; default `binding-<binding hash>.proof`). It is also persisted to `~/.ix/store/`."
    "max-ram" : Nat; "Prover RAM budget in GiB (default 0: 85% of MemAvailable); over-budget executions prove as trace shards."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "gpu-device" : Nat; "Use this CUDA device with the Aiur host (requires a CUDA build)."
    "shard-rows" : Nat; "Maximum rows per function/memory chip per trace shard (power of two; default 0)."
    "retention" : String; "What the batch keeps between its two rounds: auto, retain, or regenerate."
    "no-index"; "Do not record the proof in the shard-proof index."

  ARGS:
    ixe : String; "Path to an .ixe that carries the role binding."
]

end
