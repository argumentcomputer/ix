/-
  `ix prove-binding <ixe>`: prove the `binding` claim for an environment's
  role binding: the table binds every role and each bound constant meets its
  specification in this specification set.

  The claim depends only on the specification digest and the table's hash,
  so one proof serves every aggregate over that binding (in practice one per
  toolchain). Its claims assume the binding (`ix claim check --assume-binding`,
  `ix prove --lanes --binding-proof`), and `ix aggregate --binding-proof`
  verifies this proof once, at the root, to discharge that condition.
-/
module
public import Cli
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.ClaimContext
public import Ix.IxVM
public import Ix.IxVM.Toplevel
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
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compileWithGroups IxVM.functionGroups with
    | .error e => IO.eprintln s!"compilation failed: {e}"; return 1
    | .ok c => pure c
  let some funIdx := compiled.getFuncIdx `verify_claim
    | IO.eprintln "compiled toplevel has no `verify_claim` entry"; return 1
  let system := Aiur.AiurSystem.build compiled.bytecode Aiur.defaultCommitmentParameters
    Aiur.defaultFriParameters
  IO.println s!"Proving the binding claim for {binding.address}"
  (← IO.getStdout).flush
  let proof ← match system.proveIxVM funIdx witness.input witness.inputIOBuffer with
    | .error e => IO.eprintln s!"binding claim: {e}"; return 1
    | .ok (_, proof, _) => pure proof
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  let wrapperBytes := Ixon.Proof.ser wrapper
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let address ← StoreIO.toIO (Store.write wrapperBytes)
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
  "Prove the `binding` claim for the role binding an .ixe carries: the table binds every role and each bound constant meets its specification. One proof serves every aggregate over that binding; pass it to `ix aggregate --binding-proof` or `ix prove --lanes --binding-proof`."

  FLAGS:
    out : String; "Where to write the proof (an `Ixon.Proof`; default `binding-<binding hash>.proof`). It is also persisted to `~/.ix/store/`."

  ARGS:
    ixe : String; "Path to an .ixe that carries the role binding."
]

end
