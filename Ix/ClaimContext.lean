module

public import Ix.Claim
public import Ix.SpecDigest
public import IxC.Kernel.Ixon.Prelude

/-! # Building a claim's context

A typing claim is relative to a `ClaimContext`: the specification digest,
the role binding's hash and the axioms beyond the standard three. A claim
made today names this specification set (`Ix.SpecDigest.specDigest`) and
no further axiom; only the binding varies. -/

@[expose] public section

namespace Ix.ClaimContext

/-- The context of a claim over the role binding with hash `binding`. -/
def ofBinding (binding : Address) : Except String ClaimContext := do
  return { spec := ← Ix.SpecDigest.specDigest, binding, axioms := none }

/-- The context of a claim over an environment's own role binding. -/
def ofEnv (env : Ixon.Env) : Except String ClaimContext :=
  match env.roleBinding with
  | some binding => ofBinding binding.address
  | none => throw "claim context: the environment carries no role binding"

/-- The context of a claim over the default role table
(`Ix.Kernel.Reader.defaultTable`), the generated table of the compiled
`Init`. Like that table, for tests and the command line only. -/
def ofDefaultTable : Except String ClaimContext := do
  ofBinding (← Ix.Kernel.Reader.defaultTableAddress)

end Ix.ClaimContext

end
