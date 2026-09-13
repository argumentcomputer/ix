module
public import Ix.Ixby.Eval

/-!
# Required compilation-certificate contract

These are generic interfaces and composition theorems, NOT a certification of
Compilatrix, an Ixon runtime bridge, or an implementation of `Check` claims.
Every source/program/ABI/limit in the theorem is the same exact Lean value.
An eventual content-addressed claim adapter must enforce those equalities.
The ABI concerns logical functional values, not machine-word streams.
-/

public section
@[expose] section

namespace Ix.Ixby

/-- Result decoding is partial: malformed output is not a source value.
Canonical byte encodings and their roundtrip laws belong to a concrete ABI. -/
structure ABI (Input Result : Type) where
  encodeInput : Input → Array Value
  decodeOutput : Value → Option Result

/-- The direction needed to infer source evaluation FROM a successful bytecode
run. Forward compiler simulation alone does not have this type. -/
def ExecutionRefinement {Source Input Result : Type}
    (sourceEval : Source → Input → Result → Prop) (source : Source)
    (limits : Limits) (program : Program) (abi : ABI Input Result) : Prop :=
  ∀ input value, Evaluates limits program (abi.encodeInput input) value →
    ∃ result, abi.decodeOutput value = some result ∧ sourceEval source input result

/-- A compiler-execution/certificate relation must bind the exact source and
target program. No arbitrary well-typed theorem can stand in for this premise. -/
def CompilerCertified {Source Input Result : Type}
    (sourceEval : Source → Input → Result → Prop)
    (compiles : Source → Program → Prop) (limits : Limits) (abi : ABI Input Result) : Prop :=
  ∀ source program, compiles source program →
    ExecutionRefinement sourceEval source limits program abi

theorem certified_execution {Source Input Result : Type}
    {sourceEval : Source → Input → Result → Prop}
    {compiles : Source → Program → Prop} {limits : Limits} {abi : ABI Input Result}
    {source : Source} {program : Program} {input : Input} {value : Value}
    {result : Result}
    (certified : CompilerCertified sourceEval compiles limits abi)
    (compiled : compiles source program)
    (executed : Evaluates limits program (abi.encodeInput input) value)
    (decoded : abi.decodeOutput value = some result) :
    sourceEval source input result := by
  obtain ⟨actual, hdecode, heval⟩ := certified source program compiled input value executed
  have equal : actual = result := Option.some.inj (hdecode.symm.trans decoded)
  simpa [equal] using heval

/-- An alternative route from an existing forward simulation: if the source
terminates and the simulation supplies a successful target run under the same
resource profile, target determinism identifies the observed result. Both
extra premises are explicit; this theorem does not prove source termination
or resource adequacy for Compilatrix's accepted fragment. -/
theorem refinement_of_forward_and_termination {Source Input Result : Type}
    {sourceEval : Source → Input → Result → Prop} {source : Source}
    {limits : Limits} {program : Program} {abi : ABI Input Result}
    (terminates : ∀ input, ∃ result, sourceEval source input result)
    (forward : ∀ input result, sourceEval source input result →
      ∃ value, Evaluates limits program (abi.encodeInput input) value ∧
        abi.decodeOutput value = some result) :
    ExecutionRefinement sourceEval source limits program abi := by
  intro input value executed
  obtain ⟨result, sourceRun⟩ := terminates input
  obtain ⟨expected, targetRun, decoded⟩ := forward input result sourceRun
  have equal : value = expected := evaluates_deterministic executed targetRun
  exact ⟨result, equal.symm ▸ decoded, sourceRun⟩

end Ix.Ixby
