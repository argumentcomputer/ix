module
public import Ix.Ixby.Claim.Basic
public import Ix.Ixby.Composition

/-! Conditional composition at the exact byte boundary. These are contracts
for certificates and cryptographic backends, not implementations of either.
Hash binding is expressed as a concrete collision alternative: no assertion
that a finite digest is mathematically injective is introduced. -/

public section
@[expose] section

namespace Ix.Ixby.Claim

open Commitment (Statement)
open Codec (Bytes)

def HashCollision (domain : Commitment.Domain) (left right : Bytes) : Prop :=
  left ≠ right ∧ Commitment.hash domain left = Commitment.hash domain right

/-- Only the two actual message pairs from this opening and approved result.
This is not the globally false assumption that BLAKE3 has no collisions. -/
def Opening.bindingFailure {profile : Profile} {statement : Statement}
    (opening : Opening profile statement) (programBytes outputBytes : Bytes) : Prop :=
  let p := Commitment.hash .profile opening.profileBytes
  let b := Commitment.hash .program (p.bytes ++ programBytes)
  HashCollision .program (p.bytes ++ opening.programBytes) (p.bytes ++ programBytes) ∨
    HashCollision .output (b.bytes ++ opening.outputBytes) (b.bytes ++ outputBytes)

theorem Opening.bindings_or_collision {profile : Profile} {statement : Statement}
    (opening : Opening profile statement) (programBytes outputBytes : Bytes)
    (matching : publicStatement statement =
      bindPublic opening.profileBytes programBytes outputBytes) :
    (opening.programBytes = programBytes ∧ opening.outputBytes = outputBytes) ∨
      opening.bindingFailure programBytes outputBytes := by
  have publicEq : bindPublic opening.profileBytes opening.programBytes opening.outputBytes =
      bindPublic opening.profileBytes programBytes outputBytes := by
    rw [← public_bind opening.profileBytes opening.programBytes opening.inputBytes,
      opening.bound]
    exact matching
  by_cases code : opening.programBytes = programBytes
  · by_cases output : opening.outputBytes = outputBytes
    · exact .inl ⟨code, output⟩
    · apply Or.inr
      apply Or.inr
      constructor
      · intro equal
        exact output ((Array.append_right_inj _).mp equal)
      · have equal := congrArg PublicStatement.output publicEq
        simpa only [bindPublic, code] using equal
  · apply Or.inr
    apply Or.inl
    constructor
    · intro equal
      exact code ((Array.append_right_inj _).mp equal)
    · exact congrArg PublicStatement.program publicEq

/-- A byte ABI must recover the source input as well as decode the result.
Arbitrary admitted target inputs cannot bypass the source precondition. -/
structure ByteABI (Input Result : Type) where
  encodeInput : Input → Bytes
  decodeOutput : Bytes → Option Result

/-- Required certificate direction for the exact source, profile, image, ABI,
and resource limits. It must be derived from the compiler's value-level
execution reflection plus its concrete codec correspondence, not assumed from
forward simulation or the existence of an unrelated Lean theorem. -/
def ByteExecutionRefinement {Source Input Result : Type}
    (sourceEval : Source → Input → Result → Prop) (source : Source)
    (profile : Profile) (programBytes : Bytes) (abi : ByteABI Input Result) : Prop :=
  ∀ inputBytes outputBytes, Codec.Evaluates profile programBytes inputBytes outputBytes →
    ∃ input result, abi.encodeInput input = inputBytes ∧
      abi.decodeOutput outputBytes = some result ∧ sourceEval source input result

/-- The additional byte/value correspondence needed alongside the existing
value-level compiler certificate. All fields concern actual checked codec
runs, never an opaque native verifier or a source-evaluation oracle. -/
structure ABICorrespondence {Input Result : Type} (profile : Profile) (program : Program)
    (programBytes : Bytes) (values : ABI Input Result) (bytes : ByteABI Input Result) : Prop where
  program : ∀ {inputBytes} (execution : Codec.Execution profile programBytes inputBytes),
    execution.program.value = program
  input : ∀ {inputBytes} (execution : Codec.Execution profile programBytes inputBytes),
    ∃ input, execution.input.value = values.encodeInput input ∧ bytes.encodeInput input = inputBytes
  output : ∀ {inputBytes} (execution : Codec.Execution profile programBytes inputBytes) result,
    values.decodeOutput execution.output = some result →
      bytes.decodeOutput execution.outputBytes = some result

theorem byte_refinement_of_value_refinement {Source Input Result : Type}
    {sourceEval : Source → Input → Result → Prop} {source : Source}
    {profile : Profile} {program : Program} {programBytes : Bytes}
    {values : ABI Input Result} {bytes : ByteABI Input Result}
    (reflection : ExecutionRefinement sourceEval source profile.limits program values)
    (correspondence : ABICorrespondence profile program programBytes values bytes) :
    ByteExecutionRefinement sourceEval source profile programBytes bytes := by
  intro inputBytes outputBytes evaluated
  obtain ⟨execution, outputEqual⟩ := Codec.evaluates_execution evaluated
  obtain ⟨input, inputEqual, inputEncoded⟩ := correspondence.input execution
  have reference : Ix.Ixby.Evaluates profile.limits program
      (values.encodeInput input) execution.output := by
    simpa only [correspondence.program execution, inputEqual] using execution.reference_evaluates
  obtain ⟨result, decoded, sourceRun⟩ := reflection input execution.output reference
  refine ⟨input, result, inputEncoded, ?_, sourceRun⟩
  simpa only [outputEqual] using correspondence.output execution result decoded

theorem Opening.source_or_collision {Source Input Result : Type}
    {sourceEval : Source → Input → Result → Prop} {source : Source}
    {profile : Profile} {programBytes outputBytes : Bytes} {abi : ByteABI Input Result}
    {result : Result} {statement : Statement}
    (opening : Opening profile statement)
    (reflection : ByteExecutionRefinement sourceEval source profile programBytes abi)
    (decoded : abi.decodeOutput outputBytes = some result)
    (matching : publicStatement statement =
      bindPublic opening.profileBytes programBytes outputBytes) :
    (∃ input, sourceEval source input result) ∨
      opening.bindingFailure programBytes outputBytes := by
  rcases opening.bindings_or_collision programBytes outputBytes matching with bindings | collision
  · have executed : Codec.Evaluates profile programBytes opening.inputBytes outputBytes := by
      simpa only [bindings.1, bindings.2] using opening.evaluated
    obtain ⟨input, actual, _, decodeActual, sourceRun⟩ :=
      reflection opening.inputBytes outputBytes executed
    have equal : actual = result := Option.some.inj (decodeActual.symm.trans decoded)
    exact .inl ⟨input, equal ▸ sourceRun⟩
  · exact .inr collision

/-- The whole approved generic execution relation, not host trace evaluation.
Profile/circuit/key/primitive correctness and Flock cryptographic soundness
must jointly establish this premise for the actual native verifier. -/
def ExecSoundness {Proof : Type} (profile : Profile)
    (verifyExec : Statement → Proof → Bool) : Prop :=
  ∀ statement proof, verifyExec statement proof = true → Exec profile statement

/-- Includes the *complete* Flock transcript and all matrix/structure/jagged
root discharge. A root-conditional FFLONK body does not establish this type.
The terminal verifier sees only the public statement and its compact proof. -/
def CompressionSoundness {ExecProof TerminalProof : Type}
    (verifyExec : Statement → ExecProof → Bool)
    (verifyTerminal : PublicStatement → TerminalProof → Bool) : Prop :=
  ∀ expected proof, verifyTerminal expected proof = true →
    ∃ statement execProof, publicStatement statement = expected ∧
      verifyExec statement execProof = true

theorem terminal_exec {ExecProof TerminalProof : Type} {profile : Profile}
    {verifyExec : Statement → ExecProof → Bool}
    {verifyTerminal : PublicStatement → TerminalProof → Bool}
    {expected : PublicStatement} {proof : TerminalProof}
    (execSound : ExecSoundness profile verifyExec)
    (compressionSound : CompressionSoundness verifyExec verifyTerminal)
    (accepted : verifyTerminal expected proof = true) : PublicExec profile expected := by
  obtain ⟨statement, execProof, matching, verified⟩ := compressionSound expected proof accepted
  exact ⟨statement, matching, execSound statement execProof verified⟩

/-- End-to-end deterministic composition stops at source semantics OR a
specific binding failure in the recovered opening. Computational security
must bound the adversary's ability to produce this collision. Stage 2 protocol
refinement and cryptographic soundness are separate source-side obligations. -/
theorem terminal_source_or_collision {Source Input Result ExecProof TerminalProof : Type}
    {sourceEval : Source → Input → Result → Prop} {source : Source}
    {profile : Profile} {profileBytes programBytes outputBytes : Bytes}
    {abi : ByteABI Input Result} {result : Result}
    {verifyExec : Statement → ExecProof → Bool}
    {verifyTerminal : PublicStatement → TerminalProof → Bool} {proof : TerminalProof}
    (profileEncoded : Codec.encodeProfile profile = .ok profileBytes)
    (reflection : ByteExecutionRefinement sourceEval source profile programBytes abi)
    (decoded : abi.decodeOutput outputBytes = some result)
    (execSound : ExecSoundness profile verifyExec)
    (compressionSound : CompressionSoundness verifyExec verifyTerminal)
    (accepted : verifyTerminal (bindPublic profileBytes programBytes outputBytes) proof = true) :
    ∃ (statement : Statement) (opening : Opening profile statement),
      publicStatement statement = bindPublic profileBytes programBytes outputBytes ∧
      ((∃ input, sourceEval source input result) ∨
        opening.bindingFailure programBytes outputBytes) := by
  obtain ⟨statement, matching, ⟨opening⟩⟩ := terminal_exec execSound compressionSound accepted
  have profileEqual : opening.profileBytes = profileBytes :=
    Except.ok.inj (opening.profileEncoded.symm.trans profileEncoded)
  refine ⟨statement, opening, matching, opening.source_or_collision reflection decoded ?_⟩
  simpa only [profileEqual] using matching

end Ix.Ixby.Claim
