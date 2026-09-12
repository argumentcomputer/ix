module
public import Ix.Ixby.Claim
public import Ix.MultiStark.Verify.Proofs.Source

/-! Specialization of the existing conditional Exec composition to the ACTUAL
pure claim-returning Stage 2 source program. This is an explicit optional
import: the generic IxBy core does not depend on a Stage 2 implementation.
No compiler, Flock, terminal-root, or cryptographic premise is fabricated. -/

public section
@[expose] section

namespace Ix.Ixby.Claim.Stage2

open _root_.MultiStark.Verify (SourceConfig claimBytesWrapper claimBytesWrapper_some_iff stage2VerifyBytes)
open Commitment (Statement)
open Codec (Bytes)

structure Input where
  publicClaim : Bytes
  proofBytes : Bytes
  deriving BEq, DecidableEq, Repr

/-- The exact source computation, not an abstract acceptance oracle. The
compiler's result ABI must map `some C` to the canonical success value and
`none` to rejection; that correspondence is part of its certificate. -/
def SourceEvaluation (config : SourceConfig) (input : Input) (result : Option Bytes) : Prop :=
  claimBytesWrapper config input.publicClaim input.proofBytes = result

theorem source_claim_binding (config : SourceConfig) (input : Input) (expected : Bytes)
    (evaluated : SourceEvaluation config input (some expected)) :
    input.publicClaim = expected ∧ stage2VerifyBytes config expected input.proofBytes = true := by
  obtain ⟨equal, accepted⟩ := (claimBytesWrapper_some_iff config input.publicClaim expected input.proofBytes).mp evaluated
  refine ⟨equal.symm, ?_⟩
  simpa only [equal] using accepted

/-- The public result also reaches the independent byte-level protocol
relation, not only the executable acceptance bit. -/
theorem source_protocol_binding (config : SourceConfig) (input : Input) (expected : Bytes)
    (evaluated : SourceEvaluation config input (some expected)) :
    input.publicClaim = expected ∧
      _root_.MultiStark.Verify.Protocol.Stage2ProtocolAcceptsBytes config expected input.proofBytes := by
  obtain ⟨same, accepted⟩ := source_claim_binding config input expected evaluated
  exact ⟨same, _root_.MultiStark.Verify.Proofs.stage2VerifyBytes_sound config expected input.proofBytes accepted⟩

/-- Terminal acceptance reaches the actual pure Stage 2 verifier for the
externally expected public claim, OR a concrete program/output hash collision.
Compiler reflection, generic Exec soundness, and COMPLETE terminal compression
soundness (including all root discharge) remain explicit required premises.
The protocol corollary below adds deterministic Stage 2 refinement;
cryptographic soundness and Ixon validity remain separate implications. -/
theorem terminal_verified_claim_or_collision
    {ExecProof TerminalProof : Type} {config : SourceConfig}
    {profile : Profile} {profileBytes programBytes outputBytes expectedClaim : Bytes}
    {abi : ByteABI Input (Option Bytes)}
    {verifyExec : Statement → ExecProof → Bool}
    {verifyTerminal : PublicStatement → TerminalProof → Bool} {proof : TerminalProof}
    (profileEncoded : Codec.encodeProfile profile = .ok profileBytes)
    (reflection : ByteExecutionRefinement SourceEvaluation config profile programBytes abi)
    (decoded : abi.decodeOutput outputBytes = some (some expectedClaim))
    (execSound : ExecSoundness profile verifyExec)
    (compressionSound : CompressionSoundness verifyExec verifyTerminal)
    (accepted : verifyTerminal (bindPublic profileBytes programBytes outputBytes) proof = true) :
    ∃ (statement : Statement) (opening : Opening profile statement),
      publicStatement statement = bindPublic profileBytes programBytes outputBytes ∧
      ((∃ proofBytes, stage2VerifyBytes config expectedClaim proofBytes = true) ∨
        opening.bindingFailure programBytes outputBytes) := by
  obtain ⟨statement, opening, matching, result⟩ :=
    terminal_source_or_collision profileEncoded reflection decoded execSound compressionSound accepted
  refine ⟨statement, opening, matching, ?_⟩
  rcases result with ⟨input, evaluated⟩ | collision
  · exact .inl ⟨input.proofBytes, (source_claim_binding config input expectedClaim evaluated).2⟩
  · exact .inr collision

/-- Full deterministic source composition for the caller's public canonical
claim. This does not manufacture the compiler/backend premises or replace
the protocol's cryptographic soundness and application-approval obligations. -/
theorem terminal_protocol_claim_or_collision
    {ExecProof TerminalProof : Type} {config : SourceConfig}
    {profile : Profile} {profileBytes programBytes outputBytes expectedClaim : Bytes}
    {abi : ByteABI Input (Option Bytes)}
    {verifyExec : Statement → ExecProof → Bool}
    {verifyTerminal : PublicStatement → TerminalProof → Bool} {proof : TerminalProof}
    (profileEncoded : Codec.encodeProfile profile = .ok profileBytes)
    (reflection : ByteExecutionRefinement SourceEvaluation config profile programBytes abi)
    (decoded : abi.decodeOutput outputBytes = some (some expectedClaim))
    (execSound : ExecSoundness profile verifyExec)
    (compressionSound : CompressionSoundness verifyExec verifyTerminal)
    (accepted : verifyTerminal (bindPublic profileBytes programBytes outputBytes) proof = true) :
    ∃ (statement : Statement) (opening : Opening profile statement),
      publicStatement statement = bindPublic profileBytes programBytes outputBytes ∧
      ((∃ proofBytes, _root_.MultiStark.Verify.Protocol.Stage2ProtocolAcceptsBytes config expectedClaim proofBytes) ∨
        opening.bindingFailure programBytes outputBytes) := by
  obtain ⟨statement, opening, matching, result⟩ :=
    terminal_verified_claim_or_collision profileEncoded reflection decoded execSound compressionSound accepted
  refine ⟨statement, opening, matching, ?_⟩
  rcases result with ⟨proofBytes, verified⟩ | collision
  · exact .inl ⟨proofBytes, _root_.MultiStark.Verify.Proofs.stage2VerifyBytes_sound config expectedClaim proofBytes verified⟩
  · exact .inr collision

end Ix.Ixby.Claim.Stage2
