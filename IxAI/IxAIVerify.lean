import IxAIVerify.Spec
import IxAIVerify.Ixon
import IxAIVerify.Tools
import IxAIVerify.Compression
import IxAIVerify.Aiur
import IxAIVerify.Trajectory
import IxAIVerify.Package
import IxAIVerify.Combined
import IxAIVerify.Submission
import IxAIVerify.Sandbox
import IxAIVerify.Cli

/-!
# The verification layer

Encodings, expected claims, commitments, proof checking and their composition. It depends on the
specification (`IxAICore`), the shared primitives of `IxAICommon` (BLAKE3, Merkle roots, literals)
and the native training claims of `IxAI`, never on the toy-kernel mock-up or the proving or
experiment layers. `docs/verification.md` states the contract.
-/
