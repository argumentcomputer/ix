import IxAICommon.Hash
import IxAICommon.Merkle
import IxAICommon.Literal
import IxAICommon.Paths

/-!
# Shared primitives

What the specification's verifiers, the native pipeline and the mock-up all use: BLAKE3 digests and
canonical encodings (`Hash`), Merkle roots and paths (`Merkle`), kernel normal-form literals of
`IxAICore` values (`Literal`), and the project's location (`Paths`). Its declarations live in the
`IxAI` namespace.
-/
