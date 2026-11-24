import CertiFri.Params
import CertiFri.Proof
import CertiFriP3.GoldilocksExt3
import CertiFriP3.Digest
import CertiFriP3.Pruned

/-! # Out-of-Circuit Multi-STARK Verifier Types (`Ix.Cert.MultiStark.Types`)

Mathlib-free data types matching Protocol `v6` (`Fp^3 = Fp[X]/(X^3 - X - 1)`,
`FriBatching::Tensor`, BLAKE3 `derive_key` domain separation):
- `crates/stark-key/src/lib.rs` (v6 dense verifying-key wire format), and
- `multi-stark/src/{prover.rs,batch.rs}` (bincode v2 `Proof` / `BatchProof` wire format),
over `CertiFri.P3.{Goldilocks, GoldilocksExt3, Digest, PrunedPaths}`.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

abbrev F := Goldilocks
abbrev EF := GoldilocksExt3
abbrev D := Digest

/-- Protocol parameters from the v6 verifying-key global header (`crates/stark-key/src/lib.rs`). -/
structure StarkParams where
  logBlowup : Nat
  capHeight : Nat
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitPowBits : Nat
  queryPowBits : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Convert `StarkParams` to `CertiFri.FriParams`. -/
def StarkParams.toFriParams (p : StarkParams) : FriParams :=
  { logBlowup := p.logBlowup
    logFinalPolyLen := p.logFinalPolyLen
    maxLogArity := p.maxLogArity
    numQueries := p.numQueries
    commitPowBits := p.commitPowBits
    queryPowBits := p.queryPowBits }

/-- Column source of a constraint-graph `Var` node. -/
inductive ColSource where
  | preprocessed
  | main
  | stage2
  deriving DecidableEq, Repr, Inhabited

/-- Row offset of a constraint-graph `Var` node. -/
inductive RowOffset where
  | current
  | next
  deriving DecidableEq, Repr, Inhabited

/-- One node of a compiled `ConstraintGraph` (`multi-stark/src/graph.rs`). -/
inductive GraphNode where
  | const (val : F)
  | var (source : ColSource) (offset : RowOffset) (col : Nat)
  | publicInput (index : Nat)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- One compiled lookup (`multi-stark/src/lookup.rs`). -/
structure CompiledLookup where
  multiplicity : Nat
  args : Array Nat
  deriving DecidableEq, Repr, Inhabited

/-- One circuit inside a Multi-STARK verifying key (`crates/stark-key/src/lib.rs`). -/
structure SysCircuit where
  mainWidth : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  maxConstraintDegree : Nat
  lookupGroupSize : Nat
  lookupPrefixLen : Nat := 0
  nodes : Array GraphNode
  zeros : Array Nat
  lookups : Array CompiledLookup
  deriving DecidableEq, Repr, Inhabited

/-- Number of chained LogUp accumulator groups: `⌈L / k⌉` (0 when `L = 0`). -/
def SysCircuit.logupGroupCount (c : SysCircuit) : Nat :=
  let k := max 1 c.lookupGroupSize
  (c.lookups.size + k - 1) / k

/-- Flattened stage-2 base-column width: `max(⌈L / k⌉, 1) * 3` for `Fp^3`
(`multi-stark/src/lookup.rs`, `SystemDeserialize.lean:251`). -/
def SysCircuit.stage2Width (c : SysCircuit) : Nat :=
  max c.logupGroupCount 1 * 3

/-- Total constraint count folded with α: `zeros.size + max(⌈L / k⌉, 1) * 3`
(`multi-stark/src/system.rs`, `SystemDeserialize.lean:252`). -/
def SysCircuit.constraintCount (c : SysCircuit) : Nat :=
  c.zeros.size + max c.logupGroupCount 1 * 3

/-- Quotient degree as a multiple of trace degree (`multi-stark/src/system.rs`). -/
def SysCircuit.quotientDegree (c : SysCircuit) : Nat :=
  let n := max c.maxConstraintDegree 2 - 1
  if n ≤ 1 then 1
  else 1 <<< (Nat.log2 (n - 1) + 1)

/-- Full Protocol `v6` Multi-STARK verifying key (`System<GoldilocksBlake3Config>`). -/
structure StarkSystem where
  vkDigest : D := default
  params : StarkParams
  circuits : Array SysCircuit
  preprocessedCommit : Option (Array D)
  preprocessedIndices : Array (Option Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Opened OOD values for one commitment round: `[matrix][point][col]`. -/
abbrev OpenedRound := Array (Array (Array EF))

/-- Stage-1, Stage-2, and Quotient commitments of a single shard proof. -/
structure ShardCommitments where
  stage1Trace : Array D
  stage2Trace : Array D
  quotientChunks : Array D
  deriving DecidableEq, Repr, Inhabited

/-- A single shard STARK proof (`multi-stark/src/prover.rs`). -/
structure ShardProof where
  active : Array Bool
  commitments : ShardCommitments
  intermediateAccumulators : Array EF
  logDegrees : Array Nat
  openingProof : FriProof F EF D (PrunedPaths D) (PrunedPaths D)
  quotientOpenedValues : OpenedRound
  preprocessedOpenedValues : Option OpenedRound
  stage1OpenedValues : OpenedRound
  stage2OpenedValues : OpenedRound

/-- One shard's preamble header (`multi-stark/src/batch.rs`). -/
structure ShardHeader where
  active : Array Bool
  stage1Trace : Array D
  logDegrees : Array Nat
  claims : Array (Array F)
  deriving DecidableEq, Repr, Inhabited

/-- One verifier-side batch lookup message (`multi-stark/src/batch.rs`). -/
structure BatchMessage where
  args : Array F
  multiplicity : F
  deriving DecidableEq, Repr, Inhabited

/-- Full batch preamble (`multi-stark/src/batch.rs`). -/
structure BatchPreamble where
  headers : Array ShardHeader
  messages : Array BatchMessage
  deriving DecidableEq, Repr, Inhabited

/-- Full batch proof (`multi-stark/src/batch.rs`). -/
structure BatchProof where
  preamble : BatchPreamble
  proofs : Array ShardProof

/-- Maximum total batch rows (`MAX_BATCH_ROWS = 2^39`, `StarkVerifier.lean`, `batch.rs`). -/
def MAX_BATCH_ROWS : Nat := 1 <<< 39

/-- Maximum lookups per circuit (`< 2^24`, `StarkVerifier.lean`). -/
def MAX_CIRCUIT_LOOKUPS : Nat := 1 <<< 24

/-- Maximum shard count (`1 ≤ shards ≤ 2^16`, `StarkVerifier.lean`). -/
def MAX_BATCH_SHARDS : Nat := 1 <<< 16

/-- Memory-segment LogUp channel tag (`MEMSEG = 16`, `StarkVerifier.lean`). -/
def MEMSEG_CHANNEL : Nat := 16

/-- Maximum number of `MEMSEG = 16` closure pairs permitted in a batch preamble
(`2 * MAX_CLOSURE_PAIRS` messages, matching `crates/aiur/src/trace/stark/batch.rs`). -/
def MAX_CLOSURE_PAIRS : Nat := 1 <<< 16

end Ix.Cert.MultiStark
