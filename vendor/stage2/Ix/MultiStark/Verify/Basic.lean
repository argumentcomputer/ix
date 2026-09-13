module
public import Ix.Ixby.Goldilocks

/-! Pure data for the current native Stage 2 multiproof protocol. This does
not import Aiur's DSL, native proof/field types, or a verification oracle.
Canonical parsing, shape admission, and protocol verification are distinct. -/

public section
@[expose] section

namespace MultiStark.Verify

abbrev Bytes := Array UInt8
abbrev Field := Ix.Ixby.Goldilocks
abbrev Ext := Ix.Ixby.ExtGoldilocks

structure Digest where
  bytes : Bytes
  size : bytes.size = 32
  deriving BEq, DecidableEq, Repr

abbrev MerkleCap := Array Digest
abbrev OpenedRound := Array (Array (Array Ext))

structure Commitments where
  stage1 : MerkleCap
  stage2 : MerkleCap
  quotient : MerkleCap
  deriving BEq, DecidableEq, Repr

/-- One shared multiproof per input batch, not legacy per-query paths.
The opened values are indexed by query, matrix, and row coordinate. -/
structure BatchOpening where
  values : Array (Array (Array Field))
  frontier : Array Digest
  deriving BEq, DecidableEq, Repr

structure CommitPhaseStep where
  logArity : UInt8
  siblings : Array (Array Ext)
  frontier : Array Digest
  deriving BEq, DecidableEq, Repr

structure FriProof where
  commits : Array MerkleCap
  commitPow : Array Field
  inputOpenings : Array BatchOpening
  commitOpenings : Array CommitPhaseStep
  finalPoly : Array Ext
  queryPow : Field
  deriving BEq, DecidableEq, Repr

/-- Field order mirrors current `multi-stark::prover::Proof` at 9a906122
and Plonky3's multiproof `FriProof` at 3152b14a. Every per-circuit sequence
except `active` is indexed by ACTIVE position. -/
structure Proof where
  active : Array Bool
  commitments : Commitments
  accumulators : Array Ext
  logDegrees : Array UInt8
  fri : FriProof
  quotient : OpenedRound
  preprocessed : Option OpenedRound
  stage1 : OpenedRound
  stage2 : OpenedRound
  deriving BEq, DecidableEq, Repr

/-- Parser resource admission, not a security parameter recommendation or
the physical capacity of a proving backend. Bounds are explicit caller data. -/
structure DecodeLimits where
  bytes : Nat := 16777216
  vector : Nat := 1048576
  items : Nat := 2097152
  deriving BEq, Repr, Inhabited

inductive DecodeError where
  | byteLimit
  | vectorLimit
  | itemLimit
  | integerRange
  | truncated
  | trailing
  | tag
  | field
  | shape
  | nonCanonical
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A total checked guard. A failed condition never supplies a value to the
continuation. Kept explicit for first-order extraction and phase refinement. -/
def ensure {ε : Type} (condition : Bool) (error : ε) : Except ε Unit :=
  if condition then .ok () else .error error

end MultiStark.Verify
