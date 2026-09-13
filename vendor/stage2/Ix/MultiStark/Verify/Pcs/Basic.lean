module
public import Ix.MultiStark.Verify.Arithmetic
public import Ix.MultiStark.Verify.Transcript.Basic
public import Ix.MultiStark.Verify.Mmcs

public section
@[expose] section

namespace MultiStark.Verify.Pcs

structure PointOpening where
  point : Ext
  values : Array Ext
  deriving BEq, DecidableEq, Repr

/-- Trace-domain log size, before the FRI blowup. Width is owned by the
key/statement adapter, never inferred from a private opened row. -/
structure Matrix where
  logDegree : Nat
  width : Nat
  points : Array PointOpening
  deriving BEq, DecidableEq, Repr

structure Round where
  commitment : MerkleCap
  matrices : Array Matrix
  deriving BEq, DecidableEq, Repr

/-- The PCS observes every OOD value before sampling the FRI combination
challenge: round, matrix, point, coordinate, then extension basis order. -/
def observePointList (limits : Transcript.Limits) : List PointOpening → Transcript.Action Unit
  | [] => pure ()
  | opening :: rest => do
    Transcript.observeExts limits opening.values.toList
    observePointList limits rest

def observeMatrixList (limits : Transcript.Limits) : List Matrix → Transcript.Action Unit
  | [] => pure ()
  | matrix :: rest => do
    observePointList limits matrix.points.toList
    observeMatrixList limits rest

def observeRoundList (limits : Transcript.Limits) : List Round → Transcript.Action Unit
  | [] => pure ()
  | round :: rest => do
    observeMatrixList limits round.matrices.toList
    observeRoundList limits rest

def observeOpenings (limits : Transcript.Limits) (rounds : Array Round) : Transcript.Action Unit :=
  observeRoundList limits rounds.toList

end MultiStark.Verify.Pcs
