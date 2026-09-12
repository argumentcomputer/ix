module
public import Ix.MultiStark.Verify.Basic

/-! Typed raw key data for the current dense native v5 codec. Parsing these
records does not establish graph validity, key approval, or proof validity.
Derived widths/counts are functions, never redundant untrusted wire fields. -/

public section
@[expose] section

namespace MultiStark.Verify

structure Parameters where
  logBlowup : Nat
  capHeight : Nat
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitPowBits : Nat
  queryPowBits : Nat
  deriving BEq, DecidableEq, Repr

def Parameters.words (params : Parameters) : Array Nat :=
  #[params.logBlowup, params.capHeight, params.logFinalPolyLen,
    params.maxLogArity, params.numQueries, params.commitPowBits, params.queryPowBits]

inductive Source where
  | preprocessed | main | stage2
  deriving BEq, DecidableEq, Repr

inductive Node where
  | const (value : Field)
  | var (source : Source) (next : Bool) (column : Nat)
  | «public» (index : Nat)
  | first | last | transition
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)
  | neg (child : Nat)
  deriving BEq, DecidableEq, Repr

structure Lookup where
  multiplicity : Nat
  args : Array Nat
  deriving BEq, DecidableEq, Repr

structure Circuit where
  mainWidth : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  maxConstraintDegree : Nat
  lookupGroupSize : Nat
  nodes : Array Node
  zeros : Array Nat
  lookups : Array Lookup
  deriving BEq, DecidableEq, Repr

/-- Matches native `lookup_groups`, including the lookup-free pass-through.
Group-size admission is separate; total derivation never divides by zero. -/
def Circuit.lookupGroups (circuit : Circuit) : Nat :=
  max 1 ((circuit.lookups.size + max 1 circuit.lookupGroupSize - 1) /
    max 1 circuit.lookupGroupSize)

def Circuit.stage2Width (circuit : Circuit) : Nat := 2 * circuit.lookupGroups
def Circuit.numPublics : Nat := 8
def Circuit.constraintCount (circuit : Circuit) : Nat := circuit.zeros.size + circuit.stage2Width

/-- The exact seven shape words observed for each canonical circuit, including
inactive circuits. Activation is bound separately in the transcript. -/
def Circuit.shapeWords (circuit : Circuit) : Array Nat :=
  #[circuit.constraintCount, circuit.maxConstraintDegree, circuit.preprocessedHeight,
    circuit.preprocessedWidth, circuit.mainWidth, circuit.stage2Width, circuit.lookupGroupSize]

structure Key where
  params : Parameters
  circuits : Array Circuit
  preprocessed : Option MerkleCap
  preprocessedIndices : Array (Option Nat)
  deriving BEq, DecidableEq, Repr

def Key.shapeWords (key : Key) : Array Nat :=
  #[key.circuits.size] ++ key.circuits.flatMap Circuit.shapeWords

end MultiStark.Verify
