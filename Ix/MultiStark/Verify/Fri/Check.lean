module
public import Ix.MultiStark.Verify.Fri.Transcript
public import Ix.MultiStark.Verify.Fri.Fold
public import Ix.MultiStark.Verify.Fri.Inputs

public section
@[expose] section

namespace MultiStark.Verify.Fri

structure QueryRound where
  index : Nat
  values : Array Ext
  deriving BEq, DecidableEq, Repr

structure FoldState where
  index : Nat
  height : Nat
  nextReduced : Nat
  value : Ext
  deriving BEq, DecidableEq, Repr

/-- Insert the carried evaluation without dropping or reordering siblings. -/
def insertValue (value : Ext) : Nat → List Ext → Except Error (List Ext)
  | 0, siblings => .ok (value :: siblings)
  | _ + 1, [] => .error .width
  | position + 1, sibling :: siblings => do
    return sibling :: (← insertValue value position siblings)

def rollIn (beta : Ext) (logArity : Nat) (reduced : Array ReducedOpening)
    (state : FoldState) : FoldState :=
  match reduced[state.nextReduced]? with
  | some next =>
    if next.logHeight == state.height then
      { state with
        value := state.value.add ((Arithmetic.pow2 beta logArity).mul next.value)
        nextReduced := state.nextReduced + 1 }
    else state
  | none => state

def foldRound (limits : Limits) (challenges : Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array ReducedOpening) (round : Nat) (state : FoldState) :
    Except Error (FoldState × QueryRound) := do
  let beta ← getAt challenges.betas round
  let logArity ← getAt challenges.arities round
  ensure (1 ≤ logArity && logArity ≤ state.height) .arity
  let arity := 2 ^ logArity
  ensure (arity ≤ limits.foldArity) .limit
  let siblings ← getAt (← getAt proof.commitOpenings round).siblings query
  ensure (siblings.size == arity - 1) .width
  let fullRow := (← insertValue state.value (state.index % arity) siblings.toList).toArray
  let height := state.height - logArity
  let index := state.index / arity
  let value ← foldRow limits index height logArity beta fullRow
  return (rollIn beta logArity reduced ⟨index, height, state.nextReduced, value⟩, ⟨index, fullRow⟩)

def foldRounds (limits : Limits) (challenges : Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array ReducedOpening) :
    Nat → Nat → FoldState → Except Error (FoldState × List QueryRound)
  | _, 0, state => .ok (state, [])
  | round, remaining + 1, state => do
    let (middle, row) ← foldRound limits challenges proof query reduced round state
    let (final, rows) ← foldRounds limits challenges proof query reduced (round + 1) remaining middle
    return (final, row :: rows)

def finishQuery (challenges : Challenges) (proof : FriProof) (query : Nat)
    (reduced : Array ReducedOpening) (state : FoldState) : Except Error Unit := do
  ensure (state.height == challenges.logFinal) .foldHeight
  ensure (state.nextReduced == reduced.size) .unconsumed
  let generator ← (Arithmetic.twoAdicGenerator challenges.logGlobal).mapError Error.arithmetic
  -- Native FRI uses the GLOBAL group's generator and bit width here, even
  -- though the index has already been divided by every folding arity.
  let point := Arithmetic.embed (generator.pow (reverseBits state.index challenges.logGlobal))
  ensure (polynomial proof.finalPoly point == state.value) (.finalPoly query)

def initialOpening (reduced : Array ReducedOpening) : Except Error ReducedOpening :=
  match reduced[0]? with | some first => .ok first | none => .error .initial

def foldQuery (limits : Limits) (challenges : Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array ReducedOpening) : Except Error (Array QueryRound) := do
  let first ← initialOpening reduced
  ensure (first.logHeight == challenges.logGlobal) .initial
  ensure (challenges.betas.size == challenges.arities.size &&
      challenges.betas.size == proof.commitOpenings.size) .count
  let index ← getAt challenges.indices query
  let (final, rows) ← foldRounds limits challenges proof query reduced 0 challenges.arities.size
    ⟨index, challenges.logGlobal, 1, first.value⟩
  finishQuery challenges proof query reduced final
  return rows.toArray

def flattenRow : List Ext → List Field
  | [] => []
  | value :: values => value.c0 :: value.c1 :: flattenRow values

/-- Collect every query's verifier-derived index and saved pre-roll-in row. -/
def commitRows (round : Nat) :
    List (Array QueryRound) → Except Error (List Nat × List (Array (Array Field)))
  | [] => .ok ([], [])
  | query :: queries => do
    let row ← getAt query round
    let (indices, rows) ← commitRows round queries
    return (row.index :: indices, #[(flattenRow row.values.toList).toArray] :: rows)

def authenticateCommitRounds (params : Parameters) (proof : FriProof)
    (queries : Array (Array QueryRound)) : List Nat → Nat → Nat → Except Error Unit
  | [], _, _ => .ok ()
  | logArity :: arities, round, height => do
    ensure (logArity ≤ height) .height
    let height := height - logArity
    let (indices, rows) ← commitRows round queries.toList
    let opening ← getAt proof.commitOpenings round
    let commitment ← getAt proof.commits round
    (Mmcs.check params.capHeight #[⟨height, 2 * 2 ^ logArity⟩] commitment indices.toArray
      ⟨rows.toArray, opening.frontier⟩).mapError (.commitMmcs round)
    authenticateCommitRounds params proof queries arities (round + 1) height

def authenticateCommits (params : Parameters) (challenges : Challenges) (proof : FriProof)
    (queries : Array (Array QueryRound)) : Except Error Unit := do
  ensure (queries.size == challenges.indices.size && proof.commits.size == challenges.arities.size) .count
  authenticateCommitRounds params proof queries challenges.arities.toList 0 challenges.logGlobal

def foldQueries (limits : Limits) (challenges : Challenges) (proof : FriProof)
    (reduced : Array (Array ReducedOpening)) : Nat → Nat → Except Error (List (Array QueryRound))
  | _, 0 => .ok []
  | query, remaining + 1 => do
    let rows ← foldQuery limits challenges proof query (← getAt reduced query)
    let rest ← foldQueries limits challenges proof reduced (query + 1) remaining
    return rows :: rest

/-- Complete deterministic FRI check; success is not a cryptographic
soundness theorem. The input challenger must already include PCS OOD values. -/
def check (limits : Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state : Transcript.Challenger) :
    Except Error (Challenges × Transcript.Challenger) := do
  let (challenges, next) ← replay limits params rounds proof state
  let reduced ← openInputs params challenges rounds proof.inputOpenings
  let queries ← foldQueries limits challenges proof reduced 0 challenges.indices.size
  authenticateCommits params challenges proof queries.toArray
  return (challenges, next)

end MultiStark.Verify.Fri
