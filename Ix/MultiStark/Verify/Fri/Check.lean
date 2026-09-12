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

def foldQuery (limits : Limits) (challenges : Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array ReducedOpening) : Except Error (Array QueryRound) := do
  let first ← match reduced[0]? with | some first => pure first | none => throw .initial
  unless first.logHeight == challenges.logGlobal do throw .initial
  unless challenges.betas.size == challenges.arities.size &&
      challenges.betas.size == proof.commitOpenings.size do throw .count
  let mut value := first.value
  let mut nextReduced := 1
  let mut index ← getAt challenges.indices query
  let mut height := challenges.logGlobal
  let mut rows := #[]
  for round in [0:challenges.arities.size] do
    let beta ← getAt challenges.betas round
    let logArity ← getAt challenges.arities round
    unless 1 ≤ logArity && logArity ≤ height do throw .arity
    let arity := 2 ^ logArity
    if arity > limits.foldArity then throw .limit
    let siblings ← getAt (← getAt proof.commitOpenings round).siblings query
    unless siblings.size == arity - 1 do throw .width
    let position := index % arity
    let mut fullRow := #[]
    let mut siblingIndex := 0
    for column in [0:arity] do
      if column == position then fullRow := fullRow.push value
      else
        fullRow := fullRow.push (← getAt siblings siblingIndex)
        siblingIndex := siblingIndex + 1
    height := height - logArity
    index := index / arity
    value ← foldRow limits index height logArity beta fullRow
    rows := rows.push ⟨index, fullRow⟩
    match reduced[nextReduced]? with
    | some next =>
      if next.logHeight == height then
        value := value.add ((Arithmetic.pow2 beta logArity).mul next.value)
        nextReduced := nextReduced + 1
    | none => pure ()
  unless height == challenges.logFinal do throw .foldHeight
  unless nextReduced == reduced.size do throw .unconsumed
  let generator ← (Arithmetic.twoAdicGenerator challenges.logGlobal).mapError Error.arithmetic
  let point := Arithmetic.embed (generator.pow (reverseBits index challenges.logGlobal))
  unless polynomial proof.finalPoly point == value do throw (.finalPoly query)
  return rows

def authenticateCommits (params : Parameters) (challenges : Challenges) (proof : FriProof)
    (queries : Array (Array QueryRound)) : Except Error Unit := do
  unless queries.size == challenges.indices.size && proof.commits.size == challenges.arities.size do throw .count
  let mut height := challenges.logGlobal
  for round in [0:challenges.arities.size] do
    let logArity ← getAt challenges.arities round
    unless logArity ≤ height do throw .height
    height := height - logArity
    let mut indices := #[]
    let mut rows := #[]
    for query in queries do
      let queryRound ← getAt query round
      indices := indices.push queryRound.index
      let flat := queryRound.values.flatMap fun value => #[value.c0, value.c1]
      rows := rows.push #[flat]
    let opening ← getAt proof.commitOpenings round
    let commitment ← getAt proof.commits round
    (Mmcs.check params.capHeight #[⟨height, 2 * 2 ^ logArity⟩] commitment indices
      ⟨rows, opening.frontier⟩).mapError (.commitMmcs round)

/-- Complete deterministic FRI check; success is not a cryptographic
soundness theorem. The input challenger must already include PCS OOD values. -/
def check (limits : Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state : Transcript.Challenger) :
    Except Error (Challenges × Transcript.Challenger) := do
  let (challenges, next) ← replay limits params rounds proof state
  let reduced ← openInputs params challenges rounds proof.inputOpenings
  let mut queries := #[]
  for query in [0:challenges.indices.size] do
    queries := queries.push (← foldQuery limits challenges proof query (← getAt reduced query))
  authenticateCommits params challenges proof queries
  return (challenges, next)

end MultiStark.Verify.Fri
