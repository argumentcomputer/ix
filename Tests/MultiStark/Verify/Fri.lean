module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Fri

namespace Tests.MultiStark.Verify.Fri

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private def e (n : Nat) : Ext := Arithmetic.fromNat n
private def okEquals {ε α : Type} [BEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with | .ok actual => actual == expected | .error _ => false

private structure Fixture where
  params : Parameters
  rounds : Array Pcs.Round
  proof : FriProof
  state : Transcript.Challenger
  challenges : Fri.Challenges

/-- A fully committed constant input polynomial and zero FRI quotient. The
tree has just four input leaves and two FRI rows, so its entire authentication
frontier is enumerated directly, independently of the verifier's tree walk. -/
private def fixture : Except Fri.Error Fixture := do
  let params : Parameters := ⟨1, 0, 0, 1, 2, 0, 0⟩
  let leaf := Mmcs.hashRow #[7]
  let pair := Mmcs.compress leaf leaf
  let cap := #[Mmcs.compress pair pair]
  let friLeaf := Mmcs.hashRow #[0, 0, 0, 0]
  let friCap := #[Mmcs.compress friLeaf friLeaf]
  let rounds : Array Pcs.Round := #[⟨cap, #[⟨1, 1, #[⟨e 9, #[e 7]⟩]⟩]⟩]
  let proof : FriProof := ⟨#[friCap], #[0], #[⟨#[#[#[7]], #[#[7]]], #[]⟩],
    #[⟨1, #[#[e 0], #[e 0]], #[]⟩], #[e 0], 0⟩
  let (_, state) ← ((Pcs.observeOpenings {} rounds).run {}).mapError Fri.Error.transcript
  let (challenges, _) ← Fri.replay {} params rounds proof state
  let indices := challenges.indices
  let mut boundary := #[]
  for index in [0:4] do
    let sibling := if index % 2 == 0 then index + 1 else index - 1
    if !indices.contains index && indices.contains sibling then boundary := boundary.push leaf
  let spansBoth := indices.any (· < 2) && indices.any (· ≥ 2)
  if !spansBoth then boundary := boundary.push pair
  let friBoundary := if spansBoth then #[] else #[friLeaf]
  let proof := { proof with
    inputOpenings := #[⟨#[#[#[7]], #[#[7]]], boundary⟩]
    commitOpenings := #[⟨1, #[#[e 0], #[e 0]], friBoundary⟩] }
  return ⟨params, rounds, proof, state, challenges⟩

private def reductionChecks : IO (List Check) := do
  let params : Parameters := ⟨1, 0, 0, 1, 1, 0, 0⟩
  let challenges : Fri.Challenges := ⟨e 2, #[], #[0], #[], 4, 1⟩
  let z1 : Ext := ⟨9, 17⟩
  let z2 : Ext := ⟨10, 19⟩
  let linear (constant slope : Nat) (z : Ext) := (e constant).add ((e slope).mul z)
  let high : Pcs.Matrix := ⟨3, 2, #[
    ⟨z1, #[linear 2 3 z1, linear 4 5 z1]⟩,
    ⟨z2, #[linear 2 3 z2, linear 4 5 z2]⟩]⟩
  let low : Pcs.Matrix := ⟨2, 1, #[⟨z1, #[linear 1 7 z1]⟩]⟩
  let constant : Pcs.Matrix := ⟨0, 1, #[⟨z1, #[e 19]⟩]⟩
  let laterHigh : Pcs.Matrix := ⟨3, 1, #[⟨z1, #[linear 6 11 z1]⟩]⟩
  let laterLow : Pcs.Matrix := ⟨2, 1, #[⟨z1, #[linear 8 13 z1]⟩, ⟨z2, #[linear 8 13 z2]⟩]⟩
  let rounds : Array Pcs.Round := #[⟨#[], #[high, low, constant]⟩, ⟨#[], #[laterHigh, laterLow]⟩]
  let openings : Array BatchOpening := #[⟨#[#[#[23, 39], #[50], #[19]]], #[]⟩,
    ⟨#[#[#[83], #[99]]], #[]⟩]
  let swappedHigh := { high with points := high.points.map fun opening =>
    { opening with values := opening.values.reverse } }
  let swappedRounds : Array Pcs.Round := #[⟨#[], #[swappedHigh, low, constant]⟩, ⟨#[], #[laterHigh, laterLow]⟩]
  let swappedRows : Array BatchOpening := #[⟨#[#[#[39, 23], #[50], #[19]]], #[]⟩,
    ⟨#[#[#[83], #[99]]], #[]⟩]
  let quadratic : Pcs.Matrix := ⟨3, 1, #[⟨z1, #[z1.mul z1]⟩, ⟨z2, #[z2.mul z2]⟩]⟩
  let squareRows : Array BatchOpening := #[⟨#[#[#[49]]], #[]⟩]
  let badConstant := { constant with points := #[⟨z1, #[e 20]⟩] }
  let badRounds : Array Pcs.Round := #[⟨#[], #[high, low, badConstant]⟩, ⟨#[], #[laterHigh, laterLow]⟩]
  return [
    ("nonzero quotient powers continue across matrices and batches by height", okEquals
      (Fri.reduceQuery params challenges rounds openings 0) #[⟨4, e 241⟩, ⟨3, e 85⟩, ⟨1, e 0⟩]),
    ("coordinate order determines each alpha-weighted contribution", okEquals
      (Fri.reduceQuery params challenges swappedRounds swappedRows 0) #[⟨4, e 231⟩, ⟨3, e 85⟩, ⟨1, e 0⟩]),
    ("batch order changes the nonzero reduction in every shared height", okEquals
      (Fri.reduceQuery params challenges rounds.reverse openings.reverse 0) #[⟨4, e 141⟩, ⟨3, e 67⟩, ⟨1, e 0⟩]),
    ("opening points contribute both extension coordinates in order", okEquals
      (Fri.reduceQuery params challenges #[⟨#[], #[quadratic]⟩] squareRows 0) #[⟨4, ⟨50, 55⟩⟩]),
    ("reversing points changes their alpha weights", okEquals
      (Fri.reduceQuery params challenges #[⟨#[], #[{ quadratic with points := quadratic.points.reverse }]⟩] squareRows 0)
      #[⟨4, ⟨49, 53⟩⟩]),
    ("nonzero constant-height quotient is rejected", !(Fri.reduceQuery params challenges badRounds openings 0).isOk),
    ("coordinate reduction never truncates an extra opened value", !(Fri.reduceCoordinates
      (e 2) (e 1) [3] [e 5, e 7] (e 1) (e 0)).isOk),
    ("coordinate reduction never truncates an extra row value", !(Fri.reduceCoordinates
      (e 2) (e 1) [3, 4] [e 5] (e 1) (e 0)).isOk),
    ("empty coordinate reduction preserves both accumulators", okEquals
      (Fri.reduceCoordinates (e 2) (e 1) [] [] (e 5) (e 11)) (e 5, e 11)),
    ("input quotient rejects a singular opening point", !(Fri.reducePoints
      (e 2) (e 7) 1 #[49] [⟨e 7, #[e 49]⟩] (e 1) (e 0)).isOk),
    ("matrix reduction checks declared width independently of row and opening", !(Fri.reduceQuery params challenges
      #[⟨#[], #[{ quadratic with width := 2 }]⟩] squareRows 0).isOk),
    ("query reduction requires the original verifier query", !(Fri.reduceQuery params challenges rounds openings 1).isOk)
  ]

private def queryChainChecks : IO (List Check) := do
  let insertion : List Check := [
    ("row insertion preserves all siblings at every legal position", (List.range 4).all fun position =>
      okEquals (Fri.insertValue (e 11) position [e 2, e 3, e 5])
        ([e 2, e 3, e 5].take position ++ e 11 :: [e 2, e 3, e 5].drop position)),
    ("row insertion rejects an index beyond the end", !(Fri.insertValue (e 11) 4 [e 2, e 3, e 5]).isOk),
    ("empty sibling list permits exactly position zero", okEquals (Fri.insertValue (e 11) 0 []) [e 11] &&
      !(Fri.insertValue (e 11) 1 []).isOk),
    ("extension flattening preserves c0-c1 and value order", Fri.flattenRow [⟨2, 3⟩, ⟨5, 7⟩] == [2, 3, 5, 7])
  ]
  let vector : Except Fri.Error (List Check) := do
    let beta0 := e 2
    let beta1 : Ext := ⟨11, 13⟩
    let points0 ← Fri.rowPoints 15 4 1
    let row0 := points0.map fun x => (e 3).add ((e 5).mul (Arithmetic.embed x))
    let first ← Fri.getAt row0 1
    let sibling0 ← Fri.getAt row0 0
    -- First row's linear polynomial folds to 3 + 5*2 = 13; the
    -- height-four roll-in adds 2^2 * 7, giving the next carried value 41.
    let carried := e 41
    let points1 ← Fri.rowPoints 3 2 2
    let selected := Arithmetic.embed (← Fri.getAt points1 3)
    let slope : Ext := ⟨2, 3⟩
    let row1 := points1.map fun x => carried.add (slope.mul ((Arithmetic.embed x).sub selected))
    let reduced : Array Fri.ReducedOpening := #[⟨5, first⟩, ⟨4, e 7⟩, ⟨2, ⟨17, 19⟩⟩]
    let fourth := (beta1.mul beta1).mul (beta1.mul beta1)
    let finalValue := (carried.add (slope.mul (beta1.sub selected))).add (fourth.mul ⟨17, 19⟩)
    let globalGenerator ← (Arithmetic.twoAdicGenerator 5).mapError Fri.Error.arithmetic
    -- reverseBits 3 5 = 24, whereas reverseBits 3 2 = 3. Changing BOTH
    -- the group and bit width gives the same point; mixing their widths
    -- does not. A nonconstant polynomial detects the latter error.
    let finalPoint := Arithmetic.embed (globalGenerator.pow 24)
    let finalSlope : Ext := ⟨23, 29⟩
    let finalPoly := #[finalValue.sub (finalSlope.mul finalPoint), finalSlope]
    let challenges : Fri.Challenges := ⟨e 31, #[beta0, beta1], #[31], #[1, 2], 5, 2⟩
    let proof : FriProof := ⟨#[], #[], #[], #[⟨1, #[#[sibling0]], #[]⟩,
      ⟨2, #[row1.extract 0 3], #[]⟩], finalPoly, 0⟩
    let expected : Array Fri.QueryRound := #[⟨15, row0⟩, ⟨3, row1⟩]
    let run (proof : FriProof) (reduced : Array Fri.ReducedOpening) := Fri.foldQuery {} challenges proof 0 reduced
    let wrongOrder := { proof with commitOpenings := proof.commitOpenings.modify 1 fun opening =>
      { opening with siblings := opening.siblings.map Array.reverse } }
    let postRollInRows : Array (Array Fri.QueryRound) := #[expected.modify 0 fun row =>
      { row with values := row.values.set! 1 carried }]
    let finalState : Fri.FoldState := ⟨3, 2, 3, finalValue⟩
    let smallerGenerator ← (Arithmetic.twoAdicGenerator 2).mapError Fri.Error.arithmetic
    let smallerPoint := Arithmetic.embed (smallerGenerator.pow 3)
    let mismatchedPoint := Arithmetic.embed (globalGenerator.pow 3)
    let leaf0 := Mmcs.hashRow (Fri.flattenRow row0.toList).toArray
    let leaf1 := Mmcs.hashRow (Fri.flattenRow row1.toList).toArray
    -- Leaf-level caps give an independent commitment fixture: the selected
    -- slots are 15 and 3, with no frontier or parent-hash construction.
    let authProof := { proof with commits := #[Array.replicate 16 leaf0, Array.replicate 4 leaf1] }
    let params : Parameters := {
      logBlowup := 1, logFinalPolyLen := 1, capHeight := 4,
      maxLogArity := 2, numQueries := 1, commitPowBits := 0, queryPowBits := 0 }
    let mutatedRows := #[expected.modify 1 fun row =>
      { row with values := row.values.modify 0 fun value => value.add (e 1) }]
    return [
      ("nonzero binary/quaternary query chain saves pre-roll-in rows", okEquals (run proof reduced) expected),
      (s!"nonzero query chain authenticates each flattened row ({repr (Fri.authenticateCommits params challenges authProof #[expected])})",
        (Fri.authenticateCommits params challenges authProof #[expected]).isOk),
      ("commit authentication rejects a changed saved coordinate", !(Fri.authenticateCommits params challenges authProof mutatedRows).isOk),
      ("commit authentication does not accept post-roll-in row substitution", !(Fri.authenticateCommits params challenges authProof postRollInRows).isOk),
      ("commit row lookup rejects a truncated saved query", !(Fri.authenticateCommits params challenges authProof #[expected.pop]).isOk),
      ("commit authentication rejects a missing query", !(Fri.authenticateCommits params challenges authProof #[]).isOk),
      ("nonzero sibling order affects the final polynomial equation", !(run wrongOrder reduced).isOk),
      ("nonzero roll-in values affect the final polynomial equation", !(run proof (reduced.modify 1 fun row =>
        { row with value := e 8 })).isOk),
      ("roll-in cannot skip an earlier wrong-height reduction", !(run proof #[⟨5, first⟩, ⟨3, e 7⟩, ⟨2, ⟨17, 19⟩⟩]).isOk),
      ("duplicate roll-in height remains unconsumed", !(run proof #[⟨5, first⟩, ⟨4, e 7⟩, ⟨4, e 0⟩, ⟨2, ⟨17, 19⟩⟩]).isOk),
      ("query chain requires the exact final height", !(Fri.foldQuery {} { challenges with logFinal := 1 } proof 0 reduced).isOk),
      ("query chain requires every beta", !(Fri.foldQuery {} { challenges with betas := #[beta0] } proof 0 reduced).isOk),
      ("query chain requires the verifier's original query", !(Fri.foldQuery {} challenges proof 1 reduced).isOk),
      ("final nonconstant equation pairs the subgroup and bit width", (Fri.finishQuery challenges proof 0 reduced finalState).isOk &&
        smallerPoint == finalPoint && Fri.polynomial finalPoly mismatchedPoint != finalValue),
      ("final equation independently checks reduction consumption", !(Fri.finishQuery challenges proof 0 reduced
        { finalState with nextReduced := 2 }).isOk),
      ("commit collection preserves saved index and exact extension layout", okEquals
        (Fri.commitRows 1 [expected]) ([3], #[((row1.toList.flatMap fun value => [value.c0, value.c1]).toArray)] :: []))
    ]
  return insertion ++ match vector with
    | .ok checks => checks
    | .error error => [(s!"construct nonzero FRI query-chain vector ({repr error})", false)]

private def checks : IO (List Check) := do
  let coefficients := #[e 3, ⟨5, 7⟩, e 11, ⟨13, 17⟩]
  let beta : Ext := ⟨19, 23⟩
  let interpolates : Bool := match Fri.rowPoints 3 4 2 with
    | .error _ => false
    | .ok points =>
      let evaluations := points.map fun x => Fri.polynomial coefficients (Arithmetic.embed x)
      okEquals (Fri.foldRow {} 3 4 2 beta evaluations) (Fri.polynomial coefficients beta) &&
        (Array.range 4).all fun i => match points[i]?, evaluations[i]? with
          | some x, some y => okEquals (Fri.foldRow {} 3 4 2 (Arithmetic.embed x) evaluations) y
          | _, _ => false
  let arithmeticChecks : List Check := [
    ("exact low-bit reversal golden values", Fri.reverseBits 1 4 == 8 &&
      Fri.reverseBits 6 3 == 3 && Fri.reverseBits 31 3 == 7 && Fri.reverseBits 13 0 == 0),
    ("bit reversal is involutive within its width", (List.range 8).all fun bits =>
      (List.range (2 ^ bits)).all fun index => Fri.reverseBits (Fri.reverseBits index bits) bits == index),
    ("polynomial coefficients are constant-first", Fri.polynomial #[e 2, e 3, e 5] (e 7) == e 268),
    ("empty polynomial is zero", Fri.polynomial #[] beta == e 0),
    ("binary row point order is plus then minus", okEquals (Fri.rowPoints 0 1 1) #[1, (1 : Field).neg]),
    ("binary fold golden value", okEquals (Fri.foldRow {} 0 1 1 (e 3) #[e 8, e 4]) (e 12)),
    ("variable-arity fold and challenge-on-domain interpolation", interpolates),
    ("duplicate interpolation points rejected", !(Fri.interpolate #[1, 1] #[e 3, e 3] beta).isOk),
    ("empty interpolation rejected", !(Fri.interpolate #[] #[] beta).isOk),
    ("wrong interpolation width rejected", !(Fri.interpolate #[1, 2] #[e 3] beta).isOk),
    ("fold row width is exact", !(Fri.foldRow {} 0 1 1 beta #[e 3]).isOk),
    ("fold arity admission precedes allocation", !(Fri.foldRow {} 0 0 32 beta #[]).isOk),
    ("unsupported field domain rejected", !(Fri.foldRow {} 0 32 1 beta #[e 0, e 0]).isOk),
    ("fold index is range checked", !(Fri.foldRow {} 2 1 1 beta #[e 0, e 0]).isOk),
    ("input coset includes native generator seven", okEquals (Fri.queryPoint 0 4 3) (e 7)),
    ("input query projects before bit reversal", match Arithmetic.twoAdicGenerator 3 with
      | .ok generator => okEquals (Fri.queryPoint 6 4 3) ((Arithmetic.embed (generator.pow 6)).mul (e 7))
      | .error _ => false),
    ("input matrix cannot exceed global domain", !(Fri.queryPoint 0 3 4).isOk),
    ("query index cannot exceed domain", !(Fri.queryPoint 16 4 3).isOk)
  ]
  let forced : Transcript.Challenger := {
    input := #[99], output := (#[17, 42].flatMap (Codec.Wire.littleEndian 8)).reverse }
  let transcriptChecks : List Check := [
    ("zero queries leave the challenger untouched", okEquals
      ((Fri.queryIndices 64 0).run forced) ([], forced)),
    ("raw query draw sequence preserves order and exact count", match (Fri.queryIndices 4 2).run forced with
      | .ok (indices, final) => indices == [1, 10] && final.input == #[99] && final.output.isEmpty
      | .error _ => false),
    ("nonempty query sequence checks bit width", !((Fri.queryIndices 64 1).run forced).isOk),
    ("empty commitment phase is inert", okEquals ((Fri.commitPhase {} 64 [] []).run forced) ([], forced)),
    ("extra commitment witness cannot be ignored", !((Fri.commitPhase {} 0 [] [0]).run forced).isOk),
    ("missing commitment witness cannot be defaulted", !((Fri.commitPhase {} 0 [#[]] []).run forced).isOk)
  ]
  let vectorChecks : List Check := match fixture with
    | .error error => [(s!"construct full FRI fixture ({repr error})", false)]
    | .ok f =>
      let check (proof : FriProof) := Fri.check {} f.params f.rounds proof f.state
      let accepted := check f.proof
      let altered (change : CommitPhaseStep → CommitPhaseStep) : FriProof :=
        { f.proof with commitOpenings := f.proof.commitOpenings.modify 0 change }
      let rows : Array Fri.ReducedOpening := #[⟨2, e 0⟩]
      let chain := Fri.foldQuery {} f.challenges f.proof 0 rows
      let constantBad := f.rounds.map fun round => { round with
        matrices := round.matrices.map fun matrix => { matrix with
          points := matrix.points.map fun opening => { opening with values := #[e 8] } } }
      [
        (s!"complete synthetic MMCS/FRI proof ({repr (accepted.map (fun _ => ()))})", accepted.isOk),
        ("all query indices are derived and bounded", f.challenges.indices.size == 2 && f.challenges.indices.all (· < 4)),
        ("zero-query instance rejected", !(Fri.check {} { f.params with numQueries := 0 } f.rounds f.proof f.state).isOk),
        ("explicit query resource bound enforced", !(Fri.check { queries := 1 } f.params f.rounds f.proof f.state).isOk),
        ("explicit commitment sampling bound enforced", !(Fri.replay
          { transcript := { sampleAttempts := 0 } } f.params f.rounds f.proof f.state).isOk),
        ("explicit FRI observation bound enforced", !(Fri.replay
          { transcript := { observationBytes := 1 } } f.params f.rounds f.proof f.state).isOk),
        ("commitment grinding bit bound enforced", !(Fri.replay {}
          { f.params with commitPowBits := 64 } f.rounds f.proof f.state).isOk),
        ("query grinding bit bound enforced", !(Fri.replay {}
          { f.params with queryPowBits := 64 } f.rounds f.proof f.state).isOk),
        ("commitment/opening counts must agree", !(check { f.proof with commits := #[] }).isOk),
        ("commitment/PoW counts must agree", !(check { f.proof with commitPow := #[] }).isOk),
        ("input batch counts must agree", !(check { f.proof with inputOpenings := #[] }).isOk),
        ("every round opens every query", !(check (altered fun opening => { opening with siblings := opening.siblings.pop })).isOk),
        ("every query has arity-minus-one siblings", !(check (altered fun opening =>
          { opening with siblings := opening.siblings.map Array.pop })).isOk),
        ("zero arity rejected", !(check (altered fun opening => { opening with logArity := 0 })).isOk),
        ("unapproved arity rejected", !(check (altered fun opening => { opening with logArity := 2 })).isOk),
        ("global height cross-checked against inputs", !(Fri.check {} f.params
          (f.rounds.map fun round => { round with matrices := round.matrices.map fun matrix =>
            { matrix with logDegree := 2 } }) f.proof f.state).isOk),
        ("final polynomial length is exact", !(check { f.proof with finalPoly := #[] }).isOk),
        ("extra final coefficient rejected", !(check { f.proof with finalPoly := #[e 0, e 0] }).isOk),
        ("matrix opened at no points rejected", !(Fri.check {} f.params
          (f.rounds.map fun round => { round with matrices := round.matrices.map fun matrix =>
            { matrix with points := #[] } }) f.proof f.state).isOk),
        ("opened-point widths checked independently of proof row", !(Fri.check {} f.params
          (f.rounds.map fun round => { round with matrices := round.matrices.map fun matrix =>
            { matrix with width := 2 } }) f.proof f.state).isOk),
        ("query-chain arithmetic returns every committed row", match chain with
          | .ok rows => rows.size == 1 | .error _ => false),
        ("missing initial reduced opening rejected", !(Fri.foldQuery {} f.challenges f.proof 0 #[]).isOk),
        ("wrong initial reduced height rejected", !(Fri.foldQuery {} f.challenges f.proof 0 #[⟨1, e 0⟩]).isOk),
        ("unconsumed reduced opening rejected", !(Fri.foldQuery {} f.challenges f.proof 0
          #[⟨2, e 0⟩, ⟨0, e 0⟩]).isOk),
        ("roll-in at the folded height is consumed", (Fri.foldQuery {} f.challenges f.proof 0
          #[⟨2, e 0⟩, ⟨1, e 0⟩]).isOk),
        ("roll-in changes the authenticated final equation", !(Fri.foldQuery {} f.challenges f.proof 0
          #[⟨2, e 0⟩, ⟨1, e 1⟩]).isOk),
        ("final folded value is checked", !(Fri.foldQuery {} f.challenges
          { f.proof with finalPoly := #[e 1] } 0 rows).isOk),
        ("input point/value mismatch is not ignored", match
            Fri.openInputs f.params f.challenges constantBad f.proof.inputOpenings with
          | .error _ => true
          | .ok reduced => match reduced[0]? with
            | some values => !(Fri.foldQuery {} f.challenges f.proof 0 values).isOk
            | none => false)
      ]
  return arithmeticChecks ++ transcriptChecks ++ (← reductionChecks) ++ (← queryChainChecks) ++ vectorChecks

public def suite : IO UInt32 := runChecks "stage2-fri" checks

end Tests.MultiStark.Verify.Fri
