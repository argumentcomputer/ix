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
  return arithmeticChecks ++ transcriptChecks ++ vectorChecks

public def suite : IO UInt32 := runChecks "stage2-fri" checks

end Tests.MultiStark.Verify.Fri
