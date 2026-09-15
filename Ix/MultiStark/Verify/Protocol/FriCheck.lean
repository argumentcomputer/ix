module
public import Ix.MultiStark.Verify.Fri.Check
public import Ix.MultiStark.Verify.Protocol.FriTranscript
public import Ix.MultiStark.Verify.Protocol.FriInputs

/-! Independent equations for the complete deterministic FRI phase. The
carried evaluation is inserted at the verifier's query position; every
authenticated row is saved before roll-in. All reductions must be consumed,
and the terminal value equals the final polynomial at the native global
subgroup point. This relation asserts neither low-degree soundness nor
cryptographic binding of the transcript and Merkle primitives. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def RowInsertion (value : Ext) (position : Nat) (siblings result : List Ext) : Prop :=
  position ≤ siblings.length ∧ siblings.take position ++ value :: siblings.drop position = result

def RolledIn (beta : Ext) (logArity : Nat) (reduced : Array Fri.ReducedOpening)
    (before after : Fri.FoldState) : Prop :=
  match reduced[before.nextReduced]? with
  | none => before = after
  | some next =>
    if next.logHeight = before.height then
      (⟨before.index, before.height, before.nextReduced + 1,
        before.value.add ((Arithmetic.pow2 beta logArity).mul next.value)⟩ : Fri.FoldState) = after
    else before = after

def QueryFoldRound (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array Fri.ReducedOpening) (round : Nat)
    (before after : Fri.FoldState) (saved : Fri.QueryRound) : Prop :=
  ∃ beta logArity, challenges.betas[round]? = some beta ∧ challenges.arities[round]? = some logArity ∧
    (1 ≤ logArity ∧ logArity ≤ before.height) ∧ 2 ^ logArity ≤ limits.foldArity ∧
    ∃ opening siblings, proof.commitOpenings[round]? = some opening ∧ opening.siblings[query]? = some siblings ∧
      siblings.size = 2 ^ logArity - 1 ∧
      ∃ fullRow value, RowInsertion before.value (before.index % 2 ^ logArity) siblings.toList fullRow ∧
        RowFold limits (before.index / 2 ^ logArity) (before.height - logArity) logArity beta fullRow.toArray value ∧
        RolledIn beta logArity reduced
          ⟨before.index / 2 ^ logArity, before.height - logArity, before.nextReduced, value⟩ after ∧
        (⟨before.index / 2 ^ logArity, fullRow.toArray⟩ : Fri.QueryRound) = saved

def QueryFoldRounds (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array Fri.ReducedOpening) :
    Nat → Nat → Fri.FoldState → Fri.FoldState → List Fri.QueryRound → Prop
  | _, 0, before, after, [] => before = after
  | round, remaining + 1, before, after, row :: rows =>
    ∃ middle, QueryFoldRound limits challenges proof query reduced round before middle row ∧
      QueryFoldRounds limits challenges proof query reduced (round + 1) remaining middle after rows
  | _, _, _, _, _ => False

def FinalPolynomial (challenges : Fri.Challenges) (proof : FriProof)
    (reduced : Array Fri.ReducedOpening) (state : Fri.FoldState) : Prop :=
  state.height = challenges.logFinal ∧ state.nextReduced = reduced.size ∧
    ∃ generator, TwoAdicGenerator challenges.logGlobal generator ∧
      PolynomialValue proof.finalPoly.toList
        (Arithmetic.embed (generator.pow (bitReverse state.index challenges.logGlobal))) = state.value

def QueryFold (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array Fri.ReducedOpening) (rows : Array Fri.QueryRound) : Prop :=
  ∃ first, reduced[0]? = some first ∧ first.logHeight = challenges.logGlobal ∧
    (challenges.betas.size = challenges.arities.size ∧ challenges.betas.size = proof.commitOpenings.size) ∧
    ∃ index final, challenges.indices[query]? = some index ∧
      QueryFoldRounds limits challenges proof query reduced 0 challenges.arities.size
        ⟨index, challenges.logGlobal, 1, first.value⟩ final rows.toList ∧
      FinalPolynomial challenges proof reduced final

/-- Each extension value is committed in c0,c1 order; there is one matrix
per FRI commit and one complete saved row per query, in original query order. -/
def FlatRow (values : List Ext) : List Field :=
  values.flatMap (fun value => [value.c0, value.c1])

def CommitRows (round : Nat) :
    List (Array Fri.QueryRound) → List Nat → List (Array (Array Field)) → Prop
  | [], [], [] => True
  | query :: queries, index :: indices, row :: rows =>
    ∃ saved, query[round]? = some saved ∧ saved.index = index ∧
      #[(FlatRow saved.values.toList).toArray] = row ∧ CommitRows round queries indices rows
  | _, _, _ => False

def CommitAuthentication (params : Parameters) (proof : FriProof)
    (queries : Array (Array Fri.QueryRound)) : List Nat → Nat → Nat → Prop
  | [], _, _ => True
  | logArity :: arities, round, height =>
    logArity ≤ height ∧
      ∃ indices rows, CommitRows round queries.toList indices rows ∧
        ∃ opening commitment, proof.commitOpenings[round]? = some opening ∧ proof.commits[round]? = some commitment ∧
          MmcsAccepted params.capHeight #[⟨height - logArity, 2 * 2 ^ logArity⟩] commitment indices.toArray
            ⟨rows.toArray, opening.frontier⟩ ∧
          CommitAuthentication params proof queries arities (round + 1) (height - logArity)

def CommitsAuthenticated (params : Parameters) (challenges : Fri.Challenges) (proof : FriProof)
    (queries : Array (Array Fri.QueryRound)) : Prop :=
  (queries.size = challenges.indices.size ∧ proof.commits.size = challenges.arities.size) ∧
    CommitAuthentication params proof queries challenges.arities.toList 0 challenges.logGlobal

def QueryFolds (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (reduced : Array (Array Fri.ReducedOpening)) : Nat → Nat → List (Array Fri.QueryRound) → Prop
  | _, 0, [] => True
  | query, remaining + 1, rows :: rest =>
    ∃ opening, reduced[query]? = some opening ∧ QueryFold limits challenges proof query opening rows ∧
      QueryFolds limits challenges proof reduced (query + 1) remaining rest
  | _, _, _ => False

def FriAccepted (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state : Transcript.Challenger)
    (challenges : Fri.Challenges) (final : Transcript.Challenger) : Prop :=
  FriTranscript limits params rounds proof state challenges final ∧
    ∃ reduced queries, InputsOpened params challenges rounds proof.inputOpenings reduced ∧
      QueryFolds limits challenges proof reduced 0 challenges.indices.size queries ∧
      CommitsAuthenticated params challenges proof queries.toArray

end MultiStark.Verify.Protocol
