module
public import Ix.MultiStark.Verify.Protocol.FriCheck
public import Ix.MultiStark.Verify.Proofs.FriInputs
public import Ix.MultiStark.Verify.Proofs.FriTranscript

public section

namespace MultiStark.Verify.Proofs

theorem insertValue_refines (value : Ext) (position : Nat) (siblings result : List Ext) :
    Fri.insertValue value position siblings = .ok result ↔ Protocol.RowInsertion value position siblings result := by
  induction position generalizing siblings result with
  | zero => simp [Fri.insertValue, Protocol.RowInsertion]
  | succ position ih =>
    cases siblings with
    | nil => simp [Fri.insertValue, Protocol.RowInsertion]
    | cons sibling siblings =>
      simp only [Fri.insertValue, bind_ok_iff, pure_ok_iff, ih, Protocol.RowInsertion,
        List.length_cons, Nat.succ_le_succ_iff, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      constructor
      · rintro ⟨rest, ⟨bound, rfl⟩, rfl⟩
        exact ⟨bound, rfl⟩
      · rintro ⟨bound, rfl⟩
        exact ⟨_, ⟨bound, rfl⟩, rfl⟩

theorem rollIn_refines (beta : Ext) (logArity : Nat) (reduced : Array Fri.ReducedOpening)
    (before after : Fri.FoldState) :
    Fri.rollIn beta logArity reduced before = after ↔ Protocol.RolledIn beta logArity reduced before after := by
  unfold Fri.rollIn Protocol.RolledIn
  cases reduced[before.nextReduced]? with
  | none => rfl
  | some next => by_cases same : next.logHeight = before.height <;> simp [same]

theorem foldRound_refines (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array Fri.ReducedOpening) (round : Nat)
    (before after : Fri.FoldState) (saved : Fri.QueryRound) :
    Fri.foldRound limits challenges proof query reduced round before = .ok (after, saved) ↔
      Protocol.QueryFoldRound limits challenges proof query reduced round before after saved := by
  simp only [Fri.foldRound, bind_ok_iff, unit_exists_iff, ensure_ok_iff, fri_getAt_refines,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, insertValue_refines, foldRow_refines,
    pure_ok_iff, Prod.mk.injEq, rollIn_refines, Protocol.QueryFoldRound, exists_and_left, and_assoc]

theorem foldRounds_refines (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array Fri.ReducedOpening) (round remaining : Nat)
    (before after : Fri.FoldState) (rows : List Fri.QueryRound) :
    Fri.foldRounds limits challenges proof query reduced round remaining before = .ok (after, rows) ↔
      Protocol.QueryFoldRounds limits challenges proof query reduced round remaining before after rows := by
  induction remaining generalizing round before after rows with
  | zero => cases rows <;> simp [Fri.foldRounds, Protocol.QueryFoldRounds]
  | succ remaining ih =>
    cases rows with
    | nil =>
      simp [Fri.foldRounds, bind_ok_iff, map_ok_iff, Protocol.QueryFoldRounds]
    | cons row rows =>
      simp only [Fri.foldRounds, bind_ok_iff, Prod.exists, foldRound_refines, ih, pure_ok_iff,
        Prod.mk.injEq, List.cons.injEq, Protocol.QueryFoldRounds]
      constructor
      · rintro ⟨middle, first, folded, final, rest, tail, same, rfl, rfl⟩
        cases same
        exact ⟨middle, folded, tail⟩
      · rintro ⟨middle, folded, tail⟩
        exact ⟨middle, row, folded, after, rows, tail, rfl, rfl, rfl⟩

theorem finishQuery_refines (challenges : Fri.Challenges) (proof : FriProof) (query : Nat)
    (reduced : Array Fri.ReducedOpening) (state : Fri.FoldState) :
    Fri.finishQuery challenges proof query reduced state = .ok () ↔
      Protocol.FinalPolynomial challenges proof reduced state := by
  simp only [Fri.finishQuery, bind_ok_iff, unit_exists_iff, ensure_ok_iff, beq_iff_eq,
    extension_beq_iff_eq, mapError_ok_iff, twoAdicGenerator_refines, reverseBits_refines,
    fri_polynomial_refines, Protocol.FinalPolynomial]

theorem initialOpening_refines (reduced : Array Fri.ReducedOpening) (first : Fri.ReducedOpening) :
    Fri.initialOpening reduced = .ok first ↔ reduced[0]? = some first := by
  unfold Fri.initialOpening
  cases reduced[0]? <;> simp

theorem foldQuery_refines (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (query : Nat) (reduced : Array Fri.ReducedOpening) (rows : Array Fri.QueryRound) :
    Fri.foldQuery limits challenges proof query reduced = .ok rows ↔
      Protocol.QueryFold limits challenges proof query reduced rows := by
  simp only [Fri.foldQuery, bind_ok_iff, unit_exists_iff, ensure_ok_iff, initialOpening_refines,
    beq_iff_eq, Bool.and_eq_true, fri_getAt_refines, Prod.exists, foldRounds_refines,
    finishQuery_refines, pure_ok_iff, Protocol.QueryFold]
  constructor
  · rintro ⟨first, initial, height, counts, index, hi, final, saved, folded, finished, same⟩
    cases same
    exact ⟨first, initial, height, counts, index, final, hi, by simpa using folded, finished⟩
  · rintro ⟨first, initial, height, counts, index, final, hi, folded, finished⟩
    exact ⟨first, initial, height, counts, index, hi, final, rows.toList, folded, finished, by simp⟩

theorem flattenRow_refines (values : List Ext) : Fri.flattenRow values = Protocol.FlatRow values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [Fri.flattenRow, Protocol.FlatRow, ih]

theorem commitRows_refines (round : Nat) (queries : List (Array Fri.QueryRound))
    (indices : List Nat) (rows : List (Array (Array Field))) :
    Fri.commitRows round queries = .ok (indices, rows) ↔ Protocol.CommitRows round queries indices rows := by
  induction queries generalizing indices rows with
  | nil => cases indices <;> cases rows <;> simp [Fri.commitRows, Protocol.CommitRows]
  | cons query queries ih =>
    cases indices <;> cases rows <;>
      simp [Fri.commitRows, bind_ok_iff, map_ok_iff, Prod.exists, fri_getAt_refines,
        flattenRow_refines, ih, Protocol.CommitRows, and_assoc]
    constructor
    · rintro ⟨saved, lookup, indices, rows, rest, hi, rfl, hr, rfl⟩
      exact ⟨saved, lookup, hi, hr, rest⟩
    · rintro ⟨saved, lookup, hi, hr, rest⟩
      exact ⟨saved, lookup, _, _, rest, hi, rfl, hr, rfl⟩

theorem authenticateCommitRounds_refines (params : Parameters) (proof : FriProof)
    (queries : Array (Array Fri.QueryRound)) (arities : List Nat) (round height : Nat) :
    Fri.authenticateCommitRounds params proof queries arities round height = .ok () ↔
      Protocol.CommitAuthentication params proof queries arities round height := by
  induction arities generalizing round height with
  | nil => simp [Fri.authenticateCommitRounds, Protocol.CommitAuthentication]
  | cons logArity arities ih =>
    simp only [Fri.authenticateCommitRounds, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      decide_eq_true_eq, Prod.exists, commitRows_refines, fri_getAt_refines,
      mapError_ok_iff, mmcs_check_refines, ih, Protocol.CommitAuthentication, exists_and_left]

theorem authenticateCommits_refines (params : Parameters) (challenges : Fri.Challenges) (proof : FriProof)
    (queries : Array (Array Fri.QueryRound)) :
    Fri.authenticateCommits params challenges proof queries = .ok () ↔
      Protocol.CommitsAuthenticated params challenges proof queries := by
  simp only [Fri.authenticateCommits, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    Bool.and_eq_true, beq_iff_eq, authenticateCommitRounds_refines, Protocol.CommitsAuthenticated]

theorem foldQueries_refines (limits : Fri.Limits) (challenges : Fri.Challenges) (proof : FriProof)
    (reduced : Array (Array Fri.ReducedOpening)) (query remaining : Nat) (rows : List (Array Fri.QueryRound)) :
    Fri.foldQueries limits challenges proof reduced query remaining = .ok rows ↔
      Protocol.QueryFolds limits challenges proof reduced query remaining rows := by
  induction remaining generalizing query rows with
  | zero => cases rows <;> simp [Fri.foldQueries, Protocol.QueryFolds]
  | succ remaining ih =>
    cases rows <;>
      simp [Fri.foldQueries, bind_ok_iff, map_ok_iff, fri_getAt_refines, foldQuery_refines,
        ih, Protocol.QueryFolds]

theorem fri_check_refines (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state final : Transcript.Challenger) (challenges : Fri.Challenges) :
    Fri.check limits params rounds proof state = .ok (challenges, final) ↔
      Protocol.FriAccepted limits params rounds proof state challenges final := by
  simp only [Fri.check, bind_ok_iff, unit_exists_iff, Prod.exists, fri_replay_refines,
    openInputs_refines, foldQueries_refines, authenticateCommits_refines, pure_ok_iff,
    Prod.mk.injEq, Protocol.FriAccepted]
  constructor
  · rintro ⟨derived, next, replay, reduced, inputs, queries, folds, commits, rfl, rfl⟩
    exact ⟨replay, reduced, queries, inputs, folds, commits⟩
  · rintro ⟨replay, reduced, queries, inputs, folds, commits⟩
    exact ⟨challenges, final, replay, reduced, inputs, queries, folds, commits, rfl, rfl⟩

end MultiStark.Verify.Proofs
