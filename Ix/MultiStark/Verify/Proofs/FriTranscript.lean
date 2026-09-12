module
public import Ix.MultiStark.Verify.Protocol.FriTranscript
public import Ix.MultiStark.Verify.Proofs.Replay

public section

namespace MultiStark.Verify.Proofs

open Transcript (Challenger)

theorem observePointList_refines (limits : Transcript.Limits) (points : List Pcs.PointOpening)
    (state final : Challenger) :
    ((Pcs.observePointList limits points).run state = .ok ((), final)) ↔
      Protocol.PointsObserved limits points state final := by
  induction points generalizing state with
  | nil => simp only [Pcs.observePointList, action_pure_ok_iff, Protocol.PointsObserved, true_and]
  | cons point rest ih =>
    simp only [Pcs.observePointList, action_bind_ok_iff, unit_exists_iff,
      observeExts_refines, ih, Protocol.PointsObserved]

theorem observeMatrixList_refines (limits : Transcript.Limits) (matrices : List Pcs.Matrix)
    (state final : Challenger) :
    ((Pcs.observeMatrixList limits matrices).run state = .ok ((), final)) ↔
      Protocol.MatricesObserved limits matrices state final := by
  induction matrices generalizing state with
  | nil => simp only [Pcs.observeMatrixList, action_pure_ok_iff, Protocol.MatricesObserved, true_and]
  | cons matrix rest ih =>
    simp only [Pcs.observeMatrixList, action_bind_ok_iff, unit_exists_iff,
      observePointList_refines, ih, Protocol.MatricesObserved]

theorem observeRoundList_refines (limits : Transcript.Limits) (rounds : List Pcs.Round)
    (state final : Challenger) :
    ((Pcs.observeRoundList limits rounds).run state = .ok ((), final)) ↔
      Protocol.RoundsObserved limits rounds state final := by
  induction rounds generalizing state with
  | nil => simp only [Pcs.observeRoundList, action_pure_ok_iff, Protocol.RoundsObserved, true_and]
  | cons round rest ih =>
    simp only [Pcs.observeRoundList, action_bind_ok_iff, unit_exists_iff,
      observeMatrixList_refines, ih, Protocol.RoundsObserved]

theorem observeOpenings_refines (limits : Transcript.Limits) (rounds : Array Pcs.Round)
    (state final : Challenger) :
    ((Pcs.observeOpenings limits rounds).run state = .ok ((), final)) ↔
      Protocol.RoundsObserved limits rounds.toList state final :=
  observeRoundList_refines limits _ state final

theorem fri_shape_refines (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (result : Array Nat × Nat × Nat) :
    Fri.shape limits params rounds proof = .ok result ↔ Protocol.FriShape limits params rounds proof result := by
  simp only [Fri.shape, bind_ok_iff, unit_exists_iff, ensure_ok_iff, pure_ok_iff,
    Protocol.FriShape, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Array.all_eq_true', Bool.not_eq_true', Array.isEmpty_eq_false_iff, and_assoc]

theorem commitPhase_refines (limits : Transcript.Limits) (bits : Nat)
    (caps : List MerkleCap) (witnesses : List Field) (state final : Challenger) (betas : List Ext) :
    ((Fri.commitPhase limits bits caps witnesses).run state = .ok (betas, final)) ↔
      Protocol.CommitChallenges limits bits caps witnesses state betas final := by
  induction caps generalizing witnesses state betas final with
  | nil =>
    cases witnesses <;> cases betas <;>
      simp only [Fri.commitPhase, Protocol.CommitChallenges, action_pure_ok_iff,
        action_throw_ok_iff, List.nil_eq, List.cons_ne_nil, true_and, false_and]
  | cons cap caps ih =>
    cases witnesses with
    | nil =>
      simp only [Fri.commitPhase, action_throw_ok_iff, Protocol.CommitChallenges]
    | cons witness witnesses =>
      simp only [Fri.commitPhase, action_bind_ok_iff, action_pure_ok_iff, unit_exists_iff,
        observeCap_refines, checkWitness_refines, sampleExt_refines, ih]
      cases betas with
      | nil => simp only [Protocol.CommitChallenges, List.cons_ne_nil, false_and, and_false, exists_false]
      | cons beta betas =>
        simp only [List.cons.injEq, and_assoc, Protocol.CommitChallenges]
        constructor
        · rintro ⟨s0, h0, s1, h1, b, s2, h2, bs, s3, h3, rfl, rfl, rfl⟩
          exact ⟨s0, s1, s2, h0, h1, h2, h3⟩
        · rintro ⟨s0, s1, s2, h0, h1, h2, h3⟩
          exact ⟨s0, h0, s1, h1, beta, s2, h2, betas, final, h3, rfl, rfl, rfl⟩

theorem queryIndices_refines (bits count : Nat) (state final : Challenger) (indices : List Nat) :
    ((Fri.queryIndices bits count).run state = .ok (indices, final)) ↔
      Protocol.QueryDraws bits count state indices final := by
  induction count generalizing state indices final with
  | zero =>
    cases indices <;> simp only [Fri.queryIndices, action_pure_ok_iff, Protocol.QueryDraws,
      List.nil_eq, List.cons_ne_nil, true_and, false_and]
  | succ count ih =>
    simp only [Fri.queryIndices, action_bind_ok_iff, action_pure_ok_iff, sampleBits_refines, ih]
    cases indices with
    | nil => simp only [Protocol.QueryDraws, List.cons_ne_nil, false_and, and_false, exists_false]
    | cons index rest =>
      simp only [List.cons.injEq, and_assoc, Protocol.QueryDraws]
      constructor
      · rintro ⟨i, middle, drawn, is, last, remaining, rfl, rfl, rfl⟩
        exact ⟨middle, drawn, remaining⟩
      · rintro ⟨middle, drawn, remaining⟩
        exact ⟨index, middle, drawn, rest, final, remaining, rfl, rfl, rfl⟩

theorem fri_replayAction_refines (limits : Transcript.Limits) (params : Parameters) (proof : FriProof)
    (arities : Array Nat) (logGlobal : Nat) (state final : Challenger)
    (alpha : Ext) (betas : List Ext) (indices : List Nat) :
    ((Fri.replayAction limits params proof arities logGlobal).run state = .ok ((alpha, betas, indices), final)) ↔
      Protocol.FriTranscriptAction limits params proof arities logGlobal state alpha betas indices final := by
  simp only [Fri.replayAction, action_bind_ok_iff, action_pure_ok_iff, unit_exists_iff,
    sampleExt_refines, commitPhase_refines, observeExts_refines, observeNats_refines,
    checkWitness_refines, queryIndices_refines, Prod.mk.injEq, and_assoc, Protocol.FriTranscriptAction]
  constructor
  · rintro ⟨a, s0, h0, bs, s1, h1, s2, h2, s3, h3, s4, h4, is, s5, h5, rfl, rfl, rfl, rfl⟩
    exact ⟨s0, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5⟩
  · rintro ⟨s0, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5⟩
    exact ⟨alpha, s0, h0, betas, s1, h1, s2, h2, s3, h3, s4, h4,
      indices, final, h5, rfl, rfl, rfl, rfl⟩

theorem fri_replay_refines (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state final : Challenger) (challenges : Fri.Challenges) :
    Fri.replay limits params rounds proof state = .ok (challenges, final) ↔
      Protocol.FriTranscript limits params rounds proof state challenges final := by
  cases challenges with
  | mk alpha betas indices arities logGlobal logFinal =>
    simp only [Fri.replay, bind_ok_iff, pure_ok_iff, mapError_ok_iff, Prod.exists,
      fri_shape_refines, fri_replayAction_refines, Protocol.FriTranscript,
      Prod.mk.injEq, Fri.Challenges.mk.injEq, and_assoc]
    constructor
    · rintro ⟨ars, lg, lf, shape, a, bs, is, next, replay,
        rfl, hb, hi, rfl, rfl, rfl, rfl⟩
      cases hb
      cases hi
      exact ⟨shape, by simpa using replay⟩
    · rintro ⟨shape, replay⟩
      exact ⟨arities, logGlobal, logFinal, shape, alpha, betas.toList, indices.toList, final, replay,
        rfl, by simp, by simp, rfl, rfl, rfl, rfl⟩

theorem queryDraws_length (bits count : Nat) (state final : Challenger) (indices : List Nat)
    (derived : Protocol.QueryDraws bits count state indices final) : indices.length = count := by
  induction count generalizing state indices final with
  | zero => cases indices <;> simp_all [Protocol.QueryDraws]
  | succ count ih =>
    cases indices with
    | nil => simp [Protocol.QueryDraws] at derived
    | cons index rest =>
      obtain ⟨middle, _, remaining⟩ := derived
      simp only [List.length_cons, ih middle final rest remaining]

theorem queryDraws_bounded (bits count : Nat) (state final : Challenger) (indices : List Nat)
    (derived : Protocol.QueryDraws bits count state indices final) :
    ∀ index ∈ indices, index < 2 ^ bits := by
  induction count generalizing state indices final with
  | zero => cases indices <;> simp_all [Protocol.QueryDraws]
  | succ count ih =>
    cases indices with
    | nil => simp [Protocol.QueryDraws] at derived
    | cons first rest =>
      obtain ⟨middle, drawn, remaining⟩ := derived
      intro index member
      cases List.mem_cons.mp member with
      | inl equal =>
        subst index
        rw [← drawn.2.1]
        exact Nat.mod_lt _ (Nat.two_pow_pos bits)
      | inr member => exact ih middle final rest remaining index member

theorem fri_replay_query_count (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state final : Challenger) (challenges : Fri.Challenges)
    (accepted : Fri.replay limits params rounds proof state = .ok (challenges, final)) :
    challenges.indices.size = params.numQueries := by
  obtain ⟨_, action⟩ := (fri_replay_refines limits params rounds proof state final challenges).mp accepted
  obtain ⟨_, _, _, _, powState, _, _, _, _, _, queries⟩ := action
  simpa only [Array.length_toList] using
    queryDraws_length challenges.logGlobal params.numQueries powState final challenges.indices.toList queries

theorem fri_replay_query_bounds (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state final : Challenger) (challenges : Fri.Challenges)
    (accepted : Fri.replay limits params rounds proof state = .ok (challenges, final)) :
    ∀ index ∈ challenges.indices, index < 2 ^ challenges.logGlobal := by
  obtain ⟨_, action⟩ := (fri_replay_refines limits params rounds proof state final challenges).mp accepted
  obtain ⟨_, _, _, _, powState, _, _, _, _, _, queries⟩ := action
  simpa only [Array.mem_def] using
    queryDraws_bounded challenges.logGlobal params.numQueries powState final challenges.indices.toList queries

end MultiStark.Verify.Proofs
