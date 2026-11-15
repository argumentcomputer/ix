import IxVMRefinement.Decl.JudgeMap

/-! # Judgement maps for modeled inductive runs

All witnesses and stored-data checks are retained. Only the annotation, typing, conversion,
and sort judgements change packages.
-/

namespace IxVM.Refinement.Decl.JudgementsMap

open Ix.Kernel Ix.Kernel.Semantics

variable {md : Mode} {J K : Judgements md} (M : JudgementsMap J K)

include M

theorem memberValRun {env : Env md} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} (h : MemberValRunJ J env blockNames cv cvA) :
    MemberValRunJ K env blockNames cv cvA := by
  obtain ⟨ty, hc, heq, hsuffix, cvm, value, hint, hfind, hlevels, htype⟩ := h
  exact ⟨ty, M.constantValRun hc, heq, hsuffix, cvm, value, hint, hfind, hlevels, htype⟩

theorem indMembersRun {blockNames : List (Key md)} {caps : IndCaps md} :
    ∀ {env : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ J blockNames caps env members env₂ →
      IndMembersRunJ K blockNames caps env members env₂
  | _, [], _, h => h
  | _, ci :: rest, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    refine ⟨cvA, M.memberValRun hmv, ?_⟩
    cases ci with
    | indInfo _ _ => exact M.indMembersRun hm
    | ctorInfo _ _ _ => exact M.indMembersRun hm
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ => exact hm

theorem provisionRecsRun {blockNames : List (Key md)} :
    ∀ {env : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ J blockNames env recs envSelf checked →
      ProvisionRecsRunJ K blockNames env recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest, hci, hmv, hrec, hchecked⟩ := h
    exact ⟨cvA, mI, rP, rules, rest, hci, M.memberValRun hmv,
      M.provisionRecsRun hrec, hchecked⟩

theorem iotaThmRun {env envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    (h : IotaThmRunJ J env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA) :
    IotaThmRunJ K env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA := by
  obtain ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7,
    M.defEqList k8, M.iotaRuns k9⟩

theorem iotaThmNRun {env envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    {lvls : List Level} {pins : List (Expr md)}
    (h : IotaThmNRunJ J env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins) :
    IotaThmNRunJ K env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA lvls pins := by
  obtain ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hshape, cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP,
    crestP, xFvsP, ldoms, k1, k2, k3, k4, k5, ldomsL, lrest2, k7,
    M.typedList k8, M.iotaRuns k9⟩

theorem iotaRuleRun {env envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r r' : RecRule md}
    (h : IotaRuleRunJ J env envSelf f cvName lps tyA mI rP j r r') :
    IotaRuleRunJ K env envSelf f cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, ⟨ty, h9⟩, fire, h10,
    hbr⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, M.annot h5, h6, h7, h8,
    ⟨ty, M.infer h9⟩, fire, h10, ?_⟩
  rcases hbr with ⟨hp, hf, ht⟩ | ⟨hp, lvls, pins, hf, ht⟩
  · exact Or.inl ⟨hp, hf, M.iotaThmRun ht⟩
  · exact Or.inr ⟨hp, lvls, pins, hf, M.iotaThmNRun ht⟩

theorem iotaRulesRun {env envSelf : Env md} {f : Key md → Key md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rules rules' : List (RecRule md)},
      IotaRulesRunJ J env envSelf f cvName lps tyA mI rP j rules rules' →
      IotaRulesRunJ K env envSelf f cvName lps tyA mI rP j rules rules'
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨r', rest, hr, hrest, hout⟩ := h
    exact ⟨r', rest, M.iotaRuleRun hr, M.iotaRulesRun hrest, hout⟩

theorem indRecsFoldRun {blockNames : List (Key md)} {envBase envSelf : Env md} :
    ∀ {acc : Env md} {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))}
      {out : Env md},
      IndRecsFoldRunJ J blockNames envBase envSelf acc checked out →
      IndRecsFoldRunJ K blockNames envBase envSelf acc checked out
  | _, [], _, h => h
  | _, _ :: _, _, h => by
    obtain ⟨rules, hrules, hrest⟩ := h
    exact ⟨rules, M.iotaRulesRun hrules, M.indRecsFoldRun hrest⟩

theorem indRecsRun {blockNames : List (Key md)} {env : Env md}
    {recs : List (ConstantInfo md)} {env₂ : Env md}
    (h : IndRecsRunJ J blockNames env recs env₂) :
    IndRecsRunJ K blockNames env recs env₂ := by
  rcases h with h | ⟨hne, heq, envSelf, checked, hprov, hfold⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, heq, envSelf, checked, M.provisionRecsRun hprov, M.indRecsFoldRun hfold⟩

/-- Modeled inductive records transport without changing their installed environment. -/
theorem modeled {env env₂ : Env md} {block : List (ConstantInfo md)}
    (h : DeclIndRunJ J env block env₂) : DeclIndRunJ K env block env₂ := by
  obtain ⟨hshape, envM, hmembers, hrecs⟩ := h
  exact ⟨hshape, envM, M.indMembersRun hmembers, M.indRecsRun hrecs⟩

end IxVM.Refinement.Decl.JudgementsMap
