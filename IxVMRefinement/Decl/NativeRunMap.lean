import IxVMRefinement.Decl.ModeledRunMap
import IxVMRefinement.Decl.VerifiedRunMap
import IxC.Kernel.Semantics.Inductives.DeclNativeJ

/-! # Judgement maps for native and twin inductive runs

The map preserves every environment, installed constant, rule, and structural check.
Together with the verified primitive map, it translates accepted kernel runs to rules-tier
derivations at the same environment.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics

namespace JudgementsMap

variable {md : Mode} {J K : Judgements md} (M : JudgementsMap J K)

include M

theorem constantValCheck {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : ConstantValCheckJ K env cv cv' := by
  obtain ⟨ty, hc, heq⟩ := h
  exact ⟨ty, M.constantValRun hc, heq⟩

theorem formerStored {env : Env md} {nIdx : Nat} {cv₀ cvTa cvS : ConstantVal md}
    (h : FormerStoredJ J env nIdx cv₀ cvTa cvS) : FormerStoredJ K env nIdx cv₀ cvTa cvS := by
  rcases h with heq | ⟨heq, hde, hn⟩
  · exact Or.inl heq
  · exact Or.inr ⟨heq, M.defeq hde, hn⟩

theorem sumIndRun {env envI : Env md} {p p' : InductiveShape md}
    {capsOf : InductiveShape md → IndCaps md} {cvTa : ConstantVal md}
    (h : SumIndRunJ J env p capsOf envI cvTa p') : SumIndRunJ K env p capsOf envI cvTa p' := by
  obtain ⟨cv₀, s, bs, cvS, hc, halt, hstrip, hstored, hp, henv⟩ := h
  refine ⟨cv₀, s, bs, cvS, M.constantValCheck hc, ?_, hstrip, M.formerStored hstored, hp, henv⟩
  rcases halt with heq | ⟨ty, hc'⟩
  · exact Or.inl heq
  · exact Or.inr ⟨ty, M.constantValCheck hc'⟩

theorem fieldSorts {env : Env md} {isProp large : Bool} {s : Level}
    {nP n : Nat} {fvs idxArgs : List (Expr md)} {sorts : List Level}
    (h : FieldSortsJ J env isProp large s nP fvs idxArgs n sorts) :
    FieldSortsJ K env isProp large s nP fvs idxArgs n sorts := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨fv, ty, level, hv, hu, hinfer, hsort, hle, hzero⟩ := h.2 i hi
  exact ⟨fv, ty, level, hv, hu, M.infer hinfer, M.sort hsort, hle, hzero⟩

theorem structDoms {env : Env md} {off n : Nat} {fvs doms : List (Expr md)}
    (h : StructDomsJ J env off fvs doms n) : StructDomsJ K env off fvs doms n := by
  intro i hi
  obtain ⟨a, b, ha, hb, hde⟩ := h i hi
  exact ⟨a, b, ha, hb, M.defeq hde⟩

theorem sharedStructDoms {env : Env md} {n : Nat} {fvs tfvs : List (Expr md)}
    (h : SharedStructDomsJ J env fvs tfvs n) : SharedStructDomsJ K env fvs tfvs n := by
  intro i hi
  obtain ⟨a, b, a', ha, hb, heq, hde, hleaves⟩ := h i hi
  exact ⟨a, b, a', ha, hb, heq, M.defeq hde, hleaves⟩

theorem sumCtorRun {env₀ env : Env md} {T : Key md} {lps : List LevelParam}
    {nP nIdx nF : Nat} {s : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal md} {sorts : List Level}
    (h : SumCtorRunJ J env₀ env T lps nP nIdx s isProp large cvC nF cvTa cvCa sorts) :
    SumCtorRunJ K env₀ env T lps nP nIdx s isProp large cvC nF cvTa cvCa sorts := by
  obtain ⟨⟨cv₀, hc, halt⟩, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
    hopP, hopT, hdoms, hopF, hlen, hxres, hires, hsorts⟩ := h
  refine ⟨⟨cv₀, M.constantValCheck hc, ?_⟩, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs,
    hopP, hopT, hdoms.elim (fun hd => Or.inl (M.structDoms hd))
      (fun hd => Or.inr (M.sharedStructDoms hd)), hopF, hlen, hxres, hires, M.fieldSorts hsorts⟩
  rcases halt with heq | ⟨ty, hc'⟩
  · exact Or.inl heq
  · exact Or.inr ⟨ty, M.constantValCheck hc'⟩

theorem sumCtorsRun {env₀ env : Env md} {T : Key md} {lps : List LevelParam}
    {nP nIdx : Nat} {s : Level} {isProp large : Bool} {cvTa : ConstantVal md}
    {cs ctorsA : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (h : SumCtorsRunJ J env₀ env T lps nP nIdx s isProp large cvTa cs ctorsA sortss) :
    SumCtorsRunJ K env₀ env T lps nP nIdx s isProp large cvTa cs ctorsA sortss := by
  refine ⟨h.1, h.2.1, fun j c cA hc hcA => ?_⟩
  obtain ⟨hnF, sorts, hs, hr⟩ := h.2.2 j c cA hc hcA
  exact ⟨hnF, sorts, hs, M.sumCtorRun hr⟩

theorem nativeRecRun {env : Env md} {p : NativeParts md} {cvTa cvRa : ConstantVal md}
    {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : NativeRecRunJ J env p cvTa ctorsA cvRa rhss) :
    NativeRecRunJ K env p cvTa ctorsA cvRa rhss := by
  obtain ⟨hlps, hpin, cvI, recTy, hc, hgen, hlp, hres, hbv, hfv, hde, hrules, hcv⟩ := h
  exact ⟨hlps, hpin, cvI, recTy, M.constantValCheck hc, hgen, hlp, hres, hbv, hfv,
    M.defeq hde, hrules, hcv⟩

theorem annotList {env : Env md} {d : Nat} :
    ∀ {as bs : List (Expr md)}, Forall₂ (J.annot env d) as bs → Forall₂ (K.annot env d) as bs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (M.annot h) (annotList hs)

theorem recStored {env : Env md} {p : NativeParts md} {cvRg cvRa : ConstantVal md}
    {rhsG rhss : List (Expr md)} (h : RecStoredJ J env p cvRg rhsG cvRa rhss) :
    RecStoredJ K env p cvRg rhsG cvRa rhss := by
  rcases h with heq | ⟨cvI, hc, hcv, hty, hrhs, hlf, hann, hlfTy, hlp, hmajor⟩
  · exact Or.inl heq
  · exact Or.inr ⟨cvI, M.constantValCheck hc, hcv, hty, hrhs, hlf, M.annotList hann,
      hlfTy, hlp, hmajor⟩

theorem nativeRec {env : Env md} {p : NativeParts md} {cvTa cvRa : ConstantVal md}
    {ctorsA : List (ConstantVal md × Nat)} {rhss : List (Expr md)}
    (h : NativeRecJ J env p cvTa ctorsA cvRa rhss) : NativeRecJ K env p cvTa ctorsA cvRa rhss := by
  obtain ⟨cvRg, rhsG, hr, hs⟩ := h
  exact ⟨cvRg, rhsG, M.nativeRecRun hr, M.recStored hs⟩

/-- Native runs retain their exact output environment under a judgement map. -/
theorem native {env env₂ : Env md} {p₀ : NativeParts md}
    (h : DeclNativeRunJ J env p₀ env₂) : DeclNativeRunJ K env p₀ env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss,
    tfvs, trest, isorts, hInd, hp, hCtors, hKinds, hcaps, hlarge, hop, hsorts, hfields,
    hRec, hTbl, hformer⟩ := h
  exact ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss,
    tfvs, trest, isorts, M.sumIndRun hInd, hp, M.sumCtorsRun hCtors, hKinds, hcaps, hlarge,
    hop, M.fieldSorts hsorts, hfields, M.nativeRec hRec, hTbl, hformer⟩

theorem nativeNoRec {env env₂ : Env md} {p₀ : NativeParts md}
    (h : DeclNativeNoRecRunJ J env p₀ env₂) : DeclNativeNoRecRunJ K env p₀ env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts,
    hInd, hp, hCtors, hKinds, hcaps, hop, hsorts, hfields, hTbl, hformer⟩ := h
  exact ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts,
    M.sumIndRun hInd, hp, M.sumCtorsRun hCtors, hKinds, hcaps, hop, M.fieldSorts hsorts,
    hfields, hTbl, hformer⟩

theorem twinRule {env envSelf : Env md} {f : Key md → Key md} {recName : Key md}
    {lps : List LevelParam} {cvW : ConstantVal md} {mI rP : Nat} {rW rW' rC : RecRule md}
    (h : TwinRuleJ J env envSelf f recName lps cvW mI rP rW rW' rC) :
    TwinRuleJ K env envSelf f recName lps cvW mI rP rW rW' rC := by
  obtain ⟨hctor, hnf, hbv, hfv, hann, hlp, hres, hlf, hctorC, hnfC, hnp, hfire,
    hk, hblind, heta, hplain, hnested, rhsG, hwC, hwW, hgen⟩ := h
  refine ⟨hctor, hnf, hbv, hfv, M.annot hann, hlp, hres, hlf, hctorC, hnfC, hnp, hfire,
    hk, hblind, heta, hplain, hnested, rhsG, hwC, hwW, ?_⟩
  rcases hgen with heq | ⟨hfvG, hlpG, hresG, hbvG, ty, hi⟩
  · exact Or.inl heq
  · exact Or.inr ⟨hfvG, hlpG, hresG, hbvG, ty, M.infer hi⟩

theorem twinRules {env envSelf : Env md} {f : Key md → Key md} {recName : Key md}
    {lps : List LevelParam} {cvW : ConstantVal md} {mI rP : Nat} :
    ∀ {pairs : List (RecRule md × RecRule md)} {rules : List (RecRule md)},
      Forall₂ (fun p r => TwinRuleJ J env envSelf f recName lps cvW mI rP p.1 p.2 r) pairs rules →
      Forall₂ (fun p r => TwinRuleJ K env envSelf f recName lps cvW mI rP p.1 p.2 r) pairs rules
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (M.twinRule h) (twinRules hs)

theorem twin {env env₂ : Env md} {block : List (ConstantInfo md)}
    (h : DeclRecTwinRunJ J env block env₂) : DeclRecTwinRunJ K env block env₂ := by
  obtain ⟨ws, f, hne, hblock, henv, hnd, hfr, hrename, hmembers⟩ := h
  refine ⟨ws, f, hne, hblock, henv, hnd, hfr, hrename, ?_⟩
  intro w hw
  obtain ⟨hc, hlf, hfind, hlps, hmodel, hgen, hlen, hrules⟩ := hmembers w hw
  refine ⟨M.constantValCheck hc, hlf, hfind, hlps, hmodel, ?_, hlen, M.twinRules hrules⟩
  obtain ⟨tyG, hwC, hwW, hgen⟩ := hgen
  refine ⟨tyG, hwC, hwW, ?_⟩
  rcases hgen with heq | ⟨hfv, hlp, hres, hbv, ty, hi⟩
  · exact Or.inl heq
  · exact Or.inr ⟨hfv, hlp, hres, hbv, ty, M.infer hi⟩

/-- All inductive routes transport at the same environment and declaration. -/
theorem indRoutes {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    (h : IndRoutesJ J env block nP env₂) : IndRoutesJ K env block nP env₂ := by
  rcases h with ⟨p, hp, hn⟩ | hm | ⟨p, hp, hn⟩ | ht
  · exact Or.inl ⟨p, hp, M.native hn⟩
  · exact Or.inr (Or.inl (M.modeled hm))
  · exact Or.inr (Or.inr (Or.inl ⟨p, hp, M.nativeNoRec hn⟩))
  · exact Or.inr (Or.inr (Or.inr (M.twin ht)))

end JudgementsMap

/-- An accepted verified inductive run supplies rules-tier evidence at its original environment. -/
theorem verifiedIndRoutes_to_rulesJ {fuel : Nat} {env env₂ : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (h : IndRoutesJ (runJ .verified fuel) env block nP env₂) :
    IndRoutesJ Ix.Kernel.Model.rulesJ env block nP env₂ :=
  (verifiedRunMap fuel).indRoutes h

end IxVM.Refinement.Decl
