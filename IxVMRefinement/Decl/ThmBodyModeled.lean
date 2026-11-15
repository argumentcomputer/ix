import IxVMRefinement.Decl.ThmBodyDecl
import IxC.Kernel.Semantics.DeclIndRun

/-! # Modeled member and recursor checks under the opaque theorem view

The model signatures, constructor records, and recursor rules stay exact. The transports keep
the actual annotation and checking runs and rebuild each extended environment in order.
-/

namespace IxVM.Refinement.Decl.ThmBodyView.Agrees

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Verify

variable {md : Mode} {source target : Env md} (h : Agrees source target)

include h

theorem recRuleKOf (ctor : Key md) :
    Ix.Kernel.recRuleKOf source.find? ctor = Ix.Kernel.recRuleKOf target.find? ctor := by
  unfold Ix.Kernel.recRuleKOf
  have rel := h ctor
  generalize source.find? ctor = left at rel ⊢
  generalize target.find? ctor = right at rel ⊢
  cases rel with
  | thm => rfl
  | same =>
    cases left with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cv nP nF =>
        dsimp only
        cases cv.type.piResult.getAppFn with
        | const T levels =>
          exact h.observe T (α := Bool)
            (fun (q : Option (ConstantInfo md)) => match q with | some (.indInfo _ caps) => caps.ruleK && nF == 0 | _ => false)
            (by intros; rfl)
        | _ => rfl
      | _ => rfl

theorem recRuleEtaOf (recName ctor : Key md) :
    Ix.Kernel.recRuleEtaOf source.find? recName ctor =
      Ix.Kernel.recRuleEtaOf target.find? recName ctor := by
  unfold Ix.Kernel.recRuleEtaOf
  have rel := h ctor
  generalize source.find? ctor = left at rel ⊢
  generalize target.find? ctor = right at rel ⊢
  cases rel with
  | thm => rfl
  | same =>
    cases left with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo cv nP nF =>
        dsimp only
        cases cv.type.piResult.getAppFn with
        | const T levels =>
          exact h.observe T (α := Bool)
            (fun (q : Option (ConstantInfo md)) => match q with
              | some (.indInfo cvT caps) =>
                caps.eta && caps.etaCtor == some ctor && !Key.isProjFnShape recName &&
                  cv.levelParams == cvT.levelParams
              | _ => false) (by intros; rfl)
        | _ => rfl
      | _ => rfl

theorem recRuleBits (recName : Key md) (rule : RecRule md) :
    Ix.Kernel.recRuleBits source.find? recName rule = Ix.Kernel.recRuleBits target.find? recName rule := by
  simp only [Ix.Kernel.recRuleBits, h.recRuleKOf, h.recRuleEtaOf]

theorem defEqListOk (mode : CheckMode) (fuel depth : Nat) (as bs : List (Expr md)) :
    DefEqListOk mode fuel source depth as bs = DefEqListOk mode fuel target depth as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih => cases bs <;> simp only [DefEqListOk, h.isDefEqCore, ih]

theorem typedListOk (mode : CheckMode) (fuel depth : Nat) (as bs : List (Expr md)) :
    TypedListOk mode fuel source depth as bs = TypedListOk mode fuel target depth as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih => cases bs <;> simp only [TypedListOk, h.inferTypeCore, h.isDefEqCore, ih]

theorem iotaRuns (mode : CheckMode) (fuel depth : Nat)
    (idxL idxR domL domR preL preR lamL lamR : List (Expr md))
    (rhsS rhsApplied alphaS lhsS : Expr md) :
    IotaRuns mode fuel source depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS =
    IotaRuns mode fuel target depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS := by
  simp only [IotaRuns, h.defEqListOk, h.isDefEqCore, h.inferTypeCore]

theorem nestedRuleShape {sourceSelf targetSelf : Env md} (hs : Agrees sourceSelf targetSelf)
    (cvName : Key md) (lps : List LevelParam) (ty : Expr md) (mI rP cnP j : Nat) :
    Ix.Kernel.nestedRuleShape source sourceSelf cvName lps ty mI rP cnP j =
      Ix.Kernel.nestedRuleShape target targetSelf cvName lps ty mI rP cnP j := by
  simp only [Ix.Kernel.nestedRuleShape, h.findCV, hs.constsResolve]

theorem memberValRun {mode : CheckMode} {fuel : Nat} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} (run : MemberValRun mode fuel source blockNames cv cvA) :
    MemberValRun mode fuel target blockNames cv cvA := by
  obtain ⟨ty, hcv, hout, hname, cvm, value, hint, found, levels, type⟩ := run
  exact ⟨ty, h.constantValRun hcv, hout, hname, cvm, value, hint,
    h.find_nonThm found (by intros; intro heq; cases heq), levels, type⟩

theorem indMembersRun {mode : CheckMode} {fuel : Nat} {blockNames : List (Key md)}
    {caps : IndCaps md} {members : List (ConstantInfo md)} {sourceOut : Env md}
    (run : IndMembersRun mode fuel blockNames caps source members sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      IndMembersRun mode fuel blockNames caps target members targetOut := by
  induction members generalizing source target with
  | nil =>
    change sourceOut = source at run
    subst sourceOut
    exact ⟨target, h, rfl⟩
  | cons ci rest ih =>
    obtain ⟨cvA, hmember, run⟩ := run
    have hm := h.memberValRun hmember
    cases ci with
    | indInfo cv caps' =>
      obtain ⟨out, agreement, hrest⟩ := ih (h.cons (.indInfo cvA caps)) run
      exact ⟨out, agreement, cvA, hm, hrest⟩
    | ctorInfo cv nP nF =>
      obtain ⟨out, agreement, hrest⟩ := ih (h.cons (.ctorInfo cvA nP nF)) run
      exact ⟨out, agreement, cvA, hm, hrest⟩
    | _ => exact run.elim

theorem provisionRecsRun {mode : CheckMode} {fuel : Nat} {blockNames : List (Key md)}
    {recs : List (ConstantInfo md)} {sourceSelf : Env md}
    {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))}
    (run : ProvisionRecsRun mode fuel blockNames source recs sourceSelf checked) :
    ∃ targetSelf, Agrees sourceSelf targetSelf ∧
      ProvisionRecsRun mode fuel blockNames target recs targetSelf checked := by
  induction recs generalizing source target checked with
  | nil =>
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, h, rfl, rfl⟩
  | cons ci rest ih =>
    obtain ⟨cvA, mI, rP, rules, rest', hci, hmember, run, hout⟩ := run
    obtain ⟨targetSelf, agreement, targetRun⟩ := ih (h.cons (.recInfo cvA mI rP [])) run
    exact ⟨targetSelf, agreement, cvA, mI, rP, rules, rest', hci,
      h.memberValRun hmember, targetRun, hout⟩

theorem iotaThmRun {sourceSelf targetSelf : Env md} (hs : Agrees sourceSelf targetSelf)
    {mode : CheckMode} {fuel : Nat} {f : Key md → Key md} {cvName : Key md}
    {lps : List LevelParam} {ty : Expr md} {mI rP j : Nat} {r : RecRule md}
    {cvj : ConstantVal md} {cnP cnF : Nat} {rhs : Expr md}
    (run : IotaThmRun mode fuel source sourceSelf f cvName lps ty mI rP j r cvj cnP cnF rhs) :
    IotaThmRun mode fuel target targetSelf f cvName lps ty mI rP j r cvj cnP cnF rhs := by
  simpa only [IotaThmRun, h.findCV, hs.defEqListOk, hs.iotaRuns] using run

theorem iotaThmNRun {sourceSelf targetSelf : Env md} (hs : Agrees sourceSelf targetSelf)
    {mode : CheckMode} {fuel : Nat} {f : Key md → Key md} {cvName : Key md}
    {lps : List LevelParam} {ty : Expr md} {mI rP j : Nat} {r : RecRule md}
    {cvj : ConstantVal md} {cnP cnF : Nat} {rhs : Expr md} {lvls : List Level} {pins : List (Expr md)}
    (run : IotaThmNRun mode fuel source sourceSelf f cvName lps ty mI rP j r cvj cnP cnF rhs lvls pins) :
    IotaThmNRun mode fuel target targetSelf f cvName lps ty mI rP j r cvj cnP cnF rhs lvls pins := by
  simpa only [IotaThmNRun, h.nestedRuleShape hs, h.findCV, hs.typedListOk,
    hs.iotaRuns, hs.annotateCore] using run

theorem iotaRuleRun {sourceSelf targetSelf : Env md} (hs : Agrees sourceSelf targetSelf)
    {mode : CheckMode} {fuel : Nat} {f : Key md → Key md} {cvName : Key md}
    {lps : List LevelParam} {ty : Expr md} {mI rP j : Nat} {r r' : RecRule md}
    (run : IotaRuleRun mode fuel source sourceSelf f cvName lps ty mI rP j r r') :
    IotaRuleRun mode fuel target targetSelf f cvName lps ty mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhs, found, fields, bounded, closed, ann, levels, resolves,
    shape, inferred, fire, output, branch⟩ := run
  refine ⟨cvj, cnP, cnF, rhs, h.find_nonThm found (by intros; intro heq; cases heq),
    fields, bounded, closed, ?_, levels, ?_, shape, ?_, fire, ?_, ?_⟩
  · simpa only [hs.annotateCore] using ann
  · simpa only [hs.constsResolve] using resolves
  · simpa only [hs.inferTypeCore] using inferred
  · simpa only [h.recRuleBits] using output
  · rcases branch with ⟨plain, hfire, hthm⟩ | ⟨nested, lvls, pins, hfire, hthm⟩
    · exact Or.inl ⟨plain, hfire, h.iotaThmRun hs hthm⟩
    · exact Or.inr ⟨nested, lvls, pins, hfire, h.iotaThmNRun hs hthm⟩

theorem iotaRulesRun {sourceSelf targetSelf : Env md} (hs : Agrees sourceSelf targetSelf)
    {mode : CheckMode} {fuel : Nat} {f : Key md → Key md} {cvName : Key md}
    {lps : List LevelParam} {ty : Expr md} {mI rP j : Nat} {rules rules' : List (RecRule md)}
    (run : IotaRulesRun mode fuel source sourceSelf f cvName lps ty mI rP j rules rules') :
    IotaRulesRun mode fuel target targetSelf f cvName lps ty mI rP j rules rules' := by
  induction rules generalizing j rules' with
  | nil => exact run
  | cons r rest ih =>
    obtain ⟨r', rest', hr, hrest, hout⟩ := run
    exact ⟨r', rest', h.iotaRuleRun hs hr, ih hrest, hout⟩

theorem indRecsFoldRun {sourceBase targetBase sourceSelf targetSelf : Env md}
    (hb : Agrees sourceBase targetBase) (hs : Agrees sourceSelf targetSelf)
    {mode : CheckMode} {fuel : Nat} {blockNames : List (Key md)}
    {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))} {sourceOut : Env md}
    (run : IndRecsRun.IndRecsFoldRun mode fuel blockNames sourceBase sourceSelf source checked sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      IndRecsRun.IndRecsFoldRun mode fuel blockNames targetBase targetSelf target checked targetOut := by
  induction checked generalizing source target with
  | nil =>
    change sourceOut = source at run
    subst sourceOut
    exact ⟨target, h, rfl⟩
  | cons c rest ih =>
    obtain ⟨rules, hrules, hrest⟩ := run
    obtain ⟨out, agreement, targetRest⟩ := ih (h.cons (.recInfo c.1 c.2.1 c.2.2.1 rules)) hrest
    exact ⟨out, agreement, rules, hb.iotaRulesRun hs hrules, targetRest⟩

theorem indRecsRun {mode : CheckMode} {fuel : Nat} {blockNames : List (Key md)}
    {recs : List (ConstantInfo md)} {sourceOut : Env md}
    (run : IndRecsRun mode fuel blockNames source recs sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      IndRecsRun mode fuel blockNames target recs targetOut := by
  rcases run with ⟨empty, rfl⟩ | ⟨nonempty, eq, sourceSelf, checked, provision, installed⟩
  · exact ⟨target, h, Or.inl ⟨empty, rfl⟩⟩
  · obtain ⟨targetSelf, hs, targetProvision⟩ := h.provisionRecsRun provision
    obtain ⟨targetOut, agreement, targetInstalled⟩ := h.indRecsFoldRun h hs installed
    exact ⟨targetOut, agreement, Or.inr ⟨nonempty,
      h.find_nonThm eq (by intros; intro heq; cases heq),
      targetSelf, checked, targetProvision, targetInstalled⟩⟩

end IxVM.Refinement.Decl.ThmBodyView.Agrees
