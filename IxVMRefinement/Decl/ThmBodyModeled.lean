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

theorem ctorLevelParamsOf (ctor : Key md) :
    Ix.Kernel.ctorLevelParamsOf source.find? ctor = Ix.Kernel.ctorLevelParamsOf target.find? ctor :=
  h.observe ctor (fun q => match q with | some (.ctorInfo cv _ _) => cv.levelParams | _ => [])
    (by intros; rfl)

theorem projFnRule (T ctor : Key md) (pty : Expr md) (nP nF i : Nat) (rhs : Expr md) :
    Ix.Kernel.projFnRule source.find? T ctor pty nP nF i rhs =
      Ix.Kernel.projFnRule target.find? T ctor pty nP nF i rhs := by
  simp only [Ix.Kernel.projFnRule, h.ctorLevelParamsOf, h.recRuleBits]

theorem checkEtaThm (mode : CheckMode) (T ctorName : Key md) (lps : List LevelParam) (nP nF : Nat) :
    Ix.Kernel.checkEtaThm mode source T ctorName lps nP nF =
      Ix.Kernel.checkEtaThm mode target T ctorName lps nP nF := by
  let read (theoremInfo modelT modelC equalInfo : Option (ConstantInfo md)) (slots : Bool) : Bool :=
    match theoremInfo,
        modelT,
        modelC, equalInfo with
    | some (.thmInfo tcv _), some (.defnInfo cvmT _ _),
        some (.defnInfo cvmC _ _), some eqStored =>
      eqStored == eqA && tcv.levelParams == lps &&
      cvmT.levelParams == lps && cvmC.levelParams == lps &&
      slots &&
      (match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with
       | some (sbinders, sbody), some (tbindersM, tbodyM) =>
         domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
         (match sbinders[nP]? with
          | some (xdom, _) =>
            xdom == Expr.mkAppN (.const (auxKey T .model) (lps.map .param))
              ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
          | none => false) &&
         (match sbody with
          | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
            c == eqName && lhsC == Expr.bvar 0 &&
            tySlot == Expr.mkAppN (.const (auxKey T .model) (lps.map .param))
              ((List.range nP).map fun k => Expr.bvar (nP - k)) &&
            rhsC == Expr.mkAppN
              (.const (auxKey ctorName .model) (lps.map .param))
              (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
               (List.range nF).map fun j => Expr.mkAppN
                 (.const (projModelName T j) (lps.map .param))
                 (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                  [Expr.bvar 0])) &&
            (!mode.ttChecks || tbodyM == Expr.sort ℓA)
          | _ => false)
       | _, _ => false)
    | _, _, _, _ => false

  let sourceSlots := (List.range nF).all (fun j =>
      match source.find? (projModelName T j) with
      | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
      | _ => false)
  let targetSlots := (List.range nF).all (fun j =>
      match target.find? (projModelName T j) with
      | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
      | _ => false)
  have slots : sourceSlots = targetSlots := by
    apply congrArg (List.all (List.range nF))
    funext j
    exact h.observe (projModelName T j) (α := Bool)
      (fun q => match q with | some (.defnInfo cv _ _) => cv.levelParams == lps | _ => false)
      (by intros; rfl)
  change read (source.find? (auxKey (auxKey T .model) .eta)) (source.find? (auxKey T .model))
      (source.find? (auxKey ctorName .model)) (source.find? eqName) sourceSlots =
    read (target.find? (auxKey (auxKey T .model) .eta)) (target.find? (auxKey T .model))
      (target.find? (auxKey ctorName .model)) (target.find? eqName) targetSlots
  calc
    _ = read (target.find? (auxKey (auxKey T .model) .eta)) (source.find? (auxKey T .model))
        (source.find? (auxKey ctorName .model)) (source.find? eqName) sourceSlots :=
      h.observe _ (fun q => read q (source.find? (auxKey T .model))
        (source.find? (auxKey ctorName .model)) (source.find? eqName) sourceSlots) (by intros; dsimp only [read]; repeat' first | rfl | split)
    _ = read (target.find? (auxKey (auxKey T .model) .eta)) (target.find? (auxKey T .model))
        (source.find? (auxKey ctorName .model)) (source.find? eqName) sourceSlots :=
      h.observe _ (fun q => read (target.find? (auxKey (auxKey T .model) .eta)) q
        (source.find? (auxKey ctorName .model)) (source.find? eqName) sourceSlots) (by intros; dsimp only [read]; repeat' first | rfl | split)
    _ = read (target.find? (auxKey (auxKey T .model) .eta)) (target.find? (auxKey T .model))
        (target.find? (auxKey ctorName .model)) (source.find? eqName) sourceSlots :=
      h.observe _ (fun q => read (target.find? (auxKey (auxKey T .model) .eta))
        (target.find? (auxKey T .model)) q (source.find? eqName) sourceSlots) (by intros; dsimp only [read]; repeat' first | rfl | split)
    _ = read (target.find? (auxKey (auxKey T .model) .eta)) (target.find? (auxKey T .model))
        (target.find? (auxKey ctorName .model)) (target.find? eqName) sourceSlots :=
      h.observe _ (fun q => read (target.find? (auxKey (auxKey T .model) .eta))
        (target.find? (auxKey T .model)) (target.find? (auxKey ctorName .model)) q sourceSlots)
        (by intros; dsimp only [read]; repeat' first | rfl | split)
    _ = _ := congrArg (read (target.find? (auxKey (auxKey T .model) .eta))
      (target.find? (auxKey T .model)) (target.find? (auxKey ctorName .model))
      (target.find? eqName)) slots

theorem checkUnitThm (mode : CheckMode) (T : Key md) (lps : List LevelParam) (nP : Nat) :
    Ix.Kernel.checkUnitThm mode source T lps nP = Ix.Kernel.checkUnitThm mode target T lps nP := by
  let read (theoremInfo modelT equalInfo : Option (ConstantInfo md)) : Bool :=
    match theoremInfo,
        modelT, equalInfo with
    | some (.thmInfo tcv _), some (.defnInfo cvmT _ _), some eqStored =>
      eqStored == eqA && tcv.levelParams == lps &&
      cvmT.levelParams == lps &&
      (match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
       | some (sbinders, sbody), some (tbindersM, tbodyM) =>
         domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
         (match sbinders[nP]? with
          | some (xdom, _) =>
            xdom == Expr.mkAppN (.const (auxKey T .model) (lps.map .param))
              ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
          | none => false) &&
         (match sbinders[nP + 1]? with
          | some (ydom, _) =>
            ydom == Expr.mkAppN (.const (auxKey T .model) (lps.map .param))
              ((List.range nP).map fun k => Expr.bvar (nP - k))
          | none => false) &&
         (match sbody with
          | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
            c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0 &&
            tySlot == Expr.mkAppN (.const (auxKey T .model) (lps.map .param))
              ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)) &&
            (!mode.ttChecks || tbodyM == Expr.sort ℓA)
          | _ => false)
       | _, _ => false)
    | _, _, _ => false

  change read (source.find? (auxKey (auxKey T .model) .unitlike))
      (source.find? (auxKey T .model)) (source.find? eqName) =
    read (target.find? (auxKey (auxKey T .model) .unitlike))
      (target.find? (auxKey T .model)) (target.find? eqName)
  calc
    _ = read (target.find? (auxKey (auxKey T .model) .unitlike))
        (source.find? (auxKey T .model)) (source.find? eqName) :=
      h.observe _ (fun q => read q (source.find? (auxKey T .model)) (source.find? eqName))
        (by intros; dsimp only [read]; repeat' first | rfl | split)
    _ = read (target.find? (auxKey (auxKey T .model) .unitlike))
        (target.find? (auxKey T .model)) (source.find? eqName) :=
      h.observe _ (fun q => read (target.find? (auxKey (auxKey T .model) .unitlike)) q
        (source.find? eqName)) (by intros; dsimp only [read]; repeat' first | rfl | split)
    _ = _ := h.observe _ (fun q => read (target.find? (auxKey (auxKey T .model) .unitlike))
      (target.find? (auxKey T .model)) q) (by intros; dsimp only [read]; repeat' first | rfl | split)

theorem indBlockCaps (mode : CheckMode) (cvT cvC : ConstantVal md) (nP nF : Nat) :
    Ix.Kernel.indBlockCaps mode source cvT cvC nP nF =
      Ix.Kernel.indBlockCaps mode target cvT cvC nP nF := by
  simp only [Ix.Kernel.indBlockCaps, h.checkEtaThm, h.checkUnitThm]

theorem ctorResidualOk (mode : CheckMode) (T ctor : Key md) (lps : List LevelParam)
    (nP nF : Nat) (eta : Bool) :
    Ix.Kernel.ctorResidualOk mode source T ctor lps nP nF eta =
      Ix.Kernel.ctorResidualOk mode target T ctor lps nP nF eta := by
  unfold Ix.Kernel.ctorResidualOk
  have rel := h ctor
  generalize source.find? ctor = left at rel ⊢
  generalize target.find? ctor = right at rel ⊢
  cases rel <;> rfl

/-- Projection-function checks retain the theorem's signature while its unread body may differ. -/
theorem projFnRun {mode : CheckMode} {fuel : Nat} {T ctor : Key md}
    {lps : List LevelParam} {nP nF i : Nat} {sourceOut : Env md}
    (run : ProjFnRun mode fuel source T ctor lps nP nF i sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ ProjFnRun mode fuel target T ctor lps nP nF i targetOut := by
  obtain ⟨cvj, mcv, mval, mhint, pty, rhs, hc, hm, hmlps, hfresh,
    hT, hEq, hpty, hround, hres, hbound, hclosed, hlps, hstrip1,
    hlt, hstripP, hplain, hbig, rfl⟩ := run
  obtain ⟨cbinders, cbody, hCstrip, hcargs, hchead, hrclosed, hrbound, hrlps,
    hrres, hrstrip, hri, tcv, tval, hthm, htlps, hpin, fvs, sbody,
    hopen, hleft, hright⟩ := hbig
  obtain ⟨tval', hthm'⟩ := h.find_thm hthm
  let ci : ConstantInfo md := .recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [Ix.Kernel.projFnRule source.find? T ctor pty nP nF i rhs]
  refine ⟨⟨ci :: target.consts⟩, h.cons ci, cvj, mcv, mval, mhint, pty, rhs,
    h.find_nonThm hc (by intros; intro heq; cases heq),
    h.find_nonThm hm (by intros; intro heq; cases heq), hmlps,
    ?_, ?_, h.find_nonThm hEq (by intros; intro heq; cases heq), hpty, hround,
    ?_, hbound, hclosed, hlps, hstrip1, hlt, hstripP, hplain, ?_, ?_⟩
  · simpa only [h.isNone] using hfresh
  · simpa only [h.isSome] using hT
  · simpa only [h.constsResolve] using hres
  · refine ⟨cbinders, cbody, hCstrip, hcargs, hchead, hrclosed, hrbound, hrlps,
      ?_, hrstrip, ?_, tcv, tval', hthm', htlps, hpin, fvs, sbody, hopen, ?_, ?_⟩
    · simpa only [h.constsResolve] using hrres
    · simpa only [h.inferTypeCore] using hri
    · simpa only [h.inferTypeCore, h.isDefEqCore] using hleft
    · simpa only [h.inferTypeCore, h.isDefEqCore] using hright
  · simp only [ci, h.projFnRule]

theorem projInstallRun {mode : CheckMode} {fuel : Nat} {T ctor : Key md}
    {lps : List LevelParam} {nP nF : Nat} {fields : List Nat} {sourceOut : Env md}
    (run : ProjInstallRun mode fuel T ctor lps nP nF source fields sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      ProjInstallRun mode fuel T ctor lps nP nF target fields targetOut := by
  induction fields generalizing source target with
  | nil =>
    change sourceOut = source at run
    subst sourceOut
    exact ⟨target, h, rfl⟩
  | cons i rest ih =>
    obtain ⟨sourceNext, hstep, hrest⟩ := run
    rcases hstep with installed | ⟨missing, rfl⟩
    · obtain ⟨targetNext, agreement, targetStep⟩ := h.projFnRun installed
      obtain ⟨targetOut, outAgreement, targetRest⟩ := ih agreement hrest
      exact ⟨targetOut, outAgreement, targetNext, Or.inl targetStep, targetRest⟩
    · obtain ⟨targetOut, outAgreement, targetRest⟩ := ih h hrest
      exact ⟨targetOut, outAgreement, target,
        Or.inr ⟨by simpa only [h.isNone] using missing, rfl⟩, targetRest⟩

/-- Both actual modeled branches replay with identical capabilities and stored rule data. -/
theorem modeledRun {mode : CheckMode} {fuel : Nat} {block : List (ConstantInfo md)}
    {sourceOut : Env md} (run : DeclIndRun mode fuel source block sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ DeclIndRun mode fuel target block targetOut := by
  obtain ⟨splitBlock, branch⟩ := run
  rcases branch with ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt, envM, envR,
    members, recs, residual, fresh, projections⟩ | ⟨nonsingle, envM, members, recs⟩
  · obtain ⟨targetM, hM, targetMembers⟩ := h.indMembersRun members
    have targetMembers' := targetMembers
    rw [h.indBlockCaps] at targetMembers'
    obtain ⟨targetR, hR, targetRecs⟩ := hM.indRecsRun recs
    obtain ⟨targetOut, outAgreement, targetProjections⟩ := hR.projInstallRun projections
    refine ⟨targetOut, outAgreement, splitBlock, Or.inl
      ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt, targetM, targetR,
        targetMembers', targetRecs, ?_, ?_, targetProjections⟩⟩
    · simpa only [h.indBlockCaps, hR.ctorResidualOk] using residual
    · simpa only [hR.isNone] using fresh
  · obtain ⟨targetM, hM, targetMembers⟩ := h.indMembersRun members
    obtain ⟨targetOut, outAgreement, targetRecs⟩ := hM.indRecsRun recs
    exact ⟨targetOut, outAgreement, splitBlock,
      Or.inr ⟨nonsingle, targetM, targetMembers, targetRecs⟩⟩

end IxVM.Refinement.Decl.ThmBodyView.Agrees
