import IxVMRefinement.Decl.ThmBodyModeled
import IxC.Kernel.Semantics.Inductives.DeclNative
import IxC.Kernel.Verify.Extend.Inversions

/-! # Native checker stages under the opaque theorem view

Native normalization and typing observe exact constant signatures and definition bodies.
The transports retain each stage's actual result, including its normalized former and constructors.
-/

namespace IxVM.Refinement.Decl.ThmBodyView.Agrees

open Ix.Kernel Ix.Kernel.Semantics

variable {md : Mode} {source target : Env md} (h : Agrees source target)

include h

theorem constsResolveShallow (e : Expr md) :
    e.constsResolveShallow source = e.constsResolveShallow target :=
  h.constsResolve e.eraseFvarTypes

theorem whnfTelescope (mode : CheckMode) (fuel i n : Nat) (e : Expr md) :
    Ix.Kernel.whnfTelescope (fueledOps mode fuel) source i n e =
      Ix.Kernel.whnfTelescope (fueledOps mode fuel) target i n e := by
  induction n generalizing i e with
  | zero => simp only [Ix.Kernel.whnfTelescope, fueledOps_whnf, h.whnf]
  | succ n ih => simp only [Ix.Kernel.whnfTelescope, fueledOps_whnf, h.whnf, ih]

theorem checkSumTele (mode : CheckMode) (fuel : Nat) (cv : ConstantVal md)
    (n : Nat) (cvA : ConstantVal md) :
    Ix.Kernel.checkSumTele (fueledOps mode fuel) source cv n cvA =
      Ix.Kernel.checkSumTele (fueledOps mode fuel) target cv n cvA := by
  simp only [Ix.Kernel.checkSumTele, h.whnfTelescope, h.checkConstantVal]

theorem checkStructFieldSortsI (mode : CheckMode) (fuel : Nat) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs indices : List (Expr md)) (n : Nat) :
    Ix.Kernel.checkStructFieldSortsI (fueledOps mode fuel) source isProp large s nP fvs indices n =
      Ix.Kernel.checkStructFieldSortsI (fueledOps mode fuel) target isProp large s nP fvs indices n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Ix.Kernel.checkStructFieldSortsI, fueledOps_inferType, fueledOps_ensureSort,
      h.inferTypeCore, h.ensureSortCore, ih]

theorem checkStructDomsAt (mode : CheckMode) (fuel off : Nat) (fvs doms : List (Expr md)) (n : Nat) :
    Ix.Kernel.checkStructDomsAt (fueledOps mode fuel) source off fvs doms n =
      Ix.Kernel.checkStructDomsAt (fueledOps mode fuel) target off fvs doms n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Ix.Kernel.checkStructDomsAt, fueledOps_isDefEq, h.isDefEqCore, ih]

theorem normPosDom (mode : CheckMode) (fuel : Nat) (T : Key md) (d steps : Nat) (e : Expr md) :
    Ix.Kernel.normPosDom (fueledOps mode fuel) source T d steps e =
      Ix.Kernel.normPosDom (fueledOps mode fuel) target T d steps e := by
  induction steps generalizing d e with
  | zero => rfl
  | succ steps ih => simp only [Ix.Kernel.normPosDom, fueledOps_whnf, h.whnf, ih]

theorem normFieldDoms (mode : CheckMode) (fuel : Nat) (T : Key md) (i n : Nat) (e : Expr md) :
    Ix.Kernel.normFieldDoms (fueledOps mode fuel) source T i n e =
      Ix.Kernel.normFieldDoms (fueledOps mode fuel) target T i n e := by
  induction n generalizing i e with
  | zero => rfl
  | succ n ih => cases e <;> simp only [Ix.Kernel.normFieldDoms, h.normPosDom, ih]

theorem normCtorVal (mode : CheckMode) (fuel : Nat) (T : Key md) (nP nF : Nat)
    (cv cvA : ConstantVal md) :
    Ix.Kernel.normCtorVal (fueledOps mode fuel) source T nP nF cv cvA =
      Ix.Kernel.normCtorVal (fueledOps mode fuel) target T nP nF cv cvA := by
  simp only [Ix.Kernel.normCtorVal, h.normFieldDoms, h.checkConstantVal]

theorem checkSumCtor {source₀ target₀ : Env md} (h₀ : Agrees source₀ target₀)
    (mode : CheckMode) (fuel : Nat) (T : Key md) (lps : List LevelParam)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal md) (nF : Nat) (cvTa : ConstantVal md) :
    Ix.Kernel.checkSumCtor (fueledOps mode fuel) source₀ source T lps nP nIdx resSort isProp large
      cvC nF cvTa =
    Ix.Kernel.checkSumCtor (fueledOps mode fuel) target₀ target T lps nP nIdx resSort isProp large
      cvC nF cvTa := by
  simp only [Ix.Kernel.checkSumCtor, h.checkConstantVal, h.normCtorVal, h.checkStructDomsAt,
    h₀.constsResolve, h.checkStructFieldSortsI]

theorem checkSumCtors {source₀ target₀ : Env md} (h₀ : Agrees source₀ target₀)
    (mode : CheckMode) (fuel : Nat) (T : Key md) (lps : List LevelParam)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal md) (ctors : List (ConstantVal md × Nat)) :
    Ix.Kernel.checkSumCtors (fueledOps mode fuel) source₀ source T lps nP nIdx resSort isProp large cvTa ctors =
      Ix.Kernel.checkSumCtors (fueledOps mode fuel) target₀ target T lps nP nIdx resSort isProp large cvTa ctors := by
  induction ctors with
  | nil => rfl
  | cons c rest ih => simp only [Ix.Kernel.checkSumCtors, h.checkSumCtor h₀, ih]

theorem consSumCtors (nP : Nat) (ctors : List (ConstantVal md × Nat)) :
    Agrees (Ix.Kernel.consSumCtors nP ctors source) (Ix.Kernel.consSumCtors nP ctors target) := by
  induction ctors generalizing source target with
  | nil => exact h
  | cons c rest ih => exact ih (h.cons (.ctorInfo c.1 nP c.2))

theorem sumRules (name : Key md) (nP mI rP : Nat) (ty : Expr md)
    (ctors : List (ConstantVal md × Nat)) (rhss : List (Expr md)) :
    Ix.Kernel.sumRules source.find? name nP mI rP ty ctors rhss =
      Ix.Kernel.sumRules target.find? name nP mI rP ty ctors rhss := by
  induction ctors generalizing rhss with
  | nil => cases rhss <;> rfl
  | cons c rest ih => cases rhss <;> simp only [Ix.Kernel.sumRules, h.recRuleBits, ih]

theorem nativeOpenedOk (T : Key md) (lps : List LevelParam) (nP nIdx : Nat)
    (cty : Expr md) (nF : Nat) (kinds : List RecFieldKind) :
    Ix.Kernel.nativeOpenedOk source T lps nP nIdx cty nF kinds =
      Ix.Kernel.nativeOpenedOk target T lps nP nIdx cty nF kinds := by
  simp only [Ix.Kernel.nativeOpenedOk, h.constsResolveShallow]

theorem nativeFieldsOk (T : Key md) (lps : List LevelParam) (nP nIdx : Nat)
    (ctors : List (ConstantVal md × Nat)) (kinds : List (List RecFieldKind)) :
    Ix.Kernel.nativeFieldsOk source T lps nP nIdx ctors kinds =
      Ix.Kernel.nativeFieldsOk target T lps nP nIdx ctors kinds := by
  simp only [Ix.Kernel.nativeFieldsOk, h.nativeOpenedOk]

theorem checkNativeRules (rlps : List LevelParam) (T : Key md) (lps : List LevelParam)
    (elim : LevelParam) (large : Bool) (nP nIdx : Nat) (tty : Expr md)
    (ctors : List (Key md × Nat × Expr md × List Nat)) (recC : Key md) (rlvls : List Level) (n j : Nat) :
    Ix.Kernel.checkNativeRules (m := CheckM md) source rlps T lps elim large nP nIdx tty ctors recC rlvls n j =
      Ix.Kernel.checkNativeRules (m := CheckM md) target rlps T lps elim large nP nIdx tty ctors recC rlvls n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [Ix.Kernel.checkNativeRules, h.constsResolve, ih]

theorem checkNativeRec (mode : CheckMode) (fuel : Nat) (p : NativeParts md)
    (cvTa : ConstantVal md) (ctors : List (ConstantVal md × Nat)) :
    Ix.Kernel.checkNativeRec (fueledOps mode fuel) source p cvTa ctors =
      Ix.Kernel.checkNativeRec (fueledOps mode fuel) target p cvTa ctors := by
  simp only [Ix.Kernel.checkNativeRec, h.checkConstantVal, h.constsResolve,
    fueledOps_inferType, fueledOps_ensureSort, fueledOps_isDefEq,
    h.inferTypeCore, h.ensureSortCore, h.isDefEqCore,
    (h.cons _).checkNativeRules]

/-- The former stage returns the same checked signature and completed record over the new prefix. -/
theorem checkSumInd {mode : CheckMode} {fuel : Nat} {p p' : InductiveShape md}
    {capsOf : InductiveShape md → IndCaps md} {cvTa : ConstantVal md} {sourceOut : Env md}
    (checked : Ix.Kernel.checkSumInd (fueledOps mode fuel) source p capsOf = .ok (sourceOut, cvTa, p')) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      Ix.Kernel.checkSumInd (fueledOps mode fuel) target p capsOf = .ok (targetOut, cvTa, p') := by
  unfold Ix.Kernel.checkSumInd at checked
  obtain ⟨cv₀, hcv, rest⟩ := exceptBind_ok checked
  obtain ⟨pair, htele, rest⟩ := exceptBind_ok rest
  obtain ⟨cvA, level⟩ := pair
  dsimp only at rest
  obtain ⟨pair, hstrip, rest⟩ := exceptBind_ok rest
  obtain ⟨binders, body⟩ := pair
  dsimp only at rest
  by_cases shape : (body == Expr.sort level) = true
  · rw [ite_eq_left shape] at rest
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl, rfl⟩ := rest
    have hcv' := hcv
    have htele' := htele
    rw [h.checkConstantVal] at hcv'
    rw [h.checkSumTele] at htele'
    refine ⟨_, h.cons _, ?_⟩
    simp only [Ix.Kernel.checkSumInd, hcv', htele', hstrip,
      Bind.bind, Except.bind, shape, ↓reduceIte, Pure.pure, Except.pure]
  · rw [ite_eq_right shape] at rest
    cases rest

/-- A structure table is installed with the same generated bodies and guards. -/
theorem checkStructProjTable {T C : Key md} {lps : List LevelParam} {nP nF off : Nat}
    {resSort : Level} {guards : List Level} {cvCa : ConstantVal md} {sourceOut : Env md}
    (checked : Ix.Kernel.checkStructProjTable (m := CheckM md)
      T C lps nP nF resSort guards off cvCa source = .ok sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      Ix.Kernel.checkStructProjTable (m := CheckM md)
        T C lps nP nF resSort guards off cvCa target = .ok targetOut := by
  obtain ⟨bodies, hb, wellScoped, names, fresh, rfl⟩ := checkStructProjTable_inv checked
  have wellScoped' : bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined lps && b.constsResolve target && b.looseBVarsBounded (nP + 1)) = true := by
    simpa only [h.constsResolve] using wellScoped
  have names' : (List.range nF).all (fun j => (target.find? (projFnName T j)).isNone) = true := by
    simpa only [h.isNone] using names
  have fresh' : (target.find? (projTableName T)).isNone = true := by
    rw [← h.isNone, fresh]
    rfl
  refine ⟨_, h.cons _, ?_⟩
  simp only [Ix.Kernel.checkStructProjTable, hb, unwrapOr, Pure.pure, Except.pure,
    Bind.bind, Except.bind]
  rw [ite_eq_left wellScoped', ite_eq_left names', ite_eq_left fresh']

private theorem returnEnvironment {sourceOut : Env md}
    (checked : (pure source : CheckM md (Env md)) = .ok sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ (pure target : CheckM md (Env md)) = .ok targetOut := by
  cases checked
  exact ⟨target, h, rfl⟩

theorem checkNativeTable {p : NativeParts md} {ctors : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {sourceOut : Env md}
    (checked : Ix.Kernel.checkNativeTable (m := CheckM md) p ctors sortss source = .ok sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧
      Ix.Kernel.checkNativeTable (m := CheckM md) p ctors sortss target = .ok targetOut := by
  cases ctors with
  | nil => exact returnEnvironment h checked
  | cons ctor rest =>
    cases rest with
    | cons => exact returnEnvironment h checked
    | nil =>
      cases sortss with
      | nil => exact returnEnvironment h checked
      | cons sorts rest =>
        cases rest with
        | cons => exact returnEnvironment h checked
        | nil =>
          by_cases noIndices : (p.nIdx == 0) = true
          · simp only [Ix.Kernel.checkNativeTable, noIndices, ↓reduceIte] at checked ⊢
            exact h.checkStructProjTable checked
          · simp only [Ix.Kernel.checkNativeTable, noIndices] at checked ⊢
            exact returnEnvironment h checked

/-- The complete native run replays with the same normalized constants and generated rules. -/
theorem nativeRun {mode : CheckMode} {fuel : Nat} {p₀ : NativeParts md} {sourceOut : Env md}
    (run : DeclNativeRun mode fuel source p₀ sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ DeclNativeRun mode fuel target p₀ targetOut := by
  obtain ⟨distinct, isRec, source₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest,
    isorts, former, completed, ctors, classified, caps, elimination, opened, sorts,
    fields, rules, recursor, plain, table⟩ := run
  obtain ⟨target₁, h₁, former'⟩ := h.checkSumInd former
  have h₂ := h₁.consSumCtors p.nP ctorsA
  have hrules := h₂.sumRules cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss
  have hR : Agrees
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA source₁).find? cvRa.name
          p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) ::
          (Ix.Kernel.consSumCtors p.nP ctorsA source₁).consts⟩
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA target₁).find? cvRa.name
          p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) ::
          (Ix.Kernel.consSumCtors p.nP ctorsA target₁).consts⟩ := by
    rw [← hrules]
    exact h₂.cons _
  obtain ⟨targetOut, agreement, table'⟩ := hR.checkNativeTable table
  refine ⟨targetOut, agreement, distinct, isRec, target₁, cvTa, p₁, p, ctorsA, sortss, kinds,
    cvRa, rhss, tfvs, trest, isorts, former', completed, ?_, classified, caps,
    elimination, opened, ?_, ?_, rules, ?_, plain, table'⟩
  · simpa only [h₁.checkSumCtors h₁] using ctors
  · simpa only [h₁.checkStructFieldSortsI] using sorts
  · simpa only [h.nativeFieldsOk] using fields
  · simpa only [h₂.checkNativeRec] using recursor

end IxVM.Refinement.Decl.ThmBodyView.Agrees
