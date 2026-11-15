import IxVMRefinement.Decl.ThmBodyView
import IxC.Kernel.Verify.Knot

/-! # Core checking under opaque theorem-body changes

The core reads theorem signatures but never their opaque values. The following congruences
keep all terms, definition bodies, hints, and judgement results exact under `Agrees`.
-/

namespace IxVM.Refinement.Decl.ThmBodyView.Agrees

open Ix.Kernel

variable {md : Mode} {source target : Env md} (_h : Agrees source target)

include _h

theorem reduceNat (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.reduceNat r source d e = Ix.Kernel.reduceNat r target d e := by
  simp only [Ix.Kernel.reduceNat, _h.natLitSupported, _h.natOpStored]

omit _h in
theorem iotaCerts (_h : Agrees source target) (r : CoreFns md (CheckM md)) (d : Nat) (lic : Bool)
    (e : Expr md) (args : List (Expr md)) :
    Ix.Kernel.iotaCerts r source d lic e args = Ix.Kernel.iotaCerts r target d lic e args := by
  induction args generalizing e with
  | nil => rfl
  | cons arg rest ih => cases e <;> simp only [Ix.Kernel.iotaCerts, ih]

omit _h in
theorem defEqList (_h : Agrees source target) (r : CoreFns md (CheckM md)) (d : Nat) (as bs : List (Expr md)) :
    Ix.Kernel.defEqList r source d as bs = Ix.Kernel.defEqList r target d as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih => cases bs <;> simp only [Ix.Kernel.defEqList, ih]

theorem iotaIndexOk (r : CoreFns md (CheckM md)) (d mI rP nP : Nat)
    (ty : Expr md) (args indices : List (Expr md)) :
    Ix.Kernel.iotaIndexOk r source d mI rP nP ty args indices =
      Ix.Kernel.iotaIndexOk r target d mI rP nP ty args indices := by
  simp only [Ix.Kernel.iotaIndexOk, _h.defEqList r]

theorem proofIrrel (r : CoreFns md (CheckM md)) (d : Nat) (a b : Expr md) :
    Ix.Kernel.proofIrrel r source d a b = Ix.Kernel.proofIrrel r target d a b := by
  simp only [Ix.Kernel.proofIrrel, _h.isUnitLikeTy]

theorem propIrrel (r : CoreFns md (CheckM md)) (d : Nat) (a b : Expr md) :
    Ix.Kernel.propIrrel r source d a b = Ix.Kernel.propIrrel r target d a b := by
  simp only [Ix.Kernel.propIrrel, _h.notProofFast, _h.isProofFast]

theorem structEtaProjCerts (r : CoreFns md (CheckM md)) (d : Nat)
    (T : Key md) (us : List Level) (args : List (Expr md)) (b : Expr md)
    (lps : List LevelParam) (fields : List Nat) :
    Ix.Kernel.structEtaProjCerts r source d T us args b lps fields =
      Ix.Kernel.structEtaProjCerts r target d T us args b lps fields := by
  induction fields with
  | nil => rfl
  | cons i fields ih =>
    simp only [Ix.Kernel.structEtaProjCerts, _h.iotaCerts r, ih]
    have rel := _h (projFnName T i)
    generalize hs : source.find? (projFnName T i) = left at rel ⊢
    generalize ht : target.find? (projFnName T i) = right at rel ⊢
    cases rel <;> rfl

theorem structEtaCertWith (mode : CheckMode) (r : CoreFns md (CheckM md))
    (d : Nat) (a b ty : Expr md) :
    Ix.Kernel.structEtaCertWith mode r source d a b ty =
      Ix.Kernel.structEtaCertWith mode r target d a b ty := by
  simp only [Ix.Kernel.structEtaCertWith, _h.towerSlotsAll, _h.recSlotsAll,
    _h.iotaCerts r, _h.structEtaProjCerts r, _h.defEqList r, _h.etaProjs]
  cases a.getAppFn with
  | const c us =>
    dsimp only
    have rel := _h c
    generalize hs : source.find? c = left at rel ⊢
    generalize ht : target.find? c = right at rel ⊢
    cases rel with
    | thm => rfl
    | same =>
      cases left with
      | none => rfl
      | some ci =>
        cases ci with
        | ctorInfo cv nP nF =>
          dsimp only
          split
          · cases ty.getAppFn with
            | const T levels =>
              dsimp only
              have rel := _h T
              generalize hs : source.find? T = left at rel ⊢
              generalize ht : target.find? T = right at rel ⊢
              cases rel <;> rfl
            | _ => rfl
          · rfl
        | _ => rfl
  | _ => rfl

theorem structEtaCert (mode : CheckMode) (r : CoreFns md (CheckM md))
    (d : Nat) (a b : Expr md) :
    Ix.Kernel.structEtaCert mode r source d a b = Ix.Kernel.structEtaCert mode r target d a b := by
  simp only [Ix.Kernel.structEtaCert, _h.etaCtorShape, _h.structEtaCertWith mode r]

theorem structUnitCert (r : CoreFns md (CheckM md)) (d : Nat) (a b : Expr md) :
    Ix.Kernel.structUnitCert r source d a b = Ix.Kernel.structUnitCert r target d a b := by
  simp only [Ix.Kernel.structUnitCert, _h.iotaCerts r]
  congr 1
  funext inferred
  congr 1
  funext reduced
  cases reduced.getAppFn with
  | const T levels =>
    dsimp only
    have rel := _h T
    generalize hs : source.find? T = left at rel ⊢
    generalize ht : target.find? T = right at rel ⊢
    cases rel <;> rfl
  | _ => rfl

omit _h in
theorem etaCert (_h : Agrees source target) (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat)
    (ty body : Expr md) (bm : BinderMeta) (b : Expr md) :
    Ix.Kernel.etaCert mode r source d ty body bm b =
      Ix.Kernel.etaCert mode r target d ty body bm b := rfl

theorem stuckIrrel (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat) (a b : Expr md) :
    Ix.Kernel.stuckIrrel mode r source d a b = Ix.Kernel.stuckIrrel mode r target d a b := by
  simp only [Ix.Kernel.stuckIrrel, _h.structEtaCert mode r, _h.structUnitCert r, _h.proofIrrel r]

theorem majorToCtor (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat)
    (name : Key md) (rules : List (RecRule md)) (major : Expr md) :
    Ix.Kernel.majorToCtor mode r source d name rules major =
      Ix.Kernel.majorToCtor mode r target d name rules major := by
  unfold Ix.Kernel.majorToCtor
  rw [_h.isCtorApp]
  split
  · rfl
  · cases rules with
    | nil => rfl
    | cons rule rest =>
      cases rest with
      | cons => rfl
      | nil =>
        dsimp only
        have rel := _h rule.ctor
        generalize hs : source.find? rule.ctor = left at rel ⊢
        generalize ht : target.find? rule.ctor = right at rel ⊢
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
                dsimp only
                have rel := _h T
                generalize hs : source.find? T = left at rel ⊢
                generalize ht : target.find? T = right at rel ⊢
                cases rel <;>
                  simp only [_h.iotaCerts r, _h.proofIrrel r,
                    _h.structEtaCertWith mode r, _h.etaFabArgsE, _h.andRescueSlots]
              | _ => rfl
            | _ => rfl

theorem litMajorToCtor (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.litMajorToCtor r source d e = Ix.Kernel.litMajorToCtor r target d e := by
  simp only [Ix.Kernel.litMajorToCtor, Ix.Kernel.litToCtorIfNat,
    _h.strLitSupported, _h.natLitSupported]

theorem projLitToCtor (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.projLitToCtor r source d e = Ix.Kernel.projLitToCtor r target d e := by
  simp only [Ix.Kernel.projLitToCtor, _h.strLitSupported]

theorem prepareMajor (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat)
    (name : Key md) (rules : List (RecRule md)) (major : Expr md) :
    Ix.Kernel.prepareMajor mode r source d name rules major =
      Ix.Kernel.prepareMajor mode r target d name rules major := by
  simp only [Ix.Kernel.prepareMajor, _h.majorToCtor mode r, _h.litMajorToCtor r]

theorem iotaRec (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.iotaRec mode r source d e = Ix.Kernel.iotaRec mode r target d e := by
  simp only [Ix.Kernel.iotaRec, _h.prepareMajor mode r, _h.iotaCerts r,
    _h.iotaIndexOk r, _h.defEqList r]
  cases e.getAppFn with
  | const c levels =>
    dsimp only
    have rel := _h c
    generalize hs : source.find? c = left at rel ⊢
    generalize ht : target.find? c = right at rel ⊢
    cases rel with
    | thm => rfl
    | same =>
      cases left with
      | none => rfl
      | some ci =>
        cases ci with
        | recInfo cv mI rP rules =>
          dsimp only
          split
          · congr 1
            funext major
            cases major.getAppFn with
            | const ctor ctorLevels =>
              dsimp only
              have rel := _h ctor
              generalize hs : source.find? ctor = left at rel ⊢
              generalize ht : target.find? ctor = right at rel ⊢
              cases rel <;> rfl
            | _ => rfl
          · rfl
        | _ => rfl
  | _ => rfl

theorem projCert (r : CoreFns md (CheckM md)) (d : Nat) (lic : Bool)
    (c : Key md) (levels : List Level) (args : List (Expr md)) :
    Ix.Kernel.projCert r source d lic c levels args = Ix.Kernel.projCert r target d lic c levels args := by
  simp only [Ix.Kernel.projCert, _h.iotaCerts r]
  have rel := _h c
  generalize hs : source.find? c = left at rel ⊢
  generalize ht : target.find? c = right at rel ⊢
  cases rel <;> rfl

theorem projCertAt (r : CoreFns md (CheckM md)) (d : Nat) (verified lic : Bool)
    (c : Key md) (levels : List Level) (args : List (Expr md)) :
    Ix.Kernel.projCertAt r source d verified lic c levels args =
      Ix.Kernel.projCertAt r target d verified lic c levels args := by
  simp only [Ix.Kernel.projCertAt, _h.projCert r]

theorem whnfCoreBody (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.whnfCoreBody mode r source d e = Ix.Kernel.whnfCoreBody mode r target d e := by
  simp only [Ix.Kernel.whnfCoreBody, _h.iotaRec mode r, _h.projLitToCtor r,
    _h.findProj, _h.projCertAt r]

theorem whnfStep (r : CoreFns md (CheckM md)) (d : Nat) (cont : Expr md → CheckM md (Expr md))
    (e : Expr md) :
    Ix.Kernel.whnfStep r source d cont e = Ix.Kernel.whnfStep r target d cont e := by
  simp only [Ix.Kernel.whnfStep, _h.reduceNat r, _h.unfoldDefinition]

theorem whnfLoop (r : CoreFns md (CheckM md)) (d fuel : Nat) (e : Expr md) :
    Ix.Kernel.whnfLoop r source d fuel e = Ix.Kernel.whnfLoop r target d fuel e := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
    have heq := funext ih
    simp only [Ix.Kernel.whnfLoop, heq, _h.whnfStep r]

theorem whnfBody (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.whnfBody r source d e = Ix.Kernel.whnfBody r target d e := by
  simp only [Ix.Kernel.whnfBody, _h.whnfLoop r]

theorem inferBody (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.inferBody mode r source d e = Ix.Kernel.inferBody mode r target d e := by
  simp only [Ix.Kernel.inferBody, Ix.Kernel.ensureSort,
    _h.natLitSupported, _h.strLitSupported, _h.findProj]
  cases e with
  | const name levels =>
    dsimp only
    have rel := _h name
    generalize hs : source.find? name = left at rel ⊢
    generalize ht : target.find? name = right at rel ⊢
    cases rel <;> rfl
  | lit literal => cases literal <;> rfl
  | _ => rfl

theorem inferBodyIO (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.inferBodyIO mode r source d e = Ix.Kernel.inferBodyIO mode r target d e := by
  simp only [Ix.Kernel.inferBodyIO, Ix.Kernel.ensureSort,
    _h.natLitSupported, _h.strLitSupported, _h.findProj]
  cases e with
  | const name levels =>
    dsimp only
    have rel := _h name
    generalize hs : source.find? name = left at rel ⊢
    generalize ht : target.find? name = right at rel ⊢
    cases rel <;> rfl
  | lit literal => cases literal <;> rfl
  | _ => rfl

theorem defeqSpine (r : CoreFns md (CheckM md)) (d : Nat) (a b : Expr md) :
    Ix.Kernel.defeqSpine r source d a b = Ix.Kernel.defeqSpine r target d a b := by
  simp only [Ix.Kernel.defeqSpine, _h.defEqList r]

theorem defeqStep (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat)
    (cont : Bool → Expr md → Expr md → CheckM md Bool) (pi : Bool) (a b : Expr md) :
    Ix.Kernel.defeqStep mode r source d cont pi a b =
      Ix.Kernel.defeqStep mode r target d cont pi a b := by
  simp only [Ix.Kernel.defeqStep, _h.propIrrel r, _h.reduceNat r,
    _h.unfoldableHead, _h.unfoldDefinition, _h.headHint, _h.defeqSpine r,
    _h.stuckIrrel mode r, _h.etaCert mode r, _h.defEqList r, _h.strLitSupported]

theorem defeqLoop (mode : CheckMode) (r : CoreFns md (CheckM md)) (d fuel : Nat)
    (pi : Bool) (a b : Expr md) :
    Ix.Kernel.defeqLoop mode r source d fuel pi a b =
      Ix.Kernel.defeqLoop mode r target d fuel pi a b := by
  induction fuel generalizing pi a b with
  | zero => rfl
  | succ fuel ih =>
    have heq := funext fun pi => funext fun a => funext fun b => ih pi a b
    simp only [Ix.Kernel.defeqLoop, heq, _h.defeqStep mode r]

theorem defeqBody (mode : CheckMode) (r : CoreFns md (CheckM md)) (d : Nat) (a b : Expr md) :
    Ix.Kernel.defeqBody mode r source d a b = Ix.Kernel.defeqBody mode r target d a b := by
  simp only [Ix.Kernel.defeqBody, _h.defeqLoop mode r]

theorem annotPwPi (r : CoreFns md (CheckM md)) (d : Nat) (body : Expr md) :
    Ix.Kernel.annotPwPi r source d body = Ix.Kernel.annotPwPi r target d body := by
  simp only [Ix.Kernel.annotPwPi, _h.typeSortPW, Ix.Kernel.ensureSort]

theorem annotPwLam (r : CoreFns md (CheckM md)) (d : Nat) (body : Expr md) :
    Ix.Kernel.annotPwLam r source d body = Ix.Kernel.annotPwLam r target d body := by
  simp only [Ix.Kernel.annotPwLam, _h.proofPW, Ix.Kernel.ensureSort]

theorem annotateBody (r : CoreFns md (CheckM md)) (d : Nat) (e : Expr md) :
    Ix.Kernel.annotateBody r source d e = Ix.Kernel.annotateBody r target d e := by
  simp only [Ix.Kernel.annotateBody, _h.natLitSupported, _h.strLitSupported,
    _h.annotPwPi r, _h.annotPwLam r, _h.findProj, Ix.Kernel.ensureSort]

/-- Opaque theorem-body changes preserve every entry of the mutually recursive pure core. -/
theorem coreKnot (mode : CheckMode) (wrap : CoreFns md (CheckM md) → CoreFns md (CheckM md))
    (fuel : Nat) : Ix.Kernel.coreKnot mode source wrap fuel = Ix.Kernel.coreKnot mode target wrap fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [Ix.Kernel.coreKnot, ih, _h.whnfCoreBody, _h.whnfBody, _h.inferBody,
      _h.defeqBody, _h.annotateBody, _h.inferBodyIO]

/-- The accepted core operations have identical results under the checker view. -/
theorem pureFns (mode : CheckMode) (fuel : Nat) :
    Ix.Kernel.pureFns mode source fuel = Ix.Kernel.pureFns mode target fuel :=
  _h.coreKnot mode id fuel

theorem whnfCore (mode : CheckMode) (fuel depth : Nat) (e : Expr md) :
    Ix.Kernel.whnfCore mode source fuel depth e = Ix.Kernel.whnfCore mode target fuel depth e := by
  simp only [Ix.Kernel.whnfCore, _h.pureFns]

theorem whnf (mode : CheckMode) (fuel depth : Nat) (e : Expr md) :
    Ix.Kernel.whnf mode source fuel depth e = Ix.Kernel.whnf mode target fuel depth e := by
  simp only [Ix.Kernel.whnf, _h.pureFns]

theorem inferTypeCore (mode : CheckMode) (fuel depth : Nat) (e : Expr md) :
    Ix.Kernel.inferTypeCore mode source fuel depth e =
      Ix.Kernel.inferTypeCore mode target fuel depth e := by
  simp only [Ix.Kernel.inferTypeCore, _h.pureFns]

theorem inferTypeIO (mode : CheckMode) (fuel depth : Nat) (e : Expr md) :
    Ix.Kernel.inferTypeIO mode source fuel depth e = Ix.Kernel.inferTypeIO mode target fuel depth e := by
  simp only [Ix.Kernel.inferTypeIO, _h.pureFns]

theorem isDefEqCore (mode : CheckMode) (fuel depth : Nat) (a b : Expr md) :
    Ix.Kernel.isDefEqCore mode source fuel depth a b =
      Ix.Kernel.isDefEqCore mode target fuel depth a b := by
  simp only [Ix.Kernel.isDefEqCore, _h.pureFns]

theorem annotateCore (mode : CheckMode) (fuel depth : Nat) (e : Expr md) :
    Ix.Kernel.annotateCore mode source fuel depth e = Ix.Kernel.annotateCore mode target fuel depth e := by
  simp only [Ix.Kernel.annotateCore, _h.pureFns]

theorem ensureSortCore (mode : CheckMode) (fuel depth : Nat) (e : Expr md) :
    Ix.Kernel.ensureSortCore mode source fuel depth e =
      Ix.Kernel.ensureSortCore mode target fuel depth e := by
  simp only [Ix.Kernel.ensureSortCore, Ix.Kernel.ensureSort, _h.pureFns]

end IxVM.Refinement.Decl.ThmBodyView.Agrees
