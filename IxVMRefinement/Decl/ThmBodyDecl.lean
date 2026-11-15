import IxVMRefinement.Decl.ThmBodyCore
import IxC.Kernel.Semantics.DeclRun

/-! # Declaration fronts under opaque theorem-body changes

The reference checker retains raw theorem values, while the semantic store retains checked
annotations. These lemmas transport the actual checks using their common opaque checker view.
-/

namespace IxVM.Refinement.Decl.ThmBodyView.Agrees

open Ix.Kernel Ix.Kernel.Semantics

variable {md : Mode} {source target : Env md} (h : Agrees source target)

include h

theorem checkConstantVal (mode : CheckMode) (fuel : Nat) (cv : ConstantVal md) :
    Ix.Kernel.checkConstantVal (fueledOps mode fuel) source cv =
      Ix.Kernel.checkConstantVal (fueledOps mode fuel) target cv := by
  simp only [Ix.Kernel.checkConstantVal, fueledOps, h.isSome, h.annotateCore,
    h.constsResolve, h.inferTypeCore, h.ensureSortCore]

theorem constantValRun {mode : CheckMode} {fuel : Nat} {cv : ConstantVal md} {ty : Expr md}
    (run : ConstantValRun mode fuel source cv ty) : ConstantValRun mode fuel target cv ty := by
  simpa only [ConstantValRun, h.isNone, h.annotateCore, h.constsResolve,
    h.inferTypeCore, h.ensureSortCore] using run

theorem valueFrontRun {mode : CheckMode} {fuel : Nat} {cv : ConstantVal md}
    {value ty value' : Expr md} (run : ValueFrontRun mode fuel source cv value ty value') :
    ValueFrontRun mode fuel target cv value ty value' := by
  simpa only [ValueFrontRun, h.annotateCore, h.constsResolve, h.inferTypeCore,
    h.isDefEqCore] using run

theorem natOpGuard (c : Key md) : Ix.Kernel.natOpGuard source c = Ix.Kernel.natOpGuard target c := by
  have deps : (fun n => match source.find? n with
      | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
      | _ => false) = (fun n => match target.find? n with
      | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
      | _ => false) := funext fun n => h.observe n _ (by intros; rfl)
  simp only [Ix.Kernel.natOpGuard, h.natLitSupported, deps]
  rw [h.observe boolTrueName
    (fun q => match q with | some ci => ci.toConstantVal.levelParams.isEmpty | none => false)
    (by intros; rfl), h.observe boolFalseName
    (fun q => match q with | some ci => ci.toConstantVal.levelParams.isEmpty | none => false)
    (by intros; rfl)]

theorem natOpCod (c : Key md) (e : Expr md) :
    Ix.Kernel.natOpCod source c e = Ix.Kernel.natOpCod target c e := by
  unfold Ix.Kernel.natOpCod
  rw [h.observe boolName
    (fun q => match q with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .sort (.succ .zero)
      | none => false) (by intros; rfl)]

theorem natOpTyPinned (c : Key md) (ty : Expr md) :
    Ix.Kernel.natOpTyPinned source c ty = Ix.Kernel.natOpTyPinned target c ty := by
  have same := funext (h.natOpCod c)
  simp only [Ix.Kernel.natOpTyPinned, same]

theorem natOpStoredOk (n : Key md) :
    Ix.Kernel.natOpStoredOk source n = Ix.Kernel.natOpStoredOk target n := by
  apply h.inspect n
    (fun q => match q with
      | some (.defnInfo cv _ _) => cv.levelParams.isEmpty && Ix.Kernel.natOpTyPinned source n cv.type
      | _ => false)
    (fun q => match q with
      | some (.defnInfo cv _ _) => cv.levelParams.isEmpty && Ix.Kernel.natOpTyPinned target n cv.type
      | _ => false)
  · intro q
    cases q with
    | none => rfl
    | some ci => cases ci <;> simp only [h.natOpTyPinned]
  · intros; rfl

theorem divModEnvGuard (c : Key md) :
    Ix.Kernel.divModEnvGuard source c = Ix.Kernel.divModEnvGuard target c := by
  simp only [Ix.Kernel.divModEnvGuard, h.natOpGuard, funext h.natOpStoredOk]
  rw [h.observe eqName (fun q => q == some eqA) (by intros; rfl),
    h.observe boolTrueName
      (fun q => match q with | some ci => ci.toConstantVal.type == .const boolName [] | none => false)
      (by intros; rfl),
    h.observe boolFalseName
      (fun q => match q with | some ci => ci.toConstantVal.type == .const boolName [] | none => false)
      (by intros; rfl)]

theorem divModCertGuard (c : Key md) (value : Expr md) (hyps : List (Expr md))
    (eqE proof : Expr md) :
    Ix.Kernel.divModCertGuard source c value hyps eqE proof =
      Ix.Kernel.divModCertGuard target c value hyps eqE proof := by
  simp only [Ix.Kernel.divModCertGuard, h.constsResolve]

theorem divModCertsGuard (proofs : List (Expr md)) (c : Key md) (value : Expr md) :
    Ix.Kernel.divModCertsGuard proofs source c value =
      Ix.Kernel.divModCertsGuard proofs target c value := by
  simp only [Ix.Kernel.divModCertsGuard, h.divModCertGuard]

theorem checkDivModCerts (mode : CheckMode) (fuel : Nat) (c : Key md) (value : Expr md)
    (statements : List (List (Expr md) × Expr md)) (proofs : List (Expr md)) :
    Ix.Kernel.checkDivModCerts (fueledOps mode fuel) source c value statements proofs =
      Ix.Kernel.checkDivModCerts (fueledOps mode fuel) target c value statements proofs := by
  induction statements generalizing proofs with
  | nil => cases proofs <;> rfl
  | cons stmt statements ih =>
    cases proofs with
    | nil => rfl
    | cons proof proofs =>
      cases stmt
      simp only [Ix.Kernel.checkDivModCerts, fueledOps, h.divModCertGuard,
        h.annotateCore, h.inferTypeCore, h.isDefEqCore, ih]

theorem stdAxiomOk (cv : ConstantVal md) :
    Ix.Kernel.stdAxiomOk source cv = Ix.Kernel.stdAxiomOk target cv := by
  unfold Ix.Kernel.stdAxiomOk
  rw [h.observe eqName (fun q => decide (q = some eqA)) (by intros; rfl),
    h.observe iffName
      (fun q => match q with
        | some (.indInfo cvI _) => ConstantVal.matchesPin cvI iffA.toConstantVal
        | _ => false) (by intros; rfl),
    h.observe iffIntroName
      (fun q => match q with
        | some (.ctorInfo cvI 2 2) => ConstantVal.matchesPin cvI iffIntroA.toConstantVal
        | _ => false) (by intros; rfl),
    h.observe iffRecName
      (fun q => match q with
        | some (.recInfo cvI 4 4 _) => ConstantVal.matchesPin cvI iffRecA.toConstantVal
        | _ => false) (by intros; rfl),
    h.observe nonemptyName
      (fun q => match q with
        | some (.indInfo cvN _) => ConstantVal.matchesPin cvN nonemptyA.toConstantVal
        | _ => false) (by intros; rfl),
    h.observe nonemptyIntroName
      (fun q => match q with
        | some (.ctorInfo cvN 1 1) => ConstantVal.matchesPin cvN nonemptyIntroA.toConstantVal
        | _ => false) (by intros; rfl),
    h.observe nonemptyRecName
      (fun q => match q with
        | some (.recInfo cvN 3 3 _) => ConstantVal.matchesPin cvN nonemptyRecA.toConstantVal
        | _ => false) (by intros; rfl)]

/-- A successful definition run can be replayed with the same annotated type, value, and hint. -/
theorem declDefnRun {mode : CheckMode} {fuel : Nat} {cv : ConstantVal md}
    {value : Expr md} {hint : ReducibilityHint} {sourceOut : Env md}
    (run : DeclDefnRun mode fuel source cv value hint sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ DeclDefnRun mode fuel target cv value hint targetOut := by
  obtain ⟨ty, value', hcv, hv, rfl, hnat, hdiv⟩ := run
  let ci : ConstantInfo md := .defnInfo ⟨cv.name, cv.levelParams, ty⟩ value' hint
  refine ⟨⟨ci :: target.consts⟩, h.cons ci, ty, value', h.constantValRun hcv,
    h.valueFrontRun hv, rfl, ?_, ?_⟩
  · intro hn
    obtain ⟨guard, deps, eqns⟩ := hnat hn
    refine ⟨?_, ?_, ?_⟩
    · simpa only [(h.cons ci).natOpGuard] using guard
    · simpa only [funext (h.cons ci).natOpStoredOk] using deps
    · intro eq mem
      simpa only [h.isDefEqCore] using eqns eq mem
  · intro hd
    obtain ⟨guard, proofs, guarded, checked⟩ := hdiv hd
    refine ⟨?_, proofs, ?_, ?_⟩
    · simpa only [(h.cons ci).divModEnvGuard] using guard
    · simpa only [h.divModCertsGuard] using guarded
    · simpa only [h.checkDivModCerts] using checked

/-- An opaque run keeps the same checked signature and witness checks. -/
theorem declOpaqueRun {mode : CheckMode} {fuel : Nat} {cv : ConstantVal md}
    {value : Expr md} {sourceOut : Env md}
    (run : DeclOpaqueRun mode fuel source cv value sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ DeclOpaqueRun mode fuel target cv value targetOut := by
  obtain ⟨ty, value', hcv, hv, rfl⟩ := run
  exact ⟨_, h.cons _, ty, value', h.constantValRun hcv, h.valueFrontRun hv, rfl⟩

/-- The standard-axiom tests only inspect pinned signatures and non-theorem kinds. -/
theorem declAxiomRun {mode : CheckMode} {fuel : Nat} {cv : ConstantVal md} {sourceOut : Env md}
    (run : DeclAxiomRun mode fuel source cv sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ DeclAxiomRun mode fuel target cv targetOut := by
  rcases run with ⟨hq, rfl⟩ | ⟨ty, hcv, hrest⟩
  · exact ⟨target, h, Or.inl ⟨hq, rfl⟩⟩
  · rcases hrest with ⟨hstd, rfl⟩ | ⟨hstd, hprop, hchoice, hsorry, rfl⟩
    · exact ⟨_, h.cons _, Or.inr ⟨ty, h.constantValRun hcv,
        Or.inl ⟨by simpa only [h.stdAxiomOk] using hstd, rfl⟩⟩⟩
    · exact ⟨target, h, Or.inr ⟨ty, h.constantValRun hcv,
        Or.inr ⟨by simpa only [h.stdAxiomOk] using hstd, hprop, hchoice, hsorry, rfl⟩⟩⟩

theorem basisInstallRun {entries : List (ConstantInfo md)} {sourceOut : Env md}
    (run : BasisInstallRun source entries sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ BasisInstallRun target entries targetOut := by
  induction entries generalizing source target with
  | nil =>
    change sourceOut = source at run
    subst sourceOut
    exact ⟨target, h, rfl⟩
  | cons ci rest ih =>
    obtain ⟨fresh, restRun⟩ := run
    obtain ⟨targetOut, agreement, targetRun⟩ := ih (h.cons ci) restRun
    exact ⟨targetOut, agreement, by simpa only [h.isNone] using fresh, targetRun⟩

/-- Pinned blocks preserve exact installed entries and the pinned equality prerequisite. -/
theorem declBasisRun {kind : BasisKind} {sourceOut : Env md}
    (run : DeclBasisRun source kind sourceOut) :
    ∃ targetOut, Agrees sourceOut targetOut ∧ DeclBasisRun target kind targetOut := by
  obtain ⟨targetOut, agreement, installed⟩ := h.basisInstallRun run.2
  exact ⟨targetOut, agreement,
    (fun hk => h.find_nonThm (run.1 hk) (by intros; intro heq; cases heq)), installed⟩

end IxVM.Refinement.Decl.ThmBodyView.Agrees
