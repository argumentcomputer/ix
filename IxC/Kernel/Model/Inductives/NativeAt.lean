module

public import IxC.Kernel.Model.FoldLate
public import IxC.Kernel.Model.StoreRecShape
public import IxC.Kernel.Model.StoreFold
public import IxC.Kernel.Semantics.Inductives.DeclNativeExtJ
import IxC.Kernel.Model.Inductives.DeclNative

@[expose] public section

/-!
# The native route without a recursor record, at a given index count

`nativePartsNoRec?` (`Semantics/Inductives/DeclNativeJ.lean`) reads a one-type block without
its recursor record by appending a recursor slot whose argument sums are `0`. Where the
former's stored type is not a syntactic telescope ending in a sort (a former declared at a
definition, which reaches its telescope only after unfolding), the recogniser reads the index
count off the recursor record's argument sums (`nativeCounts?`), and the slot's sums read as no
count at all: such a block is not recognised, and `IndRoutesJ` has no route for it.

The stages of the route do not depend on the slot: `DeclNativeNoRecRunJ` reads the former at its
telescope constant, which the former's stage checks from scratch (`SumIndRunJ`), and may store
the declared former, definitionally equal to it, at a family with indices (`FormerStoredJ`).
The model of the install (`declNativeCoreJ`) is proved for the parts `nativeParts?` reads off
any block. This module therefore adds the route with the index count given:

* `nativeRecStubAt cvT nP nIdx nC`: the recursor slot whose argument sums carry the counts
  (`rulePrefix = nP + 1 + nC`, `majorIdx = rulePrefix + nIdx`); `nativePartsAt? nP nIdx block`
  reads the block with that slot appended. At a former that is a syntactic telescope the
  counts are read off the telescope, as before; otherwise the index count is `nIdx`.
* `NativeAtRunJ`: the recognised parts and `DeclNativeNoRecRunJ` at them; `IndRoutesAJ`:
  `IndRoutesJ` or this route.
* The model step (`declNativeAtJ`, `nativeAtStep_rulesJ`, the fold `foldRulesRoutesA`), the
  registry (`EnvModelN.declRunJA`, `EnvModelN.nativeAt`), and the store facts along a step of
  `IndRoutesAJ` (`storeInv_declRunJA`, `thmTyped_declRunJA`, `recK_declRunJA`,
  `etaTowers_declRunJA`, `recShape_declRunJA`, `tableBodies_declRunJA`, `declRunJA_envExt`).

Every theorem here reuses the no-recursor route's own lemmas; the recogniser enters them only
through `nativeParts?` at some block (`nativePartsAt?_parts`) and the recogniser's invariant
(`nativeRecog_at`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps
  NativeParts InductiveShape Declaration EtaFamiliesClosed EnvExt)

universe w

/-! ## Recognition at a given index count -/

/-- **The recursor slot carrying the counts**: the small eliminator's level shape under the
derived key (as `nativeRecStub`), no rule, and the argument sums of a recursor of `nP`
parameters, `nC` constructors and `nIdx` indices. -/
def nativeRecStubAt (cvT : ConstantVal md) (nP nIdx nC : Nat) : ConstantInfo md :=
  .recInfo ⟨Ix.Kernel.auxKey cvT.name .recursor, cvT.levelParams, .sort .zero⟩
    (nP + 1 + nC + nIdx) (nP + 1 + nC) []

/-- **A one-type block without its recursor record, read at the index count `nIdx`**: the
type former followed by constructors only, recognised as `nativeParts?` recognises it with the
slot `nativeRecStubAt` appended. -/
def nativePartsAt? (nPd nIdx : Nat) (block : List (ConstantInfo md)) :
    Option (NativeParts md) :=
  match block with
  | .indInfo cvT caps :: rest =>
    if rest.all (fun | .ctorInfo .. => true | _ => false) then
      Ix.Kernel.nativeParts? nPd
        (.indInfo cvT caps :: (rest ++ [nativeRecStubAt cvT nPd nIdx rest.length]))
    else none
  | _ => none

/-- The parts are `nativeParts?`'s at some block. -/
theorem nativePartsAt?_parts {nPd nIdx : Nat} {block : List (ConstantInfo md)}
    {p₀ : NativeParts md} (h : nativePartsAt? nPd nIdx block = some p₀) :
    ∃ blk : List (ConstantInfo md), Ix.Kernel.nativeParts? nPd blk = some p₀ := by
  unfold nativePartsAt? at h
  split at h
  · split at h
    · exact ⟨_, h⟩
    · exact nomatch h
  · exact nomatch h

/-- The recogniser's invariant at the parts. -/
theorem nativeRecog_at {nPd nIdx : Nat} {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (h : nativePartsAt? nPd nIdx block = some p₀) : NativeRecog p₀ :=
  let ⟨_, h'⟩ := nativePartsAt?_parts h
  nativeRecog_of h'

/-! ## The route -/

/-- **The native route without a recursor record, at a given index count**, over a package:
the parts read off the block at some index count, and the stages of `DeclNativeNoRecRunJ`. -/
def NativeAtRunJ (J : Judgements md) (env : Env md) (block : List (ConstantInfo md)) (nP : Nat)
    (env₂ : Env md) : Prop :=
  ∃ (nIdx : Nat) (p₀ : NativeParts md),
    nativePartsAt? nP nIdx block = some p₀ ∧ DeclNativeNoRecRunJ J env p₀ env₂

/-- **An inductive block's routes, with the route at a given index count.** -/
def IndRoutesAJ (J : Judgements md) (env : Env md) (block : List (ConstantInfo md)) (nP : Nat)
    (env₂ : Env md) : Prop :=
  IndRoutesJ J env block nP env₂ ∨ NativeAtRunJ J env block nP env₂

/-- The route extends the environment. -/
theorem nativeAtRunJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} (h : NativeAtRunJ J env block nP env₂) :
    EnvExt env env₂ :=
  let ⟨_, _, _, hN⟩ := h
  declNativeNoRecRunJ_envExt hN

/-- The route keeps the η families closed. -/
theorem nativeAtRunJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} (hE : EtaFamiliesClosed env)
    (h : NativeAtRunJ J env block nP env₂) : EtaFamiliesClosed env₂ :=
  let ⟨_, _, _, hN⟩ := h
  declNativeNoRecRunJ_etaClosed hE hN

/-- The routes extend the environment. -/
theorem indRoutesAJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nP : Nat} (h : IndRoutesAJ J env block nP env₂) :
    EnvExt env env₂ := by
  rcases h with h | h
  · exact indRoutesJ_envExt h
  · exact nativeAtRunJ_envExt h

/-- Every declaration step over the routes extends the environment. -/
theorem declRunJA_envExt {J : Judgements md} {env env₂ : Env md} {d : Declaration md}
    (hrun : DeclRunJ J (IndRoutesAJ J env) env d env₂) : EnvExt env env₂ :=
  declRunJ_envExt (fun hb => basisRun_envExt hb) (fun hI => indRoutesAJ_envExt hI) hrun

/-- **A step over the routes is a step over `IndRoutesJ`, or the route at a given index
count** at an unpinned block. -/
theorem declRunJA_cases {J : Judgements md} {env env₂ : Env md} {d : Declaration md}
    (h : DeclRunJ J (IndRoutesAJ J env) env d env₂) :
    DeclRunJ J (IndRoutesJ J env) env d env₂ ∨
      ∃ (block : List (ConstantInfo md)) (nP : Nat), d = .indDecl block nP ∧
        Ix.Kernel.basisPinHit block = none ∧ NativeAtRunJ J env block nP env₂ := by
  cases d
  case indDecl block nP =>
    cases hpin : Ix.Kernel.basisPinHit block with
    | some kind =>
      left
      simp only [DeclRunJ, hpin] at h ⊢
      exact h
    | none =>
      simp only [DeclRunJ, hpin] at h
      rcases h with h | h
      · left
        simp only [DeclRunJ, hpin]
        exact h
      · exact Or.inr ⟨block, nP, rfl, hpin, h⟩
  all_goals exact Or.inl h

/-! ## The model step -/

section Model

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The P carrier survives the route**, over a judgement package (`declNativeCoreJ` with the
table over the constructors, at the parts `nativeParts?` reads off the block with the slot
appended). -/
theorem declNativeAtJ {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    (hI : JudgeInv J)
    (hS : ∀ {e : Env md} (m : EnvModelM V μ e) ψ, SortClaimJ J m.base2 ψ)
    {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    (mp : EnvModelM V μ env) (hE : EtaFamiliesClosed env)
    (h : NativeAtRunJ J env block nP env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ThmValOk mp → ModelExt mp mp₂ := by
  obtain ⟨nIdx, p₀, hdp, hnd₀, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest,
    isorts, hInd, hp, hCtors, hK, hcaps, hopT2, hsorts, hFOk, hTbl, hFR⟩ := h
  obtain ⟨_, hdp'⟩ := nativePartsAt?_parts hdp
  obtain ⟨mp₂, hext⟩ := declNativeCoreJ hfr hJ hI hS mp hE hdp' hnd₀ hInd hp hCtors hK hcaps
    hopT2 hsorts hFOk hFR (Or.inr hTbl)
  exact ⟨mp₂, fun hthm => (hext hthm).1⟩

/-- **The route over derivations**: the two facts `foldRules` asks of the inductive kind. -/
theorem nativeAtStep_rulesJ {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    (mp : EnvModelM V μ env) (hT : ThmValOk mp) (hE : EtaFamiliesClosed env)
    (h : NativeAtRunJ rulesJ env block nP env₂) :
    EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  refine ⟨nativeAtRunJ_etaClosed hE h, ?_⟩
  obtain ⟨mp₂, hext⟩ := declNativeAtJ judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m)
    judgeInv_rulesJ (fun m φ => sortClaim_rulesJ_of m φ) mp hE h
  exact ⟨mp₂, hext hT⟩

/-- **The routes over derivations**: the four routes of `IndRoutesJ` and the route at a given
index count. -/
theorem indRoutesAJ_step_rulesJ {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    (mp : EnvModelM V μ env) (hT : ThmValOk mp) (hE : EtaFamiliesClosed env)
    (h : IndRoutesAJ rulesJ env block nP env₂) :
    EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  rcases h with (⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT') | hA
  · exact nativeStep_rulesJ mp hT hE hdp hN
  · exact modeledStep_rulesJ mp hE hM
  · exact nativeNoRecStep_rulesJ mp hT hE hdp hN
  · exact twinStep_rulesJ mp hE hT'
  · exact nativeAtStep_rulesJ mp hT hE hA

/-- **The fold at the derivation package over the routes** (`IndRoutesAJ`). -/
theorem foldRulesRoutesA {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ (IndRoutesAJ rulesJ) env ds env' → EnvModelT V μ env → EnvModelT V μ env' :=
  foldRules fun {_} mp hT hE {_ _ _} h => indRoutesAJ_step_rulesJ mp hT hE h

end Model

/-! ## The registry -/

/-- **Every declaration step over the routes keeps the registry** (no registration). -/
theorem EnvModelN.declRunJA {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md} {d : Declaration md} {R : NativeFam md → Prop}
    (h : EnvModelN V μ env R) (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    EnvModelN V μ env₂ R :=
  EnvModelN.step V h fun mp hT hE =>
    declStep_preservesJ rulesJ_thmValue mp (judgeSound_rulesJ_of mp) (axiomBits_rulesJ env) hE
      (fun hI => indRoutesAJ_step_rulesJ mp hT hE hI) hrun

/-- **The route registers its family**: `EnvModelN.nativeCore` with the no-recursor tail, at the
parts read off the block at a given index count. -/
theorem EnvModelN.nativeAt {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nPd nIdx : Nat} {p₀ : NativeParts md}
    {R : NativeFam md → Prop} (h : EnvModelN V μ env R)
    (hdp : nativePartsAt? nPd nIdx block = some p₀)
    {isRec : Bool} {cvS cvTa : ConstantVal md} {caps : IndCaps md} {p₁ : InductiveShape md}
    {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {kinds : List (List RecFieldKind)}
    {tfvs : List (Expr md)} {trest : Expr md} {isorts : List Level}
    (hnd₀ : (p₀.ctors.map (·.1.name)).Nodup)
    (hInd : SumIndRunJ rulesJ env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      ⟨.indInfo cvS caps :: env.consts⟩ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩
      ⟨.indInfo cvS caps :: env.consts⟩
      p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors ctorsA
      sortss)
    (hK : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM md) p.cvT.name p.cvT.levelParams
      p.nP p.nIdx ctorsA = .ok kinds)
    (hcaps : Ix.Kernel.nativeCaps p = Ix.Kernel.nativeCapsAt p₁ isRec)
    (hopT2 : Ix.Kernel.openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest))
    (hsorts : FieldSortsJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩ true false p.resSort p.nP
      (tfvs.drop p.nP) [] p.nIdx isorts)
    (hFOk : Ix.Kernel.nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true)
    (hFR : FormerReadJ ⟨.indInfo cvS caps :: env.consts⟩ p cvTa ctorsA)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
        (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩) = .ok env₂) :
    EnvModelN V μ env₂ (fun f => R f ∨ f = ⟨p, cvS, cvTa, ctorsA⟩) :=
  let ⟨_, hdp'⟩ := nativePartsAt?_parts hdp
  EnvModelN.nativeCore V h hdp' hnd₀ hInd hp hCtors hK hcaps hopT2 hsorts hFOk hFR (Or.inr hTbl)

/-! ## The store facts along a step of the routes -/

/-- The route keeps the store invariant. -/
theorem storeInv_nativeAtRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat} (h : StoreInv env)
    (hA : NativeAtRunJ J env block nP env₂) : StoreInv env₂ :=
  let ⟨_, _, hdp, hN⟩ := hA
  storeInv_declNativeNoRecRunJ hfr (nativeRecog_at hdp) h hN

/-- The routes keep the store invariant. -/
theorem storeInv_indRoutesAJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat} (h : StoreInv env)
    (hr : IndRoutesAJ J env block nP env₂) : StoreInv env₂ := by
  rcases hr with hr | hr
  · exact storeInv_indRoutesJ hfr h hr
  · exact storeInv_nativeAtRunJ hfr h hr

/-- **One declaration step over the routes keeps the store invariant.** -/
theorem storeInv_declRunJA {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {d : Declaration md} (h : StoreInv env)
    (hrun : DeclRunJ J (IndRoutesAJ J env) env d env₂) : StoreInv env₂ :=
  storeInv_declRunJ hfr (fun hI => storeInv_indRoutesAJ hfr h hI) h hrun

/-- **One declaration step over the routes keeps the stored theorems typed.** -/
theorem thmTyped_declRunJA {env env₂ : Env md} {d : Declaration md} (h : ThmTyped env)
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) : ThmTyped env₂ := by
  rcases declRunJA_cases hrun with h' | ⟨block, nP, rfl, -, _, _, -, hN⟩
  · exact thmTyped_declRunJ h h'
  · exact thmTyped_step_noThm (declNativeNoRecRunJ_envExt hN) h
      (nativeNoRec_newSat (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) hN)

/-- **One declaration step over the routes keeps the K facts.** -/
theorem recK_declRunJA {env env₂ : Env md} {d : Declaration md} (h : StoreInv env)
    (hK : RecK env) (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    RecK env₂ := by
  rcases declRunJA_cases hrun with h' | ⟨block, nP, rfl, -, _, _, -, hN⟩
  · exact recK_declRunJ h hK h'
  · exact recK_step_noRec h hK (declNativeNoRecRunJ_envExt hN).find
      (nativeNoRec_newSat (fun _ _ _ _ _ _ heq => nomatch heq)
        (fun _ _ _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hN)

/-- **One declaration step over the routes keeps the η families' tables.** -/
theorem etaTowers_declRunJA {env env₂ : Env md} {d : Declaration md} (h : EtaTowers env)
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) : EtaTowers env₂ := by
  rcases declRunJA_cases hrun with h' | ⟨block, nP, rfl, -, _, _, -, hN⟩
  · exact etaTowers_declRunJ h h'
  · refine etaTowers_step (declNativeNoRecRunJ_envExt hN) h ?_
    obtain ⟨-, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp, hCtors, -,
      -, -, -, -, hTbl, -⟩ := hN
    exact nativeFormer_towers hInd hp hCtors
      (consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)) hTbl

/-- **One declaration step over the routes keeps the recursors' shape facts.** -/
theorem recShape_declRunJA {env env₂ : Env md} {d : Declaration md} (h : StoreInv env)
    (hS : RecShape env) (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    RecShape env₂ := by
  rcases declRunJA_cases hrun with h' | ⟨block, nP, rfl, -, _, _, -, hN⟩
  · exact recShape_declRunJ h hS h'
  · exact recShape_step_noRec h hS (declNativeNoRecRunJ_envExt hN).find
      (nativeNoRec_newSat (fun _ _ _ _ _ _ heq => nomatch heq)
        (fun _ _ _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hN)

/-- **One declaration step over the routes keeps every stored projection table the
generator's.** -/
theorem tableBodies_declRunJA {env env₂ : Env md} {d : Declaration md} (hS : StoreInv env)
    (h : TableBodies env) (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    TableBodies env₂ := by
  rcases declRunJA_cases hrun with h' | ⟨block, nP, rfl, -, nIdx, p₀, hdp, hN⟩
  · exact tableBodies_declRunJ hS h h'
  · have hfr : ∀ e : Env md, JudgeFrames rulesJ e := fun e => judgeFrames_rulesJ e
    refine tableBodies_step (declNativeNoRecRunJ_envExt hN).find h ?_
    obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp, hCtors,
      -, -, -, -, -, hTbl, -⟩ := hN
    have hF := nativeFront hfr hS (nativeRecog_at hdp) hnd hInd hp hCtors
    obtain ⟨_, _, _, _, _, _, ⟨_, henv₁, _⟩, _, _⟩ := hInd.shape
    have hXno : NewSat env (Ix.Kernel.consSumCtors p.nP ctorsA env₁) NotProj := by
      subst henv₁
      exact (NewSat.cons (fun _ heq => nomatch heq)).trans
        (consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq))
    exact nativeTable_bodies hCtors (fun j cA hj => (hF.ctor j cA hj).1) hXno hTbl

end Ix.Kernel.Model
