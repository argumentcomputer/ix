module

public import IxC.Kernel.Model.AxiomPin
public import IxC.Kernel.Model.BasisEq
public import IxC.Kernel.Model.BasisFalse
public import IxC.Kernel.Model.ThmVal
public import IxC.Kernel.Model.Fold

public section

/-!
# The declaration fold over a judgement package (lane l5)

`declStep_preserves` and `foldPM` (`Model/Fold.lean`) at the kernel's runs,
restated over a judgement package `J` (`Semantics/DeclJ.lean`) for the records
an IxVM refinement produces (obligation L5). The invariant is `EnvModelT`: the
kernel's `EnvModelM` with stored theorem values read to their leaves
(`ThmValOk`, `Model/ThmVal.lean`, the `thm_val` input of S2's rule N1), and the
η-family closure.

What the fold needs of `J`, at every prefix model with theorem values read:

* `JudgeSound J mp.base2` (`Model/JudgeSound.lean`): the facts the value-kind
  harvests read;
* `AxiomBitsJ J env` (`Model/AxiomBits.lean`): the pinned axioms' binder bits;
* `J.thmValue v v' = v'`: a theorem is stored with its annotated value
  (decision D11). The kernel's own package (`runJ`) stores the raw value, which
  is why the kernel's fold (`foldPM`) does not carry `ThmValOk`;
* the inductive kind's step (`hind`), which the restated inductive tier
  supplies (lane l5c).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal Declaration)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **A pinned basis block extends the model** (`basisStepPB_of` with the
extension exposed). -/
theorem basisStepExt {env : Env md} (mp : EnvModelM V μ env)
    {kind : Ix.Kernel.BasisKind} {env₂ : Env md}
    (h : DeclBasisRun env kind env₂) : ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  obtain ⟨hEq, hchain⟩ := h
  cases kind with
  | eqK => exact declBasisPB_eqK mp hchain
  | natK => exact declBasisPB_natK mp hchain
  | punitK => exact declBasisPB_punitK mp hchain
  | emptyK => exact declBasisPB_emptyK mp hchain
  | falseK => exact declBasisPB_falseK mp hchain
  | quotK => exact declBasisPB_quotK mp (hEq rfl) hchain

/-- **The per-declaration step over a package, by dispatch**: the η half and a
model extension. -/
theorem declStep_preservesJ {J : Judgements md}
    {Ind : List (ConstantInfo md) → Nat → Env md → Prop}
    {env env₂ : Env md} {d : Declaration md}
    (hTV : ∀ v v' : Expr md, J.thmValue v v' = v')
    (mp : EnvModelM V μ env) (hJ : JudgeSound J mp.base2) (hbits : AxiomBitsJ J env)
    (hE : EtaFamiliesClosed env)
    (hind : ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
      Ind block nP envI →
        EtaFamiliesClosed envI ∧ ∃ mp₂ : EnvModelM V μ envI, ModelExt mp mp₂)
    (hrun : DeclRunJ J Ind env d env₂) :
    EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  refine ⟨declEtaStepRunJ (fun h' => (hind h').1) hE hrun, ?_⟩
  cases d with
  | defnDecl cv value hint => exact harvestDefnJ mp hJ hrun
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, hvfr, rfl⟩ := hrun
    obtain ⟨A, mp₂, hac, hA⟩ := harvestThmJ mp hJ hcv hvfr
    refine ⟨mp₂, .step
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ (J.thmValue value value')) (A := A)
      .refl (Option.isNone_iff_eq_none.mp hcv.1)
      (fun _ _ _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)) ?_ hac⟩
    intro cv₂ v₂ heq
    injection heq with _ hv
    subst hv
    rw [hTV]
    exact ⟨hvfr.2.2.2.2.1, hA⟩
  | opaqueDecl cv value => exact harvestOpaqueJ mp hJ hrun
  | axiomDecl cv =>
    -- the `Quot.sound` arm installs nothing
    rcases hrun with ⟨-, rfl⟩ | hR
    · exact ⟨mp, .refl⟩
    obtain ⟨type', hcv, hbranch⟩ := hR
    rcases hbranch with ⟨hok, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact axiomStdJ mp hJ hbits hcv hok
    · exact ⟨mp, .refl⟩
  | basisDecl kind => exact basisStepExt mp hrun
  | quotDecl k cv =>
    cases k with
    | type => exact basisStepExt mp hrun
    | _ =>
      obtain rfl : env₂ = env := hrun
      exact ⟨mp, .refl⟩
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact basisStepExt mp hrun
    · exact (hind hrun).2

/-- **The restated fold invariant**: a model whose stored theorem values read to
their leaves, and the η-family closure. -/
@[expose] def EnvModelT (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env md) : Prop :=
  (∃ mp : EnvModelM V μ env, ThmValOk mp) ∧ EtaFamiliesClosed env

theorem EnvModelT.empty : EnvModelT V μ (Env.empty : Env md) :=
  ⟨⟨EnvModelM.empty V μ, ThmValOk.empty _⟩, EtaFamiliesClosed.empty⟩

/-- **The step keeps `EnvModelT`.** -/
theorem declStep_preservesT {J : Judgements md}
    {Ind : List (ConstantInfo md) → Nat → Env md → Prop}
    {env env₂ : Env md} {d : Declaration md}
    (hTV : ∀ v v' : Expr md, J.thmValue v v' = v')
    (mp : EnvModelM V μ env) (hT : ThmValOk mp) (hJ : JudgeSound J mp.base2)
    (hbits : AxiomBitsJ J env) (hE : EtaFamiliesClosed env)
    (hind : ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
      Ind block nP envI →
        EtaFamiliesClosed envI ∧ ∃ mp₂ : EnvModelM V μ envI, ModelExt mp mp₂)
    (hrun : DeclRunJ J Ind env d env₂) : EnvModelT V μ env₂ := by
  obtain ⟨hE₂, mp₂, hext⟩ := declStep_preservesJ hTV mp hJ hbits hE hind hrun
  exact ⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩

/-- **The fold over a package** (`foldPM`'s restatement): a stream of records
over `J` keeps `EnvModelT`, given the package's soundness at every prefix model
with theorem values read, its axiom bits, and the inductive kind's step. -/
theorem foldJ {J : Judgements md}
    {Ind : Env md → List (ConstantInfo md) → Nat → Env md → Prop}
    (hTV : ∀ v v' : Expr md, J.thmValue v v' = v')
    (hJ : ∀ {env : Env md} (mp : EnvModelM V μ env), ThmValOk mp → JudgeSound J mp.base2)
    (hbits : ∀ env : Env md, AxiomBitsJ J env)
    (hind : ∀ {env : Env md} (mp : EnvModelM V μ env), ThmValOk mp → EtaFamiliesClosed env →
      ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
        Ind env block nP envI →
          EtaFamiliesClosed envI ∧ ∃ mp₂ : EnvModelM V μ envI, ModelExt mp mp₂)
    {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ J Ind env ds env' → EnvModelT V μ env → EnvModelT V μ env' := by
  intro hds
  induction hds with
  | nil => exact id
  | cons hd _ ih =>
    intro h
    obtain ⟨⟨mp, hT⟩, hE⟩ := h
    exact ih (declStep_preservesT hTV mp hT (hJ mp hT) (hbits _) hE (hind mp hT hE) hd)

end Ix.Kernel.Model
