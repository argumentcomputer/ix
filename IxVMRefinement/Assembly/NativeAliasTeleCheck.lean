import IxVMRefinement.Decl.NativeCommon
import IxVMRefinement.Decl.ModeledAux
import IxVMRefinement.Assembly.NativeAliasTraceLevels

/-! # IxCK's check of a telescope constant whose type is read at the term seam

The telescope the circuit builds for a former declared at a definition is registered as the
term the builder's walk produces (`Assembly/NativeAliasOpenTrace.lean`). The heap pointer
represents that term at the term seam `Tm` (levels of sorts and constants up to semantic
equality), not exactly. IxCK's from-scratch check of a constant (`ConstantValCheckJ`) asks for
facts of the constant's type itself, so each is taken from where it holds of the walk's term:

* no free variable, no loose bound variable, no `let`: from the representation
  (`Tm.hasFvar_false`, `Tm.looseBVarsBounded`, `Tm.noLetExpr_closed`);
* a sort typing derivation: from the circuit's `k_ensure_sort` on the pointer, at the term seam;
* the constants resolve: from the typing derivation;
* the level parameters are the constant's: **a premise**, because the circuit's scope check of
  the heap term says nothing of a term that agrees with it only up to semantic level equality.
  For the traced telescope it is `Decl.tracedTele_allLevelParamsDefined`.

`constantValCheckJ_of_tm` assembles them, for a constant at positional level parameters.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (Expr Level LevelParam ConstantVal)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (ConstantValCheckJ)
open Ix.Kernel.Model (rulesJ)

/-- A term represented at the term seam, over a context of `let`-free types, has no `let`: a
heap `let` is read as its substitution instance. -/
theorem Tm.noLetExpr_of_ctx {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hΓ : ∀ j, j < d → noLetExpr (Γ j) = true)
    (rep : Tm κ d Γ h k E p) :
    noLetExpr E = true := by
  induction rep with
  | bvarLocal => rfl
  | @bvarFree k₀ _ i _ _ hk hd =>
    exact hΓ (fvIdx d k₀ (ZMod.val i)) (by unfold fvIdx; omega)
  | sort | const | litNat | litStr => rfl
  | app _ _ _ ihf iha => simp only [noLetExpr, ihf, iha]; rfl
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb =>
    simp only [noLetExpr, iht, ihb]; rfl
  | letE _ _ _ _ _ ihv ihb => exact noLetExpr_instShift ihv 0 ihb
  | proj _ _ _ ihe => exact ihe

/-- A term represented at the term seam with no opened variable has no `let`. -/
theorem Tm.noLetExpr_closed {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h 0 E p) : noLetExpr E = true :=
  Tm.noLetExpr_of_ctx (fun _ hlt => absurd hlt (Nat.not_lt_zero _)) rep

/-- **IxCK's from-scratch check of a constant whose type is represented at the term seam**, at
positional level parameters. The type's level parameters are a premise (module docstring); the
sort typing is the circuit's `k_ensure_sort` on the representing pointer. -/
theorem constantValCheckJ_of_tm {c : ScopedCtx} {Γ : Nat → KExpr} {name : KKey} {k : Nat}
    {Z : KExpr} {rc ty types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlpd : Z.allLevelParamsDefined (List.range k) = true)
    (hfresh : c.env.find? name = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains name = false)
    (hshape : name.isProjFnShape = false)
    (hstore : Ix.Kernel.Open.StoreInv c.env)
    (hrc : RCRep c.t c.lim h rc) (hty : TypesRep c.κ Γ h 0 types)
    (hef : CoreEnvFacts c.toCtx) (hlf : ScopedLoadFacts c) (hgood : CoreGood c cs)
    (htm : Tm c.κ 0 Γ h 0 Z ty)
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort" [rc, ty, types] h r h' cs) :
    ConstantValCheckJ rulesJ c.env ⟨name, List.range k, Z⟩ ⟨name, List.range k, Z⟩ := by
  have hfv : Z.hasFvar = false := Tm.hasFvar_false htm
  have hlbd : Z.looseBVarsBounded 0 = true := Tm.looseBVarsBounded htm
  have hnl : noLetExpr Z = true := Tm.noLetExpr_closed htm
  obtain ⟨sty, u, ℓ, hinf, hred, -, -⟩ :=
    scoped_core_ensure_sort hrc hty (ghostScoped_zero Γ) hef hlf hgood ev_sort htm
  have hcr : Z.constsResolve c.env = true := infer_constsResolve hinf hstore hfv
  exact ⟨Z, ⟨Option.isNone_iff_eq_none.mpr hfresh, hbasis, hshape,
    nat_levelParam_nodup_of_nodup List.nodup_range, hlbd, hfv,
    (JudgementsMap.refl rulesJ).annot (annot_refl_of_noLetExpr hnl hfv hlbd 0), hlpd, hcr,
    ⟨sty, u, (JudgementsMap.refl rulesJ).infer hinf, (JudgementsMap.refl rulesJ).sort hred⟩⟩,
    rfl⟩

end IxVM.Refinement.Decl
