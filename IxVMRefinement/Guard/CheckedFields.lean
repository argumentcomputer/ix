import IxVMRefinement.Guard.Fields

/-! # The classifier's field loop at a constructor, with the sorts it checked

`Core.GuardData.check_prop_fields_sorts` reads a `KernelGuard::check_prop_fields` run at a
structure-like proposition (one constructor, no index, a level that evaluates to zero) and gives
field sorts with their `FieldSortsJ` witness and, per field, the evidence of the classifier's
check (`CheckedSortAt`). Its conclusion is existential in the sorts, so a consumer that runs
IxC's table stage at them has to keep them together with the run they came from.

* `CheckedFieldsAt c calls b i nP nF cty u sorts`: the run data of the field loop at the first
  constructor of member `i` of the block at `b`, inside the run `calls`, together with the
  facts of `check_prop_fields_sorts` at these `sorts`. Its run data are the hypotheses of
  `Core.CheckedFieldsReading` (`Guard/Certificate.lean`): the loop's observation on the type
  pointer of the constructor the run loaded, the load itself, and the goodness of both.
* `checkedFieldsAt_of_run`: the loop's observation gives sorts with `CheckedFieldsAt`.
-/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open Ix.Kernel (Expr Level)
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

/-- A list of length one is the singleton of its first element. -/
theorem eq_singleton {α : Type} {l : List α} {x : α} (hl : l.length = 1)
    (h0 : l[0]? = some x) : l = [x] := by
  cases l with
  | nil => exact absurd hl (by simp)
  | cons a tl =>
    cases tl with
    | nil =>
      have hax : a = x := by simpa using h0
      rw [hax]
    | cons b tl' =>
      simp only [List.length_cons] at hl
      omega

/-- **The field loop's run at a constructor, with the sorts it checked** (module docstring). The
context `c` is the one the loop ran at; `calls` is the run the loop and the constructor's load
lie in. -/
def CheckedFieldsAt (c : ScopedCtx) (calls : List (Call F)) (b : Bytes.Address) (i : F)
    (nP nF : Nat) (cty : KExpr) (u : KLevel) (sorts : List KLevel) : Prop :=
  ∃ (Γ : Nat → KExpr) (residual body : KExpr) (parameters fvs : List KExpr)
    (rc level p r : SourceValue F) (np nf : F) (h h' : Heap F) (cs : List (Call F))
    (bp ptr w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F) (h₀ m : Heap F) (cs₀ : List (Call F)),
    np.val = nP ∧ nf.val = nF ∧
    Ix.Kernel.openPisAtFvars nP cty 0 = some (parameters, residual) ∧
    Ix.Kernel.openPisAtFvars nF residual nP = some (fvs, body) ∧
    CoreGood c cs ∧ c.rc h rc ∧ Tm c.κ 0 Γ h 0 cty p ∧ RepKLevel h u level ∧
    (∀ φ, Level.eval φ u = 0) ∧
    ObsFn W "KernelGuard::check_prop_fields"
      [rc, level, .field 1, .field 0, p, .field np, .field nf] h r h' cs ∧
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h₀ ptr m cs₀ ∧
    CoreGood c cs₀ ∧ Bytes.RepAddressRef addrTy h₀ b bp ∧
    loadValue m ptr = .ok (.construct kciEnum "Ctor" [w₁, p, w₃, w₄, w₅, w₆, w₇, w₈]) ∧
    Heap.Extends m h ∧ (∀ cl ∈ cs, cl ∈ calls) ∧ (∀ cl ∈ cs₀, cl ∈ calls) ∧
    Ix.Kernel.Semantics.FieldSortsJ Ix.Kernel.Model.rulesJ c.env true false u nP fvs [] nF
      sorts ∧
    ∀ j < nF, ∃ fv v, fvs[j]? = some fv ∧ sorts[j]? = some v ∧
      CheckedSortAt c h cs (nP + j) fv.fvarTypeD v

/-- The sorts of `CheckedFieldsAt` have their `FieldSortsJ` witness at the telescope the loop
opened. -/
theorem CheckedFieldsAt.sorted {c : ScopedCtx} {calls : List (Call F)} {b : Bytes.Address}
    {i : F} {nP nF : Nat} {cty : KExpr} {u : KLevel} {sorts : List KLevel}
    (h : CheckedFieldsAt c calls b i nP nF cty u sorts) :
    ∃ (parameters fvs : List KExpr) (residual body : KExpr),
      Ix.Kernel.openPisAtFvars nP cty 0 = some (parameters, residual) ∧
      Ix.Kernel.openPisAtFvars nF residual nP = some (fvs, body) ∧
      Ix.Kernel.Semantics.FieldSortsJ Ix.Kernel.Model.rulesJ c.env true false u nP fvs [] nF
        sorts := by
  obtain ⟨Γ, residual, body, parameters, fvs, rc, level, p, r, np, nf, h₁, h₂, cs, bp, ptr,
    w₁, w₃, w₄, w₅, w₆, w₇, w₈, h₀, m, cs₀, -, -, opened, openedFields, -, -, -, -, -, -, -, -,
    -, -, -, -, -, sorted, -⟩ := h
  exact ⟨parameters, fvs, residual, body, opened, openedFields, sorted⟩

/-- The run data hold inside any longer run. -/
theorem CheckedFieldsAt.mono {c : ScopedCtx} {calls calls' : List (Call F)} {b : Bytes.Address}
    {i : F} {nP nF : Nat} {cty : KExpr} {u : KLevel} {sorts : List KLevel}
    (h : CheckedFieldsAt c calls b i nP nF cty u sorts)
    (hsub : ∀ cl ∈ calls, cl ∈ calls') : CheckedFieldsAt c calls' b i nP nF cty u sorts := by
  obtain ⟨Γ, residual, body, parameters, fvs, rc, level, p, r, np, nf, h₁, h₂, cs, bp, ptr,
    w₁, w₃, w₄, w₅, w₆, w₇, w₈, h₀, m, cs₀, hp, hf, opened, openedFields, hg, hrc, hE,
    represented, zero, ev, load, good₀, hb, ld, hext, hin, hin₀, sorted, checked⟩ := h
  exact ⟨Γ, residual, body, parameters, fvs, rc, level, p, r, np, nf, h₁, h₂, cs, bp, ptr,
    w₁, w₃, w₄, w₅, w₆, w₇, w₈, h₀, m, cs₀, hp, hf, opened, openedFields, hg, hrc, hE,
    represented, zero, ev, load, good₀, hb, ld, hext, fun cl hcl => hsub cl (hin cl hcl),
    fun cl hcl => hsub cl (hin₀ cl hcl), sorted, checked⟩

/-- **The loop's observation gives sorts with their run data**: the hypotheses are those of
`check_prop_fields_sorts`, the constructor's load whose type field is the pointer the loop
walks, and that the loop's calls and the load's lie in `calls`. -/
theorem checkedFieldsAt_of_run {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {calls : List (Call F)} {nP nF : Nat} {Γ : Nat → KExpr} {E residual body : KExpr}
    {parameters fvs : List KExpr} {rc level p r : SourceValue F} {np nf : F}
    {h h' : Heap F} {cs : List (Call F)} {u : KLevel}
    (hp : np.val = nP) (hf : nf.val = nF)
    (opened : Ix.Kernel.openPisAtFvars nP E 0 = some (parameters, residual))
    (openedFields : Ix.Kernel.openPisAtFvars nF residual nP = some (fvs, body))
    (hg : CoreGood c cs) (hrc : c.rc h rc) (hE : Tm c.κ 0 Γ h 0 E p)
    (represented : RepKLevel h u level) (zero : ∀ φ, Level.eval φ u = 0)
    (ev : ObsFn W "KernelGuard::check_prop_fields"
      [rc, level, .field 1, .field 0, p, .field np, .field nf] h r h' cs)
    {b : Bytes.Address} {i : F} {bp ptr w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F}
    {h₀ m : Heap F} {cs₀ : List (Call F)}
    (load : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h₀ ptr m cs₀)
    (good₀ : CoreGood c cs₀) (hb : Bytes.RepAddressRef addrTy h₀ b bp)
    (ld : loadValue m ptr = .ok (.construct kciEnum "Ctor" [w₁, p, w₃, w₄, w₅, w₆, w₇, w₈]))
    (hext : Heap.Extends m h)
    (hin : ∀ cl ∈ cs, cl ∈ calls) (hin₀ : ∀ cl ∈ cs₀, cl ∈ calls) :
    ∃ sorts : List KLevel,
      Ix.Kernel.Semantics.FieldSortsJ Ix.Kernel.Model.rulesJ c.env true false u nP fvs [] nF
        sorts ∧
      CheckedFieldsAt c calls b i nP nF E u sorts := by
  obtain ⟨sorts, sorted, checked⟩ :=
    check_prop_fields_sorts hc hp hf opened openedFields hg hrc hE represented zero ev
  exact ⟨sorts, sorted, Γ, residual, body, parameters, fvs, rc, level, p, r, np, nf, h, h', cs,
    bp, ptr, w₁, w₃, w₄, w₅, w₆, w₇, w₈, h₀, m, cs₀, hp, hf, opened, openedFields, hg, hrc, hE,
    represented, zero, ev, load, good₀, hb, ld, hext, hin, hin₀, sorted, checked⟩

end IxVM.Refinement.Core.GuardData
