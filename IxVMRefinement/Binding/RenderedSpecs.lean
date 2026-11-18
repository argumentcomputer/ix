import IxVMRefinement.Binding.OpOpen
import IxVMRefinement.Core.LoadedExact

/-! # What the rendered role specifications represent

The circuit's role validations compare a bound record with terms that `KernelRoleSpec` builds on
the heap: a role's specified type (`role_type`), the two sides of an operation's recurrence
(`op_equation_lhs`, `op_equation_rhs`) and an operation's certificate statement
(`op_certificate`). Each of those functions is a `match` whose arms allocate one closed term, with
the constants of other roles read through the table (`role_bound_addr(tbl, i)`). The arms are
rendered from the kernel's specification set (`Ix.Kernel.Role.spec`) after the kernel's annotation
pass, which recomputes the binders' data and changes nothing else.

This file states, as propositions, what each of those functions returns. They are the seam
between the role validations' refinement and the rendered functions: every one has the same
form.

* `specTypeRaw r`: the type the specification set declares for the role `r`, with its universe
  parameters by position; `opSideRaw l`: a recurrence side `l` closed over its two `Nat`
  variables; `certRaw st`: a certificate statement closed over its two `Nat` variables and its
  hypotheses. They are the terms the renderer annotates and renders.
* `RendersUpToBinderData t h T₀ p`: the pointer `p` represents, exactly, under the table's own
  keying, a term that is `T₀` up to its binders' data.
* `RoleTypeRenders`, `OpEquationLhsRenders`, `OpEquationRhsRenders`, `OpCertificateRenders`: the
  four statements. The certificate's adds that the telescope is a spine of `Forall` cells (a `Let`
  cell reads as its ζ-reduct, at which `KernelRoles::open_foralls` stops).
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)

/-! ## The specified terms -/

/-- **The universe parameters and the type the specification set declares for a role**: the
role's own declaration of its block, an anchor's, operation's or equation definition's type, an
axiom's type. -/
def specDecl (r : Role) : Option (List Ix.Kernel.LevelParam × KExpr) :=
  match r.spec (md := .anon) with
  | .block decls =>
    (decls.find? fun ci => ci.name == (Ix.Kernel.Key.role r : KKey)).map fun ci =>
      (ci.toConstantVal.levelParams, ci.toConstantVal.type)
  | .anchor n ty => some (List.range n, ty)
  | .ops ty _ => some ([], ty)
  | .axiom n (some ty) => some (List.range n, ty)
  | .axiom _ none => none
  | .eqns n ty _ => some (List.range n, ty)

/-- **A role's specified type, its universe parameters by position** (the circuit names a
universe parameter by its position in the constant's list). -/
def specTypeRaw (r : Role) : Option KExpr :=
  (specDecl r).map fun d =>
    d.2.instantiateLevelParams d.1 ((List.range d.1.length).map Ix.Kernel.Level.param)

/-- **A recurrence side closed over its two `Nat` variables**: `fun (x y : Nat) => l`, for a
side `l` over the variables `fvar 0`, `fvar 1`. -/
def opSideRaw (l : KExpr) : KExpr :=
  .lam OpOpen.natTy ((Ix.Kernel.Expr.lam OpOpen.natTy (l.abstract1 1) { pw := .never }).abstract1 0)
    { pw := .never }

/-- **A certificate statement closed**: `∀ (x y : Nat) (h₀ : hyp₀) …, equation`, for hypotheses
and an equation over the variables `fvar 0`, `fvar 1` (the hypotheses' own variables are
`fvar 2`, `fvar 3`). -/
def certRaw (st : List KExpr × KExpr) : KExpr :=
  .forallE OpOpen.natTy
    ((Ix.Kernel.Expr.forallE OpOpen.natTy
      ((st.1.zipIdx.foldr (fun hi body => Ix.Kernel.Expr.forallE hi.1 (body.abstract1 (2 + hi.2))
        { pw := .never }) st.2).abstract1 1) { pw := .never }).abstract1 0) { pw := .never }

/-! ## The statements -/

/-- **The pointer represents, exactly, a term that is `T₀` up to its binders' data**, under the
keying of the table `t` (a role's address is the role's key). -/
def RendersUpToBinderData (t : Ix.Kernel.RoleTable) (h : Heap F) (T₀ : KExpr)
    (p : SourceValue F) : Prop :=
  ∃ T : KExpr, Decl.TmCExact (keyOf t) h T p ∧ T.erasePw = T₀.erasePw

/-- **`KernelRoleSpec::role_type(tbl, r)` builds the role's specified type.** -/
def RoleTypeRenders : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (r : Role) (T₀ : KExpr), specTypeRaw r = some T₀ → t.wf = true →
    ∀ {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      TableRep t h x_tbl →
      ObsFn W "KernelRoleSpec::role_type" [x_tbl, .field (roleNum r)] h res h' cs →
      Heap.Extends h h' ∧ RendersUpToBinderData t h' T₀ res

/-- **One side of a structural operation's `k`-th recurrence, as the named function builds
it**: `side` selects the side of an equation of `natOpEquations`. -/
def OpEquationSideRenders (fn : String) (side : KExpr × KExpr → KExpr) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (r : Role) (k : Nat) (eq : KExpr × KExpr),
    (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames →
    (Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey))[k]? = some eq → t.wf = true →
    ∀ {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      TableRep t h x_tbl →
      ObsFn W fn [x_tbl, .field (roleNum r), .field ((k : Nat) : F)] h res h' cs →
      Heap.Extends h h' ∧ RendersUpToBinderData t h' (opSideRaw (side eq)) res

/-- **`KernelRoleSpec::op_equation_lhs(tbl, r, k)` builds the left side of the `k`-th
recurrence.** -/
def OpEquationLhsRenders : Prop :=
  OpEquationSideRenders "KernelRoleSpec::op_equation_lhs" Prod.fst

/-- **`KernelRoleSpec::op_equation_rhs(tbl, r, k)` builds the right side of the `k`-th
recurrence.** -/
def OpEquationRhsRenders : Prop :=
  OpEquationSideRenders "KernelRoleSpec::op_equation_rhs" Prod.snd

/-- **`KernelRoleSpec::op_certificate(tbl, r, k)` builds the `k`-th certificate statement of a
well-founded operation**, along a spine of `Forall` cells. -/
def OpCertificateRenders : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (r : Role) (k : Nat) (st : List KExpr × KExpr),
    (Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames →
    (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey))[k]? = some st → t.wf = true →
    ∀ {x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      TableRep t h x_tbl →
      ObsFn W "KernelRoleSpec::op_certificate" [x_tbl, .field (roleNum r), .field ((k : Nat) : F)]
        h res h' cs →
      Heap.Extends h h' ∧ RendersUpToBinderData t h' (certRaw st) res ∧
        OpOpen.ForallSpine h' (2 + st.1.length) res

/-! ## The specified types the role validations pin, evaluated -/

set_option maxRecDepth 100000 in
/-- The literal support's two sorts: `Char` and `String` are specified at `Type`. -/
theorem specTypeRaw_char_string :
    specTypeRaw .char = some (.sort (.succ .zero)) ∧
      specTypeRaw .string = some (.sort (.succ .zero)) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
/-- The two standard axioms are specified at the types the kernel's check of them reads. -/
theorem specTypeRaw_standardAxioms :
    specTypeRaw .propext = some (Ix.Kernel.propextRaw (md := .anon)).type ∧
      (specTypeRaw .choice).isSome = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
/-- Every operation, every standard axiom, and every role whose stored shape a later group reads
has a specified type. -/
theorem specTypeRaw_isSome :
    ([Role.bool, .boolFalse, .boolTrue, .iff, .iffIntro, .iffRec, .nonempty, .nonemptyIntro,
      .nonemptyRec, .list, .listNil, .listCons, .string, .stringOfList, .char, .charOfNat,
      .natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq, .natBle, .natDiv, .natMod, .natGcd,
      .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight, .propext, .choice].all
      fun r => (specTypeRaw r).isSome) = true := by
  decide +kernel

end IxVM.Refinement.Binding
