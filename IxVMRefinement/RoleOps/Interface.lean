import IxVMRefinement.RoleOps.Guards
import IxCK.Kernel.Semantics.DeclJ
import IxCK.Kernel.Model.JudgeRules

/-! # What a check of a `Nat` operation establishes

The facts a check of the record bound to one of the fifteen `Nat` operations must establish for
the kernel's judgement-level install record (`Ix.Kernel.Semantics.DeclDefnRunJ` over derivations,
`Ix.Kernel.Model.rulesJ`) to hold at the operation's key. Every field is a derivation of the
rules tier or a syntactic fact about the terms the check handled; none mentions a run of a
checker. The environment `env` is the one before the operation is stored.

* `OpFront`: the record checked as a definition: its type is a type and its value has that
  type. `ty₀`, `val₀` are the terms annotated and `ty`, `val` their annotations, the terms
  stored. A check that handles terms already in annotated form (no `let`, binder data written)
  takes `ty₀ = ty` and `val₀ = val`.
* `StructOpCheck` (the seven structural operations): the type has the pinned shape, and each
  recurrence of `natOpEquations` is a conversion at depth 2, between its two sides with the
  operation's own constant replaced by the value `val`.
* `WfOpCheck` (the eight well-founded operations): the type has the pinned shape, and for each
  certificate statement of `divModCertStmts` there is a closed proof term `P` that names no
  constant outside `env` (so not the operation), whose application to the statement's variables
  has a type convertible to the statement's equation, the operation replaced by `val` in the
  statement (`CertFacts`).
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey)
open Ix.Kernel (Env Expr natOpEquations divModCertStmts divModCertApplied)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

/-- **The record checked as a definition**: the declared type and value are closed, `ty` and
`val` annotate them and mention no level parameter, `ty` is a type and `val` has a type
convertible to it, all in `env`. -/
structure OpFront (env : Env .anon) (ty₀ val₀ ty val : KExpr) : Prop where
  tyClosed : ty₀.looseBVarsBounded 0 = true
  tyNoFvar : ty₀.hasFvar = false
  tyAnnot : Annot 0 ty₀ ty
  tyLevels : ty.allLevelParamsDefined [] = true
  tySort : ∃ s u, Infer env .full 0 ty s ∧ Red env 0 s (.sort u)
  valClosed : val₀.looseBVarsBounded 0 = true
  valNoFvar : val₀.hasFvar = false
  valAnnot : Annot 0 val₀ val
  valLevels : val.allLevelParamsDefined [] = true
  valTyped : ∃ vt, Infer env .full 0 val vt ∧ DefEq env 0 vt ty

/-- **A structural operation's check**: the definition's check, the pinned shape of its type, and
every recurrence as a conversion at depth 2 in `env`, the operation replaced by its value. The
recurrences' variables are the opened variables `0` and `1`, of type `Nat`. -/
structure StructOpCheck (env : Env .anon) (c : KKey) (ty₀ val₀ ty val : KExpr) : Prop where
  front : OpFront env ty₀ val₀ ty val
  tyShape : OpTyShape c ty
  eqs : ∀ eq ∈ natOpEquations 0 c,
    DefEq env 2 (Expr.substConst0 c val eq.1) (Expr.substConst0 c val eq.2)

/-- **One certificate, checked**: `P` is a closed proof term with no level parameter whose
constants are stored in `env`; applied to the statement's variables (the opened variables `0` and
`1` of type `Nat`, then one per hypothesis, typed by the hypothesis with the operation replaced
by `val`) it annotates to a term whose inferred type is convertible to the statement's equation,
the operation replaced by `val`. Frame depth 4, as the kernel's record states it. -/
structure CertFacts (env : Env .anon) (c : KKey) (val : KExpr) (st : List KExpr × KExpr)
    (P : KExpr) : Prop where
  closed : P.looseBVarsBounded 0 = true
  noFvar : P.hasFvar = false
  levels : P.allLevelParamsDefined [] = true
  resolves : P.constsResolve env = true
  typed : ∃ appliedA tp,
    Annot 4 (divModCertApplied P (st.1.map (Expr.substConst0 c val))) appliedA ∧
      Infer env .full 4 appliedA tp ∧ DefEq env 4 tp (Expr.substConst0 c val st.2)

/-- **A well-founded operation's check**: the definition's check, the pinned shape of its type,
and one checked certificate per statement of `divModCertStmts`, in order. -/
structure WfOpCheck (env : Env .anon) (c : KKey) (ty₀ val₀ ty val : KExpr) : Prop where
  front : OpFront env ty₀ val₀ ty val
  tyShape : OpTyShape c ty
  certs : ∃ proofs : List KExpr,
    List.Forall₂ (CertFacts env c val) (divModCertStmts c) proofs

end IxVM.Refinement.RoleOps
