import Lean

namespace Tests.Ix.Compile.IxcRefusalRecords

inductive LeanReason where
  | smallEliminator (typeName : String)
  | minorMismatch (typeName ctorName : String)
  | unsafeInductive
  | blocked (rootName : String)

structure LeanRecord where
  unit : String
  reason : LeanReason
  names : List String

/-- M7's nine-unit measurement: 17 exact groups, 134 refused labels across
five units. Every other measured label accepts or types; unmeasured refusals
remain errors. No namespace wildcard or inferred unsafe-failure rule. -/
def leanRecords : List LeanRecord := [
  { unit := "NestedSortU", reason := .smallEliminator "NestedSortU.T", names := [
    "NestedSortU.T",
    "NestedSortU.T.mk",
    "NestedSortU.T.rec",
    "NestedSortU.T.rec_1"
  ] },
  { unit := "NestedSortU", reason := .blocked "NestedSortU.T.rec", names := [
    "NestedSortU.t_rec"
  ] },
  { unit := "NestedSortUK", reason := .smallEliminator "NestedSortUK.T", names := [
    "NestedSortUK.T",
    "NestedSortUK.T.mk",
    "NestedSortUK.T.rec",
    "NestedSortUK.T.rec_1"
  ] },
  { unit := "NestedSortUK", reason := .blocked "NestedSortUK.T", names := [
    "NestedSortUK.t_rec"
  ] },
  { unit := "NestShapes", reason := .blocked "NestShapes.R.rec", names := [
    "NestShapes.R._sizeOf_1",
    "NestShapes.R._sizeOf_2",
    "NestShapes.R.below",
    "NestShapes.R.below_1",
    "NestShapes.R.brecOn",
    "NestShapes.R.brecOn.eq",
    "NestShapes.R.brecOn.go",
    "NestShapes.R.brecOn_1",
    "NestShapes.R.brecOn_1.eq",
    "NestShapes.R.brecOn_1.go",
    "NestShapes.R.casesOn",
    "NestShapes.R.recOn"
  ] },
  { unit := "NestShapes", reason := .minorMismatch "NestShapes.R" "NestShapes.R.mk", names := [
    "NestShapes.R",
    "NestShapes.R.leaf",
    "NestShapes.R.mk",
    "NestShapes.R.rec",
    "NestShapes.R.rec_1"
  ] },
  { unit := "NestShapes", reason := .blocked "NestShapes.R", names := [
    "NestShapes.R._sizeOf_inst",
    "NestShapes.R.ctorElim",
    "NestShapes.R.ctorElimType",
    "NestShapes.R.ctorIdx",
    "NestShapes.R.leaf.elim",
    "NestShapes.R.leaf.sizeOf_spec",
    "NestShapes.R.mk.elim",
    "NestShapes.R.mk.inj",
    "NestShapes.R.mk.injEq",
    "NestShapes.R.mk.noConfusion",
    "NestShapes.R.mk.sizeOf_spec",
    "NestShapes.R.noConfusion",
    "NestShapes.R.noConfusionType"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UNestNeg.rec", names := [
    "UnsafeI.UNestNeg.below",
    "UnsafeI.UNestNeg.below_1",
    "UnsafeI.UNestNeg.brecOn",
    "UnsafeI.UNestNeg.brecOn.eq",
    "UnsafeI.UNestNeg.brecOn.go",
    "UnsafeI.UNestNeg.brecOn_1",
    "UnsafeI.UNestNeg.brecOn_1.eq",
    "UnsafeI.UNestNeg.brecOn_1.go",
    "UnsafeI.UNestNeg.casesOn",
    "UnsafeI.UNestNeg.noConfusion",
    "UnsafeI.UNestNeg.noConfusionType",
    "UnsafeI.UNestNeg.recOn"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UN", names := [
    "UnsafeI.UN.below",
    "UnsafeI.UN.below_1",
    "UnsafeI.UN.brecOn",
    "UnsafeI.UN.brecOn.eq",
    "UnsafeI.UN.brecOn.go",
    "UnsafeI.UN.brecOn_1",
    "UnsafeI.UN.brecOn_1.eq",
    "UnsafeI.UN.brecOn_1.go",
    "UnsafeI.UN.casesOn",
    "UnsafeI.UN.ctorIdx",
    "UnsafeI.UN.mk.noConfusion",
    "UnsafeI.UN.noConfusion",
    "UnsafeI.UN.noConfusionType",
    "UnsafeI.UN.recOn"
  ] },
  { unit := "UnsafeI", reason := .unsafeInductive, names := [
    "UnsafeI.U",
    "UnsafeI.U.leaf",
    "UnsafeI.U.mk",
    "UnsafeI.U.rec",
    "UnsafeI.UN",
    "UnsafeI.UN.mk",
    "UnsafeI.UN.rec",
    "UnsafeI.UN.rec_1",
    "UnsafeI.UNeg",
    "UnsafeI.UNeg.mk",
    "UnsafeI.UNeg.rec",
    "UnsafeI.UNestNeg",
    "UnsafeI.UNestNeg.mk",
    "UnsafeI.UNestNeg.rec",
    "UnsafeI.UNestNeg.rec_1"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UNeg", names := [
    "UnsafeI.UNeg.below",
    "UnsafeI.UNeg.brecOn",
    "UnsafeI.UNeg.brecOn.eq",
    "UnsafeI.UNeg.brecOn.go",
    "UnsafeI.UNeg.casesOn",
    "UnsafeI.UNeg.ctorIdx",
    "UnsafeI.UNeg.mk.noConfusion",
    "UnsafeI.UNeg.noConfusion",
    "UnsafeI.UNeg.noConfusionType",
    "UnsafeI.UNeg.recOn"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.U", names := [
    "UnsafeI.U.ctorElim",
    "UnsafeI.U.ctorElimType",
    "UnsafeI.U.ctorIdx",
    "UnsafeI.U.depth",
    "UnsafeI.U.depth.match_1",
    "UnsafeI.U.leaf.elim",
    "UnsafeI.U.mk.elim",
    "UnsafeI.U.mk.noConfusion",
    "UnsafeI.U.noConfusion",
    "UnsafeI.U.noConfusionType"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.UNestNeg", names := [
    "UnsafeI.UNestNeg.ctorIdx",
    "UnsafeI.UNestNeg.mk.noConfusion"
  ] },
  { unit := "UnsafeI", reason := .blocked "UnsafeI.U.rec", names := [
    "UnsafeI.U.below",
    "UnsafeI.U.brecOn",
    "UnsafeI.U.brecOn.eq",
    "UnsafeI.U.brecOn.go",
    "UnsafeI.U.casesOn",
    "UnsafeI.U.recOn"
  ] },
  { unit := "KernelSpec", reason := .blocked "KernelSpec.T.rec", names := [
    "KernelSpec.T.below",
    "KernelSpec.T.below_1",
    "KernelSpec.T.brecOn",
    "KernelSpec.T.brecOn.eq",
    "KernelSpec.T.brecOn.go",
    "KernelSpec.T.brecOn_1",
    "KernelSpec.T.brecOn_1.eq",
    "KernelSpec.T.brecOn_1.go",
    "KernelSpec.T.casesOn",
    "KernelSpec.T.ctorElim",
    "KernelSpec.T.ctorIdx",
    "KernelSpec.T.mk.noConfusion",
    "KernelSpec.T.noConfusion",
    "KernelSpec.T.noConfusionType",
    "KernelSpec.T.recOn"
  ] },
  { unit := "KernelSpec", reason := .minorMismatch "KernelSpec.T" "KernelSpec.T.mk", names := [
    "KernelSpec.T",
    "KernelSpec.T.leaf",
    "KernelSpec.T.mk",
    "KernelSpec.T.rec",
    "KernelSpec.T.rec_1"
  ] },
  { unit := "KernelSpec", reason := .blocked "KernelSpec.T", names := [
    "KernelSpec.T.ctorElimType",
    "KernelSpec.T.leaf.elim",
    "KernelSpec.T.mk.elim",
    "KernelSpec.T.mk.inj",
    "KernelSpec.T.mk.injEq"
  ] },
]

end Tests.Ix.Compile.IxcRefusalRecords
