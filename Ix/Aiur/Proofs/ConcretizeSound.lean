module
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Proofs.ConcretizeProgress
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.ConcreteEvalInversion
public import Ix.Aiur.Proofs.ValueEqFlatten
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.DrainInvariants
public import Ix.Aiur.Semantics.ConcreteInvariants

/-!
Concretize soundness.

Preservation: `substInTypedTerm subst body` has the same value denotation as
`body` under the original type environment. Values are type-erased; substitution
changes types but not value denotation.

Progress: the termination check (rejecting polymorphic recursion) bounds the
worklist; termination follows by structural induction on the type-argument DAG.
-/

public section

namespace Aiur

/-! ## `typFlatSize` preservation through concretize's type rewrites

These theorems capture a structural fact about `concretize`'s type rewrites:
`rewriteTyp emptySubst mono` preserves `typFlatSize` on `MvarFree` types whose
`.app` heads are in `mono`. They are sorried here because a full proof requires
induction over `Typ` + `DataType` mutual recursion paralleling `typFlatSizeBound`
+ `dataTypeFlatSizeBound`. See `StructCompatible.lean` for the downstream
consumer (`compile_ok_input_layout_matches`). -/

/-! ### `typFlatSize` preservation across `concretize`.

The earlier `MonoCompatible` predicate was stated on source `decls` with
`.ref g'` expected to resolve there — but `g' = concretizeName g args` is
fresh, never in source decls, so the predicate was provably false for any
non-trivial polymorphic program. Additionally, `typFlatSizeBound`'s `.app`
arm ignores `args` (single `g`-lookup), making the equation self-contradictory
for templates with multiple instantiations.

The correct formulation lives across TWO decls tables: source decls for the
pre-rewrite side, mono decls (post-concretize Step 3) for the rewritten side.
Empty `visited` is sufficient — the downstream caller
(`compile_ok_input_layout_matches`) only invokes at the outer entry.

-/

-- Phase 2 (MonoHasDecl + MonoShapeOk + polymorphic exclusion helpers) moved to
-- `ConcretizeSound/MonoInvariants.lean` 2026-04-29.

-- FnFree mutual block + `Concrete.Eval.runFunction_preserves_FnFree`
-- moved to `ConcretizeSound/FnFree.lean` 2026-04-29.


-- FirstOrderReturn bridge + FO preservation helpers + concretizeBuild FO
-- + drain NewFunctionsFO + PendingArgsFO chain moved to
-- `ConcretizeSound/FirstOrder.lean` 2026-04-29.

-- TermRefsDt full chain (substInTypedTerm/rewriteTypedTerm/termToConcrete
-- preservation + drain + concretizeBuild + step4Lower fold) moved to
-- `ConcretizeSound/RefsDt.lean` 2026-04-29.

-- typFlatSize main + concretize stage extract + sub-lemmas + Phase A.1 moved to
-- `ConcretizeSound/StageExtract.lean` 2026-04-29.

-- concretize_layoutMap_progress decomposition moved to
-- `ConcretizeSound/Layout.lean` 2026-04-29.

-- Shapes (StrongNewNameShape + NewFnInputsLabelShape + IndexMap helpers
-- + step4Lower key helpers) moved to `ConcretizeSound/Shapes.lean` 2026-04-29.

-- Phase A.2/A.3 + reverse origin + explicit-structure + Phase 0 moved to
-- `ConcretizeSound/CtorKind.lean` 2026-04-29.


-- Phase A.4 + Phase B prereq + Wire B moved to
-- `ConcretizeSound/Phase4.lean` 2026-04-29.

end Aiur

end -- public section
