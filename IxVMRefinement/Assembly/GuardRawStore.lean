import IxVMRefinement.Assembly.GuardRawLookup
import IxVMRefinement.StatementRel.LoadedReadsCanon
import IxVMRefinement.Assembly.TypingDefnStep

/-! # Optional annotated readings and typed step-store adapters for the raw dictionary

The raw dictionary and its record/blob extension theorems do not depend on declaration
preservation. This leaf connects it to the existing typed step-store interface, and retains
an optional richer annotation reader for consumers that need binder data.
-/

namespace IxVM.Refinement.GuardRaw

open IxVM.Consistency
open Ix.Kernel (Expr)

/-- The richer annotated reading is retained separately for consumers that need binder data. -/
noncomputable def readAnnotatedRoot (blob : Blobs) (root : Root) : Option (Expr .anon) := do
  let e ← (exprReader addressTable blob root.source id root.self).read root.expression |>.toOption
  LoadedReads.canonAnn root.source (List.range root.levels) (root.offset : IxVM.F) root.expression e

/-- The actual run-store interface supplies its raw dictionary extension. -/
theorem ofStore_extends_stepStore {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} (h : Typing.StepStore calls t E₀ E) :
    (ofStore E₀).Extends (ofStore E) :=
  lookup_extends (fun _ _ hc => h.held hc) h.runBlob

end IxVM.Refinement.GuardRaw
