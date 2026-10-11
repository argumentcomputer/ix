import Ix.CompileCert.Faithful

/-! # Initial direct-cone coverage predicates

These predicates are checked on a supplied finite source inventory. They
are not the final `Dom` for L4 totality and do not classify unsupported
source features as invalid Lean. Target correspondence must still be
established from the actual reader stream.
-/

namespace Ix.CompileCert

/-- Named syntax limitations of the current independent exporter. This is
coverage reporting, not a claim that these expressions are invalid Lean. -/
def unsupportedExpr : Lean.Expr → Option String
  | .fvar _ => some "free variable in closed source"
  | .mvar _ => some "expression metavariable"
  | .mdata _ e => unsupportedExpr e
  | .sort u => if u.hasMVar then some "universe metavariable" else none
  | .const _ us => if us.any Lean.Level.hasMVar then some "universe metavariable" else none
  | .app f a => (unsupportedExpr f).orElse fun _ => unsupportedExpr a
  | .lam _ t b _ | .forallE _ t b _ =>
    (unsupportedExpr t).orElse fun _ => unsupportedExpr b
  | .letE _ t v b _ => (unsupportedExpr t).orElse fun _ =>
    (unsupportedExpr v).orElse fun _ => unsupportedExpr b
  | .proj _ _ e => unsupportedExpr e
  | _ => none

def unsupportedSource (ci : Lean.ConstantInfo) : Option String :=
  if !sourceSupported ci then some "unsafe or partial source declaration"
  else (unsupportedExpr ci.type).orElse fun _ =>
    match ci with
    | .defnInfo v => unsupportedExpr v.value
    | .thmInfo v => unsupportedExpr v.value
    | .opaqueInfo v => unsupportedExpr v.value
    | .recInfo v => v.rules.findSome? (fun r => unsupportedExpr r.rhs)
    | _ => none

def DirectDomain (s : Source) (roots : List Lean.Name) (m : SourceMap) : Prop :=
  CompleteSource s roots ∧ MapComplete s m

instance (s : Source) (roots : List Lean.Name) (m : SourceMap) :
    Decidable (DirectDomain s roots m) :=
  inferInstanceAs (Decidable (CompleteSource s roots ∧ MapComplete s m))

end Ix.CompileCert
