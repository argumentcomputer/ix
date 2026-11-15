module

public import IxC.Kernel.CoreDefs

@[expose] public section

namespace Ix.Kernel.Expr

/-- Erase free-variable type annotations while preserving variable indices and binder data. -/
def eraseFvarTypes : Expr md → Expr md
  | .bvar i => .bvar i
  | .fvar i _ => .fvar i (.sort .zero)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (eraseFvarTypes f) (eraseFvarTypes a)
  | .lam ty b m => .lam (eraseFvarTypes ty) (eraseFvarTypes b) m
  | .forallE ty b m => .forallE (eraseFvarTypes ty) (eraseFvarTypes b) m
  | .letE ty v b m => .letE (eraseFvarTypes ty) (eraseFvarTypes v) (eraseFvarTypes b) m
  | .lit l => .lit l
  | .proj s i e => .proj s i (eraseFvarTypes e)

/-- Constant resolution for readings, which ignore free-variable type annotations.
Declaration typing continues to use the hereditary `constsResolve` check. -/
def constsResolveShallow (env : Env md) (e : Expr md) : Bool :=
  (eraseFvarTypes e).constsResolve env

end Ix.Kernel.Expr
