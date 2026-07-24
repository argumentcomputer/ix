module

public import Ix.Tc.Subst

/-!
Mirror: crates/kernel/src/lctx.rs

Local context for free-variable-based binder opening. When a binder
(`lam`/`all`/`letE`) is recursed into, it is opened by replacing the bound
`Var(0)` with a fresh fvar and pushing a `LocalDecl`. Each fvar carries a
unique `FVarId` embedded in its content hash, so expressions mentioning
different fvars hash distinctly — the soundness lever that lets WHNF / infer
/ def-eq caches key by expression alone.

Rust's legacy `NameGenerator` is not ported: fvar ids are minted from
`KEnv.nextFVarId` (the load-bearing counter; see env.rs docs).
-/

public section
@[expose] section

namespace Ix.Tc

/-- A single local-context entry: a regular binder (`cdecl`, from lambda or
    forall) or a let-binding (`ldecl`, with an associated value that WHNF
    zeta-reduces to). -/
inductive LocalDecl (m : Mode) where
  | cdecl (name : m.F Name) (bi : m.F Lean.BinderInfo) (ty : KExpr m)
  | ldecl (name : m.F Name) (ty : KExpr m) (val : KExpr m)

namespace LocalDecl

def ty : LocalDecl m → KExpr m
  | .cdecl _ _ t => t
  | .ldecl _ t _ => t

def name : LocalDecl m → m.F Name
  | .cdecl n _ _ => n
  | .ldecl n _ _ => n

/-- `some val` for let-bindings, `none` otherwise. -/
def val? : LocalDecl m → Option (KExpr m)
  | .cdecl .. => none
  | .ldecl _ _ v => some v

def isLet : LocalDecl m → Bool
  | .ldecl .. => true
  | .cdecl .. => false

instance : Inhabited (LocalDecl m) :=
  ⟨.cdecl Mode.F.mkDefault Mode.F.mkDefault default⟩

end LocalDecl

/-- Insertion-ordered local context indexed by `FVarId`. Push/truncate are
    O(1) amortized; lookup is O(1) via the parallel `index` map. -/
structure LocalContext (m : Mode) where
  /-- Insertion-ordered fvars and their declarations. -/
  decls : Array (FVarId × LocalDecl m) := #[]
  /-- Position lookup: `index[fv] = i` iff `decls[i].1 = fv`. -/
  index : Std.HashMap FVarId Nat := {}

namespace LocalContext

def empty : LocalContext m := {}

instance : Inhabited (LocalContext m) := ⟨{}⟩

def size (lctx : LocalContext m) : Nat := lctx.decls.size

def isEmpty (lctx : LocalContext m) : Bool := lctx.decls.isEmpty

/-- Look up a declaration by `FVarId`. -/
def find? (lctx : LocalContext m) (id : FVarId) : Option (LocalDecl m) := do
  let i ← lctx.index[id]?
  return (← lctx.decls[i]?).2

/-- Push a declaration. The caller must ensure `id` is fresh. -/
def push (lctx : LocalContext m) (id : FVarId) (decl : LocalDecl m) :
    LocalContext m :=
  { decls := lctx.decls.push (id, decl)
    index := lctx.index.insert id lctx.decls.size }

/-- Truncate to `len`, dropping declarations pushed since (their fvars become
    unresolvable via `find?`). -/
def truncate (lctx : LocalContext m) (len : Nat) : LocalContext m := Id.run do
  let mut decls := lctx.decls
  let mut index := lctx.index
  while decls.size > len do
    let (id, _) := decls.back!
    decls := decls.pop
    index := index.erase id
  return { decls, index }

def wrapBinders (lctx : LocalContext m) (fvars : Array FVarId)
    (body : KExpr m) (asLambda : Bool) : InternM m (KExpr m) := do
  -- Wrap innermost-first: rightmost fvar is the innermost binder.
  let mut acc := body
  for fv in fvars.reverse do
    let some decl := lctx.find? fv
      | panic! "LocalContext.wrapBinders: fvar not in context"
    acc ← match decl with
      | .cdecl name bi ty =>
        if asLambda then internExprM (KExpr.mkLam name bi ty acc)
        else internExprM (KExpr.mkAll name bi ty acc)
      | .ldecl name ty val =>
        -- Let-bindings always close as `letE`, regardless of `asLambda`.
        -- `nonDep` is conservatively false (refining it would need a
        -- body-occurrence analysis at close time).
        internExprM (KExpr.mkLet name ty val acc false)
  return acc

/-- Abstract `body` over `fvars` and wrap in a chain of `lam` (or `letE` for
    `ldecl` entries) binders, innermost-first. `fvars[0]` becomes the
    outermost binder. Mirrors `Lean.LocalContext.mkLambda`. -/
def mkLambda (lctx : LocalContext m) (fvars : Array FVarId) (body : KExpr m) :
    InternM m (KExpr m) := do
  lctx.wrapBinders fvars (← abstractFVars body fvars) true

/-- Same shape as `mkLambda` but emits `all` for `cdecl` entries. Mirrors
    `Lean.LocalContext.mkForall`. -/
def mkPi (lctx : LocalContext m) (fvars : Array FVarId) (body : KExpr m) :
    InternM m (KExpr m) := do
  lctx.wrapBinders fvars (← abstractFVars body fvars) false

end LocalContext

/-- Cheap head-only fvar predicate. -/
def isFVar (e : KExpr m) : Bool :=
  match e with
  | .fvar .. => true
  | _ => false

end Ix.Tc

end
end
