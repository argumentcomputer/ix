import Ix.Aiur.Match
import Ix.Aiur.Check

namespace Aiur

/-- This temporary variable can only be used when it does not shadow any other internal. -/
private abbrev tmpVar := Local.idx 0

partial def simplifyTerm (decls: Decls) : Term → Term
  | .let var@(.var _) val body => .let var (recr val) (recr body)
  -- NOTE: This would not be safe in case Aiur allows side-effects. A sequencing operation would be needed.
  | .let .wildcard _ body => recr body
  | .let pat val body =>
    let mtch := .match (.var tmpVar) [(pat, body)]
    .let (.var tmpVar) (recr val) (recr mtch)
  | .match term branches =>
    let (tree, _diag) := runMatchCompiler decls term branches
    match decisionToTerm tree with
    | some term => term
    | none => unreachable!
  | .ret r => .ret (recr r)
  | .app global args => .app global (args.map recr)
  | .preimg global out => .preimg global (recr out)
  | .ffi global args => .ffi global (args.map recr)
  | .if b t f => .if (recr b) (recr t) (recr f)
  | .data (.tuple args) => .data (.tuple (args.map recr))
  | t => t
where
  recr := simplifyTerm decls

def simplify (decls : Decls) : Decls :=
  decls.map fun decl => match decl with
    | .function function => .function { function with body := simplifyTerm decls function.body }
    | _ => decl

def checkAndSimplifyToplevel (toplevel : Toplevel) : Except CheckError TypedDecls := do
  let decls ← toplevel.mkDecls
  wellFormedDecls decls
  -- TODO: do not duplicate type inference. I.e. do simplification on typed expressions
  toplevel.functions.forM fun function => do
    let _ ← (checkFunction function) (getFunctionContext function decls)
  let decls := simplify decls
  decls.foldlM (init := default) fun typedDecls (name, decl) => match decl with
    | .constructor d c => pure $ typedDecls.insert name (.constructor d c)
    | .dataType d => pure $ typedDecls.insert name (.dataType d)
    | .function f => do
      let _ ← (checkFunction f) (getFunctionContext f decls)
      let f ← (checkFunction f) (getFunctionContext f decls)
      pure $ typedDecls.insert name (.function f)
    | .gadget g => pure $ typedDecls.insert name (.gadget g)

end Aiur
