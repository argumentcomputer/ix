import Ix.Aiur.Match
import Ix.Aiur.Check

namespace Aiur

/-- This temporary variable can only be used when it does not shadow any other internal. -/
private abbrev tmpVar := Local.idx 0

partial def simplifyTerm (decls : Decls) : Term → Term
  | .let var@(.var _) val body => .let var (recr val) (recr body)
  -- NOTE: This would not be safe in case Aiur allows side-effects.
  -- A sequencing operation would be needed.
  | .let .wildcard _ body => recr body
  | .let pat val body =>
    let mtch := .match (.var tmpVar) [(pat, body)]
    .let (.var tmpVar) (recr val) (recr mtch)
  | .match term branches =>
    let simpBranches := branches.map (fun (pat, term) => (pat, recr term))
    let (tree, _diag) := runMatchCompiler decls (recr term) simpBranches
    match decisionToTerm tree with
    | some term => term
    | none => unreachable!
  | .ret r => .ret (recr r)
  | .app global args => .app global (args.map recr)
  | .data (.tuple args) => .data (.tuple (args.map recr))
  | .data (.array args) => .data (.array (args.map recr))
  | .debug label term ret => .debug label (term.map recr) (recr ret)
  | t => t
where
  recr := simplifyTerm decls

def Toplevel.checkAndSimplify (toplevel : Toplevel) : Except CheckError TypedDecls := do
  let decls ← toplevel.mkDecls
  wellFormedDecls decls
  -- The first check happens on the original terms.
  toplevel.functions.forM fun function => do
    let _ ← (checkFunction function) (getFunctionContext function decls)
  let decls := decls.map fun decl => match decl with
    | .function f => .function { f with body := simplifyTerm decls f.body }
    | _ => decl
  decls.foldlM (init := default) fun typedDecls (name, decl) => match decl with
    | .constructor d c => pure $ typedDecls.insert name (.constructor d c)
    | .dataType d => pure $ typedDecls.insert name (.dataType d)
    | .function f => do
      -- The second check happens on the simplified terms.
      let f ← (checkFunction f) (getFunctionContext f decls)
      pure $ typedDecls.insert name (.function f)

end Aiur
