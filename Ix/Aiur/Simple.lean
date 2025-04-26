import Ix.Aiur.Match

namespace Aiur

/-- This temporary variable can only be used when it does not shadow any other internal. -/
private abbrev tmpVar := Local.idx 0

partial def simplifyTerm (decls: Decls) : Term → Term
  | .let var@(.var _) val body => .let var (recr val) (recr body)
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
  | .if b t f => .if (recr b) (recr t) (recr f)
  | .data (.tuple args) => .data (.tuple (args.map recr))
  | t => t
where
  recr := simplifyTerm decls

def simplify (decls : Decls) : Decls :=
  decls.map fun _ decl => match decl with
    | (.function function) => .function { function with body := simplifyTerm decls function.body }
    | _ => decl

end Aiur
