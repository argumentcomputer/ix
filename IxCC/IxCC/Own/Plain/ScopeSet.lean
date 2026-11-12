import IxCC.Fir.Syntax

/-! # The source scope check over sets

`programDomain` and `contractProgramDomain` (`Own/Plain/Check.lean`) check every numbered
function's parameters and body scope. The list forms there (`fresh`, `scopeOk`, `scopeAlts`,
`scopeOpt`, over `signatures`) keep the scope as a list, with one search per variable occurrence
and one copy per binder, so a function with `P` parameters costs about `P²` steps (parameters cost
no Anf node, so the node budgets do not bound this), and look a callee's arity up in a list of all
the program's functions. These are the same checks with the scope as a `Src.NatSet` and the arity
read from the program by `Fir.Program.fun?`: each lookup or insertion is logarithmic in the
variable or function number. `Own/Plain/Proof/ScopeSet.lean` proves each equal to its list form
whenever the set and the list have the same members (`scopeOkSet_eq`, `freshSet_eq`). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId FunId Arg Rhs)

/-- `argIn`, the scope a set. -/
def argInSet (live : Src.NatSet) : Arg → Bool
  | .var x => live.contains x
  | _ => true

/-- `fresh`, the scope a set: no variable of the list is in scope or occurs twice in it. -/
def freshSet (live : Src.NatSet) : List Var → Bool
  | [] => true
  | x :: xs => !live.contains x && freshSet (live.insert x) xs

/-- The scope with every variable of the list added. -/
def insertVars (live : Src.NatSet) : List Var → Src.NatSet
  | [] => live
  | x :: xs => insertVars (live.insert x) xs

/-- The arity of numbered function `f`: that of `P.fun? f` when `f < P.size`, none otherwise
(an entry past `P.size` has no arity; `(signatures P).lookup f`). -/
def signatureArity (P : Fir.Program) (f : FunId) : Option Nat :=
  if f < P.size then (P.fun? f).map (·.arity) else none

/-- `rhsIn`, the scope a set and the arities read from the program. -/
def rhsInSet (P : Fir.Program) (live : Src.NatSet) : Rhs → Bool
  | .arg a => argInSet live a
  | .ctor c args => decide (args.length = c.arity) && args.all (argInSet live) &&
      decide (c.nscalar = 0) && decide (c.fieldKinds.length = c.nobj) &&
      c.fieldKinds.all (fun k => decide (k = .shared))
  | .proj x _ _ => live.contains x
  | .prim p args => decide (args.length = p.arity) && args.all (argInSet live)
  | .call f args => decide (signatureArity P f = some args.length) && args.all (argInSet live)

mutual
/-- `scopeOk`, the scope a set and the arities read from the program. -/
def scopeOkSet (P : Fir.Program) (live : Src.NatSet) (joins : List (JoinId × Nat)) :
    Fir.Code → Bool
  | .bind x r k => !live.contains x && rhsInSet P live r &&
      scopeOkSet P (live.insert x) joins k
  | .jp j ps rec body k =>
    decide (joins.lookup j = none) && freshSet live ps &&
      scopeOkSet P (insertVars live ps) (if rec then (j, ps.length) :: joins else joins) body &&
      scopeOkSet P live ((j, ps.length) :: joins) k
  | .jmp j args => decide (joins.lookup j = some args.length) && args.all (argInSet live)
  | .case x alts dflt => live.contains x && scopeAltsSet P live joins alts &&
      scopeOptSet P live joins dflt
  | .ret a => argInSet live a
  | .tcall f args => decide (signatureArity P f = some args.length) && args.all (argInSet live)
  | .trap => true

/-- `scopeAlts`, the scope a set. -/
def scopeAltsSet (P : Fir.Program) (live : Src.NatSet) (joins : List (JoinId × Nat)) :
    List Fir.Alt → Bool
  | [] => true
  | .mk _ body :: alts => scopeOkSet P live joins body && scopeAltsSet P live joins alts

/-- `scopeOpt`, the scope a set. -/
def scopeOptSet (P : Fir.Program) (live : Src.NatSet) (joins : List (JoinId × Nat)) :
    Option Fir.Code → Bool
  | none => true
  | some c => scopeOkSet P live joins c
end

end IxCC.Own.Plain
