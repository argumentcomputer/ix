import IxCC.Own.Plain.Check
import IxCC.Own.Plain.ScopeSet
import IxCC.Src.Proof.NatMap

/-! # The scope check over sets equals the scope check over lists

`Own/Plain/ScopeSet.lean`'s set forms (`freshSet`, `scopeOkSet`, `scopeAltsSet`, `scopeOptSet`,
with `signatureArity` for a callee's arity) compute the list forms of `Own/Plain/Check.lean`
(`fresh`, `scopeOk`, `scopeAlts`, `scopeOpt`, with `signatures`) whenever the set and the list
have the same members. `programDomain` and `contractProgramDomain` run the set forms; their
`_function` lemmas (`Own/Plain/Proof/Admission.lean`) conclude the list forms through these. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId FunId Arg Rhs)

theorem natSet_contains_insert (s : Src.NatSet) (k x : Nat) :
    (s.insert k).contains x = (x == k || s.contains x) := by
  sorry

theorem contains_insertVars {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (xs : List Var) :
    ∀ x, (insertVars s xs).contains x = (live ++ xs).contains x := by
  sorry

theorem argInSet_eq {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (a : Arg) :
    argInSet s a = argIn live a := by
  sorry

theorem freshSet_eq {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (xs : List Var) :
    freshSet s xs = fresh live xs := by
  sorry

theorem signatureArity_eq (P : Fir.Program) (f : FunId) :
    signatureArity P f = (signatures P).lookup f := by
  sorry

theorem rhsInSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (r : Rhs) :
    rhsInSet P s r = rhsIn (signatures P) live r := by
  sorry

theorem scopeOkSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (joins : JoinArities) (c : Fir.Code) :
    scopeOkSet P s joins c = scopeOk (signatures P) live joins c := by
  sorry

theorem scopeAltsSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (joins : JoinArities) (alts : List Fir.Alt) :
    scopeAltsSet P s joins alts = scopeAlts (signatures P) live joins alts := by
  sorry

theorem scopeOptSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (joins : JoinArities) (d : Option Fir.Code) :
    scopeOptSet P s joins d = scopeOpt (signatures P) live joins d := by
  sorry

/-- **A function's scope check, set form = list form** (what `programDomain` and
`contractProgramDomain` run per numbered function: fresh parameters, then the body in their scope
with no join). -/
theorem functionScope_eq (P : Fir.Program) (ps : List Var) (body : Fir.Code) :
    (freshSet .leaf ps && scopeOkSet P (insertVars .leaf ps) [] body) =
      (fresh [] ps && scopeOk (signatures P) ps [] body) := by
  sorry

end IxCC.Own.Plain
