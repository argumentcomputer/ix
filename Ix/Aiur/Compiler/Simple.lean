module
public import Ix.Aiur.Compiler.Match

/-!
`simplifyTerm`: `Typed.Term` → `Simple.Term`.

Consumes `Typed.Term` directly (no more double `checkFunction`). Walks the
typed tree, invoking the decision-tree match compiler on every `match`, and
transforms `let` nodes into either `.letVar`, `.letWild`, or a rebuilt `match`
(when the pattern is non-trivial).

Non-exhaustive matches are accepted at compile time.
A `.failure` leaf in the decision tree is materialized as a match case with
no default, which becomes `Bytecode.Ctrl.match … none`. Evaluators surface
the unreached case at runtime via their own `.nonExhaustiveMatch` error.
-/

public section
@[expose] section

namespace Aiur

open Typed

/-- Temporary variable used when hoisting a complex-pattern `let` into a `match`.
Only valid when it doesn't shadow any other binding. Public so proofs in other
modules can cite the definition (e.g., via unfolding). -/
abbrev tmpVar : Local := .idx 0

/-- `simplifyTypedTerm` walks a typed term, producing a term of the same shape
whose `match`es have been pre-compiled down to the decision-tree form, and whose
`let`s bind only simple locals or wildcards. It operates in the `CheckError`
monad so it can surface non-exhaustiveness.

The traversal stays in `Typed.Term`; the final `Typed → Simple` mapping is done
in `MatchCompiler.typedToSimple` after this pass. -/
def simplifyTypedTerm (decls : Source.Decls) : Term → Except CheckError Term
  | .let τ e (.var x) v b => do
      let v' ← simplifyTypedTerm decls v
      let b' ← simplifyTypedTerm decls b
      pure (.let τ e (.var x) v' b')
  | .let τ e .wildcard v b => do
      let v' ← simplifyTypedTerm decls v
      let b' ← simplifyTypedTerm decls b
      pure (.let τ e .wildcard v' b')
  | .let τ e pat v b => do
      let v' ← simplifyTypedTerm decls v
      let b' ← simplifyTypedTerm decls b
      let tmp : Term := .var v'.typ false tmpVar
      let (tree, _diag) := MatchCompiler.runMatchCompiler decls tmp [(pat, b')]
      let body : Term :=
        match MatchCompiler.decisionToTyped b'.typ tmp.typ tree with
        | some rewrite => rewrite
        | none         => .match b'.typ b'.escapes tmp [(pat, b')]
      pure (.let τ e (.var tmpVar) v' body)
  | .match τ e scrut branches => do
      let scrut' ← simplifyTypedTerm decls scrut
      let branches' ← branches.attach.mapM fun pb =>
        (simplifyTypedTerm decls pb.1.2).map (Prod.mk pb.1.1)
      let (tree, _diag) := MatchCompiler.runMatchCompiler decls scrut' branches'
      match MatchCompiler.decisionToTyped τ scrut'.typ tree with
      | some rewrite => pure rewrite
      | none =>
        match scrut' with
        | .var .. => pure (.match τ e scrut' branches')
        | _ =>
          let tmp : Term := .var scrut'.typ false tmpVar
          let inner : Term := .match τ e tmp branches'
          pure (.let τ e (.var tmpVar) scrut' inner)
  | .ret τ e r => do
      let r' ← simplifyTypedTerm decls r
      pure (.ret τ e r')
  | .app τ e g tArgs args u => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => simplifyTypedTerm decls a
      pure (.app τ e g tArgs args' u)
  | .tuple τ e ts => do
      let ts' ← ts.attach.mapM fun ⟨t, _⟩ => simplifyTypedTerm decls t
      pure (.tuple τ e ts')
  | .array τ e ts => do
      let ts' ← ts.attach.mapM fun ⟨t, _⟩ => simplifyTypedTerm decls t
      pure (.array τ e ts')
  | .debug τ e l t r => do
      let t' ← match t with
        | none => pure none
        | some sub => do pure (some (← simplifyTypedTerm decls sub))
      let r' ← simplifyTypedTerm decls r
      pure (.debug τ e l t' r')
  | .assertEq τ e a b r => do
      let a' ← simplifyTypedTerm decls a
      let b' ← simplifyTypedTerm decls b
      let r' ← simplifyTypedTerm decls r
      pure (.assertEq τ e a' b' r')
  | .ioSetInfo τ e k i l r => do
      let k' ← simplifyTypedTerm decls k
      let i' ← simplifyTypedTerm decls i
      let l' ← simplifyTypedTerm decls l
      let r' ← simplifyTypedTerm decls r
      pure (.ioSetInfo τ e k' i' l' r')
  | .ioWrite τ e d r => do
      let d' ← simplifyTypedTerm decls d
      let r' ← simplifyTypedTerm decls r
      pure (.ioWrite τ e d' r')
  | .u8LessThan τ e a b => do
      let a' ← simplifyTypedTerm decls a
      let b' ← simplifyTypedTerm decls b
      pure (.u8LessThan τ e a' b')
  | .u32LessThan τ e a b => do
      let a' ← simplifyTypedTerm decls a
      let b' ← simplifyTypedTerm decls b
      pure (.u32LessThan τ e a' b')
  | t => pure t
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have : sizeOf (_, _) < sizeOf _ := List.sizeOf_lt_of_mem ‹_ ∈ _›
       grind)
    | (have hmem := Subtype.property ‹_›
       have := List.sizeOf_lt_of_mem hmem
       grind)

/-- Run `simplifyTypedTerm` on every function in a decls map. -/
def simplifyDecls (decls : Source.Decls) (typedDecls : Typed.Decls) :
    Except CheckError Typed.Decls := do
  typedDecls.foldlM (init := default) fun acc (name, d) => match d with
    | .function f => do
      let body' ← simplifyTypedTerm decls f.body
      pure (acc.insert name (.function { f with body := body' }))
    | .dataType dt => pure (acc.insert name (.dataType dt))
    | .constructor dt c => pure (acc.insert name (.constructor dt c))

/-- Full pipeline `Source.Toplevel` → `Typed.Decls`:
`mkDecls`, `wellFormedDecls`, typecheck, simplify. -/
def Source.Toplevel.checkAndSimplify (toplevel : Source.Toplevel) :
    Except CheckError Typed.Decls := do
  let decls ← toplevel.mkDecls
  wellFormedDecls decls
  let typedDecls ← decls.foldlM (init := default) fun acc (name, decl) => match decl with
    | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
    | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
    | .function f => do
      let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
      pure $ acc.insert name (.function f : Typed.Declaration)
  simplifyDecls decls typedDecls

end Aiur

end -- @[expose] section
end
