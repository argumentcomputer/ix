import Aiur.Semantics.WithCalls

/-!
# Guards on the calls an evaluation makes

A compiler's soundness proof builds an evaluation of a function body from a circuit row, and
consults a hypothesis about the row's calls at each call expression. A `CallGuard` lets that
hypothesis be asked only of calls the guard allows: it is a predicate on (environment,
expression) pairs that passes from an expression to the subexpressions its evaluation reaches
(`Reaches`), and that at a call allows the callee with the evaluated arguments.

`CallGuard.all` allows every call. A static analysis of the body gives a guard that allows
only the calls the analysis describes.
-/

namespace Aiur

variable {F : Type} [Field F] [DecidableEq F]

/-- `Reaches decls rom calls env expr env' expr'`: an evaluation of `expr` in `env` evaluates
its direct subexpression `expr'` in `env'`. A let body and a match arm are reached in the
environment extended by the bindings of the evaluated value. Every arm whose pattern matches
is reached, not only the first. -/
inductive Reaches (decls : Declarations) (rom : ROM F) (calls : CallRelation F) :
    Environment F → Expr F → Environment F → Expr F → Prop where
  | tuple {env : Environment F} {items : List (Expr F)} {item : Expr F} (member : item ∈ items) :
      Reaches decls rom calls env (.tuple items) env item
  | construct {env : Environment F} {name ctor : String} {items : List (Expr F)} {item : Expr F}
      (member : item ∈ items) : Reaches decls rom calls env (.construct name ctor items) env item
  | project {env : Environment F} {value : Expr F} {index : Nat} :
      Reaches decls rom calls env (.project value index) env value
  | letValue {env : Environment F} {pattern : Pattern F} {value body : Expr F} :
      Reaches decls rom calls env (.letValue pattern value body) env value
  | letBody {env bindings : Environment F} {pattern : Pattern F} {value body : Expr F}
      {input : Value F} (evaluated : ROMEvalExprWith decls rom calls env value input)
      (matched : pattern.bindings input = some bindings) :
      Reaches decls rom calls env (.letValue pattern value body) (bindings ++ env) body
  | store {env : Environment F} {value : Expr F} : Reaches decls rom calls env (.store value) env value
  | load {env : Environment F} {value : Expr F} : Reaches decls rom calls env (.load value) env value
  | hint {env : Environment F} {type : Ty} {key : Expr F} {channel : String} :
      Reaches decls rom calls env (.hint type key channel) env key
  | neg {env : Environment F} {value : Expr F} : Reaches decls rom calls env (.neg value) env value
  | binaryLeft {env : Environment F} {op : BinOp} {left right : Expr F} :
      Reaches decls rom calls env (.binary op left right) env left
  | binaryRight {env : Environment F} {op : BinOp} {left right : Expr F} :
      Reaches decls rom calls env (.binary op left right) env right
  | assertEqLeft {env : Environment F} {assertion : Assertion} {left right : Expr F} :
      Reaches decls rom calls env (.assertEq assertion left right) env left
  | assertEqRight {env : Environment F} {assertion : Assertion} {left right : Expr F} :
      Reaches decls rom calls env (.assertEq assertion left right) env right
  | ptrEqLeft {env : Environment F} {left right : Expr F} :
      Reaches decls rom calls env (.ptrEq left right) env left
  | ptrEqRight {env : Environment F} {left right : Expr F} :
      Reaches decls rom calls env (.ptrEq left right) env right
  | callArg {env : Environment F} {name : String} {args : List (Expr F)} {arg : Expr F}
      (member : arg ∈ args) : Reaches decls rom calls env (.call name args) env arg
  | matchScrutinee {env : Environment F} {scrutinee : Expr F} {arms : List (Pattern F × Expr F)} :
      Reaches decls rom calls env (.matchValue scrutinee arms) env scrutinee
  | matchArm {env bindings : Environment F} {scrutinee : Expr F}
      {arms : List (Pattern F × Expr F)} {arm : Pattern F × Expr F} {input : Value F}
      (evaluated : ROMEvalExprWith decls rom calls env scrutinee input) (member : arm ∈ arms)
      (matched : arm.1.bindings input = some bindings) :
      Reaches decls rom calls env (.matchValue scrutinee arms) (bindings ++ env) arm.2

/-- A predicate on (environment, expression) that evaluations preserve, with the calls it
allows. -/
structure CallGuard (decls : Declarations) (rom : ROM F) (calls : CallRelation F) where
  holds : Environment F → Expr F → Prop
  allowed : String → List (Value F) → Prop
  sub : ∀ {env env' : Environment F} {expr expr' : Expr F}, holds env expr →
    Reaches decls rom calls env expr env' expr' → holds env' expr'
  call : ∀ {env : Environment F} {name : String} {args : List (Expr F)} {values : List (Value F)},
    holds env (.call name args) → ROMEvalArgsWith decls rom calls env args values →
    allowed name values

/-- The guard that holds everywhere and allows every call. -/
def CallGuard.all (decls : Declarations) (rom : ROM F) (calls : CallRelation F) :
    CallGuard decls rom calls :=
  ⟨fun _ _ => True, fun _ _ => True, fun _ _ => trivial, fun _ _ => trivial⟩

end Aiur
