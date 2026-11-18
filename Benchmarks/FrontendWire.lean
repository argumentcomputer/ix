import Benchmarks.FrontendRepresentative

/-! Canonical, lossless constant payloads, modulo bound-variable names and
cached content hashes. Both are intentionally omitted: binder names are alpha
irrelevant and cached hashes are derived data. All universe levels, binder
information, metadata, declaration flags and recursor rules are retained.
This is the constant environment, not the elaborator's transient lookup caches.
-/
namespace FrontendWire
open Ix Ix.Frontend.Elab
open scoped Ix.Frontend

inductive Wire where
  | num : Nat → Wire
  | text : String → Wire
  | node : Nat → List Wire → Wire
  deriving BEq, Repr, Inhabited

def seq (xs : List Wire) : Wire := .node 0 xs
def name : Ix.Name → Wire
  | .anonymous _ => .node 20 []
  | .str p s _ => .node 21 [name p, .text s]
  | .num p n _ => .node 22 [name p, .num n]
def names (ns : Array Ix.Name) : Wire := seq (ns.toList.map name)
def bool (b : Bool) : Wire := .num (if b then 1 else 0)
def level : Ix.Level → Wire
  | .zero _ => .node 0 []
  | .succ u _ => .node 1 [level u]
  | .max u v _ => .node 2 [level u, level v]
  | .imax u v _ => .node 3 [level u, level v]
  | .param n _ => .node 4 [name n]
  | .mvar n _ => .node 5 [name n]
def dataValue : Ix.DataValue → Wire
  | .ofString s => .node 0 [.text s]
  | .ofBool b => .node 1 [bool b]
  | .ofName n => .node 2 [name n]
  | .ofNat n => .node 3 [.num n]
  | .ofInt n => .node 4 [.text (reprStr n)]
  | .ofSyntax s => .node 5 [.text (reprStr s)]
def expr : Ix.Expr → Wire
  | .bvar i _ => .node 0 [.num i]
  | .sort u _ => .node 1 [level u]
  | .const n us _ => .node 2 [name n, seq (us.toList.map level)]
  | .app f a _ => .node 3 [expr f, expr a]
  | .lam _ a b bi _ => .node 4 [.num (Ix.Expr.binderInfoTag bi).toNat, expr a, expr b]
  | .forallE _ a b bi _ => .node 5 [.num (Ix.Expr.binderInfoTag bi).toNat, expr a, expr b]
  | .letE _ t v b nd _ => .node 6 [bool nd, expr t, expr v, expr b]
  | .lit (.natVal n) _ => .node 7 [.num n]
  | .lit (.strVal s) _ => .node 8 [.text s]
  | .mdata d e _ => .node 9 [seq (d.toList.map fun (n,v) => seq [name n, dataValue v]), expr e]
  | .proj n i e _ => .node 10 [name n, .num i, expr e]
  | .fvar n _ => .node 11 [name n]
  | .mvar n _ => .node 12 [name n]
def hints : Lean.ReducibilityHints → Wire
  | .opaque => .node 0 []
  | .abbrev => .node 1 []
  | .regular n => .node 2 [.num n.toNat]
def safety : Lean.DefinitionSafety → Wire
  | .safe => .num 0 | .unsafe => .num 1 | .partial => .num 2
def rule (r : Ix.RecursorRule) : Wire := seq [name r.ctor, .num r.nfields, expr r.rhs]
def constant (ci : Ix.ConstantInfo) : Wire :=
  let c := ci.getCnst
  let common := [name c.name, names c.levelParams, expr c.type]
  match ci with
  | .axiomInfo v => .node 100 (common ++ [bool v.isUnsafe])
  | .defnInfo v => .node 101 (common ++ [expr v.value, hints v.hints, safety v.safety, names v.all])
  | .thmInfo v => .node 102 (common ++ [expr v.value, names v.all])
  | .opaqueInfo v => .node 103 (common ++ [expr v.value, bool v.isUnsafe, names v.all])
  | .quotInfo v => .node 104 (common ++ [.num (match v.kind with
      | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3)])
  | .inductInfo v => .node 105 (common ++ [.num v.numParams, .num v.numIndices,
      names v.all, names v.ctors, .num v.numNested, bool v.isRec, bool v.isUnsafe, bool v.isReflexive])
  | .ctorInfo v => .node 106 (common ++ [name v.induct, .num v.cidx, .num v.numParams,
      .num v.numFields, bool v.isUnsafe])
  | .recInfo v => .node 107 (common ++ [names v.all, .num v.numParams, .num v.numIndices,
      .num v.numMotives, .num v.numMinors, seq (v.rules.toList.map rule), bool v.k, bool v.isUnsafe])

def constants (env : IxElabEnv) : List Ix.ConstantInfo :=
  (env.constOrder.filterMap env.find?).mergeSort fun a b =>
    match Ix.Frontend.charsCmp
      (Ix.Frontend.Name.toStringTotal a.getCnst.name).toList
      (Ix.Frontend.Name.toStringTotal b.getCnst.name).toList with
    | .gt => false | _ => true
def ofEnv (env : IxElabEnv) : Wire := seq ((constants env).map constant)

partial def json : Wire → Lean.Json
  | .num n => .arr #[Lean.toJson (0 : Nat), Lean.toJson n]
  | .text s => .arr #[Lean.toJson (1 : Nat), Lean.toJson s]
  | .node n xs => .arr #[Lean.toJson (2 : Nat), Lean.toJson n, .arr (xs.toArray.map json)]

end FrontendWire
