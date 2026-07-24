module

public import LSpec
public import Ix.Ground

/-!
Unit tests for `Ix.Ground` (the pure-Lean port of
`crates/compile/src/ground.rs`).

Coverage mirrors the Rust `#[cfg(test)]` module in ground.rs (grounded
constants, missing refs, out-of-scope bvars, mvars, level params,
inductive ctor checks, depth increments, fvars, propagation) plus
Lean-side checks of the exact traversal/cache semantics: the
`(binder-depth, expr)` cache key, sub-check ordering (ctors before
type, rec rules before type, const levels before env lookup, proj env
lookup before struct), and worklist termination on cyclic in-ref
graphs.

Per the contract documented on `Ix.proliferateUngrounded`, everything
transitive is asserted by error KIND only (`GroundError.kind`) — never
by transitive `.ref` attribution payloads, which are pop-order
dependent. Immediate-error payloads (which ARE order-independent) are
asserted where the Rust tests assert them.
-/

public section

namespace Tests.Ground

open LSpec
open Ix (Name Level Expr Environment ConstantInfo RecursorRule
  GroundError GroundErrorKind groundConstCheck groundConsts
  proliferateUngrounded)

/-! ## Construction helpers -/

def nm (s : String) : Name := Name.mkStr .mkAnon s

def sort0 : Expr := Expr.mkSort Level.mkZero

def axiomC (name : String) (typ : Expr) (lps : Array Name := #[]) : ConstantInfo :=
  .axiomInfo { cnst := { name := nm name, levelParams := lps, type := typ },
               isUnsafe := false }

def defnC (name : String) (typ value : Expr) : ConstantInfo :=
  .defnInfo { cnst := { name := nm name, levelParams := #[], type := typ },
              value, hints := .opaque, safety := .safe, all := #[nm name] }

def thmC (name : String) (typ value : Expr) : ConstantInfo :=
  .thmInfo { cnst := { name := nm name, levelParams := #[], type := typ },
             value, all := #[nm name] }

def opaqueC (name : String) (typ value : Expr) : ConstantInfo :=
  .opaqueInfo { cnst := { name := nm name, levelParams := #[], type := typ },
                value, isUnsafe := false, all := #[nm name] }

def quotC (name : String) (typ : Expr) : ConstantInfo :=
  .quotInfo { cnst := { name := nm name, levelParams := #[], type := typ },
              kind := .type }

def ctorC (name : String) (induct : String) (typ : Expr := sort0) : ConstantInfo :=
  .ctorInfo { cnst := { name := nm name, levelParams := #[], type := typ },
              induct := nm induct, cidx := 0, numParams := 0, numFields := 0,
              isUnsafe := false }

def inductC (name : String) (ctors : Array Name) (typ : Expr := sort0) :
    ConstantInfo :=
  .inductInfo { cnst := { name := nm name, levelParams := #[], type := typ },
                numParams := 0, numIndices := 0, all := #[nm name], ctors,
                numNested := 0, isRec := false, isUnsafe := false,
                isReflexive := false }

def recC (name : String) (rules : Array RecursorRule) (typ : Expr := sort0) :
    ConstantInfo :=
  .recInfo { cnst := { name := nm name, levelParams := #[], type := typ },
             all := #[nm name], numParams := 0, numIndices := 0,
             numMotives := 1, numMinors := 0, rules, k := false,
             isUnsafe := false }

def mkEnv (cs : List (Name × ConstantInfo)) : Environment :=
  ⟨Std.HashMap.ofList cs⟩

def refsMap (l : List (Name × List Name)) : Ix.Map Name (Ix.Set Name) :=
  l.foldl (init := {}) fun m (k, vs) =>
    m.insert k (vs.foldl (init := ({} : Ix.Set Name)) fun s v => s.insert v)

/-! ## Assertion helpers (kind-based, per the proliferation contract) -/

/-- Per-constant check result as an error, `none` = grounded. -/
def checkErr? (c : ConstantInfo) (env : Environment) : Option GroundError :=
  match groundConstCheck c env with
  | .ok _ => none
  | .error e => some e

def checkKind? (c : ConstantInfo) (env : Environment) : Option GroundErrorKind :=
  (checkErr? c env).map (·.kind)

def kindAt? (errs : Ix.Map Name GroundError) (s : String) :
    Option GroundErrorKind :=
  (errs.get? (nm s)).map (·.kind)

def refPayload? : GroundError → Option Name
  | .ref n => some n
  | _ => none

def varBinds? : GroundError → Option Nat
  | .var _ b => some b
  | _ => none

def indcInfoIsSome? : GroundError → Option Bool
  | .indc _ ci => some ci.isSome
  | _ => none

/-! ## Grounded constants (Rust: grounded_axiom,
grounded_defn_with_bvar_in_lam, grounded_level_param_when_declared) -/

def groundedTests : TestSeq :=
  test "grounded axiom: Sort 0 type, empty groundConsts result"
    ((let a := axiomC "A" sort0
      let env := mkEnv [(nm "A", a)]
      checkKind? a env == none
        && (groundConsts env (refsMap [(nm "A", [])])).isEmpty : Bool))
  ++ test "grounded defn: fun (_ : Sort 0) => #0 (bvar under one binder)"
    ((let f := defnC "f" sort0
        (Expr.mkLam .mkAnon sort0 (Expr.mkBVar 0) .default)
      let env := mkEnv [(nm "f", f)]
      checkKind? f env == none && (groundConsts env {}).isEmpty : Bool))
  ++ test "grounded level param: A.{u} : Sort u with u declared"
    ((let a := axiomC "A" (Expr.mkSort (Level.mkParam (nm "u"))) #[nm "u"]
      checkKind? a (mkEnv [(nm "A", a)]) == none : Bool))
  ++ test "letE depths: body at binds+1 grounded, value at binds escapes"
    ((let ok := axiomC "Ok" (Expr.mkLetE .mkAnon sort0 sort0 (Expr.mkBVar 0) false)
      let bad := axiomC "Bad" (Expr.mkLetE .mkAnon sort0 (Expr.mkBVar 0) sort0 false)
      let env := mkEnv [(nm "Ok", ok), (nm "Bad", bad)]
      checkKind? ok env == none && checkKind? bad env == some .var : Bool))
  ++ test "mdata is transparent (same binder depth)"
    ((let b := axiomC "B" sort0
      let a := axiomC "A" (Expr.mkMData #[] (Expr.mkConst (nm "B") #[]))
      let env := mkEnv [(nm "A", a), (nm "B", b)]
      checkKind? a env == none : Bool))
  ++ test "lit is grounded"
    ((let a := axiomC "L" (Expr.mkLit (.natVal 42))
      checkKind? a (mkEnv [(nm "L", a)]) == none : Bool))
  ++ test "inductive with a proper ctor is grounded"
    ((let t := inductC "T" #[nm "T.mk"]
      let mk := ctorC "T.mk" "T"
      let env := mkEnv [(nm "T", t), (nm "T.mk", mk)]
      checkKind? t env == none && (groundConsts env {}).isEmpty : Bool))

/-! ## Immediate error kinds (Rust: ungrounded_missing_ref,
ungrounded_bvar_out_of_scope, ungrounded_mvar, ungrounded_level_param,
inductive_missing_ctor, inductive_ctor_wrong_kind,
binding_increments_depth, fvar_is_ungrounded) -/

def immediateErrorTests : TestSeq :=
  test "missing const ref: A : B with B absent -> ref B"
    ((let a := axiomC "A" (Expr.mkConst (nm "B") #[])
      let env := mkEnv [(nm "A", a)]
      checkKind? a env == some .ref
        && (checkErr? a env).bind refPayload? == some (nm "B") : Bool))
  ++ test "bvar with no enclosing binder -> var at binds 0"
    ((let a := axiomC "A" (Expr.mkBVar 0)
      let env := mkEnv [(nm "A", a)]
      checkKind? a env == some .var
        && (checkErr? a env).bind varBinds? == some 0 : Bool))
  ++ test "lam: #0 grounded, #1 escapes with binds 1"
    ((let ok := defnC "ok" sort0
        (Expr.mkLam .mkAnon sort0 (Expr.mkBVar 0) .default)
      let bad := defnC "bad" sort0
        (Expr.mkLam .mkAnon sort0 (Expr.mkBVar 1) .default)
      let env := mkEnv [(nm "ok", ok), (nm "bad", bad)]
      checkKind? ok env == none
        && checkKind? bad env == some .var
        && (checkErr? bad env).bind varBinds? == some 1 : Bool))
  ++ test "forallE: #0 grounded, #1 escapes"
    ((let ok := axiomC "Ok" (Expr.mkForallE .mkAnon sort0 (Expr.mkBVar 0) .default)
      let bad := axiomC "Bad" (Expr.mkForallE .mkAnon sort0 (Expr.mkBVar 1) .default)
      let env := mkEnv [(nm "Ok", ok), (nm "Bad", bad)]
      checkKind? ok env == none && checkKind? bad env == some .var : Bool))
  ++ test "undeclared level param -> level"
    ((let a := axiomC "A" (Expr.mkSort (Level.mkParam (nm "u")))
      checkKind? a (mkEnv [(nm "A", a)]) == some .level : Bool))
  ++ test "level mvar -> level"
    ((let a := axiomC "A" (Expr.mkSort (Level.mkMvar (nm "m")))
      checkKind? a (mkEnv [(nm "A", a)]) == some .level : Bool))
  ++ test "level params checked inside succ/max/imax spines"
    ((let u := Level.mkParam (nm "u")
      let a := axiomC "A" (Expr.mkSort (Level.mkSucc (Level.mkMax Level.mkZero
        (Level.mkIMax u Level.mkZero))))
      checkKind? a (mkEnv [(nm "A", a)]) == some .level : Bool))
  ++ test "expression mvar -> mvar"
    ((let a := axiomC "A" (Expr.mkMVar (nm "m"))
      checkKind? a (mkEnv [(nm "A", a)]) == some .mvar : Bool))
  ++ test "fvar -> var at binds 0"
    ((let a := axiomC "A" (Expr.mkFVar (nm "x"))
      let env := mkEnv [(nm "A", a)]
      checkKind? a env == some .var
        && (checkErr? a env).bind varBinds? == some 0 : Bool))
  ++ test "inductive missing ctor -> indc with info none"
    ((let t := inductC "T" #[nm "T.mk"]
      let env := mkEnv [(nm "T", t)]
      checkKind? t env == some .indc
        && (checkErr? t env).bind indcInfoIsSome? == some false : Bool))
  ++ test "inductive ctor of wrong kind -> indc with info some"
    ((let t := inductC "T" #[nm "T.mk"]
      let env := mkEnv [(nm "T", t), (nm "T.mk", axiomC "T.mk" sort0)]
      checkKind? t env == some .indc
        && (checkErr? t env).bind indcInfoIsSome? == some true : Bool))
  ++ test "thm and opaque check their values"
    ((let t := thmC "t" sort0 (Expr.mkMVar (nm "m"))
      let o := opaqueC "o" sort0 (Expr.mkFVar (nm "x"))
      let env := mkEnv [(nm "t", t), (nm "o", o)]
      checkKind? t env == some .mvar && checkKind? o env == some .var : Bool))
  ++ test "quot and ctor check their types"
    ((let q := quotC "q" (Expr.mkBVar 0)
      let c := ctorC "c" "T" (Expr.mkMVar (nm "m"))
      let env := mkEnv [(nm "q", q), (nm "c", c)]
      checkKind? q env == some .var && checkKind? c env == some .mvar : Bool))

/-! ## Traversal-order and cache-key semantics -/

def orderingCacheTests : TestSeq :=
  test "inductive: ctor presence checked BEFORE its own type"
    ((let t := inductC "T" #[nm "T.mk"] (Expr.mkConst (nm "Missing") #[])
      checkKind? t (mkEnv [(nm "T", t)]) == some .indc : Bool))
  ++ test "recursor: rule rhs checked BEFORE its own type"
    ((let r := recC "R"
        #[{ ctor := nm "T.mk", nfields := 0,
            rhs := Expr.mkConst (nm "Missing") #[] }]
        (Expr.mkMVar (nm "m"))
      checkKind? r (mkEnv [(nm "R", r)]) == some .ref : Bool))
  ++ test "defn: type checked BEFORE value"
    ((let f := defnC "f" (Expr.mkConst (nm "Missing") #[]) (Expr.mkMVar (nm "m"))
      checkKind? f (mkEnv [(nm "f", f)]) == some .ref : Bool))
  ++ test "const: level args checked BEFORE the env lookup"
    ((let a := axiomC "A" (Expr.mkConst (nm "B") #[Level.mkParam (nm "u")])
      -- u undeclared AND B missing: levels first -> level, not ref
      checkKind? a (mkEnv [(nm "A", a)]) == some .level : Bool))
  ++ test "proj: type-name env lookup BEFORE recursing into the struct"
    ((let a := axiomC "A" (Expr.mkProj (nm "Missing") 0 (Expr.mkMVar (nm "m")))
      checkKind? a (mkEnv [(nm "A", a)]) == some .ref : Bool))
  ++ test "proj: struct recursed once the type name resolves"
    ((let s := axiomC "S" sort0
      let a := axiomC "A" (Expr.mkProj (nm "S") 0 (Expr.mkMVar (nm "m")))
      let env := mkEnv [(nm "S", s), (nm "A", a)]
      checkKind? a env == some .mvar : Bool))
  ++ test "expr cache keys on (binder-depth, expr): #0 rechecked at depth 0"
    ((-- (fun (_ : Sort 0) => #0) #0 — the App visits the lam first,
      -- caching #0 at depth 1 (in scope); the argument #0 at depth 0
      -- must MISS the cache and fail. An expr-only cache key would
      -- wrongly skip it and report grounded.
      let e := Expr.mkApp
        (Expr.mkLam .mkAnon sort0 (Expr.mkBVar 0) .default)
        (Expr.mkBVar 0)
      let a := axiomC "A" e
      let env := mkEnv [(nm "A", a)]
      checkKind? a env == some .var
        && (checkErr? a env).bind varBinds? == some 0 : Bool))

/-! ## Transitive proliferation (Rust: propagation_through_in_refs).
Kind-only assertions for everything transitive. -/

def proliferationTests : TestSeq :=
  test "A refs ungrounded B -> both ungrounded; bystander D grounded"
    ((let b := axiomC "B" (Expr.mkConst (nm "C") #[]) -- C not in env
      let a := axiomC "A" (Expr.mkConst (nm "B") #[])
      let d := axiomC "D" sort0
      let env := mkEnv [(nm "B", b), (nm "A", a), (nm "D", d)]
      let inRefs := refsMap
        [(nm "C", [nm "B"]), (nm "B", [nm "A"]), (nm "A", []), (nm "D", [])]
      let errs := groundConsts env inRefs
      errs.size == 2
        && kindAt? errs "B" == some .ref
        && kindAt? errs "A" == some .ref
        -- immediate attribution (B's own error) IS order-independent:
        && (errs.get? (nm "B")).bind refPayload? == some (nm "C")
        && (errs.get? (nm "D")).isNone : Bool))
  ++ test "three-hop chain: result SET invariant under env insertion order"
    ((let c := axiomC "C" (Expr.mkConst (nm "X") #[]) -- X not in env
      let b := axiomC "B" (Expr.mkConst (nm "C") #[])
      let a := axiomC "A" (Expr.mkConst (nm "B") #[])
      let d := axiomC "D" sort0
      let l := [(nm "A", a), (nm "B", b), (nm "C", c), (nm "D", d)]
      let inRefs := refsMap
        [(nm "X", [nm "C"]), (nm "C", [nm "B"]), (nm "B", [nm "A"])]
      let e1 := groundConsts (mkEnv l) inRefs
      let e2 := groundConsts (mkEnv l.reverse) inRefs
      e1.size == 3 && e2.size == 3
        && ["A", "B", "C"].all (fun s =>
             kindAt? e1 s == some .ref && kindAt? e2 s == some .ref)
        && (e1.get? (nm "D")).isNone && (e2.get? (nm "D")).isNone : Bool))
  ++ test "proliferateUngrounded: vacant-only inserts, grounded refs ignored"
    ((let seed : Ix.Map Name GroundError :=
        ({} : Ix.Map Name GroundError).insert (nm "B") (.ref (nm "X"))
      -- G is grounded (not in seed): its in-refs must NOT leak in.
      let inRefs := refsMap [(nm "B", [nm "A"]), (nm "G", [nm "H"])]
      let out := proliferateUngrounded seed inRefs
      out.size == 2
        -- the seeded (immediate) entry is never overwritten:
        && (out.get? (nm "B")).bind refPayload? == some (nm "X")
        && kindAt? out "A" == some .ref
        && (out.get? (nm "H")).isNone : Bool))
  ++ test "proliferateUngrounded terminates on cyclic in-ref graphs"
    ((let seed : Ix.Map Name GroundError :=
        ({} : Ix.Map Name GroundError).insert (nm "B") (.ref (nm "C"))
      -- A and B reference each other; the visited-set must break the cycle.
      let inRefs := refsMap
        [(nm "C", [nm "B"]), (nm "B", [nm "A"]), (nm "A", [nm "B"])]
      let out := proliferateUngrounded seed inRefs
      out.size == 2
        && kindAt? out "A" == some .ref
        && kindAt? out "B" == some .ref : Bool))

public def suite : List TestSeq :=
  [groundedTests, immediateErrorTests, orderingCacheTests, proliferationTests]

end Tests.Ground

end
