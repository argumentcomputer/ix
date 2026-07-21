module

public import LSpec
public import Ix.AuxGen.Recursor

/-!
Property tests for the pure (kernel-free) helpers of
`Ix.AuxGen.Recursor` (port of
`crates/compile/src/compile/aux_gen/recursor.rs`).

Every expected value was derived by hand-tracing the Rust bodies
(`reorder_flat_by_layout`, `infer_implicit`, `name_append_after`,
`collect_binders`, `maximize_occurrence_levels`,
`match_classes_against_app`, `collect_const_refs`); expression/level
assertions are hash-based `==` (bit-parity, not just structural).

Not registered in `Tests/Main.lean`; suite entry point is
`Tests.AuxGen.Recursor.suite`.
-/

public section

namespace Tests.AuxGen.Recursor

open LSpec
open Ix.AuxGen
open Ix (Name Level Expr)

def nm (s : String) : Name := Name.mkStr .mkAnon s
def u : Level := Level.mkParam (nm "u")
def v : Level := Level.mkParam (nm "v")
def prop : Expr := Expr.mkSort Level.mkZero

def fm (s : String) : CompileFlatMember :=
  { name := nm s, specParams := #[], occurrenceLevelArgs := #[]
    ownParams := 0, nIndices := 0 }

def mkLayout (perm : Array UInt64) : Ixon.AuxLayout :=
  { perm, sourceCtorCounts := #[] }

def flatNames : Except (Array CompileFlatMember × String) (Array CompileFlatMember) →
    Option (List String)
  | .ok f => some (f.toList.map (·.name.pretty))
  | .error _ => none

/-- `reorder_flat_by_layout` (recursor.rs:340) happy/roundtrip paths. -/
def reorderTests : TestSeq :=
  test "reorderFlatByLayout: no aux section is a no-op"
    ((flatNames (reorderFlatByLayout #[fm "A", fm "B"] 2 (mkLayout #[]))
      == some ["A", "B"] : Bool))
  ++ test "reorderFlatByLayout: identity perm is a roundtrip"
    ((flatNames
        (reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1 (mkLayout #[0, 1]))
      == some ["A", "x", "y"] : Bool))
  ++ test "reorderFlatByLayout: perm [1,0] swaps the aux tail"
    ((flatNames
        (reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1 (mkLayout #[1, 0]))
      == some ["A", "y", "x"] : Bool))
  ++ test "reorderFlatByLayout: alpha-collapse many-to-one takes FIRST source"
    -- perm = [1, 0, 0]: slot 1 ← source 0 ("x"), slot 0 ← source 1 ("y");
    -- source 2 also claims slot 0 but the first mapping wins (stable
    -- rule), and source 2 ≥ n_aux is ignored by the `source_j < n_aux`
    -- guard anyway.
    ((flatNames
        (reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1 (mkLayout #[1, 0, 0]))
      == some ["A", "y", "x"] : Bool))

/-- `reorder_flat_by_layout` error branches (shape mismatches). -/
def reorderErrorTests : TestSeq :=
  test "reorderFlatByLayout: perm claiming wrong slot count errors"
    (((reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1 (mkLayout #[0]))
        matches .error _ : Bool))
  ++ test "reorderFlatByLayout: short perm (fewer sources than auxes) errors"
    -- perm = [1]: max_canon = 2 == n_aux, but perm.size 1 < n_aux 2.
    (((reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1 (mkLayout #[1]))
        matches .error _ : Bool))
  ++ test "reorderFlatByLayout: PERM_OUT_OF_SCC pads are ignored"
    (((flatNames (reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1
        (mkLayout #[1, 0, UInt64.ofNat PERM_OUT_OF_SCC])))
      == some ["A", "y", "x"] : Bool))
  ++ test "reorderFlatByLayout: canonical slot with no source mapping errors"
    -- perm maps both sources to slot 1; slot 0 never filled.
    (((reorderFlatByLayout #[fm "A", fm "x", fm "y"] 1 (mkLayout #[1, 1]))
        matches .error _ : Bool))

/-- `infer_implicit` (recursor.rs:2208): binders whose variable feeds a
    later explicit domain become implicit; others stay explicit. -/
def inferImplicitTests : TestSeq :=
  -- ∀ (α : Sort u) (x : α), α — α (BVar 1 in x's domain, explicit) is
  -- used in an explicit domain → becomes implicit; x stays explicit.
  test "inferImplicit marks a domain-feeding binder implicit"
    ((let ty := Expr.mkForallE (nm "α") (Expr.mkSort u)
        (Expr.mkForallE (nm "x") (Expr.mkBVar 0) (Expr.mkBVar 1) .default)
        .default
      inferImplicit ty 1000
        == Expr.mkForallE (nm "α") (Expr.mkSort u)
          (Expr.mkForallE (nm "x") (Expr.mkBVar 0) (Expr.mkBVar 1) .default)
          .implicit : Bool))
  ++ test "inferImplicit leaves a range-only binder explicit (strict domains)"
    -- ∀ (α : Sort u), α — α only appears in the range, not a domain.
    ((let ty := Expr.mkForallE (nm "α") (Expr.mkSort u) (Expr.mkBVar 0) .default
      inferImplicit ty 1000 == ty : Bool))
  ++ test "inferImplicit with numParams = 0 is the identity"
    ((let ty := Expr.mkForallE (nm "α") (Expr.mkSort u)
        (Expr.mkForallE (nm "x") (Expr.mkBVar 0) (Expr.mkBVar 1) .default)
        .default
      inferImplicit ty 0 == ty : Bool))
  ++ test "inferImplicit respects the numParams cutoff"
    -- Only the outermost binder is eligible; the inner chain is left
    -- alone even though its binder feeds an explicit domain.
    ((let inner := Expr.mkForallE (nm "β") (Expr.mkSort u)
        (Expr.mkForallE (nm "y") (Expr.mkBVar 0) (Expr.mkBVar 1) .default)
        .default
      let ty := Expr.mkForallE (nm "n") (Expr.mkConst (nm "Nat") #[]) inner
        .default
      inferImplicit ty 1
        == Expr.mkForallE (nm "n") (Expr.mkConst (nm "Nat") #[]) inner
          .default : Bool))

/-- `name_append_after` (recursor.rs:2021) incl. the hygienic-name case. -/
def nameAppendAfterTests : TestSeq :=
  test "nameAppendAfter on a plain str name appends in place"
    ((nameAppendAfter (nm "a") "_ih" == nm "a_ih" : Bool))
  ++ test "nameAppendAfter on a dotted name touches the DEEPEST str"
    ((nameAppendAfter (Name.mkStr (nm "A") "b") "_ih"
      == Name.mkStr (nm "A_ih") "b" : Bool))
  ++ test "nameAppendAfter on anonymous wraps in a str"
    ((nameAppendAfter Name.mkAnon "_ih" == nm "_ih" : Bool))
  ++ test "nameAppendAfter recurses through Num wrappers (hygienic names)"
    -- Num(Str(Str(Anon,"a"),"_hyg"),0) → Num(Str(Str(Anon,"a_ih"),"_hyg"),0)
    ((nameAppendAfter (Name.mkNat (Name.mkStr (nm "a") "_hyg") 0) "_ih"
      == Name.mkNat (Name.mkStr (nm "a_ih") "_hyg") 0 : Bool))

/-- `collect_binders` (recursor.rs:894): count + annotation stripping. -/
def collectBindersTests : TestSeq :=
  test "collectBinders stops at the first non-forall"
    ((let ty := Expr.mkForallE (nm "x") prop
        (Expr.mkForallE (nm "y") prop prop .implicit) .default
      let bs := collectBinders ty 5
      bs.size == 2 && bs[0]!.name == nm "x" && (bs[1]!.info matches .implicit)
      : Bool))
  ++ test "collectBinders strips outParam wrappers from domains"
    ((let dom := Expr.mkApp (Expr.mkConst (nm "outParam") #[u]) prop
      let ty := Expr.mkForallE (nm "x") dom prop .default
      (collectBinders ty 1)[0]!.domain == prop : Bool))

/-- `maximize_occurrence_levels` (nested.rs:1958) + `level_max_raw`. -/
def maximizeLevelsTests : TestSeq :=
  test "levelMaxRaw: only equality/zero simplifications"
    ((levelMaxRaw u u == u && levelMaxRaw Level.mkZero u == u
      && levelMaxRaw u Level.mkZero == u
      && levelMaxRaw u v == Level.mkMax u v : Bool))
  ++ test "maximizeOccurrenceLevels merges same-name aux levels pointwise"
    ((let mk := fun (ls : Array Level) =>
        ({ name := nm "Array", specParams := #[], occurrenceLevelArgs := ls
           ownParams := 1, nIndices := 0 } : FvarFlatMember)
      let orig : FvarFlatMember :=
        { name := nm "T", specParams := #[], occurrenceLevelArgs := #[u]
          ownParams := 0, nIndices := 0 }
      let out := maximizeOccurrenceLevels #[orig, mk #[u], mk #[Level.mkMax u v]] 1
      -- level_max_raw(u, max u v) = Max(u, max u v) (raw — no subsumption);
      -- both aux entries get the merged value; the original is untouched.
      let merged := levelMaxRaw u (Level.mkMax u v)
      out[0]!.occurrenceLevelArgs == #[u]
        && out[1]!.occurrenceLevelArgs == #[merged]
        && out[2]!.occurrenceLevelArgs == #[merged] : Bool))

def mkFlatInfo (s : String) (isAux : Bool) (specParams : Array Expr)
    (ownParams : Nat) : FlatInfo :=
  { name := nm s
    ind :=
      { cnst := { name := nm s, levelParams := #[], type := prop }
        numParams := ownParams, numIndices := 0, all := #[nm s], ctors := #[]
        numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
    ctors := #[]
    allNames := #[nm s]
    isAux
    specParams
    occurrenceLevelArgs := #[]
    ownParams
    nIndices := 0 }

/-- `match_classes_against_app` (recursor.rs:2160). -/
def matchClassesTests : TestSeq :=
  test "matchClassesAgainstApp: original with matching param FVars"
    ((let pf := (freshFVar "param" 0).2
      let cls := mkFlatInfo "T" false #[] 1
      let ty := Expr.mkApp (Expr.mkConst (nm "T") #[]) pf
      matchClassesAgainstApp ty #[cls] #[pf] 1 == some 0 : Bool))
  ++ test "matchClassesAgainstApp: original with WRONG param arg misses"
    ((let pf := (freshFVar "param" 0).2
      let cls := mkFlatInfo "T" false #[] 1
      let ty := Expr.mkApp (Expr.mkConst (nm "T") #[])
        (Expr.mkConst (nm "Nat") #[])
      matchClassesAgainstApp ty #[cls] #[pf] 1 == none : Bool))
  ++ test "matchClassesAgainstApp: non-Const head misses"
    ((matchClassesAgainstApp prop #[mkFlatInfo "T" false #[] 0] #[] 0
      == none : Bool))
  ++ test "matchClassesAgainstApp: aux matches through BVar spec_params"
    -- spec_params = [BVar 0] (identity for 1 param) instantiated with the
    -- param FVar must equal the applied arg.
    ((let pf := (freshFVar "param" 0).2
      let cls := mkFlatInfo "Ext" true #[Expr.mkBVar 0] 1
      let ty := Expr.mkApp (Expr.mkConst (nm "Ext") #[]) pf
      matchClassesAgainstApp ty #[cls] #[pf] 1 == some 0 : Bool))

/-- `collect_const_refs` (recursor.rs:2694): stack order + proj names. -/
def collectConstRefsTests : TestSeq :=
  test "collectConstRefs collects app spine in stack order"
    -- stack: push f, push a; pop a first → refs in [arg, fn] order.
    ((let e := Expr.mkApp (Expr.mkConst (nm "f") #[]) (Expr.mkConst (nm "a") #[])
      (collectConstRefs e #[]).toList.map (·.pretty) == ["a", "f"] : Bool))
  ++ test "collectConstRefs includes Proj type names"
    ((let e := Expr.mkProj (nm "S") 0 (Expr.mkConst (nm "s") #[])
      (collectConstRefs e #[]).toList.map (·.pretty) == ["S", "s"] : Bool))
  ++ test "collectConstRefs appends onto the given queue"
    (((collectConstRefs (Expr.mkConst (nm "c") #[]) #[nm "pre"]).toList.map
        (·.pretty) == ["pre", "c"] : Bool))

public def suite : List TestSeq :=
  [reorderTests, reorderErrorTests, inferImplicitTests, nameAppendAfterTests,
   collectBindersTests, maximizeLevelsTests, matchClassesTests,
   collectConstRefsTests]

end Tests.AuxGen.Recursor

end
