module

public import LSpec
public import Ix.AuxSource

/-!
Unit tests for `Ix.AuxSource` (the source side of a block's auxiliaries;
Rust `crates/compile/src/compile/aux_source.rs`): the application telescopes
and the temporary-variable supply of the split-minor helpers. O2's and
O11a's end-to-end captures join these with their passes (CQ5.1, CQ5.3).
Ported from the donor's `Tests/Ix/AuxGen/AuxSourceTests.lean`
(`jcb/ix-certify-compile` `a9cf3607`), with names compared structurally
(`Ix.AuxGen.sameStructure`).

Registered in `Tests/Main.lean` as `aux-source-unit`.
-/

public section

namespace Tests.Compile.AuxSource

open LSpec
open Ix.AuxGen
open Ix (Name Level Expr ConstantVal ConstantInfo Environment)

/-- A one-component name. -/
def nm (s : String) : Name := Name.mkStr .mkAnon s

/-! ## Telescope utilities -/

def telescopeTests : TestSeq :=
  test "collectLeanTelescope: peels a 3-arg spine in application order"
    ((let f := Expr.mkConst (nm "f") #[]
      let a1 := Expr.mkBVar 0
      let a2 := Expr.mkBVar 1
      let a3 := Expr.mkBVar 2
      let app := Expr.mkApp (Expr.mkApp (Expr.mkApp f a1) a2) a3
      let (head, args) := collectLeanTelescope app
      head == f && args == #[a1, a2, a3] : Bool))
  ++ test "collectIxonTelescope: peels a 2-arg spine in application order"
    ((let f := Ixon.Expr.ref 7 #[]
      let a1 := Ixon.Expr.var 0
      let a2 := Ixon.Expr.var 1
      let app := Ixon.Expr.app (Ixon.Expr.app f a1) a2
      let (head, args) := collectIxonTelescope app
      head == f && args == #[a1, a2] : Bool))


/-- Full raw-tree comparison, not a cached-hash assertion. -/
def rawSame (a b : Expr) : Bool := reprStr a == reprStr b

def sort0 : Expr := Expr.mkSort Level.mkZero

def capturePeel (pfx : String) (collision : Bool) : Bool := Id.run do
  let free := (freshFVar (if collision then pfx else "caller") 0).1
  let external := Expr.mkFVar free
  -- The second binder depends both on the first and on a caller FVar.
  let domain := Expr.mkApp external (Expr.mkBVar 0)
  let body := Expr.mkApp external (Expr.mkApp (Expr.mkBVar 1) (Expr.mkBVar 0))
  let source := Expr.mkForallE (nm "x") sort0
    (Expr.mkForallE (nm "y") domain body .implicit) .default
  let some (decls, fvars, opened) := peelBinders source 2 pfx 0 | return false
  let expected := Expr.mkLam (nm "x") sort0
    (Expr.mkLam (nm "y") domain body .implicit) .default
  return decls.size == 2 && fvars.size == 2 && rawSame (mkLambda opened decls) expected &&
    (if collision then !sameStructure decls[0]!.fvarName free
     else sameStructure decls[0]!.fvarName (freshFVar pfx 0).1)

/-- Distinct cached fields may neither hide equal names nor identify different names. -/
def forgedFresh (sameSpelling : Bool) : Bool := Id.run do
  let preferred := (freshFVar "split_field" 0).1
  let forged := Name.str (Name.anonymous (nm "parent-cache").getHash)
    (if sameSpelling then "_split_field_0" else "other") preferred.getHash
  let s := FreshFVars.protectExpr {} (Expr.mkFVar forged)
  let ((chosen, fv), _) := s.fresh "split_field" 0
  let expectedName := if sameSpelling then Name.mkNat preferred 0 else preferred
  let decl : LocalDecl := { fvarName := chosen, binderName := nm "x", domain := sort0, info := .default }
  let external := Expr.mkFVar forged
  return sameStructure chosen expectedName &&
    rawSame (mkLambda (Expr.mkApp external fv) #[decl])
      (Expr.mkLam (nm "x") sort0 (Expr.mkApp external (Expr.mkBVar 0)) .default)

def suffixAndStride : Bool := Id.run do
  let preferred := (freshFVar "split_xs" 1024).1
  let s := ((FreshFVars.reserve {} preferred).reserve (Name.mkNat preferred 0)).reserve
    (Name.mkNat preferred 17)
  let ((n, _), s) := s.fresh "split_xs" (0 * 1024 + 1024)
  let ((m, _), _) := s.fresh "split_xs" (1 * 1024 + 0)
  return sameStructure n (Name.mkNat preferred 18) &&
    sameStructure m (Name.mkNat preferred 19)

def allFreeChildren : Bool := Id.run do
  let names := (Array.range 5).map fun i => (freshFVar "field" i).1
  let a := Expr.mkFVar names[0]!
  let b := Expr.fvar names[1]! a.getHash
  let shared := Expr.mkApp a b
  let e := Expr.mkLetE (nm "x") shared
    (Expr.mkLam (nm "z") (Expr.mkFVar names[2]!) shared .default)
    (Expr.mkMData #[] (Expr.mkProj (nm "P") 0
      (Expr.mkApp (Expr.mkFVar names[3]!) (Expr.mkFVar names[4]!)))) false
  let s := FreshFVars.protectExpr {} e
  return (Array.range 5).all fun i =>
    let ((chosen, _), _) := s.fresh "field" i
    sameStructure chosen (Name.mkNat names[i]! 0)


def smallInd (name : Name) (ctors : Array Name) (np : Nat := 0) : Ix.InductiveVal :=
  { cnst := { name, levelParams := #[], type := sort0 }, numParams := np, numIndices := 0,
    all := #[nm "A", nm "B"], ctors, numNested := 0, isRec := true,
    isUnsafe := false, isReflexive := false }



def signatureCapture (collision : Bool) : Bool := Id.run do
  let free := Expr.mkFVar (freshFVar (if collision then "aux_sig_idx" else "caller") 0).1
  let pair := Expr.mkConst (nm "pair") #[]
  let spec := mkAppN pair #[free, Expr.mkBVar 0]
  let motiveTy := Expr.mkForallE (nm "idx") sort0
    (Expr.mkForallE (nm "major") (Expr.mkApp (Expr.mkConst (nm "Ext") #[]) spec) sort0 .default) .default
  let rv : Ix.RecursorVal := {
    cnst := { name := nm "R", levelParams := #[], type := Expr.mkForallE (nm "motive") motiveTy sort0 .default },
    all := #[], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 0,
    rules := #[], k := false, isUnsafe := false }
  let consts := ({} : Std.HashMap Name ConstantInfo).insert
    (nm "Ext") (.inductInfo (smallInd (nm "Ext") #[] 1))
  let env : Environment := { consts }
  let sigs := auxMotiveSigs rv #[] #[] #[sort0] env
  let preferred := (freshFVar "aux_sig_idx" 0).1
  let chosen := if collision then Name.mkNat preferred 0 else preferred
  return sigs.size == 1 && sigs[0]!.specs.size == 1 &&
    rawSame sigs[0]!.specs[0]! (mkAppN pair #[free, Expr.mkFVar chosen])


def captureTests : TestSeq :=
  test "split_field: preserve caller FVar and dependent domain through abstraction" (capturePeel "split_field" true)
  ++ test "split_field: ordinary open-input neighbour retains preferred names" (capturePeel "split_field" false)
  ++ test "split_ih: preserve caller FVar and dependent domain through abstraction" (capturePeel "split_ih" true)
  ++ test "split_ih: ordinary open-input neighbour retains preferred names" (capturePeel "split_ih" false)
  ++ test "split_xs: preserve caller FVar and dependent domain through abstraction" (capturePeel "split_xs" true)
  ++ test "split_xs: ordinary open-input neighbour retains preferred names" (capturePeel "split_xs" false)
  ++ test "aux_sig_idx: preserve caller FVar and dependent domain through abstraction" (capturePeel "aux_sig_idx" true)
  ++ test "aux_sig_idx: ordinary open-input neighbour retains preferred names" (capturePeel "aux_sig_idx" false)
  ++ test "freshness recognizes equal spelling despite altered cached fields" (forgedFresh true)
  ++ test "freshness does not identify distinct names with colliding digests" (forgedFresh false)
  ++ test "fallback skips protected suffixes and overlapping stride bands" suffixAndStride
  ++ test "free-name collection visits all binder/let/projection/metadata children" allFreeChildren
  ++ test "peeler still declines a missing forall" ((peelBinders sort0 1 "split_field" 0).isNone)
  ++ test "signature indices preserve caller FVars" (signatureCapture true)
  ++ test "signature ordinary open neighbour retains preferred name" (signatureCapture false)

def suite : List TestSeq :=
  [telescopeTests, captureTests]

end Tests.Compile.AuxSource
