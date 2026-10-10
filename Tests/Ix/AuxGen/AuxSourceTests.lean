module

public import LSpec
public import Ix.AuxSource
public import Ix.Compile.Pass.Opt.O2
public import Ix.Compile.Pass.Opt.O11a

/-!
Unit tests for `Ix.AuxSource` (the source side of a block's auxiliaries,
`crates/compile/src/compile/aux_source.rs` in Rust): the application
telescopes. The `computeCallSitePlans` fixtures that lived here were deleted
with the legacy call-site surgery (M6R slice 6, 2026-10-07); the split-minor
helpers are exercised end to end by O2 and O11a (`pass3`, `o11a-decline`).

Registered in `Tests/Main.lean` under `aux-gen-unit`.
-/

public section

namespace Tests.AuxGen.AuxSource

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
    (if collision then Ix.Compile.Canon.keyName decls[0]!.fvarName != Ix.Compile.Canon.keyName free
     else Ix.Compile.Canon.keyName decls[0]!.fvarName == Ix.Compile.Canon.keyName (freshFVar pfx 0).1)

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
  return Ix.Compile.Canon.keyName chosen == Ix.Compile.Canon.keyName expectedName &&
    rawSame (mkLambda (Expr.mkApp external fv) #[decl])
      (Expr.mkLam (nm "x") sort0 (Expr.mkApp external (Expr.mkBVar 0)) .default)

def suffixAndStride : Bool := Id.run do
  let preferred := (freshFVar "split_xs" 1024).1
  let s := ((FreshFVars.reserve {} preferred).reserve (Name.mkNat preferred 0)).reserve
    (Name.mkNat preferred 17)
  let ((n, _), s) := s.fresh "split_xs" (0 * 1024 + 1024)
  let ((m, _), _) := s.fresh "split_xs" (1 * 1024 + 0)
  return Ix.Compile.Canon.keyName n == Ix.Compile.Canon.keyName (Name.mkNat preferred 18) &&
    Ix.Compile.Canon.keyName m == Ix.Compile.Canon.keyName (Name.mkNat preferred 19)

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
    Ix.Compile.Canon.keyName chosen == Ix.Compile.Canon.keyName (Name.mkNat names[i]! 0)

/-- Raw helper fixture, not an accepted-source/kernel-validity claim. -/
def smallInd (name : Name) (ctors : Array Name) (np : Nat := 0) : Ix.InductiveVal :=
  { cnst := { name, levelParams := #[], type := sort0 }, numParams := np, numIndices := 0,
    all := #[nm "A", nm "B"], ctors, numNested := 0, isRec := true,
    isUnsafe := false, isReflexive := false }

def minorFixture (higher : Bool) : Environment × Ix.RecursorVal := Id.run do
  let a := nm "A"
  let b := nm "B"
  let ctor := nm "A.mk"
  let target := Expr.mkConst b #[]
  let fieldTy := if higher then Expr.mkForallE (nm "x") sort0 target .default else target
  let minorTy := Expr.mkForallE (nm "field") fieldTy
    (Expr.mkForallE (nm "ih") sort0 sort0 .default) .default
  let rv : Ix.RecursorVal := {
    cnst := { name := nm "A.rec", levelParams := #[],
      type := Expr.mkForallE (nm "minor") minorTy sort0 .default },
    all := #[a, b], numParams := 0, numIndices := 0, numMotives := 0, numMinors := 1,
    rules := #[], k := false, isUnsafe := false }
  let cv : Ix.ConstructorVal := {
    cnst := { name := ctor, levelParams := #[], type := sort0 },
    induct := a, cidx := 0, numParams := 0, numFields := 1, isUnsafe := false }
  let env : Environment := { consts := ({} : Std.HashMap Name ConstantInfo)
    |>.insert a (.inductInfo (smallInd a #[ctor]))
    |>.insert b (.inductInfo (smallInd b #[]))
    |>.insert ctor (.ctorInfo cv) }
  return (env, rv)

def actualO2Capture (higher collision : Bool) : Bool := Id.run do
  let (env, rv) := minorFixture higher
  let pfx := if higher then "split_xs" else "split_field"
  let m := Expr.mkFVar (freshFVar (if collision then pfx else "caller") 0).1
  let recur := fun (o : Ix.Compile.Pass.Opt.Occ) =>
    some (mkAppN (Expr.mkConst o.head o.us) o.args)
  let some (some actual) := Ix.Compile.Pass.Opt.adaptMinor recur env rv
    #[true, false] #[] #[] #[] #[m] 0 | return false
  let target := Expr.mkConst (nm "B") #[]
  let fieldTy := if higher then Expr.mkForallE (nm "x") sort0 target .default else target
  let call := if higher then
      Expr.mkLam (nm "x") sort0
        (mkAppN (Expr.mkConst (Name.mkStr (nm "B") "rec") #[])
          #[m, Expr.mkApp (Expr.mkBVar 1) (Expr.mkBVar 0)]) .default
    else mkAppN (Expr.mkConst (Name.mkStr (nm "B") "rec") #[]) #[m, Expr.mkBVar 0]
  let expected := Expr.mkLam (nm "field") fieldTy
    (mkAppN m #[Expr.mkBVar 0, call]) .default
  return rawSame actual expected &&
    (Ix.Compile.Pass.Opt.adaptMinor (fun _ => none) env rv
      #[true, false] #[] #[] #[] #[m] 0).isNone

def actualO11aCapture (collision : Bool) : Bool := Id.run do
  let (ienv, rv) := minorFixture false
  let env : Ix.Compile.Pass.Opt.OptEnv := { ienv, resolves := fun _ => false, blockOf := fun _ => none }
  let external := Expr.mkFVar (freshFVar (if collision then "o11a" else "caller") 0).1
  let body := Expr.mkApp external (Expr.mkBVar 1)
  let target := Expr.mkConst (nm "B") #[]
  let m := Expr.mkLam (nm "field") target
    (Expr.mkLam (nm "ih") sort0 body .default) .default
  let inst := fun (_ : Name) (_ : Array Expr) => Except.ok (nm "inst", Level.mkZero)
  let result := Ix.Compile.Pass.Opt.sizeOfMinorWith env inst rv
    #[true, false] #[] #[] #[] #[m] 0
  let .ok (some actual) := result | return false
  let expected := Expr.mkLam (nm "field") target
    (Expr.mkApp external (Expr.mkBVar 0)) .default
  -- Preserve the real failure branch too; no fabricated successful instance.
  let declined := Ix.Compile.Pass.Opt.sizeOfMinorWith env
    (fun _ _ => Except.error (some "fixture-decline")) rv
    #[true, false] #[] #[] #[] #[m] 0
  return rawSame actual expected && match declined with
    | .error (some "fixture-decline") => true
    | _ => false

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
  let env : Environment := { consts := ({} : Std.HashMap Name ConstantInfo)
    |>.insert (nm "Ext") (.inductInfo (smallInd (nm "Ext") #[] 1)) }
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
  ++ test "o11a: preserve caller FVar and dependent domain through abstraction" (capturePeel "o11a" true)
  ++ test "o11a: ordinary open-input neighbour retains preferred names" (capturePeel "o11a" false)
  ++ test "aux_sig_idx: preserve caller FVar and dependent domain through abstraction" (capturePeel "aux_sig_idx" true)
  ++ test "aux_sig_idx: ordinary open-input neighbour retains preferred names" (capturePeel "aux_sig_idx" false)
  ++ test "freshness recognizes equal spelling despite altered cached fields" (forgedFresh true)
  ++ test "freshness does not identify distinct names with colliding digests" (forgedFresh false)
  ++ test "fallback skips protected suffixes and overlapping stride bands" suffixAndStride
  ++ test "free-name collection visits all binder/let/projection/metadata children" allFreeChildren
  ++ test "peeler still declines a missing forall" ((peelBinders sort0 1 "split_field" 0).isNone)
  ++ test "O2 field capture is avoided" (actualO2Capture false true)
  ++ test "O2 field ordinary open neighbour" (actualO2Capture false false)
  ++ test "O2 higher-order recursive field preserves caller FVar" (actualO2Capture true true)
  ++ test "O2 higher-order ordinary open neighbour" (actualO2Capture true false)
  ++ test "O11a preserves caller FVar and exact instance refusal" (actualO11aCapture true)
  ++ test "O11a ordinary open neighbour and refusal" (actualO11aCapture false)
  ++ test "signature indices preserve caller FVars" (signatureCapture true)
  ++ test "signature ordinary open neighbour retains preferred name" (signatureCapture false)

def suite : List TestSeq :=
  [telescopeTests, captureTests]

end Tests.AuxGen.AuxSource
