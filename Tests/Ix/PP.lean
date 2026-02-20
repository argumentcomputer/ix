/-
  Pretty printer test suite.

  Tests Expr.pp in both .meta and .anon modes, covering:
  - Level/Sort display
  - Binder/Var/Const name formatting
  - App parenthesization
  - Pi and Lambda chain collapsing
  - Let expressions
  - Literals and projections
-/
import Ix.Kernel
import LSpec

open LSpec
open Ix.Kernel

namespace Tests.PP

/-! ## Helpers -/

private def mkName (s : String) : Ix.Name :=
  Ix.Name.mkStr Ix.Name.mkAnon s

private def mkDottedName (a b : String) : Ix.Name :=
  Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon a) b

private def testAddr : Address := Address.blake3 (ByteArray.mk #[1, 2, 3])
private def testAddr2 : Address := Address.blake3 (ByteArray.mk #[4, 5, 6])

/-- First 8 hex chars of testAddr, for anon mode assertions. -/
private def testAddrShort : String :=
  String.ofList ((toString testAddr).toList.take 8)

/-! ## Meta mode: Level / Sort display -/

def testPpSortMeta : TestSeq :=
  -- Sort display
  let prop : Expr .meta := .sort .zero
  let type : Expr .meta := .sort (.succ .zero)
  let type1 : Expr .meta := .sort (.succ (.succ .zero))
  let type2 : Expr .meta := .sort (.succ (.succ (.succ .zero)))
  -- Universe params
  let uName := mkName "u"
  let vName := mkName "v"
  let sortU : Expr .meta := .sort (.param 0 uName)
  let typeU : Expr .meta := .sort (.succ (.param 0 uName))
  let sortMax : Expr .meta := .sort (.max (.param 0 uName) (.param 1 vName))
  let sortIMax : Expr .meta := .sort (.imax (.param 0 uName) (.param 1 vName))
  -- Succ offset on param: Type (u + 1), Type (u + 2)
  let typeU1 : Expr .meta := .sort (.succ (.succ (.param 0 uName)))
  let typeU2 : Expr .meta := .sort (.succ (.succ (.succ (.param 0 uName))))
  test "sort zero → Prop" (prop.pp == "Prop") ++
  test "sort 1 → Type" (type.pp == "Type") ++
  test "sort 2 → Type 1" (type1.pp == "Type 1") ++
  test "sort 3 → Type 2" (type2.pp == "Type 2") ++
  test "sort (param u) → Sort u" (sortU.pp == "Sort u") ++
  test "sort (succ (param u)) → Type u" (typeU.pp == "Type u") ++
  test "sort (succ^2 (param u)) → Type (u + 1)" (typeU1.pp == "Type (u + 1)") ++
  test "sort (succ^3 (param u)) → Type (u + 2)" (typeU2.pp == "Type (u + 2)") ++
  test "sort (max u v) → Sort (max (u) (v))" (sortMax.pp == "Sort (max (u) (v))") ++
  test "sort (imax u v) → Sort (imax (u) (v))" (sortIMax.pp == "Sort (imax (u) (v))") ++
  .done

/-! ## Meta mode: Atoms (bvar, const, lit) -/

def testPpAtomsMeta : TestSeq :=
  let x := mkName "x"
  let natAdd := mkDottedName "Nat" "add"
  -- bvar with name
  let bv : Expr .meta := .bvar 0 x
  test "bvar with name → x" (bv.pp == "x") ++
  -- const with name
  let c : Expr .meta := .const testAddr #[] natAdd
  test "const Nat.add → Nat.add" (c.pp == "Nat.add") ++
  -- nat literal
  let n : Expr .meta := .lit (.natVal 42)
  test "natLit 42 → 42" (n.pp == "42") ++
  -- string literal
  let s : Expr .meta := .lit (.strVal "hello")
  test "strLit hello → \"hello\"" (s.pp == "\"hello\"") ++
  .done

/-! ## Meta mode: App parenthesization -/

def testPpAppMeta : TestSeq :=
  let f : Expr .meta := .const testAddr #[] (mkName "f")
  let g : Expr .meta := .const testAddr2 #[] (mkName "g")
  let a : Expr .meta := .bvar 0 (mkName "a")
  let b : Expr .meta := .bvar 1 (mkName "b")
  -- Simple application: no parens at top level
  let fa := Expr.app f a
  test "f a (no parens)" (fa.pp == "f a") ++
  -- Nested left-assoc: f a b
  let fab := Expr.app (Expr.app f a) b
  test "f a b (left-assoc, no parens)" (fab.pp == "f a b") ++
  -- Nested arg: f (g a) — arg needs parens
  let fga := Expr.app f (Expr.app g a)
  test "f (g a) (arg parens)" (fga.pp == "f (g a)") ++
  -- Atom mode: (f a)
  test "f a atom → (f a)" (Expr.pp true fa == "(f a)") ++
  -- Deep nesting: f a (g b)
  let fagb := Expr.app (Expr.app f a) (Expr.app g b)
  test "f a (g b)" (fagb.pp == "f a (g b)") ++
  .done

/-! ## Meta mode: Lambda and Pi -/

def testPpBindersMeta : TestSeq :=
  let nat : Expr .meta := .const testAddr #[] (mkName "Nat")
  let bool : Expr .meta := .const testAddr2 #[] (mkName "Bool")
  let body : Expr .meta := .bvar 0 (mkName "x")
  let body2 : Expr .meta := .bvar 1 (mkName "y")
  -- Single lambda
  let lam1 : Expr .meta := .lam nat body (mkName "x") .default
  test "λ (x : Nat) => x" (lam1.pp == "λ (x : Nat) => x") ++
  -- Single forall
  let pi1 : Expr .meta := .forallE nat body (mkName "x") .default
  test "∀ (x : Nat), x" (pi1.pp == "∀ (x : Nat), x") ++
  -- Chained lambdas
  let lam2 : Expr .meta := .lam nat (.lam bool body2 (mkName "y") .default) (mkName "x") .default
  test "λ (x : Nat) (y : Bool) => y" (lam2.pp == "λ (x : Nat) (y : Bool) => y") ++
  -- Chained foralls
  let pi2 : Expr .meta := .forallE nat (.forallE bool body2 (mkName "y") .default) (mkName "x") .default
  test "∀ (x : Nat) (y : Bool), y" (pi2.pp == "∀ (x : Nat) (y : Bool), y") ++
  -- Lambda in atom position
  test "lambda atom → (λ ...)" (Expr.pp true lam1 == "(λ (x : Nat) => x)") ++
  -- Forall in atom position
  test "forall atom → (∀ ...)" (Expr.pp true pi1 == "(∀ (x : Nat), x)") ++
  .done

/-! ## Meta mode: Let -/

def testPpLetMeta : TestSeq :=
  let nat : Expr .meta := .const testAddr #[] (mkName "Nat")
  let zero : Expr .meta := .lit (.natVal 0)
  let body : Expr .meta := .bvar 0 (mkName "x")
  let letE : Expr .meta := .letE nat zero body (mkName "x")
  test "let x : Nat := 0; x" (letE.pp == "let x : Nat := 0; x") ++
  -- Let in atom position
  test "let atom → (let ...)" (Expr.pp true letE == "(let x : Nat := 0; x)") ++
  .done

/-! ## Meta mode: Projection -/

def testPpProjMeta : TestSeq :=
  let struct : Expr .meta := .bvar 0 (mkName "s")
  let proj0 : Expr .meta := .proj testAddr 0 struct (mkName "Prod")
  test "s.0" (proj0.pp == "s.0") ++
  -- Projection of app (needs parens around struct)
  let f : Expr .meta := .const testAddr #[] (mkName "f")
  let a : Expr .meta := .bvar 0 (mkName "a")
  let projApp : Expr .meta := .proj testAddr 1 (.app f a) (mkName "Prod")
  test "(f a).1" (projApp.pp == "(f a).1") ++
  .done

/-! ## Anon mode -/

def testPpAnon : TestSeq :=
  -- bvar: ^idx
  let bv : Expr .anon := .bvar 3 ()
  test "anon bvar 3 → ^3" (bv.pp == "^3") ++
  -- const: #hash
  let c : Expr .anon := .const testAddr #[] ()
  test "anon const → #hash" (c.pp == s!"#{testAddrShort}") ++
  -- sort
  let prop : Expr .anon := .sort .zero
  test "anon sort zero → Prop" (prop.pp == "Prop") ++
  -- level param: u_idx
  let sortU : Expr .anon := .sort (.param 0 ())
  test "anon sort (param 0) → Sort u_0" (sortU.pp == "Sort u_0") ++
  -- lambda: binder name = _
  let lam : Expr .anon := .lam (.sort .zero) (.bvar 0 ()) () ()
  test "anon lam → λ (_ : ...) => ..." (lam.pp == "λ (_ : Prop) => ^0") ++
  -- forall: binder name = _
  let pi : Expr .anon := .forallE (.sort .zero) (.bvar 0 ()) () ()
  test "anon forall → ∀ (_ : ...), ..." (pi.pp == "∀ (_ : Prop), ^0") ++
  -- let: binder name = _
  let letE : Expr .anon := .letE (.sort .zero) (.lit (.natVal 0)) (.bvar 0 ()) ()
  test "anon let → let _ : ..." (letE.pp == "let _ : Prop := 0; ^0") ++
  -- chained anon lambdas
  let lam2 : Expr .anon := .lam (.sort .zero) (.lam (.sort (.succ .zero)) (.bvar 0 ()) () ()) () ()
  test "anon chained lam" (lam2.pp == "λ (_ : Prop) (_ : Type) => ^0") ++
  .done

/-! ## Meta mode: ??? detection (flags naming bugs) -/

/-- In .meta mode, default/anonymous names produce "???" in binder positions
    and full address hashes in const positions. These indicate naming info was
    never present in the source expression (e.g., anonymous Ix.Name).

    Binder names survive the eval/quote round-trip: Value.lam and Value.pi
    carry MetaField name and binder info, which quote extracts.

    Remaining const-name loss: `strLitToCtorVal`/`toCtorIfLit` create
    Neutral.const with default names for synthetic primitive constructors.
-/
def testPpMetaDefaultNames : TestSeq :=
  let anonName := Ix.Name.mkAnon
  -- bvar with anonymous name shows ???
  let bv : Expr .meta := .bvar 0 anonName
  test "meta bvar with anonymous name → ???" (bv.pp == "???") ++
  -- const with anonymous name shows full hash
  let c : Expr .meta := .const testAddr #[] anonName
  test "meta const with anonymous name → full hash" (c.pp == s!"{testAddr}") ++
  -- lambda with anonymous binder name shows ???
  let lam : Expr .meta := .lam (.sort .zero) (.bvar 0 anonName) anonName .default
  test "meta lam with anonymous binder → λ (??? : Prop) => ???" (lam.pp == "λ (??? : Prop) => ???") ++
  -- forall with anonymous binder name shows ???
  let pi : Expr .meta := .forallE (.sort .zero) (.bvar 0 anonName) anonName .default
  test "meta forall with anonymous binder → ∀ (??? : Prop), ???" (pi.pp == "∀ (??? : Prop), ???") ++
  .done

/-! ## Complex expressions -/

def testPpComplex : TestSeq :=
  let nat : Expr .meta := .const testAddr #[] (mkName "Nat")
  let bool : Expr .meta := .const testAddr2 #[] (mkName "Bool")
  -- ∀ (n : Nat), Nat → Nat  (arrow sugar approximation)
  -- This is: forallE Nat (forallE Nat Nat)
  let arrow : Expr .meta := .forallE nat (.forallE nat nat (mkName "m") .default) (mkName "n") .default
  test "∀ (n : Nat) (m : Nat), Nat" (arrow.pp == "∀ (n : Nat) (m : Nat), Nat") ++
  -- fun (f : Nat → Bool) (x : Nat) => f x
  let fType : Expr .meta := .forallE nat bool (mkName "a") .default
  let fApp : Expr .meta := .app (.bvar 1 (mkName "f")) (.bvar 0 (mkName "x"))
  let expr : Expr .meta := .lam fType (.lam nat fApp (mkName "x") .default) (mkName "f") .default
  test "λ (f : ∀ ...) (x : Nat) => f x"
    (expr.pp == "λ (f : ∀ (a : Nat), Bool) (x : Nat) => f x") ++
  -- Nested let: let x : Nat := 0; let y : Nat := x; y
  let innerLet : Expr .meta := .letE nat (.bvar 0 (mkName "x")) (.bvar 0 (mkName "y")) (mkName "y")
  let outerLet : Expr .meta := .letE nat (.lit (.natVal 0)) innerLet (mkName "x")
  test "nested let" (outerLet.pp == "let x : Nat := 0; let y : Nat := x; y") ++
  .done

/-! ## Quote round-trip: names survive eval → quote → pp -/

/-- Build a Value with named binders and verify names survive through quote → pp.
    Uses a minimal TypecheckM context. -/
def testQuoteRoundtrip : TestSeq :=
  .individualIO "quote round-trip preserves names" (do
    let xName : MetaField .meta Ix.Name := mkName "x"
    let yName : MetaField .meta Ix.Name := mkName "y"
    let nat : Expr .meta := .const testAddr #[] (mkName "Nat")
    -- Build Value.pi: ∀ (x : Nat), Nat
    let domVal : SusValue .meta := ⟨.none, Thunk.mk fun _ => Value.neu (.const testAddr #[] (mkName "Nat"))⟩
    let imgTE : TypedExpr .meta := ⟨.none, nat⟩
    let piVal : Value .meta := .pi domVal imgTE (.mk [] []) xName .default
    -- Build Value.lam: fun (y : Nat) => y
    let bodyTE : TypedExpr .meta := ⟨.none, .bvar 0 yName⟩
    let lamVal : Value .meta := .lam domVal bodyTE (.mk [] []) yName .default
    -- Quote and pp in a minimal TypecheckM context
    let ctx : TypecheckCtx .meta := {
      lvl := 0, env := .mk [] [], types := [],
      kenv := default, prims := buildPrimitives,
      safety := .safe, quotInit := true, mutTypes := default, recAddr? := none
    }
    let stt : TypecheckState .meta := { typedConsts := default }
    -- Test pi
    match TypecheckM.run ctx stt (ppValue 0 piVal) with
    | .ok s =>
      if s != "∀ (x : Nat), Nat" then
        return (false, some s!"pi round-trip: expected '∀ (x : Nat), Nat', got '{s}'")
      else pure ()
    | .error e => return (false, some s!"pi round-trip error: {e}")
    -- Test lam
    match TypecheckM.run ctx stt (ppValue 0 lamVal) with
    | .ok s =>
      if s != "λ (y : Nat) => y" then
        return (false, some s!"lam round-trip: expected 'λ (y : Nat) => y', got '{s}'")
      else pure ()
    | .error e => return (false, some s!"lam round-trip error: {e}")
    return (true, none)
  ) .done

/-! ## Literal folding: Nat/String constructor chains → literals in ppValue -/

def testFoldLiterals : TestSeq :=
  let prims := buildPrimitives
  -- Nat.zero → 0
  let natZero : Expr .meta := .const prims.natZero #[] (mkName "Nat.zero")
  let folded := foldLiterals prims natZero
  test "fold Nat.zero → 0" (folded.pp == "0") ++
  -- Nat.succ Nat.zero → 1
  let natOne : Expr .meta := .app (.const prims.natSucc #[] (mkName "Nat.succ")) natZero
  let folded := foldLiterals prims natOne
  test "fold Nat.succ Nat.zero → 1" (folded.pp == "1") ++
  -- Nat.succ (Nat.succ Nat.zero) → 2
  let natTwo : Expr .meta := .app (.const prims.natSucc #[] (mkName "Nat.succ")) natOne
  let folded := foldLiterals prims natTwo
  test "fold Nat.succ^2 Nat.zero → 2" (folded.pp == "2") ++
  -- Nats inside types get folded: ∀ (n : Nat), Eq Nat n Nat.zero
  let natType : Expr .meta := .const prims.nat #[] (mkName "Nat")
  let eqAddr := Address.blake3 (ByteArray.mk #[99])
  let eq3 : Expr .meta :=
    .app (.app (.app (.const eqAddr #[] (mkName "Eq")) natType) (.bvar 0 (mkName "n"))) natZero
  let piExpr : Expr .meta := .forallE natType eq3 (mkName "n") .default
  let folded := foldLiterals prims piExpr
  test "fold nat inside forall" (folded.pp == "∀ (n : Nat), Eq Nat n 0") ++
  -- String.mk (List.cons (Char.ofNat 104) (List.cons (Char.ofNat 105) List.nil)) → "hi"
  let charH : Expr .meta := .app (.const prims.charMk #[] (mkName "Char.ofNat")) (.lit (.natVal 104))
  let charI : Expr .meta := .app (.const prims.charMk #[] (mkName "Char.ofNat")) (.lit (.natVal 105))
  let charType : Expr .meta := .const prims.char #[] (mkName "Char")
  let nilExpr : Expr .meta := .app (.const prims.listNil #[.zero] (mkName "List.nil")) charType
  let consI : Expr .meta :=
    .app (.app (.app (.const prims.listCons #[.zero] (mkName "List.cons")) charType) charI) nilExpr
  let consH : Expr .meta :=
    .app (.app (.app (.const prims.listCons #[.zero] (mkName "List.cons")) charType) charH) consI
  let strExpr : Expr .meta := .app (.const prims.stringMk #[] (mkName "String.mk")) consH
  let folded := foldLiterals prims strExpr
  test "fold String.mk char list → \"hi\"" (folded.pp == "\"hi\"") ++
  -- Nat.succ applied to a non-literal arg stays unfolded
  let succX : Expr .meta := .app (.const prims.natSucc #[] (mkName "Nat.succ")) (.bvar 0 (mkName "x"))
  let folded := foldLiterals prims succX
  test "fold Nat.succ x → Nat.succ x (no fold)" (folded.pp == "Nat.succ x") ++
  .done

/-! ## Suites -/

def suite : List TestSeq := [
  testPpSortMeta,
  testPpAtomsMeta,
  testPpAppMeta,
  testPpBindersMeta,
  testPpLetMeta,
  testPpProjMeta,
  testPpAnon,
  testPpMetaDefaultNames,
  testPpComplex,
  testQuoteRoundtrip,
  testFoldLiterals,
]

end Tests.PP
