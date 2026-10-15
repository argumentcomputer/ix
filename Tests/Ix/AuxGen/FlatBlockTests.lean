module

public import LSpec
public import Ix.AuxGen.FlatBlock

/-!
Tests of the canonical flat block and σ (`Ix.AuxGen.FlatBlock`, AuxGen M1),
on hand-built blocks (the end-to-end check, on the compiler's own canonical
blocks and through Source mode, is `Tests.Ix.AuxGen.FlatBlockSource`):

* **Alias collapse.** `A | a : B → A`, `B | b : A → B` in one class: σ sends
  both members to `A`'s fresh name and `B.b` to `A.a`'s; the flat block has
  one inductive, whose constructor type and whose recursor's type and rule
  name only fresh names.
* **Nested auxiliaries.** Canonical auxiliary recursors named by source
  index (`T.rec_2`, `T.rec_1`) become `F.rec_1`, `F.rec_2` in canonical
  order, and the flat block's `numNested` counts them.
* **The renaming** renames constants and projections' structure names, and
  returns a term σ does not touch as it is.
* **When it is needed**, and σ's `Key.map` side condition (`misfit`).
* **Refusals**: an empty class, a collapsed member with another constructor
  count, a class recursor not named `<rep>.rec`, a fresh name the
  environment declares, a conflict in σ.

Registered in `aux-gen-unit`.
-/

public section

namespace Tests.AuxGen.FlatBlock

open LSpec
open Ix.AuxGen.Flat
open Ix.Compile.ExactKey (nameEq exprEq)
open Ix (Name Level Expr ConstantVal InductiveVal ConstructorVal ConstantInfo RecursorVal
  RecursorRule)

private def nm (s : String) : Name := (s.splitOn ".").foldl Name.mkStr .mkAnon
private def type0 : Expr := Expr.mkSort (Level.mkSucc Level.mkZero)
private def cnst (s : String) : Expr := Expr.mkConst (nm s) #[]
private def arrow (a b : Expr) : Expr := Expr.mkForallE (nm "x") a b .default

/-! ## Fixtures -/

/-- An inductive `n : Type` with constructors `(c, type)`. -/
private def inductive_ (n : String) (ctors : List (String × Expr)) : List (Name × ConstantInfo) :=
  let ind : ConstantInfo := .inductInfo
    { cnst := { name := nm n, levelParams := #[], type := type0 }
      numParams := 0, numIndices := 0, all := #[nm n]
      ctors := (ctors.map fun (c, _) => nm s!"{n}.{c}").toArray
      numNested := 0, isRec := true, isUnsafe := false, isReflexive := false }
  let cs := ctors.zipIdx.map fun ((c, cty), i) =>
    (nm s!"{n}.{c}", ConstantInfo.ctorInfo
      { cnst := { name := nm s!"{n}.{c}", levelParams := #[], type := cty }
        induct := nm n, cidx := i, numParams := 0, numFields := 1, isUnsafe := false })
  (nm n, ind) :: cs

/-- `A | a : B → A` and `B | b : A → B`, α-equivalent; `C` with two
constructors; `T` with one. -/
private def consts : List (Name × ConstantInfo) :=
  inductive_ "A" [("a", arrow (cnst "B") (cnst "A"))]
    ++ inductive_ "B" [("b", arrow (cnst "A") (cnst "B"))]
    ++ inductive_ "C" [("c", arrow (cnst "A") (cnst "C")), ("d", arrow (cnst "C") (cnst "C"))]
    ++ inductive_ "T" [("mk", arrow (cnst "T") (cnst "T"))]

private def lookupIn (cs : List (Name × ConstantInfo)) (n : Name) : Option ConstantInfo :=
  (cs.find? fun (m, _) => nameEq m n).map (·.2)

private def lookup := lookupIn consts

/-- A recursor value standing for a canonical recursor: its type and rule
name the block's constants (the flat block does not read their meaning). -/
private def recVal (name : String) (type : Expr) (rules : List (String × Expr)) : RecursorVal :=
  { cnst := { name := nm name, levelParams := #[], type }
    all := #[], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1
    rules := (rules.map fun (c, rhs) => ({ ctor := nm c, nfields := 1, rhs } : RecursorRule)).toArray
    k := false, isUnsafe := false }

/-- The collapsed class's recursor: its type mentions `A`, `B` and `A.a`, a
projection of `B`, its rule `A.rec` itself. -/
private def recA : RecursorVal :=
  recVal "A.rec"
    (arrow (cnst "B") (Expr.mkApp (cnst "A.a") (Expr.mkProj (nm "B") 0 (Expr.mkBVar 0))))
    [("A.a", Expr.mkApp (cnst "A.rec") (Expr.mkBVar 0))]

private def collapsed : Except FlatError FlatBlock :=
  build lookup #[#[nm "A", nm "B"]] #[(nm "A.rec", recA)]

/-! ## Helpers -/

/-- The constants and projection structure names of a term. -/
private def names : Expr → List Name
  | .const n _ _ => [n]
  | .app f a _ => names f ++ names a
  | .lam _ t b _ _ | .forallE _ t b _ _ => names t ++ names b
  | .letE _ t v b _ _ => names t ++ names v ++ names b
  | .mdata _ b _ => names b
  | .proj n _ b _ => n :: names b
  | _ => []

private def onlyFresh (e : Expr) : Bool := (names e).all isFresh

private def same (a b : Name) : Bool := nameEq a b

/-! ## 1. Alias collapse -/

private def collapseSigma : Bool :=
  match collapsed with
  | .ok b =>
    let σ := b.sigma
    same (σ.apply (nm "A")) (fresh (nm "A")) && same (σ.apply (nm "B")) (fresh (nm "A"))
      && same (σ.apply (nm "A.a")) (fresh (nm "A.a"))
      && same (σ.apply (nm "B.b")) (fresh (nm "A.a"))
      && same (σ.apply (nm "A.rec")) (fresh (nm "A.rec"))
      -- everything else is fixed
      && same (σ.apply (nm "C")) (nm "C") && same (σ.apply (nm "B.rec")) (nm "B.rec")
      && σ.entries.size == 5
  | .error _ => false

private def collapseBlock : Bool :=
  match collapsed with
  | .ok b =>
    b.types.size == 1 && b.ctors.size == 1 && b.recs.size == 1 && b.numNested == 0
      && (b.firstName.map (same · (fresh (nm "A")))).getD false
      && b.types.all (fun v => v.all.size == 1 && v.ctors.size == 1 && v.numNested == 0)
      && b.ctors.all (·.all fun c => same c.induct (fresh (nm "A")) && onlyFresh c.cnst.type
        && exprEq c.cnst.type (arrow (Expr.mkConst (fresh (nm "A")) #[])
          (Expr.mkConst (fresh (nm "A")) #[])))
      && b.recs.all (fun r => same r.cnst.name (fresh (nm "A.rec")) && onlyFresh r.cnst.type
        && r.rules.all (fun rule => same rule.ctor (fresh (nm "A.a")) && onlyFresh rule.rhs)
        && r.all.size == 1)
      && b.consts.size == 3
  | .error _ => false

/-! ## 2. Nested auxiliaries -/

/-- One class `T` with two canonical auxiliaries, whose canonical recursors
carry source-indexed names in canonical order (`T.rec_2`, then `T.rec_1`). -/
private def nested : Except FlatError FlatBlock :=
  let ty := cnst "T"
  build lookup #[#[nm "T"]]
    #[(nm "T.rec", recVal "T.rec" ty [("T.mk", cnst "T.rec_2")]),
      (nm "T.rec_2", recVal "T.rec_2" ty [("List.cons", cnst "T.rec")]),
      (nm "T.rec_1", recVal "T.rec_1" ty [("List.nil", cnst "T.rec_1")])]

private def nestedNames : Bool :=
  match nested with
  | .ok b =>
    let F := fresh (nm "T")
    match b.recs.toList with
    | [r0, r1, r2] =>
      b.numNested == 2 && b.types.all (·.numNested == 2)
        && same (b.sigma.apply (nm "T.rec_2")) (Name.mkStr F "rec_1")
        && same (b.sigma.apply (nm "T.rec_1")) (Name.mkStr F "rec_2")
        && same r0.cnst.name (Name.mkStr F "rec")
        && same r1.cnst.name (Name.mkStr F "rec_1")
        && same r2.cnst.name (Name.mkStr F "rec_2")
        -- an auxiliary's rule names the external constructor, which σ fixes
        && r1.rules.all (fun r => same r.ctor (nm "List.cons"))
        && r1.rules.all (fun r => (names r.rhs).all (same · (fresh (nm "T.rec"))))
        && r0.rules.all (fun r => (names r.rhs).all (same · (Name.mkStr F "rec_1")))
    | _ => false
  | .error _ => false

/-! ## 3. The renaming -/

private def σAB : ClassMap :=
  match collapsed with
  | .ok b => b.sigma
  | .error _ => {}

private def renames : Bool :=
  let untouched := Expr.mkApp (cnst "C.c") (Expr.mkLam (nm "y") (cnst "C") (Expr.mkBVar 0) .default)
  let projected := Expr.mkProj (nm "B") 1 (cnst "B.b")
  let shared := Expr.mkApp (cnst "B") (cnst "B")
  -- a term σ does not touch comes back as it is
  exprEq (rename σAB untouched) untouched
    -- a projection's structure name is renamed with its argument
    && exprEq (rename σAB projected)
      (Expr.mkProj (fresh (nm "A")) 1 (Expr.mkConst (fresh (nm "A.a")) #[]))
    -- one memo across the DAG
    && exprEq (rename σAB shared)
      (Expr.mkApp (Expr.mkConst (fresh (nm "A")) #[]) (Expr.mkConst (fresh (nm "A")) #[]))

/-- A block that references a collapsed one reads it through the earlier
block's σ (`base`), and its own σ holds only its own entries. -/
private def throughBase : Bool :=
  let recC := recVal "C.rec" (arrow (cnst "A") (cnst "C")) [("C.c", cnst "C.rec"), ("C.d", cnst "B")]
  match build lookup #[#[nm "C"]] #[(nm "C.rec", recC)] σAB with
  | .ok b =>
    let fA := Expr.mkConst (fresh (nm "A")) #[]
    let fC := Expr.mkConst (fresh (nm "C")) #[]
    b.sigma.entries.size == 4 && (b.sigma.find? (nm "A")).isNone
      && b.ctors.all (fun cs => match cs.toList with
        | [c, d] => exprEq c.cnst.type (arrow fA fC) && exprEq d.cnst.type (arrow fC fC)
        | _ => false)
      && b.recs.all (fun r => exprEq r.cnst.type (arrow fA fC)
        && r.rules.all (fun rule => onlyFresh rule.rhs))
  | .error _ => false

/-! ## 4. When it is needed; σ and `Key.map` -/

private def neededCases : Bool :=
  let A := nm "A"
  let B := nm "B"
  needed #[#[A, B]] #[A, B] #[] 0
    && !needed #[#[A], #[B]] #[A, B] #[] 0
    && needed #[#[B], #[A]] #[A, B] #[] 0
    && needed #[#[A]] #[A, B] #[] 0
    && !needed #[#[A]] #[A] #[nm "A.rec_1", nm "A.rec_2"] 2
    && needed #[#[A]] #[A] #[nm "A.rec_2", nm "A.rec_1"] 2
    && needed #[#[A]] #[A] #[nm "A.rec_1"] 2

private def misfits : Bool :=
  σAB.misfit (fun _ => false) == none
    && (σAB.misfit (same · (nm "B"))).map (same · (nm "B")) == some true
    && (σAB.misfit (same · (fresh (nm "A.a")))).isSome

private def freshNames : Bool :=
  isFresh (fresh (nm "A.rec")) && !isFresh (nm "A.rec")
    && same (fresh (Name.mkStr (nm "A") "rec")) (Name.mkStr (fresh (nm "A")) "rec")
    && !same (fresh (nm "A")) (fresh (nm "B"))

/-! ## 5. Refusals -/

private def refusals : Bool :=
  let emptyClass := match build lookup #[#[]] #[] with
    | .error (.emptyClass 0) => true
    | _ => false
  let ctorCount := match build lookup #[#[nm "A", nm "C"]] #[(nm "A.rec", recA)] with
    | .error (.ctorCount m r 2 1) => same m (nm "C") && same r (nm "A")
    | _ => false
  let recName := match build lookup #[#[nm "A", nm "B"]] #[(nm "B.rec", recA)] with
    | .error (.recName e g) => same e (nm "A.rec") && same g (nm "B.rec")
    | _ => false
  let tooFew := match build lookup #[#[nm "A"], #[nm "T"]] #[(nm "A.rec", recA)] with
    | .error (.recCount 2 1) => true
    | _ => false
  let squatter : ConstantInfo := .axiomInfo
    { cnst := { name := fresh (nm "A"), levelParams := #[], type := type0 }, isUnsafe := false }
  let takenEnv := consts ++ [(fresh (nm "A"), squatter)]
  let taken := match build (lookupIn takenEnv) #[#[nm "A", nm "B"]] #[(nm "A.rec", recA)] with
    | .error (.taken f) => same f (fresh (nm "A"))
    | _ => false
  let conflict := match σAB.insert (nm "B") (fresh (nm "C")) with
    | .error (.conflict n _ _) => same n (nm "B")
    | _ => false
  let reinsert := (σAB.insert (nm "B") (fresh (nm "A"))).toOption.map (·.entries.size) == some 5
  emptyClass && ctorCount && recName && tooFew && taken && conflict && reinsert

def suite : List TestSeq := [
  test "FlatBlock: σ collapses a class onto its representative's fresh names" collapseSigma
  ++ test "FlatBlock: the collapsed block names only fresh names" collapseBlock
  ++ test "FlatBlock: nested auxiliaries renamed into canonical order" nestedNames
  ++ test "FlatBlock: σ renames constants and projections, and keeps untouched terms" renames
  ++ test "FlatBlock: a later block reads an earlier block's σ" throughBase
  ++ test "FlatBlock: needed exactly when the layout is not Lean's" neededCases
  ++ test "FlatBlock: σ's Key.map side condition" misfits
  ++ test "FlatBlock: fresh names" freshNames
  ++ test "FlatBlock: refusals" refusals
]

end Tests.AuxGen.FlatBlock
