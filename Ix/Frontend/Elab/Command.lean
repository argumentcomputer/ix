/-
  Ix.Frontend.Elab.Command: Top-Level Command & SCC Elaborator for the Ix Frontend.

  Orchestrates:
  - Optional core prelude seeding (`Bool`, `Nat`, `Unit`, `PUnit`, `Eq`, `Prod`, `Option`, `List`, `String`)
    for types not redefined in the module itself.
  - Elaboration of scheduled Strongly Connected Components (`ScheduledSCC`) in Tarjan
    topological order (callees before callers):
    1. Inductive / Structure / Class SCCs (`elabInductiveSCC`), followed immediately by
       in-elaborator constructor & block canonicalization (`Ix.Frontend.CanonBlock`) and
       surgery-free auxiliary generation (`Ix.Frontend.AuxGen`).
    2. Value declaration SCCs (`def`, `abbrev`, `theorem`, `opaque`, `axiom`, `instance`),
       with automatic structural-recursion lowering to `<Ind>.recOn` for `ι`-reducible
       definitions and post-elaboration minimal SCC splitting & canonicalization.
-/
module

public import Ix.Frontend.Elab.Term

@[expose] public section

namespace Ix.Frontend.Elab

open Ix.Frontend
open Ix.Frontend.Parser
open Ix.Frontend.Canon
open Ix.Frontend.AuxGen

/-! ## Core Prelude Seeding (for Standalone `.ix` Modules) -/

/-- Default address resolver for in-elaborator canonicalization:
    uses `importMap.lookupName?` if pinned, otherwise the constant/name's content hash. -/
def defaultAddrOf (env : IxElabEnv) (nm : Ix.Name) : Address :=
  match env.importMap.lookupName? nm with
  | some addr => addr
  | none      => Name.computeHash nm

/-- Register a minimal core prelude (`Bool`, `Nat`, `Unit`, `PUnit`, `Eq`, `Prod`, `Option`, `List`)
    for any core type not explicitly declared in `modIdx`. -/
def seedCorePreludeIfMissing (env : IxElabEnv) (modIdx : ModuleIndex) : IxElabEnv := Id.run do
  let mut env := env
  let uName := Name.simple "u"
  let vName := Name.simple "v"
  let uLvl := Level.mkParam uName
  let vLvl := Level.mkParam vName
  let type0 := Expr.mkSort (Level.mkSucc Level.mkZero)
  let typeU := Expr.mkSort (Level.mkSucc uLvl)
  let sortU := Expr.mkSort uLvl

  -- 1. `Bool : Type` (`Bool.false` cidx=0, `Bool.true` cidx=1)
  let boolName := Name.simple "Bool"
  if !env.contains boolName && !modIdx.declByName.contains boolName then
    let falseName := Name.mkStr2 "Bool" "false"
    let trueName  := Name.mkStr2 "Bool" "true"
    let boolConst := Expr.mkConst boolName #[]
    let iv : Ix.InductiveVal := {
      cnst := { name := boolName, levelParams := #[], type := type0 }
      numParams := 0, numIndices := 0, all := #[boolName]
      ctors := #[falseName, trueName], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cFalse : Ix.ConstructorVal := {
      cnst := { name := falseName, levelParams := #[], type := boolConst }
      induct := boolName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
    }
    let cTrue : Ix.ConstructorVal := {
      cnst := { name := trueName, levelParams := #[], type := boolConst }
      induct := boolName, cidx := 1, numParams := 0, numFields := 0, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cFalse, cTrue])]

  -- 2. `Nat : Type` (`Nat.zero` cidx=0, `Nat.succ` cidx=1)
  let natName := Name.simple "Nat"
  if !env.contains natName && !modIdx.declByName.contains natName then
    let zeroName := Name.mkStr2 "Nat" "zero"
    let succName := Name.mkStr2 "Nat" "succ"
    let natConst := Expr.mkConst natName #[]
    let iv : Ix.InductiveVal := {
      cnst := { name := natName, levelParams := #[], type := type0 }
      numParams := 0, numIndices := 0, all := #[natName]
      ctors := #[zeroName, succName], numNested := 0
      isRec := true, isUnsafe := false, isReflexive := false
    }
    let cZero : Ix.ConstructorVal := {
      cnst := { name := zeroName, levelParams := #[], type := natConst }
      induct := natName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
    }
    let cSucc : Ix.ConstructorVal := {
      cnst := { name := succName, levelParams := #[], type := Expr.mkForallE (Name.simple "n") natConst natConst .default }
      induct := natName, cidx := 1, numParams := 0, numFields := 1, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cZero, cSucc])]

  -- 3. `PUnit.{u} : Sort u` (`PUnit.unit`)
  let punitName := Name.simple "PUnit"
  if !env.contains punitName && !modIdx.declByName.contains punitName then
    let unitCtorName := Name.mkStr2 "PUnit" "unit"
    let punitConst := Expr.mkConst punitName #[uLvl]
    let iv : Ix.InductiveVal := {
      cnst := { name := punitName, levelParams := #[uName], type := sortU }
      numParams := 0, numIndices := 0, all := #[punitName]
      ctors := #[unitCtorName], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cUnit : Ix.ConstructorVal := {
      cnst := { name := unitCtorName, levelParams := #[uName], type := punitConst }
      induct := punitName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cUnit])]

  -- 4. `Unit : Type` (`Unit.unit`)
  let unitName := Name.simple "Unit"
  if !env.contains unitName && !modIdx.declByName.contains unitName then
    let uCtor := Name.mkStr2 "Unit" "unit"
    let unitConst := Expr.mkConst unitName #[]
    let iv : Ix.InductiveVal := {
      cnst := { name := unitName, levelParams := #[], type := type0 }
      numParams := 0, numIndices := 0, all := #[unitName]
      ctors := #[uCtor], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cU : Ix.ConstructorVal := {
      cnst := { name := uCtor, levelParams := #[], type := unitConst }
      induct := unitName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cU])]

  -- 5. `Eq.{u} : {α : Sort u} → α → α → Prop` (`Eq.refl : {α : Sort u} → (a : α) → Eq a a`)
  let eqName := Name.simple "Eq"
  if !env.contains eqName && !modIdx.declByName.contains eqName then
    let reflName := Name.mkStr2 "Eq" "refl"
    let eqType :=
      Expr.mkForallE (Name.simple "α") sortU
        (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 0)
          (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 1) Expr.mkProp .default) .default)
        .implicit
    let reflRet :=
      Expr.mkAppN (Expr.mkConst eqName #[uLvl]) #[Expr.mkBVar 1, Expr.mkBVar 0, Expr.mkBVar 0]
    let reflType :=
      Expr.mkForallE (Name.simple "α") sortU
        (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 0) reflRet .default)
        .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := eqName, levelParams := #[uName], type := eqType }
      numParams := 2, numIndices := 1, all := #[eqName]
      ctors := #[reflName], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cRefl : Ix.ConstructorVal := {
      cnst := { name := reflName, levelParams := #[uName], type := reflType }
      induct := eqName, cidx := 0, numParams := 2, numFields := 0, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cRefl])]

  -- 5b. Core Logical Connectives (`True`, `False`, `Not`, `Ne`, `And`, `Or`, `Iff`, `Exists`)
  let prop := Expr.mkProp
  let truePropName := Name.simple "True"
  if !env.contains truePropName && !modIdx.declByName.contains truePropName then
    let introName := Name.mkStr2 "True" "intro"
    let iv : Ix.InductiveVal := {
      cnst := { name := truePropName, levelParams := #[], type := prop }
      numParams := 0, numIndices := 0, all := #[truePropName]
      ctors := #[introName], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cIntro : Ix.ConstructorVal := {
      cnst := { name := introName, levelParams := #[], type := Expr.mkConst truePropName #[] }
      induct := truePropName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cIntro])]

  let falsePropName := Name.simple "False"
  if !env.contains falsePropName && !modIdx.declByName.contains falsePropName then
    let iv : Ix.InductiveVal := {
      cnst := { name := falsePropName, levelParams := #[], type := prop }
      numParams := 0, numIndices := 0, all := #[falsePropName]
      ctors := #[], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[])]

  let notName := Name.simple "Not"
  if !env.contains notName && !modIdx.declByName.contains notName then
    env := env.addConst (.defnInfo {
      cnst := {
        name := notName, levelParams := #[]
        type := Expr.mkForallE (Name.simple "a") prop prop .default
      }
      value := Expr.mkLam (Name.simple "a") prop
        (Expr.mkForallE Name.mkAnon (Expr.mkBVar 0) (Expr.mkConst falsePropName #[]) .default) .default
      hints := .abbrev, safety := .safe, all := #[notName]
    })

  let neName := Name.simple "Ne"
  if !env.contains neName && !modIdx.declByName.contains neName then
    let neType :=
      Expr.mkForallE (Name.simple "α") sortU
        (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 0)
          (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 1) prop .default) .default)
        .implicit
    let neVal :=
      Expr.mkLam (Name.simple "α") sortU
        (Expr.mkLam (Name.simple "a") (Expr.mkBVar 0)
          (Expr.mkLam (Name.simple "b") (Expr.mkBVar 1)
            (Expr.mkApp (Expr.mkConst notName #[])
              (Expr.mkAppN (Expr.mkConst eqName #[uLvl]) #[Expr.mkBVar 2, Expr.mkBVar 1, Expr.mkBVar 0]))
            .default) .default) .implicit
    env := env.addConst (.defnInfo {
      cnst := { name := neName, levelParams := #[uName], type := neType }
      value := neVal, hints := .abbrev, safety := .safe, all := #[neName]
    })

  let andName := Name.simple "And"
  if !env.contains andName && !modIdx.declByName.contains andName then
    let andIntro := Name.mkStr2 "And" "intro"
    let andLeft  := Name.mkStr2 "And" "left"
    let andRight := Name.mkStr2 "And" "right"
    let andType  := Expr.mkForallE (Name.simple "a") prop (Expr.mkForallE (Name.simple "b") prop prop .default) .default
    let andApp   := Expr.mkAppN (Expr.mkConst andName #[]) #[Expr.mkBVar 3, Expr.mkBVar 2]
    let andIntroTy :=
      Expr.mkForallE (Name.simple "a") prop
        (Expr.mkForallE (Name.simple "b") prop
          (Expr.mkForallE (Name.simple "left") (Expr.mkBVar 1)
            (Expr.mkForallE (Name.simple "right") (Expr.mkBVar 1) andApp .default) .default)
          .implicit) .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := andName, levelParams := #[], type := andType }
      numParams := 2, numIndices := 0, all := #[andName]
      ctors := #[andIntro], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cIntro : Ix.ConstructorVal := {
      cnst := { name := andIntro, levelParams := #[], type := andIntroTy }
      induct := andName, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cIntro])]
    for p in generateStructProjections iv cIntro #[andLeft, andRight] true do
      env := env.addConst (.defnInfo p)
    env := env.addStructInfo {
      structName := andName, ctorName := andIntro, numParams := 2
      fields := #[
        { fieldName := Name.simple "left",  projFnName := andLeft,  fieldIdx := 0 },
        { fieldName := Name.simple "right", projFnName := andRight, fieldIdx := 1 }
      ]
    }

  let orName := Name.simple "Or"
  if !env.contains orName && !modIdx.declByName.contains orName then
    let orInl := Name.mkStr2 "Or" "inl"
    let orInr := Name.mkStr2 "Or" "inr"
    let orType := Expr.mkForallE (Name.simple "a") prop (Expr.mkForallE (Name.simple "b") prop prop .default) .default
    let orApp  := Expr.mkAppN (Expr.mkConst orName #[]) #[Expr.mkBVar 2, Expr.mkBVar 1]
    let inlTy :=
      Expr.mkForallE (Name.simple "a") prop
        (Expr.mkForallE (Name.simple "b") prop
          (Expr.mkForallE (Name.simple "h") (Expr.mkBVar 1) orApp .default) .implicit) .implicit
    let inrTy :=
      Expr.mkForallE (Name.simple "a") prop
        (Expr.mkForallE (Name.simple "b") prop
          (Expr.mkForallE (Name.simple "h") (Expr.mkBVar 0) orApp .default) .implicit) .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := orName, levelParams := #[], type := orType }
      numParams := 2, numIndices := 0, all := #[orName]
      ctors := #[orInl, orInr], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cInl : Ix.ConstructorVal := {
      cnst := { name := orInl, levelParams := #[], type := inlTy }
      induct := orName, cidx := 0, numParams := 2, numFields := 1, isUnsafe := false
    }
    let cInr : Ix.ConstructorVal := {
      cnst := { name := orInr, levelParams := #[], type := inrTy }
      induct := orName, cidx := 1, numParams := 2, numFields := 1, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cInl, cInr])]

  let iffName := Name.simple "Iff"
  if !env.contains iffName && !modIdx.declByName.contains iffName then
    let iffIntro := Name.mkStr2 "Iff" "intro"
    let iffMp    := Name.mkStr2 "Iff" "mp"
    let iffMpr   := Name.mkStr2 "Iff" "mpr"
    let iffType  := Expr.mkForallE (Name.simple "a") prop (Expr.mkForallE (Name.simple "b") prop prop .default) .default
    let iffApp   := Expr.mkAppN (Expr.mkConst iffName #[]) #[Expr.mkBVar 3, Expr.mkBVar 2]
    let mpDom    := Expr.mkForallE Name.mkAnon (Expr.mkBVar 1) (Expr.mkBVar 1) .default
    let mprDom   := Expr.mkForallE Name.mkAnon (Expr.mkBVar 1) (Expr.mkBVar 3) .default
    let iffIntroTy :=
      Expr.mkForallE (Name.simple "a") prop
        (Expr.mkForallE (Name.simple "b") prop
          (Expr.mkForallE (Name.simple "mp") mpDom
            (Expr.mkForallE (Name.simple "mpr") mprDom iffApp .default) .default)
          .implicit) .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := iffName, levelParams := #[], type := iffType }
      numParams := 2, numIndices := 0, all := #[iffName]
      ctors := #[iffIntro], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cIntro : Ix.ConstructorVal := {
      cnst := { name := iffIntro, levelParams := #[], type := iffIntroTy }
      induct := iffName, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cIntro])]
    for p in generateStructProjections iv cIntro #[iffMp, iffMpr] true do
      env := env.addConst (.defnInfo p)
    env := env.addStructInfo {
      structName := iffName, ctorName := iffIntro, numParams := 2
      fields := #[
        { fieldName := Name.simple "mp",  projFnName := iffMp,  fieldIdx := 0 },
        { fieldName := Name.simple "mpr", projFnName := iffMpr, fieldIdx := 1 }
      ]
    }

  let existsName := Name.simple "Exists"
  if !env.contains existsName && !modIdx.declByName.contains existsName then
    let exIntro := Name.mkStr2 "Exists" "intro"
    let predDom := Expr.mkForallE Name.mkAnon (Expr.mkBVar 0) prop .default
    let exType  :=
      Expr.mkForallE (Name.simple "α") sortU
        (Expr.mkForallE (Name.simple "p") predDom prop .default) .implicit
    let exApp := Expr.mkAppN (Expr.mkConst existsName #[uLvl]) #[Expr.mkBVar 3, Expr.mkBVar 2]
    let exIntroTy :=
      Expr.mkForallE (Name.simple "α") sortU
        (Expr.mkForallE (Name.simple "p") predDom
          (Expr.mkForallE (Name.simple "w") (Expr.mkBVar 1)
            (Expr.mkForallE (Name.simple "h") (Expr.mkApp (Expr.mkBVar 1) (Expr.mkBVar 0)) exApp .default) .default)
          .implicit) .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := existsName, levelParams := #[uName], type := exType }
      numParams := 2, numIndices := 0, all := #[existsName]
      ctors := #[exIntro], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cIntro : Ix.ConstructorVal := {
      cnst := { name := exIntro, levelParams := #[uName], type := exIntroTy }
      induct := existsName, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cIntro])]

  -- 6. `Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)` (`Prod.mk`, `Prod.fst`, `Prod.snd`)
  let prodName := Name.simple "Prod"
  if !env.contains prodName && !modIdx.declByName.contains prodName then
    let mkName := Name.mkStr2 "Prod" "mk"
    let fstName := Name.mkStr2 "Prod" "fst"
    let sndName := Name.mkStr2 "Prod" "snd"
    let typeV := Expr.mkSort (Level.mkSucc vLvl)
    let typeMaxUV := Expr.mkSort (Level.mkSucc (Level.mkMax uLvl vLvl))
    let prodType :=
      Expr.mkForallE (Name.simple "α") typeU
        (Expr.mkForallE (Name.simple "β") typeV typeMaxUV .default) .default
    let prodApp := Expr.mkAppN (Expr.mkConst prodName #[uLvl, vLvl]) #[Expr.mkBVar 3, Expr.mkBVar 2]
    let mkType :=
      Expr.mkForallE (Name.simple "α") typeU
        (Expr.mkForallE (Name.simple "β") typeV
          (Expr.mkForallE (Name.simple "fst") (Expr.mkBVar 1)
            (Expr.mkForallE (Name.simple "snd") (Expr.mkBVar 1) prodApp .default) .default)
          .implicit) .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := prodName, levelParams := #[uName, vName], type := prodType }
      numParams := 2, numIndices := 0, all := #[prodName]
      ctors := #[mkName], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cMk : Ix.ConstructorVal := {
      cnst := { name := mkName, levelParams := #[uName, vName], type := mkType }
      induct := prodName, cidx := 0, numParams := 2, numFields := 2, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cMk])]
    let projs := generateStructProjections iv cMk #[fstName, sndName] false
    for p in projs do
      env := env.addConst (.defnInfo p)
    env := env.addStructInfo {
      structName := prodName
      ctorName   := mkName
      numParams  := 2
      fields     := #[
        { fieldName := Name.simple "fst", projFnName := fstName, fieldIdx := 0 },
        { fieldName := Name.simple "snd", projFnName := sndName, fieldIdx := 1 }
      ]
    }

  -- 7. `List.{u} (α : Type u) : Type u` (`List.nil` cidx=0, `List.cons` cidx=1)
  let listName := Name.simple "List"
  if !env.contains listName && !modIdx.declByName.contains listName then
    let nilName  := Name.mkStr2 "List" "nil"
    let consName := Name.mkStr2 "List" "cons"
    let listType := Expr.mkForallE (Name.simple "α") typeU typeU .default
    let listApp0 := Expr.mkApp (Expr.mkConst listName #[uLvl]) (Expr.mkBVar 0)
    let listApp1 := Expr.mkApp (Expr.mkConst listName #[uLvl]) (Expr.mkBVar 1)
    let listApp2 := Expr.mkApp (Expr.mkConst listName #[uLvl]) (Expr.mkBVar 2)
    let nilType  := Expr.mkForallE (Name.simple "α") typeU listApp0 .implicit
    let consType :=
      Expr.mkForallE (Name.simple "α") typeU
        (Expr.mkForallE (Name.simple "head") (Expr.mkBVar 0)
          (Expr.mkForallE (Name.simple "tail") listApp1 listApp2 .default) .default)
        .implicit
    let iv : Ix.InductiveVal := {
      cnst := { name := listName, levelParams := #[uName], type := listType }
      numParams := 1, numIndices := 0, all := #[listName]
      ctors := #[nilName, consName], numNested := 0
      isRec := true, isUnsafe := false, isReflexive := false
    }
    let cNil : Ix.ConstructorVal := {
      cnst := { name := nilName, levelParams := #[uName], type := nilType }
      induct := listName, cidx := 0, numParams := 1, numFields := 0, isUnsafe := false
    }
    let cCons : Ix.ConstructorVal := {
      cnst := { name := consName, levelParams := #[uName], type := consType }
      induct := listName, cidx := 1, numParams := 1, numFields := 2, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cNil, cCons])]

  -- 8. `String : Type` (for string literals `"..."`)
  let stringName := Name.simple "String"
  if !env.contains stringName && !modIdx.declByName.contains stringName then
    let strMkName := Name.mkStr2 "String" "mk"
    let charName := Name.simple "Char"
    if !env.contains charName && !modIdx.declByName.contains charName then
      env := env.addConst (.axiomInfo {
        cnst := { name := charName, levelParams := #[], type := type0 }
        isUnsafe := false
      })
    let listChar := Expr.mkApp (Expr.mkConst listName #[Level.mkZero]) (Expr.mkConst charName #[])
    let strConst := Expr.mkConst stringName #[]
    let iv : Ix.InductiveVal := {
      cnst := { name := stringName, levelParams := #[], type := type0 }
      numParams := 0, numIndices := 0, all := #[stringName]
      ctors := #[strMkName], numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    let cMk : Ix.ConstructorVal := {
      cnst := {
        name := strMkName, levelParams := #[]
        type := Expr.mkForallE (Name.simple "data") listChar strConst .default
      }
      induct := stringName, cidx := 0, numParams := 0, numFields := 1, isUnsafe := false
    }
    env := registerCanonicalInductiveBlock env #[(iv, #[cMk])]
    let strProjs := generateStructProjections iv cMk #[Name.mkStr2 "String" "toList"] false
    for p in strProjs do
      env := env.addConst (.defnInfo p)
    let strOfListName := Name.mkStr2 "String" "ofList"
    if !env.contains strOfListName && !modIdx.declByName.contains strOfListName then
      env := env.addConst (.defnInfo {
        cnst := {
          name := strOfListName, levelParams := #[]
          type := Expr.mkForallE (Name.simple "data") listChar strConst .default
        }
        value := Expr.mkLam (Name.simple "data") listChar
          (Expr.mkApp (Expr.mkConst strMkName #[]) (Expr.mkBVar 0)) .default
        hints := .abbrev
        safety := .safe
        all := #[strOfListName]
      })

  -- 9. Core `Nat`, `Char`, and `String` operations (if not declared in the module)
  let natConst  := Expr.mkConst natName #[]
  let boolConst := Expr.mkConst boolName #[]
  let charConst := Expr.mkConst (Name.simple "Char") #[]
  let strConst  := Expr.mkConst stringName #[]
  let natToNat  := Expr.mkForallE (Name.simple "x") natConst natConst .default
  let natBinTy  := Expr.mkForallE (Name.simple "x") natConst (Expr.mkForallE (Name.simple "y") natConst natConst .default) .default
  let natCmpTy  := Expr.mkForallE (Name.simple "x") natConst (Expr.mkForallE (Name.simple "y") natConst boolConst .default) .default
  let charToNat := Expr.mkForallE (Name.simple "c") charConst natConst .default
  let natToChar := Expr.mkForallE (Name.simple "n") natConst charConst .default
  let strToNat  := Expr.mkForallE (Name.simple "s") strConst natConst .default
  let strToBool := Expr.mkForallE (Name.simple "s") strConst boolConst .default
  let strToChar := Expr.mkForallE (Name.simple "s") strConst charConst .default
  let charToStr := Expr.mkForallE (Name.simple "c") charConst strConst .default
  let strBinTy  := Expr.mkForallE (Name.simple "s1") strConst (Expr.mkForallE (Name.simple "s2") strConst strConst .default) .default
  let strPushTy := Expr.mkForallE (Name.simple "s") strConst (Expr.mkForallE (Name.simple "c") charConst strConst .default) .default

  let primAxioms : Array (Ix.Name × Ix.Expr) := #[
    (Name.mkStr2 "Nat" "add", natBinTy),
    (Name.mkStr2 "Nat" "sub", natBinTy),
    (Name.mkStr2 "Nat" "mul", natBinTy),
    (Name.mkStr2 "Nat" "div", natBinTy),
    (Name.mkStr2 "Nat" "mod", natBinTy),
    (Name.mkStr2 "Nat" "pow", natBinTy),
    (Name.mkStr2 "Nat" "pred", natToNat),
    (Name.mkStr2 "Nat" "beq", natCmpTy),
    (Name.mkStr2 "Nat" "ble", natCmpTy),
    (Name.mkStr2 "Char" "ofNat", natToChar),
    (Name.mkStr2 "Char" "toNat", charToNat),
    (Name.mkStr2 "Char" "utf8Size", charToNat),
    (Name.mkStr2 "String" "length", strToNat),
    (Name.mkStr2 "String" "utf8ByteSize", strToNat),
    (Name.mkStr2 "String" "isEmpty", strToBool),
    (Name.mkStr2 "String" "append", strBinTy),
    (Name.mkStr2 "String" "push", strPushTy),
    (Name.mkStr2 "String" "singleton", charToStr),
    (Name.mkStr2 "String" "back", strToChar)
  ]
  for (pName, pType) in primAxioms do
    if !env.contains pName && !modIdx.declByName.contains pName then
      env := env.addConst (.axiomInfo {
        cnst := { name := pName, levelParams := #[], type := pType }
        isUnsafe := false
      })

  -- 10. On-demand seeding of `Inhabited`, `BEq`, and `Coe` when referenced or derived in `modIdx`
  let rec stxHasRefOrOp : Nat → Ix.Syntax → Bool
    | 0, _ => false
    | _ + 1, .ident _ _ id _ =>
      let c := (Name.components id).headD ""
      c == "Inhabited" || c == "default" || c == "BEq" || c == "DecidableEq" || c == "Coe"
    | _, .atom _ v => v == "==" || v == "!=" || v == "&&"
    | f + 1, .node _ _ as => as.any (stxHasRefOrOp f)
    | _, _ => false
  let needsCoreClasses := modIdx.decls.any fun d => stxHasRefOrOp 64 d.stx
  if needsCoreClasses then
    -- 10a. `Inhabited.{u} (α : Type u) : Type u`, `Inhabited.mk`, `Inhabited.default`, `default`, `instInhabitedNat`, `instInhabitedBool`
    let inhName := Name.simple "Inhabited"
    if !env.contains inhName && !modIdx.declByName.contains inhName then
      let inhMk := Name.mkStr2 "Inhabited" "mk"
      let inhDef := Name.mkStr2 "Inhabited" "default"
      let inhTy := Expr.mkForallE (Name.simple "α") typeU typeU .default
      let inhApp0 := Expr.mkApp (Expr.mkConst inhName #[uLvl]) (Expr.mkBVar 0)
      let inhApp1 := Expr.mkApp (Expr.mkConst inhName #[uLvl]) (Expr.mkBVar 1)
      let inhMkTy :=
        Expr.mkForallE (Name.simple "α") typeU
          (Expr.mkForallE (Name.simple "default") (Expr.mkBVar 0) inhApp1 .default) .implicit
      let iv : Ix.InductiveVal := {
        cnst := { name := inhName, levelParams := #[uName], type := inhTy }
        numParams := 1, numIndices := 0, all := #[inhName]
        ctors := #[inhMk], numNested := 0
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let cMk : Ix.ConstructorVal := {
        cnst := { name := inhMk, levelParams := #[uName], type := inhMkTy }
        induct := inhName, cidx := 0, numParams := 1, numFields := 1, isUnsafe := false
      }
      env := registerCanonicalInductiveBlock env #[(iv, #[cMk])]
      for p in generateStructProjections iv cMk #[inhDef] true do
        env := env.addConst (.defnInfo p)
      env := env.addStructInfo {
        structName := inhName, ctorName := inhMk, numParams := 1, isClass := true
        fields := #[{ fieldName := Name.simple "default", projFnName := inhDef, fieldIdx := 0 }]
      }
      let topDefName := Name.simple "default"
      if !env.contains topDefName && !modIdx.declByName.contains topDefName then
        let topDefTy :=
          Expr.mkForallE (Name.simple "α") typeU
            (Expr.mkForallE (Name.simple "self") inhApp0 (Expr.mkBVar 1) .instImplicit) .implicit
        let topDefVal :=
          Expr.mkLam (Name.simple "α") typeU
            (Expr.mkLam (Name.simple "self") inhApp0
              (Expr.mkProj inhName 0 (Expr.mkBVar 0)) .instImplicit) .implicit
        env := env.addConst (.defnInfo {
          cnst := { name := topDefName, levelParams := #[uName], type := topDefTy }
          value := topDefVal, hints := .abbrev, safety := .safe, all := #[topDefName]
        })
      let instInhNat := Name.simple "instInhabitedNat"
      if !env.contains instInhNat && !modIdx.declByName.contains instInhNat then
        env := env.addConst (.defnInfo {
          cnst := { name := instInhNat, levelParams := #[], type := Expr.mkApp (Expr.mkConst inhName #[Level.mkZero]) natConst }
          value := Expr.mkAppN (Expr.mkConst inhMk #[Level.mkZero]) #[natConst, Expr.mkConst (Name.mkStr2 "Nat" "zero") #[]]
          hints := .abbrev, safety := .safe, all := #[instInhNat]
        })
        env := env.addInstance { instName := instInhNat, className := inhName }
      let instInhBool := Name.simple "instInhabitedBool"
      if !env.contains instInhBool && !modIdx.declByName.contains instInhBool then
        env := env.addConst (.defnInfo {
          cnst := { name := instInhBool, levelParams := #[], type := Expr.mkApp (Expr.mkConst inhName #[Level.mkZero]) boolConst }
          value := Expr.mkAppN (Expr.mkConst inhMk #[Level.mkZero]) #[boolConst, Expr.mkConst (Name.mkStr2 "Bool" "false") #[]]
          hints := .abbrev, safety := .safe, all := #[instInhBool]
        })
        env := env.addInstance { instName := instInhBool, className := inhName }

    -- 10b. `BEq.{u} (α : Type u) : Type u`, `BEq.mk`, `BEq.beq`, `and`, `instBEqNat`, `instBEqBool`
    let andBoolName := Name.simple "and"
    if !env.contains andBoolName && !modIdx.declByName.contains andBoolName then
      let andVal :=
        Expr.mkLam (Name.simple "x") boolConst
          (Expr.mkLam (Name.simple "y") boolConst
            (Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Bool" "casesOn") #[Level.mkSucc Level.mkZero])
              #[Expr.mkLam (Name.simple "_") boolConst boolConst .default,
                Expr.mkBVar 1,
                Expr.mkConst (Name.mkStr2 "Bool" "false") #[],
                Expr.mkBVar 0]) .default) .default
      let boolBinTy := Expr.mkForallE (Name.simple "x") boolConst (Expr.mkForallE (Name.simple "y") boolConst boolConst .default) .default
      env := env.addConst (.defnInfo {
        cnst := { name := andBoolName, levelParams := #[], type := boolBinTy }
        value := andVal, hints := .abbrev, safety := .safe, all := #[andBoolName]
      })
    let beqClsName := Name.simple "BEq"
    if !env.contains beqClsName && !modIdx.declByName.contains beqClsName then
      let beqMk := Name.mkStr2 "BEq" "mk"
      let beqFn := Name.mkStr2 "BEq" "beq"
      let beqClsTy := Expr.mkForallE (Name.simple "α") typeU typeU .default
      let beqFnDom :=
        Expr.mkForallE Name.mkAnon (Expr.mkBVar 0)
          (Expr.mkForallE Name.mkAnon (Expr.mkBVar 1) boolConst .default) .default
      let beqApp1 := Expr.mkApp (Expr.mkConst beqClsName #[uLvl]) (Expr.mkBVar 1)
      let beqMkTy :=
        Expr.mkForallE (Name.simple "α") typeU
          (Expr.mkForallE (Name.simple "beq") beqFnDom beqApp1 .default) .implicit
      let iv : Ix.InductiveVal := {
        cnst := { name := beqClsName, levelParams := #[uName], type := beqClsTy }
        numParams := 1, numIndices := 0, all := #[beqClsName]
        ctors := #[beqMk], numNested := 0
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let cMk : Ix.ConstructorVal := {
        cnst := { name := beqMk, levelParams := #[uName], type := beqMkTy }
        induct := beqClsName, cidx := 0, numParams := 1, numFields := 1, isUnsafe := false
      }
      env := registerCanonicalInductiveBlock env #[(iv, #[cMk])]
      for p in generateStructProjections iv cMk #[beqFn] true do
        env := env.addConst (.defnInfo p)
      env := env.addStructInfo {
        structName := beqClsName, ctorName := beqMk, numParams := 1, isClass := true
        fields := #[{ fieldName := Name.simple "beq", projFnName := beqFn, fieldIdx := 0 }]
      }
      let instBEqNat := Name.simple "instBEqNat"
      if !env.contains instBEqNat && !modIdx.declByName.contains instBEqNat then
        env := env.addConst (.defnInfo {
          cnst := { name := instBEqNat, levelParams := #[], type := Expr.mkApp (Expr.mkConst beqClsName #[Level.mkZero]) natConst }
          value := Expr.mkAppN (Expr.mkConst beqMk #[Level.mkZero]) #[natConst, Expr.mkConst (Name.mkStr2 "Nat" "beq") #[]]
          hints := .abbrev, safety := .safe, all := #[instBEqNat]
        })
        env := env.addInstance { instName := instBEqNat, className := beqClsName }
      let instBEqBool := Name.simple "instBEqBool"
      if !env.contains instBEqBool && !modIdx.declByName.contains instBEqBool then
        let boolBeqVal :=
          Expr.mkLam (Name.simple "a") boolConst
            (Expr.mkLam (Name.simple "b") boolConst
              (Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Bool" "casesOn") #[Level.mkSucc Level.mkZero])
                #[Expr.mkLam (Name.simple "_") boolConst boolConst .default,
                  Expr.mkBVar 1,
                  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Bool" "casesOn") #[Level.mkSucc Level.mkZero])
                    #[Expr.mkLam (Name.simple "_") boolConst boolConst .default,
                      Expr.mkBVar 0,
                      Expr.mkConst (Name.mkStr2 "Bool" "true") #[],
                      Expr.mkConst (Name.mkStr2 "Bool" "false") #[]],
                  Expr.mkBVar 0]) .default) .default
        env := env.addConst (.defnInfo {
          cnst := { name := instBEqBool, levelParams := #[], type := Expr.mkApp (Expr.mkConst beqClsName #[Level.mkZero]) boolConst }
          value := Expr.mkAppN (Expr.mkConst beqMk #[Level.mkZero]) #[boolConst, boolBeqVal]
          hints := .abbrev, safety := .safe, all := #[instBEqBool]
        })
        env := env.addInstance { instName := instBEqBool, className := beqClsName }

    -- 10c. `Coe.{u, v} (α : Type u) (β : Type v) : Type (max u v)`, `Coe.mk`, `Coe.coe`
    let coeClsName := Name.simple "Coe"
    if !env.contains coeClsName && !modIdx.declByName.contains coeClsName then
      let coeMk := Name.mkStr2 "Coe" "mk"
      let coeFn := Name.mkStr2 "Coe" "coe"
      let typeV := Expr.mkSort (Level.mkSucc vLvl)
      let typeMaxUV := Expr.mkSort (Level.mkSucc (Level.mkMax uLvl vLvl))
      let coeClsTy :=
        Expr.mkForallE (Name.simple "α") typeU
          (Expr.mkForallE (Name.simple "β") typeV typeMaxUV .default) .default
      let coeFnDom := Expr.mkForallE Name.mkAnon (Expr.mkBVar 1) (Expr.mkBVar 1) .default
      let coeApp := Expr.mkAppN (Expr.mkConst coeClsName #[uLvl, vLvl]) #[Expr.mkBVar 2, Expr.mkBVar 1]
      let coeMkTy :=
        Expr.mkForallE (Name.simple "α") typeU
          (Expr.mkForallE (Name.simple "β") typeV
            (Expr.mkForallE (Name.simple "coe") coeFnDom coeApp .default)
            .implicit) .implicit
      let iv : Ix.InductiveVal := {
        cnst := { name := coeClsName, levelParams := #[uName, vName], type := coeClsTy }
        numParams := 2, numIndices := 0, all := #[coeClsName]
        ctors := #[coeMk], numNested := 0
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let cMk : Ix.ConstructorVal := {
        cnst := { name := coeMk, levelParams := #[uName, vName], type := coeMkTy }
        induct := coeClsName, cidx := 0, numParams := 2, numFields := 1, isUnsafe := false
      }
      env := registerCanonicalInductiveBlock env #[(iv, #[cMk])]
      for p in generateStructProjections iv cMk #[coeFn] true do
        env := env.addConst (.defnInfo p)
      env := env.addStructInfo {
        structName := coeClsName, ctorName := coeMk, numParams := 2, isClass := true
        fields := #[{ fieldName := Name.simple "coe", projFnName := coeFn, fieldIdx := 0 }]
      }

  return env

/-- Register the core Lean 4 `Init` arithmetic/order typeclass instance entries in `env.instances`. -/
def registerLeanInitArithInstances (env : IxElabEnv) : IxElabEnv := Id.run do
  let mut env := env
  let entries : Array (Ix.Name × Ix.Name) := #[
    (Name.simple "OfNat",  Name.simple "instOfNatNat"),
    (Name.simple "LE",     Name.simple "instLENat"),
    (Name.simple "LT",     Name.simple "instLTNat"),
    (Name.simple "Add",    Name.simple "instAddNat"),
    (Name.simple "HAdd",   Name.simple "instHAdd"),
    (Name.simple "NatPow", Name.simple "instNatPowNat"),
    (Name.simple "Pow",    Name.simple "instPowNat"),
    (Name.simple "HPow",   Name.simple "instHPow")
  ]
  for (clsName, instName) in entries do
    if !(env.instances.any fun e => e.className == clsName && e.instName == instName) then
      env := env.addInstance { className := clsName, instName := instName }
  return env

/-- Seed Lean 4's `Init` arithmetic, order, numeral (`OfNat`), and inequality (`Ne`) typeclasses
    and `Nat` instances (`LE.le`, `LT.lt`, `GE.ge`, `GT.gt`, `HAdd.hAdd`, `HPow.hPow`, `OfNat.ofNat`)
    into `env` so statements like Fermat's Last Theorem elaborate to the exact Lean 4 `Ix.Expr`. -/
def seedLeanInitArith (env : IxElabEnv) : IxElabEnv := Id.run do
  let mut env := env
  let uName := Name.simple "u"
  let vName := Name.simple "v"
  let wName := Name.simple "w"
  let uLvl  := Level.mkParam uName
  let vLvl  := Level.mkParam vName
  let wLvl  := Level.mkParam wName
  let zLvl  := Level.mkZero
  let type0 := Expr.mkSort (Level.mkSucc zLvl)
  let sortU := Expr.mkSort uLvl
  let typeU := Expr.mkSort (Level.mkSucc uLvl)
  let typeV := Expr.mkSort (Level.mkSucc vLvl)
  let typeW := Expr.mkSort (Level.mkSucc wLvl)
  let prop  := Expr.mkProp
  let natName := Name.simple "Nat"
  let natConst := Expr.mkConst natName #[]

  let addAxiomIfMissing (e : IxElabEnv) (nm : Ix.Name) (lvls : Array Ix.Name) (ty : Ix.Expr) : IxElabEnv :=
    if e.contains nm then e
    else e.addConst (.axiomInfo { cnst := { name := nm, levelParams := lvls, type := ty }, isUnsafe := false })

  -- 0. `Nat : Type` and `Eq.{u} : {α : Sort u} → α → α → Prop`
  env := addAxiomIfMissing env natName #[] type0
  let eqName := Name.simple "Eq"
  let eqType :=
    Expr.mkForallE (Name.simple "α") sortU
      (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 0)
        (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 1) prop .default) .default)
      .implicit
  env := addAxiomIfMissing env eqName #[uName] eqType

  -- 1. `Not : Prop → Prop` and `Ne.{u} : {α : Sort u} → α → α → Prop`
  let notName := Name.simple "Not"
  env := addAxiomIfMissing env notName #[] (Expr.mkForallE (Name.simple "a") prop prop .default)
  let neName := Name.simple "Ne"
  let neType :=
    Expr.mkForallE (Name.simple "α") sortU
      (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 0)
        (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 1) prop .default) .default)
      .implicit
  env := addAxiomIfMissing env neName #[uName] neType

  -- 2. `OfNat.{u} (α : Type u) (_ : Nat) : Type u`, `OfNat.ofNat`, `instOfNatNat`
  let ofNatName := Name.simple "OfNat"
  let ofNatTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE Name.mkAnon natConst typeU .default) .default
  env := addAxiomIfMissing env ofNatName #[uName] ofNatTy

  let ofNatFnName := Name.mkStr2 "OfNat" "ofNat"
  let ofNatApp := Expr.mkAppN (Expr.mkConst ofNatName #[uLvl]) #[Expr.mkBVar 1, Expr.mkBVar 0]
  let ofNatFnTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "x") natConst
        (Expr.mkForallE (Name.simple "self") ofNatApp (Expr.mkBVar 2) .instImplicit) .default)
      .implicit
  env := addAxiomIfMissing env ofNatFnName #[uName] ofNatFnTy

  let instOfNatNatName := Name.simple "instOfNatNat"
  let instOfNatNatTy :=
    Expr.mkForallE (Name.simple "n") natConst
      (Expr.mkAppN (Expr.mkConst ofNatName #[zLvl]) #[natConst, Expr.mkBVar 0]) .default
  env := addAxiomIfMissing env instOfNatNatName #[] instOfNatNatTy

  -- 3. `LE.{u}`, `LE.le.{u}`, `instLENat`, `GE.ge.{u}`
  let leName := Name.simple "LE"
  env := addAxiomIfMissing env leName #[uName] (Expr.mkForallE (Name.simple "α") typeU typeU .default)
  let leApp0 := Expr.mkApp (Expr.mkConst leName #[uLvl]) (Expr.mkBVar 0)
  let leRelTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "self") leApp0
        (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 1)
          (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 2) prop .default) .default)
        .instImplicit) .implicit
  env := addAxiomIfMissing env (Name.mkStr2 "LE" "le") #[uName] leRelTy
  env := addAxiomIfMissing env (Name.mkStr2 "GE" "ge") #[uName] leRelTy
  env := addAxiomIfMissing env (Name.simple "instLENat") #[]
    (Expr.mkApp (Expr.mkConst leName #[zLvl]) natConst)

  -- 4. `LT.{u}`, `LT.lt.{u}`, `instLTNat`, `GT.gt.{u}`
  let ltName := Name.simple "LT"
  env := addAxiomIfMissing env ltName #[uName] (Expr.mkForallE (Name.simple "α") typeU typeU .default)
  let ltApp0 := Expr.mkApp (Expr.mkConst ltName #[uLvl]) (Expr.mkBVar 0)
  let ltRelTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "self") ltApp0
        (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 1)
          (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 2) prop .default) .default)
        .instImplicit) .implicit
  env := addAxiomIfMissing env (Name.mkStr2 "LT" "lt") #[uName] ltRelTy
  env := addAxiomIfMissing env (Name.mkStr2 "GT" "gt") #[uName] ltRelTy
  env := addAxiomIfMissing env (Name.simple "instLTNat") #[]
    (Expr.mkApp (Expr.mkConst ltName #[zLvl]) natConst)

  -- 5. `Add.{u}`, `HAdd.{u, v, w}`, `HAdd.hAdd.{u, v, w}`, `instHAdd.{u}`, `instAddNat`
  let addName := Name.simple "Add"
  env := addAxiomIfMissing env addName #[uName] (Expr.mkForallE (Name.simple "α") typeU typeU .default)
  let hAddName := Name.simple "HAdd"
  let typeMaxUVW := Expr.mkSort (Level.mkSucc (Level.mkMax (Level.mkMax uLvl vLvl) wLvl))
  let hAddTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "β") typeV
        (Expr.mkForallE (Name.simple "γ") typeW typeMaxUVW .default) .default) .default
  env := addAxiomIfMissing env hAddName #[uName, vName, wName] hAddTy

  let hAddApp := Expr.mkAppN (Expr.mkConst hAddName #[uLvl, vLvl, wLvl]) #[Expr.mkBVar 2, Expr.mkBVar 1, Expr.mkBVar 0]
  let hAddFnTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "β") typeV
        (Expr.mkForallE (Name.simple "γ") typeW
          (Expr.mkForallE (Name.simple "self") hAddApp
            (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 3)
              (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 3) (Expr.mkBVar 3) .default) .default)
            .instImplicit) .implicit) .implicit) .implicit
  env := addAxiomIfMissing env (Name.mkStr2 "HAdd" "hAdd") #[uName, vName, wName] hAddFnTy

  let instHAddTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "self") (Expr.mkApp (Expr.mkConst addName #[uLvl]) (Expr.mkBVar 0))
        (Expr.mkAppN (Expr.mkConst hAddName #[uLvl, uLvl, uLvl]) #[Expr.mkBVar 1, Expr.mkBVar 1, Expr.mkBVar 1])
        .instImplicit) .implicit
  env := addAxiomIfMissing env (Name.simple "instHAdd") #[uName] instHAddTy
  env := addAxiomIfMissing env (Name.simple "instAddNat") #[]
    (Expr.mkApp (Expr.mkConst addName #[zLvl]) natConst)

  -- 6. `NatPow.{u}`, `Pow.{u, v}`, `HPow.{u, v, w}`, `HPow.hPow.{u, v, w}`, `instHPow.{u, v}`, `instPowNat.{u}`, `instNatPowNat`
  let natPowName := Name.simple "NatPow"
  env := addAxiomIfMissing env natPowName #[uName] (Expr.mkForallE (Name.simple "α") typeU typeU .default)
  let powName := Name.simple "Pow"
  let typeMaxUV := Expr.mkSort (Level.mkSucc (Level.mkMax uLvl vLvl))
  env := addAxiomIfMissing env powName #[uName, vName]
    (Expr.mkForallE (Name.simple "α") typeU (Expr.mkForallE (Name.simple "β") typeV typeMaxUV .default) .default)
  let hPowName := Name.simple "HPow"
  let hPowTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "β") typeV
        (Expr.mkForallE (Name.simple "γ") typeW typeMaxUVW .default) .default) .default
  env := addAxiomIfMissing env hPowName #[uName, vName, wName] hPowTy

  let hPowApp := Expr.mkAppN (Expr.mkConst hPowName #[uLvl, vLvl, wLvl]) #[Expr.mkBVar 2, Expr.mkBVar 1, Expr.mkBVar 0]
  let hPowFnTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "β") typeV
        (Expr.mkForallE (Name.simple "γ") typeW
          (Expr.mkForallE (Name.simple "self") hPowApp
            (Expr.mkForallE (Name.simple "a") (Expr.mkBVar 3)
              (Expr.mkForallE (Name.simple "b") (Expr.mkBVar 3) (Expr.mkBVar 3) .default) .default)
            .instImplicit) .implicit) .implicit) .implicit
  env := addAxiomIfMissing env (Name.mkStr2 "HPow" "hPow") #[uName, vName, wName] hPowFnTy

  let instHPowTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "β") typeV
        (Expr.mkForallE (Name.simple "self")
          (Expr.mkAppN (Expr.mkConst powName #[uLvl, vLvl]) #[Expr.mkBVar 1, Expr.mkBVar 0])
          (Expr.mkAppN (Expr.mkConst hPowName #[uLvl, vLvl, uLvl]) #[Expr.mkBVar 2, Expr.mkBVar 1, Expr.mkBVar 2])
          .instImplicit) .implicit) .implicit
  env := addAxiomIfMissing env (Name.simple "instHPow") #[uName, vName] instHPowTy

  let instPowNatTy :=
    Expr.mkForallE (Name.simple "α") typeU
      (Expr.mkForallE (Name.simple "self")
        (Expr.mkApp (Expr.mkConst natPowName #[uLvl]) (Expr.mkBVar 0))
        (Expr.mkAppN (Expr.mkConst powName #[uLvl, zLvl]) #[Expr.mkBVar 1, natConst])
        .instImplicit) .implicit
  env := addAxiomIfMissing env (Name.simple "instPowNat") #[uName] instPowNatTy
  env := addAxiomIfMissing env (Name.simple "instNatPowNat") #[]
    (Expr.mkApp (Expr.mkConst natPowName #[zLvl]) natConst)

  return registerLeanInitArithInstances env

/-! ## Auto-Bound Implicit Parameters & Attributes -/

/-- Extract `@[attr₁, attr₂, ...]` attribute names from a declaration's `modifiers` node. -/
def extractDeclAttributes (modsNode : Ix.Syntax) : Array Ix.Name :=
  (Syntax.getArgs modsNode).filterMap fun child =>
    match child with
    | .ident _ _ id _ => if Name.isAnonymous id then none else some id
    | _               => none

/-- True if `id` is a single-component Greek (`α..ω`) or single lowercase ASCII (`a..z`) identifier
    eligible for Lean 4 auto-implicit parameter binding (`{α : _}`). -/
def isAutoImplicitCandidate (id : Ix.Name) : Bool :=
  match Name.components id with
  | [s] =>
    if s.length == 1 then
      match s.toList with
      | [c] =>
        ('a' ≤ c && c ≤ 'z') ||
        (0x03B1 ≤ c.toNat && c.toNat ≤ 0x03C9) -- Greek α (0x03B1) .. ω (0x03C9)
      | _ => false
    else false
  | _ => false

/-- Scan `paramGroups` and `optTypeNode` for unbound auto-implicit candidates, returning
    implicit `{id : _}` `ParsedBinderGroup`s in left-to-right appearance order. -/
def collectAutoImplicitGroups (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (env : IxElabEnv) (varGroups : List ParsedBinderGroup)
    (paramGroups : List ParsedBinderGroup) (optTypeNode : Ix.Syntax) : List ParsedBinderGroup := Id.run do
  let isKnownConst (id : Ix.Name) : Bool :=
    let res := resolveIdentInScope scope modIdx (fun n => env.contains n) id
    env.contains res || modIdx.declByName.contains res || env.isCtor res || modIdx.isModuleCtor res
  let rec scanStx (fuel : Nat) (bound : NameSet) (stx : Ix.Syntax) (acc : List Ix.Name) : List Ix.Name :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      match stx with
      | .ident _ _ id _ =>
        if !bound.contains id && isAutoImplicitCandidate id && !isKnownConst id && !acc.contains id then
          acc ++ [id]
        else
          acc
      | .node _ k args =>
        -- Do not treat universe level annotations as term auto-implicits
        if k == SyntaxKind.typeTerm || k == SyntaxKind.sortTerm ||
           k == SyntaxKind.explicitTerm || k == SyntaxKind.projTerm then
          if k == SyntaxKind.projTerm then
            scanStx f bound (args.getD 0 .missing) acc
          else acc
        else if k == SyntaxKind.forallTerm then
          let isKw := match args[0]? with
            | some (.atom _ kw) => kw == "forall" || kw == "∀"
            | _ => false
          let bNode := if isKw then args.getD 1 .missing else args.getD 0 .missing
          let body  := if isKw then args.getD 4 .missing else args.getD 3 .missing
          let bGrps := (Syntax.getArgs bNode).toList.map decodeBinderNode
          let (bound', acc') := bGrps.foldl (fun (bSet, a) g =>
            let a' := match g.typeStx? with | some ts => scanStx f bSet ts a | none => a
            let bSet' := g.names.foldl (fun s n => s.insert n) bSet
            (bSet', a')) (bound, acc)
          scanStx f bound' body acc'
        else if k == SyntaxKind.funTerm then
          let bNode := args.getD 1 .missing
          let body  := args.getD 3 .missing
          let bGrps := (Syntax.getArgs bNode).toList.map decodeBinderNode
          let (bound', acc') := bGrps.foldl (fun (bSet, a) g =>
            let a' := match g.typeStx? with | some ts => scanStx f bSet ts a | none => a
            let bSet' := g.names.foldl (fun s n => s.insert n) bSet
            (bSet', a')) (bound, acc)
          scanStx f bound' body acc'
        else if k == SyntaxKind.letTerm || k == SyntaxKind.letBorrowTerm || k == SyntaxKind.letRecTerm then
          let isLong := k != SyntaxKind.letTerm
          let idStx  := if isLong then args.getD 3 .missing else args.getD 2 .missing
          let bNode  := if isLong then args.getD 4 .missing else args.getD 3 .missing
          let optTy  := if isLong then args.getD 5 .missing else args.getD 4 .missing
          let val    := if isLong then args.getD 7 .missing else args.getD 6 .missing
          let body   := if isLong then args.getD 9 .missing else args.getD 8 .missing
          let letId  := Syntax.getId idStx
          let bGrps  := (Syntax.getArgs bNode).toList.map decodeBinderNode
          let (boundB, acc1) := bGrps.foldl (fun (bSet, a) g =>
            let a' := match g.typeStx? with | some ts => scanStx f bSet ts a | none => a
            let bSet' := g.names.foldl (fun s n => s.insert n) bSet
            (bSet', a')) (bound, acc)
          let acc2 := scanStx f boundB optTy acc1
          let boundVal := if k == SyntaxKind.letRecTerm && !Name.isAnonymous letId then boundB.insert letId else boundB
          let acc3 := scanStx f boundVal val acc2
          let boundBody := if Name.isAnonymous letId then bound else bound.insert letId
          scanStx f boundBody body acc3
        else
          args.toList.foldl (fun a child => scanStx f bound child a) acc
      | _ => acc
  let initBound : NameSet :=
    varGroups.foldl (fun s g => g.names.foldl (fun s' n => s'.insert n) s) NameSet.empty
  let (boundAfterParams, autoNames1) :=
    paramGroups.foldl (fun (bSet, a) g =>
      let a' := match g.typeStx? with | some ts => scanStx 64 bSet ts a | none => a
      let bSet' := g.names.foldl (fun s n => s.insert n) bSet
      (bSet', a')) (initBound, [])
  let autoNames := scanStx 64 boundAfterParams optTypeNode autoNames1
  let defaultTypeStx := Syntax.mkNode SyntaxKind.typeTerm #[Syntax.mkSimpleAtom "Type", Syntax.mkNullNode #[]]
  return autoNames.map fun nm =>
    { names := #[nm], typeStx? := some defaultTypeStx, binderInfo := .implicit, contract := default }

/-! ## Inductive, Structure, and Class SCC Elaboration -/

/-- Elaborate the header `(numParams, numIndices, levelParams, fullType)` of an
    `inductive`, `structure`, or `class` declaration. -/
def elabInductiveHeader (decl : ModuleDecl) (fuel : Nat := 128) :
    IxElabM (Nat × Nat × Array Ix.Name × Ix.Expr) := do
  modify fun st => { st with autoBoundUnivs := [], localLetContracts := #[] }
  let cmd := decl.stx
  let k := Syntax.getKind cmd
  let bindersNode := Syntax.getArg cmd 4
  let optTypeNode :=
    if k == SyntaxKind.inductiveDecl then Syntax.getArg cmd 6
    else Syntax.getArg cmd 7
  let varGroups := decl.scope.varBinders.toList.map decodeBinderNode
  let paramGroups := (Syntax.getArgs bindersNode).toList.map decodeBinderNode
  let ctx0 ← read
  let st0 ← get
  let autoGroups := collectAutoImplicitGroups decl.scope ctx0.modIdx st0.env varGroups paramGroups optTypeNode
  let allGroups := varGroups ++ autoGroups ++ paramGroups
  withReader (fun ctx => { ctx with
      lctx := LocalContext.empty
      scope := decl.scope
      currDecl? := some decl.fullName
      univParams := decl.univParams }) do
    elabBinderGroups (fun s exp? => elabTerm fuel s exp?) allGroups #[] fun paramFVars => do
      let resultTy ←
        if Syntax.isNone optTypeNode || Syntax.isMissing optTypeNode then
          pure (Expr.mkSort (Level.mkSucc Level.mkZero))
        else
          let t ← elabTerm fuel optTypeNode none
          let _ ← ensureSort 32 t
          instantiateMVars 32 t
      let nIndices := countForalls 64 resultTy
      let fullType ← mkForallFVars paramFVars resultTy
      let fullType ← instantiateMVars 32 fullType
      let fullType := defaultUnassignedExprLevelMVars fullType
      let st ← get
      let lvlParams := Array.mk (decl.univParams ++ decl.scope.levelNames ++ st.autoBoundUnivs).eraseDups
      return (paramFVars.size, nIndices, lvlParams, fullType)

/-- Elaborate a single constructor `| shortId binders [: optType]` of an inductive `decl`. -/
def elabOneConstructor (decl : ModuleDecl) (lvlParams : Array Ix.Name)
    (paramGroups : List ParsedBinderGroup) (ctorStx : Ix.Syntax) (cidx : Nat)
    (fuel : Nat := 128) : IxElabM (Ix.ConstructorVal × Array Ixon.BinderContract × Ixon.ValueContract) := do
  let shortId := Syntax.getId (Syntax.getArg ctorStx 1)
  let fullCtorName := Name.append decl.fullName shortId
  let cBindersNode := Syntax.getArg ctorStx 2
  let cVPrefNode   := Syntax.getArg ctorStx 3
  let cOptTypeNode := Syntax.getArg ctorStx 4
  let retContract  := (decodeContractPrefix cVPrefNode).toValueContract
  let cGroups      := (Syntax.getArgs cBindersNode).toList.map decodeBinderNode
  -- Param binders on constructors are always `.implicit` in Lean/Ix kernel
  let implicitParamGroups := paramGroups.map fun g => { g with binderInfo := .implicit }
  withReader (fun ctx => { ctx with
      lctx := LocalContext.empty
      scope := decl.scope
      currDecl? := some fullCtorName
      univParams := lvlParams.toList }) do
    elabBinderGroups (fun s exp? => elabTerm fuel s exp?) implicitParamGroups #[] fun paramFVars => do
      elabBinderGroups (fun s exp? => elabTerm fuel s exp?) cGroups #[] fun fieldFVars => do
        let indUnivs := lvlParams.map Level.mkParam
        let paramExprs := paramFVars.map Expr.mkFVar
        let defaultRet := Expr.mkAppN (Expr.mkConst decl.fullName indUnivs) paramExprs
        let (targetRet, extraFields) ←
          if Syntax.isNone cOptTypeNode || Syntax.isMissing cOptTypeNode then
            pure (defaultRet, 0)
          else
            let t ← elabTerm fuel cOptTypeNode none
            let _ ← ensureSort 32 t
            let tInst ← instantiateMVars 32 t
            pure (tInst, countForalls 64 tInst)
        let allFVars := paramFVars ++ fieldFVars
        let fullCtorTy ← mkForallFVars allFVars targetRet retContract
        let fullCtorTy ← instantiateMVars 32 fullCtorTy
        let fullCtorTy := defaultUnassignedExprLevelMVars fullCtorTy
        let ctxNow ← read
        let bcs : Array Ixon.BinderContract := allFVars.filterMap fun fv =>
          (ctxNow.lctx.findFVar? fv).map (·.contract)
        let cval : Ix.ConstructorVal := {
          cnst := {
            name        := fullCtorName
            levelParams := lvlParams
            type        := fullCtorTy
          }
          induct    := decl.fullName
          cidx      := cidx
          numParams := paramFVars.size
          numFields := fieldFVars.size + extraFields
          isUnsafe  := false
        }
        return (cval, bcs, retContract)

/-- Elaborate a `structure` or `class` field list (including `extends Parent₁, Parent₂` with
    diamond field deduplication) into a single constructor, `StructInfo`, and parent projection definitions. -/
def elabStructureFields (decl : ModuleDecl) (lvlParams : Array Ix.Name)
    (paramGroups : List ParsedBinderGroup) (ctorFullName : Ix.Name)
    (fieldsNode : Ix.Syntax) (fuel : Nat := 128) :
    IxElabM (Ix.ConstructorVal × StructInfo × Array Ixon.BinderContract × Array Ix.DefinitionVal) := do
  let implicitParamGroups := paramGroups.map fun g => { g with binderInfo := .implicit }
  let extendsNode := Syntax.getArg decl.stx 5
  let parentStxs := (Syntax.getArgs extendsNode).toList
  let fieldItems := (Syntax.getArgs fieldsNode).toList
  withReader (fun ctx => { ctx with
      lctx := LocalContext.empty
      scope := decl.scope
      currDecl? := some ctorFullName
      univParams := lvlParams.toList }) do
    elabBinderGroups (fun s exp? => elabTerm fuel s exp?) implicitParamGroups #[] fun paramFVars => do
      -- Flatten `fieldDecl` items into `(shortFieldName, bi, contract, tyStx, defaultStx?)`
      let flatFields : List (Ix.Name × Lean.BinderInfo × Ixon.BinderContract × Ix.Syntax × Option Ix.Syntax) :=
        fieldItems.flatMap fun item =>
          let firstAtom := Syntax.getAtomVal (Syntax.getArg item 0)
          let (isBrack, bi) : Bool × Lean.BinderInfo :=
            if firstAtom == "(" then (true, .default)
            else if firstAtom == "{" then (true, .implicit)
            else (false, .default)
          let bPrefNode := if isBrack then Syntax.getArg item 1 else Syntax.getArg item 0
          let idsNode   := if isBrack then Syntax.getArg item 2 else Syntax.getArg item 1
          let vPrefNode := if isBrack then Syntax.getArg item 4 else Syntax.getArg item 3
          let tyNode    := if isBrack then Syntax.getArg item 5 else Syntax.getArg item 4
          let optDef    := if isBrack then Syntax.getArg item 6 else Syntax.getArg item 5
          let defStx?   := (Syntax.getOptional? optDef).map fun seq => Syntax.getArg seq 1
          let contract  := (mergeParsedContracts (decodeContractPrefix bPrefNode) (decodeContractPrefix vPrefNode)).toBinderContract
          (Syntax.getArgs idsNode).toList.map fun idStx =>
            (Syntax.getId idStx, bi, contract, tyNode, defStx?)

      -- Elaborate own fields after inherited parent fields (with diamond deduplication)
      let rec elabFieldLoop
          (rem : List (Ix.Name × Lean.BinderInfo × Ixon.BinderContract × Ix.Syntax × Option Ix.Syntax))
          (fIdx : Nat) (fvars : Array Ix.Name) (fInfos : Array StructFieldInfo)
          (k : Array Ix.Name → Array StructFieldInfo → IxElabM (Ix.ConstructorVal × StructInfo × Array Ixon.BinderContract × Array Ix.DefinitionVal)) :
          IxElabM (Ix.ConstructorVal × StructInfo × Array Ixon.BinderContract × Array Ix.DefinitionVal) := do
        match rem with
        | [] => k fvars fInfos
        | (fShort, bi, contract, tyStx, defStx?) :: rest =>
          -- If `fShort` was already inherited from a parent structure, optionally update its default value and skip
          match fInfos.findIdx? (fun fi => fi.fieldName == fShort) with
          | some existingIdx =>
            let fInfos' := match defStx? with
              | some dStx =>
                if h : existingIdx < fInfos.size then
                  fInfos.set existingIdx { fInfos[existingIdx] with defaultVal := some dStx }
                else fInfos
              | none => fInfos
            elabFieldLoop rest fIdx fvars fInfos' k
          | none =>
            let fTy ← elabTerm fuel tyStx none
            let _ ← ensureSort 32 fTy
            let fTyInst ← instantiateMVars 32 fTy
            let fInfo : StructFieldInfo := {
              fieldName  := fShort
              projFnName := Name.append decl.fullName fShort
              fieldIdx   := fIdx
              binderInfo := bi
              contract   := contract
              defaultVal := defStx?
            }
            withLocalDecl fShort fTyInst bi contract fun fvId _ =>
              elabFieldLoop rest (fIdx + 1) (fvars.push fvId) (fInfos.push fInfo) k

      -- Elaborate inherited parent structures (`extends P₁, P₂`) and flatten their fields with diamond deduplication
      let rec elabParentFields
          (remPFields : List StructFieldInfo) (curPCtorTy : Ix.Expr)
          (fIdx : Nat) (fvars : Array Ix.Name) (fInfos : Array StructFieldInfo)
          (nextK : Nat → Array Ix.Name → Array StructFieldInfo → IxElabM (Ix.ConstructorVal × StructInfo × Array Ixon.BinderContract × Array Ix.DefinitionVal)) :
          IxElabM (Ix.ConstructorVal × StructInfo × Array Ixon.BinderContract × Array Ix.DefinitionVal) := do
        match remPFields with
        | [] => nextK fIdx fvars fInfos
        | pf :: restPF =>
          let curW ← whnf fuel curPCtorTy
          match stripMData curW with
          | .forallE _ fDom fBody _ _ =>
            match fInfos.findIdx? (fun fi => fi.fieldName == pf.fieldName) with
            | some existingIdx =>
              let existingFvExpr := Expr.mkFVar (fvars.getD existingIdx Name.mkAnon)
              elabParentFields restPF (instantiate1 fBody existingFvExpr) fIdx fvars fInfos nextK
            | none =>
              let fDomInst ← instantiateMVars 32 fDom
              let fInfo : StructFieldInfo := {
                fieldName  := pf.fieldName
                projFnName := Name.append decl.fullName pf.fieldName
                fieldIdx   := fIdx
                binderInfo := pf.binderInfo
                contract   := pf.contract
                defaultVal := pf.defaultVal
              }
              withLocalDecl pf.fieldName fDomInst pf.binderInfo pf.contract fun fvId fvExpr =>
                elabParentFields restPF (instantiate1 fBody fvExpr) (fIdx + 1) (fvars.push fvId) (fInfos.push fInfo) nextK
          | _ => nextK fIdx fvars fInfos

      let rec elabParentsLoop
          (remParents : List Ix.Syntax)
          (fIdx : Nat) (fvars : Array Ix.Name) (fInfos : Array StructFieldInfo)
          (parentSpecs : Array (Ix.Name × Array Ix.Level × Array Ix.Expr × StructInfo)) :
          IxElabM (Ix.ConstructorVal × StructInfo × Array Ixon.BinderContract × Array Ix.DefinitionVal) := do
        match remParents with
        | [] =>
          elabFieldLoop flatFields fIdx fvars fInfos fun fieldFVars fieldInfos => do
            let indUnivs := lvlParams.map Level.mkParam
            let paramExprs := paramFVars.map Expr.mkFVar
            let retTy := Expr.mkAppN (Expr.mkConst decl.fullName indUnivs) paramExprs
            let allFVars := paramFVars ++ fieldFVars
            let ctorTy ← mkForallFVars allFVars retTy
            let ctorTy ← instantiateMVars 32 ctorTy
            let ctorTy := defaultUnassignedExprLevelMVars ctorTy
            let ctxNow ← read
            let bcs : Array Ixon.BinderContract := allFVars.filterMap fun fv =>
              (ctxNow.lctx.findFVar? fv).map (·.contract)
            let cval : Ix.ConstructorVal := {
              cnst := {
                name        := ctorFullName
                levelParams := lvlParams
                type        := ctorTy
              }
              induct    := decl.fullName
              cidx      := 0
              numParams := paramFVars.size
              numFields := fieldFVars.size
              isUnsafe  := false
            }
            let sInfo : StructInfo := {
              structName := decl.fullName
              ctorName   := ctorFullName
              numParams  := paramFVars.size
              fields     := fieldInfos
              parents    := parentSpecs.map (fun (pn, _, _, _) => pn)
              isClass    := decl.kind == .cls
            }
            -- Build `<Child>.to<Parent>` projection functions for each parent in `parentSpecs`
            let mut toParentDefs : Array Ix.DefinitionVal := #[]
            let selfBi : Lean.BinderInfo := if decl.kind == .cls then .instImplicit else .default
            for (pName, pUnivs, pArgs, pInfo) in parentSpecs do
              let basePName := (Name.conflictOrigName? pName).getD pName
              let pShort := (Name.components basePName).getLastD (Name.toStringTotal basePName)
              let toParentName := Name.mkStr decl.fullName s!"to{pShort}"
              let pRetTy := Expr.mkAppN (Expr.mkConst pName pUnivs) pArgs
              let (tpTy, tpVal) ← withLocalDecl (Name.simple "self") retTy selfBi default fun selfFvId selfExpr => do
                let mut ctorCall := Expr.mkAppN (Expr.mkConst pInfo.ctorName pUnivs) pArgs
                for pf in pInfo.fields do
                  let cIdx := (fieldInfos.find? (fun cf => cf.fieldName == pf.fieldName)).map (·.fieldIdx) |>.getD 0
                  ctorCall := Expr.mkApp ctorCall (Expr.mkProj decl.fullName cIdx selfExpr)
                let fnTy ← mkForallFVars (paramFVars.push selfFvId) pRetTy
                let fnVal ← mkLambdaFVars (paramFVars.push selfFvId) ctorCall
                let fnTy ← instantiateMVars 32 fnTy
                let fnVal ← instantiateMVars 32 fnVal
                pure (defaultUnassignedExprLevelMVars fnTy, defaultUnassignedExprLevelMVars fnVal)
              toParentDefs := toParentDefs.push {
                cnst := { name := toParentName, levelParams := lvlParams, type := tpTy }
                value := tpVal
                hints := .abbrev
                safety := .safe
                all := #[toParentName]
              }
            return (cval, sInfo, bcs, toParentDefs)
        | pStx :: restP =>
          let pTy ← elabTerm fuel pStx none
          let _ ← ensureSort 32 pTy
          let pTyInst ← instantiateMVars 32 pTy
          let pTyW ← whnf fuel pTyInst
          let (pHead, pArgs) := getAppFnArgs pTyW
          let st ← get
          match pHead with
          | .const pStructName pUnivs _ =>
            match st.env.structTable.get? pStructName with
            | some pInfo =>
              match st.env.find? pInfo.ctorName with
              | some (.ctorInfo pCval) =>
                let pCtorInstTy := pArgs.foldl (fun cur pa =>
                  match stripMData cur with
                  | .forallE _ _ b _ _ => instantiate1 b pa
                  | other => other) (substExprLevelParams pCval.cnst.levelParams pUnivs pCval.cnst.type)
                elabParentFields pInfo.fields.toList pCtorInstTy fIdx fvars fInfos fun fIdx' fvars' fInfos' =>
                  elabParentsLoop restP fIdx' fvars' fInfos' (parentSpecs.push (pStructName, pUnivs, pArgs, pInfo))
              | _ =>
                throwElabError s!"missing constructor for parent structure '{Name.toStringTotal pStructName}'" (some pStx)
            | none =>
              throwElabError s!"parent '{Name.toStringTotal pStructName}' in 'extends' is not a structure or class" (some pStx)
          | _ =>
            throwElabError "parent in 'extends' must be a structure or class application" (some pStx)

      elabParentsLoop parentStxs 0 #[] #[] #[]

/-- Synthesize and register derived typeclass instances (`deriving Inhabited, BEq, DecidableEq`)
    for an elaborated `inductive` or `structure`. -/
def elabDerivingHandlers (decl : ModuleDecl) (ival : Ix.InductiveVal) (fuel : Nat := 128) : IxElabM Unit := do
  let cmd := decl.stx
  let k := Syntax.getKind cmd
  let derivNode :=
    if k == SyntaxKind.inductiveDecl then Syntax.getArg cmd 8
    else Syntax.getArg cmd 10
  let derivIds := (Syntax.getArgs derivNode).toList.map Syntax.getId
  if derivIds.isEmpty then return ()
  let shortDecl := (Name.components decl.fullName).getLastD (Name.toStringTotal decl.fullName)
  let indUnivs := ival.cnst.levelParams.map Level.mkParam
  let (paramFVars, paramDecls, _) := openForallTelescope ival.numParams ival.cnst.type "dp" 0 #[] #[]
  let indApplied := Expr.mkAppN (Expr.mkConst decl.fullName indUnivs) paramFVars
  let paramImpDecls := paramDecls.map fun d => { d with binderInfo := .implicit }

  for clsId in derivIds do
    -- 1. `deriving Inhabited`
    if clsId == Name.simple "Inhabited" then
      let st ← get
      if let some ctorName := ival.ctors[0]? then
        if let some (.ctorInfo cval) := st.env.find? ctorName then
          -- Require `[Inhabited α_i]` for each type parameter `α_i`
          let mut instDecls : Array AuxLocalDecl := #[]
          for (pDecl, pIdx) in paramDecls.zipIdx do
            let (pSortHead, _) := getAppFnArgs pDecl.domain
            if let .sort u _ := pSortHead then
              let uPred := match u with | .succ p _ => p | _ => Level.mkZero
              let (iFvId, _) := mkAuxFVar "dinh" pIdx
              let iDom := Expr.mkApp (Expr.mkConst (Name.simple "Inhabited") #[uPred]) (paramFVars.getD pIdx indApplied)
              instDecls := instDecls.push { fvarId := iFvId, binderName := Name.simple s!"inst_{pIdx}", domain := iDom, binderInfo := .instImplicit }
          -- Temporarily add `paramImpDecls ++ instDecls` to `lctx` and synthesize `Inhabited.default` for each field of `ctorName`
          let allHdrDecls := paramImpDecls ++ instDecls
          let lctxHdr := allHdrDecls.foldl (fun lc d =>
            lc.addDecl { fvarId := d.fvarId, userName := d.binderName, type := d.domain, binderInfo := d.binderInfo }) LocalContext.empty
          let ctorInstTy := paramFVars.foldl (fun cur p =>
            match stripMData cur with
            | .forallE _ _ b _ _ => instantiate1 b p
            | other => other) (substExprLevelParams cval.cnst.levelParams indUnivs cval.cnst.type)
          let defaultVal ← withReader (fun ctx => { ctx with lctx := lctxHdr, scope := decl.scope, univParams := ival.cnst.levelParams.toList }) do
            let mut curFn := Expr.mkAppN (Expr.mkConst ctorName indUnivs) paramFVars
            let mut curTy := ctorInstTy
            for _ in [:cval.numFields] do
              let curW ← whnf fuel curTy
              match stripMData curW with
              | .forallE _ fDom fBody _ _ =>
                let defTerm ← elabTerm fuel (Syntax.mkSimpleIdent (Name.simple "default")) (some fDom)
                curFn := Expr.mkApp curFn defTerm
                curTy := instantiate1 fBody defTerm
              | _ => pure ()
            instantiateMVars 32 curFn
          let inhZero := Level.mkZero
          let instRetTy := Expr.mkApp (Expr.mkConst (Name.simple "Inhabited") #[inhZero]) indApplied
          let instBody := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Inhabited" "mk") #[inhZero]) #[indApplied, defaultVal]
          let instFullTy := defaultUnassignedExprLevelMVars (closeForalls allHdrDecls instRetTy)
          let instFullVal := defaultUnassignedExprLevelMVars (closeLambdas allHdrDecls instBody)
          let instName := Name.fromComponents ((Name.components decl.fullName).dropLast ++ [s!"instInhabited{shortDecl}"])
          modifyEnv fun env =>
            let env := env.addConst (.defnInfo {
              cnst := { name := instName, levelParams := ival.cnst.levelParams, type := instFullTy }
              value := instFullVal, hints := .abbrev, safety := .safe, all := #[instName]
            })
            env.addInstance { instName := instName, className := Name.simple "Inhabited" }

    -- 2. `deriving BEq` (and `DecidableEq`)
    else if clsId == Name.simple "BEq" || clsId == Name.simple "DecidableEq" then
      let st ← get
      let casesOnName := Name.mkStr decl.fullName "casesOn"
      if let some (.defnInfo casesOnDef) := st.env.find? casesOnName then
        let mut instDecls : Array AuxLocalDecl := #[]
        for (pDecl, pIdx) in paramDecls.zipIdx do
          let (pSortHead, _) := getAppFnArgs pDecl.domain
          if let .sort u _ := pSortHead then
            let uPred := match u with | .succ p _ => p | _ => Level.mkZero
            let (iFvId, _) := mkAuxFVar "dbeq" pIdx
            let iDom := Expr.mkApp (Expr.mkConst (Name.simple "BEq") #[uPred]) (paramFVars.getD pIdx indApplied)
            instDecls := instDecls.push { fvarId := iFvId, binderName := Name.simple s!"instBEq_{pIdx}", domain := iDom, binderInfo := .instImplicit }
        let (aFvId, aFvExpr) := mkAuxFVar "dbeq_a" 0
        let (bFvId, bFvExpr) := mkAuxFVar "dbeq_b" 1
        let aDecl : AuxLocalDecl := { fvarId := aFvId, binderName := Name.simple "a", domain := indApplied }
        let bDecl : AuxLocalDecl := { fvarId := bFvId, binderName := Name.simple "b", domain := indApplied }
        let allHdrDecls := paramImpDecls ++ instDecls
        let boolConst := Expr.mkConst (Name.simple "Bool") #[]
        let trueConst := Expr.mkConst (Name.mkStr2 "Bool" "true") #[]
        let falseConst := Expr.mkConst (Name.mkStr2 "Bool" "false") #[]
        let casesOnUnivs :=
          if casesOnDef.cnst.levelParams.size == indUnivs.size + 1 then
            #[Level.mkSucc Level.mkZero] ++ indUnivs
          else indUnivs
        let motive := Expr.mkLam (Name.simple "_") indApplied boolConst .default
        -- Build outer `casesOn` on `aFvExpr` and inner `casesOn` on `bFvExpr`
        let mut outerMinors : Array Ix.Expr := #[]
        for (ctorA, idxA) in ival.ctors.zipIdx do
          if let some (.ctorInfo cvalA) := st.env.find? ctorA then
            let ctorATy := paramFVars.foldl (fun cur p =>
              match stripMData cur with
              | .forallE _ _ b _ _ => instantiate1 b p
              | other => other) (substExprLevelParams cvalA.cnst.levelParams indUnivs cvalA.cnst.type)
            let (aFieldFVars, aFieldDecls, _) := openForallTelescope cvalA.numFields ctorATy s!"dfa_{idxA}" 0 #[] #[]
            let mut innerMinors : Array Ix.Expr := #[]
            for (ctorB, idxB) in ival.ctors.zipIdx do
              if let some (.ctorInfo cvalB) := st.env.find? ctorB then
                let ctorBTy := paramFVars.foldl (fun cur p =>
                  match stripMData cur with
                  | .forallE _ _ b _ _ => instantiate1 b p
                  | other => other) (substExprLevelParams cvalB.cnst.levelParams indUnivs cvalB.cnst.type)
                let (bFieldFVars, bFieldDecls, _) := openForallTelescope cvalB.numFields ctorBTy s!"dfb_{idxB}" 0 #[] #[]
                if idxA != idxB then
                  innerMinors := innerMinors.push (closeLambdas bFieldDecls falseConst)
                else if cvalA.numFields == 0 then
                  innerMinors := innerMinors.push (closeLambdas bFieldDecls trueConst)
                else
                  let branchDecls := allHdrDecls ++ #[aDecl, bDecl] ++ aFieldDecls ++ bFieldDecls
                  let lctxBranch := branchDecls.foldl (fun lc d =>
                    lc.addDecl { fvarId := d.fvarId, userName := d.binderName, type := d.domain, binderInfo := d.binderInfo }) LocalContext.empty
                  let cmpExpr ← withReader (fun ctx => { ctx with lctx := lctxBranch, scope := decl.scope, univParams := ival.cnst.levelParams.toList }) do
                    let mut eqConj : Option Ix.Expr := none
                    for fIdx in [:cvalA.numFields] do
                      let lhsF := aFieldFVars.getD fIdx trueConst
                      let rhsF := bFieldFVars.getD fIdx trueConst
                      let fDom := (aFieldDecls.getD fIdx aDecl).domain
                      let beqGoal := Expr.mkApp (Expr.mkConst (Name.simple "BEq") #[Level.mkZero]) fDom
                      let instExpr ← match ← synthInstance? 8 beqGoal with
                        | some ie => pure ie
                        | none    => pure (Expr.mkConst (Name.simple "instBEqNat") #[])
                      let fEq := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "BEq" "beq") #[Level.mkZero]) #[fDom, instExpr, lhsF, rhsF]
                      eqConj := match eqConj with
                        | none      => some fEq
                        | some prev => some (Expr.mkAppN (Expr.mkConst (Name.simple "and") #[]) #[prev, fEq])
                    instantiateMVars 32 (eqConj.getD trueConst)
                  innerMinors := innerMinors.push (closeLambdas bFieldDecls cmpExpr)
            let innerCases := Expr.mkAppN (Expr.mkConst casesOnName casesOnUnivs)
              (paramFVars ++ #[motive, bFvExpr] ++ innerMinors)
            outerMinors := outerMinors.push (closeLambdas aFieldDecls innerCases)
        let outerCases := Expr.mkAppN (Expr.mkConst casesOnName casesOnUnivs)
          (paramFVars ++ #[motive, aFvExpr] ++ outerMinors)
        let beqLam := closeLambdas #[aDecl, bDecl] outerCases
        let beqZero := Level.mkZero
        let instRetTy := Expr.mkApp (Expr.mkConst (Name.simple "BEq") #[beqZero]) indApplied
        let instBody := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "BEq" "mk") #[beqZero]) #[indApplied, beqLam]
        let instFullTy := defaultUnassignedExprLevelMVars (closeForalls allHdrDecls instRetTy)
        let instFullVal := defaultUnassignedExprLevelMVars (closeLambdas allHdrDecls instBody)
        let instName := Name.fromComponents ((Name.components decl.fullName).dropLast ++ [s!"instBEq{shortDecl}"])
        modifyEnv fun env =>
          let env := env.addConst (.defnInfo {
            cnst := { name := instName, levelParams := ival.cnst.levelParams, type := instFullTy }
            value := instFullVal, hints := .abbrev, safety := .safe, all := #[instName]
          })
          env.addInstance { instName := instName, className := Name.simple "BEq" }

/-- Elaborate an inductive/structure/class SCC, canonicalize its block & constructor order,
    and generate surgery-free recursors and auxiliary definitions. -/
def elabInductiveSCC (decls : Array ModuleDecl) (fuel : Nat := 128) : IxElabM Unit := do
  -- Step 1: Elaborate headers and pre-register temporary `InductiveVal`s in `st.env`
  let allNames := decls.map (·.fullName)
  let mut headers : Array (ModuleDecl × Nat × Nat × Array Ix.Name × Ix.Expr) := #[]
  for decl in decls do
    let (nParams, nIndices, lvlParams, indType) ← elabInductiveHeader decl fuel
    let tempIndVal : Ix.InductiveVal := {
      cnst := { name := decl.fullName, levelParams := lvlParams, type := indType }
      numParams := nParams, numIndices := nIndices, all := allNames
      ctors := Array.mk decl.ctorNames, numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false
    }
    modifyEnv (·.addConst (.inductInfo tempIndVal))
    headers := headers.push (decl, nParams, nIndices, lvlParams, indType)

  -- Step 2: Elaborate constructors / structure fields for each inductive in the SCC
  let mut rawItems : Array (Ix.InductiveVal × Array Ix.ConstructorVal) := #[]
  let mut structToGenerate : Array (Ix.InductiveVal × Ix.ConstructorVal × StructInfo × Array Ix.DefinitionVal) := #[]
  let indNameSet : NameSet := allNames.foldl (fun s n => s.insert n) NameSet.empty

  for (decl, nParams, nIndices, lvlParams, indType) in headers do
    let cmd := decl.stx
    let k := Syntax.getKind cmd
    let optTypeNode :=
      if k == SyntaxKind.inductiveDecl then Syntax.getArg cmd 6
      else Syntax.getArg cmd 7
    let varGroups := decl.scope.varBinders.toList.map decodeBinderNode
    let rawParamGroups := (Syntax.getArgs (Syntax.getArg cmd 4)).toList.map decodeBinderNode
    let ctxNow ← read
    let stNow ← get
    let autoGroups := collectAutoImplicitGroups decl.scope ctxNow.modIdx stNow.env varGroups rawParamGroups optTypeNode
    let paramGroups := varGroups ++ autoGroups ++ rawParamGroups
    if k == SyntaxKind.inductiveDecl then
      let ctorsNode := Syntax.getArg cmd 7
      let ctorStxs := Syntax.getArgs ctorsNode
      let mut ctors : Array Ix.ConstructorVal := #[]
      for (ctorStx, cidx) in ctorStxs.zipIdx do
        let (cval, bcs, retC) ← elabOneConstructor decl lvlParams paramGroups ctorStx cidx fuel
        modifyEnv (·.addContracts cval.cnst.name bcs retC)
        ctors := ctors.push cval
      let isRec := ctors.any fun cv =>
        let (_, fieldDecls, _) := openForallTelescope (cv.numParams + cv.numFields) cv.cnst.type "rc" 0 #[] #[]
        (fieldDecls.extract cv.numParams fieldDecls.size).any fun fd =>
          !(collectRefsInSet indNameSet fd.domain).isEmpty
      let indVal : Ix.InductiveVal := {
        cnst := { name := decl.fullName, levelParams := lvlParams, type := indType }
        numParams := nParams, numIndices := nIndices, all := allNames
        ctors := ctors.map (·.cnst.name), numNested := 0
        isRec := isRec, isUnsafe := false, isReflexive := false
      }
      rawItems := rawItems.push (indVal, ctors)
    else
      -- `structure` or `class`
      let fieldsOrCtorsNode := Syntax.getArg cmd 9
      let children := Syntax.getArgs fieldsOrCtorsNode
      let isCtorStyleClass : Bool := match children[0]? with
        | some c0 => Syntax.isOfKind c0 SyntaxKind.ctorDecl
        | none    => false
      if isCtorStyleClass == true then
        let mut ctors : Array Ix.ConstructorVal := #[]
        for (ctorStx, cidx) in children.zipIdx do
          let (cval, bcs, retC) ← elabOneConstructor decl lvlParams paramGroups ctorStx cidx fuel
          modifyEnv (·.addContracts cval.cnst.name bcs retC)
          ctors := ctors.push cval
        let isRec := ctors.any fun cv =>
          let (_, fieldDecls, _) := openForallTelescope (cv.numParams + cv.numFields) cv.cnst.type "rc" 0 #[] #[]
          (fieldDecls.extract cv.numParams fieldDecls.size).any fun fd =>
            !(collectRefsInSet indNameSet fd.domain).isEmpty
        let indVal : Ix.InductiveVal := {
          cnst := { name := decl.fullName, levelParams := lvlParams, type := indType }
          numParams := nParams, numIndices := nIndices, all := allNames
          ctors := ctors.map (·.cnst.name), numNested := 0
          isRec := isRec, isUnsafe := false, isReflexive := false
        }
        if decl.kind == .cls then
          modifyEnv fun env => { env with classSet := env.classSet.insert decl.fullName }
        rawItems := rawItems.push (indVal, ctors)
      else
        let ctorFullName := decl.ctorNames.headD (Name.mkStr decl.fullName "mk")
        let (cval, sInfo, bcs, toParentDefs) ← elabStructureFields decl lvlParams paramGroups ctorFullName fieldsOrCtorsNode fuel
        modifyEnv fun env =>
          let env := env.addContracts cval.cnst.name bcs .shared
          env.addStructInfo sInfo
        let indVal : Ix.InductiveVal := {
          cnst := { name := decl.fullName, levelParams := lvlParams, type := indType }
          numParams := nParams, numIndices := nIndices, all := allNames
          ctors := #[cval.cnst.name], numNested := 0
          isRec := false, isUnsafe := false, isReflexive := false
        }
        rawItems := rawItems.push (indVal, #[cval])
        structToGenerate := structToGenerate.push (indVal, cval, sInfo, toParentDefs)

  -- Step 3: Canonicalize block member order & constructor order (breaking α-ties by source order!)
  let stNow ← get
  let addrOf := defaultAddrOf stNow.env
  let canonItems := canonicalizeInductiveBlock addrOf rawItems

  -- Step 4: Register canonical `InductiveVal`s, `ConstructorVal`s, and surgery-free `.rec`, `.recOn`, `.casesOn`, `._ctorIdx`
  modifyEnv fun env => registerCanonicalInductiveBlock env canonItems

  -- Step 5: Generate and register structure/class field projection functions and `.to<Parent>` coercions
  for (iv, cv, sInfo, toParentDefs) in structToGenerate do
    let projFieldNames := sInfo.fields.map (·.projFnName)
    let projs := generateStructProjections iv cv projFieldNames sInfo.isClass
    modifyEnv fun env =>
      let env := projs.foldl (fun acc p => acc.addConst (.defnInfo p)) env
      let env := toParentDefs.foldl (fun acc tp => acc.addConst (.defnInfo tp)) env
      if sInfo.isClass then
        (sInfo.parents.zip toParentDefs).foldl (fun acc (pName, tpDef) =>
          if acc.classSet.contains pName then
            acc.addInstance { instName := tpDef.cnst.name, className := pName }
          else acc) env
      else env

  -- Step 6: Run `deriving` handlers (`Inhabited`, `BEq`, `DecidableEq`)
  for (decl, _, _, _, _) in headers do
    let stAfter ← get
    if let some (.inductInfo ival) := stAfter.env.find? decl.fullName then
      elabDerivingHandlers decl ival fuel

/-! ## Value Declaration SCC Elaboration (`def`, `abbrev`, `theorem`, `opaque`, `axiom`, `instance`) -/

/-- Elaborate a strongly connected component of value/axiom declarations. -/
def elabValueSCC (decls : Array ModuleDecl) (isRecursive : Bool := true) (fuel : Nat := 128) : IxElabM Unit := do
  -- Step 1: Elaborate each declaration's signature and pre-register a temporary header
  -- so recursive and mutually recursive references resolve during body elaboration.
  -- (For a single non-recursive non-axiom declaration, skip Step 1 to avoid elaborating the signature twice!)
  let mut sigInfos : Array (ModuleDecl × Array Ix.Name × Ix.Expr × Array Ixon.BinderContract × Ixon.ValueContract) := #[]

  for decl in decls do
    let cmd := decl.stx
    let vPrefNode := Syntax.getArg cmd 5
    let retContract := (decodeContractPrefix vPrefNode).toValueContract
    if !isRecursive && decls.size == 1 && Syntax.getKind cmd != SyntaxKind.axiomDecl then
      let initLvls := Array.mk (decl.univParams ++ decl.scope.levelNames).eraseDups
      sigInfos := sigInfos.push (decl, initLvls, Expr.mkProp, #[], retContract)
    else
      modify fun st => match st with | ⟨env, _, nextIdx, _, _⟩ => ⟨env, {}, nextIdx, [], #[]⟩
      let varGroups := decl.scope.varBinders.toList.map decodeBinderNode
      let rawParamGroups := (Syntax.getArgs (Syntax.getArg cmd 4)).toList.map decodeBinderNode
      let optTypeNode := Syntax.getArg cmd 6
      let ctx0 ← read
      let st0 ← get
      let autoGroups := collectAutoImplicitGroups decl.scope ctx0.modIdx st0.env varGroups rawParamGroups optTypeNode
      let paramGroups := varGroups ++ autoGroups ++ rawParamGroups

      let (lvlParams, fullType, bcs) ← withReader (fun ctx => { ctx with
          lctx := LocalContext.empty
          scope := decl.scope
          currDecl? := some decl.fullName
          univParams := decl.univParams }) do
        elabBinderGroups (fun s exp? => elabTerm fuel s exp?) paramGroups #[] fun paramFVars => do
          let retTy ←
            if Syntax.isNone optTypeNode || Syntax.isMissing optTypeNode then
              let u ← mkFreshLevelMVar
              mkFreshExprMVar (Expr.mkSort u)
            else
              let t ← elabTerm fuel optTypeNode none
              let _ ← ensureSortIfNotForall 32 t
              instantiateMVars 32 t
          let piTy ← mkForallFVars paramFVars retTy retContract
          let piTy ← instantiateMVars 32 piTy
          let ctxNow ← read
          let bcs : Array Ixon.BinderContract := Array.mk <| paramFVars.toList.filterMap fun fv =>
            (ctxNow.lctx.findFVar? fv).map (·.contract)
          let stNow ← get
          let lvls := Array.mk (decl.univParams ++ decl.scope.levelNames ++ stNow.autoBoundUnivs).eraseDups
          return (lvls, piTy, bcs)

      -- Pre-register temporary `.axiomInfo` header for recursive calls (or final `.axiomInfo` for `axiom`)
      let tempAx : Ix.AxiomVal := {
        cnst := { name := decl.fullName, levelParams := lvlParams, type := defaultUnassignedExprLevelMVars fullType }
        isUnsafe := false
      }
      modifyEnv (·.addConst (.axiomInfo tempAx))
      sigInfos := sigInfos.push (decl, lvlParams, fullType, bcs, retContract)

  -- Step 2: Elaborate bodies for all non-axiom declarations in the SCC
  let mut elabbedDefs : Array Ix.Def := #[]
  for (decl, initLvlParams, _, _, retContract) in sigInfos do
    let cmd := decl.stx
    let k := Syntax.getKind cmd
    let attrs := extractDeclAttributes (Syntax.getArg cmd 0)
    if attrs.contains (Name.simple "simp") then
      modifyEnv (·.addInstance { instName := decl.fullName, className := Name.mkStr2 "_Ix" "simpLemma" })
    if k == SyntaxKind.axiomDecl then
      -- Already registered as `.axiomInfo` in Step 1!
      pure ()
    else
      modify fun st => match st with | ⟨env, _, nextIdx, _, _⟩ => ⟨env, {}, nextIdx, initLvlParams.toList, #[]⟩
      let varGroups := decl.scope.varBinders.toList.map decodeBinderNode
      let rawParamBinders := (Syntax.getArgs (Syntax.getArg cmd 4)).toList.map decodeBinderNode
      let optTypeNode := Syntax.getArg cmd 6
      let ctx0 ← read
      let st0 ← get
      let autoGroups := collectAutoImplicitGroups decl.scope ctx0.modIdx st0.env varGroups rawParamBinders optTypeNode
      let paramGroups := varGroups ++ autoGroups ++ rawParamBinders

      let (finalLvls, finalType, finalVal, finalBcs, finalLcs) ← withReader (fun ctx => { ctx with
          lctx := LocalContext.empty
          scope := decl.scope
          currDecl? := some decl.fullName
          univParams := initLvlParams.toList }) do
        elabBinderGroups (fun s exp? => elabTerm fuel s exp?) paramGroups #[] fun paramFVars => do
          let expRetTy? ←
            if Syntax.isNone optTypeNode || Syntax.isMissing optTypeNode then
              pure none
            else
              let t ← elabTerm fuel optTypeNode none
              let _ ← ensureSortIfNotForall 32 t
              let tInst ← instantiateMVars 32 t
              pure (some tInst)

          -- Determine body syntax:
          -- - `instance ... where field := val ...` -> desugar to `structInst`
          -- - Pattern-matching `def f (x : A) : B | pat => rhs ...` -> desugar to `match` on last binder (or synthesize fresh binder)
          -- - Standard `:= body`
          let (bodyExpr, bodyRetTy, extraFVars) ←
            if k == SyntaxKind.instanceDecl && Syntax.getAtomVal (Syntax.getArg cmd 7) == "where" then
              let fieldAssigns := Syntax.getArgs (Syntax.getArg cmd 8)
              -- Desugar any binder arguments on `field x y := rhs` into `field := fun x y => rhs`
              let normAssigns := fieldAssigns.map fun fa =>
                let fId := Syntax.getArg fa 0
                let fBinders := Syntax.getArg fa 1
                let fRhs := Syntax.getArg fa 3
                let rhsTerm :=
                  if (Syntax.getArgs fBinders).isEmpty then fRhs
                  else Syntax.mkNode SyntaxKind.funTerm #[Syntax.mkSimpleAtom "fun", fBinders, Syntax.mkSimpleAtom "=>", fRhs]
                Syntax.mkNode SyntaxKind.structFieldAssign #[fId, Syntax.mkSimpleAtom ":=", rhsTerm]
              let structLit := Syntax.mkNode SyntaxKind.structInst
                #[Syntax.mkSimpleAtom "{", Syntax.mkNullNode #[], Syntax.mkNullNode normAssigns, Syntax.mkSimpleAtom "}"]
              let val ← elabTerm fuel structLit expRetTy?
              let rTy ← match expRetTy? with | some t => pure t | none => inferType fuel val
              pure (val, rTy, #[])
            else if Syntax.getNumArgs cmd == 8 && k != SyntaxKind.axiomDecl then
              -- Pattern-matching definition `def f ... | pat => rhs`
              let altsNode := Syntax.getArg cmd 7
              let ctxNow ← read
              let rec stxMentions (nm : Ix.Name) (fuelM : Nat) (s : Ix.Syntax) : Bool :=
                match fuelM with
                | 0 => false
                | f + 1 =>
                  match s with
                  | .ident _ _ id _ => id == nm
                  | .node _ _ as    => as.any (stxMentions nm f)
                  | _               => false
              let targetFvId? :=
                (paramFVars.find? fun fvId =>
                  match ctxNow.lctx.findFVar? fvId with
                  | some d => d.binderInfo == .default && !stxMentions d.userName 64 altsNode
                  | none   => false).orElse (fun _ => paramFVars.back?)
              match targetFvId? with
              | some lastFvId =>
                let lastName := match ctxNow.lctx.findFVar? lastFvId with
                  | some d => d.userName
                  | none   => Name.simple "x"
                let discrIdent := Syntax.mkSimpleIdent lastName
                let matchStx := Syntax.mkNode SyntaxKind.matchTerm
                  #[Syntax.mkSimpleAtom "match", Syntax.mkNullNode #[discrIdent],
                    Syntax.mkSimpleAtom "with", altsNode]
                let val ← elabTerm fuel matchStx expRetTy?
                let rTy ← match expRetTy? with | some t => pure t | none => inferType fuel val
                pure (val, rTy, #[])
              | none =>
                -- Pattern-matching `def f : A → B | pat => rhs` where the parameter is in `expRetTy?`
                match expRetTy? with
                | some rTy =>
                  let rTyW ← whnf fuel rTy
                  match stripMData rTyW with
                  | .forallE _ dom cod bi _ =>
                    let discrName := Name.simple "_x"
                    withLocalDecl discrName dom bi default fun fvId fvExpr => do
                      let codInst := instantiate1 cod fvExpr
                      let matchStx := Syntax.mkNode SyntaxKind.matchTerm
                        #[Syntax.mkSimpleAtom "match", Syntax.mkNullNode #[Syntax.mkSimpleIdent discrName],
                          Syntax.mkSimpleAtom "with", altsNode]
                      let val ← elabTerm fuel matchStx (some codInst)
                      let lamVal ← mkLambdaFVars #[fvId] val
                      let piTy ← mkForallFVars #[fvId] codInst
                      pure (lamVal, piTy, #[])
                  | _ => throwElabError "pattern-matching definition requires a parameter or function return type" (some cmd)
                | none => throwElabError "pattern-matching definition requires a parameter or type signature" (some cmd)
            else
              let bodyStx := Syntax.getArg cmd 8
              let val ← elabTerm fuel bodyStx expRetTy?
              let rTy ← match expRetTy? with | some t => pure t | none => inferType fuel val
              pure (val, rTy, #[])

          let allParamFVars := paramFVars ++ extraFVars
          let fullTy ← mkForallFVars allParamFVars bodyRetTy retContract
          let fullVal ← mkLambdaFVars allParamFVars bodyExpr
          let fullTy ← instantiateMVars 32 fullTy
          let fullVal ← instantiateMVars 32 fullVal
          let fullTy := defaultUnassignedExprLevelMVars fullTy
          let fullVal := defaultUnassignedExprLevelMVars fullVal
          let ctxNow ← read
          let bcs : Array Ixon.BinderContract := Array.mk <| allParamFVars.toList.filterMap fun fv =>
            (ctxNow.lctx.findFVar? fv).map (·.contract)
          let stNow ← get
          let lvls := Array.mk (decl.univParams ++ decl.scope.levelNames ++ stNow.autoBoundUnivs).eraseDups
          return (lvls, fullTy, fullVal, bcs, stNow.localLetContracts)

      -- If this is a single recursive definition, try lowering structural `casesOn` self-recursion to `recOn`
      let stNow ← get
      let finalVal :=
        if isRecursive && decls.size == 1 then tryLowerStructuralRecToRecOn stNow.env decl.fullName finalVal
        else finalVal

      modifyEnv (·.addContracts decl.fullName finalBcs retContract finalLcs)

      -- If `decl.kind == .inst` or `@[instance]`, register in `st.env.instances`
      if decl.kind == .inst || attrs.contains (Name.simple "instance") then
        let (_, _, retBody) := openForallTelescope (countForalls 64 finalType) finalType "inst" 0 #[] #[]
        let (headClass, _) := getAppFnArgs retBody
        if let .const className _ _ := headClass then
          modifyEnv (·.addInstance { instName := decl.fullName, className })

      let defKind : Ix.DefKind :=
        if decl.kind == .thm then .thm
        else if decl.kind == .opaqueDecl then .opaq
        else .defn
      let hints : Lean.ReducibilityHints :=
        if decl.kind == .abbrev || attrs.contains (Name.simple "reducible") || attrs.contains (Name.simple "inline") then .abbrev
        else if decl.kind == .thm || decl.kind == .opaqueDecl || attrs.contains (Name.simple "irreducible") then .opaque
        else .regular 1
      let dItem : Ix.Def := {
        name        := decl.fullName
        levelParams := finalLvls
        type        := finalType
        kind        := defKind
        value       := finalVal
        hints       := hints
        safety      := .safe
        all         := #[decl.fullName]
      }
      elabbedDefs := elabbedDefs.push dItem

  -- Step 3: Split into minimal post-elaboration SCCs and canonicalize mutual definition blocks!
  if !elabbedDefs.isEmpty then
    let stNow ← get
    let addrOf := defaultAddrOf stNow.env
    let canonSccs := canonicalizeElaboratedDefs addrOf elabbedDefs
    for sccDefs in canonSccs do
      for d in sccDefs do
        let ci : Ix.ConstantInfo := match d.kind with
          | .thm => .thmInfo {
              cnst := { name := d.name, levelParams := d.levelParams, type := d.type }
              value := d.value
              all := d.all
            }
          | .opaq => .opaqueInfo {
              cnst := { name := d.name, levelParams := d.levelParams, type := d.type }
              value := d.value
              isUnsafe := false
              all := d.all
            }
          | .defn => .defnInfo {
              cnst := { name := d.name, levelParams := d.levelParams, type := d.type }
              value := d.value
              hints := d.hints
              safety := .safe
              all := d.all
            }
        modifyEnv (·.addConst ci)

/-! ## Whole-Module Elaboration Entry Points -/

/-- Elaborate a `ModuleSchedule` (produced by Pass 1 + Pass 2 + Pass 3) into an `IxElabEnv`. -/
def elabModuleSchedule (sched : ModuleSchedule)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except ElabError IxElabEnv := do
  let baseEnv := initEnv.withImportMap (initEnv.importMap.merge sched.modIdx.importMap)
  let baseEnv := if seedPrelude then seedCorePreludeIfMissing baseEnv sched.modIdx else baseEnv
  baseEnv.bindEnv fun baseEnv' => do
    let initState : ElabState := { env := baseEnv' }
    let initCtx : ElabContext := { modIdx := sched.modIdx }
    let declList := sched.modIdx.decls.toList
    let act : IxElabM Unit := do
      for scc in sched.sccs.toList do
        let sccDecls := Array.mk (scc.declIdxs.toList.filterMap fun idx => Syntax.listGet? declList idx)
        if !sccDecls.isEmpty then
          let allInd := sccDecls.toList.all fun d => d.kind == .ind || d.kind == .struct || d.kind == .cls
          if allInd then
            elabInductiveSCC sccDecls
          else
            elabValueSCC sccDecls (scc.kind != .singleNonRec)
    let (_, finalState) ← IxElabM.run act initCtx initState
    return finalState.env

/-- Elaborate a parsed `Ix.Syntax` module AST (`SyntaxKind.moduleKind`) into an `IxElabEnv`. -/
def elabModuleSyntax (moduleStx : Ix.Syntax)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String IxElabEnv := do
  let modIdx ← buildModuleIndex moduleStx
  let baseEnv := if seedPrelude then seedCorePreludeIfMissing initEnv modIdx else initEnv
  baseEnv.bindEnv fun baseEnv' => do
    let sched ← scheduleModuleDecls modIdx
      (fun n => baseEnv'.contains n)
      (fun n => baseEnv'.isCtor n)
    match elabModuleSchedule sched baseEnv' false with
    | .ok env  => return env
    | .error e => throw (toString e)

/-- Parse and elaborate a `.ix` / `.lean` source string into a pure `IxElabEnv` (zero `IO`). -/
def elabSource (input : String) (fileName : String := "<input>")
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String IxElabEnv := do
  let (stx, _) ← parseModuleWithEnv input fileName
  elabModuleSyntax stx initEnv seedPrelude

end Ix.Frontend.Elab
