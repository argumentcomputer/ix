/-
  Kernel2 Primitive: Validation of primitive definitions, inductives, and quotient types.

  Adapted from Ix.Kernel.Primitive for Kernel2's TypecheckM σ m monad.
  All comparisons use isDefEq (not structural equality) so that .meta mode
  name/binder-info differences don't cause spurious failures.
-/
import Ix.Kernel2.TypecheckM

namespace Ix.Kernel2

/-! ## KernelOps2 — callback struct to access mutual-block functions -/

structure KernelOps2 (σ : Type) (m : Ix.Kernel.MetaMode) where
  isDefEq : KExpr m → KExpr m → TypecheckM σ m Bool
  whnf    : KExpr m → TypecheckM σ m (KExpr m)
  infer   : KExpr m → TypecheckM σ m (KTypedExpr m × KExpr m)
  isProp  : KExpr m → TypecheckM σ m Bool
  isSort  : KExpr m → TypecheckM σ m (KTypedExpr m × KLevel m)

/-! ## Expression builders -/

private def natConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.nat #[]
private def boolConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.bool #[]
private def trueConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.boolTrue #[]
private def falseConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.boolFalse #[]
private def zeroConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.natZero #[]
private def charConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.char #[]
private def stringConst (p : KPrimitives) : KExpr m := Ix.Kernel.Expr.mkConst p.string #[]
private def listCharConst (p : KPrimitives) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.list #[Ix.Kernel.Level.succ .zero]) (charConst p)

private def succApp (p : KPrimitives) (e : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natSucc #[]) e
private def predApp (p : KPrimitives) (e : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natPred #[]) e
private def addApp (p : KPrimitives) (a b : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natAdd #[]) a) b
private def subApp (p : KPrimitives) (a b : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natSub #[]) a) b
private def mulApp (p : KPrimitives) (a b : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natMul #[]) a) b
private def modApp (p : KPrimitives) (a b : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natMod #[]) a) b
private def divApp (p : KPrimitives) (a b : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.natDiv #[]) a) b

private def mkArrow (a b : KExpr m) : KExpr m := Ix.Kernel.Expr.mkForallE a (b.liftBVars 1)

private def natBinType (p : KPrimitives) : KExpr m :=
  mkArrow (natConst p) (mkArrow (natConst p) (natConst p))

private def natUnaryType (p : KPrimitives) : KExpr m :=
  mkArrow (natConst p) (natConst p)

private def natBinBoolType (p : KPrimitives) : KExpr m :=
  mkArrow (natConst p) (mkArrow (natConst p) (boolConst p))

private def defeq1 (ops : KernelOps2 σ m) (p : KPrimitives) (a b : KExpr m) : TypecheckM σ m Bool :=
  -- Wrap in lambda (not forallE) so bvar 0 is captured by the lambda binder.
  -- mkArrow used forallE + liftBVars which left bvars free; lambdas bind them directly.
  ops.isDefEq (Ix.Kernel.Expr.mkLam (natConst p) a) (Ix.Kernel.Expr.mkLam (natConst p) b)

private def defeq2 (ops : KernelOps2 σ m) (p : KPrimitives) (a b : KExpr m) : TypecheckM σ m Bool :=
  let nat := natConst p
  ops.isDefEq (Ix.Kernel.Expr.mkLam nat (Ix.Kernel.Expr.mkLam nat a))
              (Ix.Kernel.Expr.mkLam nat (Ix.Kernel.Expr.mkLam nat b))

private def resolved (addr : Address) : Bool := addr != default

/-! ## Primitive inductive validation -/

def checkPrimitiveInductive (ops : KernelOps2 σ m) (p : KPrimitives) (kenv : KEnv m)
    (addr : Address) : TypecheckM σ m Bool := do
  let ci ← derefConst addr
  let .inductInfo iv := ci | return false
  if iv.isUnsafe then return false
  if iv.numLevels != 0 then return false
  if iv.numParams != 0 then return false
  unless ← ops.isDefEq iv.type (Ix.Kernel.Expr.mkSort (Ix.Kernel.Level.succ .zero)) do return false
  if addr == p.bool then
    if iv.ctors.size != 2 then throw "Bool must have exactly 2 constructors"
    for ctorAddr in iv.ctors do
      let ctor ← derefConst ctorAddr
      unless ← ops.isDefEq ctor.type (boolConst p) do throw "Bool constructor has unexpected type"
    return true
  if addr == p.nat then
    if iv.ctors.size != 2 then throw "Nat must have exactly 2 constructors"
    for ctorAddr in iv.ctors do
      let ctor ← derefConst ctorAddr
      if ctorAddr == p.natZero then
        unless ← ops.isDefEq ctor.type (natConst p) do throw "Nat.zero has unexpected type"
      else if ctorAddr == p.natSucc then
        unless ← ops.isDefEq ctor.type (natUnaryType p) do throw "Nat.succ has unexpected type"
      else throw "unexpected Nat constructor"
    return true
  return false

/-! ## Primitive definition validation -/

def checkPrimitiveDef (ops : KernelOps2 σ m) (p : KPrimitives) (kenv : KEnv m) (addr : Address)
    : TypecheckM σ m Bool := do
  let ci ← derefConst addr
  let .defnInfo v := ci | return false
  let isPrimAddr := addr == p.natAdd || addr == p.natSub || addr == p.natMul ||
    addr == p.natPow || addr == p.natBeq || addr == p.natBle ||
    addr == p.natShiftLeft || addr == p.natShiftRight ||
    addr == p.natLand || addr == p.natLor || addr == p.natXor ||
    addr == p.natPred || addr == p.natBitwise ||
    addr == p.natMod || addr == p.natDiv || addr == p.natGcd ||
    addr == p.charMk ||
    (addr == p.stringOfList && p.stringOfList != p.stringMk)
  if !isPrimAddr then return false
  let fail {α : Type} (msg : String := "invalid form for primitive def") : TypecheckM σ m α :=
    throw msg
  let nat : KExpr m := natConst p
  let tru : KExpr m := trueConst p
  let fal : KExpr m := falseConst p
  let zero : KExpr m := zeroConst p
  let succ : KExpr m → KExpr m := succApp p
  let pred : KExpr m → KExpr m := predApp p
  let add : KExpr m → KExpr m → KExpr m := addApp p
  let _sub : KExpr m → KExpr m → KExpr m := subApp p
  let mul : KExpr m → KExpr m → KExpr m := mulApp p
  let _mod' : KExpr m → KExpr m → KExpr m := modApp p
  let div' : KExpr m → KExpr m → KExpr m := divApp p
  let one : KExpr m := succ zero
  let two : KExpr m := succ one
  let x : KExpr m := .mkBVar 0
  let y : KExpr m := .mkBVar 1

  if addr == p.natAdd then
    if !kenv.contains p.nat || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let addV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← defeq1 ops p (addV x zero) x do fail
    unless ← defeq2 ops p (addV y (succ x)) (succ (addV y x)) do fail
    return true

  if addr == p.natPred then
    if !kenv.contains p.nat || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natUnaryType p) do fail
    let predV := fun a => Ix.Kernel.Expr.mkApp v.value a
    unless ← ops.isDefEq (predV zero) zero do fail
    unless ← defeq1 ops p (predV (succ x)) x do fail
    return true

  if addr == p.natSub then
    if !kenv.contains p.natPred || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let subV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← defeq1 ops p (subV x zero) x do fail
    unless ← defeq2 ops p (subV y (succ x)) (pred (subV y x)) do fail
    return true

  if addr == p.natMul then
    if !kenv.contains p.natAdd || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let mulV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← defeq1 ops p (mulV x zero) zero do fail
    unless ← defeq2 ops p (mulV y (succ x)) (add (mulV y x) y) do fail
    return true

  if addr == p.natPow then
    if !kenv.contains p.natMul || v.numLevels != 0 then fail "natPow: missing natMul or bad numLevels"
    unless ← ops.isDefEq v.type (natBinType p) do fail "natPow: type mismatch"
    let powV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← defeq1 ops p (powV x zero) one do fail "natPow: pow x 0 ≠ 1"
    unless ← defeq2 ops p (powV y (succ x)) (mul (powV y x) y) do fail "natPow: step check failed"
    return true

  if addr == p.natBeq then
    if !kenv.contains p.nat || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinBoolType p) do fail
    let beqV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← ops.isDefEq (beqV zero zero) tru do fail
    unless ← defeq1 ops p (beqV zero (succ x)) fal do fail
    unless ← defeq1 ops p (beqV (succ x) zero) fal do fail
    unless ← defeq2 ops p (beqV (succ y) (succ x)) (beqV y x) do fail
    return true

  if addr == p.natBle then
    if !kenv.contains p.nat || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinBoolType p) do fail
    let bleV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← ops.isDefEq (bleV zero zero) tru do fail
    unless ← defeq1 ops p (bleV zero (succ x)) tru do fail
    unless ← defeq1 ops p (bleV (succ x) zero) fal do fail
    unless ← defeq2 ops p (bleV (succ y) (succ x)) (bleV y x) do fail
    return true

  if addr == p.natShiftLeft then
    if !kenv.contains p.natMul || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let shlV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← defeq1 ops p (shlV x zero) x do fail
    unless ← defeq2 ops p (shlV x (succ y)) (shlV (mul two x) y) do fail
    return true

  if addr == p.natShiftRight then
    if !kenv.contains p.natDiv || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let shrV := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp v.value a) b
    unless ← defeq1 ops p (shrV x zero) x do fail
    unless ← defeq2 ops p (shrV x (succ y)) (div' (shrV x y) two) do fail
    return true

  if addr == p.natLand then
    if !kenv.contains p.natBitwise || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.land value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise do fail "Nat.land value head must be Nat.bitwise"
    let andF := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp f a) b
    unless ← defeq1 ops p (andF fal x) fal do fail
    unless ← defeq1 ops p (andF tru x) x do fail
    return true

  if addr == p.natLor then
    if !kenv.contains p.natBitwise || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.lor value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise do fail "Nat.lor value head must be Nat.bitwise"
    let orF := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp f a) b
    unless ← defeq1 ops p (orF fal x) x do fail
    unless ← defeq1 ops p (orF tru x) tru do fail
    return true

  if addr == p.natXor then
    if !kenv.contains p.natBitwise || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.xor value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise do fail "Nat.xor value head must be Nat.bitwise"
    let xorF := fun a b => Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp f a) b
    unless ← ops.isDefEq (xorF fal fal) fal do fail
    unless ← ops.isDefEq (xorF tru fal) tru do fail
    unless ← ops.isDefEq (xorF fal tru) tru do fail
    unless ← ops.isDefEq (xorF tru tru) fal do fail
    return true

  if addr == p.natMod then
    if !kenv.contains p.natSub || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    return true

  if addr == p.natDiv then
    if !kenv.contains p.natSub || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    return true

  if addr == p.natGcd then
    if !kenv.contains p.natMod || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    return true

  if addr == p.charMk then
    if !kenv.contains p.nat || v.numLevels != 0 then fail
    let expectedType := mkArrow nat (charConst p)
    unless ← ops.isDefEq v.type expectedType do fail
    return true

  if addr == p.stringOfList then
    if v.numLevels != 0 then fail
    let listChar := listCharConst p
    let expectedType := mkArrow listChar (stringConst p)
    unless ← ops.isDefEq v.type expectedType do fail
    let nilChar := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.listNil #[Ix.Kernel.Level.succ .zero]) (charConst p)
    let (_, nilType) ← ops.infer nilChar
    unless ← ops.isDefEq nilType listChar do fail
    let consChar := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.listCons #[Ix.Kernel.Level.succ .zero]) (charConst p)
    let (_, consType) ← ops.infer consChar
    let expectedConsType := mkArrow (charConst p) (mkArrow listChar listChar)
    unless ← ops.isDefEq consType expectedConsType do fail
    return true

  return false

/-! ## Quotient validation -/

def checkEqType (ops : KernelOps2 σ m) (p : KPrimitives) : TypecheckM σ m Unit := do
  if !(← read).kenv.contains p.eq then throw "Eq type not found in environment"
  let ci ← derefConst p.eq
  let .inductInfo iv := ci | throw "Eq is not an inductive"
  if iv.numLevels != 1 then throw "Eq must have exactly 1 universe parameter"
  if iv.ctors.size != 1 then throw "Eq must have exactly 1 constructor"
  let u : KLevel m := .param 0 default
  let sortU : KExpr m := Ix.Kernel.Expr.mkSort u
  let expectedEqType : KExpr m :=
    Ix.Kernel.Expr.mkForallE sortU
      (Ix.Kernel.Expr.mkForallE (.mkBVar 0)
        (Ix.Kernel.Expr.mkForallE (.mkBVar 1)
          Ix.Kernel.Expr.prop))
  unless ← ops.isDefEq ci.type expectedEqType do throw "Eq has unexpected type"
  if !(← read).kenv.contains p.eqRefl then throw "Eq.refl not found in environment"
  let refl ← derefConst p.eqRefl
  if refl.numLevels != 1 then throw "Eq.refl must have exactly 1 universe parameter"
  let eqConst : KExpr m := Ix.Kernel.Expr.mkConst p.eq #[u]
  let expectedReflType : KExpr m :=
    Ix.Kernel.Expr.mkForallE sortU
      (Ix.Kernel.Expr.mkForallE (.mkBVar 0)
        (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp eqConst (.mkBVar 1)) (.mkBVar 0)) (.mkBVar 0)))
  unless ← ops.isDefEq refl.type expectedReflType do throw "Eq.refl has unexpected type"

def checkQuotTypes (ops : KernelOps2 σ m) (p : KPrimitives) : TypecheckM σ m Unit := do
  let u : KLevel m := .param 0 default
  let sortU : KExpr m := Ix.Kernel.Expr.mkSort u
  let relType (depth : Nat) : KExpr m :=
    Ix.Kernel.Expr.mkForallE (.mkBVar depth)
      (Ix.Kernel.Expr.mkForallE (.mkBVar (depth + 1))
        Ix.Kernel.Expr.prop)

  if resolved p.quotType then
    let ci ← derefConst p.quotType
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallE sortU
        (Ix.Kernel.Expr.mkForallE (relType 0)
          (Ix.Kernel.Expr.mkSort u))
    unless ← ops.isDefEq ci.type expectedType do throw "Quot type signature mismatch"

  if resolved p.quotCtor then
    let ci ← derefConst p.quotCtor
    let quotApp : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 2)) (.mkBVar 1)
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallE sortU
        (Ix.Kernel.Expr.mkForallE (relType 0)
          (Ix.Kernel.Expr.mkForallE (.mkBVar 1)
            quotApp))
    unless ← ops.isDefEq ci.type expectedType do throw "Quot.mk type signature mismatch"

  if resolved p.quotLift then
    let ci ← derefConst p.quotLift
    if ci.numLevels != 2 then throw "Quot.lift must have exactly 2 universe parameters"
    let v : KLevel m := .param 1 default
    let sortV : KExpr m := Ix.Kernel.Expr.mkSort v
    let fType : KExpr m := Ix.Kernel.Expr.mkForallE (.mkBVar 2) (.mkBVar 1)
    let hType : KExpr m :=
      Ix.Kernel.Expr.mkForallE (.mkBVar 3)
        (Ix.Kernel.Expr.mkForallE (.mkBVar 4)
          (Ix.Kernel.Expr.mkForallE
            (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (.mkBVar 4) (.mkBVar 1)) (.mkBVar 0))
            (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.eq #[v]) (.mkBVar 4))
              (Ix.Kernel.Expr.mkApp (.mkBVar 3) (.mkBVar 2)))
              (Ix.Kernel.Expr.mkApp (.mkBVar 3) (.mkBVar 1)))))
    let qType : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 4)) (.mkBVar 3)
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallE sortU
        (Ix.Kernel.Expr.mkForallE (relType 0)
          (Ix.Kernel.Expr.mkForallE sortV
            (Ix.Kernel.Expr.mkForallE fType
              (Ix.Kernel.Expr.mkForallE hType
                (Ix.Kernel.Expr.mkForallE qType
                  (.mkBVar 3))))))
    unless ← ops.isDefEq ci.type expectedType do throw "Quot.lift type signature mismatch"

  if resolved p.quotInd then
    let ci ← derefConst p.quotInd
    if ci.numLevels != 1 then throw "Quot.ind must have exactly 1 universe parameter"
    let quotAtDepth2 : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 1)) (.mkBVar 0)
    let betaType : KExpr m := Ix.Kernel.Expr.mkForallE quotAtDepth2 Ix.Kernel.Expr.prop
    let quotMkA : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotCtor #[u]) (.mkBVar 3)) (.mkBVar 2)) (.mkBVar 0)
    let hType : KExpr m := Ix.Kernel.Expr.mkForallE (.mkBVar 2) (Ix.Kernel.Expr.mkApp (.mkBVar 1) quotMkA)
    let qType : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 3)) (.mkBVar 2)
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallE sortU
        (Ix.Kernel.Expr.mkForallE (relType 0)
          (Ix.Kernel.Expr.mkForallE betaType
            (Ix.Kernel.Expr.mkForallE hType
              (Ix.Kernel.Expr.mkForallE qType
                (Ix.Kernel.Expr.mkApp (.mkBVar 2) (.mkBVar 0))))))
    unless ← ops.isDefEq ci.type expectedType do throw "Quot.ind type signature mismatch"

/-! ## Top-level dispatch -/

def checkPrimitive (ops : KernelOps2 σ m) (p : KPrimitives) (kenv : KEnv m) (addr : Address)
    : TypecheckM σ m Bool := do
  if addr == p.bool || addr == p.nat then
    return ← checkPrimitiveInductive ops p kenv addr
  checkPrimitiveDef ops p kenv addr

end Ix.Kernel2
