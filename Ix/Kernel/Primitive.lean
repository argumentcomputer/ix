/-
  Kernel2 Primitive: Validation of primitive definitions, inductives, and quotient types.

  Adapted from Ix.Kernel.Primitive for Kernel2's TypecheckM σ m monad.
  All comparisons use isDefEq (not structural equality) so that .meta mode
  name/binder-info differences don't cause spurious failures.
-/
import Ix.Kernel.TypecheckM

namespace Ix.Kernel

/-! ## KernelOps2 — callback struct to access mutual-block functions -/

structure KernelOps2 (σ : Type) (m : Ix.Kernel.MetaMode) where
  isDefEq : KExpr m → KExpr m → TypecheckM σ m Bool
  whnf    : KExpr m → TypecheckM σ m (KExpr m)
  infer   : KExpr m → TypecheckM σ m (KTypedExpr m × KExpr m)
  isProp  : KExpr m → TypecheckM σ m Bool
  isSort  : KExpr m → TypecheckM σ m (KTypedExpr m × KLevel m)

/-! ## Expression builders -/

@[inline] private def primConst (id : KMetaId m) : KExpr m := Ix.Kernel.Expr.mkConst id #[]
@[inline] private def primUnApp (id : KMetaId m) (a : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (primConst id) a
@[inline] private def primBinApp (id : KMetaId m) (a b : KExpr m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (primUnApp id a) b

private def natConst (p : KPrimitives m) : KExpr m := primConst p.nat
private def boolConst (p : KPrimitives m) : KExpr m := primConst p.bool
private def trueConst (p : KPrimitives m) : KExpr m := primConst p.boolTrue
private def falseConst (p : KPrimitives m) : KExpr m := primConst p.boolFalse
private def zeroConst (p : KPrimitives m) : KExpr m := primConst p.natZero
private def charConst (p : KPrimitives m) : KExpr m := primConst p.char
private def stringConst (p : KPrimitives m) : KExpr m := primConst p.string
private def listCharConst (p : KPrimitives m) : KExpr m :=
  Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.list #[.zero]) (charConst p)

private def succApp (p : KPrimitives m) (e : KExpr m) : KExpr m := primUnApp p.natSucc e
private def predApp (p : KPrimitives m) (e : KExpr m) : KExpr m := primUnApp p.natPred e
private def addApp (p : KPrimitives m) (a b : KExpr m) : KExpr m := primBinApp p.natAdd a b
private def subApp (p : KPrimitives m) (a b : KExpr m) : KExpr m := primBinApp p.natSub a b
private def mulApp (p : KPrimitives m) (a b : KExpr m) : KExpr m := primBinApp p.natMul a b
private def modApp (p : KPrimitives m) (a b : KExpr m) : KExpr m := primBinApp p.natMod a b
private def divApp (p : KPrimitives m) (a b : KExpr m) : KExpr m := primBinApp p.natDiv a b

private def mkArrow (a b : KExpr m) : KExpr m := Ix.Kernel.Expr.mkForallE a (b.liftBVars 1)

private def natBinType (p : KPrimitives m) : KExpr m :=
  mkArrow (natConst p) (mkArrow (natConst p) (natConst p))

private def natUnaryType (p : KPrimitives m) : KExpr m :=
  mkArrow (natConst p) (natConst p)

private def natBinBoolType (p : KPrimitives m) : KExpr m :=
  mkArrow (natConst p) (mkArrow (natConst p) (boolConst p))

private def defeq1 (ops : KernelOps2 σ m) (p : KPrimitives m) (a b : KExpr m) : TypecheckM σ m Bool :=
  -- Wrap in lambda (not forallE) so bvar 0 is captured by the lambda binder.
  -- mkArrow used forallE + liftBVars which left bvars free; lambdas bind them directly.
  ops.isDefEq (Ix.Kernel.Expr.mkLam (natConst p) a) (Ix.Kernel.Expr.mkLam (natConst p) b)

private def defeq2 (ops : KernelOps2 σ m) (p : KPrimitives m) (a b : KExpr m) : TypecheckM σ m Bool :=
  let nat := natConst p
  ops.isDefEq (Ix.Kernel.Expr.mkLam nat (Ix.Kernel.Expr.mkLam nat a))
              (Ix.Kernel.Expr.mkLam nat (Ix.Kernel.Expr.mkLam nat b))

private def resolved (mid : MetaId m) : Bool := mid.addr != default

/-! ## Primitive inductive validation -/

def checkPrimitiveInductive (ops : KernelOps2 σ m) (p : KPrimitives m)
    (addr : Address) : TypecheckM σ m Bool := do
  let ci ← derefConstByAddr addr
  let .inductInfo iv := ci | return false
  if iv.isUnsafe then return false
  if iv.numLevels != 0 then return false
  if iv.numParams != 0 then return false
  unless ← ops.isDefEq iv.type (Ix.Kernel.Expr.mkSort (Ix.Kernel.Level.succ .zero)) do return false
  if addr == p.bool.addr then
    if iv.ctors.size != 2 then throw "Bool must have exactly 2 constructors"
    for ctorId in iv.ctors do
      let ctor ← derefConst ctorId
      unless ← ops.isDefEq ctor.type (boolConst p) do throw "Bool constructor has unexpected type"
    return true
  if addr == p.nat.addr then
    if iv.ctors.size != 2 then throw "Nat must have exactly 2 constructors"
    for ctorId in iv.ctors do
      let ctor ← derefConst ctorId
      if ctorId.addr == p.natZero.addr then
        unless ← ops.isDefEq ctor.type (natConst p) do throw "Nat.zero has unexpected type"
      else if ctorId.addr == p.natSucc.addr then
        unless ← ops.isDefEq ctor.type (natUnaryType p) do throw "Nat.succ has unexpected type"
      else throw "unexpected Nat constructor"
    return true
  return false

/-! ## Primitive definition validation -/

def checkPrimitiveDef (ops : KernelOps2 σ m) (p : KPrimitives m) (kenv : KEnv m) (addr : Address)
    : TypecheckM σ m Bool := do
  let ci ← derefConstByAddr addr
  let .defnInfo v := ci | return false
  let isPrimAddr := addr == p.natAdd.addr || addr == p.natSub.addr || addr == p.natMul.addr ||
    addr == p.natPow.addr || addr == p.natBeq.addr || addr == p.natBle.addr ||
    addr == p.natShiftLeft.addr || addr == p.natShiftRight.addr ||
    addr == p.natLand.addr || addr == p.natLor.addr || addr == p.natXor.addr ||
    addr == p.natPred.addr || addr == p.natBitwise.addr ||
    addr == p.natMod.addr || addr == p.natDiv.addr || addr == p.natGcd.addr ||
    addr == p.charMk.addr ||
    (addr == p.stringOfList.addr && p.stringOfList.addr != p.stringMk.addr)
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
  let mul : KExpr m → KExpr m → KExpr m := mulApp p
  let div' : KExpr m → KExpr m → KExpr m := divApp p
  let one : KExpr m := succ zero
  let two : KExpr m := succ one
  let x : KExpr m := .mkBVar 0
  let y : KExpr m := .mkBVar 1

  -- Use the constant (not v.value) so tryReduceNatVal step-case fires
  let primId : KMetaId m := MetaId.mk m addr ci.cv.name
  let prim : KExpr m := .mkConst primId #[]
  -- Shared closures for applying the primitive as a binary/unary operator
  let binV (a b : KExpr m) : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp prim a) b
  let unV (a : KExpr m) : KExpr m := Ix.Kernel.Expr.mkApp prim a
  -- Shared preamble: check dependency exists and numLevels == 0
  let guardDep (dep : Address) : TypecheckM σ m Unit := do
    if !kenv.containsAddr dep || v.numLevels != 0 then fail
  let guardDeps (deps : Array Address) : TypecheckM σ m Unit := do
    for dep in deps do
      if !kenv.containsAddr dep then fail
    if v.numLevels != 0 then fail

  if addr == p.natAdd.addr then
    guardDep p.nat.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    unless ← defeq1 ops p (binV x zero) x do fail
    unless ← defeq2 ops p (binV y (succ x)) (succ (binV y x)) do fail
    return true

  if addr == p.natPred.addr then
    guardDep p.nat.addr
    unless ← ops.isDefEq v.type (natUnaryType p) do fail
    unless ← ops.isDefEq (unV zero) zero do fail
    unless ← defeq1 ops p (unV (succ x)) x do fail
    return true

  if addr == p.natSub.addr then
    guardDep p.natPred.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    unless ← defeq1 ops p (binV x zero) x do fail
    unless ← defeq2 ops p (binV y (succ x)) (pred (binV y x)) do fail
    return true

  if addr == p.natMul.addr then
    guardDep p.natAdd.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    unless ← defeq1 ops p (binV x zero) zero do fail
    unless ← defeq2 ops p (binV y (succ x)) (add (binV y x) y) do fail
    return true

  if addr == p.natPow.addr then
    guardDep p.natMul.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail "natPow: type mismatch"
    unless ← defeq1 ops p (binV x zero) one do fail "natPow: pow x 0 ≠ 1"
    unless ← defeq2 ops p (binV y (succ x)) (mul (binV y x) y) do fail "natPow: step check failed"
    return true

  if addr == p.natBeq.addr then
    guardDeps #[p.nat.addr, p.bool.addr]
    unless ← ops.isDefEq v.type (natBinBoolType p) do fail
    unless ← ops.isDefEq (binV zero zero) tru do fail
    unless ← defeq1 ops p (binV zero (succ x)) fal do fail
    unless ← defeq1 ops p (binV (succ x) zero) fal do fail
    unless ← defeq2 ops p (binV (succ y) (succ x)) (binV y x) do fail
    return true

  if addr == p.natBle.addr then
    guardDeps #[p.nat.addr, p.bool.addr]
    unless ← ops.isDefEq v.type (natBinBoolType p) do fail
    unless ← ops.isDefEq (binV zero zero) tru do fail
    unless ← defeq1 ops p (binV zero (succ x)) tru do fail
    unless ← defeq1 ops p (binV (succ x) zero) fal do fail
    unless ← defeq2 ops p (binV (succ y) (succ x)) (binV y x) do fail
    return true

  if addr == p.natShiftLeft.addr then
    guardDep p.natMul.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    unless ← defeq1 ops p (binV x zero) x do fail
    unless ← defeq2 ops p (binV x (succ y)) (binV (mul two x) y) do fail
    return true

  if addr == p.natShiftRight.addr then
    guardDep p.natDiv.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    unless ← defeq1 ops p (binV x zero) x do fail
    unless ← defeq2 ops p (binV x (succ y)) (div' (binV x y) two) do fail
    return true

  if addr == p.natLand.addr then
    guardDep p.natBitwise.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.land value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise.addr do fail "Nat.land value head must be Nat.bitwise"
    let bwF (a b : KExpr m) := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp f a) b
    unless ← defeq1 ops p (bwF fal x) fal do fail
    unless ← defeq1 ops p (bwF tru x) x do fail
    return true

  if addr == p.natLor.addr then
    guardDep p.natBitwise.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.lor value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise.addr do fail "Nat.lor value head must be Nat.bitwise"
    let bwF (a b : KExpr m) := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp f a) b
    unless ← defeq1 ops p (bwF fal x) x do fail
    unless ← defeq1 ops p (bwF tru x) tru do fail
    return true

  if addr == p.natXor.addr then
    guardDep p.natBitwise.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.xor value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise.addr do fail "Nat.xor value head must be Nat.bitwise"
    let bwF (a b : KExpr m) := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp f a) b
    unless ← ops.isDefEq (bwF fal fal) fal do fail
    unless ← ops.isDefEq (bwF tru fal) tru do fail
    unless ← ops.isDefEq (bwF fal tru) tru do fail
    unless ← ops.isDefEq (bwF tru tru) fal do fail
    return true

  if addr == p.natMod.addr then
    guardDeps #[p.natSub.addr, p.bool.addr]
    unless ← ops.isDefEq v.type (natBinType p) do fail
    -- Spot-check: mod x 0 = x, mod 0 3 = 0
    unless ← defeq1 ops p (binV x zero) x do fail "natMod: mod x 0 ≠ x"
    unless ← ops.isDefEq (binV zero (.lit (.natVal 3))) zero do fail "natMod: mod 0 3 ≠ 0"
    return true

  if addr == p.natDiv.addr then
    guardDeps #[p.natSub.addr, p.bool.addr]
    unless ← ops.isDefEq v.type (natBinType p) do fail
    -- Spot-check: div x 0 = 0, div 0 3 = 0
    unless ← defeq1 ops p (binV x zero) zero do fail "natDiv: div x 0 ≠ 0"
    unless ← ops.isDefEq (binV zero (.lit (.natVal 3))) zero do fail "natDiv: div 0 3 ≠ 0"
    return true

  if addr == p.natGcd.addr then
    guardDep p.natMod.addr
    unless ← ops.isDefEq v.type (natBinType p) do fail
    -- Spot-check: gcd 0 x = x, gcd x 0 = x
    unless ← defeq1 ops p (binV zero x) x do fail "natGcd: gcd 0 x ≠ x"
    unless ← defeq1 ops p (binV x zero) x do fail "natGcd: gcd x 0 ≠ x"
    return true

  if addr == p.charMk.addr then
    guardDep p.nat.addr
    let expectedType := mkArrow nat (charConst p)
    unless ← ops.isDefEq v.type expectedType do fail
    return true

  if addr == p.stringOfList.addr then
    if v.numLevels != 0 then fail
    let listChar := listCharConst p
    let expectedType := mkArrow listChar (stringConst p)
    unless ← ops.isDefEq v.type expectedType do fail
    let nilChar := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.listNil #[.zero]) (charConst p)
    let (_, nilType) ← ops.infer nilChar
    unless ← ops.isDefEq nilType listChar do fail
    let consChar := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.listCons #[.zero]) (charConst p)
    let (_, consType) ← ops.infer consChar
    let expectedConsType := mkArrow (charConst p) (mkArrow listChar listChar)
    unless ← ops.isDefEq consType expectedConsType do fail
    return true

  return false

/-! ## Quotient validation -/

def checkEqType (ops : KernelOps2 σ m) (p : KPrimitives m) : TypecheckM σ m Unit := do
  if !(← read).kenv.containsAddr p.eq.addr then throw "Eq type not found in environment"
  let ci ← derefConstByAddr p.eq.addr
  let .inductInfo iv := ci | throw "Eq is not an inductive"
  if iv.numLevels != 1 then throw "Eq must have exactly 1 universe parameter"
  if iv.ctors.size != 1 then throw "Eq must have exactly 1 constructor"
  let u : KLevel m := .param 0 default
  let sortU : KExpr m := Ix.Kernel.Expr.mkSort u
  let expectedEqType : KExpr m :=
    Ix.Kernel.Expr.mkForallChain #[sortU, .mkBVar 0, .mkBVar 1] Ix.Kernel.Expr.prop
  unless ← ops.isDefEq ci.type expectedEqType do throw "Eq has unexpected type"
  if !(← read).kenv.containsAddr p.eqRefl.addr then throw "Eq.refl not found in environment"
  let refl ← derefConstByAddr p.eqRefl.addr
  if refl.numLevels != 1 then throw "Eq.refl must have exactly 1 universe parameter"
  let eqConst : KExpr m := Ix.Kernel.Expr.mkConst p.eq #[u]
  let expectedReflType : KExpr m :=
    Ix.Kernel.Expr.mkForallChain #[sortU, .mkBVar 0]
      (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp eqConst (.mkBVar 1)) (.mkBVar 0)) (.mkBVar 0))
  unless ← ops.isDefEq refl.type expectedReflType do throw "Eq.refl has unexpected type"

def checkQuotTypes (ops : KernelOps2 σ m) (p : KPrimitives m) : TypecheckM σ m Unit := do
  let u : KLevel m := .param 0 default
  let sortU : KExpr m := Ix.Kernel.Expr.mkSort u
  let relType (depth : Nat) : KExpr m :=
    Ix.Kernel.Expr.mkForallChain #[.mkBVar depth, .mkBVar (depth + 1)] Ix.Kernel.Expr.prop

  if resolved p.quotType then
    let ci ← derefConstByAddr p.quotType.addr
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallChain #[sortU, relType 0] (Ix.Kernel.Expr.mkSort u)
    unless ← ops.isDefEq ci.type expectedType do throw "Quot type signature mismatch"

  if resolved p.quotCtor then
    let ci ← derefConstByAddr p.quotCtor.addr
    let quotApp : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 2)) (.mkBVar 1)
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallChain #[sortU, relType 0, .mkBVar 1] quotApp
    unless ← ops.isDefEq ci.type expectedType do throw "Quot.mk type signature mismatch"

  if resolved p.quotLift then
    let ci ← derefConstByAddr p.quotLift.addr
    if ci.numLevels != 2 then throw "Quot.lift must have exactly 2 universe parameters"
    let v : KLevel m := .param 1 default
    let sortV : KExpr m := Ix.Kernel.Expr.mkSort v
    let fType : KExpr m := Ix.Kernel.Expr.mkForallE (.mkBVar 2) (.mkBVar 1)
    let hType : KExpr m :=
      Ix.Kernel.Expr.mkForallChain #[.mkBVar 3, .mkBVar 4,
        Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (.mkBVar 4) (.mkBVar 1)) (.mkBVar 0)]
        (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.eq #[v]) (.mkBVar 4))
          (Ix.Kernel.Expr.mkApp (.mkBVar 3) (.mkBVar 2)))
          (Ix.Kernel.Expr.mkApp (.mkBVar 3) (.mkBVar 1)))
    let qType : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 4)) (.mkBVar 3)
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallChain #[sortU, relType 0, sortV, fType, hType, qType] (.mkBVar 3)
    unless ← ops.isDefEq ci.type expectedType do throw "Quot.lift type signature mismatch"

  if resolved p.quotInd then
    let ci ← derefConstByAddr p.quotInd.addr
    if ci.numLevels != 1 then throw "Quot.ind must have exactly 1 universe parameter"
    let quotAtDepth2 : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 1)) (.mkBVar 0)
    let betaType : KExpr m := Ix.Kernel.Expr.mkForallE quotAtDepth2 Ix.Kernel.Expr.prop
    let quotMkA : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotCtor #[u]) (.mkBVar 3)) (.mkBVar 2)) (.mkBVar 0)
    let hType : KExpr m := Ix.Kernel.Expr.mkForallE (.mkBVar 2) (Ix.Kernel.Expr.mkApp (.mkBVar 1) quotMkA)
    let qType : KExpr m := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst p.quotType #[u]) (.mkBVar 3)) (.mkBVar 2)
    let expectedType : KExpr m :=
      Ix.Kernel.Expr.mkForallChain #[sortU, relType 0, betaType, hType, qType]
        (Ix.Kernel.Expr.mkApp (.mkBVar 2) (.mkBVar 0))
    unless ← ops.isDefEq ci.type expectedType do throw "Quot.ind type signature mismatch"

/-! ## Top-level dispatch -/

def checkPrimitive (ops : KernelOps2 σ m) (p : KPrimitives m) (kenv : KEnv m) (addr : Address)
    : TypecheckM σ m Bool := do
  if addr == p.bool.addr || addr == p.nat.addr then
    return ← checkPrimitiveInductive ops p addr
  checkPrimitiveDef ops p kenv addr

end Ix.Kernel
