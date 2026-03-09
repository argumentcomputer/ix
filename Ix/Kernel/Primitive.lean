/-
  Kernel Primitive: Validation of primitive definitions, inductives, and quotient types.

  Translates lean4lean's Primitive.lean and Quot.lean checks to work with
  Ix's address-based, de Bruijn-indexed expressions. Called from the mutual
  block in Infer.lean via the KernelOps callback struct.

  All comparisons use isDefEq (not structural equality) so that .meta mode
  name/binder-info differences don't cause spurious failures.
-/
import Ix.Kernel.TypecheckM

namespace Ix.Kernel

/-! ## KernelOps — callback struct to access mutual-block functions -/

structure KernelOps (m : MetaMode) where
  isDefEq : Expr m → Expr m → TypecheckM m Bool
  whnf    : Expr m → TypecheckM m (Expr m)
  infer   : Expr m → TypecheckM m (TypedExpr m × Expr m)
  isProp  : Expr m → TypecheckM m Bool
  isSort  : Expr m → TypecheckM m (TypedExpr m × Level m)

/-! ## Expression builders -/

private def natConst (p : Primitives) : Expr m := Expr.mkConst p.nat #[]
private def boolConst (p : Primitives) : Expr m := Expr.mkConst p.bool #[]
private def trueConst (p : Primitives) : Expr m := Expr.mkConst p.boolTrue #[]
private def falseConst (p : Primitives) : Expr m := Expr.mkConst p.boolFalse #[]
private def zeroConst (p : Primitives) : Expr m := Expr.mkConst p.natZero #[]
private def charConst (p : Primitives) : Expr m := Expr.mkConst p.char #[]
private def stringConst (p : Primitives) : Expr m := Expr.mkConst p.string #[]
private def listCharConst (p : Primitives) : Expr m :=
  Expr.mkApp (Expr.mkConst p.list #[Level.succ .zero]) (charConst p)

private def succApp (p : Primitives) (e : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkConst p.natSucc #[]) e
private def predApp (p : Primitives) (e : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkConst p.natPred #[]) e
private def addApp (p : Primitives) (a b : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkApp (Expr.mkConst p.natAdd #[]) a) b
private def subApp (p : Primitives) (a b : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkApp (Expr.mkConst p.natSub #[]) a) b
private def mulApp (p : Primitives) (a b : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkApp (Expr.mkConst p.natMul #[]) a) b
private def modApp (p : Primitives) (a b : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkApp (Expr.mkConst p.natMod #[]) a) b
private def divApp (p : Primitives) (a b : Expr m) : Expr m :=
  Expr.mkApp (Expr.mkApp (Expr.mkConst p.natDiv #[]) a) b

/-- Arrow type: `a → b` (non-dependent forall). -/
private def mkArrow (a b : Expr m) : Expr m := Expr.mkForallE a (b.liftBVars 1)

/-- `Nat → Nat → Nat` -/
private def natBinType (p : Primitives) : Expr m :=
  mkArrow (natConst p) (mkArrow (natConst p) (natConst p))

/-- `Nat → Nat` -/
private def natUnaryType (p : Primitives) : Expr m :=
  mkArrow (natConst p) (natConst p)

/-- `Nat → Nat → Bool` -/
private def natBinBoolType (p : Primitives) : Expr m :=
  mkArrow (natConst p) (mkArrow (natConst p) (boolConst p))

/-- Wrap both sides in `∀ (_ : Nat), _` so bvar 0 is well-typed as Nat. -/
private def defeq1 (ops : KernelOps m) (p : Primitives) (a b : Expr m) : TypecheckM m Bool :=
  ops.isDefEq (mkArrow (natConst p) a) (mkArrow (natConst p) b)

/-- Wrap both sides in `∀ (_ : Nat), ∀ (_ : Nat), _` for two free variables. -/
private def defeq2 (ops : KernelOps m) (p : Primitives) (a b : Expr m) : TypecheckM m Bool :=
  defeq1 ops p (mkArrow (natConst p) a) (mkArrow (natConst p) b)

/-- Check if an address is non-default (i.e., was actually resolved). -/
private def resolved (addr : Address) : Bool := addr != default

/-! ## Primitive inductive validation -/

/-- Check that Bool or Nat inductives have the expected form.
    Uses isDefEq for type comparison so it works in both .meta and .anon modes.
    Matches constructors by address from Primitives, not by position. -/
def checkPrimitiveInductive (ops : KernelOps m) (p : Primitives) (kenv : Env m)
    (addr : Address) : TypecheckM m Bool := do
  let ci ← derefConst addr
  let .inductInfo iv := ci | return false
  if iv.isUnsafe then return false
  if iv.numLevels != 0 then return false
  if iv.numParams != 0 then return false
  unless ← ops.isDefEq iv.type (Expr.mkSort (Level.succ .zero)) do return false
  -- Check Bool
  if addr == p.bool then
    if iv.ctors.size != 2 then
      throw "Bool must have exactly 2 constructors"
    for ctorAddr in iv.ctors do
      let ctor ← derefConst ctorAddr
      unless ← ops.isDefEq ctor.type (boolConst p) do
        throw s!"Bool constructor has unexpected type"
    return true
  -- Check Nat
  if addr == p.nat then
    if iv.ctors.size != 2 then
      throw "Nat must have exactly 2 constructors"
    for ctorAddr in iv.ctors do
      let ctor ← derefConst ctorAddr
      if ctorAddr == p.natZero then
        unless ← ops.isDefEq ctor.type (natConst p) do
          throw "Nat.zero has unexpected type"
      else if ctorAddr == p.natSucc then
        unless ← ops.isDefEq ctor.type (natUnaryType p) do
          throw "Nat.succ has unexpected type"
      else
        throw s!"unexpected Nat constructor"
    return true
  return false

/-! ## Simple primitive definition checks -/

/-- Check a primitive definition's type and reduction rules.
    Returns true if the address matches a known primitive and passes validation. -/
def checkPrimitiveDef (ops : KernelOps m) (p : Primitives) (kenv : Env m) (addr : Address)
    : TypecheckM m Bool := do
  let ci ← derefConst addr
  let .defnInfo v := ci | return false
  -- Skip if addr doesn't match any known primitive (avoid false positives).
  -- stringOfList is excluded when it equals stringMk (constructor, validated via inductive path).
  let isPrimAddr := addr == p.natAdd || addr == p.natSub || addr == p.natMul ||
    addr == p.natPow || addr == p.natBeq || addr == p.natBle ||
    addr == p.natShiftLeft || addr == p.natShiftRight ||
    addr == p.natLand || addr == p.natLor || addr == p.natXor ||
    addr == p.natPred || addr == p.natBitwise ||
    addr == p.natMod || addr == p.natDiv || addr == p.natGcd ||
    addr == p.charMk ||
    (addr == p.stringOfList && p.stringOfList != p.stringMk)
  if !isPrimAddr then return false
  let fail {α : Type} (msg : String := "invalid form for primitive def") : TypecheckM m α :=
    throw msg
  let nat : Expr m := natConst p
  let tru : Expr m := trueConst p
  let fal : Expr m := falseConst p
  let zero : Expr m := zeroConst p
  let succ : Expr m → Expr m := succApp p
  let pred : Expr m → Expr m := predApp p
  let add : Expr m → Expr m → Expr m := addApp p
  let _sub : Expr m → Expr m → Expr m := subApp p
  let mul : Expr m → Expr m → Expr m := mulApp p
  let _mod' : Expr m → Expr m → Expr m := modApp p
  let div' : Expr m → Expr m → Expr m := divApp p
  let one : Expr m := succ zero
  let two : Expr m := succ one
  -- x = bvar 0, y = bvar 1 (inside wrapping binders)
  let x : Expr m := .mkBVar 0
  let y : Expr m := .mkBVar 1

  -- Nat.add
  if addr == p.natAdd then
    if !kenv.contains p.nat || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let addV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← defeq1 ops p (addV x zero) x do fail
    unless ← defeq2 ops p (addV y (succ x)) (succ (addV y x)) do fail
    return true

  -- Nat.pred
  if addr == p.natPred then
    if !kenv.contains p.nat || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natUnaryType p) do fail
    let predV := fun a => Expr.mkApp v.value a
    unless ← ops.isDefEq (predV zero) zero do fail
    unless ← defeq1 ops p (predV (succ x)) x do fail
    return true

  -- Nat.sub
  if addr == p.natSub then
    if !kenv.contains p.natPred || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let subV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← defeq1 ops p (subV x zero) x do fail
    unless ← defeq2 ops p (subV y (succ x)) (pred (subV y x)) do fail
    return true

  -- Nat.mul
  if addr == p.natMul then
    if !kenv.contains p.natAdd || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let mulV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← defeq1 ops p (mulV x zero) zero do fail
    unless ← defeq2 ops p (mulV y (succ x)) (add (mulV y x) y) do fail
    return true

  -- Nat.pow
  if addr == p.natPow then
    if !kenv.contains p.natMul || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let powV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← defeq1 ops p (powV x zero) one do fail
    unless ← defeq2 ops p (powV y (succ x)) (mul (powV y x) y) do fail
    return true

  -- Nat.beq
  if addr == p.natBeq then
    if !kenv.contains p.nat || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinBoolType p) do fail
    let beqV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← ops.isDefEq (beqV zero zero) tru do fail
    unless ← defeq1 ops p (beqV zero (succ x)) fal do fail
    unless ← defeq1 ops p (beqV (succ x) zero) fal do fail
    unless ← defeq2 ops p (beqV (succ y) (succ x)) (beqV y x) do fail
    return true

  -- Nat.ble
  if addr == p.natBle then
    if !kenv.contains p.nat || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinBoolType p) do fail
    let bleV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← ops.isDefEq (bleV zero zero) tru do fail
    unless ← defeq1 ops p (bleV zero (succ x)) tru do fail
    unless ← defeq1 ops p (bleV (succ x) zero) fal do fail
    unless ← defeq2 ops p (bleV (succ y) (succ x)) (bleV y x) do fail
    return true

  -- Nat.shiftLeft
  if addr == p.natShiftLeft then
    if !kenv.contains p.natMul || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let shlV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← defeq1 ops p (shlV x zero) x do fail
    unless ← defeq2 ops p (shlV x (succ y)) (shlV (mul two x) y) do fail
    return true

  -- Nat.shiftRight
  if addr == p.natShiftRight then
    if !kenv.contains p.natDiv || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let shrV := fun a b => Expr.mkApp (Expr.mkApp v.value a) b
    unless ← defeq1 ops p (shrV x zero) x do fail
    unless ← defeq2 ops p (shrV x (succ y)) (div' (shrV x y) two) do fail
    return true

  -- Nat.land
  if addr == p.natLand then
    if !kenv.contains p.natBitwise || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.land value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise do fail "Nat.land value head must be Nat.bitwise"
    let andF := fun a b => Expr.mkApp (Expr.mkApp f a) b
    unless ← defeq1 ops p (andF fal x) fal do fail
    unless ← defeq1 ops p (andF tru x) x do fail
    return true

  -- Nat.lor
  if addr == p.natLor then
    if !kenv.contains p.natBitwise || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.lor value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise do fail "Nat.lor value head must be Nat.bitwise"
    let orF := fun a b => Expr.mkApp (Expr.mkApp f a) b
    unless ← defeq1 ops p (orF fal x) x do fail
    unless ← defeq1 ops p (orF tru x) tru do fail
    return true

  -- Nat.xor
  if addr == p.natXor then
    if !kenv.contains p.natBitwise || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    let (.app fn f) := v.value | fail "Nat.xor value must be Nat.bitwise applied to a function"
    unless fn.isConstOf p.natBitwise do fail "Nat.xor value head must be Nat.bitwise"
    let xorF := fun a b => Expr.mkApp (Expr.mkApp f a) b
    unless ← ops.isDefEq (xorF fal fal) fal do fail
    unless ← ops.isDefEq (xorF tru fal) tru do fail
    unless ← ops.isDefEq (xorF fal tru) tru do fail
    unless ← ops.isDefEq (xorF tru tru) fal do fail
    return true

  -- Nat.mod (type validation only — full behavioral validation requires
  -- well-founded recursion checking with Nat.modCore.go, see lean4lean Primitive.lean:233-258)
  if addr == p.natMod then
    if !kenv.contains p.natSub || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    return true

  -- Nat.div (type validation only — full behavioral validation requires
  -- well-founded recursion checking with Nat.div.go, see lean4lean Primitive.lean:259-281)
  if addr == p.natDiv then
    if !kenv.contains p.natSub || !kenv.contains p.bool || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    return true

  -- Nat.gcd (type validation only — full behavioral validation requires
  -- unfoldWellFounded + Nat.mod, see lean4lean Primitive.lean:282-292)
  if addr == p.natGcd then
    if !kenv.contains p.natMod || v.numLevels != 0 then fail
    unless ← ops.isDefEq v.type (natBinType p) do fail
    return true

  -- Char.ofNat (charMk field)
  if addr == p.charMk then
    if !kenv.contains p.nat || v.numLevels != 0 then fail
    let expectedType := mkArrow nat (charConst p)
    unless ← ops.isDefEq v.type expectedType do fail
    return true

  -- String.ofList
  if addr == p.stringOfList then
    if v.numLevels != 0 then fail
    let listChar := listCharConst p
    let expectedType := mkArrow listChar (stringConst p)
    unless ← ops.isDefEq v.type expectedType do fail
    -- Check List.nil Char : List Char
    let nilChar := Expr.mkApp (Expr.mkConst p.listNil #[Level.succ .zero]) (charConst p)
    let (_, nilType) ← ops.infer nilChar
    unless ← ops.isDefEq nilType listChar do fail
    -- Check List.cons Char : Char → List Char → List Char
    let consChar := Expr.mkApp (Expr.mkConst p.listCons #[Level.succ .zero]) (charConst p)
    let (_, consType) ← ops.infer consChar
    let expectedConsType := mkArrow (charConst p) (mkArrow listChar listChar)
    unless ← ops.isDefEq consType expectedConsType do fail
    return true

  return false

/-! ## Quotient validation -/

/-- Check that the Eq inductive has the correct form using isDefEq.
    Eq must be an inductive with 1 univ param, 1 constructor.
    Eq type: ∀ {α : Sort u}, α → α → Prop
    Eq.refl type: ∀ {α : Sort u} (a : α), @Eq α a a -/
def checkEqType (ops : KernelOps m) (p : Primitives) : TypecheckM m Unit := do
  if !(← read).kenv.contains p.eq then
    throw "Eq type not found in environment"
  let ci ← derefConst p.eq
  let .inductInfo iv := ci | throw "Eq is not an inductive"
  if iv.numLevels != 1 then
    throw "Eq must have exactly 1 universe parameter"
  if iv.ctors.size != 1 then
    throw "Eq must have exactly 1 constructor"
  -- Check Eq type: ∀ {α : Sort u}, α → α → Prop
  let u : Level m := .param 0 default
  let sortU : Expr m := Expr.mkSort u
  let expectedEqType : Expr m :=
    Expr.mkForallE sortU             -- {α : Sort u}
      (Expr.mkForallE (.mkBVar 0)    -- (a : α)
        (Expr.mkForallE (.mkBVar 1)  -- (b : α)
          Expr.prop))                -- Prop
  unless ← ops.isDefEq ci.type expectedEqType do
    throw "Eq has unexpected type"

  -- Check Eq.refl
  if !(← read).kenv.contains p.eqRefl then
    throw "Eq.refl not found in environment"
  let refl ← derefConst p.eqRefl
  if refl.numLevels != 1 then
    throw "Eq.refl must have exactly 1 universe parameter"
  let eqConst : Expr m := Expr.mkConst p.eq #[u]
  let expectedReflType : Expr m :=
    Expr.mkForallE sortU               -- {α : Sort u}
      (Expr.mkForallE (.mkBVar 0)      -- (a : α)
        (Expr.mkApp (Expr.mkApp (Expr.mkApp eqConst (.mkBVar 1)) (.mkBVar 0)) (.mkBVar 0)))
  unless ← ops.isDefEq refl.type expectedReflType do
    throw "Eq.refl has unexpected type"

/-- Check quotient type signatures against expected forms. -/
def checkQuotTypes (ops : KernelOps m) (p : Primitives)
    : TypecheckM m Unit := do
  let u : Level m := .param 0 default
  let sortU : Expr m := Expr.mkSort u

  -- Build `α → α → Prop` where α = bvar depth at the current level.
  -- Under one binder, α = bvar (depth+1). Direct forallE, no mkArrow lift.
  let relType (depth : Nat) : Expr m :=
    Expr.mkForallE (.mkBVar depth)                         -- ∀ (_ : α)
      (Expr.mkForallE (.mkBVar (depth + 1))               -- ∀ (_ : α)
        Expr.prop)

  -- Quot.{u} : ∀ {α : Sort u} (r : α → α → Prop), Sort u
  if resolved p.quotType then
    let ci ← derefConst p.quotType
    let expectedType : Expr m :=
      Expr.mkForallE sortU              -- {α : Sort u}
        (Expr.mkForallE (relType 0)     -- (r : α → α → Prop)
          (Expr.mkSort u))
    unless ← ops.isDefEq ci.type expectedType do
      throw "Quot type signature mismatch"

  -- Quot.mk.{u} : ∀ {α : Sort u} (r : α → α → Prop) (a : α), @Quot α r
  -- Under {α=2, r=1, a=0}: Quot α r = Quot (bvar 2) (bvar 1)
  if resolved p.quotCtor then
    let ci ← derefConst p.quotCtor
    let quotApp : Expr m := Expr.mkApp (Expr.mkApp (Expr.mkConst p.quotType #[u]) (.mkBVar 2)) (.mkBVar 1)
    let expectedType : Expr m :=
      Expr.mkForallE sortU              -- {α : Sort u}
        (Expr.mkForallE (relType 0)     -- (r : α → α → Prop)
          (Expr.mkForallE (.mkBVar 1)   -- (a : α) — α=bvar 1 under {α=1, r=0}
            quotApp))
    unless ← ops.isDefEq ci.type expectedType do
      throw "Quot.mk type signature mismatch"

  -- Quot.lift.{u,v} : ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
  --   (∀ (a b : α), r a b → @Eq β (f a) (f b)) → @Quot α r → β
  if resolved p.quotLift then
    let ci ← derefConst p.quotLift
    if ci.numLevels != 2 then
      throw "Quot.lift must have exactly 2 universe parameters"
    let v : Level m := .param 1 default
    let sortV : Expr m := Expr.mkSort v
    -- f type at depth 3 (α=bvar2, r=bvar1, β=bvar0): α → β
    let fType : Expr m := Expr.mkForallE (.mkBVar 2) (.mkBVar 1)
    -- h type at depth 4 (α=bvar3, r=bvar2, β=bvar1, f=bvar0):
    --   ∀ (a : α) (b : α), r a b → @Eq β (f a) (f b)
    let hType : Expr m :=
      Expr.mkForallE (.mkBVar 3)                                   -- ∀ (a : α)
        (Expr.mkForallE (.mkBVar 4)                                -- ∀ (b : α)
          (Expr.mkForallE                                          -- r a b →
            (Expr.mkApp (Expr.mkApp (.mkBVar 4) (.mkBVar 1)) (.mkBVar 0))
            -- @Eq.{v} β (f a) (f b) at depth 7
            (Expr.mkApp (Expr.mkApp (Expr.mkApp (Expr.mkConst p.eq #[v]) (.mkBVar 4))
              (Expr.mkApp (.mkBVar 3) (.mkBVar 2)))
              (Expr.mkApp (.mkBVar 3) (.mkBVar 1)))))
    -- q type at depth 5 (α=bvar4, r=bvar3): @Quot α r
    let qType : Expr m := Expr.mkApp (Expr.mkApp (Expr.mkConst p.quotType #[u]) (.mkBVar 4)) (.mkBVar 3)
    -- return type at depth 6: β = bvar 3
    let expectedType : Expr m :=
      Expr.mkForallE sortU                                         -- {α : Sort u}
        (Expr.mkForallE (relType 0)                                -- {r : α → α → Prop}
          (Expr.mkForallE sortV                                    -- {β : Sort v}
            (Expr.mkForallE fType                                  -- (f : α → β)
              (Expr.mkForallE hType                                -- (h : ∀ a b, ...)
                (Expr.mkForallE qType                              -- @Quot α r →
                  (.mkBVar 3))))))                                 -- β
    unless ← ops.isDefEq ci.type expectedType do
      throw "Quot.lift type signature mismatch"

  -- Quot.ind.{u} : ∀ {α : Sort u} {r : α → α → Prop} {β : @Quot α r → Prop},
  --   (∀ (a : α), β (@Quot.mk α r a)) → ∀ (q : @Quot α r), β q
  if resolved p.quotInd then
    let ci ← derefConst p.quotInd
    if ci.numLevels != 1 then
      throw "Quot.ind must have exactly 1 universe parameter"
    -- β type at depth 2 (α=bvar1, r=bvar0): @Quot α r → Prop
    let quotAtDepth2 : Expr m := Expr.mkApp (Expr.mkApp (Expr.mkConst p.quotType #[u]) (.mkBVar 1)) (.mkBVar 0)
    let betaType : Expr m := Expr.mkForallE quotAtDepth2 Expr.prop
    -- h type at depth 3 (α=bvar2, r=bvar1, β=bvar0): ∀ (a : α), β (Quot.mk α r a)
    let quotMkA : Expr m := Expr.mkApp (Expr.mkApp (Expr.mkApp (Expr.mkConst p.quotCtor #[u]) (.mkBVar 3)) (.mkBVar 2)) (.mkBVar 0)
    let hType : Expr m := Expr.mkForallE (.mkBVar 2) (Expr.mkApp (.mkBVar 1) quotMkA)
    -- q type at depth 4 (α=bvar3, r=bvar2): @Quot α r
    let qType : Expr m := Expr.mkApp (Expr.mkApp (Expr.mkConst p.quotType #[u]) (.mkBVar 3)) (.mkBVar 2)
    -- return at depth 5: β q = app(bvar 2, bvar 0)
    let expectedType : Expr m :=
      Expr.mkForallE sortU                                         -- {α : Sort u}
        (Expr.mkForallE (relType 0)                                -- {r : α → α → Prop}
          (Expr.mkForallE betaType                                 -- {β : @Quot α r → Prop}
            (Expr.mkForallE hType                                  -- (h : ∀ a, β (Quot.mk α r a))
              (Expr.mkForallE qType                                -- ∀ (q : @Quot α r),
                (Expr.mkApp (.mkBVar 2) (.mkBVar 0))))))           -- β q
    unless ← ops.isDefEq ci.type expectedType do
      throw "Quot.ind type signature mismatch"

/-! ## Top-level dispatch -/

/-- Check if `addr` is a known primitive and validate it.
    Returns true if the address matches a known primitive and passes validation. -/
def checkPrimitive (ops : KernelOps m) (p : Primitives) (kenv : Env m) (addr : Address)
    : TypecheckM m Bool := do
  -- Try primitive inductives first
  if addr == p.bool || addr == p.nat then
    return ← checkPrimitiveInductive ops p kenv addr
  -- Try primitive definitions
  checkPrimitiveDef ops p kenv addr

end Ix.Kernel
