/-
  Kernel2 Helpers: Non-mutual utility functions on Val.

  These operate on Val without needing the mutual block (eval/force/isDefEq/infer).
  Includes: nat/string literal handling, projection reduction on values,
  primitive detection, and constructor analysis.

  Note: with lazy spines (Nat), helpers that inspect spine args
  require forced values. Functions here work on already-forced Val values
  or on metadata that doesn't require forcing (addresses, spine sizes).
-/
import Ix.Kernel.TypecheckM

namespace Ix.Kernel

/-! ## Nat helpers on Val -/

def extractNatVal (prims : KPrimitives m) (v : Val m) : Option Nat :=
  match v with
  | .lit (.natVal n) => some n
  | _ => do
    let addr ← v.constAddr?
    guard (addr == prims.natZero.addr && v.spine!.isEmpty)
    return 0

def isPrimOp (prims : KPrimitives m) (addr : Address) : Bool :=
  addr == prims.natAdd.addr || addr == prims.natSub.addr || addr == prims.natMul.addr ||
  addr == prims.natPow.addr || addr == prims.natGcd.addr || addr == prims.natMod.addr ||
  addr == prims.natDiv.addr || addr == prims.natBeq.addr || addr == prims.natBle.addr ||
  addr == prims.natLand.addr || addr == prims.natLor.addr || addr == prims.natXor.addr ||
  addr == prims.natShiftLeft.addr || addr == prims.natShiftRight.addr ||
  addr == prims.natSucc.addr || addr == prims.natPred.addr

/-- Check if a value is a nat primitive applied to args (not yet reduced). -/
def isNatPrimHead (prims : KPrimitives m) (v : Val m) : Bool :=
  match v with
  | .neutral (.const id _) spine => isPrimOp prims id.addr && !spine.isEmpty
  | _ => false

/-- Check if a value is a nat constructor (zero, succ, or literal).
    Unlike extractNatVal, this doesn't require fully extractable values —
    Nat.succ(x) counts even when x is symbolic. -/
def isNatConstructor (prims : KPrimitives m) (v : Val m) : Bool :=
  match v with
  | .lit (.natVal _) => true
  | _ =>
    if let some addr := v.constAddr? then
      let sp := v.spine!
      (addr == prims.natZero.addr && sp.isEmpty) ||
      (addr == prims.natSucc.addr && sp.size == 1)
    else false

/-- Extract the predecessor thunk from a structural Nat.succ value, without forcing.
    Only matches Ctor/Neutral with nat_succ head. Does NOT match Lit(NatVal(n)) —
    literals are handled by computeNatPrim in O(1). Matching literals here would
    cause O(n) recursion in the symbolic step-case reductions. -/
def extractSuccPred (prims : KPrimitives m) (v : Val m) : Option Nat := do
  let addr ← v.constAddr?
  let sp := v.spine!
  guard (addr == prims.natSucc.addr && sp.size == 1)
  return sp[0]!

/-- Check if a value is Nat.zero (constructor or literal 0). -/
def isNatZeroVal (prims : KPrimitives m) (v : Val m) : Bool :=
  match v with
  | .lit (.natVal 0) => true
  | _ =>
    if let some addr := v.constAddr? then
      addr == prims.natZero.addr && v.spine!.isEmpty
    else false

/-- Compute a nat primitive given two resolved nat values. -/
def computeNatPrim (prims : KPrimitives m) (addr : Address) (x y : Nat) : Option (Val m) :=
  if addr == prims.natAdd.addr then some (.lit (.natVal (x + y)))
  else if addr == prims.natSub.addr then some (.lit (.natVal (x - y)))
  else if addr == prims.natMul.addr then some (.lit (.natVal (x * y)))
  else if addr == prims.natPow.addr then
    if y > 16777216 then none
    else some (.lit (.natVal (Nat.pow x y)))
  else if addr == prims.natMod.addr then some (.lit (.natVal (x % y)))
  else if addr == prims.natDiv.addr then some (.lit (.natVal (x / y)))
  else if addr == prims.natGcd.addr then some (.lit (.natVal (Nat.gcd x y)))
  else if addr == prims.natBeq.addr then
    if x == y then some (.ctor prims.boolTrue #[] 1 0 0 prims.bool #[])
    else some (.ctor prims.boolFalse #[] 0 0 0 prims.bool #[])
  else if addr == prims.natBle.addr then
    if x ≤ y then some (.ctor prims.boolTrue #[] 1 0 0 prims.bool #[])
    else some (.ctor prims.boolFalse #[] 0 0 0 prims.bool #[])
  else if addr == prims.natLand.addr then some (.lit (.natVal (Nat.land x y)))
  else if addr == prims.natLor.addr then some (.lit (.natVal (Nat.lor x y)))
  else if addr == prims.natXor.addr then some (.lit (.natVal (Nat.xor x y)))
  else if addr == prims.natShiftLeft.addr then some (.lit (.natVal (Nat.shiftLeft x y)))
  else if addr == prims.natShiftRight.addr then some (.lit (.natVal (Nat.shiftRight x y)))
  else none

/-! ## Nat literal → constructor conversion on Val -/

-- Note: natLit (n+1) → Nat.succ (natLit n) requires allocating a thunk,
-- so it must be done in TypecheckM. See natLitToCtorThunked in Infer.lean.

/-! ## Projection reduction on Val (needs forced struct) -/

/-- Try to reduce a projection on an already-forced struct value.
    Returns the ThunkId (spine index) of the projected field if successful. -/
def reduceValProjForced (_typeId : KMetaId m) (idx : Nat) (structV : Val m)
    (_kenv : KEnv m) (_prims : KPrimitives m)
    : Option Nat :=
  match structV with
  | .ctor _ _ _ numParams _ _ spine =>
    let realIdx := numParams + idx
    if h : realIdx < spine.size then
      some spine[realIdx]
    else
      none
  | _ => none

/-! ## Delta-reducibility check on Val -/

def getDeltaInfo (v : Val m) (kenv : KEnv m)
    : Option (KMetaId m × KReducibilityHints) :=
  match v with
  | .neutral (.const id _) _ =>
    match kenv.find? id with
    | some (.defnInfo dv) => some (id, dv.hints)
    | some (.thmInfo _) => some (id, .regular 0)
    | _ => none
  | _ => none

def isStructLikeApp (v : Val m) (kenv : KEnv m)
    : Option (Ix.Kernel.ConstructorVal m) :=
  match v with
  | .ctor id _ _ _ _ inductId _ =>
    match kenv.find? id with
    | some (.ctorInfo cv) =>
      if kenv.isStructureLike inductId then some cv else none
    | _ => none
  | _ => none

end Ix.Kernel
