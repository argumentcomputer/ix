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

def extractNatVal (prims : KPrimitives) (v : Val m) : Option Nat :=
  match v with
  | .lit (.natVal n) => some n
  | .neutral (.const addr _ _) spine =>
    if addr == prims.natZero && spine.isEmpty then some 0 else none
  | .ctor addr _ _ _ _ _ _ spine =>
    if addr == prims.natZero && spine.isEmpty then some 0 else none
  | _ => none

def isPrimOp (prims : KPrimitives) (addr : Address) : Bool :=
  addr == prims.natAdd || addr == prims.natSub || addr == prims.natMul ||
  addr == prims.natPow || addr == prims.natGcd || addr == prims.natMod ||
  addr == prims.natDiv || addr == prims.natBeq || addr == prims.natBle ||
  addr == prims.natLand || addr == prims.natLor || addr == prims.natXor ||
  addr == prims.natShiftLeft || addr == prims.natShiftRight ||
  addr == prims.natSucc

/-- Check if a value is a nat primitive applied to args (not yet reduced). -/
def isNatPrimHead (prims : KPrimitives) (v : Val m) : Bool :=
  match v with
  | .neutral (.const addr _ _) spine => isPrimOp prims addr && !spine.isEmpty
  | _ => false

/-- Check if a value is a nat constructor (zero, succ, or literal).
    Unlike extractNatVal, this doesn't require fully extractable values —
    Nat.succ(x) counts even when x is symbolic. -/
def isNatConstructor (prims : KPrimitives) (v : Val m) : Bool :=
  match v with
  | .lit (.natVal _) => true
  | .neutral (.const addr _ _) spine =>
    (addr == prims.natZero && spine.isEmpty) ||
    (addr == prims.natSucc && spine.size == 1)
  | .ctor addr _ _ _ _ _ _ spine =>
    (addr == prims.natZero && spine.isEmpty) ||
    (addr == prims.natSucc && spine.size == 1)
  | _ => false

/-- Compute a nat primitive given two resolved nat values. -/
def computeNatPrim (prims : KPrimitives) (addr : Address) (x y : Nat) : Option (Val m) :=
  if addr == prims.natAdd then some (.lit (.natVal (x + y)))
  else if addr == prims.natSub then some (.lit (.natVal (x - y)))
  else if addr == prims.natMul then some (.lit (.natVal (x * y)))
  else if addr == prims.natPow then
    if y > 16777216 then none
    else some (.lit (.natVal (Nat.pow x y)))
  else if addr == prims.natMod then some (.lit (.natVal (x % y)))
  else if addr == prims.natDiv then some (.lit (.natVal (x / y)))
  else if addr == prims.natGcd then some (.lit (.natVal (Nat.gcd x y)))
  else if addr == prims.natBeq then
    if x == y then some (.ctor prims.boolTrue #[] default 1 0 0 prims.bool #[])
    else some (.ctor prims.boolFalse #[] default 0 0 0 prims.bool #[])
  else if addr == prims.natBle then
    if x ≤ y then some (.ctor prims.boolTrue #[] default 1 0 0 prims.bool #[])
    else some (.ctor prims.boolFalse #[] default 0 0 0 prims.bool #[])
  else if addr == prims.natLand then some (.lit (.natVal (Nat.land x y)))
  else if addr == prims.natLor then some (.lit (.natVal (Nat.lor x y)))
  else if addr == prims.natXor then some (.lit (.natVal (Nat.xor x y)))
  else if addr == prims.natShiftLeft then some (.lit (.natVal (Nat.shiftLeft x y)))
  else if addr == prims.natShiftRight then some (.lit (.natVal (Nat.shiftRight x y)))
  else none

/-! ## Nat literal → constructor conversion on Val -/

-- Note: natLit (n+1) → Nat.succ (natLit n) requires allocating a thunk,
-- so it must be done in TypecheckM. See natLitToCtorThunked in Infer.lean.

/-! ## Projection reduction on Val (needs forced struct) -/

/-- Try to reduce a projection on an already-forced struct value.
    Returns the ThunkId (spine index) of the projected field if successful. -/
def reduceValProjForced (_typeAddr : Address) (idx : Nat) (structV : Val m)
    (_kenv : KEnv m) (_prims : KPrimitives)
    : Option Nat :=
  match structV with
  | .ctor _ _ _ _ numParams _ _ spine =>
    let realIdx := numParams + idx
    if h : realIdx < spine.size then
      some spine[realIdx]
    else
      none
  | _ => none

/-! ## Delta-reducibility check on Val -/

def getDeltaInfo (v : Val m) (kenv : KEnv m)
    : Option (Address × KReducibilityHints) :=
  match v with
  | .neutral (.const addr _ _) _ =>
    match kenv.find? addr with
    | some (.defnInfo dv) => some (addr, dv.hints)
    | some (.thmInfo _) => some (addr, .regular 0)
    | _ => none
  | _ => none

def isStructLikeApp (v : Val m) (kenv : KEnv m)
    : Option (Ix.Kernel.ConstructorVal m) :=
  match v with
  | .ctor addr _ _ _ _ _ inductAddr _ =>
    match kenv.find? addr with
    | some (.ctorInfo cv) =>
      if kenv.isStructureLike inductAddr then some cv else none
    | _ => none
  | _ => none

end Ix.Kernel
