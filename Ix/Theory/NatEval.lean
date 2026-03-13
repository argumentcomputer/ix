/-
  Ix.Theory.NatEval: Nat-reducing evaluator and roundtrip properties.

  Defines `tryNatReduce` and `eval_nat_s`, a wrapper around `eval_s` that
  reduces nat primitive operations. Proves key properties about nat reduction.
-/
import Ix.Theory.Nat
import Ix.Theory.Roundtrip

namespace Ix.Theory

/-! ## Nat reduction oracle -/

variable {L : Type}

/-- Check if a head is a const with a specific ID. -/
def SHead.isConstId (h : SHead L) (id : Nat) : Bool :=
  match h with
  | .const cid _ => cid == id
  | .fvar _ => false

/-- Identify which binary op (if any) a const head corresponds to. -/
def SNatConfig.identifyBinOp [BEq L] (cfg : SNatConfig) (hd : SHead L) :
    Option NatPrimOp :=
  if hd.isConstId cfg.addId then some .add
  else if hd.isConstId cfg.subId then some .sub
  else if hd.isConstId cfg.mulId then some .mul
  else if hd.isConstId cfg.powId then some .pow
  else if hd.isConstId cfg.divId then some .div
  else if hd.isConstId cfg.modId then some .mod
  else if hd.isConstId cfg.gcdId then some .gcd
  else if hd.isConstId cfg.beqId then some .beq
  else if hd.isConstId cfg.bleId then some .ble
  else if hd.isConstId cfg.landId then some .land
  else if hd.isConstId cfg.lorId then some .lor
  else if hd.isConstId cfg.xorId then some .xor
  else if hd.isConstId cfg.shiftLeftId then some .shiftLeft
  else if hd.isConstId cfg.shiftRightId then some .shiftRight
  else none

/-- Try to reduce a fully-applied nat primitive on a value.
    Mirrors `try_reduce_nat_val` in `src/ix/kernel/whnf.rs:469-517`. -/
def tryNatReduce [BEq L] (cfg : SNatConfig) : SVal L → Option (SVal L)
  | .neutral hd [] =>
    if hd.isConstId cfg.zeroId then some (.lit 0) else none
  | .neutral hd [.lit n] =>
    if hd.isConstId cfg.succId then some (.lit (n + 1)) else none
  | .neutral hd [.lit m, .lit n] =>
    (cfg.identifyBinOp hd).map fun op => .lit (natPrimCompute op m n)
  | _ => none

/-- Apply nat reduction to a value, falling through if it doesn't fire. -/
def reduceNat [BEq L] (cfg : SNatConfig) (v : SVal L) : SVal L :=
  (tryNatReduce cfg v).getD v

/-! ## Nat-reducing evaluator -/

mutual
def eval_nat_s [BEq L] (fuel : Nat) (e : SExpr L) (env : List (SVal L))
    (cfg : SNatConfig) : Option (SVal L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar idx => env[idx]?
    | .sort u => some (.sort u)
    | .const id levels => some (reduceNat cfg (.neutral (.const id levels) []))
    | .app fn arg =>
      do let fv ← eval_nat_s fuel fn env cfg
         let av ← eval_nat_s fuel arg env cfg
         apply_nat_s fuel fv av cfg
    | .lam dom body =>
      do let dv ← eval_nat_s fuel dom env cfg
         some (.lam dv body env)
    | .forallE dom body =>
      do let dv ← eval_nat_s fuel dom env cfg
         some (.pi dv body env)
    | .letE _ty val body =>
      do let vv ← eval_nat_s fuel val env cfg
         eval_nat_s fuel body (vv :: env) cfg
    | .lit n => some (.lit n)
    | .proj _t _i _s => none

def apply_nat_s [BEq L] (fuel : Nat) (fn arg : SVal L) (cfg : SNatConfig) :
    Option (SVal L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match fn with
    | .lam _dom body env => eval_nat_s fuel body (arg :: env) cfg
    | .neutral hd spine =>
      some (reduceNat cfg (.neutral hd (spine ++ [arg])))
    | _ => none
end

/-- Full NbE with nat reduction: evaluate then quote back. -/
def nbe_nat_s [BEq L] (fuel : Nat) (e : SExpr L) (env : List (SVal L))
    (cfg : SNatConfig) (d : Nat) : Option (SExpr L) :=
  do let v ← eval_nat_s fuel e env cfg
     quote_s fuel v d

/-! ## tryNatReduce on fvar-headed values -/

/-- `tryNatReduce` never fires on fvar-headed neutrals. -/
theorem tryNatReduce_fvar [BEq L] (level : Nat) (spine : List (SVal L))
    (cfg : SNatConfig) :
    tryNatReduce cfg (.neutral (.fvar level) spine) = none := by
  unfold tryNatReduce
  cases spine with
  | nil => simp [SHead.isConstId]
  | cons hd tl =>
    cases hd with
    | lit n =>
      cases tl with
      | nil => simp [SHead.isConstId]
      | cons hd2 tl2 =>
        cases hd2 with
        | lit m =>
          cases tl2 with
          | nil =>
            simp [Option.map, SNatConfig.identifyBinOp, SHead.isConstId]
          | cons => rfl
        | sort _ => rfl
        | lam _ _ _ => rfl
        | pi _ _ _ => rfl
        | neutral _ _ => rfl
    | sort _ => rfl
    | lam _ _ _ => rfl
    | pi _ _ _ => rfl
    | neutral _ _ => rfl

/-- `reduceNat` is the identity on fvar-headed neutrals. -/
theorem reduceNat_fvar [BEq L] (level : Nat) (spine : List (SVal L))
    (cfg : SNatConfig) :
    reduceNat cfg (.neutral (.fvar level) spine) =
    SVal.neutral (.fvar level) spine := by
  simp [reduceNat, tryNatReduce_fvar]

/-- `tryNatReduce` preserves well-formedness: if it succeeds,
    the result is always a literal, which is trivially well-formed. -/
theorem tryNatReduce_preserves_wf [BEq L] (cfg : SNatConfig)
    (hv : tryNatReduce cfg v = some v') : ValWF (L := L) v' d := by
  unfold tryNatReduce at hv
  split at hv
  · -- zero case
    split at hv <;> simp at hv; subst hv; exact .lit
  · -- succ case
    split at hv <;> simp at hv; subst hv; exact .lit
  · -- binary op case: uses identifyBinOp which returns Option, mapped to .lit
    simp [Option.map] at hv
    split at hv <;> simp at hv
    subst hv; exact .lit
  · -- catch-all: returns none
    contradiction

/-! ## Sanity checks -/

private def testCfg : SNatConfig where
  natId := 0; zeroId := 1; succId := 2; recId := 3; predId := 4
  addId := 5; subId := 6; mulId := 7; powId := 8; divId := 9
  modId := 10; gcdId := 11; beqId := 12; bleId := 13; landId := 14
  lorId := 15; xorId := 16; shiftLeftId := 17; shiftRightId := 18

-- Nat.add 3 5 = 8
#guard eval_nat_s (L := Nat) 20
  (.app (.app (.const 5 []) (.lit 3)) (.lit 5)) [] testCfg == some (.lit 8)

-- Nat.succ 41 = 42
#guard eval_nat_s (L := Nat) 20
  (.app (.const 2 []) (.lit 41)) [] testCfg == some (.lit 42)

-- Nat.zero = 0
#guard eval_nat_s (L := Nat) 20
  (.const 1 []) [] testCfg == some (.lit 0)

-- Nat.mul 3 5 = 15
#guard eval_nat_s (L := Nat) 20
  (.app (.app (.const 7 []) (.lit 3)) (.lit 5)) [] testCfg == some (.lit 15)

-- Nested: Nat.add (Nat.mul 2 3) (Nat.succ 4) = 6 + 5 = 11
#guard eval_nat_s (L := Nat) 30
  (.app (.app (.const 5 [])
    (.app (.app (.const 7 []) (.lit 2)) (.lit 3)))
    (.app (.const 2 []) (.lit 4))) [] testCfg == some (.lit 11)

-- Non-nat const stays neutral
#guard eval_nat_s (L := Nat) 20
  (.app (.const 99 []) (.lit 1)) [] testCfg ==
  some (.neutral (.const 99 []) [.lit 1])

-- Nat type const stays neutral (natId=0 ≠ zeroId=1)
#guard eval_nat_s (L := Nat) 20
  (.const 0 []) [] testCfg ==
  some (.neutral (.const 0 []) [])

end Ix.Theory
