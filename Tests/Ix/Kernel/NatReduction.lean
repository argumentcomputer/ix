/-
  Comprehensive Nat literal reduction tests.

  See `docs/nat-reduction-audit.md` for the reference comparison
  (Ix kernel vs `refs/lean4` and `refs/lean4lean`).

  Tests use hand-built `Lean.Declaration` values with raw `.lit (.natVal _)`
  expressions rather than `by rfl` over surface syntax. This bypasses
  Lean's elaborator wrapping numerals in `OfNat.ofNat` and exercises our
  kernel's `try_reduce_nat` directly.

  Sections:
    A. Per-primitive literal-on-literal (parity with reference)
    B. `Nat.zero` literal-extension recognition (D10)
    C. `Nat.succ`/`Nat.zero` chains
    D. Def-eq mixed forms (literal vs constructor)
    E. Negative tests (`bad_decl`) guarding over-reduction
    F. `Nat.pow` cap (D6)
    G. `Nat.rec` linear shortcut (D9)
    H. `Nat.pred` via definition/iota
-/
import Tests.Ix.Kernel.TutorialMeta

set_option linter.unusedVariables false

open Tests.Ix.Kernel.TutorialMeta

namespace Tests.Ix.Kernel.NatReduction

/-! ## Helpers — raw declaration builders -/

/-- `op (lit a) (lit b) = lit r` -/
private def natBinThm (name : Lean.Name) (op : Lean.Name) (a b r : Nat) : Lean.Declaration :=
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
      (Lean.mkApp2 (Lean.mkConst op) (.lit (.natVal a)) (.lit (.natVal b)))
      (.lit (.natVal r))
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (.lit (.natVal r))
  }

/-- `pred (lit a) (lit b) = (true|false)` -/
private def natPredThm (name : Lean.Name) (op : Lean.Name) (a b : Nat) (result : Bool) : Lean.Declaration :=
  let boolCtor := Lean.mkConst (if result then ``Bool.true else ``Bool.false)
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Bool)
      (Lean.mkApp2 (Lean.mkConst op) (.lit (.natVal a)) (.lit (.natVal b)))
      boolCtor
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) boolCtor
  }

/-- `op (lit a) = lit r` (unary) -/
private def natUnaryThm (name : Lean.Name) (op : Lean.Name) (a r : Nat) : Lean.Declaration :=
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
      (Lean.mkApp (Lean.mkConst op) (.lit (.natVal a)))
      (.lit (.natVal r))
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (.lit (.natVal r))
  }

/-- `op zero|succ|lit/zero|succ|lit = result` for arbitrary Lean `Expr` arguments. -/
private def natBinThmExpr (name : Lean.Name) (op : Lean.Name) (a b r : Lean.Expr) : Lean.Declaration :=
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
      (Lean.mkApp2 (Lean.mkConst op) a b) r
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) r
  }

/-- `pred zero|succ|lit/zero|succ|lit = (true|false)` for arbitrary Lean `Expr` arguments. -/
private def natPredThmExpr (name : Lean.Name) (op : Lean.Name) (a b : Lean.Expr) (result : Bool) : Lean.Declaration :=
  let boolCtor := Lean.mkConst (if result then ``Bool.true else ``Bool.false)
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Bool)
      (Lean.mkApp2 (Lean.mkConst op) a b) boolCtor
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) boolCtor
  }

/-- A succ-chain over `lit 0`: `Nat.succ^n (lit 0)`. -/
private def succChainOfZero (n : Nat) : Lean.Expr :=
  match n with
  | 0 => Lean.mkConst ``Nat.zero
  | n + 1 => Lean.mkApp (Lean.mkConst ``Nat.succ) (succChainOfZero n)

/-! ## A. Per-primitive literal-on-literal (parity)
    Both Ix and the reference kernel reduce `op (lit a) (lit b)` to
    `lit (f a b)`. Tests use raw literals to exercise `try_reduce_nat`
    without `OfNat.ofNat` wrappers from Lean's elaborator. -/

-- Nat.add
good_decl (natBinThm `natAddZeroLeft   ``Nat.add 0 7 7)
good_decl (natBinThm `natAddZeroRight  ``Nat.add 7 0 7)
good_decl (natBinThm `natAddSmall      ``Nat.add 2 3 5)
good_decl (natBinThm `natAddLarge      ``Nat.add 1000000 2000000 3000000)

-- Nat.sub (saturating)
good_decl (natBinThm `natSubExact      ``Nat.sub 5 3 2)
good_decl (natBinThm `natSubEqual      ``Nat.sub 5 5 0)
good_decl (natBinThm `natSubUnderflow  ``Nat.sub 3 5 0)
good_decl (natBinThm `natSubByZero     ``Nat.sub 5 0 5)

-- Nat.mul
good_decl (natBinThm `natMulZeroLeft   ``Nat.mul 0 7 0)
good_decl (natBinThm `natMulZeroRight  ``Nat.mul 7 0 0)
good_decl (natBinThm `natMulSmall      ``Nat.mul 6 7 42)
good_decl (natBinThm `natMulOne        ``Nat.mul 1 42 42)

-- Nat.div (truncating; div-by-zero ⇒ 0)
good_decl (natBinThm `natDivExact      ``Nat.div 10 2 5)
good_decl (natBinThm `natDivTrunc      ``Nat.div 7 3 2)
good_decl (natBinThm `natDivByZero     ``Nat.div 7 0 0)
good_decl (natBinThm `natDivZeroBy     ``Nat.div 0 7 0)

-- Nat.mod (mod-by-zero ⇒ a)
good_decl (natBinThm `natModExact      ``Nat.mod 10 2 0)
good_decl (natBinThm `natModNonZero    ``Nat.mod 7 3 1)
good_decl (natBinThm `natModByZero     ``Nat.mod 7 0 7)
good_decl (natBinThm `natModZeroBy     ``Nat.mod 0 7 0)

-- Nat.pow
good_decl (natBinThm `natPowZeroBase   ``Nat.pow 0 5 0)
good_decl (natBinThm `natPowZeroExp    ``Nat.pow 5 0 1)
good_decl (natBinThm `natPowSmall      ``Nat.pow 2 10 1024)
good_decl (natBinThm `natPowOneBase    ``Nat.pow 1 100 1)

-- Nat.gcd
good_decl (natBinThm `natGcdZeroLeft   ``Nat.gcd 0 7 7)
good_decl (natBinThm `natGcdZeroRight  ``Nat.gcd 7 0 7)
good_decl (natBinThm `natGcdCoprime    ``Nat.gcd 9 4 1)
good_decl (natBinThm `natGcdShared     ``Nat.gcd 12 18 6)

-- Nat.beq / Nat.ble
good_decl (natPredThm `natBleEqLits    ``Nat.ble 5 5 true)
good_decl (natPredThm `natBleLT        ``Nat.ble 3 5 true)
good_decl (natPredThm `natBleGT        ``Nat.ble 5 3 false)
good_decl (natPredThm `natBleZero      ``Nat.ble 0 0 true)
good_decl (natPredThm `natBeqZero      ``Nat.beq 0 0 true)
good_decl (natPredThm `natBeqUnequal   ``Nat.beq 1 2 false)

-- Bitwise
good_decl (natBinThm `natLandDisjoint  ``Nat.land 0xF0 0x0F 0)
good_decl (natBinThm `natLandOverlap   ``Nat.land 0xFF 0x0F 0xF)
good_decl (natBinThm `natLorDisjoint   ``Nat.lor  0xF0 0x0F 0xFF)
good_decl (natBinThm `natXorSame       ``Nat.xor  0xFF 0xFF 0)
good_decl (natBinThm `natXorDisjoint   ``Nat.xor  0xFF 0x0F 0xF0)

-- Shifts
good_decl (natBinThm `natShiftLeftSmall  ``Nat.shiftLeft 1 4 16)
good_decl (natBinThm `natShiftRightSmall ``Nat.shiftRight 16 4 1)
good_decl (natBinThm `natShiftLeftZero   ``Nat.shiftLeft 5 0 5)
good_decl (natBinThm `natShiftRightZero  ``Nat.shiftRight 5 0 5)

/-! ## B. `Nat.zero` literal-extension recognition (D10)
    Both kernels treat `Nat.zero` constant as numeric `0`. Tests mix
    `Nat.zero` constructor with literals. -/

private def zeroExpr : Lean.Expr := Lean.mkConst ``Nat.zero
private def litExpr (n : Nat) : Lean.Expr := .lit (.natVal n)

good_decl (natBinThmExpr `natAddZeroCtorLeft  ``Nat.add zeroExpr (litExpr 7) (litExpr 7))
good_decl (natBinThmExpr `natAddZeroCtorRight ``Nat.add (litExpr 7) zeroExpr (litExpr 7))
good_decl (natBinThmExpr `natMulZeroCtorLeft  ``Nat.mul zeroExpr (litExpr 7) (litExpr 0))
good_decl (natBinThmExpr `natMulZeroCtorRight ``Nat.mul (litExpr 7) zeroExpr (litExpr 0))
good_decl (natBinThmExpr `natSubZeroCtor      ``Nat.sub (litExpr 7) zeroExpr (litExpr 7))
good_decl (natPredThmExpr `natBeqZeroCtorTrue   ``Nat.beq zeroExpr (litExpr 0) true)
good_decl (natPredThmExpr `natBleZeroCtorAnything ``Nat.ble zeroExpr (litExpr 5) true)

/-! ## C. `Nat.succ`/`Nat.zero` chain reduction
    Pin `is_nat_lit_ext`-style mixed literal/constructor recognition. -/

-- Nat.succ (lit 41) = lit 42
good_decl (.thmDecl {
  name := `natSuccOfLit
  levelParams := []
  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
    (Lean.mkApp (Lean.mkConst ``Nat.succ) (litExpr 41))
    (litExpr 42)
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (litExpr 42)
})

-- Nat.succ (Nat.succ (Nat.succ Nat.zero)) = lit 3
good_decl (.thmDecl {
  name := `natSuccChainOfZero
  levelParams := []
  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
    (succChainOfZero 3)
    (litExpr 3)
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (litExpr 3)
})

-- lit 4 = Nat.succ^4 Nat.zero
good_decl (.thmDecl {
  name := `natLitEqSuccChain
  levelParams := []
  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
    (litExpr 4)
    (succChainOfZero 4)
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (litExpr 4)
})

-- Nat.succ Nat.zero = lit 1
good_decl (.thmDecl {
  name := `natSuccOfZeroIsOne
  levelParams := []
  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
    (Lean.mkApp (Lean.mkConst ``Nat.succ) zeroExpr)
    (litExpr 1)
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (litExpr 1)
})

/-! ## D. Def-eq across literal / constructor forms
    Exercises `is_def_eq_nat` (`src/ix/kernel/def_eq.rs:920-983`).
    These keep the surface syntax with `OfNat`-wrapped literals on
    purpose, complementing the raw-literal tests in C. -/

good_thm natLitEqCtorChain : (3 : Nat) = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := by rfl
good_thm natLitEqMixed     : Nat.succ (2 : Nat) = (3 : Nat) := by rfl
good_thm natLitEqLitChain  : (3 : Nat) = Nat.succ (Nat.succ (Nat.succ 0)) := by rfl
good_thm natZeroEqLit      : Nat.zero = (0 : Nat) := by rfl
good_thm natZeroLitEqCtor  : (0 : Nat) = Nat.zero := by rfl

/-! ## E. Negative tests
    Wrong arithmetic results must be rejected. Catches accidental
    over-reduction or convention drift (e.g. div-by-zero ⇒ err). -/

-- These are bad_decl with an Eq.refl proof that doesn't match the type.
-- Lean kernel check is skipped; our kernel must reject.
private def natBadBinThm (name : Lean.Name) (op : Lean.Name) (a b claimed : Nat) : Lean.Declaration :=
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat)
      (Lean.mkApp2 (Lean.mkConst op) (.lit (.natVal a)) (.lit (.natVal b)))
      (.lit (.natVal claimed))
    -- Proof is Eq.refl claimed : claimed = claimed; declared LHS reduces to a different value.
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (.lit (.natVal claimed))
  }

private def natBadPredThm (name : Lean.Name) (op : Lean.Name) (a b : Nat) (claimed : Bool) : Lean.Declaration :=
  let boolCtor := Lean.mkConst (if claimed then ``Bool.true else ``Bool.false)
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Bool)
      (Lean.mkApp2 (Lean.mkConst op) (.lit (.natVal a)) (.lit (.natVal b)))
      boolCtor
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) boolCtor
  }

bad_decl (natBadBinThm  `natAddWrongResult     ``Nat.add 2 3 6)
bad_decl (natBadBinThm  `natSubWrongUnderflow  ``Nat.sub 3 5 1)
bad_decl (natBadBinThm  `natDivByZeroWrong     ``Nat.div 7 0 7)  -- spec: 0
bad_decl (natBadBinThm  `natModByZeroWrong     ``Nat.mod 7 0 0)  -- spec: 7
bad_decl (natBadPredThm `natBleWrong           ``Nat.ble 5 3 true)
bad_decl (natBadPredThm `natBeqWrong           ``Nat.beq 5 3 true)

/-! ## F. `Nat.pow` cap (D6 — matches reference at `2^24`)
    The over-cap stuck case (`Nat.pow 2 (2^24+1)` does NOT reduce) is
    pinned in the Rust mirror — Lean's elaborator can't even build a
    term with such a large literal exponent without exhausting recursion. -/

good_decl (natBinThm `natPowSmallExp ``Nat.pow 2 10 1024)

/-! ## G. `Nat.rec` linear shortcut (D9)
    Pin `try_reduce_nat_succ_linear_rec`. Without the shortcut the
    iota expansion of `f 100` would noticeably slow this test. -/

def natRecLinearAux : Nat → Nat
  | 0     => 5
  | n + 1 => Nat.succ (natRecLinearAux n)

good_thm natRecLinearCheck : natRecLinearAux 100 = 105 := by rfl

/-! ## H. `Nat.pred`
    `Nat.pred` is not in the native Nat reducer. It still reduces
    definitionally through its standard-library definition and iota. -/

good_decl (natUnaryThm `natPredOfLit   ``Nat.pred 5 4)
good_decl (natUnaryThm `natPredOfZero  ``Nat.pred 0 0)
good_decl (natUnaryThm `natPredOfLarge ``Nat.pred 1000000 999999)

end Tests.Ix.Kernel.NatReduction
