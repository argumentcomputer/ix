import IxCCGrounding.Lits
import IxCC.Src.Word

/-!
# The word equations' `Nat` formulas (`IxCCGrounding.WordForm`, step W)

A word entry's stored theorem says `op (ofNat x) (ofNat y) = ofNat' (F x y)` with `F` a formula over
`Nat`'s operations (`Table.wordEqnType`). `NForm` is such a formula over two variables; `toK` writes it
as a kernel term over the role keys, `val` evaluates it. **At literal arguments a formula denotes the
literal of its value** (`form_den`), by `nat_accel` at each operation (the ten arithmetic roles), given
their keys stored. `spec w op` is the formula each primitive operation's theorem states; **at words
below the size its value is `WordOp.eval`'s number** (`spec_val`), so the stored theorem and SrcEval's
rule F6w agree on every word they read.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open IxCC.Src (PrimOp Width WordOp)

/-- A `Nat` formula over two variables. -/
inductive NForm where
  | x | y
  | lit (n : Nat)
  | op (o : PrimOp) (a b : NForm)
  deriving Inhabited

namespace NForm

/-- The arithmetic operations a formula may use (each a binary role with a `Nat` result). -/
def arith : PrimOp → Bool
  | .add | .sub | .mul | .div | .mod | .land | .lor | .xor | .shiftLeft | .shiftRight => true
  | _ => false

/-- Lean's `Nat` function of an arithmetic operation. -/
def natOp : PrimOp → Nat → Nat → Nat
  | .add, a, b => a + b | .sub, a, b => a - b | .mul, a, b => a * b | .div, a, b => a / b
  | .mod, a, b => a % b | .land, a, b => a &&& b | .lor, a, b => a ||| b | .xor, a, b => a ^^^ b
  | .shiftLeft, a, b => a <<< b | .shiftRight, a, b => a >>> b
  | _, _, _ => 0

/-- The formula as a kernel term, `ex` and `ey` for the variables. -/
def toK (ex ey : KExpr) : NForm → KExpr
  | .x => ex | .y => ey | .lit n => litE n
  | .op o a b => .app (.app (.const (primKey o) []) (a.toK ex ey)) (b.toK ex ey)

def val (vx vy : Nat) : NForm → Nat
  | .x => vx | .y => vy | .lit n => n
  | .op o a b => natOp o (a.val vx vy) (b.val vx vy)

/-- Every operation arithmetic. -/
def ok : NForm → Bool
  | .op o a b => arith o && a.ok && b.ok
  | _ => true

/-- The operations a formula uses. -/
def ops : NForm → List PrimOp
  | .op o a b => o :: (a.ops ++ b.ops)
  | _ => []

end NForm

theorem shiftRight_eval2 (a b : Nat) :
    (if a.log2 < b then 0 else a / 2 ^ b) = a >>> b := by
  rw [Nat.shiftRight_eq_div_pow]
  split
  · rename_i h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · refine (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_log2_self (n := a)) ?_)).symm
      exact Nat.pow_le_pow_right (by decide) h
  · rfl

theorem eval2_arith {o : PrimOp} (h : NForm.arith o = true) (a b : Nat) :
    o.eval2 a b = .nat (NForm.natOp o a b) := by
  cases o <;> simp only [NForm.arith, Bool.false_eq_true] at h <;>
    simp only [PrimOp.eval2, NForm.natOp, IxCC.Src.PrimResult.nat.injEq]
  all_goals first
    | rfl
    | (by_cases hb : b = 0 <;> simp [hb])
    | exact (Nat.shiftLeft_eq a b).symm
    | exact shiftRight_eval2 a b

theorem arity_arith {o : PrimOp} (h : NForm.arith o = true) : o.arity = 2 := by
  cases o <;> simp [NForm.arith] at h <;> rfl

section Den

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **A formula at literal arguments denotes the literal of its value** (`nat_accel`). -/
theorem form_den (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {ex ey : KExpr} {vx vy : Nat}
    (hx : Denotes M.cval env φ ρ ex (litSet M φ vx)) (hy : Denotes M.cval env φ ρ ey (litSet M φ vy)) :
    ∀ f : NForm, f.ok = true →
      (∀ o ∈ f.ops, ∃ ci : ConstantInfo .anon, env.find? (primKey o) = some ci ∧
        ci.toConstantVal.levelParams = []) →
      Denotes M.cval env φ ρ (f.toK ex ey) (litSet M φ (f.val vx vy))
  | .x, _, _ => hx
  | .y, _, _ => hy
  | .lit n, _, _ => (lit_den M (natFacts M hN φ) ρ n _).mpr rfl
  | .op o a b, hok, hst => by
    simp only [NForm.ok, Bool.and_eq_true] at hok
    obtain ⟨⟨ho, ha⟩, hb⟩ := hok
    have hF := natFacts M hN φ
    have hda := form_den M hacc hN hx hy a ha (fun o' h => hst o' (by simp [NForm.ops, h]))
    have hdb := form_den M hacc hN hx hy b hb (fun o' h => hst o' (by simp [NForm.ops, h]))
    obtain ⟨ci, hf, hl⟩ := hst o (by simp [NForm.ops])
    have hK : Denotes M.cval env φ ρ (.const (primKey o) []) (M.cval (primKey o) φ) :=
      (den_const0 hf hl).mpr rfl
    have hprim : Denotes M.cval env φ ρ (primApp o (a.val vx vy) (b.val vx vy))
        (app (app (M.cval (primKey o) φ) (litSet M φ (a.val vx vy))) (litSet M φ (b.val vx vy))) := by
      have h21 : ¬ o.arity = 1 := by rw [arity_arith ho]; decide
      simp only [primApp, h21, ↓reduceIte]
      exact .app (.app hK ((lit_den M hF ρ _ _).mpr rfl)) ((lit_den M hF ρ _ _).mpr rfl)
    have hres := hacc o (a.val vx vy) (b.val vx vy) φ ρ _ (fun h => absurd (h.symm.trans (arity_arith ho)) (by decide))
      hprim
    rw [eval2_arith ho] at hres
    have hX := (lit_den M hF ρ _ _).mp hres
    show Denotes M.cval env φ ρ (.app (.app (.const (primKey o) []) (a.toK ex ey)) (b.toK ex ey))
      (litSet M φ (NForm.natOp o (a.val vx vy) (b.val vx vy)))
    rw [← hX]
    exact .app (.app hK hda) hdb

end Den

/-! ## The formula each primitive operation's theorem states -/

open NForm in
/-- `Table.wordEqnType`'s right-hand side as a formula (`x`, `y` the theorem's variables); the
decisions have none. For `toNat` it is the `Nat` result; for `ofNat` the bridge's reduced number. -/
def spec (w : Width) : WordOp → Option NForm
  | o =>
    let S := NForm.lit w.size
    let xm := NForm.op .mod .x S
    let ym := NForm.op .mod .y S
    let red := fun (e : NForm) => NForm.op .mod e S
    match o with
    | .add => some (red (.op .add xm ym))
    | .sub => some (red (.op .add (.op .sub S ym) xm))
    | .mul => some (red (.op .mul xm ym))
    | .div => some (.op .div xm ym)
    | .mod => some (.op .mod xm ym)
    | .land => some (.op .land xm ym)
    | .lor => some (.op .lor xm ym)
    | .xor => some (.op .xor xm ym)
    | .shiftLeft => some (red (.op .shiftLeft xm (.op .mod ym (.lit w.bits))))
    | .shiftRight => some (.op .shiftRight xm (.op .mod ym (.lit w.bits)))
    | .complement => some (.op .xor (.lit (w.size - 1)) xm)
    | .neg => some (red (.op .sub S xm))
    | .convert w' => some (if w.bits ≤ w'.bits then xm else .op .mod xm (.lit w'.size))
    | .toNat => some xm
    | .ofNat => some xm
    | .decEq | .decLt | .decLe => none

/-- **At words below the size, the theorem's formula is `WordOp.eval`'s number** (for `ofNat`, `x`
any number). -/
theorem spec_val (w : Width) (op : WordOp) {f : NForm} (hf : spec w op = some f) {x y : Nat}
    (hx : op = .ofNat ∨ x < w.size) (hy : y < w.size) :
    f.val x y = (WordOp.eval w op x y).val := by
  cases op <;> simp only [spec, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case ofNat => simp [NForm.val, NForm.natOp, WordOp.eval, IxCC.Src.WordResult.val]
  all_goals replace hx : x < w.size := hx.resolve_left (by simp)
  case convert w' =>
    by_cases h : w.bits ≤ w'.bits <;>
      simp [h, NForm.val, NForm.natOp, WordOp.eval, IxCC.Src.WordResult.val, Nat.mod_eq_of_lt hx]
  all_goals simp [NForm.val, NForm.natOp, WordOp.eval, IxCC.Src.WordResult.val, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy]

/-- Every operation of a primitive's formula is arithmetic. -/
theorem spec_ok (w : Width) (op : WordOp) {f : NForm} (hf : spec w op = some f) : f.ok = true := by
  cases op <;> simp only [spec, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
  case convert w' => by_cases h : w.bits ≤ w'.bits <;> simp [h, NForm.ok, NForm.arith]
  all_goals simp [NForm.ok, NForm.arith]

end IxCC.Grounding
