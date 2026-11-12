import IxCCGrounding.Subst
import IxCCGrounding.Facts

/-!
# From #678's fields to the canonicity-free laws (`IxCCGrounding.Adapt678`)

`LawsNoCanon M`, the five laws the canonicity-free root theorems take, from `Laws678 M`, verbatim
copies of the corresponding fields of #678's public `Model` (`IxCCGrounding.Laws`, with the source
commit and line ranges):

| `LawsNoCanon` field | from | by |
| --- | --- | --- |
| `defn_value` | `defn_value` | the same statement (`Laws678.defnValue`) |
| `iota_rule` (`IotaLawG`) | `iota_rule` | its graded conjunct dropped (`IotaLaw678.toG`) |
| `cval_params` | `cval_params` | the same statement (`Laws678.cvalParams`) |
| `proj_ctor` | `proj_law` | its value part at the constructor's own level parameters (`projCtor_of_projLaw`) |
| `nat_accel` | `lit_ops` | at a reading where every `Nat` role stored is a definition, `LitDefs` (`natAccel_of_litOps`) |

`lawsNoCanon_of_678` puts them together. No law beyond the copied fields is assumed: the projection
adapter instantiates #678's law at `entry.levelParams.map .param`, where the level substitution is
the assignment itself (`substFn_self`) and the constructor's instantiated type is its stored one
(`inst_self`), and our premise that the structure's sort is not zero discharges #678's `Prop` guard
(its sort is the table's structure sort, read off the stored type by `finalSort_of_stripPis`); the
`Nat` adapter reads the role's stored constant off the denotation it is given (a role that is not
stored names nothing that denotes) and identifies SrcEval's `PrimOp.eval2` with the Lean function
#678's tables name at each of the fifteen roles.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- A stored type's final sort is read past any number of its leading `∀`s. -/
theorem finalSort_of_stripPis : ∀ {n : Nat} {t r : KExpr} {bs : List (KExpr × BinderMeta)},
    t.stripPis n = some (bs, r) → finalSort t = finalSort r
  | 0, t, r, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
  | n + 1, t, r, bs, h => by
    cases t with
    | forallE ty b m =>
      simp only [Expr.stripPis] at h
      cases hb : b.stripPis n with
      | none => rw [hb] at h; cases h
      | some p =>
        obtain ⟨bs', r'⟩ := p
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [finalSort]
        exact finalSort_of_stripPis hb
    | _ => simp [Expr.stripPis] at h

/-- **The projection of a constructor, from #678's `proj_law`**: its value part read at the
constructor's own level parameters, whose `Prop` guard (structure sort zero implies field sort zero)
holds vacuously where the structure's sort is not zero. No other law. -/
theorem projCtor_of_projLaw (h : ProjLaw M.cval env) : ProjCtor M := by
  intro T i entry cvC nP nF cvT caps s φ ρ σ R Ps Fs Y hent hC hT hs hne hPl hFl hfit hY
  obtain ⟨hlps, ⟨bs, hstrip⟩, cvC', hC', hClps, -, hval⟩ := h T i entry cvT caps hent hT
  rw [hC] at hC'
  simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hC'
  obtain ⟨rfl, rfl, rfl⟩ := hC'
  have hss : s = entry.structSort := by
    have h1 := finalSort_of_stripPis hstrip
    rw [hs] at h1
    simpa [finalSort] using h1
  have hsub : Level.substFn φ entry.levelParams (entry.levelParams.map Level.param) = φ :=
    substFn_self φ entry.levelParams
  have hF : Denotes M.cval env φ ρ (.const T (entry.levelParams.map Level.param)) (M.cval T φ) := by
    have h1 := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ)
      (us := entry.levelParams.map Level.param) hT (by simp [ConstantInfo.toConstantVal, hlps])
    simpa only [ConstantInfo.toConstantVal, hlps, hsub] using h1
  have hK : Denotes M.cval env φ ρ (.const entry.ctor (entry.levelParams.map Level.param))
      (M.cval entry.ctor φ) := by
    have h1 := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ)
      (us := entry.levelParams.map Level.param) hC (by simp [ConstantInfo.toConstantVal, hClps])
    simpa only [ConstantInfo.toConstantVal, hClps, hsub] using h1
  obtain ⟨hproj, -⟩ := hval (entry.levelParams.map Level.param) φ ρ _ _ (by simp) hF hK
  have hget : (Ps ++ Fs).getD (entry.numParams + i) empty = Y := by
    rw [List.getD_eq_getElem?_getD, ← hPl, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, hY, Option.getD_some]
  have hguard : Level.eval (Level.substFn φ entry.levelParams (entry.levelParams.map Level.param))
      entry.structSort = 0 →
      Level.eval (Level.substFn φ entry.levelParams (entry.levelParams.map Level.param))
        entry.fieldSort = 0 := by
    rw [hsub, ← hss]
    intro h0
    exact absurd h0 hne
  have hfit' : Fits M.cval env φ ρ
      (cvC.type.instantiateLevelParams cvC.levelParams (entry.levelParams.map Level.param))
      (Ps ++ Fs) σ R := by
    rw [hClps, inst_self]
    exact hfit
  rw [hproj hguard σ R (Ps ++ Fs) (by simp [hPl, hFl]) hfit', hget]

/-- `PrimOp.eval2`'s `if` at division is Lean's `Nat.div` (`a / 0 = 0`). -/
theorem eval2_div (a b : Nat) : (if (b == 0) = true then 0 else a / b) = Nat.div a b := by
  split
  · rename_i h
    rw [beq_iff_eq.mp h]
    exact (Nat.div_zero a).symm
  · rfl

/-- `PrimOp.eval2`'s `if` at remainder is Lean's `Nat.mod` (`a % 0 = a`). -/
theorem eval2_mod (a b : Nat) : (if (b == 0) = true then a else a % b) = Nat.mod a b := by
  split
  · rename_i h
    rw [beq_iff_eq.mp h]
    exact (Nat.mod_zero a).symm
  · rfl

/-- `PrimOp.eval2`'s shift left is Lean's `Nat.shiftLeft`. -/
theorem eval2_shiftLeft (a b : Nat) : a * 2 ^ b = Nat.shiftLeft a b :=
  (Nat.shiftLeft_eq a b).symm

/-- `PrimOp.eval2`'s shift right (`0` once the exponent passes the logarithm) is Lean's
`Nat.shiftRight`. -/
theorem eval2_shiftRight (a b : Nat) :
    (if a.log2 < b then 0 else a / 2 ^ b) = Nat.shiftRight a b := by
  show _ = a >>> b
  rw [Nat.shiftRight_eq_div_pow]
  split
  · rename_i hlt
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · exact (Nat.div_eq_of_lt ((Nat.log2_lt (by omega)).mp hlt)).symm
  · rfl

/-- `PrimOp.eval2`'s equality test is Lean's `Nat.beq`. -/
theorem eval2_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

/-- `PrimOp.eval2`'s order test is Lean's `Nat.ble`. -/
theorem eval2_ble (a b : Nat) : decide (a ≤ b) = Nat.ble a b := by
  cases h : Nat.ble a b
  · simp only [decide_eq_false_iff_not]
    intro hle
    rw [Nat.ble_eq_true_of_le hle] at h
    cases h
  · simp [Nat.le_of_ble_eq_true h]

/-- **The `Nat` operations on literals, from #678's `lit_ops`**, at a reading where every `Nat`
role it stores is stored as a definition (`LitDefs`). A role the reading does not store needs
nothing: the denotation the law is asked at names the role's key, so the key is stored (the
`Denotes.const` premise read off below), and `LitDefs` makes it a definition, which is what
`lit_ops` asks. Then `PrimOp.eval2` is the Lean function #678's tables name, role by role. -/
theorem natAccel_of_litOps (h : NatLitLaw M.cval env) (hd : LitDefs env) : NatAccel M := by
  obtain ⟨hpred, harith, hcmp⟩ := h
  intro op a b φ ρ X _ hden
  -- the role's key is stored: the term the law is asked at names it, and denotes
  have hst : ∃ ci, env.find? (primKey op) = some ci := by
    unfold primApp at hden
    split at hden
    · cases hden with
      | app hf _ => cases hf with
        | const hf _ => exact ⟨_, hf⟩
    · cases hden with
      | app hf _ => cases hf with
        | app hf' _ => cases hf' with
          | const hf _ => exact ⟨_, hf⟩
  obtain ⟨ci, hci⟩ := hst
  obtain ⟨cv, v, hint, rfl⟩ := hd op ci hci
  -- a binary role with a `Nat` value
  have arith : ∀ f : Nat → Nat → Nat, (primKey op, f) ∈ (natArithOps : List (KKey × _)) →
      op.arity = 2 → op.eval2 a b = .nat (f a b) →
      Denotes M.cval env φ ρ (primResultE (op.eval2 a b)) X := by
    intro f hmem har hev
    rw [hev]
    have hden' : Denotes M.cval env φ ρ
        (.app (.app (.const (primKey op) []) (.lit (.natVal a))) (.lit (.natVal b))) X := by
      simpa [primApp, har, litE] using hden
    exact harith (primKey op) f hmem cv v hint hci φ ρ a b X hden'
  -- a binary role with a `Bool` value
  have cmp : ∀ f : Nat → Nat → Bool, (primKey op, f) ∈ (natCmpOps : List (KKey × _)) →
      op.arity = 2 → op.eval2 a b = .bool (f a b) →
      Denotes M.cval env φ ρ (primResultE (op.eval2 a b)) X := by
    intro f hmem har hev
    rw [hev]
    have hden' : Denotes M.cval env φ ρ
        (.app (.app (.const (primKey op) []) (.lit (.natVal a))) (.lit (.natVal b))) X := by
      simpa [primApp, har, litE] using hden
    have h1 := hcmp (primKey op) f hmem cv v hint hci φ ρ a b X hden'
    cases hfab : f a b <;> rw [hfab] at h1 <;> exact h1
  cases op with
  | add => exact arith Nat.add (by simp [natArithOps, primKey]) rfl rfl
  | sub => exact arith Nat.sub (by simp [natArithOps, primKey]) rfl rfl
  | mul => exact arith Nat.mul (by simp [natArithOps, primKey]) rfl rfl
  | div =>
    exact arith Nat.div (by simp [natArithOps, primKey]) rfl
      (by simp only [IxCC.Src.PrimOp.eval2, eval2_div])
  | mod =>
    exact arith Nat.mod (by simp [natArithOps, primKey]) rfl
      (by simp only [IxCC.Src.PrimOp.eval2, eval2_mod])
  | pow => exact arith Nat.pow (by simp [natArithOps, primKey]) rfl rfl
  | gcd => exact arith Nat.gcd (by simp [natArithOps, primKey]) rfl rfl
  | beq =>
    exact cmp Nat.beq (by simp [natCmpOps, primKey]) rfl
      (by simp only [IxCC.Src.PrimOp.eval2, eval2_beq])
  | ble =>
    exact cmp Nat.ble (by simp [natCmpOps, primKey]) rfl
      (by simp only [IxCC.Src.PrimOp.eval2, eval2_ble])
  | land => exact arith Nat.land (by simp [natArithOps, primKey]) rfl rfl
  | lor => exact arith Nat.lor (by simp [natArithOps, primKey]) rfl rfl
  | xor => exact arith Nat.xor (by simp [natArithOps, primKey]) rfl rfl
  | shiftLeft =>
    exact arith Nat.shiftLeft (by simp [natArithOps, primKey]) rfl
      (by simp only [IxCC.Src.PrimOp.eval2, eval2_shiftLeft])
  | shiftRight =>
    exact arith Nat.shiftRight (by simp [natArithOps, primKey]) rfl
      (by simp only [IxCC.Src.PrimOp.eval2, eval2_shiftRight])
  | pred =>
    have hden' : Denotes M.cval env φ ρ (.app (.const natPredName []) (.lit (.natVal a))) X := by
      simpa [primApp, IxCC.Src.PrimOp.arity, primKey, litE] using hden
    exact hpred cv v hint hci φ ρ a X hden'

/-- **#678's fields give the canonicity-free laws**, at a reading whose stored `Nat` roles are
definitions (`LitDefs`, decided by `litDefsB`). -/
theorem lawsNoCanon_of_678 (hL : Laws678 M) (hd : LitDefs env) : LawsNoCanon M :=
  ⟨hL.defnValue, hL.iota_rule.toG, hL.cvalParams, projCtor_of_projLaw hL.proj_law,
    natAccel_of_litOps hL.lit_ops hd⟩

end IxCC.Grounding
