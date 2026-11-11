module

public import IxC.Kernel.Model.Denotes
public import IxC.Kernel.Model.NatStep

public section

/-!
# The `Nat` operations on literals, read off the invariant

`NatLitLaw` (`IxC/Kernel/Denotes.lean`) from the invariant's recurrence laws
(`EnvModelM.nat_ops` for the structural operations, `EnvModelM.div_mod` for the
well-founded ones) through the literal transports `natOpV_*` (`Model/NatSem.lean`,
`Model/NatWf.lean`), which compute each operation's leaf at every pair of numeral spines —
with no exponent cap, unlike the kernel's own reduction of `Nat.pow` (`natOpResult`).

A literal denotes the interpretation of its numeral spine (`Denotes.natLit` and
`Denotes_natLitToConstructor`), and a stored operation's constant denotes its leaf, so an
application to two literals denotes the leaf at the two spines, which the transport
computes.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel.Term
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal ReducibilityHint Denotes
  natLitSupported)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env md}

/-- A literal denotes the interpretation of its numeral spine. -/
theorem denotes_natLit_eq {acval : Key md → (LevelParam → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {φ : LevelParam → Nat}
    (hs : natLitSupported env = true) {ρ : Nat → V} {n : Nat} {X : V}
    (h : Denotes (cvalOf (V := V) acval) env φ ρ (.lit (.natVal n)) X) :
    X = interp V ρ (natLitAV (acval Ix.Kernel.natZeroName (Level.substFn φ [] []))
      (acval Ix.Kernel.natSuccName (Level.substFn φ [] [])) n) :=
  Ix.Kernel.Denotes_functional h (Denotes.natLit (Denotes_natLitToConstructor hcl hs ρ n))

/-- A constant stored without universe parameters, used at none. -/
theorem denotes_const_nil {cval : Key md → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ : Nat → V} {n : Key md} {ci : ConstantInfo md}
    (hf : env.find? n = some ci) (h0 : ci.toConstantVal.levelParams = []) :
    Denotes cval env φ ρ (.const n []) (cval n (Level.substFn φ [] [])) := by
  have h := Denotes.const (cval := cval) (env := env) (φ := φ) (ρ := ρ) hf
    (us := []) (by rw [h0]; rfl)
  rwa [h0] at h

/-- **A stored operation of the fifteen, applied to literals, denotes its leaf at the two
numeral spines**; the `Nat` literals are supported, and the operation and its
dependencies are stored without universe parameters (`natOpGuard`). -/
theorem natOp_app2_inv (m : EnvModelM V μ env) {c : Key md} {cv : ConstantVal md}
    {v : Expr md} {hint : ReducibilityHint}
    (hmem : c ∈ Ix.Kernel.natOpNames ∨ c ∈ Ix.Kernel.natDivModNames)
    (hself : c ∈ Ix.Kernel.natOpDeps c)
    (hf : env.find? c = some (.defnInfo cv v hint)) {φ : LevelParam → Nat} {ρ : Nat → V}
    {a b : Nat} {X : V}
    (h : Denotes (cvalOf (V := V) m.base2.acval) env φ ρ
      (.app (.app (.const c []) (.lit (.natVal a))) (.lit (.natVal b))) X) :
    Ix.Kernel.natOpGuard env c = true ∧
    X = SetTheory.app (SetTheory.app
        (interp V ρ (m.base2.acval c (Level.substFn φ [] [])))
        (interp V ρ (natLit m.base2 (Level.substFn φ [] []) a)))
      (interp V ρ (natLit m.base2 (Level.substFn φ [] []) b)) := by
  have hcl := m.base2.cval_closedL
  have hg := natOpGuardLaw_of m c hmem (by simp [Ix.Kernel.natOpStored, hf])
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvc, vc, hc, hfc, hlpc⟩ := hdeps c hself
  rw [hf] at hfc
  obtain ⟨rfl, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfc)
  refine ⟨hg, ?_⟩
  cases h with
  | app hfa hb =>
    cases hfa with
    | app hc0 ha =>
      have hc1 := denotes_const_nil (cval := cvalOf (V := V) m.base2.acval) (φ := φ) (ρ := ρ)
        hf hlpc
      (rw [Ix.Kernel.Denotes_functional hc0 hc1, denotes_natLit_eq hcl hs ha,
        denotes_natLit_eq hcl hs hb, interp_cvalOf hcl]) <;> rfl

/-- `natOp_app2_inv` for the unary `Nat.pred`. -/
theorem natOp_app1_inv (m : EnvModelM V μ env) {cv : ConstantVal md}
    {v : Expr md} {hint : ReducibilityHint}
    (hf : env.find? Ix.Kernel.natPredName = some (.defnInfo cv v hint)) {φ : LevelParam → Nat}
    {ρ : Nat → V} {a : Nat} {X : V}
    (h : Denotes (cvalOf (V := V) m.base2.acval) env φ ρ
      (.app (.const Ix.Kernel.natPredName []) (.lit (.natVal a))) X) :
    natLitSupported env = true ∧
    X = SetTheory.app (interp V ρ (m.base2.acval Ix.Kernel.natPredName (Level.substFn φ [] [])))
      (interp V ρ (natLit m.base2 (Level.substFn φ [] []) a)) := by
  have hcl := m.base2.cval_closedL
  have hg := natOpGuardLaw_of m Ix.Kernel.natPredName (Or.inl (by cases md <;> decide))
    (by simp [Ix.Kernel.natOpStored, hf])
  obtain ⟨hs, hdeps, -⟩ := Ix.Kernel.natOpGuard_inv hg
  obtain ⟨cvc, vc, hc, hfc, hlpc⟩ := hdeps Ix.Kernel.natPredName (by cases md <;> decide)
  rw [hf] at hfc
  obtain ⟨rfl, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfc)
  refine ⟨hs, ?_⟩
  cases h with
  | app hc0 ha =>
    have hc1 := denotes_const_nil (cval := cvalOf (V := V) m.base2.acval) (φ := φ) (ρ := ρ)
      hf hlpc
    (rw [Ix.Kernel.Denotes_functional hc0 hc1, denotes_natLit_eq hcl hs ha, interp_cvalOf hcl])
      <;> rfl

set_option maxHeartbeats 1600000 in
/-- **The `Nat` operations on literals, from the invariant.** -/
theorem natLitLaw_of_envModelM (m : EnvModelM V μ env) :
    Ix.Kernel.NatLitLaw (cvalOf (V := V) m.base2.acval) env := by
  have hcl := m.base2.cval_closedL
  refine ⟨?_, ?_, ?_⟩
  · -- `Nat.pred`
    intro cv v hint hf φ ρ a X h
    obtain ⟨hs, hX⟩ := natOp_app1_inv m hf h
    rw [hX, natOpV_pred m.base2 (m.nat_ops (Level.substFn φ [] []))
      (m.nat_heads (Level.substFn φ [] [])) m.acvalValid hf ρ a]
    exact Denotes.natLit (Denotes_natLitToConstructor hcl hs ρ (a - 1))
  · -- the twelve arithmetic operations
    intro c f hmem cv v hint hf φ ρ a b X h
    have key : (c ∈ Ix.Kernel.natOpNames ∨ c ∈ Ix.Kernel.natDivModNames) →
        c ∈ Ix.Kernel.natOpDeps c →
        (∀ ψ : LevelParam → Nat, SetTheory.app (SetTheory.app
            (interp V ρ (m.base2.acval c ψ)) (interp V ρ (natLit m.base2 ψ a)))
            (interp V ρ (natLit m.base2 ψ b)) = interp V ρ (natLit m.base2 ψ (f a b))) →
        Denotes (cvalOf (V := V) m.base2.acval) env φ ρ (.lit (.natVal (f a b))) X := by
      intro hmemN hself hop
      obtain ⟨hg, hX⟩ := natOp_app2_inv m hmemN hself hf h
      obtain ⟨hs, -, -⟩ := Ix.Kernel.natOpGuard_inv hg
      rw [hX, hop]
      exact Denotes.natLit (Denotes_natLitToConstructor hcl hs ρ (f a b))
    simp only [Ix.Kernel.natArithOps, List.mem_cons, List.mem_nil_iff, or_false,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key (Or.inl (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_add m.base2 (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid hf ρ a b
    · exact key (Or.inl (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_sub m.base2 (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid hf ρ a b
    · exact key (Or.inl (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_mul m.base2 (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid hf ρ a b
    · exact key (Or.inl (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_pow m.base2 (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_div (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_mod (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_gcd (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_land (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_lor (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_xor (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_shiftLeft (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf
          ρ a b
    · exact key (Or.inr (by cases md <;> decide)) (by cases md <;> decide)
        fun ψ => natOpV_shiftRight (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid (m.div_mod ψ) hf
          ρ a b
  · -- the two comparisons
    intro c f hmem cv v hint hf φ ρ a b X h
    have key : (c = Ix.Kernel.natBeqName ∨ c = Ix.Kernel.natBleName) →
        c ∈ Ix.Kernel.natOpDeps c →
        (∀ ψ : LevelParam → Nat, SetTheory.app (SetTheory.app
            (interp V ρ (m.base2.acval c ψ)) (interp V ρ (natLit m.base2 ψ a)))
            (interp V ρ (natLit m.base2 ψ b))
          = interp V ρ (m.base2.acval
              (if f a b then Ix.Kernel.boolTrueName else Ix.Kernel.boolFalseName) ψ)) →
        Denotes (cvalOf (V := V) m.base2.acval) env φ ρ
          (.const (if f a b then Ix.Kernel.boolTrueName else Ix.Kernel.boolFalseName) []) X := by
      intro hcb hself hop
      have hmemN : c ∈ Ix.Kernel.natOpNames ∨ c ∈ Ix.Kernel.natDivModNames := by
        rcases hcb with rfl | rfl
        · exact Or.inl (by cases md <;> decide)
        · exact Or.inl (by cases md <;> decide)
      obtain ⟨hg, hX⟩ := natOp_app2_inv m hmemN hself hf h
      obtain ⟨-, -, hbool⟩ := Ix.Kernel.natOpGuard_inv hg
      obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ :=
        hbool (by rcases hcb with h | h
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h))
      rw [hX, hop, interp_cvalOf hcl]
      split
      · exact denotes_const_nil hfT hlpT
      · exact denotes_const_nil hfF hlpF
    simp only [Ix.Kernel.natCmpOps, List.mem_cons, List.mem_nil_iff, or_false,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine key (Or.inl rfl) (by cases md <;> decide) fun ψ => ?_
      rw [natOpV_beq m.base2 (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid hf ρ a b]
      cases hb : Nat.beq a b
      · rw [if_neg (Nat.ne_of_beq_eq_false hb), if_neg (by decide)]
      · rw [if_pos (Nat.eq_of_beq_eq_true hb), if_pos rfl]
    · refine key (Or.inr rfl) (by cases md <;> decide) fun ψ => ?_
      rw [natOpV_ble m.base2 (m.nat_ops ψ) (m.nat_heads ψ) m.acvalValid hf ρ a b]
      cases hb : Nat.ble a b
      · rw [if_neg (Nat.not_le_of_not_ble_eq_true (by rw [hb]; decide)),
          if_neg (by decide)]
      · rw [if_pos (Nat.le_of_ble_eq_true hb), if_pos rfl]

end Ix.Kernel.Model
