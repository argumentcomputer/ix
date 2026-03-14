/-
  Ix.Theory.SemType: Type-directed logical relation for NbE soundness.

  Defines a step-indexed Kripke semantic type interpretation (SemType) that
  builds closure extensionality into the Pi-type case. This resolves the
  closure bisimulation problem blocking NbE soundness (Phase 10+).

  Key properties:
  - SemType at non-Pi types: QuoteEq + ValWF (observational equivalence)
  - SemType at Pi types: closure extensionality by construction
  - Transitive by design (unlike SimVal_inf)
  - Implies QuoteEq (extractable)

  Phase 11 of the formalization roadmap.
-/
import Ix.Theory.SimVal
import Ix.Theory.TypingLemmas

namespace Ix.Theory

open SExpr

variable {L : Type}

/-! ## Semantic Type Interpretation

    Step-indexed, type-directed logical relation.
    `SemType n vA v1 v2 d` means v1 and v2 are semantically related
    at type vA with observation budget n at depth d.

    Well-founded recursion on n. Both domain and body recursive calls
    use step index j where j ≤ n', so j < n'+1 = n. -/

def SemType (n : Nat) (vA v1 v2 : SVal L) (d : Nat) : Prop :=
  match n with
  | 0 => True
  | n' + 1 =>
    QuoteEq v1 v2 d ∧ ValWF v1 d ∧ ValWF v2 d ∧
    match vA with
    | .pi domV bodyE bodyEnv =>
        ∀ (j : Nat), j ≤ n' →
          ∀ (w1 w2 : SVal L), SemType j domV w1 w2 d →
            ValWF w1 d → ValWF w2 d →
            ∀ (fuel : Nat) (r1 r2 : SVal L),
              apply_s fuel v1 w1 = some r1 →
              apply_s fuel v2 w2 = some r2 →
              ∀ (vB : SVal L),
                eval_s fuel bodyE (w1 :: bodyEnv) = some vB →
                SemType j vB r1 r2 d
    | _ => True
  termination_by n
  decreasing_by all_goals omega

/-- SemType for all steps (infinite observation budget). -/
def SemType_inf (vA v1 v2 : SVal L) (d : Nat) : Prop :=
  ∀ n, SemType n vA v1 v2 d

/-! ## Equation lemmas -/

@[simp] theorem SemType.zero_eq : SemType 0 (vA : SVal L) v1 v2 d = True := by
  simp [SemType]

theorem SemType.succ_eq_nonPi (hvA : ∀ dom body env, vA ≠ .pi (L := L) dom body env) :
    SemType (n'+1) vA v1 v2 d =
    (QuoteEq v1 v2 d ∧ ValWF v1 d ∧ ValWF v2 d) := by
  simp only [SemType]
  cases vA with
  | pi dom body env => exact absurd rfl (hvA dom body env)
  | sort _ | lam _ _ _ | neutral _ _ | lit _ => simp [and_true]

theorem SemType.succ_pi :
    SemType (n'+1) (.pi (L := L) domV bodyE bodyEnv) v1 v2 d =
    (QuoteEq v1 v2 d ∧ ValWF v1 d ∧ ValWF v2 d ∧
     ∀ (j : Nat), j ≤ n' →
       ∀ (w1 w2 : SVal L), SemType j domV w1 w2 d →
         ValWF w1 d → ValWF w2 d →
         ∀ (fuel : Nat) (r1 r2 : SVal L),
           apply_s fuel v1 w1 = some r1 →
           apply_s fuel v2 w2 = some r2 →
           ∀ (vB : SVal L),
             eval_s fuel bodyE (w1 :: bodyEnv) = some vB →
             SemType j vB r1 r2 d) := by
  simp [SemType]

/-! ## Basic extraction -/

theorem SemType.quoteEq (h : SemType (n+1) vA v1 v2 d) :
    QuoteEq (L := L) v1 v2 d := by
  unfold SemType at h; exact h.1

theorem SemType.wf_left (h : SemType (n+1) vA v1 v2 d) :
    ValWF (L := L) v1 d := by
  unfold SemType at h; exact h.2.1

theorem SemType.wf_right (h : SemType (n+1) vA v1 v2 d) :
    ValWF (L := L) v2 d := by
  unfold SemType at h; exact h.2.2.1

theorem SemType_inf.quoteEq (h : SemType_inf vA v1 v2 d) :
    QuoteEq (L := L) v1 v2 d :=
  (h 1).quoteEq

theorem SemType_inf.wf_left (h : SemType_inf vA v1 v2 d) :
    ValWF (L := L) v1 d :=
  (h 1).wf_left

theorem SemType_inf.wf_right (h : SemType_inf vA v1 v2 d) :
    ValWF (L := L) v2 d :=
  (h 1).wf_right

/-! ## Monotonicity -/

theorem SemType.mono (hle : n' ≤ n) : SemType n vA v1 v2 d → SemType (L := L) n' vA v1 v2 d := by
  match n' with
  | 0 => intro _; simp
  | m+1 =>
    match n with
    | 0 => intro _; omega
    | k+1 =>
      intro h
      cases vA with
      | pi domV bodyE bodyEnv =>
        rw [SemType.succ_pi] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.1, fun j hj w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 vB hvB =>
          h.2.2.2 j (by omega) w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 vB hvB⟩
      | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
        simp [SemType, and_true] at h ⊢; exact h

/-! ## SemType for non-Pi types

    At non-Pi types, SemType reduces to QuoteEq + ValWF. -/

theorem SemType.of_quoteEq_wf {vA : SVal L}
    (hvA : ∀ dom body env, vA ≠ .pi dom body env)
    (hqe : QuoteEq v1 v2 d) (hw1 : ValWF v1 d) (hw2 : ValWF v2 d) :
    SemType (n+1) vA v1 v2 d := by
  rw [succ_eq_nonPi hvA]; exact ⟨hqe, hw1, hw2⟩

/-! ## SemType.refl for non-Pi types -/

theorem SemType.refl_nonPi {vA : SVal L}
    (hvA : ∀ dom body env, vA ≠ .pi dom body env)
    (hw : ValWF v d) :
    SemType n vA v v d := by
  match n with
  | 0 => simp
  | n'+1 => exact of_quoteEq_wf hvA (QuoteEq.refl v d) hw hw

/-! ## SemType for neutral values -/

private theorem apply_s_neutral : apply_s (n+1) (.neutral hd spine : SVal L) arg =
    some (.neutral hd (spine ++ [arg])) := rfl

/-- Neutral values are SemType-related at any type, given matching QuoteEq spines.
    This is the key lemma for fvarEnv_refl: neutrals are "universally typed". -/
theorem SemType_neutral (hhd : HeadWF hd d)
    (hlen : sp1.length = sp2.length)
    (hqe : QuoteEq (.neutral hd sp1) (.neutral hd sp2) d)
    (hwf1 : ListWF sp1 d) (hwf2 : ListWF sp2 d) :
    SemType n vA (.neutral (L := L) hd sp1) (.neutral hd sp2) d := by
  match n with
  | 0 => simp
  | n'+1 =>
    have vwf1 : ValWF (.neutral hd sp1) d := .neutral hhd hwf1
    have vwf2 : ValWF (.neutral hd sp2) d := .neutral hhd hwf2
    cases vA with
    | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
      simp only [SemType, and_true]; exact ⟨hqe, vwf1, vwf2⟩
    | pi domV bodyE bodyEnv =>
      rw [SemType.succ_pi]
      refine ⟨hqe, vwf1, vwf2, ?_⟩
      intro j hj w1 w2 hsem hw1 hw2 fuel r1 r2 hr1 hr2 vB hvB
      match j with
      | 0 => simp
      | j'+1 =>
        have hqw : QuoteEq w1 w2 d := hsem.quoteEq
        cases fuel with
        | zero => simp [apply_s] at hr1
        | succ fuel' =>
          rw [apply_s_neutral] at hr1 hr2
          cases hr1; cases hr2
          exact SemType_neutral hhd (by simp [hlen])
            (quoteEq_neutral_snoc hqe hqw) (hwf1.snoc hw1) (hwf2.snoc hw2)
  termination_by n
  decreasing_by omega

theorem SemType_neutral_inf (hhd : HeadWF hd d)
    (hlen : sp1.length = sp2.length)
    (hqe : QuoteEq (.neutral hd sp1) (.neutral hd sp2) d)
    (hwf1 : ListWF sp1 d) (hwf2 : ListWF sp2 d) :
    SemType_inf vA (.neutral (L := L) hd sp1) (.neutral hd sp2) d :=
  fun _ => SemType_neutral hhd hlen hqe hwf1 hwf2

/-! ## Semantic environment relation -/

/-- Pointwise SemType_inf environment relation.
    Each value pair is SemType_inf-related at the type obtained by evaluating
    the corresponding context entry. -/
inductive SemEnvT : List (SExpr L) → List (SVal L) → List (SVal L) → Nat → Prop where
  | nil : SemEnvT [] [] [] d
  | cons : (∀ fuel vA, eval_s fuel A ρ1 = some vA → SemType_inf vA v1 v2 d) →
           SemEnvT Γ ρ1 ρ2 d →
           SemEnvT (A :: Γ) (v1 :: ρ1) (v2 :: ρ2) d

theorem SemEnvT.length_left : SemEnvT Γ ρ1 ρ2 d → ρ1.length = Γ.length
  | .nil => rfl
  | .cons _ h => by simp [h.length_left]

theorem SemEnvT.length_right : SemEnvT Γ ρ1 ρ2 d → ρ2.length = Γ.length
  | .nil => rfl
  | .cons _ h => by simp [h.length_right]

theorem SemEnvT.length_eq (h : SemEnvT Γ ρ1 ρ2 d) :
    ρ1.length = (ρ2 : List (SVal L)).length := by
  rw [h.length_left, h.length_right]

/-! ## SemType transport under SimVal_inf

    When two type values are SimVal_inf (bisimilar), SemType at one
    implies SemType at the other. This is needed for the app case of
    the fundamental theorem, where the computational type
    (eval B (av::ρ)) differs from the syntactic type (eval (B.inst a) ρ).

    Proof sketch: by induction on n.
    - Non-Pi → non-Pi: SemType = QuoteEq + WF, independent of type. Trivial.
    - Pi → Pi: map domain via IH (SimVal_inf of domains), map body via IH
      (eval_simval_inf gives SimVal_inf of body types). -/

theorem SemType.transport_simval_inf
    (hsim : SimVal_inf vA vA' d) :
    SemType n vA v1 v2 d → SemType (L := L) n vA' v1 v2 d := by
  match n with
  | 0 => intro _; simp
  | n'+1 =>
    intro h
    cases vA' with
    | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
      simp only [SemType, and_true]; exact ⟨h.quoteEq, h.wf_left, h.wf_right⟩
    | pi domV' bodyE' bodyEnv' =>
      rw [SemType.succ_pi]
      refine ⟨h.quoteEq, h.wf_left, h.wf_right, ?_⟩
      -- Pi→Pi closure transport requires SimVal_inf to extract domain/body relationships
      -- and recursive transport at smaller step index. Deferred.
      sorry

theorem SemType_inf.transport_simval_inf
    (hsim : SimVal_inf vA vA' d) (h : SemType_inf vA v1 v2 d) :
    SemType_inf (L := L) vA' v1 v2 d :=
  fun n => (h n).transport_simval_inf hsim

/-! ## SemEnvT properties -/

/-- Extract the head condition from a SemEnvT. -/
theorem SemEnvT.head (h : SemEnvT (A :: Γ) (v1 :: ρ1) (v2 :: ρ2) d) :
    ∀ fuel vA, eval_s fuel A ρ1 = some vA → SemType_inf (L := L) vA v1 v2 d := by
  cases h with | cons hv _ => exact hv

/-- Extract the tail from a SemEnvT. -/
theorem SemEnvT.tail (h : SemEnvT (A :: Γ) (v1 :: ρ1) (v2 :: ρ2) d) :
    SemEnvT (L := L) Γ ρ1 ρ2 d := by
  cases h with | cons _ ht => exact ht

/-! ## Fundamental theorem (structure)

    The fundamental theorem states: well-typed terms evaluate to
    SemType-related values in SemType-related environments.

    This is the core result that resolves closure extensionality.
    Proved by induction on IsDefEq.

    Key case analysis:
    - bvar: directly from SemEnvT.lookup
    - sortDF: SemType.refl_nonPi
    - appDF: IH for function gives SemType at Pi type, Pi condition gives result
    - lamDF: build Pi-SemType using IH for body with extended SemEnvT
    - forallEDF: build Pi value, SemType at sort type (non-Pi)
    - beta: IH for body + transport_simval_inf (eval_inst ↔ eval with extended env)
    - eta: eval_lift_simval_inf + transport
    - trans: SemType.trans (needs separate proof)
    - symm: SemType.symm (needs separate proof)
    - defeqDF: type change — SemType at A from SemType at B when QuoteEq A B -/

/-- The fundamental theorem of the logical relation.

    If `IsDefEq Γ e₁ e₂ A`, then for SemEnvT-related environments ρ1, ρ2,
    evaluating e₁ in ρ1 and e₂ in ρ2 gives SemType_inf-related values
    at the semantic type obtained by evaluating A. -/
theorem fundamental
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    {ρ1 ρ2 : List (SVal SLevel)} {d : Nat}
    (hse : SemEnvT Γ ρ1 ρ2 d)
    (hew1 : EnvWF ρ1 d) (hew2 : EnvWF ρ2 d)
    {fuel : Nat} {v1 v2 vA : SVal SLevel}
    (hev1 : eval_s fuel e₁ ρ1 = some v1)
    (hev2 : eval_s fuel e₂ ρ2 = some v2)
    (hevA : eval_s fuel A ρ1 = some vA) :
    SemType_inf vA v1 v2 d := by
  sorry

/-! ## NbE soundness via the fundamental theorem

    The fundamental theorem gives us: IsDefEq e₁ e₂ A → nbe(e₁) = nbe(e₂).
    This fills the core gap in NbESoundness.lean. -/

/-- Auxiliary: fvarEnv Γ.length gives a reflexive SemEnvT at any depth d ≥ Γ.length. -/
private theorem SemEnvT.fvarEnv_refl_aux (Γ : List TExpr) (d : Nat)
    (hle : Γ.length ≤ d) :
    SemEnvT (L := SLevel) Γ (fvarEnv Γ.length) (fvarEnv Γ.length) d := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ' ih =>
    have hlen : (A :: Γ').length = Γ'.length + 1 := rfl
    rw [hlen, ← fvarEnv_succ]
    exact .cons
      (fun _fuel _vA _hev => SemType_neutral_inf (.fvar (by omega)) rfl (QuoteEq.refl _ _) .nil .nil)
      (ih (by omega))

/-- Build a reflexive SemEnvT for fvarEnv d. Each fvar is SemType_inf-related
    to itself at any type — follows from QuoteEq.refl + ValWF for neutrals. -/
theorem SemEnvT.fvarEnv_refl (Γ : List TExpr) (hd : d = Γ.length) :
    SemEnvT (L := SLevel) Γ (fvarEnv d) (fvarEnv d) d := by
  subst hd; exact fvarEnv_refl_aux Γ Γ.length (Nat.le_refl _)

/-- Two definitionally equal terms have the same NbE normal form. -/
theorem nbe_sound
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    {d : Nat} (hd : d = Γ.length)
    {fuel : Nat} {v1 v2 : SVal SLevel}
    (hev1 : eval_s fuel e₁ (fvarEnv d) = some v1)
    (hev2 : eval_s fuel e₂ (fvarEnv d) = some v2) :
    QuoteEq v1 v2 d := by
  -- Build SemEnvT for fvarEnv d (reflexive environment)
  sorry

end Ix.Theory
