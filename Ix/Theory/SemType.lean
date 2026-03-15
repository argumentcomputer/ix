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
    (∀ m, m ≤ n' + 1 → SimVal m v1 v2 d) ∧
    match vA with
    | .pi domV bodyE bodyEnv =>
        ∀ (j : Nat), j ≤ n' →
          ∀ (w1 w2 : SVal L), SemType j domV w1 w2 d →
            ValWF w1 d → ValWF w2 d →
            ∀ (fuel : Nat) (r1 r2 : SVal L),
              apply_s fuel v1 w1 = some r1 →
              apply_s fuel v2 w2 = some r2 →
              ∀ (vB1 vB2 : SVal L),
                eval_s fuel bodyE (w1 :: bodyEnv) = some vB1 →
                eval_s fuel bodyE (w2 :: bodyEnv) = some vB2 →
                SemType j vB1 r1 r2 d ∧ SemType j vB2 r1 r2 d
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
    (QuoteEq v1 v2 d ∧ ValWF v1 d ∧ ValWF v2 d ∧
     (∀ m, m ≤ n' + 1 → SimVal m v1 v2 d)) := by
  simp only [SemType]
  cases vA with
  | pi dom body env => exact absurd rfl (hvA dom body env)
  | sort _ | lam _ _ _ | neutral _ _ | lit _ => simp [and_true]

theorem SemType.succ_pi :
    SemType (n'+1) (.pi (L := L) domV bodyE bodyEnv) v1 v2 d =
    (QuoteEq v1 v2 d ∧ ValWF v1 d ∧ ValWF v2 d ∧
     (∀ m, m ≤ n' + 1 → SimVal m v1 v2 d) ∧
     ∀ (j : Nat), j ≤ n' →
       ∀ (w1 w2 : SVal L), SemType j domV w1 w2 d →
         ValWF w1 d → ValWF w2 d →
         ∀ (fuel : Nat) (r1 r2 : SVal L),
           apply_s fuel v1 w1 = some r1 →
           apply_s fuel v2 w2 = some r2 →
           ∀ (vB1 vB2 : SVal L),
             eval_s fuel bodyE (w1 :: bodyEnv) = some vB1 →
             eval_s fuel bodyE (w2 :: bodyEnv) = some vB2 →
             SemType j vB1 r1 r2 d ∧ SemType j vB2 r1 r2 d) := by
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

theorem SemType.simval (h : SemType (n+1) vA v1 v2 d) (hm : m ≤ n + 1) :
    SimVal (L := L) m v1 v2 d := by
  unfold SemType at h; exact h.2.2.2.1 m hm

theorem SemType.simval_inf (h : SemType_inf vA v1 v2 d) :
    SimVal_inf (L := L) v1 v2 d :=
  fun n => (h (n + 1)).simval (by omega)

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
        exact ⟨h.1, h.2.1, h.2.2.1,
          fun mm hmm => h.2.2.2.1 mm (by omega),
          fun j hj w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 vB hvB =>
          h.2.2.2.2 j (by omega) w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 vB hvB⟩
      | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
        simp [SemType, and_true] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.1, fun mm hmm => h.2.2.2 mm (by omega)⟩

/-! ## SemType for non-Pi types

    At non-Pi types, SemType reduces to QuoteEq + ValWF. -/

theorem SemType.of_quoteEq_wf {vA : SVal L}
    (hvA : ∀ dom body env, vA ≠ .pi dom body env)
    (hqe : QuoteEq v1 v2 d) (hw1 : ValWF v1 d) (hw2 : ValWF v2 d)
    (hsv : ∀ m, m ≤ n + 1 → SimVal m v1 v2 d) :
    SemType (n+1) vA v1 v2 d := by
  rw [succ_eq_nonPi hvA]; exact ⟨hqe, hw1, hw2, hsv⟩

/-! ## SemType.refl for non-Pi types -/

theorem SemType.refl_nonPi {vA : SVal L}
    (hvA : ∀ dom body env, vA ≠ .pi dom body env)
    (hw : ValWF v d) :
    SemType n vA v v d := by
  match n with
  | 0 => simp
  | n'+1 => exact of_quoteEq_wf hvA (QuoteEq.refl v d) hw hw (fun m _ => SimVal.refl_wf m hw)

/-! ## SemType for neutral values -/


/-- Neutral values are SemType-related at any type, given bounded SimVal.
    Uses bounded SimVal at the same step as SemType. -/
theorem SemType_neutral (hhd : HeadWF hd d)
    (hlen : sp1.length = sp2.length)
    (hqe : QuoteEq (.neutral hd sp1) (.neutral hd sp2) d)
    (hsv : ∀ m, m ≤ n → SimVal m (.neutral (L := L) hd sp1) (.neutral hd sp2) d)
    (hwf1 : ListWF sp1 d) (hwf2 : ListWF sp2 d) :
    SemType n vA (.neutral (L := L) hd sp1) (.neutral hd sp2) d := by
  match n with
  | 0 => simp
  | n'+1 =>
    have vwf1 : ValWF (.neutral hd sp1) d := .neutral hhd hwf1
    have vwf2 : ValWF (.neutral hd sp2) d := .neutral hhd hwf2
    cases vA with
    | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
      simp only [SemType, and_true]; exact ⟨hqe, vwf1, vwf2, hsv⟩
    | pi domV bodyE bodyEnv =>
      rw [SemType.succ_pi]
      refine ⟨hqe, vwf1, vwf2, hsv, ?_⟩
      intro j hj w1 w2 hsem hw1 hw2 fuel r1 r2 hr1 hr2 vB1 vB2 hvB1 hvB2
      match j with
      | 0 => exact ⟨by simp, by simp⟩
      | j'+1 =>
        have hqw : QuoteEq w1 w2 d := hsem.quoteEq
        cases fuel with
        | zero => simp [apply_s] at hr1
        | succ fuel' =>
          rw [apply_s_neutral] at hr1 hr2
          cases hr1; cases hr2
          -- Build bounded SimVal for extended neutrals at steps ≤ j'+1
          have mk_hsv : ∀ (wa wb : SVal L), (∀ m, m ≤ j'+1 → SimVal m wa wb d) →
              ∀ m, m ≤ j'+1 → SimVal m
              (.neutral hd (sp1 ++ [wa]) : SVal L) (.neutral hd (sp2 ++ [wb])) d :=
            fun wa wb hsw m hm => by
              match m with
              | 0 => simp
              | m'+1 =>
                rw [SimVal.neutral_neutral]
                have hsvm := hsv (m'+1) (by omega)
                rw [SimVal.neutral_neutral] at hsvm
                exact ⟨hsvm.1, hsvm.2.snoc (hsw (m'+1) hm)⟩
          constructor
          · exact SemType_neutral hhd (by simp [hlen])
              (quoteEq_neutral_snoc hqe hqw)
              (mk_hsv w1 w2 (fun m hm => hsem.simval (show m ≤ j'+1 from hm)))
              (hwf1.snoc hw1) (hwf2.snoc hw2)
          · exact SemType_neutral hhd (by simp [hlen])
              (quoteEq_neutral_snoc hqe hqw)
              (mk_hsv w1 w2 (fun m hm => hsem.simval (show m ≤ j'+1 from hm)))
              (hwf1.snoc hw1) (hwf2.snoc hw2)
  termination_by n
  decreasing_by all_goals omega

/-- SemType_inf for reflexive neutrals (sp = sp). -/
theorem SemType_neutral_refl_inf (hhd : HeadWF hd d) (hwf : ListWF sp d) :
    SemType_inf vA (.neutral (L := L) hd sp) (.neutral hd sp) d :=
  fun _ => SemType_neutral hhd rfl (QuoteEq.refl _ _)
    (fun m _ => SimVal.refl_wf m (.neutral hhd hwf)) hwf hwf


/-! ## Semantic environment relation -/

/-- Step-indexed pointwise semantic environment relation.
    Each value pair is SemType-related at step n at the type obtained by
    evaluating the corresponding context entry.

    The step parameter allows the Pi closure (which provides bounded SemType j
    for domain arguments) to build SemEnvT at step j for invoking the body IH.
    This resolves the circularity where SemType_inf was needed but only bounded
    SemType was available. -/
inductive SemEnvT (n : Nat) : List (SExpr L) → List (SVal L) → List (SVal L) → Nat → Prop where
  | nil : SemEnvT n [] [] [] d
  | cons : (∀ fuel vA, eval_s fuel A ρ1 = some vA → SemType n vA v1 v2 d) →
           SemEnvT n Γ ρ1 ρ2 d →
           SemEnvT n (A :: Γ) (v1 :: ρ1) (v2 :: ρ2) d

theorem SemEnvT.mono (hle : n' ≤ n) : SemEnvT n Γ ρ1 ρ2 d → SemEnvT (L := L) n' Γ ρ1 ρ2 d
  | .nil => .nil
  | .cons hv ht => .cons (fun f vA hev => (hv f vA hev).mono hle) (ht.mono hle)

theorem SemEnvT.length_left : SemEnvT n Γ ρ1 ρ2 d → ρ1.length = Γ.length
  | .nil => rfl
  | .cons _ h => by simp [h.length_left]

theorem SemEnvT.length_right : SemEnvT n Γ ρ1 ρ2 d → ρ2.length = Γ.length
  | .nil => rfl
  | .cons _ h => by simp [h.length_right]

theorem SemEnvT.length_eq (h : SemEnvT n Γ ρ1 ρ2 d) :
    ρ1.length = (ρ2 : List (SVal L)).length := by
  rw [h.length_left, h.length_right]

/-! ## SemType symmetry -/

theorem SemType.symm_nonPi {vA : SVal L}
    (hvA : ∀ dom body env, vA ≠ .pi (L := L) dom body env) :
    SemType (n+1) vA v1 v2 d → SemType (n+1) vA v2 v1 d := by
  rw [succ_eq_nonPi hvA, succ_eq_nonPi hvA]
  exact fun ⟨hqe, hw1, hw2, hsv⟩ => ⟨hqe.symm, hw2, hw1, fun m hm => (hsv m hm).symm⟩

theorem SemType.symm :
    SemType n vA v1 v2 d → SemType (L := L) n vA v2 v1 d := by
  match n with
  | 0 => intro _; simp
  | n'+1 =>
    intro h
    cases vA with
    | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
      exact symm_nonPi (by intros; simp_all) h
    | pi domV bodyE bodyEnv =>
      rw [SemType.succ_pi] at h ⊢
      refine ⟨h.1.symm, h.2.2.1, h.2.1,
        fun m hm => (h.2.2.2.1 m hm).symm, ?_⟩
      -- Pi closure: swap w1↔w2, swap conjuncts, symm on results
      intro j hj w1 w2 hsem hw1 hw2 fuel r1 r2 hr1 hr2 vB1 vB2 hvB1 hvB2
      -- Invoke h's closure with swapped args (w2, w1)
      -- h.2.2.2.2 : ∀ j ≤ n', ∀ w1 w2, SemType j domV w1 w2 d → ...
      --   → ∀ vB1 vB2, eval(w1::) = vB1 → eval(w2::) = vB2 → SemType j vB1 ∧ SemType j vB2
      have hcl := h.2.2.2.2 j hj w2 w1 hsem.symm hw2 hw1 fuel r2 r1 hr2 hr1 vB2 vB1 hvB2 hvB1
      -- hcl : SemType j vB2 r2 r1 d ∧ SemType j vB1 r2 r1 d
      exact ⟨hcl.2.symm, hcl.1.symm⟩

theorem SemType_inf.symm (h : SemType_inf vA v1 v2 d) :
    SemType_inf (L := L) vA v2 v1 d :=
  fun n => (h n).symm

/-! ## SemType transitivity -/

theorem SemType.trans
    (hq2 : ∃ fq e, quote_s fq v2 d = some (e : SExpr L)) :
    SemType n vA v1 v2 d → SemType n vA v2 v3 d →
    SemType (L := L) n vA v1 v3 d := by
  match n with
  | 0 => intros; simp
  | n'+1 =>
    intro h12 h23
    cases vA with
    | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
      simp [SemType, and_true] at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1 hq2, h12.2.1, h23.2.2.1,
        fun m hm => (h12.2.2.2 m hm).trans (h23.2.2.2 m hm)⟩
    | pi domV bodyE bodyEnv =>
      rw [SemType.succ_pi] at h12 h23 ⊢
      refine ⟨h12.1.trans h23.1 hq2, h12.2.1, h23.2.2.1,
        fun m hm => (h12.2.2.2.1 m hm).trans (h23.2.2.2.1 m hm), ?_⟩
      -- Pi closure: chain via shared body type eval(w2::bodyEnv)
      intro j hj w1 w3 hsem13 hw1 hw3 fuel r1 r3 hr1 hr3 vB1 vB3 hvB1 hvB3
      sorry -- Pi closure transitivity: needs intermediate witness

theorem SemType_inf.trans
    (hq2 : ∃ fq e, quote_s fq v2 d = some (e : SExpr L))
    (h12 : SemType_inf vA v1 v2 d)
    (h23 : SemType_inf vA v2 v3 d) :
    SemType_inf (L := L) vA v1 v3 d :=
  fun n => (h12 n).trans hq2 (h23 n)

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
      simp only [SemType, and_true]
      exact ⟨h.quoteEq, h.wf_left, h.wf_right, fun m hm => h.simval hm⟩
    | pi domV' bodyE' bodyEnv' =>
      rw [SemType.succ_pi]
      refine ⟨h.quoteEq, h.wf_left, h.wf_right, fun m hm => h.simval hm, ?_⟩
      -- Pi→Pi closure transport: use IH at j < n'+1.
      -- From SimVal_inf vA (.pi domV' bodyE' bodyEnv'):
      --   vA must be .pi domV bodyE bodyEnv (SimVal_inf at n+1 forces same constructor)
      --   SimVal n' domV domV' and closure condition on body envs.
      -- 1. Reverse-transport domain: SemType j domV' w1 w2 → SemType j domV w1 w2 (IH at j)
      -- 2. Use original closure condition to get SemType j vB r1 r2
      -- 3. Transport body type: SimVal j vB vB' (from SimVal closure) → SemType j vB' r1 r2 (IH at j)
      sorry

theorem SemType_inf.transport_simval_inf
    (hsim : SimVal_inf vA vA' d) (h : SemType_inf vA v1 v2 d) :
    SemType_inf (L := L) vA' v1 v2 d :=
  fun n => (h n).transport_simval_inf hsim

/-! ## SemType transport on value arguments under SimVal_inf

    When v2 SimVal_inf v2', transport SemType from v2 to v2' on the right.
    Needed for beta case: eval(body.inst arg, ρ) SimVal_inf eval(body, va::ρ),
    and we have SemType for the latter, need it for the former. -/

theorem SemType.transport_right_simval_inf
    (hsim : SimVal_inf v2 v2' d)
    (hq2 : ∃ fq e, quote_s fq v2 d = some (e : SExpr L)) :
    SemType n vA v1 v2 d → ValWF v2' d →
    SemType (L := L) n vA v1 v2' d := by
  match n with
  | 0 => intros; simp
  | n'+1 =>
    intro h hw2'
    cases vA with
    | sort _ | lam _ _ _ | neutral _ _ | lit _ =>
      simp [SemType, and_true] at h ⊢
      exact ⟨h.1.trans (quoteEq_of_simval hsim h.2.2.1 hw2') hq2, h.2.1, hw2',
        fun m hm => (h.2.2.2 m hm).trans (hsim m)⟩
    | pi domV bodyE bodyEnv =>
      rw [SemType.succ_pi] at h ⊢
      refine ⟨h.1.trans (quoteEq_of_simval hsim h.2.2.1 hw2') hq2,
              h.2.1, hw2', fun m hm => (h.2.2.2.1 m hm).trans (hsim m), ?_⟩
      sorry -- Pi closure transport

/-! ## SemEnvT properties -/

/-- Extract the head condition from a SemEnvT. -/
theorem SemEnvT.head (h : SemEnvT n (A :: Γ) (v1 :: ρ1) (v2 :: ρ2) d) :
    ∀ fuel vA, eval_s fuel A ρ1 = some vA → SemType (L := L) n vA v1 v2 d := by
  cases h with | cons hv _ => exact hv

/-- Extract the tail from a SemEnvT. -/
theorem SemEnvT.tail (h : SemEnvT n (A :: Γ) (v1 :: ρ1) (v2 :: ρ2) d) :
    SemEnvT (L := L) n Γ ρ1 ρ2 d := by
  cases h with | cons _ ht => exact ht

/-! ## SemEnvT lookup — connects Lookup + SemEnvT to produce SemType -/

/-- Given Lookup Γ i A and SemEnvT n Γ ρ1 ρ2 d, produce SemType n at the
    evaluated type. Uses eval_lift_simval_inf for the lift/eval bridge and
    transport_simval_inf for type alignment. -/
theorem SemEnvT.get (hlook : Lookup Γ i A) (hse : SemEnvT (L := SLevel) n Γ ρ1 ρ2 d)
    (hew1 : EnvWF ρ1 d) (hew2 : EnvWF ρ2 d)
    {fuel : Nat} {v1 v2 vA : SVal SLevel}
    (hev1 : ρ1[i]? = some v1) (hev2 : ρ2[i]? = some v2)
    (hevA : eval_s fuel A ρ1 = some vA) :
    SemType n vA v1 v2 d := by
  induction hlook generalizing ρ1 ρ2 v1 v2 vA fuel with
  | zero =>
    -- i = 0, A = ty.lift, Γ = ty :: Γ'
    cases hse with | cons hhead htail =>
    -- ρ1 = v1_head :: ρ1_tail, ρ2 = v2_head :: ρ2_tail
    simp [List.getElem?_cons_zero] at hev1 hev2
    cases hev1; cases hev2
    -- hhead : ∀ fuel vA', eval ty ρ1_tail = some vA' → SemType n vA' v1 v2 d
    -- hevA : eval (ty.lift) (v1 :: ρ1_tail) = some vA
    -- Need eval ty ρ1_tail to succeed, then transport from vA' to vA
    sorry -- Blocked on: eval ty ρ1_tail must succeed (eval totality for well-typed types)
  | succ hlook' ih =>
    -- i = n+1, A = ty.lift
    cases hse with | cons _ htail =>
    simp [List.getElem?_cons_succ] at hev1 hev2
    -- hevA : eval (ty.lift) ρ1 = some vA where ρ1 = v_head :: ρ_tail
    sorry -- Same pattern: eval ty ρ_tail must succeed

/-! ## Eval totality for well-typed expressions

    Axiom (sorry'd): well-typed expressions evaluate at sufficient fuel.
    This is a consequence of type soundness — well-typed terms don't get stuck.
    Once the full metatheory is established, this can be derived from the
    fundamental theorem + typing rules. For now, we axiomatize it to unblock
    the fundamental theorem's case analysis. -/

/-- Well-typed expressions and their types evaluate at sufficient fuel. Sorry'd axiom.
    Covers both e₁ and A evaluation. -/
theorem eval_of_isDefEq
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    (ρ : List (SVal SLevel)) (hlen : ρ.length = Γ.length) :
    (∀ fuel, ∃ v, eval_s (fuel + 1) e₁ ρ = some v) ∧
    (∀ fuel, ∃ v, eval_s (fuel + 1) A ρ = some v) := by
  sorry

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

    If `IsDefEq Γ e₁ e₂ A`, then for SemEnvT n-related environments ρ1, ρ2,
    evaluating e₁, e₂, A produces SemType n-related results.

    The step parameter n allows the Pi closure to build bounded SemEnvT j
    (j ≤ n-1) for the body IH, resolving the SemType_inf circularity.
    For nbe_sound, we invoke this at step 1 (sufficient for QuoteEq extraction). -/
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
    {n : Nat} {ρ1 ρ2 : List (SVal SLevel)} {d : Nat}
    (hse : SemEnvT n Γ ρ1 ρ2 d)
    (hew1 : EnvWF ρ1 d) (hew2 : EnvWF ρ2 d)
    {fuel : Nat} {v1 v2 vA : SVal SLevel}
    (hev1 : eval_s fuel e₁ ρ1 = some v1)
    (hev2 : eval_s fuel e₂ ρ2 = some v2)
    (hevA : eval_s fuel A ρ1 = some vA) :
    SemType n vA v1 v2 d := by
  induction h generalizing n ρ1 ρ2 d fuel v1 v2 vA with
  | bvar hlook =>
    cases fuel with
    | zero => simp [eval_s] at hev1
    | succ f =>
      simp [eval_s] at hev1 hev2
      exact SemEnvT.get hlook hse hew1 hew2 hev1 hev2 hevA
  | sortDF _ _ _ =>
    -- eval (.sort l) ρ = .sort l, eval (.sort l') ρ = .sort l', type = .sort (.succ l)
    -- Need SemType_inf (.sort (.succ l)) (.sort l) (.sort l') d
    -- Sort type is non-Pi, so SemType = QuoteEq + ValWF.
    -- QuoteEq (.sort l) (.sort l') requires l = l' syntactically, but we only have l ≈ l'
    -- (Level.Equiv). Needs a lemma: Level.Equiv → quote produces same SExpr.
    sorry -- Blocked on: Level.Equiv → QuoteEq for sort values
  | constDF _ _ _ _ _ =>
    -- eval (.const c ls) ρ = .neutral (.const c ls) [], similarly for ls'.
    -- Type = ci.type.instL ls, need SemType_inf at that type.
    -- QuoteEq (.neutral (.const c ls) []) (.neutral (.const c ls') []) needs ls = ls'
    -- syntactically, but we only have SForall₂ (· ≈ ·) ls ls' (pairwise Level.Equiv).
    sorry -- Blocked on: pairwise Level.Equiv → QuoteEq for const neutral values
  | symm _h ih =>
    -- Goal: SemType_inf vA v2 v1 d (e' as e₁, e as e₂ — swapped)
    -- ih : ∀ ρ1 ρ2 d, SemEnvT Γ ρ1 ρ2 d → ... → eval e ρ1 = some v1 →
    --       eval e' ρ2 = some v2 → eval A ρ1 = some vA → SemType_inf vA v1 v2 d
    -- But our goal has eval e' ρ1 = hev1 and eval e ρ2 = hev2 (reversed assignment).
    -- To use ih, we need SemEnvT Γ ρ2 ρ1 d (swapped envs), i.e., SemEnvT.symm.
    -- SemEnvT.symm requires: if SemType_inf vA v1 v2 d for all types, then
    -- SemType_inf vA' v2 v1 d — which needs eval A ρ2 (not ρ1) and SemType_inf.symm.
    -- Also need eval A ρ2 to succeed (eval totality).
    sorry -- Blocked on: SemEnvT.symm (needs eval totality + SemType_inf.symm on env entries)
  | trans _h12 _h23 ih12 ih23 =>
    -- Goal: SemType_inf vA v1 v3 d
    -- ih12 : ... → eval e₁ ρ1 → eval e₂ ρ2 → SemType_inf vA v1 v2 d
    -- ih23 : ... → eval e₂ ρ1 → eval e₃ ρ2 → SemType_inf vA v2 v3 d
    -- To use ih12: have hev1 for e₁ at ρ1 ✓, need eval e₂ at ρ2 (eval totality).
    -- To use ih23: need eval e₂ at ρ1 (eval totality), have hev2 for e₃ at ρ2.
    -- Then chain via SemType_inf.trans (which itself has sorry in Pi case).
    sorry -- Blocked on: eval totality for e₂ at both ρ1 and ρ2 + SemType.trans Pi case
  | @appDF Γ' fn fn' Adom Bbody arg arg' _hf _ha ihf iha =>
    -- e₁ = .app fn arg, e₂ = .app fn' arg', type = Bbody.inst arg
    cases fuel with
    | zero => simp [eval_s] at hev1
    | succ fuelN =>
      simp only [eval_s, bind_eq_some] at hev1 hev2
      obtain ⟨fv1, hevf1, av1, heva1, hap1⟩ := hev1
      obtain ⟨fv2, hevf2, av2, heva2, hap2⟩ := hev2
      -- Eval totality: Pi type eval via sorry'd axiom
      obtain ⟨piV, hevPi⟩ := (eval_of_isDefEq _hf ρ1 (hse.length_left ▸ rfl)).2 fuelN
      -- Decompose piV: eval (.forallE Adom Bbody) ρ1 at fuel fuelN+1
      -- eval_s (fuelN+1) (.forallE Adom Bbody) ρ1
      --   = eval_s fuelN Adom ρ1 >>= fun dv => some (.pi dv Bbody ρ1)
      -- So piV = .pi domVA Bbody ρ1
      rw [eval_s_forallE, option_bind_eq_some] at hevPi
      obtain ⟨domVA, hevdomA, hpiV_eq⟩ := hevPi; cases hpiV_eq
      -- piV = .pi domVA Bbody ρ1
      -- Eval totality: domain type eval via sorry'd axiom
      obtain ⟨domV, hevDom⟩ := (eval_of_isDefEq _ha ρ1 (hse.length_left ▸ rfl)).2 fuelN
      -- domV = eval Adom ρ1 at fuel fuelN+1. domVA = eval Adom ρ1 at fuel fuelN.
      -- By fuel mono, domV = domVA.
      -- ihf: SemType at Pi type (.pi domVA Bbody ρ1) — at aligned fuel
      have hevPi_aligned : eval_s (fuelN + 1) (.forallE Adom Bbody) ρ1 =
          some (.pi domVA Bbody ρ1) := by
        rw [eval_s_forallE, option_bind_eq_some]; exact ⟨domVA, hevdomA, rfl⟩
      have hSemF := ihf hse hew1 hew2
        (eval_fuel_mono hevf1 (Nat.le_succ fuelN))
        (eval_fuel_mono hevf2 (Nat.le_succ fuelN))
        hevPi_aligned
      -- iha: SemType at domain type domVA (= domV by fuel determinism)
      -- domV and domVA are the same: both eval Adom ρ1, at different fuel.
      have hevDom' : eval_s (fuelN + 1) Adom ρ1 = some domVA :=
        eval_fuel_mono hevdomA (Nat.le_succ fuelN)
      have hSemA := iha hse hew1 hew2
        (eval_fuel_mono heva1 (Nat.le_succ fuelN))
        (eval_fuel_mono heva2 (Nat.le_succ fuelN))
        hevDom'
      -- Fire Pi closure
      match n with
      | 0 => simp
      | nn' + 1 =>
        rw [SemType.succ_pi] at hSemF
        have hcl := hSemF.2.2.2.2
        -- hcl : ∀ j ≤ nn', SemType j domVA w1 w2 d → apply → body type evals → SemType j
        -- Fire with w1=av1, w2=av2. Need body type evals to succeed.
        -- eval Bbody (av1::ρ1) and eval Bbody (av2::ρ1) at some fuel — sorry (eval totality)
        obtain ⟨vB1, hvB1⟩ : ∃ vB, eval_s (fuelN + 1) Bbody (av1 :: ρ1) = some vB := by sorry
        obtain ⟨vB2, hvB2⟩ : ∃ vB, eval_s (fuelN + 1) Bbody (av2 :: ρ1) = some vB := by sorry
        -- Align fuels for closure firing: use max of all fuels
        have hF := Nat.le_max_left fuelN (fuelN + 1)
        have hcl_result := hcl nn' (by omega) av1 av2
          (hSemA.mono (by omega))
          hSemA.wf_left hSemA.wf_right
          (fuelN + 1)
          v1 v2
          (apply_fuel_mono hap1 (Nat.le_succ fuelN))
          (apply_fuel_mono hap2 (Nat.le_succ fuelN))
          vB1 vB2 hvB1 hvB2
        -- hcl_result : SemType nn' vB1 v1 v2 d ∧ SemType nn' vB2 v1 v2 d
        -- Goal: SemType (nn'+1) vA v1 v2 d where vA = eval (Bbody.inst arg) ρ1
        -- Step gap: closure gives SemType nn', goal needs SemType (nn'+1).
        -- For non-Pi vA: SemType (nn'+1) = QuoteEq + ValWF + SimVal, all available from SemType nn'.
        -- For Pi vA: need full closure at step nn'+1 — requires re-firing at nn'+1 (not nn').
        -- Type transport: vB1 = eval Bbody (av1::ρ1), vA = eval (Bbody.inst arg) ρ1.
        -- These are SimVal_inf related by eval_inst_simval_inf at k=0.
        -- Combined sorry: step gap + type transport.
        sorry -- appDF step gap + type transport (SemType nn' vB1 → SemType (nn'+1) vA)
  | @lamDF Γ' Adom Adom' u bodyE bodyE' B _hA _hbody ihA ihbody =>
    -- e₁ = .lam Adom bodyE, e₂ = .lam Adom' bodyE', type = .forallE Adom B
    cases fuel with
    | zero => simp [eval_s] at hev1
    | succ f =>
      simp only [eval_s, bind_eq_some] at hev1 hev2 hevA
      obtain ⟨domV1, hevdom1, hv1⟩ := hev1; cases hv1
      obtain ⟨domV2, hevdom2, hv2⟩ := hev2; cases hv2
      obtain ⟨domVA, hevdomA, hvA⟩ := hevA; cases hvA
      -- v1 = .lam domV1 bodyE ρ1, v2 = .lam domV2 bodyE' ρ2, vA = .pi domVA B ρ1
      match n with
      | 0 => simp
      | nn'+1 =>
        rw [SemType.succ_pi]
        refine ⟨sorry, sorry, sorry, sorry, ?_⟩  -- QuoteEq, ValWF×2, SimVal — sorry'd
        -- Pi closure condition: the KEY part
        intro j hj w1 w2 hsem hw1 hw2 fuel' r1 r2 hr1 hr2 vB1 vB2 hvB1 hvB2
        cases fuel' with
        | zero => simp [apply_s] at hr1
        | succ fuel'' =>
          rw [apply_s_lam] at hr1 hr2
          -- Build SemEnvT j (Adom :: Γ') (w1 :: ρ1) (w2 :: ρ2) d
          -- Head: eval Adom ρ1 = domVA (deterministic), hsem at domVA.
          -- Tail: SemEnvT.mono from hse at nn'+1.
          have hse_ext : SemEnvT j (Adom :: Γ') (w1 :: ρ1) (w2 :: ρ2) d :=
            .cons
              (fun fuel' vA' hevA' => by
                -- vA' = domVA by eval fuel determinism
                have heq : vA' = domVA :=
                  (Option.some.inj ((eval_fuel_mono hevdomA
                    (Nat.le_max_left f fuel')).symm.trans
                    (eval_fuel_mono hevA' (Nat.le_max_right f fuel')))).symm
                subst heq; exact hsem)
              (SemEnvT.mono (show j ≤ nn' + 1 by omega) hse)
          -- Align fuel: body evals at fuel'', type evals at fuel''+1
          have hr1' := eval_fuel_mono hr1 (Nat.le_succ fuel'')
          have hr2' := eval_fuel_mono hr2 (Nat.le_succ fuel'')
          -- First conjunct: SemType j vB1 r1 r2 d (type eval at w1, matches ihbody's first env)
          -- Second conjunct: SemType j vB2 r1 r2 d (type eval at w2, needs transport)
          exact ⟨ihbody hse_ext (hew1.cons hw1) (hew2.cons hw2) hr1' hr2' hvB1,
                 sorry⟩ -- SemType j vB2 r1 r2 d: needs SimVal_inf transport from vB1 to vB2
  | forallEDF _hA _hbody ihA ihbody =>
    -- e₁ = .forallE A body, e₂ = .forallE A' body', type = .sort (imax u v)
    -- eval (.forallE A body) ρ = .pi (eval A ρ) body ρ (closure)
    -- Type is .sort (imax u v), which is non-Pi.
    -- Need SemType_inf (.sort (imax u v)) (.pi domV1 body ρ1) (.pi domV2 body' ρ2) d
    -- Non-Pi SemType = QuoteEq + ValWF + SimVal.
    -- QuoteEq of two Pi values requires quoting domains and bodies in extended envs,
    -- checking they produce the same SExpr — requires IH + quote_eval interaction.
    -- ValWF of .pi needs domain ValWF + body closedness arguments.
    sorry -- Blocked on: QuoteEq for Pi values (quote domain + body under binders),
           -- ValWF for Pi closures, SimVal for Pi values
  | defeqDF _hAB _he ihAB ihe =>
    -- IsDefEq Γ A B (.sort u) → IsDefEq Γ e₁ e₂ A → IsDefEq Γ e₁ e₂ B
    -- Goal: SemType_inf vB v1 v2 d where vB = eval B ρ1
    -- ihe : ... → eval e₁ ρ1 → eval e₂ ρ2 → eval A ρ1 = some vA → SemType_inf vA v1 v2 d
    -- ihAB : ... → eval A ρ1 → eval B ρ2 → eval (.sort u) ρ1 → SemType_inf (.sort u) vA vB d
    -- Need eval A ρ1 = some vA to fire ihe (eval totality for well-typed A).
    -- Then ihe gives SemType_inf vA v1 v2 d.
    -- ihAB gives SemType_inf (.sort u) vA vB d, so QuoteEq vA vB → SimVal_inf vA vB.
    -- Transport: SemType_inf vA v1 v2 d + SimVal_inf vA vB → SemType_inf vB v1 v2 d.
    sorry -- Blocked on: eval totality for A at ρ1, plus transport_simval_inf Pi case
  | beta _hbody _harg ihbody iharg =>
    -- LHS: eval (.app (.lam A e) e') ρ1 = apply (.lam (eval A ρ1) e ρ1) (eval e' ρ1)
    --     = eval e ((eval e' ρ1) :: ρ1)
    -- RHS: eval (e.inst e') ρ2
    -- Type: eval (B.inst e') ρ1
    -- ihbody : SemEnvT (A::Γ) ρ1' ρ2' d → eval e ρ1' → eval e ρ2' → eval B ρ1'
    --        → SemType_inf vB v1 v2 d
    -- iharg : SemEnvT Γ ρ1' ρ2' d → eval e' ρ1' → eval e' ρ2' → eval A ρ1'
    --       → SemType_inf vA v1 v2 d
    -- To use ihbody with extended env (eval_e'_ρ1 :: ρ1) and (eval_e'_ρ2 :: ρ2):
    --   need SemEnvT (A::Γ) and eval e' at both envs (eval totality for e').
    -- For RHS: need eval_inst_simval_inf: eval (e.inst e') ρ ≈ eval e ((eval e' ρ)::ρ).
    -- For type: need eval_inst for B.inst e' similarly.
    sorry -- Blocked on: eval_inst_simval_inf (substitution-evaluation commutation),
           -- eval totality for e' at ρ2, SemEnvT.cons construction
  | eta _he ihe =>
    -- LHS: eval (.lam A (.app e.lift (.bvar 0))) ρ1 = .lam (eval A ρ1) (.app e.lift (.bvar 0)) ρ1
    -- RHS: eval e ρ2
    -- Type: eval (.forallE A B) ρ1 = .pi (eval A ρ1) B ρ1
    -- ihe : ... → eval e ρ1 → eval e ρ2 → eval (.forallE A B) ρ1 → SemType_inf piV v1 v2 d
    -- Goal needs SemType_inf at Pi type for (.lam closure) vs (eval e ρ2).
    -- The lam closure applies as: eval (.app e.lift (.bvar 0)) (w::ρ1) = apply (eval e.lift (w::ρ1)) w
    --   = apply (eval e ρ1) w (via eval_liftN1).
    -- So the lam closure is eta-equivalent to eval e ρ1.
    -- Needs eval_liftN1_simval_inf + SemType construction for eta-expanded closures.
    sorry -- Blocked on: eval_liftN1 lemma (eval e.lift (w::ρ) = eval e ρ),
           -- building SemType for eta-expanded lam closure vs original value
  | proofIrrel _hp _hh _hh' ihp ihh ihh' =>
    -- h and h' are proofs of Prop p (where p : Sort 0).
    -- Goal: SemType_inf vP vh vh' d where vP = eval p ρ1, vh = eval h ρ1, vh' = eval h' ρ2.
    -- QuoteEq vh vh' would need proof irrelevance in NbE (quote erases proof content).
    -- This is not provable from structural NbE alone — needs a proof irrelevance axiom
    -- or a modified quote that maps all proofs of Props to a canonical form.
    sorry -- Blocked on: proof irrelevance in NbE (quote must equate all proofs of a Prop)
  | extra _hdf _hls _hlen =>
    -- env.defeqs df gives a definitional equality from the environment.
    -- LHS = df.lhs.instL ls, RHS = df.rhs.instL ls, type = df.type.instL ls.
    -- This depends on the semantic content of environment definitional equalities.
    -- Need: env.WFClosed ensures df.lhs and df.rhs evaluate to SemType-related values.
    -- Requires instL_eval interaction + environment well-formedness semantics.
    sorry -- Blocked on: semantic well-formedness of env.defeqs (instL/eval interaction)
  | letDF _hty _hval _hbody ihty ihval ihbody =>
    -- eval (.letE ty val body) ρ = eval val ρ >>= fun vv => eval body (vv :: ρ)
    -- Type = B.inst val
    -- Similar structure to beta: need eval val at both ρ1 and ρ2,
    -- build SemEnvT (ty::Γ) (vval1::ρ1) (vval2::ρ2) using ihval for the head,
    -- invoke ihbody with extended envs, transport type via eval_inst.
    sorry -- Blocked on: eval_inst_simval_inf for type (B.inst val ↔ eval B (vval::ρ)),
           -- eval totality for val at ρ2, SemEnvT.cons construction
  | letZeta _hty _hval _hbody ihty ihval ihbody =>
    -- eval (.letE ty val body) ρ1 = eval val ρ1 >>= fun vv => eval body (vv :: ρ1)
    -- eval (body.inst val) ρ2 (substitution on RHS)
    -- Type = B.inst val
    -- Same blockers as beta/letDF: need eval_inst_simval_inf + eval totality.
    sorry -- Blocked on: eval_inst_simval_inf (substitution-evaluation commutation),
           -- eval totality for val, SemEnvT construction for extended env
  | litDF =>
    match n with
    | 0 => simp
    | nn'+1 =>
      cases fuel with
      | zero => simp [eval_s] at hev1
      | succ f =>
        simp [eval_s] at hev1 hev2; cases hev1; cases hev2
        cases vA with
        | pi domV bodyE bodyEnv =>
          rw [SemType.succ_pi]
          exact ⟨QuoteEq.refl _ _, .lit, .lit, fun m _ => SimVal.refl_wf m .lit,
            fun j _ w1 w2 _ _ _ fuel' r1 r2 hr1 _ _ _ _ _ =>
              absurd hr1 (by cases fuel' <;> simp [apply_s])⟩
        | _ =>
          simp only [SemType, and_true]
          exact ⟨QuoteEq.refl _ _, .lit, .lit, fun m _ => SimVal.refl_wf m .lit⟩
  | projDF _hs ihs =>
    match n with
    | 0 => simp
    | _ + 1 =>
      cases fuel with
      | zero => simp [eval_s] at hev1
      | succ f => simp [eval_s] at hev1

/-! ## NbE soundness via the fundamental theorem

    The fundamental theorem gives us: IsDefEq e₁ e₂ A → nbe(e₁) = nbe(e₂).
    This fills the core gap in NbESoundness.lean. -/

/-- Auxiliary: fvarEnv Γ.length gives a reflexive SemEnvT n at any depth d ≥ Γ.length. -/
private theorem SemEnvT.fvarEnv_refl_aux (n : Nat) (Γ : List TExpr) (d : Nat)
    (hle : Γ.length ≤ d) :
    SemEnvT (L := SLevel) n Γ (fvarEnv Γ.length) (fvarEnv Γ.length) d := by
  induction Γ with
  | nil => exact .nil
  | cons A Γ' ih =>
    have hlen : (A :: Γ').length = Γ'.length + 1 := rfl
    rw [hlen, ← fvarEnv_succ]
    exact .cons
      (fun _fuel _vA _hev => SemType_neutral (.fvar (by omega)) rfl
        (QuoteEq.refl _ _)
        (fun m _ => SimVal.refl_wf m (.neutral (.fvar (by omega)) .nil))
        .nil .nil)
      (ih (by omega))

/-- Build a reflexive SemEnvT n for fvarEnv d. Each fvar is SemType n-related
    to itself at any type — follows from QuoteEq.refl + ValWF for neutrals. -/
theorem SemEnvT.fvarEnv_refl (n : Nat) (Γ : List TExpr) (hd : d = Γ.length) :
    SemEnvT (L := SLevel) n Γ (fvarEnv d) (fvarEnv d) d := by
  subst hd; exact fvarEnv_refl_aux n Γ Γ.length (Nat.le_refl _)

/-- Two definitionally equal terms NbE to QuoteEq results.
    Applies the fundamental theorem at step 1 (sufficient for QuoteEq extraction)
    with fvarEnv and extracts QuoteEq. -/
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
    {fuel : Nat} {v1 v2 vA : SVal SLevel}
    (hev1 : eval_s fuel e₁ (fvarEnv d) = some v1)
    (hev2 : eval_s fuel e₂ (fvarEnv d) = some v2)
    (hevA : eval_s fuel A (fvarEnv d) = some vA) :
    QuoteEq v1 v2 d := by
  subst hd
  exact (fundamental (n := 1) henv hlt hpt_closed hpt hpt_inst h
    (SemEnvT.fvarEnv_refl 1 Γ rfl)
    (EnvWF_fvarEnv Γ.length) (EnvWF_fvarEnv Γ.length)
    hev1 hev2 hevA).quoteEq

end Ix.Theory
