/-
  Ix.Theory.EvalSubst: Eval-Subst Correspondence.

  Relates evaluation in extended environments to syntactic substitution.
  Core lemma: eval e (va :: env) gives a value that quotes to the same
  expression as eval (e.inst a) env, when va = eval a env.

  This bridges the gap between NbE (which uses closure environments) and
  the typing judgment (which uses syntactic substitution).
  Phase 9 of the formalization roadmap.
-/
import Ix.Theory.Roundtrip

namespace Ix.Theory

open SExpr

variable {L : Type}

/-! ## Quote-equivalence -/

/-- Two values are quote-equivalent at depth d: they quote to the same expression. -/
def QuoteEq (v1 v2 : SVal L) (d : Nat) : Prop :=
  ∀ fq1 fq2 e1 e2,
    quote_s fq1 v1 d = some e1 → quote_s fq2 v2 d = some e2 → e1 = e2

/-- Two environments are pointwise quote-equivalent. -/
def EnvQuoteEq (env1 env2 : List (SVal L)) (d : Nat) : Prop :=
  env1.length = env2.length ∧
  ∀ i (hi1 : i < env1.length) (hi2 : i < env2.length),
    QuoteEq (env1[i]) (env2[i]) d

/-! ## QuoteEq properties -/

theorem QuoteEq.refl (v : SVal L) (d : Nat) : QuoteEq v v d := by
  intro fq1 fq2 e1 e2 h1 h2
  have h1' := quote_fuel_mono h1 (Nat.le_max_left fq1 fq2)
  have h2' := quote_fuel_mono h2 (Nat.le_max_right fq1 fq2)
  rw [h1'] at h2'; exact Option.some.inj h2'.symm ▸ rfl

theorem QuoteEq.symm : QuoteEq v1 v2 d → QuoteEq (L := L) v2 v1 d := by
  intro h fq1 fq2 e1 e2 h1 h2
  exact (h fq2 fq1 e2 e1 h2 h1).symm


/-! ## Structural value relation

  Two values are structurally related when they have the same top-level
  constructor, the same syntactic bodies (for closures), and structurally
  related sub-components. This is stronger than QuoteEq but is
  preserved by evaluation of the same expression in related environments. -/

mutual
/-- Structural value relation: same constructor, same bodies, related sub-values. -/
inductive StructRel : SVal L → SVal L → Prop where
  | sort : StructRel (.sort u) (.sort u)
  | lit : StructRel (.lit n) (.lit n)
  | neutral : StructRelList sp1 sp2 → StructRel (.neutral hd sp1) (.neutral hd sp2)
  | lam : StructRel dom1 dom2 → StructRelList env1 env2 →
      StructRel (.lam dom1 body env1) (.lam dom2 body env2)
  | pi : StructRel dom1 dom2 → StructRelList env1 env2 →
      StructRel (.pi dom1 body env1) (.pi dom2 body env2)

/-- Pointwise structural relation on lists. -/
inductive StructRelList : List (SVal L) → List (SVal L) → Prop where
  | nil : StructRelList [] []
  | cons : StructRel v1 v2 → StructRelList vs1 vs2 →
      StructRelList (v1 :: vs1) (v2 :: vs2)
end

theorem StructRelList.length : StructRelList l1 l2 → l1.length = l2.length
  | .nil => rfl
  | .cons _ h => by simp; exact h.length

theorem StructRelList.get {l1 l2 : List (SVal L)}
    (h : StructRelList l1 l2) (hi1 : i < l1.length) (hi2 : i < l2.length) :
    StructRel (l1[i]) (l2[i]) := by
  cases h with
  | nil => exact absurd hi1 (by simp)
  | cons hv hvs =>
    cases i with
    | zero => exact hv
    | succ j => exact hvs.get (by simp at hi1; omega) (by simp at hi2; omega)

theorem StructRelList.snoc (hsr : StructRelList sp1 sp2) (ha : StructRel a1 a2) :
    StructRelList (sp1 ++ [a1]) (sp2 ++ [a2]) := by
  match hsr with
  | .nil => exact .cons ha .nil
  | .cons hv hvs => exact .cons hv (hvs.snoc ha)

mutual
theorem StructRel.refl : (v : SVal L) → StructRel v v
  | .sort _ => .sort
  | .lit _ => .lit
  | .neutral _ sp => .neutral (StructRelList.refl sp)
  | .lam dom _ env => .lam (StructRel.refl dom) (StructRelList.refl env)
  | .pi dom _ env => .pi (StructRel.refl dom) (StructRelList.refl env)

theorem StructRelList.refl : (l : List (SVal L)) → StructRelList l l
  | [] => .nil
  | v :: vs => .cons (StructRel.refl v) (StructRelList.refl vs)
end

/-! ## Bind decomposition helpers -/

theorem option_bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [Option.bind]

theorem bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := option_bind_eq_some

/-! ## Equation lemmas -/

theorem eval_s_zero : eval_s 0 e env = (none : Option (SVal L)) := rfl
theorem eval_s_bvar : eval_s (n+1) (.bvar idx : SExpr L) env = env[idx]? := rfl
theorem eval_s_sort : eval_s (n+1) (.sort u : SExpr L) env = some (.sort u) := rfl
theorem eval_s_const' : eval_s (n+1) (.const c ls : SExpr L) env =
    some (.neutral (.const c ls) []) := rfl
theorem eval_s_lit : eval_s (n+1) (.lit l : SExpr L) env = some (.lit l) := rfl
theorem eval_s_proj : eval_s (n+1) (.proj t i s : SExpr L) env =
    (none : Option (SVal L)) := rfl
theorem eval_s_app : eval_s (n+1) (.app fn arg : SExpr L) env =
    (eval_s n fn env).bind fun fv => (eval_s n arg env).bind fun av =>
    apply_s n fv av := rfl
theorem eval_s_lam : eval_s (n+1) (.lam dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.lam dv body env) := rfl
theorem eval_s_forallE : eval_s (n+1) (.forallE dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.pi dv body env) := rfl
theorem eval_s_letE : eval_s (n+1) (.letE ty val body : SExpr L) env =
    (eval_s n val env).bind fun vv => eval_s n body (vv :: env) := rfl
theorem apply_s_zero : apply_s 0 fn arg = (none : Option (SVal L)) := rfl
theorem apply_s_lam : apply_s (n+1) (.lam dom body fenv : SVal L) arg =
    eval_s n body (arg :: fenv) := rfl
theorem apply_s_neutral : apply_s (n+1) (.neutral hd spine : SVal L) arg =
    some (.neutral hd (spine ++ [arg])) := rfl

/-! ## eval_env_structRel: same expression, StructRel envs → StructRel results

  Proved by strong induction on fuel. The key insight: evaluating the same
  expression in structurally related environments always produces structurally
  related results. For lam closures, the body is identical (same expression),
  enabling the apply case to use the IH at lower fuel. -/

theorem eval_env_structRel :
    ∀ (fuel : Nat) (e : SExpr L) (env1 env2 : List (SVal L)) (d : Nat) (v1 : SVal L),
    eval_s fuel e env1 = some v1 →
    StructRelList env1 env2 →
    SExpr.ClosedN e env1.length → EnvWF env1 d → EnvWF env2 d →
    ∃ v2, eval_s fuel e env2 = some v2 ∧ StructRel v1 v2 := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro e env1 env2 d v1 hev hsr hcl hew1 hew2
  cases fuel with
  | zero => rw [eval_s_zero] at hev; exact absurd hev nofun
  | succ n =>
  cases e with
  | bvar idx =>
    rw [eval_s_bvar] at hev
    simp only [SExpr.ClosedN] at hcl
    have hlen := hsr.length
    have hi2 : idx < env2.length := hlen ▸ hcl
    rw [List.getElem?_eq_getElem hcl] at hev; cases hev
    exact ⟨env2[idx], by rw [eval_s_bvar, List.getElem?_eq_getElem hi2],
      hsr.get hcl hi2⟩
  | sort u =>
    rw [eval_s_sort] at hev; cases hev
    exact ⟨.sort u, by rw [eval_s_sort], .sort⟩
  | const c ls =>
    rw [eval_s_const'] at hev; cases hev
    exact ⟨.neutral (.const c ls) [], by rw [eval_s_const'], .neutral .nil⟩
  | lit l =>
    rw [eval_s_lit] at hev; cases hev
    exact ⟨.lit l, by rw [eval_s_lit], .lit⟩
  | proj _ _ _ =>
    rw [eval_s_proj] at hev; exact absurd hev nofun
  | app fn arg =>
    rw [eval_s_app] at hev
    simp only [option_bind_eq_some] at hev
    obtain ⟨fv1, hf1, av1, ha1, happ1⟩ := hev
    simp only [SExpr.ClosedN] at hcl
    -- eval fn and arg at fuel n < n+1 → IH applies
    obtain ⟨fv2, hf2, srF⟩ := ih n (Nat.lt_succ_of_le (Nat.le_refl n))
      fn env1 env2 d fv1 hf1 hsr hcl.1 hew1 hew2
    obtain ⟨av2, ha2, srA⟩ := ih n (Nat.lt_succ_of_le (Nat.le_refl n))
      arg env1 env2 d av1 ha1 hsr hcl.2 hew1 hew2
    -- apply_s n fv1 av1 = some v1; need apply_s n fv2 av2 = some v2 ∧ StructRel
    cases n with
    | zero => rw [apply_s_zero] at happ1; exact absurd happ1 nofun
    | succ m =>
      -- Case split on fv1/fv2 shape (StructRel guarantees same constructor)
      cases srF with
      | sort => exact absurd happ1 nofun
      | lit => exact absurd happ1 nofun
      | pi => exact absurd happ1 nofun
      | neutral hsp =>
        rw [apply_s_neutral] at happ1; cases happ1
        refine ⟨.neutral _ (_ ++ [av2]), ?_, .neutral (hsp.snoc srA)⟩
        rw [eval_s_app]; simp only [option_bind_eq_some]
        exact ⟨_, hf2, _, ha2, by rw [apply_s_neutral]⟩
      | lam srDom srEnv =>
        -- apply_s (m+1) (.lam dom1 body fenv1) av1 = eval_s m body (av1 :: fenv1)
        rw [apply_s_lam] at happ1
        -- Same body! StructRel envs!
        have srEnv' : StructRelList (av1 :: _ ) (av2 :: _) := .cons srA srEnv
        have hwf_fv1 := eval_preserves_wf hf1 hcl.1 hew1
        have hwf_fv2 := eval_preserves_wf hf2 (hsr.length ▸ hcl.1) hew2
        have hwf_av1 := eval_preserves_wf ha1 hcl.2 hew1
        have hwf_av2 := eval_preserves_wf ha2 (hsr.length ▸ hcl.2) hew2
        cases hwf_fv1 with | lam hwf_dom hcl_body hew_fenv =>
        cases hwf_fv2 with | lam hwf_dom2 hcl_body2 hew_fenv2 =>
        obtain ⟨v2, hv2, srR⟩ := ih m (by omega)
          _ _ _ d v1 happ1 srEnv'
          (by simp; exact hcl_body)
          (.cons hwf_av1 hew_fenv) (.cons hwf_av2 hew_fenv2)
        refine ⟨v2, ?_, srR⟩
        rw [eval_s_app]; simp only [option_bind_eq_some]
        exact ⟨_, hf2, _, ha2, by rw [apply_s_lam]; exact hv2⟩
  | lam dom body =>
    rw [eval_s_lam] at hev
    simp only [option_bind_eq_some] at hev
    obtain ⟨dv1, hd1, hv1⟩ := hev; cases hv1
    simp only [SExpr.ClosedN] at hcl
    obtain ⟨dv2, hd2, srDom⟩ := ih n (Nat.lt_succ_of_le (Nat.le_refl n))
      dom env1 env2 d dv1 hd1 hsr hcl.1 hew1 hew2
    exact ⟨.lam dv2 body env2,
      by rw [eval_s_lam]; simp only [option_bind_eq_some]; exact ⟨dv2, hd2, rfl⟩,
      .lam srDom hsr⟩
  | forallE dom body =>
    rw [eval_s_forallE] at hev
    simp only [option_bind_eq_some] at hev
    obtain ⟨dv1, hd1, hv1⟩ := hev; cases hv1
    simp only [SExpr.ClosedN] at hcl
    obtain ⟨dv2, hd2, srDom⟩ := ih n (Nat.lt_succ_of_le (Nat.le_refl n))
      dom env1 env2 d dv1 hd1 hsr hcl.1 hew1 hew2
    exact ⟨.pi dv2 body env2,
      by rw [eval_s_forallE]; simp only [option_bind_eq_some]; exact ⟨dv2, hd2, rfl⟩,
      .pi srDom hsr⟩
  | letE ty val body =>
    rw [eval_s_letE] at hev
    simp only [option_bind_eq_some] at hev
    obtain ⟨vv1, hvl1, hbd1⟩ := hev
    simp only [SExpr.ClosedN] at hcl
    obtain ⟨vv2, hvl2, srVal⟩ := ih n (Nat.lt_succ_of_le (Nat.le_refl n))
      val env1 env2 d vv1 hvl1 hsr hcl.2.1 hew1 hew2
    have wf_vv1 := eval_preserves_wf hvl1 hcl.2.1 hew1
    have wf_vv2 := eval_preserves_wf hvl2 (hsr.length ▸ hcl.2.1) hew2
    obtain ⟨v2, hv2, srBody⟩ := ih n (Nat.lt_succ_of_le (Nat.le_refl n))
      body (vv1 :: env1) (vv2 :: env2) d v1 hbd1
      (.cons srVal hsr) (by simp; exact hcl.2.2)
      (.cons wf_vv1 hew1) (.cons wf_vv2 hew2)
    exact ⟨v2, by rw [eval_s_letE]; simp only [option_bind_eq_some]; exact ⟨vv2, hvl2, hv2⟩,
      srBody⟩

/-! ## StructRel → QuoteEq

  Structurally related values quote to the same expression.
  Proof by induction on quote fuel. Uses eval_env_structRel
  for the lam/pi closure body case. -/

private theorem structRelList_quoteSpine_eq (n : Nat)
    (ih : ∀ (v1 v2 : SVal L) (d : Nat),
      StructRel v1 v2 → ValWF v1 d → ValWF v2 d →
      ∀ e1 e2, quote_s n v1 d = some e1 → quote_s n v2 d = some e2 → e1 = e2)
    {sp1 sp2 : List (SVal L)} {acc : SExpr L} {d : Nat}
    (hsr : StructRelList sp1 sp2) (hwf1 : ListWF sp1 d) (hwf2 : ListWF sp2 d)
    {r1 r2 : SExpr L}
    (hq1 : quoteSpine_s n acc sp1 d = some r1)
    (hq2 : quoteSpine_s n acc sp2 d = some r2) : r1 = r2 :=
  match hsr, hwf1, hwf2 with
  | .nil, .nil, .nil => by
    rw [quoteSpine_s.eq_1] at hq1 hq2; cases hq1; cases hq2; rfl
  | .cons hv hvs, .cons hw1 hrest1, .cons hw2 hrest2 => by
    simp only [quoteSpine_s.eq_2, bind_eq_some] at hq1 hq2
    obtain ⟨aE1, ha1, hr1⟩ := hq1
    obtain ⟨aE2, ha2, hr2⟩ := hq2
    have heq : aE1 = aE2 := ih _ _ _ hv hw1 hw2 _ _ ha1 ha2
    subst heq
    exact structRelList_quoteSpine_eq n ih hvs hrest1 hrest2 hr1 hr2

private theorem structRel_quoteEq_aux :
    ∀ (fuel : Nat) (v1 v2 : SVal L) (d : Nat),
    StructRel v1 v2 → ValWF v1 d → ValWF v2 d →
    ∀ e1 e2, quote_s fuel v1 d = some e1 → quote_s fuel v2 d = some e2 →
    e1 = e2 := by
  intro fuel
  induction fuel with
  | zero => intro v1 v2 d _ _ _ e1 e2 h1; simp [quote_s] at h1
  | succ n ih =>
    intro v1 v2 d hsr hwf1 hwf2 e1 e2 hq1 hq2
    cases hsr with
    | sort =>
      rw [quote_s.eq_2] at hq1 hq2; cases hq1; cases hq2; rfl
    | lit =>
      rw [quote_s.eq_3] at hq1 hq2; cases hq1; cases hq2; rfl
    | neutral hsp =>
      rw [quote_s.eq_6] at hq1 hq2
      exact structRelList_quoteSpine_eq n ih hsp
        (by cases hwf1 with | neutral _ h => exact h)
        (by cases hwf2 with | neutral _ h => exact h) hq1 hq2
    | lam hdom henv =>
      simp only [quote_s.eq_4, bind_eq_some] at hq1 hq2
      obtain ⟨domE1, hd1, bodyV1, hbv1, bodyE1, hbe1, hr1⟩ := hq1
      obtain ⟨domE2, hd2, bodyV2, hbv2, bodyE2, hbe2, hr2⟩ := hq2
      cases hr1; cases hr2
      cases hwf1 with | lam hwf_dom1 hcl1 hew1 =>
      cases hwf2 with | lam hwf_dom2 hcl2 hew2 =>
      have dom_eq := ih _ _ _ hdom hwf_dom1 hwf_dom2 _ _ hd1 hd2
      have fvar_wf : ValWF (SVal.neutral (.fvar d) ([] : List (SVal L))) (d + 1) :=
        .neutral (.fvar (Nat.lt_succ_of_le (Nat.le_refl d))) .nil
      let sr_fenv := StructRelList.cons (StructRel.refl (SVal.neutral (.fvar d) ([] : List (SVal L)))) henv
      have ⟨bodyV2', hbv2', sr_body⟩ := eval_env_structRel n _ _ _
        (d + 1) bodyV1 hbv1 sr_fenv (by simp; exact hcl1)
        (.cons fvar_wf (hew1.mono (Nat.le_succ d)))
        (.cons fvar_wf (hew2.mono (Nat.le_succ d)))
      rw [hbv2'] at hbv2; cases hbv2
      have wf_bv1 := eval_preserves_wf hbv1 (by simp; exact hcl1)
        (.cons fvar_wf (hew1.mono (Nat.le_succ d)))
      have wf_bv2 := eval_preserves_wf hbv2'
        (by simp; rw [← henv.length]; exact hcl1)
        (.cons fvar_wf (hew2.mono (Nat.le_succ d)))
      have body_eq := ih _ _ _ sr_body wf_bv1 wf_bv2 _ _ hbe1 hbe2
      rw [dom_eq, body_eq]
    | pi hdom henv =>
      simp only [quote_s.eq_5, bind_eq_some] at hq1 hq2
      obtain ⟨domE1, hd1, bodyV1, hbv1, bodyE1, hbe1, hr1⟩ := hq1
      obtain ⟨domE2, hd2, bodyV2, hbv2, bodyE2, hbe2, hr2⟩ := hq2
      cases hr1; cases hr2
      cases hwf1 with | pi hwf_dom1 hcl1 hew1 =>
      cases hwf2 with | pi hwf_dom2 hcl2 hew2 =>
      have dom_eq := ih _ _ _ hdom hwf_dom1 hwf_dom2 _ _ hd1 hd2
      have fvar_wf : ValWF (SVal.neutral (.fvar d) ([] : List (SVal L))) (d + 1) :=
        .neutral (.fvar (Nat.lt_succ_of_le (Nat.le_refl d))) .nil
      let sr_fenv := StructRelList.cons (StructRel.refl (SVal.neutral (.fvar d) ([] : List (SVal L)))) henv
      have ⟨bodyV2', hbv2', sr_body⟩ := eval_env_structRel n _ _ _
        (d + 1) bodyV1 hbv1 sr_fenv (by simp; exact hcl1)
        (.cons fvar_wf (hew1.mono (Nat.le_succ d)))
        (.cons fvar_wf (hew2.mono (Nat.le_succ d)))
      rw [hbv2'] at hbv2; cases hbv2
      have wf_bv1 := eval_preserves_wf hbv1 (by simp; exact hcl1)
        (.cons fvar_wf (hew1.mono (Nat.le_succ d)))
      have wf_bv2 := eval_preserves_wf hbv2'
        (by simp; rw [← henv.length]; exact hcl1)
        (.cons fvar_wf (hew2.mono (Nat.le_succ d)))
      have body_eq := ih _ _ _ sr_body wf_bv1 wf_bv2 _ _ hbe1 hbe2
      rw [dom_eq, body_eq]

/-- Structurally related values are quote-equivalent. -/
theorem structRel_implies_quoteEq {v1 v2 : SVal L} {d : Nat}
    (hsr : StructRel v1 v2) (hwf1 : ValWF v1 d) (hwf2 : ValWF v2 d) :
    QuoteEq v1 v2 d := by
  intro fq1 fq2 e1 e2 hq1 hq2
  have hq1' := quote_fuel_mono hq1 (Nat.le_max_left fq1 fq2)
  have hq2' := quote_fuel_mono hq2 (Nat.le_max_right fq1 fq2)
  exact structRel_quoteEq_aux (max fq1 fq2) _ _ _ hsr hwf1 hwf2 _ _ hq1' hq2'

/-- Evaluating the same expression in StructRel environments gives both
    StructRel and QuoteEq results. Combines eval_env_structRel with
    structRel_implies_quoteEq. -/
theorem eval_env_combined {fuel : Nat} {e : SExpr L} {env1 env2 : List (SVal L)} {d : Nat}
    {v1 : SVal L}
    (hev : eval_s fuel e env1 = some v1)
    (hsr : StructRelList env1 env2)
    (hcl : ClosedN e env1.length) (hew1 : EnvWF env1 d) (hew2 : EnvWF env2 d) :
    ∃ v2, eval_s fuel e env2 = some v2 ∧ StructRel v1 v2 ∧
      (∀ d', d ≤ d' → QuoteEq v1 v2 d') := by
  obtain ⟨v2, hev2, sr⟩ := eval_env_structRel fuel e env1 env2 d v1 hev hsr hcl hew1 hew2
  exact ⟨v2, hev2, sr, fun d' hd' => structRel_implies_quoteEq sr
    ((eval_preserves_wf hev hcl hew1).mono hd')
    ((eval_preserves_wf hev2 (hsr.length ▸ hcl) hew2).mono hd')⟩

/-! ## envInsert -/

/-- Insert a value at position k in an environment list. -/
def envInsert (k : Nat) (va : SVal L) (env : List (SVal L)) : List (SVal L) :=
  env.take k ++ [va] ++ env.drop k

theorem envInsert_zero (va : SVal L) (env : List (SVal L)) :
    envInsert 0 va env = va :: env := by
  simp [envInsert]

theorem envInsert_length (k : Nat) (va : SVal L) (env : List (SVal L)) (hk : k ≤ env.length) :
    (envInsert k va env).length = env.length + 1 := by
  simp [envInsert, List.length_take, List.length_drop, Nat.min_eq_left hk]
  omega

theorem envInsert_lt {k i : Nat} {va : SVal L} {env : List (SVal L)}
    (hi : i < k) (hk : k ≤ env.length) :
    (envInsert k va env)[i]? = env[i]? := by
  simp [envInsert]
  rw [List.getElem?_append_left (by simp [List.length_take, Nat.min_eq_left hk]; omega)]
  simp [hi]

theorem envInsert_eq {k : Nat} {va : SVal L} {env : List (SVal L)}
    (hk : k ≤ env.length) :
    (envInsert k va env)[k]? = some va := by
  simp [envInsert]
  rw [List.getElem?_append_right (by simp [List.length_take, Nat.min_eq_left hk])]
  simp [List.length_take, Nat.min_eq_left hk, Nat.sub_self]

theorem envInsert_gt {k i : Nat} {va : SVal L} {env : List (SVal L)}
    (hi : k < i) (_hilen : i < env.length + 1) (hk : k ≤ env.length) :
    (envInsert k va env)[i]? = env[i - 1]? := by
  simp [envInsert]
  rw [List.getElem?_append_right (by
    simp [List.length_take, Nat.min_eq_left hk]; omega)]
  simp [List.length_take, Nat.min_eq_left hk]
  have h1 : i - k ≥ 1 := by omega
  simp [List.getElem?_cons, show ¬(i - k = 0) by omega]
  congr 1; omega

theorem envInsert_succ (v : SVal L) (k : Nat) (va : SVal L) (env : List (SVal L)) :
    v :: envInsert k va env = envInsert (k + 1) va (v :: env) := by
  simp [envInsert, List.take_succ_cons, List.drop_succ_cons]

/-! ## The eval-subst theorem

  Proof by structural induction on `e`. This enables the IH to work under
  binders (body is a structural subterm of .lam/.forallE/.letE) regardless
  of eval/quote fuel.

  `InstEnvCond` is parameterized by `k` (substitution position) and uses
  `∀ d' ≥ d` to handle depth increase under binders. -/

/-! ## Neutral spine lemmas -/

/-- Decompose quoteSpine_s for sp ++ [arg]: quoteSpine on sp succeeded and
    quote on arg succeeded, with result = .app spineE argE. -/
private theorem quoteSpine_append_singleton_inv {fuel : Nat} {acc : SExpr L}
    {sp : List (SVal L)} {arg : SVal L} {d : Nat} {result : SExpr L}
    (h : quoteSpine_s fuel acc (sp ++ [arg]) d = some result) :
    ∃ spE argE, quoteSpine_s fuel acc sp d = some spE ∧
                quote_s fuel arg d = some argE ∧ result = .app spE argE := by
  induction sp generalizing acc with
  | nil =>
    simp only [List.nil_append, quoteSpine_s.eq_2, bind_eq_some] at h
    obtain ⟨argE, harg, hrest⟩ := h
    rw [quoteSpine_s.eq_1] at hrest; cases hrest
    exact ⟨acc, argE, by rw [quoteSpine_s.eq_1], harg, rfl⟩
  | cons a rest ih =>
    simp only [List.cons_append, quoteSpine_s.eq_2, bind_eq_some] at h
    obtain ⟨aE, haE, hrest⟩ := h
    obtain ⟨spE, argE, hsp, harg, heq⟩ := ih hrest
    exact ⟨spE, argE, by
      simp only [quoteSpine_s.eq_2, bind_eq_some]; exact ⟨aE, haE, hsp⟩, harg, heq⟩

/-- Appending QuoteEq arguments to QuoteEq neutral values preserves QuoteEq. -/
theorem quoteEq_neutral_snoc
    {hd1 hd2 : SHead L} {sp1 sp2 : List (SVal L)} {arg1 arg2 : SVal L} {d : Nat}
    (hqe : QuoteEq (.neutral hd1 sp1) (.neutral hd2 sp2) d)
    (hqa : QuoteEq arg1 arg2 d) :
    QuoteEq (.neutral hd1 (sp1 ++ [arg1])) (.neutral hd2 (sp2 ++ [arg2])) d := by
  intro fq1 fq2 r1 r2 hq1 hq2
  cases fq1 with
  | zero => simp [quote_s] at hq1
  | succ fq1' =>
    cases fq2 with
    | zero => simp [quote_s] at hq2
    | succ fq2' =>
      rw [quote_s.eq_6] at hq1 hq2
      obtain ⟨e1, argE1, hsp1, harg1, hr1⟩ := quoteSpine_append_singleton_inv hq1
      obtain ⟨e2, argE2, hsp2, harg2, hr2⟩ := quoteSpine_append_singleton_inv hq2
      subst hr1; subst hr2
      have hne1 : quote_s (fq1' + 1) (.neutral hd1 sp1) d = some e1 := by
        rw [quote_s.eq_6]; exact hsp1
      have hne2 : quote_s (fq2' + 1) (.neutral hd2 sp2) d = some e2 := by
        rw [quote_s.eq_6]; exact hsp2
      rw [hqe _ _ _ _ hne1 hne2, hqa _ _ _ _ harg1 harg2]

/-! ## Sorry'd axioms for closure bisimulation

  These axioms capture the core closure extensionality principles needed
  to fill the eval_inst_quoteEq sorry's. The neutral-neutral case of
  apply_quoteEq is proved via quoteEq_neutral_snoc. The remaining cases
  (involving at least one lam) need closure bisimulation. -/

-- REMOVED: apply_quoteEq — superseded by apply_simval_inf + simval_implies_quoteEq

/-- QuoteEq for lam values: if domains are QuoteEq and body evals (opened
    with fvar(d)) are QuoteEq at d+1, then lam values are QuoteEq at d. -/
theorem quoteEq_lam {dom1 dom2 : SVal L} {b1 b2 : SExpr L}
    {e1 e2 : List (SVal L)} {d : Nat}
    (hdom : QuoteEq dom1 dom2 d)
    (hbody : ∀ f1 f2 bv1 bv2,
      eval_s f1 b1 (SVal.neutral (.fvar d) [] :: e1) = some bv1 →
      eval_s f2 b2 (SVal.neutral (.fvar d) [] :: e2) = some bv2 →
      QuoteEq bv1 bv2 (d + 1)) :
    QuoteEq (SVal.lam dom1 b1 e1) (SVal.lam dom2 b2 e2) d := by
  intro fq1 fq2 r1 r2 hq1 hq2
  -- Decompose quote_s on lam values
  cases fq1 with
  | zero => simp [quote_s] at hq1
  | succ fq1' =>
    cases fq2 with
    | zero => simp [quote_s] at hq2
    | succ fq2' =>
      simp only [quote_s.eq_4, bind_eq_some] at hq1 hq2
      obtain ⟨domE1, hd1, bodyV1, hbv1, bodyE1, hbe1, hr1⟩ := hq1
      obtain ⟨domE2, hd2, bodyV2, hbv2, bodyE2, hbe2, hr2⟩ := hq2
      cases hr1; cases hr2
      -- Domains agree
      have hdomEq := hdom _ _ _ _ hd1 hd2
      -- Body values agree: use hbody
      have hbodyQE := hbody fq1' fq2' bodyV1 bodyV2 hbv1 hbv2
      have hbodyEq := hbodyQE _ _ _ _ hbe1 hbe2
      rw [hdomEq, hbodyEq]

/-- QuoteEq for pi values: same structure as quoteEq_lam. -/
theorem quoteEq_pi {dom1 dom2 : SVal L} {b1 b2 : SExpr L}
    {e1 e2 : List (SVal L)} {d : Nat}
    (hdom : QuoteEq dom1 dom2 d)
    (hbody : ∀ f1 f2 bv1 bv2,
      eval_s f1 b1 (SVal.neutral (.fvar d) [] :: e1) = some bv1 →
      eval_s f2 b2 (SVal.neutral (.fvar d) [] :: e2) = some bv2 →
      QuoteEq bv1 bv2 (d + 1)) :
    QuoteEq (SVal.pi dom1 b1 e1) (SVal.pi dom2 b2 e2) d := by
  intro fq1 fq2 r1 r2 hq1 hq2
  cases fq1 with
  | zero => simp [quote_s] at hq1
  | succ fq1' =>
    cases fq2 with
    | zero => simp [quote_s] at hq2
    | succ fq2' =>
      simp only [quote_s.eq_5, bind_eq_some] at hq1 hq2
      obtain ⟨domE1, hd1, bodyV1, hbv1, bodyE1, hbe1, hr1⟩ := hq1
      obtain ⟨domE2, hd2, bodyV2, hbv2, bodyE2, hbe2, hr2⟩ := hq2
      cases hr1; cases hr2
      have hdomEq := hdom _ _ _ _ hd1 hd2
      have hbodyQE := hbody fq1' fq2' bodyV1 bodyV2 hbv1 hbv2
      have hbodyEq := hbodyQE _ _ _ _ hbe1 hbe2
      rw [hdomEq, hbodyEq]

-- Removed: InstEnvCond, InstEnvCond.prepend, apply_quoteEq, eval_env_quoteEq,
-- eval_inst_quoteEq (superseded by SimVal.eval_inst_simval_inf)

-- DELETED: quotable_of_wf — FALSE as stated (.proj blocks quote_s but satisfies ValWF).
-- Not called by any live code. Callers that need quotability provide it directly.

/-- Transitivity of QuoteEq, given that the middle value is quotable. -/
theorem QuoteEq.trans (h12 : QuoteEq v1 v2 d) (h23 : QuoteEq v2 v3 d)
    (hq : ∃ fq e, quote_s fq v2 d = some (e : SExpr L)) :
    QuoteEq (L := L) v1 v3 d := by
  obtain ⟨fq2, e2, hq2⟩ := hq
  intro fq1 fq3 e1 e3 hq1 hq3
  have h1 := h12 fq1 fq2 e1 e2 hq1 hq2  -- e1 = e2
  have h2 := h23 fq2 fq3 e2 e3 hq2 hq3  -- e2 = e3
  exact h1.trans h2

/-- EnvWF is preserved by envInsert. -/
theorem EnvWF_envInsert {env : List (SVal L)} {d : Nat}
    (henv : EnvWF env d) (hva : ValWF va d) (hk : k ≤ env.length) :
    EnvWF (envInsert k va env) d := by
  induction k generalizing env with
  | zero => rw [envInsert_zero]; exact .cons hva henv
  | succ k' ih =>
    cases henv with
    | nil => simp [List.length] at hk
    | cons hv hrest =>
      rw [← envInsert_succ]
      exact .cons hv (ih hrest (by simp [List.length] at hk; omega))

-- Removed: eval_inst_quoteEq (superseded by SimVal.eval_inst_simval_inf)

end Ix.Theory
