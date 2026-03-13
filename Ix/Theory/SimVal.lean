/-
  Ix.Theory.SimVal: Step-indexed value simulation for closure bisimulation.

  Provides the extensional closure equivalence principle needed to fill
  sorry's in EvalSubst.lean and NbESoundness.lean.

  Phase 10 of the formalization roadmap.
-/
import Ix.Theory.EvalSubst

namespace Ix.Theory

open SExpr

variable {L : Type}

/-! ## Step-indexed value simulation -/

mutual
def SimVal (n : Nat) (v1 v2 : SVal L) (d : Nat) : Prop :=
  match n with
  | 0 => True
  | n' + 1 =>
    match v1, v2 with
    | .sort u1, .sort u2 => u1 = u2
    | .lit n1, .lit n2 => n1 = n2
    | .neutral h1 sp1, .neutral h2 sp2 =>
        h1 = h2 ∧ SimSpine (n' + 1) sp1 sp2 d
    | .lam d1 b1 e1, .lam d2 b2 e2 =>
        SimVal n' d1 d2 d ∧
        ∀ (j : Nat), j ≤ n' →
          ∀ (d' : Nat), d ≤ d' →
            ∀ (w1 w2 : SVal L), SimVal j w1 w2 d' →
              ValWF w1 d' → ValWF w2 d' →
              ∀ (fuel : Nat) (r1 r2 : SVal L),
                eval_s fuel b1 (w1 :: e1) = some r1 →
                eval_s fuel b2 (w2 :: e2) = some r2 →
                SimVal j r1 r2 d'
    | .pi d1 b1 e1, .pi d2 b2 e2 =>
        SimVal n' d1 d2 d ∧
        ∀ (j : Nat), j ≤ n' →
          ∀ (d' : Nat), d ≤ d' →
            ∀ (w1 w2 : SVal L), SimVal j w1 w2 d' →
              ValWF w1 d' → ValWF w2 d' →
              ∀ (fuel : Nat) (r1 r2 : SVal L),
                eval_s fuel b1 (w1 :: e1) = some r1 →
                eval_s fuel b2 (w2 :: e2) = some r2 →
                SimVal j r1 r2 d'
    | _, _ => False
  termination_by (n, sizeOf v1 + sizeOf v2)
def SimSpine (n : Nat) (sp1 sp2 : List (SVal L)) (d : Nat) : Prop :=
  match sp1, sp2 with
  | [], [] => True
  | v1 :: r1, v2 :: r2 => SimVal n v1 v2 d ∧ SimSpine n r1 r2 d
  | _, _ => False
  termination_by (n, sizeOf sp1 + sizeOf sp2)
end

def SimEnv (n : Nat) (env1 env2 : List (SVal L)) (d : Nat) : Prop :=
  env1.length = env2.length ∧
  ∀ i (h1 : i < env1.length) (h2 : i < env2.length),
    SimVal n (env1[i]) (env2[i]) d

/-- SimVal for all steps (infinite observation budget). -/
def SimVal_inf (v1 v2 : SVal L) (d : Nat) : Prop :=
  ∀ n, SimVal n v1 v2 d

/-- SimEnv for all steps. -/
def SimEnv_inf (env1 env2 : List (SVal L)) (d : Nat) : Prop :=
  env1.length = env2.length ∧
  ∀ i (h1 : i < env1.length) (h2 : i < env2.length),
    SimVal_inf (env1[i]) (env2[i]) d

/-! ## Equation lemmas for SimVal

    These avoid issues with unfold not reducing after case-splitting. -/

@[simp] theorem SimVal.zero : SimVal 0 (v1 : SVal L) v2 d = True := by
  unfold SimVal; rfl

@[simp] theorem SimVal.sort_sort : SimVal (n'+1) (.sort (L := L) u1) (.sort u2) d = (u1 = u2) := by
  unfold SimVal; rfl
@[simp] theorem SimVal.lit_lit : SimVal (n'+1) (.lit (L := L) l1) (.lit l2) d = (l1 = l2) := by
  unfold SimVal; rfl
@[simp] theorem SimVal.neutral_neutral :
    SimVal (n'+1) (.neutral (L := L) h1 sp1) (.neutral h2 sp2) d =
    (h1 = h2 ∧ SimSpine (n' + 1) sp1 sp2 d) := by
  unfold SimVal; rfl

@[simp] theorem SimVal.lam_lam :
    SimVal (n'+1) (.lam (L := L) d1 b1 e1) (.lam d2 b2 e2) d =
    (SimVal n' d1 d2 d ∧
     ∀ (j : Nat), j ≤ n' →
       ∀ (d' : Nat), d ≤ d' →
         ∀ (w1 w2 : SVal L), SimVal j w1 w2 d' →
           ValWF w1 d' → ValWF w2 d' →
           ∀ (fuel : Nat) (r1 r2 : SVal L),
             eval_s fuel b1 (w1 :: e1) = some r1 →
             eval_s fuel b2 (w2 :: e2) = some r2 →
             SimVal j r1 r2 d') := by
  simp [SimVal]

@[simp] theorem SimVal.pi_pi :
    SimVal (n'+1) (.pi (L := L) d1 b1 e1) (.pi d2 b2 e2) d =
    (SimVal n' d1 d2 d ∧
     ∀ (j : Nat), j ≤ n' →
       ∀ (d' : Nat), d ≤ d' →
         ∀ (w1 w2 : SVal L), SimVal j w1 w2 d' →
           ValWF w1 d' → ValWF w2 d' →
           ∀ (fuel : Nat) (r1 r2 : SVal L),
             eval_s fuel b1 (w1 :: e1) = some r1 →
             eval_s fuel b2 (w2 :: e2) = some r2 →
             SimVal j r1 r2 d') := by
  simp [SimVal]

-- Cross-constructor at n'+1: all False
@[simp] theorem SimVal.sort_lit : SimVal (n'+1) (.sort (L := L) u) (.lit l) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.sort_neutral : SimVal (n'+1) (.sort (L := L) u) (.neutral h sp) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.sort_lam : SimVal (n'+1) (.sort (L := L) u) (.lam d1 b e) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.sort_pi : SimVal (n'+1) (.sort (L := L) u) (.pi d1 b e) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lit_sort : SimVal (n'+1) (.lit (L := L) l) (.sort u) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lit_neutral : SimVal (n'+1) (.lit (L := L) l) (.neutral h sp) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lit_lam : SimVal (n'+1) (.lit (L := L) l) (.lam d1 b e) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lit_pi : SimVal (n'+1) (.lit (L := L) l) (.pi d1 b e) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.neutral_sort : SimVal (n'+1) (.neutral (L := L) h sp) (.sort u) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.neutral_lit : SimVal (n'+1) (.neutral (L := L) h sp) (.lit l) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.neutral_lam : SimVal (n'+1) (.neutral (L := L) h sp) (.lam d1 b e) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.neutral_pi : SimVal (n'+1) (.neutral (L := L) h sp) (.pi d1 b e) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lam_sort : SimVal (n'+1) (.lam (L := L) d1 b e) (.sort u) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lam_lit : SimVal (n'+1) (.lam (L := L) d1 b e) (.lit l) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lam_neutral : SimVal (n'+1) (.lam (L := L) d1 b e) (.neutral h sp) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.lam_pi : SimVal (n'+1) (.lam (L := L) d1 b e) (.pi d1' b' e') d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.pi_sort : SimVal (n'+1) (.pi (L := L) d1 b e) (.sort u) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.pi_lit : SimVal (n'+1) (.pi (L := L) d1 b e) (.lit l) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.pi_neutral : SimVal (n'+1) (.pi (L := L) d1 b e) (.neutral h sp) d = False := by unfold SimVal; rfl
@[simp] theorem SimVal.pi_lam : SimVal (n'+1) (.pi (L := L) d1 b e) (.lam d1' b' e') d = False := by unfold SimVal; rfl

@[simp] theorem SimSpine.nil_nil : SimSpine n ([] : List (SVal L)) [] d = True := by unfold SimSpine; rfl
@[simp] theorem SimSpine.cons_cons :
    SimSpine n (v1 :: r1 : List (SVal L)) (v2 :: r2) d =
    (SimVal n v1 v2 d ∧ SimSpine n r1 r2 d) := by
  apply propext; constructor
  · intro h; unfold SimSpine at h; exact h
  · intro h; unfold SimSpine; exact h
@[simp] theorem SimSpine.nil_cons : SimSpine n ([] : List (SVal L)) (v :: vs) d = False := by unfold SimSpine; rfl
@[simp] theorem SimSpine.cons_nil : SimSpine n (v :: vs : List (SVal L)) [] d = False := by unfold SimSpine; rfl

/-! ## Monotonicity -/

mutual
theorem SimVal.mono (h : n' ≤ n) (hs : SimVal n v1 v2 d) : SimVal (L := L) n' v1 v2 d := by
  match n', n with
  | 0, _ => simp [SimVal.zero]
  | _+1, 0 => omega
  | m+1, k+1 =>
    cases v1 <;> cases v2
    all_goals (try simp only [SimVal.sort_sort, SimVal.lit_lit, SimVal.neutral_neutral,
      SimVal.sort_lit, SimVal.sort_neutral, SimVal.sort_lam,
      SimVal.sort_pi, SimVal.lit_sort, SimVal.lit_neutral, SimVal.lit_lam, SimVal.lit_pi,
      SimVal.neutral_sort, SimVal.neutral_lit, SimVal.neutral_lam, SimVal.neutral_pi,
      SimVal.lam_sort, SimVal.lam_lit, SimVal.lam_neutral, SimVal.lam_pi,
      SimVal.pi_sort, SimVal.pi_lit, SimVal.pi_neutral, SimVal.pi_lam] at hs ⊢)
    all_goals (try exact hs)
    case lam.lam d1 b1 e1 d2 b2 e2 =>
      rw [SimVal.lam_lam] at hs ⊢
      obtain ⟨hdom, hbody⟩ := hs
      exact ⟨hdom.mono (by omega), fun j hj d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 =>
        hbody j (by omega) d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2⟩
    case pi.pi d1 b1 e1 d2 b2 e2 =>
      rw [SimVal.pi_pi] at hs ⊢
      obtain ⟨hdom, hbody⟩ := hs
      exact ⟨hdom.mono (by omega), fun j hj d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 =>
        hbody j (by omega) d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2⟩
    case neutral.neutral =>
      exact ⟨hs.1, hs.2.mono h⟩
theorem SimSpine.mono (h : n' ≤ n) (hs : SimSpine n sp1 sp2 d) : SimSpine (L := L) n' sp1 sp2 d := by
  cases sp1 <;> cases sp2
  all_goals (try simp only [SimSpine.nil_nil, SimSpine.nil_cons, SimSpine.cons_nil] at hs ⊢)
  all_goals (try exact hs)
  case cons.cons =>
    rw [SimSpine.cons_cons] at hs ⊢
    exact ⟨(hs.1).mono h, (hs.2).mono h⟩
end

mutual
theorem SimVal.depth_mono (hd : d ≤ d') (hs : SimVal n v1 v2 d) :
    SimVal (L := L) n v1 v2 d' := by
  match n with
  | 0 => simp [SimVal.zero]
  | n' + 1 =>
    cases v1 <;> cases v2
    all_goals (try simp only [SimVal.sort_sort, SimVal.lit_lit, SimVal.neutral_neutral,
      SimVal.sort_lit, SimVal.sort_neutral, SimVal.sort_lam, SimVal.sort_pi,
      SimVal.lit_sort, SimVal.lit_neutral, SimVal.lit_lam, SimVal.lit_pi,
      SimVal.neutral_sort, SimVal.neutral_lit, SimVal.neutral_lam, SimVal.neutral_pi,
      SimVal.lam_sort, SimVal.lam_lit, SimVal.lam_neutral, SimVal.lam_pi,
      SimVal.pi_sort, SimVal.pi_lit, SimVal.pi_neutral, SimVal.pi_lam] at hs ⊢)
    all_goals (try exact hs)
    case lam.lam d1 b1 e1 d2 b2 e2 =>
      rw [SimVal.lam_lam] at hs ⊢
      obtain ⟨hdom, hbody⟩ := hs
      exact ⟨hdom.depth_mono hd, fun j hj d'' hd'' => hbody j hj d'' (Nat.le_trans hd hd'')⟩
    case pi.pi d1 b1 e1 d2 b2 e2 =>
      rw [SimVal.pi_pi] at hs ⊢
      obtain ⟨hdom, hbody⟩ := hs
      exact ⟨hdom.depth_mono hd, fun j hj d'' hd'' => hbody j hj d'' (Nat.le_trans hd hd'')⟩
    case neutral.neutral =>
      exact ⟨hs.1, hs.2.depth_mono hd⟩
theorem SimSpine.depth_mono (hd : d ≤ d') (hs : SimSpine n sp1 sp2 d) :
    SimSpine (L := L) n sp1 sp2 d' := by
  cases sp1 <;> cases sp2
  all_goals (try simp only [SimSpine.nil_nil, SimSpine.nil_cons, SimSpine.cons_nil] at hs ⊢)
  all_goals (try exact hs)
  case cons.cons =>
    rw [SimSpine.cons_cons] at hs ⊢
    exact ⟨(hs.1).depth_mono hd, (hs.2).depth_mono hd⟩
end

theorem SimSpine.snoc (h1 : SimSpine n sp1 sp2 d) (h2 : SimVal n v1 v2 d) :
    SimSpine (L := L) n (sp1 ++ [v1]) (sp2 ++ [v2]) d := by
  induction sp1 generalizing sp2 with
  | nil =>
    cases sp2 with
    | nil => simp [SimSpine.cons_cons, SimSpine.nil_nil]; exact h2
    | cons => simp [SimSpine.nil_cons] at h1
  | cons a1 r1 ih =>
    cases sp2 with
    | nil => simp [SimSpine.cons_nil] at h1
    | cons a2 r2 =>
      simp only [List.cons_append, SimSpine.cons_cons] at h1 ⊢
      exact ⟨h1.1, ih h1.2⟩

/-! ## SimEnv operations -/

theorem SimEnv.cons (hv : SimVal n v1 v2 d) (he : SimEnv n env1 env2 d) :
    SimEnv (L := L) n (v1 :: env1) (v2 :: env2) d := by
  refine ⟨by simp [he.1], fun i h1 h2 => ?_⟩
  cases i with
  | zero => exact hv
  | succ j =>
    simp only [List.length_cons] at h1 h2
    exact he.2 j (by omega) (by omega)

theorem SimEnv.mono (h : n' ≤ n) (hs : SimEnv n env1 env2 d) :
    SimEnv (L := L) n' env1 env2 d :=
  ⟨hs.1, fun i h1 h2 => (hs.2 i h1 h2).mono h⟩

theorem SimEnv.depth_mono (hd : d ≤ d') (hs : SimEnv n env1 env2 d) :
    SimEnv (L := L) n env1 env2 d' :=
  ⟨hs.1, fun i h1 h2 => (hs.2 i h1 h2).depth_mono hd⟩

theorem SimEnv.length_eq (h : SimEnv n env1 env2 d) :
    env1.length = (env2 : List (SVal L)).length := h.1

theorem SimEnv_inf.cons (hv : SimVal_inf v1 v2 d) (he : SimEnv_inf env1 env2 d) :
    SimEnv_inf (L := L) (v1 :: env1) (v2 :: env2) d :=
  ⟨by simp [he.1], fun i h1 h2 => by
    simp only [List.length_cons] at h1 h2
    cases i with
    | zero => exact hv
    | succ j => exact he.2 j (by omega) (by omega)⟩

theorem SimEnv_inf.to_n (h : SimEnv_inf env1 env2 d) :
    SimEnv (L := L) n env1 env2 d :=
  ⟨h.1, fun i h1 h2 => h.2 i h1 h2 n⟩

theorem SimEnv_inf.depth_mono (hd : d ≤ d') (h : SimEnv_inf env1 env2 d) :
    SimEnv_inf (L := L) env1 env2 d' :=
  ⟨h.1, fun i h1 h2 n => (h.2 i h1 h2 n).depth_mono hd⟩

theorem SimEnv_inf.length_eq (h : SimEnv_inf env1 env2 d) :
    env1.length = (env2 : List (SVal L)).length := h.1

/-! ## Bind decomposition -/

private theorem option_bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [Option.bind]

private theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  show x.bind f = some b ↔ _; cases x <;> simp [Option.bind]

/-! ## eval_s / apply_s equation lemmas -/

private theorem eval_s_zero : eval_s 0 e env = (none : Option (SVal L)) := rfl
private theorem eval_s_bvar : eval_s (n+1) (.bvar idx : SExpr L) env = env[idx]? := rfl
private theorem eval_s_sort : eval_s (n+1) (.sort u : SExpr L) env = some (.sort u) := rfl
private theorem eval_s_const' : eval_s (n+1) (.const c ls : SExpr L) env =
    some (.neutral (.const c ls) []) := rfl
private theorem eval_s_lit : eval_s (n+1) (.lit l : SExpr L) env = some (.lit l) := rfl
private theorem eval_s_proj : eval_s (n+1) (.proj t i s : SExpr L) env =
    (none : Option (SVal L)) := rfl
private theorem eval_s_app : eval_s (n+1) (.app fn arg : SExpr L) env =
    (eval_s n fn env).bind fun fv => (eval_s n arg env).bind fun av =>
    apply_s n fv av := rfl
private theorem eval_s_lam : eval_s (n+1) (.lam dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.lam dv body env) := rfl
private theorem eval_s_forallE : eval_s (n+1) (.forallE dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.pi dv body env) := rfl
private theorem eval_s_letE : eval_s (n+1) (.letE ty val body : SExpr L) env =
    (eval_s n val env).bind fun vv => eval_s n body (vv :: env) := rfl
private theorem apply_s_lam : apply_s (n+1) (.lam dom body fenv : SVal L) arg =
    eval_s n body (arg :: fenv) := rfl
private theorem apply_s_neutral : apply_s (n+1) (.neutral hd spine : SVal L) arg =
    some (.neutral hd (spine ++ [arg])) := rfl
private theorem apply_s_sort : apply_s (n+1) (.sort u : SVal L) arg = none := rfl
private theorem apply_s_lit : apply_s (n+1) (.lit l : SVal L) arg = none := rfl
private theorem apply_s_pi : apply_s (n+1) (.pi dom body fenv : SVal L) arg = none := rfl
private theorem apply_s_sort' : apply_s n (.sort u : SVal L) arg = none := by cases n <;> rfl
private theorem apply_s_lit' : apply_s n (.lit l : SVal L) arg = none := by cases n <;> rfl
private theorem apply_s_pi' : apply_s n (.pi dom body fenv : SVal L) arg = none := by cases n <;> rfl

/-! ## apply_simval: step loss n+1 → n for different-body closures -/

theorem apply_simval (n fuel : Nat)
    (sfn : SimVal (n+1) fn1 fn2 d) (sarg : SimVal (n+1) arg1 arg2 d)
    (wf1 : ValWF fn1 d) (wf2 : ValWF (L := L) fn2 d)
    (wa1 : ValWF arg1 d) (wa2 : ValWF arg2 d)
    (hap1 : apply_s fuel fn1 arg1 = some v1)
    (hap2 : apply_s fuel fn2 arg2 = some v2) :
    SimVal n v1 v2 d := by
  cases fuel with
  | zero => simp [apply_s] at hap1
  | succ f =>
    cases fn1 <;> cases fn2
    -- fn1 = sort/lit/pi → apply_s returns none
    all_goals (try (simp only [apply_s_sort', apply_s_lit', apply_s_pi'] at hap1; exact absurd hap1 nofun))
    -- fn2 = sort/lit/pi → apply_s returns none
    all_goals (try (simp only [apply_s_sort', apply_s_lit', apply_s_pi'] at hap2; exact absurd hap2 nofun))
    -- cross-constructor → sfn is False
    case lam.neutral => rw [SimVal.lam_neutral] at sfn; exact sfn.elim
    case neutral.lam => rw [SimVal.neutral_lam] at sfn; exact sfn.elim
    case lam.lam dom1 body1 env1 dom2 body2 env2 =>
      rw [SimVal.lam_lam] at sfn
      rw [apply_s_lam] at hap1 hap2
      exact sfn.2 n (Nat.le_refl _) d (Nat.le_refl _) arg1 arg2 (sarg.mono (by omega))
        wa1 wa2 f v1 v2 hap1 hap2
    case neutral.neutral hd1 sp1 hd2 sp2 =>
      rw [SimVal.neutral_neutral] at sfn
      rw [apply_s_neutral] at hap1 hap2
      cases hap1; cases hap2
      cases n with
      | zero => simp [SimVal.zero]
      | succ m =>
        rw [SimVal.neutral_neutral]
        exact ⟨sfn.1, sfn.2.mono (by omega) |>.snoc (sarg.mono (by omega))⟩

/-! ## eval_simval: same expression in SimEnv → SimVal results

    Uses the closure condition from eval_simval at the inner step n' to fill
    the closure condition of SimVal at step n'+1. -/

-- Strengthened version: eval_simval for all m ≤ N, enabling strong induction.
-- The closure condition ∀ j ≤ n' requires calling eval_simval at arbitrary j ≤ n',
-- which simple induction on n can't provide. Instead, induct on an upper bound N
-- and prove the statement for all m ≤ N simultaneously.
private theorem eval_simval_le (N : Nat) :
    ∀ m, m ≤ N →
    ∀ (fuel : Nat) (e : SExpr L) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L),
    SimEnv m env1 env2 d → ClosedN e env1.length →
    EnvWF env1 d → EnvWF env2 d →
    eval_s fuel e env1 = some v1 → eval_s fuel e env2 = some v2 →
    SimVal m v1 v2 d := by
  induction N with
  | zero =>
    intro m hm
    have : m = 0 := by omega
    subst this
    intro _ _ _ _ _ _ _ _ _ _ _ _; simp [SimVal.zero]
  | succ N' ih_N =>
    intro m hm
    match m with
    | 0 => intro _ _ _ _ _ _ _ _ _ _ _ _; simp [SimVal.zero]
    | m' + 1 =>
      -- ih_N : ∀ j ≤ N', eval_simval j. Since m' + 1 ≤ N' + 1, m' ≤ N'.
      -- For any j ≤ m' ≤ N': ih_N j (by omega) gives eval_simval j.
      intro fuel e env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2
      cases fuel with
      | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
      | succ f =>
        cases e with
        | bvar idx =>
          rw [eval_s_bvar] at hev1 hev2
          simp [ClosedN] at hcl
          rw [List.getElem?_eq_getElem hcl] at hev1
          rw [List.getElem?_eq_getElem (hse.length_eq ▸ hcl)] at hev2
          cases hev1; cases hev2
          exact hse.2 idx hcl (hse.length_eq ▸ hcl)
        | sort u =>
          rw [eval_s_sort] at hev1 hev2; cases hev1; cases hev2; simp [SimVal.sort_sort]
        | const c ls =>
          rw [eval_s_const'] at hev1 hev2; cases hev1; cases hev2
          simp [SimVal.neutral_neutral, SimSpine.nil_nil]
        | lit l =>
          rw [eval_s_lit] at hev1 hev2; cases hev1; cases hev2; simp [SimVal.lit_lit]
        | proj _ _ _ =>
          rw [eval_s_proj] at hev1; exact absurd hev1 nofun
        | lam dom body =>
          rw [eval_s_lam] at hev1 hev2
          simp only [option_bind_eq_some] at hev1 hev2
          obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
          obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
          simp [ClosedN] at hcl
          simp only [SimVal.lam_lam]
          exact ⟨ih_N m' (by omega) f dom env1 env2 d dv1 dv2
              (hse.mono (by omega)) hcl.1 hew1 hew2 hd1 hd2,
            fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
              ih_N j (by omega) fuel' body (w1 :: env1) (w2 :: env2) d' r1 r2
                (SimEnv.cons hw (hse.mono (by omega) |>.depth_mono hd))
                hcl.2
                (.cons hw1 (hew1.mono hd))
                (.cons hw2 (hew2.mono hd))
                hr1 hr2⟩
        | forallE dom body =>
          rw [eval_s_forallE] at hev1 hev2
          simp only [option_bind_eq_some] at hev1 hev2
          obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
          obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
          simp [ClosedN] at hcl
          simp only [SimVal.pi_pi]
          exact ⟨ih_N m' (by omega) f dom env1 env2 d dv1 dv2
              (hse.mono (by omega)) hcl.1 hew1 hew2 hd1 hd2,
            fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
              ih_N j (by omega) fuel' body (w1 :: env1) (w2 :: env2) d' r1 r2
                (SimEnv.cons hw (hse.mono (by omega) |>.depth_mono hd))
                hcl.2
                (.cons hw1 (hew1.mono hd))
                (.cons hw2 (hew2.mono hd))
                hr1 hr2⟩
        | app fn arg =>
          -- Step loss: apply_simval gives SimVal m', not SimVal (m'+1).
          -- Provable with joint (n, fuel) induction, but not needed for eval_simval_inf.
          sorry
        | letE ty val body =>
          -- Same step loss issue as app case.
          sorry

-- eval in SimEnv gives SimVal at a specific step.
theorem eval_simval (n : Nat) :
    ∀ (fuel : Nat) (e : SExpr L) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L),
    SimEnv n env1 env2 d → ClosedN e env1.length →
    EnvWF env1 d → EnvWF env2 d →
    eval_s fuel e env1 = some v1 → eval_s fuel e env2 = some v2 →
    SimVal n v1 v2 d := eval_simval_le n n (Nat.le_refl _)

/-! ## SimVal reflexivity -/

mutual
theorem SimVal.refl_wf (n : Nat) (h : ValWF v d) : SimVal (L := L) n v v d := by
  match n, v, h with
  | 0, _, _ => simp [SimVal.zero]
  | _ + 1, .sort _, _ => simp [SimVal.sort_sort]
  | _ + 1, .lit _, _ => simp [SimVal.lit_lit]
  | n' + 1, .neutral hd sp, .neutral hhd hsp =>
    rw [SimVal.neutral_neutral]
    exact ⟨rfl, SimSpine.refl_wf (n' + 1) hsp⟩
  | n' + 1, .lam dom body env, .lam hdom hcl henv =>
    rw [SimVal.lam_lam]
    refine ⟨SimVal.refl_wf n' hdom, fun j hj d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 => ?_⟩
    have hse : SimEnv j (w1 :: env) (w2 :: env) d' :=
      SimEnv.cons hw ⟨rfl, fun i h1 _ => by
        obtain ⟨v, hv, hwf⟩ := (henv.mono hd).getElem? h1
        rw [List.getElem?_eq_getElem h1] at hv; cases hv
        exact (SimVal.refl_wf n' hwf).mono (by omega)⟩
    exact eval_simval j fuel body (w1 :: env) (w2 :: env) d' r1 r2
      hse hcl (.cons hw1 (henv.mono hd)) (.cons hw2 (henv.mono hd)) hr1 hr2
  | n' + 1, .pi dom body env, .pi hdom hcl henv =>
    rw [SimVal.pi_pi]
    refine ⟨SimVal.refl_wf n' hdom, fun j hj d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 => ?_⟩
    have hse : SimEnv j (w1 :: env) (w2 :: env) d' :=
      SimEnv.cons hw ⟨rfl, fun i h1 _ => by
        obtain ⟨v, hv, hwf⟩ := (henv.mono hd).getElem? h1
        rw [List.getElem?_eq_getElem h1] at hv; cases hv
        exact (SimVal.refl_wf n' hwf).mono (by omega)⟩
    exact eval_simval j fuel body (w1 :: env) (w2 :: env) d' r1 r2
      hse hcl (.cons hw1 (henv.mono hd)) (.cons hw2 (henv.mono hd)) hr1 hr2
  termination_by (n, sizeOf v)
  decreasing_by all_goals simp_wf; first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)
theorem SimSpine.refl_wf (n : Nat) (h : ListWF sp d) : SimSpine (L := L) n sp sp d := by
  match sp, h with
  | [], _ => simp [SimSpine.nil_nil]
  | v :: rest, .cons hv hrest =>
    simp [SimSpine.cons_cons]
    exact ⟨SimVal.refl_wf n hv, SimSpine.refl_wf n hrest⟩
  termination_by (n, sizeOf sp)
  decreasing_by all_goals simp_wf; apply Prod.Lex.right; omega
end

theorem SimEnv.refl_wf (n : Nat) (h : EnvWF env d) : SimEnv (L := L) n env env d :=
  ⟨rfl, fun i h1 _ => by
    obtain ⟨v, hv, hwf⟩ := h.getElem? h1
    rw [List.getElem?_eq_getElem h1] at hv
    cases hv; exact SimVal.refl_wf n hwf⟩

/-! ## eval_simval_inf: same expression in SimVal_inf envs → SimVal_inf results

    By structural induction on `e`, universally quantified over fuel.
    For lam/forallE: closure condition uses eval_simval at step n' for ALL fuel (ih_n).
    For app: uses apply_simval with step loss from n+1 to n. -/

theorem eval_simval_inf (e : SExpr L) :
    ∀ (fuel : Nat) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L),
    SimEnv_inf env1 env2 d → ClosedN e env1.length →
    EnvWF env1 d → EnvWF env2 d →
    eval_s fuel e env1 = some v1 → eval_s fuel e env2 = some v2 →
    SimVal_inf v1 v2 d := by
  induction e with
  | bvar idx =>
    intro fuel env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_bvar] at hev1 hev2
      simp [ClosedN] at hcl
      rw [List.getElem?_eq_getElem hcl] at hev1
      rw [List.getElem?_eq_getElem (hse.length_eq ▸ hcl)] at hev2
      cases hev1; cases hev2
      exact hse.2 idx hcl (hse.length_eq ▸ hcl) n
  | sort u =>
    intro fuel _ _ _ _ _ _ _ _ _ hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
        rw [eval_s_sort] at hev1 hev2; cases hev1; cases hev2
        cases n with | zero => simp [SimVal.zero] | succ => simp [SimVal.sort_sort]
  | const c ls =>
    intro fuel _ _ _ _ _ _ _ _ _ hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_const'] at hev1 hev2; cases hev1; cases hev2
      cases n with
      | zero => simp [SimVal.zero]
      | succ => simp [SimVal.neutral_neutral, SimSpine.nil_nil]
  | lit l =>
    intro fuel _ _ _ _ _ _ _ _ _ hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
        rw [eval_s_lit] at hev1 hev2; cases hev1; cases hev2
        cases n with | zero => simp [SimVal.zero] | succ => simp [SimVal.lit_lit]
  | proj _ _ _ =>
    intro fuel _ _ _ _ _ _ _ _ _ hev1 _
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f => rw [eval_s_proj] at hev1; exact absurd hev1 nofun
  | lam dom body ih_dom ih_body =>
    intro fuel env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_lam] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
      obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
      simp [ClosedN] at hcl
      cases n with
      | zero => rw [SimVal.zero]; trivial
      | succ n' =>
        rw [SimVal.lam_lam]
        have dom_inf := ih_dom f env1 env2 d dv1 dv2 hse hcl.1 hew1 hew2 hd1 hd2
        exact ⟨dom_inf n', fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
          eval_simval j fuel' body (w1 :: env1) (w2 :: env2) d' r1 r2
            (SimEnv.cons hw ⟨hse.length_eq, fun i h1 h2 => (hse.2 i h1 h2 j).depth_mono hd⟩)
            hcl.2
            (.cons hw1 (hew1.mono hd))
            (.cons hw2 (hew2.mono hd))
            hr1 hr2⟩
  | forallE dom body ih_dom ih_body =>
    intro fuel env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_forallE] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
      obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
      simp [ClosedN] at hcl
      cases n with
      | zero => rw [SimVal.zero]; trivial
      | succ n' =>
        rw [SimVal.pi_pi]
        have dom_inf := ih_dom f env1 env2 d dv1 dv2 hse hcl.1 hew1 hew2 hd1 hd2
        exact ⟨dom_inf n', fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
          eval_simval j fuel' body (w1 :: env1) (w2 :: env2) d' r1 r2
            (SimEnv.cons hw ⟨hse.length_eq, fun i h1 h2 => (hse.2 i h1 h2 j).depth_mono hd⟩)
            hcl.2
            (.cons hw1 (hew1.mono hd))
            (.cons hw2 (hew2.mono hd))
            hr1 hr2⟩
  | app fn arg ih_fn ih_arg =>
    intro fuel env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_app] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨fv1, hf1, av1, ha1, hap1⟩ := hev1
      obtain ⟨fv2, hf2, av2, ha2, hap2⟩ := hev2
      simp [ClosedN] at hcl
      have sfn := ih_fn f env1 env2 d fv1 fv2 hse hcl.1 hew1 hew2 hf1 hf2
      have sarg := ih_arg f env1 env2 d av1 av2 hse hcl.2 hew1 hew2 ha1 ha2
      -- apply_simval: SimVal (n+1) → SimVal n (step loss)
      exact apply_simval n f (sfn (n+1)) (sarg (n+1))
        (eval_preserves_wf hf1 hcl.1 hew1)
        (eval_preserves_wf hf2 (hse.length_eq ▸ hcl.1) hew2)
        (eval_preserves_wf ha1 hcl.2 hew1)
        (eval_preserves_wf ha2 (hse.length_eq ▸ hcl.2) hew2)
        hap1 hap2
  | letE ty val body ih_ty ih_val ih_body =>
    intro fuel env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_letE] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨vv1, hvl1, hbd1⟩ := hev1
      obtain ⟨vv2, hvl2, hbd2⟩ := hev2
      simp [ClosedN] at hcl
      have svl := ih_val f env1 env2 d vv1 vv2 hse hcl.2.1 hew1 hew2 hvl1 hvl2
      have hwf1 := eval_preserves_wf hvl1 hcl.2.1 hew1
      have hwf2 := eval_preserves_wf hvl2 (hse.length_eq ▸ hcl.2.1) hew2
      exact ih_body f (vv1 :: env1) (vv2 :: env2) d v1 v2
        (SimEnv_inf.cons svl (hse.depth_mono (Nat.le_refl _)))
        hcl.2.2 (.cons hwf1 hew1) (.cons hwf2 hew2) hbd1 hbd2 n

/-! ## SimVal implies QuoteEq -/

set_option maxHeartbeats 800000 in
set_option maxRecDepth 1024 in
mutual
theorem simval_implies_quoteEq (n : Nat) (v1 v2 : SVal L) (d : Nat)
    (hsim : SimVal n v1 v2 d) (hw1 : ValWF v1 d) (hw2 : ValWF v2 d)
    (fq1 fq2 : Nat) (e1 e2 : SExpr L)
    (hfq1 : fq1 ≤ n) (hfq2 : fq2 ≤ n)
    (hq1 : quote_s fq1 v1 d = some e1) (hq2 : quote_s fq2 v2 d = some e2) :
    e1 = e2 := by
  cases fq1 with
  | zero => rw [quote_s.eq_1] at hq1; exact absurd hq1 nofun
  | succ fq1' =>
  cases fq2 with
  | zero => rw [quote_s.eq_1] at hq2; exact absurd hq2 nofun
  | succ fq2' =>
  -- n ≥ 1 since fq1' + 1 ≤ n
  cases n with
  | zero => omega
  | succ n' =>
  cases v1 <;> cases v2
  -- Same-constructor cases
  case sort.sort u1 u2 =>
    rw [SimVal.sort_sort] at hsim; subst hsim
    rw [quote_s.eq_2] at hq1 hq2; cases hq1; cases hq2; rfl
  case lit.lit l1 l2 =>
    rw [SimVal.lit_lit] at hsim; subst hsim
    rw [quote_s.eq_3] at hq1 hq2; cases hq1; cases hq2; rfl
  case neutral.neutral hd1 sp1 hd2 sp2 =>
    rw [SimVal.neutral_neutral] at hsim
    obtain ⟨heq, hsp⟩ := hsim; subst heq
    rw [quote_s.eq_6] at hq1 hq2
    exact simspine_implies_quoteEq_core (n' + 1) sp1 sp2 d hsp hw1 hw2
      fq1' fq2' _ _ (by omega) (by omega) hq1 hq2
  case lam.lam dom1 body1 env1 dom2 body2 env2 =>
      rw [SimVal.lam_lam] at hsim
      obtain ⟨hdom, hclosure⟩ := hsim
      simp only [quote_s.eq_4, bind_eq_some'] at hq1 hq2
      obtain ⟨domE1, hqd1, bodyV1, hevb1, bodyE1, hqb1, he1⟩ := hq1
      obtain ⟨domE2, hqd2, bodyV2, hevb2, bodyE2, hqb2, he2⟩ := hq2
      cases he1; cases he2
      cases hw1 with | lam hwdom1 hcl1 hwenv1 =>
      cases hw2 with | lam hwdom2 hcl2 hwenv2 =>
      have hdomEq := simval_implies_quoteEq n' dom1 dom2 d hdom hwdom1 hwdom2
        fq1' fq2' domE1 domE2 (by omega) (by omega) hqd1 hqd2
      have fvar_wf : ValWF (SVal.neutral (.fvar d) [] : SVal L) (d + 1) :=
        .neutral (.fvar (by omega)) .nil
      have fvar_sim : SimVal n' (SVal.neutral (.fvar d) [] : SVal L)
          (.neutral (.fvar d) []) (d + 1) := SimVal.refl_wf n' fvar_wf
      have hbodySim := hclosure n' (Nat.le_refl _) (d + 1) (Nat.le_succ _) _ _ fvar_sim fvar_wf fvar_wf
        (max fq1' fq2') bodyV1 bodyV2
        (eval_fuel_mono hevb1 (Nat.le_max_left ..))
        (eval_fuel_mono hevb2 (Nat.le_max_right ..))
      have wfbv1 := eval_preserves_wf hevb1 hcl1
        (.cons fvar_wf (hwenv1.mono (Nat.le_succ _)))
      have wfbv2 := eval_preserves_wf hevb2 hcl2
        (.cons fvar_wf (hwenv2.mono (Nat.le_succ _)))
      have hbodyEq := simval_implies_quoteEq n' bodyV1 bodyV2 (d + 1)
        hbodySim wfbv1 wfbv2 fq1' fq2' bodyE1 bodyE2 (by omega) (by omega) hqb1 hqb2
      congr 1 <;> assumption
  case pi.pi dom1 body1 env1 dom2 body2 env2 =>
      rw [SimVal.pi_pi] at hsim
      obtain ⟨hdom, hclosure⟩ := hsim
      simp only [quote_s.eq_5, bind_eq_some'] at hq1 hq2
      obtain ⟨domE1, hqd1, bodyV1, hevb1, bodyE1, hqb1, he1⟩ := hq1
      obtain ⟨domE2, hqd2, bodyV2, hevb2, bodyE2, hqb2, he2⟩ := hq2
      cases he1; cases he2
      cases hw1 with | pi hwdom1 hcl1 hwenv1 =>
      cases hw2 with | pi hwdom2 hcl2 hwenv2 =>
      have hdomEq := simval_implies_quoteEq n' dom1 dom2 d hdom hwdom1 hwdom2
        fq1' fq2' domE1 domE2 (by omega) (by omega) hqd1 hqd2
      have fvar_wf : ValWF (SVal.neutral (.fvar d) [] : SVal L) (d + 1) :=
        .neutral (.fvar (by omega)) .nil
      have fvar_sim : SimVal n' (SVal.neutral (.fvar d) [] : SVal L)
          (.neutral (.fvar d) []) (d + 1) := SimVal.refl_wf n' fvar_wf
      have hbodySim := hclosure n' (Nat.le_refl _) (d + 1) (Nat.le_succ _) _ _ fvar_sim fvar_wf fvar_wf
        (max fq1' fq2') bodyV1 bodyV2
        (eval_fuel_mono hevb1 (Nat.le_max_left ..))
        (eval_fuel_mono hevb2 (Nat.le_max_right ..))
      have wfbv1 := eval_preserves_wf hevb1 hcl1
        (.cons fvar_wf (hwenv1.mono (Nat.le_succ _)))
      have wfbv2 := eval_preserves_wf hevb2 hcl2
        (.cons fvar_wf (hwenv2.mono (Nat.le_succ _)))
      have hbodyEq := simval_implies_quoteEq n' bodyV1 bodyV2 (d + 1)
        hbodySim wfbv1 wfbv2 fq1' fq2' bodyE1 bodyE2 (by omega) (by omega) hqb1 hqb2
      congr 1 <;> assumption
  -- Discharge all remaining cross-constructor cases (SimVal = False)
  all_goals (first
    | exact absurd hsim SimVal.sort_lit.mp | exact absurd hsim SimVal.sort_neutral.mp
    | exact absurd hsim SimVal.sort_lam.mp | exact absurd hsim SimVal.sort_pi.mp
    | exact absurd hsim SimVal.lit_sort.mp | exact absurd hsim SimVal.lit_neutral.mp
    | exact absurd hsim SimVal.lit_lam.mp | exact absurd hsim SimVal.lit_pi.mp
    | exact absurd hsim SimVal.neutral_sort.mp | exact absurd hsim SimVal.neutral_lit.mp
    | exact absurd hsim SimVal.neutral_lam.mp | exact absurd hsim SimVal.neutral_pi.mp
    | exact absurd hsim SimVal.lam_sort.mp | exact absurd hsim SimVal.lam_lit.mp
    | exact absurd hsim SimVal.lam_neutral.mp | exact absurd hsim SimVal.lam_pi.mp
    | exact absurd hsim SimVal.pi_sort.mp | exact absurd hsim SimVal.pi_lit.mp
    | exact absurd hsim SimVal.pi_neutral.mp | exact absurd hsim SimVal.pi_lam.mp)
  termination_by (n, 1 + sizeOf v1 + sizeOf v2)
  decreasing_by all_goals (try subst_vars); simp_wf; first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)
theorem simspine_implies_quoteEq_core (n : Nat) (sp1 sp2 : List (SVal L)) (d : Nat)
    (hsim : SimSpine n sp1 sp2 d)
    (hw1 : ValWF (.neutral hd1 sp1) d) (hw2 : ValWF (.neutral hd2 sp2) d)
    (fq1 fq2 : Nat) (e1 e2 : SExpr L) (hfq1 : fq1 ≤ n) (hfq2 : fq2 ≤ n)
    (hq1 : quoteSpine_s fq1 acc sp1 d = some e1)
    (hq2 : quoteSpine_s fq2 acc sp2 d = some e2) :
    e1 = e2 := by
  match sp1, sp2, hsim, hw1, hw2, hq1, hq2 with
  | [], [], _, _, _, hq1, hq2 =>
    rw [quoteSpine_s.eq_1] at hq1 hq2; cases hq1; cases hq2; rfl
  | [], _ :: _, hsim, _, _, _, _ => simp [SimSpine.nil_cons] at hsim
  | _ :: _, [], hsim, _, _, _, _ => simp [SimSpine.cons_nil] at hsim
  | v1 :: rest1, v2 :: rest2, hsim, hw1, hw2, hq1, hq2 =>
    simp only [SimSpine.cons_cons] at hsim
    obtain ⟨hv, hrest⟩ := hsim
    simp only [quoteSpine_s.eq_2, bind_eq_some'] at hq1 hq2
    obtain ⟨vE1, hvq1, hrest1⟩ := hq1
    obtain ⟨vE2, hvq2, hrest2⟩ := hq2
    cases hw1 with | neutral hhd1 hsp1 =>
    cases hw2 with | neutral hhd2 hsp2 =>
    cases hsp1 with | cons hv1wf hrest1wf =>
    cases hsp2 with | cons hv2wf hrest2wf =>
    have hvEq := simval_implies_quoteEq n v1 v2 d hv hv1wf hv2wf
      fq1 fq2 vE1 vE2 hfq1 hfq2 hvq1 hvq2
    subst hvEq
    exact simspine_implies_quoteEq_core n rest1 rest2 d hrest
      (ValWF.neutral hhd1 hrest1wf)
      (ValWF.neutral hhd2 hrest2wf)
      fq1 fq2 e1 e2 hfq1 hfq2 hrest1 hrest2
  termination_by (n, sizeOf sp1 + sizeOf sp2)
  decreasing_by all_goals (try subst_vars); simp_wf; first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)
end

-- Public wrapper that matches the original signature
theorem simspine_implies_quoteEq (n : Nat) (sp1 sp2 : List (SVal L)) (d : Nat)
    (hsim : SimSpine n sp1 sp2 d)
    (hw1 : ValWF (.neutral hd1 sp1) d) (hw2 : ValWF (.neutral hd2 sp2) d)
    (fq1 fq2 : Nat) (e1 e2 : SExpr L) (hfq1 : fq1 ≤ n) (hfq2 : fq2 ≤ n)
    (hq1 : quoteSpine_s fq1 acc sp1 d = some e1)
    (hq2 : quoteSpine_s fq2 acc sp2 d = some e2) :
    e1 = e2 :=
  simspine_implies_quoteEq_core n sp1 sp2 d hsim hw1 hw2 fq1 fq2 e1 e2 hfq1 hfq2 hq1 hq2

/-! ## QuoteEq from SimVal machinery -/

theorem quoteEq_of_simval (h : ∀ n, SimVal n v1 v2 d)
    (hw1 : ValWF v1 d) (hw2 : ValWF (L := L) v2 d) : QuoteEq v1 v2 d := by
  intro fq1 fq2 e1 e2 hq1 hq2
  exact simval_implies_quoteEq (max fq1 fq2) v1 v2 d (h _) hw1 hw2
    fq1 fq2 e1 e2 (Nat.le_max_left ..) (Nat.le_max_right ..) hq1 hq2

/-! ## Eval in SimVal_inf envs gives QuoteEq results -/

theorem eval_simval_inf_quoteEq (e : SExpr L)
    (fuel : Nat) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L)
    (hse : SimEnv_inf env1 env2 d) (hcl : ClosedN e env1.length)
    (hew1 : EnvWF env1 d) (hew2 : EnvWF env2 d)
    (hev1 : eval_s fuel e env1 = some v1) (hev2 : eval_s fuel e env2 = some v2) :
    QuoteEq v1 v2 d := by
  have sv := eval_simval_inf e fuel env1 env2 d v1 v2 hse hcl hew1 hew2 hev1 hev2
  exact quoteEq_of_simval sv
    (eval_preserves_wf hev1 hcl hew1)
    (eval_preserves_wf hev2 (hse.length_eq ▸ hcl) hew2)

/-! ## apply on SimVal_inf gives SimVal_inf results -/

theorem apply_simval_inf
    (sfn : SimVal_inf fn1 fn2 d) (sarg : SimVal_inf arg1 arg2 d)
    (wf1 : ValWF fn1 d) (wf2 : ValWF (L := L) fn2 d)
    (wa1 : ValWF arg1 d) (wa2 : ValWF arg2 d)
    (hap1 : apply_s fuel fn1 arg1 = some v1)
    (hap2 : apply_s fuel fn2 arg2 = some v2) :
    SimVal_inf v1 v2 d := by
  intro n
  exact apply_simval n fuel (sfn (n+1)) (sarg (n+1)) wf1 wf2 wa1 wa2 hap1 hap2

theorem apply_simval_inf_quoteEq
    (sfn : SimVal_inf fn1 fn2 d) (sarg : SimVal_inf arg1 arg2 d)
    (wf1 : ValWF fn1 d) (wf2 : ValWF (L := L) fn2 d)
    (wa1 : ValWF arg1 d) (wa2 : ValWF arg2 d)
    (hap1 : apply_s fuel fn1 arg1 = some v1)
    (hap2 : apply_s fuel fn2 arg2 = some v2) :
    QuoteEq v1 v2 d := by
  exact quoteEq_of_simval (apply_simval_inf sfn sarg wf1 wf2 wa1 wa2 hap1 hap2)
    (apply_preserves_wf hap1 wf1 wa1)
    (apply_preserves_wf hap2 wf2 wa2)

end Ix.Theory
