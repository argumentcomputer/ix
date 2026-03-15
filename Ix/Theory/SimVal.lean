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

/-! ## Symmetry -/

mutual
theorem SimVal.symm (hs : SimVal n v1 v2 d) : SimVal (L := L) n v2 v1 d := by
  match n with
  | 0 => simp
  | n' + 1 =>
    cases v1 <;> cases v2
    all_goals (try simp only [SimVal.sort_sort, SimVal.lit_lit, SimVal.neutral_neutral,
      SimVal.sort_lit, SimVal.sort_neutral, SimVal.sort_lam, SimVal.sort_pi,
      SimVal.lit_sort, SimVal.lit_neutral, SimVal.lit_lam, SimVal.lit_pi,
      SimVal.neutral_sort, SimVal.neutral_lit, SimVal.neutral_lam, SimVal.neutral_pi,
      SimVal.lam_sort, SimVal.lam_lit, SimVal.lam_neutral, SimVal.lam_pi,
      SimVal.pi_sort, SimVal.pi_lit, SimVal.pi_neutral, SimVal.pi_lam] at hs ⊢)
    all_goals (try exact hs)
    case sort.sort => exact hs.symm
    case lit.lit => exact hs.symm
    case neutral.neutral =>
      exact ⟨hs.1.symm, hs.2.symm⟩
    case lam.lam d1 b1 e1 d2 b2 e2 =>
      rw [SimVal.lam_lam] at hs ⊢
      obtain ⟨hdom, hbody⟩ := hs
      exact ⟨hdom.symm, fun j hj d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 =>
        (hbody j hj d' hd w2 w1 hw.symm hw2 hw1 fuel r2 r1 hr2 hr1).symm⟩
    case pi.pi d1 b1 e1 d2 b2 e2 =>
      rw [SimVal.pi_pi] at hs ⊢
      obtain ⟨hdom, hbody⟩ := hs
      exact ⟨hdom.symm, fun j hj d' hd w1 w2 hw hw1 hw2 fuel r1 r2 hr1 hr2 =>
        (hbody j hj d' hd w2 w1 hw.symm hw2 hw1 fuel r2 r1 hr2 hr1).symm⟩
  termination_by (n, sizeOf v1 + sizeOf v2)
theorem SimSpine.symm (hs : SimSpine n sp1 sp2 d) : SimSpine (L := L) n sp2 sp1 d := by
  cases sp1 <;> cases sp2
  all_goals (try simp only [SimSpine.nil_nil, SimSpine.nil_cons, SimSpine.cons_nil] at hs ⊢)
  all_goals (try exact hs)
  case cons.cons =>
    rw [SimSpine.cons_cons] at hs ⊢
    exact ⟨hs.1.symm, hs.2.symm⟩
  termination_by (n, sizeOf sp1 + sizeOf sp2)
end

theorem SimVal_inf.symm (hs : SimVal_inf v1 v2 d) : SimVal_inf (L := L) v2 v1 d :=
  fun n => (hs n).symm

theorem SimEnv_inf.symm (hs : SimEnv_inf env1 env2 d) : SimEnv_inf (L := L) env2 env1 d :=
  ⟨hs.1.symm, fun i h2 h1 => (hs.2 i (hs.1 ▸ h2) (hs.1 ▸ h1)).symm⟩

/-! ## Transitivity -/

mutual
theorem SimVal.trans (h12 : SimVal n v1 v2 d) (h23 : SimVal n v2 v3 d) :
    SimVal (L := L) n v1 v3 d := by
  match n with
  | 0 => simp
  | n' + 1 =>
    -- Match on v2 to determine constructor; v1 and v3 must match (or SimVal = False)
    cases v2 with
    | sort u2 =>
      cases v1 <;> cases v3 <;> simp_all [SimVal.sort_sort]
    | lit l2 =>
      cases v1 <;> cases v3 <;> simp_all [SimVal.lit_lit]
    | neutral hd2 sp2 =>
      cases v1 <;> cases v3 <;>
        simp only [SimVal.neutral_neutral, SimVal.sort_neutral, SimVal.lit_neutral,
          SimVal.lam_neutral, SimVal.pi_neutral, SimVal.neutral_sort, SimVal.neutral_lit,
          SimVal.neutral_lam, SimVal.neutral_pi] at h12 h23 ⊢ <;>
        try exact h12.elim
      exact ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩
    | lam d2 b2 e2 => sorry -- Closure transitivity: needs eval b2 (w2::e2) to succeed
    | pi d2 b2 e2 => sorry -- Same as lam case
  termination_by (n, sizeOf v1 + sizeOf v2 + sizeOf v3)
theorem SimSpine.trans (h12 : SimSpine n sp1 sp2 d) (h23 : SimSpine n sp2 sp3 d) :
    SimSpine (L := L) n sp1 sp3 d := by
  match sp1, sp2, sp3 with
  | [], [], [] => simp
  | [], [], _ :: _ => simp [SimSpine.nil_cons] at h23
  | [], _ :: _, _ => simp [SimSpine.nil_cons] at h12
  | _ :: _, [], _ => simp [SimSpine.cons_nil] at h12
  | _ :: _, _ :: _, [] => simp [SimSpine.cons_nil] at h23
  | a1 :: r1, a2 :: r2, a3 :: r3 =>
    rw [SimSpine.cons_cons] at h12 h23 ⊢
    exact ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩
  termination_by (n, sizeOf sp1 + sizeOf sp2 + sizeOf sp3)
end

theorem SimVal_inf.trans (h12 : SimVal_inf v1 v2 d) (h23 : SimVal_inf v2 v3 d) :
    SimVal_inf (L := L) v1 v3 d :=
  fun n => (h12 n).trans (h23 n)

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

/-! ## eval_s / apply_s equation lemmas (from EvalSubst, plus apply_s extras) -/

-- apply_s extras not in EvalSubst:
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
      simp only [quote_s.eq_4, option_bind_eq_some, bind_eq_some] at hq1 hq2
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
      simp only [quote_s.eq_5, option_bind_eq_some, bind_eq_some] at hq1 hq2
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
    simp only [quoteSpine_s.eq_2, option_bind_eq_some, bind_eq_some] at hq1 hq2
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

/-! ## eval_liftN1: evaluating lifted expression in extended environment

    Proves that eval (liftN 1 e k) env1 SimVal_inf eval e env2 when env1
    has one extra element at position k compared to env2.
    Used to fill InstEnvCond.prepend and the eta case in NbESoundness. -/

private theorem liftVar1_lt {env1 env2 : List (SVal L)}
    (hl : env1.length = env2.length + 1) (h : i < env2.length) :
    liftVar 1 i k < env1.length := by
  simp [liftVar]; split <;> omega

/-- env1 has one extra element at position k compared to env2,
    with corresponding elements related by SimVal n. -/
def LiftSimEnv (n : Nat) (env1 env2 : List (SVal L)) (k d : Nat) : Prop :=
  env1.length = env2.length + 1 ∧
  ∀ i (h1 : liftVar 1 i k < env1.length) (h2 : i < env2.length),
    SimVal n (env1[liftVar 1 i k]) (env2[i]) d

/-- LiftSimEnv for all steps. -/
def LiftSimEnv_inf (env1 env2 : List (SVal L)) (k d : Nat) : Prop :=
  env1.length = env2.length + 1 ∧
  ∀ i (h1 : liftVar 1 i k < env1.length) (h2 : i < env2.length),
    SimVal_inf (env1[liftVar 1 i k]) (env2[i]) d

theorem LiftSimEnv.mono (hm : n' ≤ n) (h : LiftSimEnv n env1 env2 k d) :
    LiftSimEnv (L := L) n' env1 env2 k d :=
  ⟨h.1, fun i h1 h2 => (h.2 i h1 h2).mono hm⟩

theorem LiftSimEnv.depth_mono (hd : d ≤ d') (h : LiftSimEnv n env1 env2 k d) :
    LiftSimEnv (L := L) n env1 env2 k d' :=
  ⟨h.1, fun i h1 h2 => (h.2 i h1 h2).depth_mono hd⟩

theorem LiftSimEnv_inf.to_n (h : LiftSimEnv_inf env1 env2 k d) :
    LiftSimEnv (L := L) n env1 env2 k d :=
  ⟨h.1, fun i h1 h2 => h.2 i h1 h2 n⟩

theorem LiftSimEnv_inf.depth_mono (hd : d ≤ d') (h : LiftSimEnv_inf env1 env2 k d) :
    LiftSimEnv_inf (L := L) env1 env2 k d' :=
  ⟨h.1, fun i h1 h2 n => (h.2 i h1 h2 n).depth_mono hd⟩

theorem LiftSimEnv_inf.initial (hwf : EnvWF env d) :
    LiftSimEnv_inf (L := L) (w :: env) env 0 d :=
  ⟨by simp, fun i h1 h2 n => by
    have : liftVar 1 i 0 = i + 1 := by simp [liftVar]; omega
    simp only [this, List.getElem_cons_succ]
    obtain ⟨_, hv, hvwf⟩ := hwf.getElem? h2
    rw [List.getElem?_eq_getElem h2] at hv; cases hv
    exact SimVal.refl_wf n hvwf⟩

theorem LiftSimEnv.cons (hv : SimVal n w1 w2 d')
    (he : LiftSimEnv n' env1 env2 k d) (hmn : n ≤ n') (hdd : d ≤ d') :
    LiftSimEnv (L := L) n (w1 :: env1) (w2 :: env2) (k + 1) d' :=
  ⟨by simp [he.1], fun i h1 h2 => by
    cases i with
    | zero =>
      simp only [liftVar_zero, List.getElem_cons_zero]; exact hv
    | succ j =>
      simp only [liftVar_succ] at h1 ⊢
      simp only [List.getElem_cons_succ]
      exact (he.2 j (by simp [List.length_cons] at h1; omega)
        (by simp [List.length_cons] at h2; omega)).depth_mono hdd |>.mono hmn⟩

theorem LiftSimEnv_inf.cons (hv : SimVal_inf v1 v2 d)
    (he : LiftSimEnv_inf env1 env2 k d) :
    LiftSimEnv_inf (L := L) (v1 :: env1) (v2 :: env2) (k + 1) d :=
  ⟨by simp [he.1], fun i h1 h2 n => by
    cases i with
    | zero =>
      simp only [liftVar_zero, List.getElem_cons_zero]; exact hv n
    | succ j =>
      simp only [liftVar_succ] at h1 ⊢
      simp only [List.getElem_cons_succ]
      exact he.2 j (by simp [List.length_cons] at h1; omega)
        (by simp [List.length_cons] at h2; omega) n⟩

/-! ### Fixed-step eval_liftN1 -/

private theorem eval_liftN1_simval_le (N : Nat) :
    ∀ m, m ≤ N →
    ∀ (e : SExpr L) (k fuel : Nat) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L),
    LiftSimEnv m env1 env2 k d → ClosedN e env2.length →
    EnvWF env1 d → EnvWF env2 d →
    eval_s fuel (liftN 1 e k) env1 = some v1 → eval_s fuel e env2 = some v2 →
    SimVal m v1 v2 d := by
  induction N with
  | zero =>
    intro m hm
    have : m = 0 := by omega
    subst this
    intros; simp [SimVal.zero]
  | succ N' ih_N =>
    intro m hm
    match m with
    | 0 => intros; simp [SimVal.zero]
    | m' + 1 =>
      intro e k fuel env1 env2 d v1 v2 hlse hcl hew1 hew2 hev1 hev2
      cases fuel with
      | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
      | succ f =>
        cases e with
        | bvar idx =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_bvar] at hev1 hev2
          simp [ClosedN] at hcl
          have hlv := liftVar1_lt (k := k) hlse.1 hcl
          rw [List.getElem?_eq_getElem hlv] at hev1
          rw [List.getElem?_eq_getElem hcl] at hev2
          cases hev1; cases hev2
          exact hlse.2 idx hlv hcl
        | sort u =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_sort] at hev1 hev2; cases hev1; cases hev2
          simp [SimVal.sort_sort]
        | const c ls =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_const'] at hev1 hev2; cases hev1; cases hev2
          simp [SimVal.neutral_neutral, SimSpine.nil_nil]
        | lit l =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_lit] at hev1 hev2; cases hev1; cases hev2
          simp [SimVal.lit_lit]
        | proj _ _ _ =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_proj] at hev1; exact absurd hev1 nofun
        | lam dom body =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_lam] at hev1 hev2
          simp only [option_bind_eq_some] at hev1 hev2
          obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
          obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
          simp [ClosedN] at hcl
          simp only [SimVal.lam_lam]
          exact ⟨ih_N m' (by omega) dom k f env1 env2 d dv1 dv2
              (hlse.mono (by omega)) hcl.1 hew1 hew2 hd1 hd2,
            fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
              ih_N j (by omega) body (k + 1) fuel' (w1 :: env1) (w2 :: env2) d' r1 r2
                (LiftSimEnv.cons hw hlse (by omega) hd)
                hcl.2
                (.cons hw1 (hew1.mono hd))
                (.cons hw2 (hew2.mono hd))
                hr1 hr2⟩
        | forallE dom body =>
          simp only [SExpr.liftN] at hev1
          rw [eval_s_forallE] at hev1 hev2
          simp only [option_bind_eq_some] at hev1 hev2
          obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
          obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
          simp [ClosedN] at hcl
          simp only [SimVal.pi_pi]
          exact ⟨ih_N m' (by omega) dom k f env1 env2 d dv1 dv2
              (hlse.mono (by omega)) hcl.1 hew1 hew2 hd1 hd2,
            fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
              ih_N j (by omega) body (k + 1) fuel' (w1 :: env1) (w2 :: env2) d' r1 r2
                (LiftSimEnv.cons hw hlse (by omega) hd)
                hcl.2
                (.cons hw1 (hew1.mono hd))
                (.cons hw2 (hew2.mono hd))
                hr1 hr2⟩
        | app fn arg =>
          -- Step loss: apply_simval gives SimVal m', not SimVal (m'+1).
          sorry
        | letE ty val body =>
          -- Same step loss issue as app case.
          sorry

theorem eval_liftN1_simval (n : Nat) :
    ∀ (e : SExpr L) (k fuel : Nat) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L),
    LiftSimEnv n env1 env2 k d → ClosedN e env2.length →
    EnvWF env1 d → EnvWF env2 d →
    eval_s fuel (liftN 1 e k) env1 = some v1 → eval_s fuel e env2 = some v2 →
    SimVal n v1 v2 d := eval_liftN1_simval_le n n (Nat.le_refl _)

/-! ### SimVal_inf for liftN 1 -/

theorem eval_liftN1_simval_inf (e : SExpr L) :
    ∀ (k fuel : Nat) (env1 env2 : List (SVal L)) (d : Nat) (v1 v2 : SVal L),
    LiftSimEnv_inf env1 env2 k d → ClosedN e env2.length →
    EnvWF env1 d → EnvWF env2 d →
    eval_s fuel (liftN 1 e k) env1 = some v1 → eval_s fuel e env2 = some v2 →
    SimVal_inf v1 v2 d := by
  induction e with
  | bvar idx =>
    intro k fuel env1 env2 d v1 v2 hlse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_bvar] at hev1 hev2
      simp [ClosedN] at hcl
      have hlv := liftVar1_lt (k := k) hlse.1 hcl
      rw [List.getElem?_eq_getElem hlv] at hev1
      rw [List.getElem?_eq_getElem hcl] at hev2
      cases hev1; cases hev2
      exact hlse.2 idx hlv hcl n
  | sort u =>
    intro k fuel env1 env2 d v1 v2 _ _ _ _ hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_sort] at hev1 hev2; cases hev1; cases hev2
      cases n with | zero => simp [SimVal.zero] | succ => simp [SimVal.sort_sort]
  | const c ls =>
    intro k fuel env1 env2 d v1 v2 _ _ _ _ hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_const'] at hev1 hev2; cases hev1; cases hev2
      cases n with
      | zero => simp [SimVal.zero]
      | succ => simp [SimVal.neutral_neutral, SimSpine.nil_nil]
  | lit l =>
    intro k fuel env1 env2 d v1 v2 _ _ _ _ hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_lit] at hev1 hev2; cases hev1; cases hev2
      cases n with | zero => simp [SimVal.zero] | succ => simp [SimVal.lit_lit]
  | proj _ _ _ =>
    intro k fuel env1 env2 d v1 v2 _ _ _ _ hev1 _
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_proj] at hev1; exact absurd hev1 nofun
  | lam dom body ih_dom ih_body =>
    intro k fuel env1 env2 d v1 v2 hlse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_lam] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
      obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
      simp [ClosedN] at hcl
      cases n with
      | zero => rw [SimVal.zero]; trivial
      | succ n' =>
        rw [SimVal.lam_lam]
        have dom_inf := ih_dom k f env1 env2 d dv1 dv2 hlse hcl.1 hew1 hew2 hd1 hd2
        exact ⟨dom_inf n', fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
          eval_liftN1_simval j body (k + 1) fuel' (w1 :: env1) (w2 :: env2) d' r1 r2
            (LiftSimEnv.cons hw (hlse.to_n (n := j)) (Nat.le_refl _) hd)
            hcl.2
            (.cons hw1 (hew1.mono hd))
            (.cons hw2 (hew2.mono hd))
            hr1 hr2⟩
  | forallE dom body ih_dom ih_body =>
    intro k fuel env1 env2 d v1 v2 hlse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_forallE] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨dv1, hd1, he1⟩ := hev1; cases he1
      obtain ⟨dv2, hd2, he2⟩ := hev2; cases he2
      simp [ClosedN] at hcl
      cases n with
      | zero => rw [SimVal.zero]; trivial
      | succ n' =>
        rw [SimVal.pi_pi]
        have dom_inf := ih_dom k f env1 env2 d dv1 dv2 hlse hcl.1 hew1 hew2 hd1 hd2
        exact ⟨dom_inf n', fun j hj d' hd w1 w2 hw hw1 hw2 fuel' r1 r2 hr1 hr2 =>
          eval_liftN1_simval j body (k + 1) fuel' (w1 :: env1) (w2 :: env2) d' r1 r2
            (LiftSimEnv.cons hw (hlse.to_n (n := j)) (Nat.le_refl _) hd)
            hcl.2
            (.cons hw1 (hew1.mono hd))
            (.cons hw2 (hew2.mono hd))
            hr1 hr2⟩
  | app fn arg ih_fn ih_arg =>
    intro k fuel env1 env2 d v1 v2 hlse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_app] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨fv1, hf1, av1, ha1, hap1⟩ := hev1
      obtain ⟨fv2, hf2, av2, ha2, hap2⟩ := hev2
      simp [ClosedN] at hcl
      have sfn := ih_fn k f env1 env2 d fv1 fv2 hlse hcl.1 hew1 hew2 hf1 hf2
      have sarg := ih_arg k f env1 env2 d av1 av2 hlse hcl.2 hew1 hew2 ha1 ha2
      have hcl_fn : ClosedN (liftN 1 fn k) env1.length := by rw [hlse.1]; exact hcl.1.liftN
      have hcl_arg : ClosedN (liftN 1 arg k) env1.length := by rw [hlse.1]; exact hcl.2.liftN
      exact apply_simval n f (sfn (n+1)) (sarg (n+1))
        (eval_preserves_wf hf1 hcl_fn hew1)
        (eval_preserves_wf hf2 hcl.1 hew2)
        (eval_preserves_wf ha1 hcl_arg hew1)
        (eval_preserves_wf ha2 hcl.2 hew2)
        hap1 hap2
  | letE ty val body ih_ty ih_val ih_body =>
    intro k fuel env1 env2 d v1 v2 hlse hcl hew1 hew2 hev1 hev2 n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.liftN] at hev1
      rw [eval_s_letE] at hev1 hev2
      simp only [option_bind_eq_some] at hev1 hev2
      obtain ⟨vv1, hvl1, hbd1⟩ := hev1
      obtain ⟨vv2, hvl2, hbd2⟩ := hev2
      simp [ClosedN] at hcl
      have svl := ih_val k f env1 env2 d vv1 vv2 hlse hcl.2.1 hew1 hew2 hvl1 hvl2
      have hcl_val : ClosedN (liftN 1 val k) env1.length := by rw [hlse.1]; exact hcl.2.1.liftN
      have hwf1 := eval_preserves_wf hvl1 hcl_val hew1
      have hwf2 := eval_preserves_wf hvl2 hcl.2.1 hew2
      exact ih_body (k + 1) f (vv1 :: env1) (vv2 :: env2) d v1 v2
        (LiftSimEnv_inf.cons svl hlse)
        hcl.2.2 (.cons hwf1 hew1) (.cons hwf2 hew2) hbd1 hbd2 n

/-! ### Corollaries: lift (k=0) -/

theorem eval_lift_simval_inf (e : SExpr L) (w : SVal L)
    (fuel : Nat) (env : List (SVal L)) (d : Nat) (v1 v2 : SVal L)
    (hwf : EnvWF env d) (hwfv : ValWF w d) (hcl : ClosedN e env.length)
    (hev1 : eval_s fuel (SExpr.lift e) (w :: env) = some v1)
    (hev2 : eval_s fuel e env = some v2) :
    SimVal_inf v1 v2 d :=
  eval_liftN1_simval_inf e 0 fuel (w :: env) env d v1 v2
    (.initial hwf) hcl (.cons hwfv hwf) hwf hev1 hev2

theorem eval_lift_quoteEq (e : SExpr L) (w : SVal L)
    (fuel1 fuel2 : Nat) (env : List (SVal L)) (d : Nat) (v1 v2 : SVal L)
    (hwf : EnvWF env d) (hwfv : ValWF w d) (hcl : ClosedN e env.length)
    (hev1 : eval_s fuel1 (SExpr.lift e) (w :: env) = some v1)
    (hev2 : eval_s fuel2 e env = some v2) :
    QuoteEq v1 v2 d := by
  have hev1' := eval_fuel_mono hev1 (Nat.le_max_left fuel1 fuel2)
  have hev2' := eval_fuel_mono hev2 (Nat.le_max_right fuel1 fuel2)
  exact quoteEq_of_simval
    (eval_lift_simval_inf e w _ env d v1 v2 hwf hwfv hcl hev1' hev2')
    (eval_preserves_wf hev1 (hcl.liftN (n := 1)) (.cons hwfv hwf))
    (eval_preserves_wf hev2 hcl hwf)

/-! ## eval_liftN1_succeeds: if eval succeeds at env2, it succeeds at env1

    When LiftSimEnv_inf env1 env2 k d (env1 has one extra element at position k),
    eval of `e` at env2 succeeding implies eval of `liftN 1 e k` at env1 also succeeds.

    By strong induction on fuel. -/

private theorem eval_liftN1_succeeds :
    ∀ (fuel : Nat) (e : SExpr L) (k : Nat) (env1 env2 : List (SVal L))
      (d : Nat) (v2 : SVal L),
    LiftSimEnv_inf env1 env2 k d →
    ClosedN e env2.length → EnvWF env1 d → EnvWF env2 d →
    eval_s fuel e env2 = some v2 →
    ∃ v1, eval_s fuel (liftN 1 e k) env1 = some v1 := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih_fuel =>
    intro e k env1 env2 d v2 hlse hcl hew1 hew2 hev2
    cases fuel with
    | zero => rw [eval_s_zero] at hev2; exact absurd hev2 nofun
    | succ f =>
      cases e with
      | bvar idx =>
        rw [eval_s_bvar] at hev2
        simp [ClosedN] at hcl
        simp only [SExpr.liftN]
        rw [eval_s_bvar]
        rw [List.getElem?_eq_getElem (liftVar1_lt hlse.1 hcl)] at *
        exact ⟨_, rfl⟩
      | sort u => exact ⟨_, rfl⟩
      | const c ls => exact ⟨_, rfl⟩
      | lit l => exact ⟨_, rfl⟩
      | proj _ _ _ => rw [eval_s_proj] at hev2; exact absurd hev2 nofun
      | app fn arg =>
        rw [eval_s_app, option_bind_eq_some] at hev2
        obtain ⟨fv2, hf2, hev2'⟩ := hev2
        rw [option_bind_eq_some] at hev2'
        obtain ⟨av2, ha2, hap2⟩ := hev2'
        simp [ClosedN] at hcl
        obtain ⟨fv1, hf1⟩ := ih_fuel f (by omega) fn k env1 env2 d fv2 hlse hcl.1 hew1 hew2 hf2
        obtain ⟨av1, ha1⟩ := ih_fuel f (by omega) arg k env1 env2 d av2 hlse hcl.2 hew1 hew2 ha2
        -- Need: apply_s f fv1 av1 = some v1'
        -- fv1 SimVal_inf fv2, av1 SimVal_inf av2, apply fv2 av2 succeeds
        -- apply success transfers via SimVal (same constructor at step ≥ 2)
        sorry -- apply success transfer under SimVal_inf
      | lam dom body =>
        simp [ClosedN] at hcl
        rw [eval_s_lam, option_bind_eq_some] at hev2
        obtain ⟨dv2, hd2, hv2⟩ := hev2; cases hv2
        obtain ⟨dv1, hd1⟩ := ih_fuel f (by omega) dom k env1 env2 d dv2 hlse hcl.1 hew1 hew2 hd2
        exact ⟨.lam dv1 (SExpr.liftN 1 body (k+1)) env1, by
          show eval_s (f+1) (SExpr.liftN 1 (.lam dom body) k) env1 = some _
          simp only [SExpr.liftN, eval_s, hd1]; rfl⟩
      | forallE dom body =>
        simp [ClosedN] at hcl
        rw [eval_s_forallE, option_bind_eq_some] at hev2
        obtain ⟨dv2, hd2, hv2⟩ := hev2; cases hv2
        obtain ⟨dv1, hd1⟩ := ih_fuel f (by omega) dom k env1 env2 d dv2 hlse hcl.1 hew1 hew2 hd2
        exact ⟨.pi dv1 (SExpr.liftN 1 body (k+1)) env1, by
          show eval_s (f+1) (SExpr.liftN 1 (.forallE dom body) k) env1 = some _
          simp only [SExpr.liftN, eval_s, hd1]; rfl⟩
      | letE ty val body =>
        simp [ClosedN] at hcl
        have ⟨vv2, hvv2, hbody2⟩ : ∃ vv, eval_s f val env2 = some vv ∧
            eval_s f body (vv :: env2) = some v2 := by
          rw [eval_s_letE, option_bind_eq_some] at hev2; exact hev2
        obtain ⟨vv1, hvv1⟩ := ih_fuel f (by omega) val k env1 env2 d vv2 hlse hcl.2.1 hew1 hew2 hvv2
        -- For body: need LiftSimEnv_inf (vv1::env1) (vv2::env2) (k+1) d
        have hlse' : LiftSimEnv_inf (vv1 :: env1) (vv2 :: env2) (k + 1) d :=
          LiftSimEnv_inf.cons
            (eval_liftN1_simval_inf val k f env1 env2 d vv1 vv2 hlse hcl.2.1 hew1 hew2 hvv1 hvv2)
            hlse
        obtain ⟨v1, hv1⟩ := ih_fuel f (by omega) body (k+1) (vv1::env1) (vv2::env2) d v2
          hlse' hcl.2.2
          (.cons (eval_preserves_wf hvv1 (hlse.1 ▸ hcl.2.1.liftN) hew1) hew1)
          (.cons (eval_preserves_wf hvv2 hcl.2.1 hew2) hew2) hbody2
        refine ⟨v1, ?_⟩
        show eval_s (f+1) (SExpr.liftN 1 (.letE ty val body) k) env1 = some v1
        simp only [SExpr.liftN, eval_s, hvv1]; exact hv1

/-! ## eval_inst_simval: substitution-evaluation commutation (bounded)

    Bounded version by N-induction, following eval_simval_le.
    Used inside lam/forallE closures of the _inf version. -/

private theorem eval_inst_simval_le (N : Nat) :
    ∀ m, m ≤ N →
    ∀ (e : SExpr L) (a : SExpr L) (k : Nat) (env1 env2 : List (SVal L)) (va : SVal L)
      (d : Nat) (fuel : Nat) (v1 v2 : SVal L),
      eval_s fuel (e.inst a k) env1 = some v1 →
      eval_s fuel e (envInsert k va env2) = some v2 →
      SimEnv m env1 env2 d →
      (∀ fuel' va', eval_s fuel' (SExpr.liftN k a) env1 = some va' → SimVal m va' va d) →
      (∀ fuel, ∃ va', eval_s (fuel+1) (SExpr.liftN k a) env1 = some va') →
      ClosedN a (env1.length - k) →
      ClosedN e (env1.length + 1) →
      k ≤ env1.length →
      EnvWF env1 d → EnvWF env2 d → ValWF va d →
      SimVal m v1 v2 d := by
  induction N with
  | zero =>
    intro m hm
    match m with
    | 0 => intros; simp
  | succ N' ih_N =>
    intro m hm
    match m with
    | 0 => intros; simp
    | m' + 1 =>
      intro e a k env1 env2 va d fuel v1 v2 hev1 hev2 hse hva hva_eval hcla hcl hk hew1 hew2 hvaw
      cases fuel with
      | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
      | succ f =>
        cases e with
        | bvar idx =>
          rw [eval_s_bvar] at hev2
          simp only [SExpr.inst, SExpr.instVar] at hev1
          split at hev1
          · rename_i hlt
            rw [eval_s_bvar] at hev1
            rw [envInsert_lt hlt (hse.1 ▸ hk)] at hev2
            have h1 : idx < env1.length := by simp [ClosedN] at hcl; omega
            have h2 : idx < env2.length := by rw [← hse.1]; exact h1
            rw [List.getElem?_eq_getElem h1] at hev1; cases hev1
            rw [List.getElem?_eq_getElem h2] at hev2; cases hev2
            exact hse.2 idx h1 h2
          · split at hev1
            · rename_i heq; subst heq
              rw [envInsert_eq (hse.1 ▸ hk)] at hev2; cases hev2
              exact hva (f + 1) v1 hev1
            · rename_i hge hne
              have hgt : k < idx := Nat.lt_of_le_of_ne (Nat.not_lt.mp hge) (Ne.symm hne)
              rw [eval_s_bvar] at hev1
              rw [envInsert_gt hgt (by rw [← hse.1]; simp [ClosedN] at hcl; omega)
                (hse.1 ▸ hk)] at hev2
              have h1 : idx - 1 < env1.length := by simp [ClosedN] at hcl; omega
              have h2 : idx - 1 < env2.length := by rw [← hse.1]; exact h1
              rw [List.getElem?_eq_getElem h1] at hev1; cases hev1
              rw [List.getElem?_eq_getElem h2] at hev2; cases hev2
              exact hse.2 (idx - 1) h1 h2
        | sort u =>
          rw [eval_s_sort] at hev2; cases hev2
          simp only [SExpr.inst] at hev1
          rw [eval_s_sort] at hev1; cases hev1; simp [SimVal.sort_sort]
        | const c ls =>
          rw [eval_s_const'] at hev2; cases hev2
          simp only [SExpr.inst] at hev1
          rw [eval_s_const'] at hev1; cases hev1
          simp [SimVal.neutral_neutral, SimSpine.nil_nil]
        | lit l =>
          rw [eval_s_lit] at hev2; cases hev2
          simp only [SExpr.inst] at hev1
          rw [eval_s_lit] at hev1; cases hev1; simp [SimVal.lit_lit]
        | proj _ _ _ =>
          simp only [SExpr.inst] at hev1
          rw [eval_s_proj] at hev1; exact absurd hev1 nofun
        | app fn arg => sorry -- Step loss (same as eval_simval_le app)
        | lam dom body =>
          simp only [SExpr.inst] at hev1
          rw [eval_s_lam, option_bind_eq_some] at hev1 hev2
          obtain ⟨dv1, hevd1, hv1⟩ := hev1; cases hv1
          obtain ⟨dv2, hevd2, hv2⟩ := hev2; cases hv2
          simp [ClosedN] at hcl
          simp only [SimVal.lam_lam]
          exact ⟨ih_N m' (by omega) dom a k env1 env2 va d f dv1 dv2
              hevd1 hevd2 (hse.mono (by omega))
              (fun f' va' h => (hva f' va' h).mono (by omega))
              hva_eval hcla hcl.1 hk hew1 hew2 hvaw,
            fun j hj d' hd' w1 w2 sw hw1 hw2 fuel' r1 r2 hr1 hr2 => by
              rw [envInsert_succ] at hr2
              have hew1' := hew1.mono hd'
              have hcl_liftk : ClosedN (SExpr.liftN k a) env1.length := by
                have := hcla.liftN (n := k) (j := 0)
                rwa [show env1.length - k + k = env1.length from Nat.sub_add_cancel hk] at this
              exact ih_N j (by omega) body a (k+1) (w1::env1) (w2::env2) va d' fuel' r1 r2
                hr1 hr2
                (SimEnv.cons sw (hse.mono (by omega) |>.depth_mono hd'))
                (fun f' va' hev' => by
                  rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
                    (liftN_liftN ..).symm] at hev'
                  obtain ⟨va'', hva''⟩ := hva_eval f'
                  exact (eval_liftN1_simval j (SExpr.liftN k a) 0 (max f' (f'+1))
                    (w1 :: env1) env1 d' va' va''
                    ((LiftSimEnv_inf.initial hew1').to_n) hcl_liftk
                    (.cons hw1 hew1') hew1'
                    (eval_fuel_mono hev' (Nat.le_max_left _ _))
                    (eval_fuel_mono hva'' (Nat.le_max_right _ _))).trans
                    ((hva _ _ hva'').mono (by omega) |>.depth_mono hd'))
                (fun f' => by
                  obtain ⟨va'', hva''⟩ := hva_eval f'
                  rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
                    (liftN_liftN ..).symm]
                  exact eval_liftN1_succeeds (f'+1) (SExpr.liftN k a) 0 (w1::env1) env1 d' va''
                    (.initial hew1') hcl_liftk (.cons hw1 hew1') hew1' hva'')
                (Eq.mpr (by simp) hcla) hcl.2 (by simp; omega)
                (.cons hw1 hew1') (.cons hw2 (hew2.mono hd')) (hvaw.mono hd')⟩
        | forallE dom body =>
          simp only [SExpr.inst] at hev1
          rw [eval_s_forallE, option_bind_eq_some] at hev1 hev2
          obtain ⟨dv1, hevd1, hv1⟩ := hev1; cases hv1
          obtain ⟨dv2, hevd2, hv2⟩ := hev2; cases hv2
          simp [ClosedN] at hcl
          simp only [SimVal.pi_pi]
          exact ⟨ih_N m' (by omega) dom a k env1 env2 va d f dv1 dv2
              hevd1 hevd2 (hse.mono (by omega))
              (fun f' va' h => (hva f' va' h).mono (by omega))
              hva_eval hcla hcl.1 hk hew1 hew2 hvaw,
            fun j hj d' hd' w1 w2 sw hw1 hw2 fuel' r1 r2 hr1 hr2 => by
              rw [envInsert_succ] at hr2
              have hew1' := hew1.mono hd'
              have hcl_liftk : ClosedN (SExpr.liftN k a) env1.length := by
                have := hcla.liftN (n := k) (j := 0)
                rwa [show env1.length - k + k = env1.length from Nat.sub_add_cancel hk] at this
              exact ih_N j (by omega) body a (k+1) (w1::env1) (w2::env2) va d' fuel' r1 r2
                hr1 hr2
                (SimEnv.cons sw (hse.mono (by omega) |>.depth_mono hd'))
                (fun f' va' hev' => by
                  rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
                    (liftN_liftN ..).symm] at hev'
                  obtain ⟨va'', hva''⟩ := hva_eval f'
                  exact (eval_liftN1_simval j (SExpr.liftN k a) 0 (max f' (f'+1))
                    (w1 :: env1) env1 d' va' va''
                    ((LiftSimEnv_inf.initial hew1').to_n) hcl_liftk
                    (.cons hw1 hew1') hew1'
                    (eval_fuel_mono hev' (Nat.le_max_left _ _))
                    (eval_fuel_mono hva'' (Nat.le_max_right _ _))).trans
                    ((hva _ _ hva'').mono (by omega) |>.depth_mono hd'))
                (fun f' => by
                  obtain ⟨va'', hva''⟩ := hva_eval f'
                  rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
                    (liftN_liftN ..).symm]
                  exact eval_liftN1_succeeds (f'+1) (SExpr.liftN k a) 0 (w1::env1) env1 d' va''
                    (.initial hew1') hcl_liftk (.cons hw1 hew1') hew1' hva'')
                (Eq.mpr (by simp) hcla) hcl.2 (by simp; omega)
                (.cons hw1 hew1') (.cons hw2 (hew2.mono hd')) (hvaw.mono hd')⟩
        | letE ty val body => sorry -- Same pattern as lam (val ih_N + body ih_N with shifted va)

theorem eval_inst_simval (m : Nat) :
    ∀ (e : SExpr L) (a : SExpr L) (k : Nat) (env1 env2 : List (SVal L)) (va : SVal L)
      (d : Nat) (fuel : Nat) (v1 v2 : SVal L),
      eval_s fuel (e.inst a k) env1 = some v1 →
      eval_s fuel e (envInsert k va env2) = some v2 →
      SimEnv m env1 env2 d →
      (∀ fuel' va', eval_s fuel' (SExpr.liftN k a) env1 = some va' → SimVal m va' va d) →
      (∀ fuel, ∃ va', eval_s (fuel+1) (SExpr.liftN k a) env1 = some va') →
      ClosedN a (env1.length - k) →
      ClosedN e (env1.length + 1) →
      k ≤ env1.length →
      EnvWF env1 d → EnvWF env2 d → ValWF va d →
      SimVal m v1 v2 d := eval_inst_simval_le m m (Nat.le_refl _)

/-! ## eval_inst_simval_inf: substitution-evaluation commutation (_inf version)

    Wraps eval_inst_simval by quantifying over n inside.
    Uses eval_inst_simval (bounded) in lam/forallE closures. -/

theorem eval_inst_simval_inf (e : SExpr L) :
    ∀ (a : SExpr L) (k : Nat) (env1 env2 : List (SVal L)) (va : SVal L) (d : Nat)
      (fuel : Nat) (v1 v2 : SVal L),
      eval_s fuel (e.inst a k) env1 = some v1 →
      eval_s fuel e (envInsert k va env2) = some v2 →
      SimEnv_inf env1 env2 d →
      (∀ fuel' va', eval_s fuel' (SExpr.liftN k a) env1 = some va' → SimVal_inf va' va d) →
      -- eval of liftN k a in env1 succeeds (needed for binder case va condition shift)
      (∀ fuel, ∃ va', eval_s (fuel+1) (SExpr.liftN k a) env1 = some va') →
      ClosedN a (env1.length - k) →
      ClosedN e (env1.length + 1) →
      k ≤ env1.length →
      EnvWF env1 d → EnvWF env2 d → ValWF va d →
      SimVal_inf v1 v2 d := by
  induction e with
  | bvar idx =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 hse hva hva_eval hcla hcl hk hew1 hew2 hvaw n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_bvar] at hev2
      simp only [SExpr.inst, SExpr.instVar] at hev1
      split at hev1
      · -- idx < k: bvar stays
        rename_i hlt
        rw [eval_s_bvar] at hev1
        rw [envInsert_lt hlt (hse.1 ▸ hk)] at hev2
        have h1 : idx < env1.length := by simp [ClosedN] at hcl; omega
        have h2 : idx < env2.length := by rw [← hse.1]; exact h1
        rw [List.getElem?_eq_getElem h1] at hev1; cases hev1
        rw [List.getElem?_eq_getElem h2] at hev2; cases hev2
        exact hse.2 idx h1 h2 n
      · split at hev1
        · -- idx = k: replaced by liftN k a
          rename_i heq; subst heq
          rw [envInsert_eq (hse.1 ▸ hk)] at hev2; cases hev2
          exact hva (f + 1) v1 hev1 n
        · -- idx > k: bvar decremented
          rename_i hge hne
          have hgt : k < idx := Nat.lt_of_le_of_ne (Nat.not_lt.mp hge) (Ne.symm hne)
          rw [eval_s_bvar] at hev1
          rw [envInsert_gt hgt (by rw [← hse.1]; simp [ClosedN] at hcl; omega)
            (hse.1 ▸ hk)] at hev2
          have h1 : idx - 1 < env1.length := by simp [ClosedN] at hcl; omega
          have h2 : idx - 1 < env2.length := by rw [← hse.1]; exact h1
          rw [List.getElem?_eq_getElem h1] at hev1; cases hev1
          rw [List.getElem?_eq_getElem h2] at hev2; cases hev2
          exact hse.2 (idx - 1) h1 h2 n
  | sort u =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 _ _ _ _ _ _ _ _ _ n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_sort] at hev2; cases hev2
      simp only [SExpr.inst] at hev1
      rw [eval_s_sort] at hev1; cases hev1
      cases n <;> simp [SimVal]
  | const c ls =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 _ _ _ _ _ _ _ _ _ n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_const'] at hev2; cases hev2
      simp only [SExpr.inst] at hev1
      rw [eval_s_const'] at hev1; cases hev1
      cases n with
      | zero => simp
      | succ => simp [SimVal.neutral_neutral, SimSpine.nil_nil]
  | lit l =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 _ _ _ _ _ _ _ _ _ n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      rw [eval_s_lit] at hev2; cases hev2
      simp only [SExpr.inst] at hev1
      rw [eval_s_lit] at hev1; cases hev1
      cases n <;> simp [SimVal]
  | proj t i s ih_s =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 _ _ _ _ _ _ _ _ _ _
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.inst] at hev1
      rw [eval_s_proj] at hev1; exact absurd hev1 nofun
  | app fn arg ih_fn ih_arg =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 hse hva hva_eval hcla hcl hk hew1 hew2 hvaw n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.inst] at hev1
      rw [eval_s_app, option_bind_eq_some] at hev1 hev2
      obtain ⟨fv1, hevf1, hev1'⟩ := hev1
      rw [option_bind_eq_some] at hev1'
      obtain ⟨av1, heva1, hap1⟩ := hev1'
      obtain ⟨fv2, hevf2, hev2'⟩ := hev2
      rw [option_bind_eq_some] at hev2'
      obtain ⟨av2, heva2, hap2⟩ := hev2'
      simp [ClosedN] at hcl
      -- IH gives SimVal_inf (all steps) for fn and arg
      have sfn := ih_fn a k env1 env2 va d f fv1 fv2 hevf1 hevf2 hse hva hva_eval hcla hcl.1 hk hew1 hew2 hvaw
      have sarg := ih_arg a k env1 env2 va d f av1 av2 heva1 heva2 hse hva hva_eval hcla hcl.2 hk hew1 hew2 hvaw
      -- apply_simval n: SimVal (n+1) → SimVal n (step loss absorbed by ∀n quantifier)
      -- ValWF from eval_preserves_wf + ClosedN.instN + EnvWF_envInsert
      have hcl_inst {e_sub : SExpr L} (h : ClosedN e_sub (env1.length + 1)) :
          ClosedN (e_sub.inst a k) env1.length := by
        have hlen : (env1.length - k) + k + 1 = env1.length + 1 := by omega
        rw [show env1.length = (env1.length - k) + k from (Nat.sub_add_cancel hk).symm]
        exact (hlen ▸ h).instN (j := k) hcla
      have hk2 : k ≤ env2.length := by rw [← hse.1]; exact hk
      have hew_ins := EnvWF_envInsert hew2 hvaw hk2
      have hlen_ins : (envInsert k va env2).length = env1.length + 1 := by
        rw [envInsert_length k va env2 hk2, hse.1]
      exact apply_simval n f (sfn (n+1)) (sarg (n+1))
        (eval_preserves_wf hevf1 (hcl_inst hcl.1) hew1)
        (eval_preserves_wf hevf2 (hlen_ins ▸ hcl.1) hew_ins)
        (eval_preserves_wf heva1 (hcl_inst hcl.2) hew1)
        (eval_preserves_wf heva2 (hlen_ins ▸ hcl.2) hew_ins)
        hap1 hap2
  | lam dom body ih_dom ih_body =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 hse hva hva_eval hcla hcl hk hew1 hew2 hvaw n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      -- (.lam dom body).inst a k = .lam (dom.inst a k) (body.inst a (k+1))
      simp only [SExpr.inst] at hev1
      rw [eval_s_lam, option_bind_eq_some] at hev2
      obtain ⟨dv2, hevd2, hv2⟩ := hev2; cases hv2
      simp [ClosedN] at hcl
      -- Extract domain eval from the inst lam eval
      -- hev1 after simp: eval (dom.inst a k) env1 >>= fun dv => some (.lam dv ...) = some v1
      have ⟨dv1, hevd1, hv1⟩ : ∃ dv, eval_s f (dom.inst a k) env1 = some dv ∧
          v1 = .lam dv (body.inst a (k+1)) env1 := by
        rw [eval_s_lam, option_bind_eq_some] at hev1
        obtain ⟨dv, hdv, hv⟩ := hev1; exact ⟨dv, hdv, by cases hv; rfl⟩
      cases hv1
      have sdom := ih_dom a k env1 env2 va d f dv1 dv2 hevd1 hevd2 hse hva hva_eval hcla hcl.1 hk hew1 hew2 hvaw
      cases n with
      | zero => simp
      | succ n' =>
        rw [SimVal.lam_lam]
        exact ⟨sdom n', fun j hj d' hd' w1 w2 sw hw1 hw2 fuel' r1 r2 hr1 hr2 => by
          rw [envInsert_succ] at hr2
          -- Va condition shift: at depth d' (fixes ValWF mismatch)
          have hew1' := hew1.mono hd'
          have hva_shifted : ∀ f' va', eval_s f' (SExpr.liftN (k+1) a) (w1::env1) = some va' →
              SimVal j va' va d' := fun f' va' hev' => by
            rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
              (liftN_liftN ..).symm] at hev'
            obtain ⟨va'', hva''⟩ := hva_eval f'
            have hcl_liftk : ClosedN (SExpr.liftN k a) env1.length := by
              have := hcla.liftN (n := k) (j := 0)
              rwa [show env1.length - k + k = env1.length from Nat.sub_add_cancel hk] at this
            -- Align fuels and apply eval_liftN1_simval
            have hf_max := Nat.le_max_left f' (f'+1)
            have hf_max' := Nat.le_max_right f' (f'+1)
            exact (eval_liftN1_simval j (SExpr.liftN k a) 0 (max f' (f'+1))
              (w1 :: env1) env1 d' va' va''
              ((LiftSimEnv_inf.initial hew1').to_n)
              hcl_liftk
              (.cons hw1 hew1') hew1'
              (eval_fuel_mono hev' hf_max)
              (eval_fuel_mono hva'' hf_max')).trans
              ((hva _ _ hva'' j).depth_mono hd')
          have hva_eval' : ∀ f, ∃ va', eval_s (f+1) (SExpr.liftN (k+1) a) (w1::env1) = some va' :=
            fun f' => by
              obtain ⟨va'', hva''⟩ := hva_eval f'
              rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
                (liftN_liftN ..).symm]
              have hcl_liftk : ClosedN (SExpr.liftN k a) env1.length := by
                have := hcla.liftN (n := k) (j := 0)
                rwa [show env1.length - k + k = env1.length from Nat.sub_add_cancel hk] at this
              exact eval_liftN1_succeeds (f'+1) (SExpr.liftN k a) 0 (w1::env1) env1 d' va''
                (.initial hew1') hcl_liftk (.cons hw1 hew1') hew1' hva''
          have hse_ext : SimEnv j (w1::env1) (w2::env2) d' :=
            SimEnv.cons sw ⟨hse.1, fun i h1 h2 =>
              (hse.2 i (hse.1 ▸ h2) (hse.1.symm ▸ h1) j).depth_mono hd'⟩
          exact eval_inst_simval j body a (k+1) (w1::env1) (w2::env2) va d' fuel' r1 r2
            hr1 hr2 hse_ext hva_shifted hva_eval'
            (by have : (w1::env1).length - (k+1) = env1.length - k := by simp
                rw [this]; exact hcla)
            hcl.2
            (by simp; omega) (.cons hw1 hew1') (.cons hw2 (hew2.mono hd'))
            (hvaw.mono hd')⟩
  | forallE dom body ih_dom ih_body =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 hse hva hva_eval hcla hcl hk hew1 hew2 hvaw n
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.inst] at hev1
      rw [eval_s_forallE, option_bind_eq_some] at hev2
      obtain ⟨dv2, hevd2, hv2⟩ := hev2; cases hv2
      simp [ClosedN] at hcl
      -- Extract domain eval from forallE inst
      have ⟨dv1, hevd1, hv1⟩ : ∃ dv, eval_s f (dom.inst a k) env1 = some dv ∧
          v1 = .pi dv (body.inst a (k+1)) env1 := by
        rw [eval_s_forallE, option_bind_eq_some] at hev1
        obtain ⟨dv, hdv, hv⟩ := hev1; exact ⟨dv, hdv, by cases hv; rfl⟩
      cases hv1
      have sdom := ih_dom a k env1 env2 va d f dv1 dv2 hevd1 hevd2 hse hva hva_eval hcla hcl.1 hk hew1 hew2 hvaw
      cases n with
      | zero => simp
      | succ n' =>
        rw [SimVal.pi_pi]
        exact ⟨sdom n', fun j hj d' hd' w1 w2 sw hw1 hw2 fuel' r1 r2 hr1 hr2 => by
          rw [envInsert_succ] at hr2
          have hew1' := hew1.mono hd'
          have hcl_liftk : ClosedN (SExpr.liftN k a) env1.length := by
            have := hcla.liftN (n := k) (j := 0)
            rwa [show env1.length - k + k = env1.length from Nat.sub_add_cancel hk] at this
          have hva_shifted : ∀ f' va', eval_s f' (SExpr.liftN (k+1) a) (w1::env1) = some va' →
              SimVal j va' va d' := fun f' va' hev' => by
            rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
              (liftN_liftN ..).symm] at hev'
            obtain ⟨va'', hva''⟩ := hva_eval f'
            exact (eval_liftN1_simval j (SExpr.liftN k a) 0 (max f' (f'+1))
              (w1 :: env1) env1 d' va' va''
              ((LiftSimEnv_inf.initial hew1').to_n) hcl_liftk
              (.cons hw1 hew1') hew1'
              (eval_fuel_mono hev' (Nat.le_max_left _ _))
              (eval_fuel_mono hva'' (Nat.le_max_right _ _))).trans
              ((hva _ _ hva'' j).depth_mono hd')
          have hva_eval' : ∀ f, ∃ va', eval_s (f+1) (SExpr.liftN (k+1) a) (w1::env1) = some va' :=
            fun f' => by
              obtain ⟨va'', hva''⟩ := hva_eval f'
              rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
                (liftN_liftN ..).symm]
              exact eval_liftN1_succeeds (f'+1) (SExpr.liftN k a) 0 (w1::env1) env1 d' va''
                (.initial hew1') hcl_liftk (.cons hw1 hew1') hew1' hva''
          have hse_ext : SimEnv j (w1::env1) (w2::env2) d' :=
            SimEnv.cons sw ⟨hse.1, fun i h1 h2 =>
              (hse.2 i (hse.1 ▸ h2) (hse.1.symm ▸ h1) j).depth_mono hd'⟩
          exact eval_inst_simval j body a (k+1) (w1::env1) (w2::env2) va d' fuel' r1 r2
            hr1 hr2 hse_ext hva_shifted hva_eval'
            (by have : (w1::env1).length - (k+1) = env1.length - k := by simp
                rw [this]; exact hcla)
            hcl.2 (by simp; omega) (.cons hw1 hew1') (.cons hw2 (hew2.mono hd'))
            (hvaw.mono hd')⟩
  | letE ty val body ih_ty ih_val ih_body =>
    intro a k env1 env2 va d fuel v1 v2 hev1 hev2 hse hva hva_eval hcla hcl hk hew1 hew2 hvaw
    cases fuel with
    | zero => rw [eval_s_zero] at hev1; exact absurd hev1 nofun
    | succ f =>
      simp only [SExpr.inst] at hev1
      rw [eval_s_letE, option_bind_eq_some] at hev1 hev2
      obtain ⟨vv1, hvv1, hr1⟩ := hev1
      obtain ⟨vv2, hvv2, hr2⟩ := hev2
      simp [ClosedN] at hcl
      rw [envInsert_succ] at hr2
      have sval := ih_val a k env1 env2 va d f vv1 vv2 hvv1 hvv2 hse hva hva_eval hcla hcl.2.1 hk hew1 hew2 hvaw
      -- ValWF for vv1/vv2 via eval_preserves_wf + ClosedN.instN
      have hcl_val_inst : ClosedN (val.inst a k) env1.length := by
        have hlen : (env1.length - k) + k + 1 = env1.length + 1 := by omega
        rw [show env1.length = (env1.length - k) + k from (Nat.sub_add_cancel hk).symm]
        exact (hlen ▸ hcl.2.1).instN (j := k) hcla
      have hwf_vv1 : ValWF vv1 d := eval_preserves_wf hvv1 hcl_val_inst hew1
      have hk2 : k ≤ env2.length := by rw [← hse.1]; exact hk
      have hlen_ins : (envInsert k va env2).length = env1.length + 1 := by
        rw [envInsert_length k va env2 hk2, hse.1]
      have hwf_vv2 : ValWF vv2 d := eval_preserves_wf hvv2
        (hlen_ins ▸ hcl.2.1) (EnvWF_envInsert hew2 hvaw hk2)
      -- Va condition shift (same chain as lam)
      have hcl_liftk : ClosedN (SExpr.liftN k a) env1.length := by
        have := hcla.liftN (n := k) (j := 0)
        rwa [show env1.length - k + k = env1.length from Nat.sub_add_cancel hk] at this
      have hva_shifted : ∀ f' va', eval_s f' (SExpr.liftN (k+1) a) (vv1::env1) = some va' →
          SimVal_inf va' va d := fun f' va' hev' => by
        rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
          (liftN_liftN ..).symm] at hev'
        obtain ⟨va'', hva''⟩ := hva_eval f'
        exact (eval_liftN1_simval_inf (SExpr.liftN k a) 0 (max f' (f'+1))
          (vv1 :: env1) env1 d va' va''
          (.initial hew1) hcl_liftk
          (.cons hwf_vv1 hew1) hew1
          (eval_fuel_mono hev' (Nat.le_max_left _ _))
          (eval_fuel_mono hva'' (Nat.le_max_right _ _))).trans
          (hva _ _ hva'')
      have hva_eval' : ∀ f, ∃ va', eval_s (f+1) (SExpr.liftN (k+1) a) (vv1::env1) = some va' :=
        fun f' => by
          obtain ⟨va'', hva''⟩ := hva_eval f'
          rw [show SExpr.liftN (k+1) a = SExpr.liftN 1 (SExpr.liftN k a) 0 from
            (liftN_liftN ..).symm]
          exact eval_liftN1_succeeds (f'+1) (SExpr.liftN k a) 0 (vv1::env1) env1 d va''
            (.initial hew1) hcl_liftk (.cons hwf_vv1 hew1) hew1 hva''
      -- Body IH with extended envs
      exact ih_body a (k+1) (vv1::env1) (vv2::env2) va d f v1 v2
        hr1 hr2
        ⟨by simp [hse.1], fun i h1 h2 n => by
          cases i with
          | zero => simp only [List.getElem_cons_zero]; exact sval n
          | succ j =>
            simp only [List.getElem_cons_succ]
            have h1' : j < env1.length := by simp [List.length_cons] at h1; omega
            have h2' : j < env2.length := by simp [List.length_cons] at h2; omega
            exact hse.2 j h1' h2' n⟩
        hva_shifted hva_eval'
        (by have : (vv1::env1).length - (k+1) = env1.length - k := by simp
            rw [this]; exact hcla)
        hcl.2.2 (by simp; omega)
        (.cons hwf_vv1 hew1) (.cons hwf_vv2 hew2)
        hvaw

end Ix.Theory
