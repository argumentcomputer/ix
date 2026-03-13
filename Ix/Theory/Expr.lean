/-
  Ix.Theory.Expr: Specification-level expressions with de Bruijn substitution algebra.

  Ported from lean4lean's Lean4Lean.Theory.VExpr, extended with `letE`, `lit`, and `proj`.
  Parameterized over a level type `L` for universe polymorphism.
  This is the syntactic ground truth against which NbE eval-quote is verified.
-/
import Ix.Theory.Level

namespace Ix.Theory

inductive SExpr (L : Type) where
  | bvar (idx : Nat)
  | sort (u : L)
  | const (id : Nat) (levels : List L)
  | app (fn arg : SExpr L)
  | lam (dom body : SExpr L)
  | forallE (dom body : SExpr L)
  | letE (ty val body : SExpr L)
  | lit (n : Nat)
  | proj (typeName : Nat) (idx : Nat) (struct : SExpr L)
  deriving Inhabited

instance [BEq L] : BEq (SExpr L) where
  beq := go where
    go : SExpr L → SExpr L → Bool
    | .bvar i, .bvar j => i == j
    | .sort u, .sort v => u == v
    | .const c ls, .const c' ls' => c == c' && ls == ls'
    | .app f a, .app f' a' => go f f' && go a a'
    | .lam d b, .lam d' b' => go d d' && go b b'
    | .forallE d b, .forallE d' b' => go d d' && go b b'
    | .letE t v b, .letE t' v' b' => go t t' && go v v' && go b b'
    | .lit n, .lit m => n == m
    | .proj t i s, .proj t' i' s' => t == t' && i == i' && go s s'
    | _, _ => false

abbrev SExpr₀ := SExpr Nat
abbrev TExpr := SExpr SLevel

-- Variable lifting: shift free variable `i` by `n` above cutoff `k`
def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

theorem liftVar_lt (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le (h : k ≤ i) : liftVar n i k = n + i := if_neg (Nat.not_lt.2 h)

theorem liftVar_base : liftVar n i = n + i := liftVar_le (Nat.zero_le _)
@[simp] theorem liftVar_base' : liftVar n i = i + n :=
  Nat.add_comm .. ▸ liftVar_le (Nat.zero_le _)

@[simp] theorem liftVar_zero : liftVar n 0 (k+1) = 0 := by simp [liftVar]
@[simp] theorem liftVar_succ : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
  simp [liftVar, Nat.succ_lt_succ_iff]; split <;> simp [Nat.add_assoc]

theorem liftVar_lt_add (self : i < k) : liftVar n i j < k + n := by
  simp [liftVar]
  split <;> rename_i h
  · exact Nat.lt_of_lt_of_le self (Nat.le_add_right ..)
  · rw [Nat.add_comm]; exact Nat.add_lt_add_right self _

namespace SExpr

variable {L : Type}

-- Lift (shift) free de Bruijn indices by `n` above cutoff `k`
variable (n : Nat) in
def liftN : SExpr L → (k :_:= 0) → SExpr L
  | .bvar i, k => .bvar (liftVar n i k)
  | .sort u, _ => .sort u
  | .const c ls, _ => .const c ls
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  | .forallE ty body, k => .forallE (ty.liftN k) (body.liftN (k+1))
  | .letE ty val body, k => .letE (ty.liftN k) (val.liftN k) (body.liftN (k+1))
  | .lit l, _ => .lit l
  | .proj t i s, k => .proj t i (s.liftN k)

abbrev lift (e : SExpr L) := liftN 1 e

@[simp] theorem liftN_zero (e : SExpr L) (k : Nat) : liftN 0 e k = e := by
  induction e generalizing k <;> simp [liftN, liftVar, *]

theorem liftN'_liftN' {e : SExpr L} {n1 n2 k1 k2 : Nat} (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN (n1+n2) e k1 := by
  induction e generalizing k1 k2 with simp [liftN, liftVar, Nat.add_assoc, *]
  | bvar i =>
    split <;> rename_i h
    · rw [if_pos (Nat.lt_of_lt_of_le h h1)]
    · rw [if_neg (mt (fun h => ?_) h), Nat.add_left_comm]
      exact (Nat.add_lt_add_iff_left ..).1 (Nat.lt_of_lt_of_le h h2)
  | lam _ _ _ ih2 | forallE _ _ _ ih2 =>
    exact ih2 (Nat.succ_le_succ h1) (Nat.succ_le_succ h2)
  | letE _ _ _ _ _ ih3 =>
    exact ih3 (Nat.succ_le_succ h1) (Nat.succ_le_succ h2)

theorem liftN'_liftN_lo (e : SExpr L) (n k : Nat) : liftN n (liftN k e) k = liftN (n+k) e := by
  simpa [Nat.add_comm] using liftN'_liftN' (n1 := k) (n2 := n) (Nat.zero_le _) (Nat.le_refl _)

theorem liftN'_liftN_hi (e : SExpr L) (n1 n2 k : Nat) :
    liftN n2 (liftN n1 e k) k = liftN (n1+n2) e k :=
  liftN'_liftN' (Nat.le_refl _) (Nat.le_add_left ..)

theorem liftN_liftN (e : SExpr L) (n1 n2 : Nat) : liftN n2 (liftN n1 e) = liftN (n1+n2) e := by
  simpa using liftN'_liftN' (Nat.zero_le _) (Nat.zero_le _)

theorem liftN_succ (e : SExpr L) (n : Nat) : liftN (n+1) e = lift (liftN n e) :=
  (liftN_liftN ..).symm

theorem liftN'_comm (e : SExpr L) (n1 n2 k1 k2 : Nat) (h : k2 ≤ k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN n1 (liftN n2 e k2) (n2+k1) := by
  induction e generalizing k1 k2 with
    simp [liftN, liftVar, Nat.add_assoc, Nat.succ_le_succ, *]
  | bvar i =>
    split <;> rename_i h'
    · rw [if_pos (c := _ < n2 + k1)]; split
      · exact Nat.lt_add_left _ h'
      · exact Nat.add_lt_add_left h' _
    · have := mt (Nat.lt_of_lt_of_le · h) h'
      rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_add_left _ n1)) this),
        if_neg this, if_neg (mt (Nat.add_lt_add_iff_left ..).1 h'), Nat.add_left_comm]

theorem lift_liftN' (e : SExpr L) (k : Nat) : lift (liftN n e k) = liftN n (lift e) (k+1) :=
  Nat.add_comm .. ▸ liftN'_comm (h := Nat.zero_le _) ..

-- ClosedN: all bvars in `e` are below `k`
def ClosedN : SExpr L → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ | .lit .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .letE ty val body, k => ty.ClosedN k ∧ val.ClosedN k ∧ body.ClosedN (k+1)
  | .proj _ _ s, k => s.ClosedN k

abbrev Closed (e : SExpr L) := ClosedN e

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN (L := L) e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    exact ⟨ih1 h self.1, ih2 h self.2.1, ih3 (Nat.succ_le_succ h) self.2.2⟩
  | proj _ _ _ ih => exact ih h self

theorem ClosedN.liftN_eq (self : ClosedN (L := L) e k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [liftN, *])
  | bvar i => exact liftVar_lt (Nat.lt_of_lt_of_le self h)
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 self.1 h, ih2 self.2 (Nat.succ_le_succ h)⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    exact ⟨ih1 self.1 h, ih2 self.2.1 h, ih3 self.2.2 (Nat.succ_le_succ h)⟩
  | proj _ _ _ ih => exact ih self h

theorem ClosedN.lift_eq (self : ClosedN (L := L) e) : lift e = e :=
  self.liftN_eq (Nat.zero_le _)

protected theorem ClosedN.liftN (self : ClosedN (L := L) e k) :
    ClosedN (e.liftN n j) (k+n) := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [SExpr.liftN, ClosedN, *])
  | bvar i => exact liftVar_lt_add self
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => exact Nat.add_right_comm .. ▸ ih2 self.2
  | letE _ _ _ _ _ ih3 => exact Nat.add_right_comm .. ▸ ih3 self.2.2

-- instVar: substitute a single variable
def instVar (i : Nat) (e : SExpr L) (k := 0) : SExpr L :=
  if i < k then .bvar i else if i = k then liftN k e else .bvar (i - 1)

@[simp] theorem instVar_zero : instVar (L := L) 0 e = e := liftN_zero ..
@[simp] theorem instVar_upper : instVar (L := L) (i+1) e = .bvar i := rfl
@[simp] theorem instVar_lower : instVar (L := L) 0 e (k+1) = .bvar 0 := by simp [instVar]
theorem instVar_succ : instVar (L := L) (i+1) e (k+1) = (instVar i e k).lift := by
  simp only [instVar]
  split <;> rename_i h
  · -- i+1 < k+1, i.e., i < k
    have hik : i < k := by omega
    rw [if_pos hik]
    simp [lift, liftN, liftVar]; omega
  · split <;> rename_i h'
    · -- ¬(i+1 < k+1) and i+1 = k+1, so i = k
      have hik : i = k := by omega
      rw [if_neg (by omega), if_pos hik]
      subst hik
      simp [lift, liftN_liftN]
    · -- ¬(i+1 < k+1) and ¬(i+1 = k+1), so k < i
      have hne : i ≠ k := by omega
      have hlt : k < i := by omega
      rw [if_neg (by omega), if_neg hne]
      let i+1 := i
      simp [lift, liftN, liftVar]; omega

-- inst: substitute bvar `k` with `val` in expression `e`
def inst : SExpr L → SExpr L → (k :_:= 0) → SExpr L
  | .bvar i, e, k => instVar i e k
  | .sort u, _, _ => .sort u
  | .const c ls, _, _ => .const c ls
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k+1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst e (k+1))
  | .letE ty val body, e, k => .letE (ty.inst e k) (val.inst e k) (body.inst e (k+1))
  | .lit l, _, _ => .lit l
  | .proj t i s, e, k => .proj t i (s.inst e k)

-- Key lemma: lifting then instantiating at the lift point cancels out
theorem inst_liftN (e1 e2 : SExpr L) : (liftN 1 e1 k).inst e2 k = e1 := by
  induction e1 generalizing k with simp [liftN, inst, *]
  | bvar i =>
    simp only [liftVar, instVar, Nat.add_comm 1]
    split
    · rfl
    · rename_i h
      rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_succ _)) h),
        if_neg (mt (by rintro rfl; apply Nat.lt_succ_self) h)]; rfl

theorem inst_lift (e1 e2 : SExpr L) : (lift e1).inst e2 = e1 := inst_liftN ..

theorem inst_liftN' (e1 e2 : SExpr L) : (liftN (n+1) e1 k).inst e2 k = liftN n e1 k := by
  rw [← liftN'_liftN_hi, inst_liftN]

-- Lifting commutes with inst (low)
theorem liftN_instN_lo (n : Nat) (e1 e2 : SExpr L) (j k : Nat) (hj : k ≤ j) :
    liftN n (e1.inst e2 j) k = (liftN n e1 k).inst e2 (n+j) := by
  induction e1 generalizing k j with
    simp [liftN, inst, instVar, Nat.add_le_add_iff_right, *]
  | bvar i => apply liftN_instVar_lo (hj := hj)
  | _ => rfl
where
  liftN_instVar_lo {i : Nat} (n : Nat) (e : SExpr L) (j k : Nat) (hj : k ≤ j) :
      liftN n (instVar i e j) k = instVar (liftVar n i k) e (n+j) := by
    simp [instVar]; split <;> rename_i h
    · rw [if_pos]; · rfl
      simp only [liftVar]; split <;> rename_i hk
      · exact Nat.lt_add_left _ h
      · exact Nat.add_lt_add_left h _
    split <;> rename_i h'
    · subst i
      rw [liftN'_liftN' (h1 := Nat.zero_le _) (h2 := hj), liftVar_le hj,
        if_neg (by simp), if_pos rfl, Nat.add_comm]
    · rw [Nat.not_lt] at h; rw [liftVar_le (Nat.le_trans hj h)]
      have hk := Nat.lt_of_le_of_ne h (Ne.symm h')
      let i+1 := i
      have := Nat.add_lt_add_left hk n
      rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
      simp only [liftN]
      rw [liftVar_le (Nat.le_trans hj <| by exact Nat.le_of_lt_succ hk)]; rfl

-- Lifting commutes with inst (high)
theorem liftN_instN_hi (e1 e2 : SExpr L) (n k j : Nat) :
    liftN n (e1.inst e2 j) (k+j) = (liftN n e1 (k+j+1)).inst (liftN n e2 k) j := by
  induction e1 generalizing j with simp [liftN, inst, instVar, *]
  | bvar i => apply liftN_instVar_hi
  | _ => rename_i IH; apply IH
where
  liftN_instVar_hi (i : Nat) (e2 : SExpr L) (n k j : Nat) :
      liftN n (instVar i e2 j) (k+j) = instVar (liftVar n i (k+j+1)) (liftN n e2 k) j := by
    simp [instVar]; split <;> rename_i h
    · have := Nat.lt_add_left k h
      rw [liftVar_lt (by exact Nat.lt_succ_of_lt this), if_pos h]
      simp [liftN, liftVar_lt this]
    split <;> rename_i h'
    · subst i
      have := Nat.le_add_left j k
      simp [liftVar_lt (by exact Nat.lt_succ_of_le this)]
      rw [liftN'_comm (h := Nat.zero_le _), Nat.add_comm]
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
      let i+1 := i
      simp [liftVar, Nat.succ_lt_succ_iff]; split <;> rename_i hi
      · simp [liftN, liftVar_lt hi]
      · have := Nat.lt_add_left n hk
        rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
        simp [liftN]; rw [liftVar_le (Nat.not_lt.1 hi)]

theorem liftN_inst_hi (e1 e2 : SExpr L) (n k : Nat) :
    liftN n (e1.inst e2) k = (liftN n e1 (k+1)).inst (liftN n e2 k) := liftN_instN_hi ..

theorem lift_instN_lo (e1 e2 : SExpr L) : lift (e1.inst e2 k) = (lift e1).inst e2 (k + 1) :=
  Nat.add_comm .. ▸ liftN_instN_lo (hj := Nat.zero_le _) ..

theorem lift_inst_hi (e1 e2 : SExpr L) :
    lift (e1.inst e2) = (liftN 1 e1 1).inst (lift e2) := liftN_instN_hi ..

-- inst-inst interaction (high side)
theorem inst_inst_hi (e1 e2 e3 : SExpr L) (k j : Nat) :
    inst (e1.inst e2 k) e3 (j+k) = (e1.inst e3 (j+k+1)).inst (e2.inst e3 j) k := by
  induction e1 generalizing k with simp [inst, instVar, *]
  | bvar i => apply inst_instVar_hi
  | _ => rename_i IH; apply IH
where
  inst_instVar_hi (i : Nat) (e2 e3 : SExpr L) (k j : Nat) :
      inst (instVar i e2 k) e3 (j+k) = (instVar i e3 (j+k+1)).inst (e2.inst e3 j) k := by
    simp [instVar]; split <;> rename_i h
    · simp [Nat.lt_succ_of_lt, inst, instVar, h, Nat.lt_of_lt_of_le h (Nat.le_add_left k j)]
    split <;> rename_i h'
    · subst i
      simp [Nat.lt_succ_of_le, Nat.le_add_left, inst, instVar]
      rw [liftN_instN_lo k e2 e3 j _ (Nat.zero_le _), Nat.add_comm]
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
      let i+1 := i
      simp [inst, instVar]; split <;> rename_i hi
      · simp [inst, instVar, h, h']
      split <;> rename_i hi'
      · subst i
        suffices liftN (j+k+1) .. = _ by rw [this]; exact (inst_liftN ..).symm
        exact (liftN'_liftN' (Nat.zero_le _) (Nat.le_add_left k j)).symm
      · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 hi) (Ne.symm hi')
        let i+1 := i
        simp [inst, instVar]
        have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
        rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]

theorem inst0_inst_hi (e1 e2 e3 : SExpr L) (j : Nat) :
    inst (e1.inst e2) e3 j = (e1.inst e3 (j+1)).inst (e2.inst e3 j) := inst_inst_hi ..

-- ClosedN is preserved by inst
theorem ClosedN.instN {e : SExpr L} (h1 : ClosedN e (k+j+1)) (h2 : ClosedN e2 k) :
    ClosedN (e.inst e2 j) (k+j) := by
  induction e generalizing j
  case bvar i =>
    simp only [ClosedN] at h1
    simp only [inst, instVar]
    split <;> rename_i hi
    · simp only [ClosedN]; omega
    split <;> rename_i hi'
    · exact h2.liftN
    · have : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.1 hi) (Ne.symm hi')
      let i+1 := i
      simp only [ClosedN]; omega
  case sort | const | lit => simp [inst, ClosedN]
  case app fn arg ih1 ih2 =>
    simp only [ClosedN] at h1 ⊢; simp only [inst]
    simp only [ClosedN]
    exact ⟨ih1 h1.1, ih2 h1.2⟩
  case lam dom body ih1 ih2 =>
    simp only [ClosedN] at h1 ⊢; simp only [inst]
    simp only [ClosedN]
    exact ⟨ih1 h1.1, ih2 (j := j+1) h1.2⟩
  case forallE dom body ih1 ih2 =>
    simp only [ClosedN] at h1 ⊢; simp only [inst]
    simp only [ClosedN]
    exact ⟨ih1 h1.1, ih2 (j := j+1) h1.2⟩
  case letE ty val body ih1 ih2 ih3 =>
    simp only [ClosedN] at h1 ⊢; simp only [inst]
    simp only [ClosedN]
    exact ⟨ih1 h1.1, ih2 h1.2.1, ih3 (j := j+1) h1.2.2⟩
  case proj t i s ih =>
    simp only [ClosedN] at h1 ⊢; simp only [inst]
    simp only [ClosedN]
    exact ih h1

theorem ClosedN.inst (h1 : ClosedN e (k+1)) (h2 : ClosedN (L := L) e2 k) :
    ClosedN (e.inst e2) k := h1.instN (j := 0) h2

-- Closed expression is stable under inst
theorem ClosedN.instN_eq (self : ClosedN (L := L) e1 k) (h : k ≤ j) :
    e1.inst e2 j = e1 := by
  conv => lhs; rw [← self.liftN_eq (n := 1) h]
  rw [inst_liftN]

-- Useful for the roundtrip: substituting bvar 0 into a lifted expression
theorem instN_bvar0 (e : SExpr L) (k : Nat) :
    inst (e.liftN 1 (k+1)) (.bvar 0) k = e := by
  induction e generalizing k with simp [liftN, inst, *]
  | bvar i =>
    unfold liftVar instVar
    split <;> rename_i h
    · -- i < k+1
      split <;> rename_i h'
      · -- i < k: result is .bvar i
        rfl
      · -- k ≤ i, so i = k (from i < k+1 and ¬(i < k))
        have hik : i = k := by omega
        subst hik
        simp [liftN, liftVar]
    · -- ¬(i < k+1), so k < i
      rw [Nat.add_comm 1 i]
      have h1 : ¬(i + 1 < k) := by omega
      have h2 : i + 1 ≠ k := by omega
      rw [if_neg h1, if_neg h2]
      congr 1

end SExpr

-- Universe-level instantiation on TExpr
namespace SExpr

variable (ls : List SLevel) in
def instL : TExpr → TExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL
  | .letE ty val body => .letE ty.instL val.instL body.instL
  | .lit n => .lit n
  | .proj t i s => .proj t i s.instL

theorem instL_liftN (ls : List SLevel) (e : TExpr) (n k : Nat) :
    (e.liftN n k).instL ls = (e.instL ls).liftN n k := by
  induction e generalizing k with simp [instL, liftN, *]

theorem instL_inst (ls : List SLevel) (e1 e2 : TExpr) (k : Nat) :
    (e1.inst e2 k).instL ls = (e1.instL ls).inst (e2.instL ls) k := by
  induction e1 generalizing k with simp [instL, inst, *]
  | bvar i =>
    simp only [instVar]
    split
    · rfl
    split
    · rename_i h; rw [instL_liftN]
    · rfl

theorem ClosedN.instL (self : ClosedN e k) (ls : List SLevel) :
    ClosedN (e.instL ls) k := by
  induction e generalizing k with
    (simp [SExpr.instL, ClosedN] at *; try exact self)
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1, ih2 self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1, ih2 self.2⟩
  | letE _ _ _ ih1 ih2 ih3 => exact ⟨ih1 self.1, ih2 self.2.1, ih3 self.2.2⟩
  | proj _ _ _ ih => exact ih self

theorem instL_instL (ls ls' : List SLevel) (e : TExpr) :
    (e.instL ls).instL ls' = e.instL (ls.map (SLevel.inst ls')) := by
  induction e with simp [instL, *]
  | sort u => exact SLevel.inst_inst
  | const c us =>
    intro a _
    exact SLevel.inst_inst

end SExpr

end Ix.Theory
