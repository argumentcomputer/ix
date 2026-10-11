import Ix.Compile.Image

/-!
# M7 X1: the erased terms and their de Bruijn arithmetic

The conversion relation of X1 (`Conv.lean`) is stated on the **kernel-relevant skeleton** of an
`Ix.Expr`: `Tm`, the same constructors without the cached Blake3 hashes, the binder names, the
binder infos, the `letE` non-dependency flag and the `mdata` wrappers. `er : Ix.Expr → Tm` is
the erasure. Two expressions with the same erasure are the same term for every kernel (the
hashes are a cache, `mdata` is metadata the kernels ignore, design document §4.8: "the kernels
see an ordinary `mdata`"; binder names and infos do not enter conversion), and every compiler
function this package reasons about commutes with `er` (`Erase.lean`), so statements about
`Ix.Expr` are made through `er` and never depend on how a hash was computed.

Names, levels and literals are kept as they are (`Ix.Name`, `Ix.Level`, `Lean.Literal`):
constants are identified by their names, levels syntactically.

The operations, on loose variables (`bvar i` refers to the `i`-th enclosing binder outside the
term when `i` is at least the number of binders entered):

* `lift n c t`: add `n` to every loose variable `≥ c` (`Ix.Compile.Canon.liftLoose`);
* `lower n c t`: subtract `n` from every loose variable `≥ c + n` (`lowerLoose`);
* `inst v k t`: replace `bvar k` (under `k` binders) by `v` lifted by `k` and lower the
  variables above it: the plain substitution `t[k := v]` of the β-rule, `v`'s loose variables
  referring to the context outside `t`'s first `k` binders (`Ix.Compile.Image.hinst`'s
  convention);
* `occ t k`: `bvar k` occurs loose in `t` (`hasLooseBVar`, `occursM`);
* `appN f as`: the application spine (`mkAppN`).
-/

namespace Ix.CompileCert.Conv

open Ix (Name Level Expr)

/-- The kernel-relevant skeleton of an `Ix.Expr`. -/
inductive Tm where
  | bvar (i : Nat)
  | fvar (n : Name)
  | mvar (n : Name)
  | sort (u : Level)
  | const (n : Name) (us : Array Level)
  | app (f a : Tm)
  | lam (t b : Tm)
  | pi (t b : Tm)
  | letE (t v b : Tm)
  | lit (l : Lean.Literal)
  | proj (s : Name) (i : Nat) (e : Tm)
  deriving Inhabited

/-- The erasure: hashes, binder names and infos, the `letE` flag and `mdata` dropped. -/
def er : Expr → Tm
  | .bvar i _ => .bvar i
  | .fvar n _ => .fvar n
  | .mvar n _ => .mvar n
  | .sort u _ => .sort u
  | .const n us _ => .const n us
  | .app f a _ => .app (er f) (er a)
  | .lam _ t b _ _ => .lam (er t) (er b)
  | .forallE _ t b _ _ => .pi (er t) (er b)
  | .letE _ t v b _ _ => .letE (er t) (er v) (er b)
  | .lit l _ => .lit l
  | .mdata _ e _ => er e
  | .proj s i e _ => .proj s i (er e)

namespace Tm

/-- Add `n` to every loose variable `≥ c`. -/
def lift (n : Nat) : Nat → Tm → Tm
  | c, bvar i => bvar (if c ≤ i then i + n else i)
  | c, app f a => app (lift n c f) (lift n c a)
  | c, lam t b => lam (lift n c t) (lift n (c + 1) b)
  | c, pi t b => pi (lift n c t) (lift n (c + 1) b)
  | c, letE t v b => letE (lift n c t) (lift n c v) (lift n (c + 1) b)
  | c, proj s i e => proj s i (lift n c e)
  | _, fvar x => fvar x
  | _, mvar x => mvar x
  | _, sort u => sort u
  | _, const x us => const x us
  | _, lit l => lit l

/-- Subtract `n` from every loose variable `≥ c + n` (the variables in `[c, c + n)` are
left as they are; callers check there are none). -/
def lower (n : Nat) : Nat → Tm → Tm
  | c, bvar i => bvar (if c + n ≤ i then i - n else i)
  | c, app f a => app (lower n c f) (lower n c a)
  | c, lam t b => lam (lower n c t) (lower n (c + 1) b)
  | c, pi t b => pi (lower n c t) (lower n (c + 1) b)
  | c, letE t v b => letE (lower n c t) (lower n c v) (lower n (c + 1) b)
  | c, proj s i e => proj s i (lower n c e)
  | _, fvar x => fvar x
  | _, mvar x => mvar x
  | _, sort u => sort u
  | _, const x us => const x us
  | _, lit l => lit l

/-- Plain substitution: `bvar k` (under `k` binders) replaced by `v` lifted by `k`, the
variables above it lowered by one. -/
def inst (v : Tm) : Nat → Tm → Tm
  | k, bvar i => if i = k then lift k 0 v else bvar (if k < i then i - 1 else i)
  | k, app f a => app (inst v k f) (inst v k a)
  | k, lam t b => lam (inst v k t) (inst v (k + 1) b)
  | k, pi t b => pi (inst v k t) (inst v (k + 1) b)
  | k, letE t w b => letE (inst v k t) (inst v k w) (inst v (k + 1) b)
  | k, proj s i e => proj s i (inst v k e)
  | _, fvar x => fvar x
  | _, mvar x => mvar x
  | _, sort u => sort u
  | _, const x us => const x us
  | _, lit l => lit l

/-- `bvar k` occurs loose in `t`. -/
def occ : Tm → Nat → Bool
  | bvar i, k => i == k
  | app f a, k => occ f k || occ a k
  | lam t b, k => occ t k || occ b (k + 1)
  | pi t b, k => occ t k || occ b (k + 1)
  | letE t v b, k => occ t k || occ v k || occ b (k + 1)
  | proj _ _ e, k => occ e k
  | _, _ => false

/-- One more than the largest loose variable (`0`: closed). -/
def range : Tm → Nat
  | bvar i => i + 1
  | app f a => max (range f) (range a)
  | lam t b => max (range t) (range b - 1)
  | pi t b => max (range t) (range b - 1)
  | letE t v b => max (max (range t) (range v)) (range b - 1)
  | proj _ _ e => range e
  | _ => 0

/-- The application spine `f a₁ … aₙ`. -/
def appN (f : Tm) : List Tm → Tm
  | [] => f
  | a :: as => appN (app f a) as

theorem appN_nil (f : Tm) : appN f [] = f := rfl
theorem appN_cons (f a : Tm) (as : List Tm) : appN f (a :: as) = appN (app f a) as := rfl

theorem appN_append (f : Tm) (as bs : List Tm) : appN f (as ++ bs) = appN (appN f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (app f a)

theorem appN_concat (f : Tm) (as : List Tm) (b : Tm) : appN f (as ++ [b]) = app (appN f as) b := by
  rw [appN_append]; rfl

/-! ## Lifting -/

theorem lift_zero : ∀ (c : Nat) (t : Tm), lift 0 c t = t
  | c, bvar i => by simp [lift]
  | c, app f a => by simp [lift, lift_zero c f, lift_zero c a]
  | c, lam t b => by simp [lift, lift_zero c t, lift_zero (c + 1) b]
  | c, pi t b => by simp [lift, lift_zero c t, lift_zero (c + 1) b]
  | c, letE t v b => by simp [lift, lift_zero c t, lift_zero c v, lift_zero (c + 1) b]
  | c, proj s i e => by simp [lift, lift_zero c e]
  | _, fvar _ | _, mvar _ | _, sort _ | _, const _ _ | _, lit _ => rfl

/-- Two lifts whose cutoffs overlap compose. -/
theorem lift_lift_of_le : ∀ (m n c d : Nat) (t : Tm), c ≤ d → d ≤ c + n →
    lift m d (lift n c t) = lift (m + n) c t
  | m, n, c, d, bvar i, h1, h2 => by
    simp only [lift]
    by_cases hi : c ≤ i
    · have : d ≤ i + n := by omega
      simp only [hi, ↓reduceIte, this]; congr 1; omega
    · have : ¬ d ≤ i := by omega
      simp [hi, this]
  | m, n, c, d, app f a, h1, h2 => by
    simp only [lift, lift_lift_of_le m n c d f h1 h2, lift_lift_of_le m n c d a h1 h2]
  | m, n, c, d, lam t b, h1, h2 => by
    simp only [lift, lift_lift_of_le m n c d t h1 h2,
      lift_lift_of_le m n (c + 1) (d + 1) b (by omega) (by omega)]
  | m, n, c, d, pi t b, h1, h2 => by
    simp only [lift, lift_lift_of_le m n c d t h1 h2,
      lift_lift_of_le m n (c + 1) (d + 1) b (by omega) (by omega)]
  | m, n, c, d, letE t v b, h1, h2 => by
    simp only [lift, lift_lift_of_le m n c d t h1 h2, lift_lift_of_le m n c d v h1 h2,
      lift_lift_of_le m n (c + 1) (d + 1) b (by omega) (by omega)]
  | m, n, c, d, proj s i e, h1, h2 => by simp only [lift, lift_lift_of_le m n c d e h1 h2]
  | _, _, _, _, fvar _, _, _ | _, _, _, _, mvar _, _, _ | _, _, _, _, sort _, _, _
  | _, _, _, _, const _ _, _, _ | _, _, _, _, lit _, _, _ => rfl

/-- Two lifts at separate cutoffs commute. -/
theorem lift_lift_comm : ∀ (m n c d : Nat) (t : Tm), d ≤ c →
    lift m d (lift n c t) = lift n (c + m) (lift m d t)
  | m, n, c, d, bvar i, h => by
    simp only [lift]
    by_cases hc : c ≤ i
    · have hd : d ≤ i := by omega
      have : d ≤ i + n := by omega
      simp only [hc, hd, this, ↓reduceIte]
      have : c + m ≤ i + m := by omega
      simp only [this, ↓reduceIte]; congr 1; omega
    · by_cases hd : d ≤ i
      · have : ¬ c + m ≤ i + m := by omega
        simp [hc, hd, this]
      · have : ¬ c + m ≤ i := by omega
        simp [hc, hd, this]
  | m, n, c, d, app f a, h => by
    simp only [lift, lift_lift_comm m n c d f h, lift_lift_comm m n c d a h]
  | m, n, c, d, lam t b, h => by
    simp only [lift, lift_lift_comm m n c d t h, lift_lift_comm m n (c + 1) (d + 1) b (by omega)]
    rw [show c + 1 + m = c + m + 1 by omega]
  | m, n, c, d, pi t b, h => by
    simp only [lift, lift_lift_comm m n c d t h, lift_lift_comm m n (c + 1) (d + 1) b (by omega)]
    rw [show c + 1 + m = c + m + 1 by omega]
  | m, n, c, d, letE t v b, h => by
    simp only [lift, lift_lift_comm m n c d t h, lift_lift_comm m n c d v h,
      lift_lift_comm m n (c + 1) (d + 1) b (by omega)]
    rw [show c + 1 + m = c + m + 1 by omega]
  | m, n, c, d, proj s i e, h => by simp only [lift, lift_lift_comm m n c d e h]
  | _, _, _, _, fvar _, _ | _, _, _, _, mvar _, _ | _, _, _, _, sort _, _
  | _, _, _, _, const _ _, _ | _, _, _, _, lit _, _ => rfl

/-! ## Occurrence and range -/

theorem occ_lift_lt : ∀ (n c k : Nat) (t : Tm), k < c → occ (lift n c t) k = occ t k
  | n, c, k, bvar i, h => by
    simp only [lift, occ]
    by_cases hi : c ≤ i
    · simp only [hi, ↓reduceIte]
      have h1 : (i + n == k) = false := by simp; omega
      have h2 : (i == k) = false := by simp; omega
      rw [h1, h2]
    · simp [hi]
  | n, c, k, app f a, h => by simp only [lift, occ, occ_lift_lt n c k f h, occ_lift_lt n c k a h]
  | n, c, k, lam t b, h => by
    simp only [lift, occ, occ_lift_lt n c k t h, occ_lift_lt n (c + 1) (k + 1) b (by omega)]
  | n, c, k, pi t b, h => by
    simp only [lift, occ, occ_lift_lt n c k t h, occ_lift_lt n (c + 1) (k + 1) b (by omega)]
  | n, c, k, letE t v b, h => by
    simp only [lift, occ, occ_lift_lt n c k t h, occ_lift_lt n c k v h,
      occ_lift_lt n (c + 1) (k + 1) b (by omega)]
  | n, c, k, proj s i e, h => by simp only [lift, occ, occ_lift_lt n c k e h]
  | _, _, _, fvar _, _ | _, _, _, mvar _, _ | _, _, _, sort _, _
  | _, _, _, const _ _, _ | _, _, _, lit _, _ => rfl

/-- A lifted term has no loose variable in `[c, c + n)`. -/
theorem occ_lift_mid : ∀ (n c k : Nat) (t : Tm), c ≤ k → k < c + n → occ (lift n c t) k = false
  | n, c, k, bvar i, h1, h2 => by
    simp only [lift, occ]
    by_cases hi : c ≤ i
    · simp only [hi, ↓reduceIte]; simp; omega
    · simp only [hi]; simp; omega
  | n, c, k, app f a, h1, h2 => by
    simp only [lift, occ, occ_lift_mid n c k f h1 h2, occ_lift_mid n c k a h1 h2, Bool.or_false]
  | n, c, k, lam t b, h1, h2 => by
    simp only [lift, occ, occ_lift_mid n c k t h1 h2,
      occ_lift_mid n (c + 1) (k + 1) b (by omega) (by omega), Bool.or_false]
  | n, c, k, pi t b, h1, h2 => by
    simp only [lift, occ, occ_lift_mid n c k t h1 h2,
      occ_lift_mid n (c + 1) (k + 1) b (by omega) (by omega), Bool.or_false]
  | n, c, k, letE t v b, h1, h2 => by
    simp only [lift, occ, occ_lift_mid n c k t h1 h2, occ_lift_mid n c k v h1 h2,
      occ_lift_mid n (c + 1) (k + 1) b (by omega) (by omega), Bool.or_false]
  | n, c, k, proj s i e, h1, h2 => by simp only [lift, occ, occ_lift_mid n c k e h1 h2]
  | _, _, _, fvar _, _, _ | _, _, _, mvar _, _, _ | _, _, _, sort _, _, _
  | _, _, _, const _ _, _, _ | _, _, _, lit _, _, _ => rfl

/-- No loose variable at or above `range t`. -/
theorem occ_of_range_le : ∀ (t : Tm) (k : Nat), range t ≤ k → occ t k = false
  | bvar i, k, h => by simp only [range] at h; simp only [occ]; simp; omega
  | app f a, k, h => by
    simp only [range, Nat.max_le] at h
    simp only [occ, occ_of_range_le f k h.1, occ_of_range_le a k h.2, Bool.or_false]
  | lam t b, k, h => by
    simp only [range, Nat.max_le] at h
    simp only [occ, occ_of_range_le t k h.1, occ_of_range_le b (k + 1) (by omega), Bool.or_false]
  | pi t b, k, h => by
    simp only [range, Nat.max_le] at h
    simp only [occ, occ_of_range_le t k h.1, occ_of_range_le b (k + 1) (by omega), Bool.or_false]
  | letE t v b, k, h => by
    simp only [range, Nat.max_le] at h
    simp only [occ, occ_of_range_le t k h.1.1, occ_of_range_le v k h.1.2,
      occ_of_range_le b (k + 1) (by omega), Bool.or_false]
  | proj s i e, k, h => by simp only [range] at h; simp only [occ, occ_of_range_le e k h]
  | fvar _, _, _ | mvar _, _, _ | sort _, _, _ | const _ _, _, _ | lit _, _, _ => rfl

/-! ## Terms with no loose variable at or above a cutoff -/

theorem lift_of_range_le : ∀ (n c : Nat) (t : Tm), range t ≤ c → lift n c t = t
  | n, c, bvar i, h => by simp only [range] at h; simp only [lift]; simp; omega
  | n, c, app f a, h => by
    simp only [range, Nat.max_le] at h
    simp only [lift, lift_of_range_le n c f h.1, lift_of_range_le n c a h.2]
  | n, c, lam t b, h => by
    simp only [range, Nat.max_le] at h
    simp only [lift, lift_of_range_le n c t h.1, lift_of_range_le n (c + 1) b (by omega)]
  | n, c, pi t b, h => by
    simp only [range, Nat.max_le] at h
    simp only [lift, lift_of_range_le n c t h.1, lift_of_range_le n (c + 1) b (by omega)]
  | n, c, letE t v b, h => by
    simp only [range, Nat.max_le] at h
    simp only [lift, lift_of_range_le n c t h.1.1, lift_of_range_le n c v h.1.2,
      lift_of_range_le n (c + 1) b (by omega)]
  | n, c, proj s i e, h => by simp only [range] at h; simp only [lift, lift_of_range_le n c e h]
  | _, _, fvar _, _ | _, _, mvar _, _ | _, _, sort _, _ | _, _, const _ _, _ | _, _, lit _, _ => rfl

theorem lower_of_range_le : ∀ (n c : Nat) (t : Tm), range t ≤ c → lower n c t = t
  | n, c, bvar i, h => by simp only [range] at h; simp only [lower]; simp; omega
  | n, c, app f a, h => by
    simp only [range, Nat.max_le] at h
    simp only [lower, lower_of_range_le n c f h.1, lower_of_range_le n c a h.2]
  | n, c, lam t b, h => by
    simp only [range, Nat.max_le] at h
    simp only [lower, lower_of_range_le n c t h.1, lower_of_range_le n (c + 1) b (by omega)]
  | n, c, pi t b, h => by
    simp only [range, Nat.max_le] at h
    simp only [lower, lower_of_range_le n c t h.1, lower_of_range_le n (c + 1) b (by omega)]
  | n, c, letE t v b, h => by
    simp only [range, Nat.max_le] at h
    simp only [lower, lower_of_range_le n c t h.1.1, lower_of_range_le n c v h.1.2,
      lower_of_range_le n (c + 1) b (by omega)]
  | n, c, proj s i e, h => by simp only [range] at h; simp only [lower, lower_of_range_le n c e h]
  | _, _, fvar _, _ | _, _, mvar _, _ | _, _, sort _, _ | _, _, const _ _, _ | _, _, lit _, _ => rfl

theorem inst_of_range_le : ∀ (v : Tm) (k : Nat) (t : Tm), range t ≤ k → inst v k t = t
  | v, k, bvar i, h => by
    simp only [range] at h; simp only [inst]
    have : i ≠ k := by omega
    simp only [this, ↓reduceIte]; congr 1; simp; omega
  | v, k, app f a, h => by
    simp only [range, Nat.max_le] at h
    simp only [inst, inst_of_range_le v k f h.1, inst_of_range_le v k a h.2]
  | v, k, lam t b, h => by
    simp only [range, Nat.max_le] at h
    simp only [inst, inst_of_range_le v k t h.1, inst_of_range_le v (k + 1) b (by omega)]
  | v, k, pi t b, h => by
    simp only [range, Nat.max_le] at h
    simp only [inst, inst_of_range_le v k t h.1, inst_of_range_le v (k + 1) b (by omega)]
  | v, k, letE t w b, h => by
    simp only [range, Nat.max_le] at h
    simp only [inst, inst_of_range_le v k t h.1.1, inst_of_range_le v k w h.1.2,
      inst_of_range_le v (k + 1) b (by omega)]
  | v, k, proj s i e, h => by simp only [range] at h; simp only [inst, inst_of_range_le v k e h]
  | _, _, fvar _, _ | _, _, mvar _, _ | _, _, sort _, _ | _, _, const _ _, _ | _, _, lit _, _ => rfl

/-! ## Substitution against lifting -/

/-- Substituting for a variable a lift skipped is lowering it back. -/
theorem inst_lift_self : ∀ (v : Tm) (k : Nat) (t : Tm), inst v k (lift 1 k t) = t
  | v, k, bvar i => by
    simp only [lift, inst]
    by_cases hi : k ≤ i
    · simp only [hi, ↓reduceIte]
      have : i + 1 ≠ k := by omega
      simp only [this, ↓reduceIte]; congr 1; simp; omega
    · simp only [hi, ↓reduceIte]
      have : i ≠ k := by omega
      simp only [this, ↓reduceIte]; congr 1; simp; omega
  | v, k, app f a => by simp only [lift, inst, inst_lift_self v k f, inst_lift_self v k a]
  | v, k, lam t b => by simp only [lift, inst, inst_lift_self v k t, inst_lift_self v (k + 1) b]
  | v, k, pi t b => by simp only [lift, inst, inst_lift_self v k t, inst_lift_self v (k + 1) b]
  | v, k, letE t w b => by
    simp only [lift, inst, inst_lift_self v k t, inst_lift_self v k w, inst_lift_self v (k + 1) b]
  | v, k, proj s i e => by simp only [lift, inst, inst_lift_self v k e]
  | _, _, fvar _ | _, _, mvar _ | _, _, sort _ | _, _, const _ _ | _, _, lit _ => rfl

/-- A lift below the substituted variable moves it up. -/
theorem inst_lift_lo : ∀ (v : Tm) (n c k : Nat) (t : Tm), c ≤ k →
    inst v (k + n) (lift n c t) = lift n c (inst v k t)
  | v, n, c, k, bvar i, h => by
    simp only [lift, inst]
    by_cases hc : c ≤ i
    · simp only [hc, ↓reduceIte]
      by_cases hk : i = k
      · subst hk
        simp only [↓reduceIte]
        rw [lift_lift_of_le n i 0 c v (Nat.zero_le _) (by omega), Nat.add_comm]
      · have : i + n ≠ k + n := by omega
        simp only [this, hk, ↓reduceIte, lift]
        by_cases hki : k < i
        · have : k + n < i + n := by omega
          simp only [this, hki, ↓reduceIte]
          have : c ≤ i - 1 := by omega
          simp only [this, ↓reduceIte]; congr 1; omega
        · have : ¬ k + n < i + n := by omega
          simp only [this, hki, ↓reduceIte, hc]
    · simp only [hc, ↓reduceIte]
      have h1 : i ≠ k + n := by omega
      have h2 : i ≠ k := by omega
      have h3 : ¬ k + n < i := by omega
      have h4 : ¬ k < i := by omega
      simp [h1, h2, h3, h4, lift, hc]
  | v, n, c, k, app f a, h => by
    simp only [lift, inst, inst_lift_lo v n c k f h, inst_lift_lo v n c k a h]
  | v, n, c, k, lam t b, h => by
    simp only [lift, inst, inst_lift_lo v n c k t h]
    rw [show k + n + 1 = (k + 1) + n by omega, inst_lift_lo v n (c + 1) (k + 1) b (by omega)]
  | v, n, c, k, pi t b, h => by
    simp only [lift, inst, inst_lift_lo v n c k t h]
    rw [show k + n + 1 = (k + 1) + n by omega, inst_lift_lo v n (c + 1) (k + 1) b (by omega)]
  | v, n, c, k, letE t w b, h => by
    simp only [lift, inst, inst_lift_lo v n c k t h, inst_lift_lo v n c k w h]
    rw [show k + n + 1 = (k + 1) + n by omega, inst_lift_lo v n (c + 1) (k + 1) b (by omega)]
  | v, n, c, k, proj s i e, h => by simp only [lift, inst, inst_lift_lo v n c k e h]
  | _, _, _, _, fvar _, _ | _, _, _, _, mvar _, _ | _, _, _, _, sort _, _
  | _, _, _, _, const _ _, _ | _, _, _, _, lit _, _ => rfl

/-- A lift above the substituted variable passes into the value. -/
theorem lift_inst_hi : ∀ (v : Tm) (n c k : Nat) (t : Tm), k ≤ c →
    lift n c (inst v k t) = inst (lift n (c - k) v) k (lift n (c + 1) t)
  | v, n, c, k, bvar i, h => by
    by_cases hk : i = k
    · subst hk
      have h1 : ¬ c + 1 ≤ i := by omega
      simp only [lift, inst, h1, ↓reduceIte]
      rw [lift_lift_comm i n (c - i) 0 v (Nat.zero_le _), show c - i + i = c by omega]
    · by_cases hki : k < i
      · by_cases hc : c + 1 ≤ i
        · have h1 : c ≤ i - 1 := by omega
          have h2 : i + n ≠ k := by omega
          have h3 : k < i + n := by omega
          simp only [lift, inst, hk, hki, hc, h1, h2, h3, ↓reduceIte]; congr 1; omega
        · have h1 : ¬ c ≤ i - 1 := by omega
          simp only [lift, inst, hk, hki, hc, h1, ↓reduceIte]
      · have h1 : ¬ c ≤ i := by omega
        have h2 : ¬ c + 1 ≤ i := by omega
        simp only [lift, inst, hk, hki, h1, h2, ↓reduceIte]
  | v, n, c, k, app f a, h => by
    simp only [lift, inst, lift_inst_hi v n c k f h, lift_inst_hi v n c k a h]
  | v, n, c, k, lam t b, h => by
    simp only [lift, inst, lift_inst_hi v n c k t h, lift_inst_hi v n (c + 1) (k + 1) b (by omega)]
    rw [show c + 1 - (k + 1) = c - k by omega]
  | v, n, c, k, pi t b, h => by
    simp only [lift, inst, lift_inst_hi v n c k t h, lift_inst_hi v n (c + 1) (k + 1) b (by omega)]
    rw [show c + 1 - (k + 1) = c - k by omega]
  | v, n, c, k, letE t w b, h => by
    simp only [lift, inst, lift_inst_hi v n c k t h, lift_inst_hi v n c k w h,
      lift_inst_hi v n (c + 1) (k + 1) b (by omega)]
    rw [show c + 1 - (k + 1) = c - k by omega]
  | v, n, c, k, proj s i e, h => by simp only [lift, inst, lift_inst_hi v n c k e h]
  | _, _, _, _, fvar _, _ | _, _, _, _, mvar _, _ | _, _, _, _, sort _, _
  | _, _, _, _, const _ _, _ | _, _, _, _, lit _, _ => rfl

/-- A lifted value passes under a substitution above the lift. -/
theorem inst_lift_val : ∀ (u : Tm) (n c k : Nat) (t : Tm), c ≤ k →
    inst u (k + n) (lift n c t) = lift n c (inst u k t) := inst_lift_lo

/-- **The substitution lemma.** -/
theorem inst_inst : ∀ (u v : Tm) (j k : Nat) (t : Tm), j ≤ k →
    inst u k (inst v j t) = inst (inst u (k - j) v) j (inst u (k + 1) t)
  | u, v, j, k, bvar i, h => by
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · have a1 : i ≠ j := by omega
      have a2 : ¬ j < i := by omega
      have a3 : i ≠ k := by omega
      have a4 : ¬ k < i := by omega
      have a5 : i ≠ k + 1 := by omega
      have a6 : ¬ k + 1 < i := by omega
      simp only [inst, a1, a2, a3, a4, a5, a6, ↓reduceIte]
    · subst hij
      have a5 : i ≠ k + 1 := by omega
      have a6 : ¬ k + 1 < i := by omega
      simp only [inst, a5, a6, ↓reduceIte]
      have e := inst_lift_lo u i 0 (k - i) v (Nat.zero_le _)
      rw [show k - i + i = k by omega] at e
      exact e
    · have a1 : i ≠ j := by omega
      rcases Nat.lt_trichotomy (i - 1) k with hk | hk | hk
      · have a3 : i - 1 ≠ k := by omega
        have a4 : ¬ k < i - 1 := by omega
        have a5 : i ≠ k + 1 := by omega
        have a6 : ¬ k + 1 < i := by omega
        simp only [inst, a1, hij, a3, a4, a5, a6, ↓reduceIte]
      · obtain rfl : i = k + 1 := by omega
        have a5 : k + 1 - 1 = k := by omega
        simp only [inst, a1, hij, a5, ↓reduceIte]
        rw [show k + 1 = 1 + k by omega, ← lift_lift_of_le 1 k 0 j u (Nat.zero_le _) (by omega),
          inst_lift_self]
      · have a3 : i - 1 ≠ k := by omega
        have a5 : i ≠ k + 1 := by omega
        have a6 : k + 1 < i := by omega
        have a7 : i - 1 ≠ j := by omega
        have a8 : j < i - 1 := by omega
        simp only [inst, a1, hij, a3, hk, a5, a6, a7, a8, ↓reduceIte]
  | u, v, j, k, app f a, h => by
    simp only [inst, inst_inst u v j k f h, inst_inst u v j k a h]
  | u, v, j, k, lam t b, h => by
    simp only [inst, inst_inst u v j k t h, inst_inst u v (j + 1) (k + 1) b (by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | u, v, j, k, pi t b, h => by
    simp only [inst, inst_inst u v j k t h, inst_inst u v (j + 1) (k + 1) b (by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | u, v, j, k, letE t w b, h => by
    simp only [inst, inst_inst u v j k t h, inst_inst u v j k w h,
      inst_inst u v (j + 1) (k + 1) b (by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | u, v, j, k, proj s i e, h => by simp only [inst, inst_inst u v j k e h]
  | _, _, _, _, fvar _, _ | _, _, _, _, mvar _, _ | _, _, _, _, sort _, _
  | _, _, _, _, const _ _, _ | _, _, _, _, lit _, _ => rfl

end Tm

end Ix.CompileCert.Conv
