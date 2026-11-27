import Aiur.Tiling.Refinement
import Aiur.Optimized.Grouping.Memo
import Std.Data.HashSet
import Std.Data.HashMap

/-!
# Boolean enables, checked

LogUp's field balance is read as integer counts only if every send and memory
enable is `0` or `1` on every row (`Bridge.Boolean`). `checkEnables c` decides a
certificate for that from the activated chip's own constraints, so the fact is
a consequence of `(lower idOf c).Holds w` rather than a hypothesis.

An enable `e` is certified (`boolCert cs e`) when

* it is identically `0` or `1`;
* some constraint of `cs` is identical to `e·(e − 1)` or to `e − e·e`;
* it is a product `x·y` of certified factors; or
* it is `1 − x` for a certified `x`.

Identity is decided by the sound normal form of `Poly.lean`. The certificate is
syntactic: an enable the checker cannot certify is rejected, never assumed.
-/

namespace Aiur.Tiling.Bridge

open Aiur.Circuit
open Aiur.Optimized


variable {F : Type} [Field F] [DecidableEq F]

/-- Every send and memory enable of the activated chip is boolean on the row:
the assumption under which LogUp's field balance is read as integer counts
(`Optimized/EndToEnd.lean`). -/
def Boolean (c : Chip F) (w : Var → F) : Prop :=
  (∀ s ∈ (Activation.compile c).sends, s.enable.denote w = 0 ∨ s.enable.denote w = 1) ∧
    ∀ m ∈ (Activation.compile c).memory, m.enable.denote w = 0 ∨ m.enable.denote w = 1

/-- `e·(e − 1)`. -/
def boolExpr (e : ArithExpr F) : ArithExpr F := .mul e (.sub e (.const 1))

/-- Some constraint of `cs` is identical to `±e·(e − 1)`, or `e` is identically `0` or `1`. -/
def boolDirect (cs : List (ArithExpr F)) (e : ArithExpr F) : Bool :=
  Poly.Identical (Poly.ofExpr e) ([] : Poly F) || Poly.Identical (Poly.ofExpr e) (Poly.const 1) ||
    cs.any fun c => Poly.Identical (Poly.ofExpr c) (Poly.ofExpr (boolExpr e)) ||
      Poly.Identical (Poly.ofExpr c) (Poly.ofExpr (.sub e (.mul e e)))

def boolCert (cs : List (ArithExpr F)) : ArithExpr F → Bool
  | .mul x y => boolDirect cs (.mul x y) || (boolCert cs x && boolCert cs y)
  | .sub x y => boolDirect cs (.sub x y) ||
      (Poly.Identical (Poly.ofExpr x) (Poly.const 1) && boolCert cs y)
  | e => boolDirect cs e

/-- `e` with the variable `v` replaced by the constant `k`. -/
def substVar (v : Var) (k : F) : ArithExpr F → ArithExpr F
  | .const c => .const c
  | .var u => if u = v then .const k else .var u
  | .add x y => .add (substVar v k x) (substVar v k y)
  | .sub x y => .sub (substVar v k x) (substVar v k y)
  | .mul x y => .mul (substVar v k x) (substVar v k y)

/-- The variables of a nested sum `v₀ + (v₁ + …)` of variables. -/
def addVars : ArithExpr F → Option (List Var)
  | .var v => some [v]
  | .add x y => do return (← addVars x) ++ (← addVars y)
  | _ => none

def varsOf : ArithExpr F → List Var
  | .var v => [v]
  | .const _ => []
  | .add x y | .sub x y | .mul x y => varsOf x ++ varsOf y

def sumExpr (vs : List Var) : ArithExpr F := vs.foldr (fun v acc => .add (.var v) acc) (.const 0)

/-- `e` is a sum of distinct variables, all among the variables `J` of some
constraint, where every variable of `J` and the sum of `J` are certified
boolean and `|J| < bound`: at most one variable of `J` is `1`, so a partial sum
is `0` or `1`. This is the one-hot shape of match-arm selectors. -/
def boolSum (cs : List (ArithExpr F)) (bound : Nat) (e : ArithExpr F) : Bool :=
  match addVars e with
  | none => false
  | some I => decide I.Nodup && cs.any fun c =>
      let J := (varsOf c).dedup
      I.all (· ∈ J) && J.all (fun j => boolDirect cs (.var j)) && boolDirect cs (sumExpr J) &&
        decide (J.length < bound)

/-- The sum `v₀ + (v₁ + …)` of a nonempty variable list, as `addVars` reads it. -/
def addOf : List Var → ArithExpr F
  | [] => .const 0
  | [v] => .var v
  | v :: vs => .add (.var v) (addOf vs)

/-- `e` is identical (as a polynomial) to a one-hot partial sum `Σ I` or to its
complement `1 − Σ I`, where `I` are the variables of `e` and `Σ I` passes
`boolSum`. This is the shape of a default match arm's selector. -/
def boolLinear (cs : List (ArithExpr F)) (bound : Nat) (e : ArithExpr F) : Bool :=
  let I := (varsOf e).dedup
  !I.isEmpty && boolSum cs bound (addOf I) &&
    (Poly.Identical (Poly.ofExpr e) (Poly.ofExpr (addOf I)) ||
      Poly.Identical (Poly.ofExpr e) (Poly.ofExpr (.sub (.const 1) (addOf I))))

/-- The certified-boolean variables near `e`: the variables of `e` and of
every constraint sharing a variable with `e`, kept if `boolDirect` certifies
them. -/
def boolVars (cs : List (ArithExpr F)) (e : ArithExpr F) : List Var :=
  let E := (varsOf e).dedup
  let near := cs.filter fun c => (varsOf c).any (· ∈ E)
  (E ++ near.flatMap varsOf).dedup.filter fun v => boolDirect cs (.var v)

/-- The 0/1 assignment that is `1` exactly on `S`. -/
def indicator (S : List Var) (v : Var) : F := if v ∈ S then 1 else 0

/-- Case analysis over at most `2^12` assignments: every variable of `e` is
among the certified-boolean variables `V` near it, and on every 0/1
assignment of `V` satisfying the constraints over `V` alone, `e` is `0` or
`1`. -/
def boolEnum (cs : List (ArithExpr F)) (e : ArithExpr F) : Bool :=
  let V := boolVars cs e
  let C := cs.filter fun c => (varsOf c).all (· ∈ V)
  decide (V.length ≤ 12) && (varsOf e).all (· ∈ V) &&
    V.sublists.all fun S =>
      !(C.all fun c => decide (c.denote (indicator S) = 0)) ||
        decide (e.denote (indicator S) = 0) || decide (e.denote (indicator S) = 1)

def boolAny (cs : List (ArithExpr F)) (bound : Nat) (e : ArithExpr F) : Bool :=
  boolCert cs e || boolSum cs bound e || boolLinear cs bound e || boolEnum cs e

/-- `boolAny`, or a split on the row selector `sel`: some constraint is
identical to `(1 − sel)·e`, so `e = 0` unless `sel = 1`, and `e` with `sel := 1`
is certified. This is the shape of an activated enable whose source enable has
a nonzero constant term (`Activation.polynomial`, `Activation.silent`). -/
def boolCertAt (cs : List (ArithExpr F)) (bound : Nat) (sel : Var) (e : ArithExpr F) : Bool :=
  boolAny cs bound e ||
    ((cs.any fun c => Poly.Identical (Poly.ofExpr c) (Poly.ofExpr (.mul (.sub (.const 1) (.var sel)) e))) &&
      boolAny cs bound (substVar sel 1 e))

/-- Every send and memory enable of the activated chip is certified boolean by
the activated chip's constraints. `bound` is a `SmallCast` bound of the field. -/
def checkEnables (bound : Nat) (c : Chip F) : Bool :=
  let a := Activation.compile c
  a.sends.all (fun s => boolCertAt a.constraints bound c.numVars s.enable) &&
    a.memory.all (fun m => boolCertAt a.constraints bound c.numVars m.enable)

theorem boolDirect_sound {cs : List (ArithExpr F)} {e : ArithExpr F} {w : Var → F}
    (h : boolDirect cs e = true) (sat : Scalar.Circuit.Satisfies cs w) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  simp only [boolDirect, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (h | h) | ⟨c, hc, h | h⟩
  · left
    have := Poly.Identical.denote w h
    rw [Poly.denote_ofExpr] at this
    simpa [Poly.denote] using this
  · right
    have := Poly.Identical.denote w h
    rw [Poly.denote_ofExpr] at this
    simpa [Poly.denote, Poly.const, Mono.eval] using this
  · have zero := sat c hc
    have := Poly.Identical.denote w h
    rw [Poly.denote_ofExpr, Poly.denote_ofExpr, zero] at this
    simp only [boolExpr, Scalar.Circuit.ArithExpr.denote] at this
    rcases mul_eq_zero.mp this.symm with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · have zero := sat c hc
    have := Poly.Identical.denote w h
    rw [Poly.denote_ofExpr, Poly.denote_ofExpr, zero] at this
    simp only [Scalar.Circuit.ArithExpr.denote] at this
    have : e.denote w * (1 - e.denote w) = 0 := by rw [mul_sub, mul_one]; exact this.symm
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1).symm

theorem boolCert_sound {cs : List (ArithExpr F)} {w : Var → F}
    (sat : Scalar.Circuit.Satisfies cs w) :
    ∀ {e : ArithExpr F}, boolCert cs e = true → e.denote w = 0 ∨ e.denote w = 1
  | .const _, h => boolDirect_sound h sat
  | .var _, h => boolDirect_sound h sat
  | .add _ _, h => boolDirect_sound h sat
  | .mul x y, h => by
      simp only [boolCert, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hx, hy⟩
      · exact boolDirect_sound h sat
      · have bx := boolCert_sound sat hx
        have byy := boolCert_sound sat hy
        simp only [Scalar.Circuit.ArithExpr.denote]
        rcases bx with bx | bx <;> rcases byy with byy | byy <;> simp [bx, byy]
  | .sub x y, h => by
      simp only [boolCert, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hx, hy⟩
      · exact boolDirect_sound h sat
      · have one := Poly.Identical.denote w hx
        rw [Poly.denote_ofExpr] at one
        simp only [Poly.denote, Poly.const, Mono.eval] at one
        simp only [List.map_cons, List.map_nil, List.prod_nil, mul_one, List.sum_cons,
          List.sum_nil, add_zero] at one
        have byy := boolCert_sound sat hy
        simp only [Scalar.Circuit.ArithExpr.denote, one]
        rcases byy with byy | byy <;> simp [byy]

theorem substVar_denote (v : Var) (k : F) (w : Var → F) (at_ : w v = k) :
    ∀ e : ArithExpr F, (substVar v k e).denote w = e.denote w
  | .const _ => rfl
  | .var u => by
      by_cases h : u = v
      · subst h; simp [substVar, Scalar.Circuit.ArithExpr.denote, at_]
      · simp [substVar, h, Scalar.Circuit.ArithExpr.denote]
  | .add x y => by simp [substVar, Scalar.Circuit.ArithExpr.denote, substVar_denote v k w at_ x,
      substVar_denote v k w at_ y]
  | .sub x y => by simp [substVar, Scalar.Circuit.ArithExpr.denote, substVar_denote v k w at_ x,
      substVar_denote v k w at_ y]
  | .mul x y => by simp [substVar, Scalar.Circuit.ArithExpr.denote, substVar_denote v k w at_ x,
      substVar_denote v k w at_ y]

theorem addVars_denote {w : Var → F} :
    ∀ {e : ArithExpr F} {I : List Var}, addVars e = some I → e.denote w = (I.map w).sum
  | .var v, I, h => by
      simp only [addVars, Option.some.injEq] at h
      subst h; simp [Scalar.Circuit.ArithExpr.denote]
  | .add x y, I, h => by
      simp only [addVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      simp [Scalar.Circuit.ArithExpr.denote, addVars_denote ha, addVars_denote hb]
  | .const _, _, h => by simp [addVars] at h
  | .sub _ _, _, h => by simp [addVars] at h
  | .mul _ _, _, h => by simp [addVars] at h

theorem sumExpr_denote (w : Var → F) (vs : List Var) : (sumExpr vs).denote w = (vs.map w).sum := by
  induction vs with
  | nil => simp [sumExpr, Scalar.Circuit.ArithExpr.denote]
  | cons v vs ih =>
      simp only [sumExpr, List.foldr_cons] at ih ⊢
      simp [Scalar.Circuit.ArithExpr.denote, ih]

/-- A sum of `0`/`1` values over a finset is the number of ones. -/
theorem finset_sum_bits {S : Finset Var} {w : Var → F} (bits : ∀ j ∈ S, w j = 0 ∨ w j = 1) :
    ∑ j ∈ S, w j = ((S.filter fun j => w j = 1).card : F) := by
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rcases bits j hj with h | h <;> simp [h]

theorem boolSum_sound {cs : List (ArithExpr F)} {bound : Nat} {e : ArithExpr F} {w : Var → F}
    (small : SmallCast F bound) (h : boolSum cs bound e = true) (sat : Scalar.Circuit.Satisfies cs w) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  unfold boolSum at h
  cases hI : addVars e with
  | none => simp [hI] at h
  | some I =>
    simp only [hI, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.all_eq_true] at h
    obtain ⟨nodupI, c, _, ⟨⟨sub, bitsJ⟩, sumJ⟩, short⟩ := h
    set J := (varsOf c).dedup
    have nodupJ : J.Nodup := List.nodup_dedup _
    have bits : ∀ j ∈ J.toFinset, w j = 0 ∨ w j = 1 := fun j hj => by
      have := boolDirect_sound (bitsJ j (List.mem_toFinset.mp hj)) sat
      simpa [Scalar.Circuit.ArithExpr.denote] using this
    have total := boolDirect_sound sumJ sat
    rw [sumExpr_denote, ← List.sum_toFinset _ nodupJ, finset_sum_bits bits] at total
    set k := (J.toFinset.filter fun j => w j = 1).card
    have kle : k ≤ J.length :=
      (Finset.card_filter_le _ _).trans (List.toFinset_card_le J)
    have kOne : k ≤ 1 := by
      rcases total with t | t
      · have := small k (by omega) t; omega
      · by_contra big
        have : ((k - 1 : Nat) : F) = 0 := by
          rw [Nat.cast_sub (by omega), t]; simp
        have := small (k - 1) (by omega) this
        omega
    have subset : I.toFinset ⊆ J.toFinset := fun i hi =>
      List.mem_toFinset.mpr (sub i (List.mem_toFinset.mp hi))
    have bitsI : ∀ i ∈ I.toFinset, w i = 0 ∨ w i = 1 := fun i hi => bits i (subset hi)
    rw [addVars_denote hI, ← List.sum_toFinset _ nodupI, finset_sum_bits bitsI]
    have le : (I.toFinset.filter fun j => w j = 1).card ≤ k :=
      Finset.card_le_card (Finset.filter_subset_filter _ subset)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (le.trans kOne) with h0 | h1
    · left; rw [h0]; simp
    · right; rw [h1]; simp

theorem boolLinear_sound {cs : List (ArithExpr F)} {bound : Nat} {e : ArithExpr F} {w : Var → F}
    (small : SmallCast F bound) (h : boolLinear cs bound e = true) (sat : Scalar.Circuit.Satisfies cs w) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  change Scalar.Circuit.ArithExpr.denote w e = 0 ∨ Scalar.Circuit.ArithExpr.denote w e = 1
  simp only [boolLinear, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨_, sum⟩, same | compl⟩ := h
  · have := Poly.Identical.denote w same
    rw [Poly.denote_ofExpr, Poly.denote_ofExpr] at this
    rw [this]
    exact boolSum_sound small sum sat
  · have := Poly.Identical.denote w compl
    rw [Poly.denote_ofExpr, Poly.denote_ofExpr] at this
    rw [this]
    simp only [Scalar.Circuit.ArithExpr.denote]
    rcases boolSum_sound small sum sat with b | b <;> simp [b]

theorem denote_congr_vars {w a : Var → F} :
    ∀ (x : ArithExpr F), (∀ v ∈ varsOf x, w v = a v) →
      Scalar.Circuit.ArithExpr.denote w x = Scalar.Circuit.ArithExpr.denote a x
  | .const _, _ => rfl
  | .var v, h => by simp [Scalar.Circuit.ArithExpr.denote, h v (by simp [varsOf])]
  | .add x y, h => by
      simp only [Scalar.Circuit.ArithExpr.denote]
      rw [denote_congr_vars x fun v hv => h v (by simp [varsOf, hv]),
        denote_congr_vars y fun v hv => h v (by simp [varsOf, hv])]
  | .sub x y, h => by
      simp only [Scalar.Circuit.ArithExpr.denote]
      rw [denote_congr_vars x fun v hv => h v (by simp [varsOf, hv]),
        denote_congr_vars y fun v hv => h v (by simp [varsOf, hv])]
  | .mul x y, h => by
      simp only [Scalar.Circuit.ArithExpr.denote]
      rw [denote_congr_vars x fun v hv => h v (by simp [varsOf, hv]),
        denote_congr_vars y fun v hv => h v (by simp [varsOf, hv])]

theorem boolEnum_sound {cs : List (ArithExpr F)} {e : ArithExpr F} {w : Var → F}
    (h : boolEnum cs e = true) (sat : Scalar.Circuit.Satisfies cs w) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  change Scalar.Circuit.ArithExpr.denote w e = 0 ∨ Scalar.Circuit.ArithExpr.denote w e = 1
  simp only [boolEnum, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, inV⟩, cases⟩ := h
  set V := boolVars cs e
  have bits : ∀ v ∈ V, w v = 0 ∨ w v = 1 := by
    intro v hv
    have hb : boolDirect cs (.var v) = true := (List.mem_filter.mp hv).2
    simpa [Scalar.Circuit.ArithExpr.denote] using boolDirect_sound hb sat
  set S := V.filter fun v => decide (w v = 1)
  have agree : ∀ v ∈ V, w v = indicator S v := by
    intro v hv
    simp only [indicator, S, List.mem_filter, decide_eq_true_eq]
    rcases bits v hv with h0 | h1
    · have : ¬ w v = 1 := by rw [h0]; exact zero_ne_one
      simp [h0]
    · simp [hv, h1]
  have hS := cases S (List.mem_sublists.mpr (List.filter_sublist))
  have congrE := denote_congr_vars e fun v hv => agree v (inV v hv)
  rw [congrE]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hS
  rcases hS with (hC | h0) | h1
  · exfalso
    have : (cs.filter fun c => (varsOf c).all (· ∈ V)).all
        (fun c => decide (Scalar.Circuit.ArithExpr.denote (indicator S) c = 0)) = true := by
      apply List.all_eq_true.mpr
      intro c hc
      have hc' := List.mem_filter.mp hc
      have allV : ∀ v ∈ varsOf c, v ∈ V := by
        simpa [List.all_eq_true] using hc'.2
      rw [decide_eq_true_eq, ← denote_congr_vars c fun v hv => agree v (allV v hv)]
      exact sat c hc'.1
    rw [this] at hC
    exact Bool.false_ne_true hC.symm
  · exact Or.inl h0
  · exact Or.inr h1

theorem boolAny_sound {cs : List (ArithExpr F)} {bound : Nat} {e : ArithExpr F} {w : Var → F}
    (small : SmallCast F bound) (h : boolAny cs bound e = true) (sat : Scalar.Circuit.Satisfies cs w) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  simp only [boolAny, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact boolCert_sound sat h
  · exact boolSum_sound small h sat
  · exact boolLinear_sound small h sat
  · exact boolEnum_sound h sat

theorem boolCertAt_sound {cs : List (ArithExpr F)} {bound : Nat} {sel : Var} {e : ArithExpr F}
    {w : Var → F} (small : SmallCast F bound) (h : boolCertAt cs bound sel e = true)
    (sat : Scalar.Circuit.Satisfies cs w) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  simp only [boolCertAt, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨⟨c, hc, silent⟩, h⟩
  · exact boolAny_sound small h sat
  · by_cases on : w sel = 1
    · rw [← substVar_denote sel 1 w on e]
      exact boolAny_sound small h sat
    · left
      have := Poly.Identical.denote w silent
      rw [Poly.denote_ofExpr, Poly.denote_ofExpr, sat c hc] at this
      simp only [Scalar.Circuit.ArithExpr.denote] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (sub_ne_zero.mpr (Ne.symm on))

/-- `checkEnables` discharges `Boolean` on every row satisfying the activated
chip's constraints. -/
theorem boolean_of_checkEnables {bound : Nat} (small : SmallCast F bound) {c : Chip F}
    (ok : checkEnables bound c = true) {w : Var → F}
    (sat : Scalar.Circuit.Satisfies (Activation.compile c).constraints w) : Boolean c w := by
  simp only [checkEnables, Bool.and_eq_true, List.all_eq_true] at ok
  exact ⟨fun s hs => boolCertAt_sound small (ok.1 s hs) sat,
    fun m hm => boolCertAt_sound small (ok.2 m hm) sat⟩

/-! ## Fast, complete exporter enable checker

Checks booleanity directly on the unactivated chip `c`, before
`Activation.compile` threads the row selector through every constant-bearing
constraint. On inactive rows (`w c.numVars = 0`), `Activation.compile`'s silence
guards force every send and memory enable to `0`; on active rows (`w c.numVars = 1`),
every activated constraint and enable evaluates identically to `c`'s own.

The checker extracts directly boolean variables from degree-≤-2 univariate
constraints, reads forced zeros (including `S·(S + 1) = 0`) and pairwise
exclusions from uniform affine linear/product constraints, handles arbitrary-size
mutually exclusive affine sums directly, and falls back to fuel-bounded,
early-pruned branch-and-bound search over closed boolean neighborhoods. -/

section FastEnables

/-- Syntactic degree upper bound of an arithmetic expression. -/
def exprDegree : ArithExpr F → Nat
  | .const _ => 0
  | .var _ => 1
  | .add x y | .sub x y => max (exprDegree x) (exprDegree y)
  | .mul x y => exprDegree x + exprDegree y

/-- Extract coefficients `(c0, c1, c2)` of a polynomial that is at most quadratic
in the single variable `v`. -/
def extractQuad (v : Var) : Poly F → Option (F × F × F)
  | [] => some (0, 0, 0)
  | (m, k) :: rest => do
      let (c0, c1, c2) ← extractQuad v rest
      if m == [] then some (c0 + k, c1, c2)
      else if m == [v] then some (c0, c1 + k, c2)
      else if m == [v, v] then some (c0, c1, c2 + k)
      else none

theorem extractQuad_denote {v : Var} :
    ∀ {p : Poly F} {c0 c1 c2 : F},
      extractQuad v p = some (c0, c1, c2) →
      ∀ w : Var → F, p.denote w = c0 + c1 * w v + c2 * (w v * w v)
  | [], c0, c1, c2, h, w => by
      simp only [extractQuad, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [Poly.denote]
  | (m, k) :: rest, c0, c1, c2, h, w => by
      simp only [extractQuad, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨r0, r1, r2⟩, hr, hstep⟩ := h
      have ih := extractQuad_denote hr w
      rw [Poly.denote_cons, ih]
      by_cases hm0 : m == []
      · simp only [hm0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        have hm : m = [] := beq_iff_eq.mp hm0
        subst hm
        simp only [Mono.eval_nil, mul_one]
        ring
      · simp only [hm0, Bool.false_eq_true, ↓reduceIte] at hstep
        by_cases hm1 : m == [v]
        · simp only [hm1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl, rfl⟩ := hstep
          have hm : m = [v] := beq_iff_eq.mp hm1
          subst hm
          simp only [Mono.eval_cons, Mono.eval_nil, mul_one]
          ring
        · simp only [hm1, Bool.false_eq_true, ↓reduceIte] at hstep
          by_cases hm2 : m == [v, v]
          · simp only [hm2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl, rfl⟩ := hstep
            have hm : m = [v, v] := beq_iff_eq.mp hm2
            subst hm
            simp only [Mono.eval_cons, Mono.eval_nil, mul_one]
            ring
          · simp only [hm2, Bool.false_eq_true, ↓reduceIte] at hstep
            cases hstep

/-- Whether `c0 + c1·x + c2·x² = 0` forces `x ∈ {0, 1}` (or is unsatisfiable). -/
def forcesBoolQuad (c0 c1 c2 : F) : Bool :=
  if c2 != 0 then c0 == 0 && c2 + c1 == 0
  else if c1 != 0 then c0 == 0 || c1 + c0 == 0
  else c0 != 0

theorem forcesBoolQuad_sound {c0 c1 c2 x : F}
    (hf : forcesBoolQuad c0 c1 c2 = true) (hz : c0 + c1 * x + c2 * (x * x) = 0) :
    x = 0 ∨ x = 1 := by
  unfold forcesBoolQuad at hf
  by_cases h2 : c2 = 0
  · subst h2
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hf hz
    by_cases h1 : c1 = 0
    · subst h1
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq,
        zero_mul, add_zero] at hf hz
      exact False.elim (hf hz)
    · have h1b : (c1 != 0) = true := bne_iff_ne.mpr h1
      simp only [h1b, ↓reduceIte, Bool.or_eq_true, beq_iff_eq] at hf
      rcases hf with rfl | hsum
      · rw [zero_add] at hz
        exact Or.inl ((mul_eq_zero.mp hz).resolve_left h1)
      · have h0 : c0 = -c1 := eq_neg_of_add_eq_zero_right hsum
        rw [h0] at hz
        have : c1 * (x - 1) = 0 := by linear_combination hz
        exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h1))
  · have h2b : (c2 != 0) = true := bne_iff_ne.mpr h2
    simp only [h2b, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, hsum⟩ := hf
    have h1 : c1 = -c2 := eq_neg_of_add_eq_zero_right hsum
    rw [h1] at hz
    have : c2 * (x * (x - 1)) = 0 := by linear_combination hz
    have hprod := (mul_eq_zero.mp this).resolve_left h2
    rcases mul_eq_zero.mp hprod with hx0 | hx1
    · exact Or.inl hx0
    · exact Or.inr (sub_eq_zero.mp hx1)

/-- If a univariate constraint of degree at most 3 forces its sole variable into
`{0, 1}`, return that variable. -/
def univarBoolVar (c : ArithExpr F) : Option Var :=
  match (varsOf c).dedup with
  | [v] =>
      if exprDegree c ≤ 3 then
        match extractQuad v (Poly.norm (Poly.ofExpr c)) with
        | some (c0, c1, c2) => if forcesBoolQuad c0 c1 c2 then some v else none
        | none => none
      else none
  | _ => none

theorem univarBoolVar_sound {c : ArithExpr F} {v : Var} {w : Var → F}
    (h : univarBoolVar c = some v) (hc : c.denote w = 0) :
    w v = 0 ∨ w v = 1 := by
  unfold univarBoolVar at h
  cases hd : (varsOf c).dedup with
  | nil => simp [hd] at h
  | cons u rest =>
    cases rest with
    | cons _ _ => simp [hd] at h
    | nil =>
      simp only [hd] at h
      split at h
      · cases hq : extractQuad u (Poly.norm (Poly.ofExpr c)) with
        | none => simp [hq] at h
        | some triple =>
          rcases triple with ⟨c0, c1, c2⟩
          simp only [hq] at h
          split at h
          · rename_i hf
            simp only [Option.some.injEq] at h
            subst h
            have hden := extractQuad_denote hq w
            rw [Poly.denote_norm, Poly.denote_ofExpr] at hden
            change c.denote w = _ at hden
            rw [hc] at hden
            exact forcesBoolQuad_sound hf hden.symm
          · cases h
      · cases h

/-- Insert `k · v` into a sorted, merged affine term list, dropping zeros. -/
def insertCoeff (v : Var) (k : F) : List (Var × F) → List (Var × F)
  | [] => if k = 0 then [] else [(v, k)]
  | (u, c) :: rest =>
      if v = u then
        if k + c = 0 then rest else (u, k + c) :: rest
      else if v < u then
        if k = 0 then (u, c) :: rest else (v, k) :: (u, c) :: rest
      else (u, c) :: insertCoeff v k rest

/-- Denotation of an affine form `(terms, const)`. -/
def affineDenote (w : Var → F) (a : List (Var × F) × F) : F :=
  (a.1.map fun t => t.2 * w t.1).sum + a.2

theorem insertCoeff_denote (w : Var → F) (v : Var) (k : F) :
    ∀ ts : List (Var × F),
      ((insertCoeff v k ts).map fun t => t.2 * w t.1).sum =
        k * w v + (ts.map fun t => t.2 * w t.1).sum
  | [] => by
      unfold insertCoeff
      split <;> simp [*]
  | (u, c) :: rest => by
      unfold insertCoeff
      split
      · rename_i hvu
        subst hvu
        split
        · rename_i hsum
          simp only [List.map_cons, List.sum_cons]
          have : k * w v + c * w v = 0 := by rw [← add_mul, hsum, zero_mul]
          linear_combination -this
        · simp only [List.map_cons, List.sum_cons]
          ring
      · split
        · split
          · rename_i hk0
            subst hk0
            simp
          · simp only [List.map_cons, List.sum_cons]
        · simp only [List.map_cons, List.sum_cons, insertCoeff_denote w v k rest]
          ring

def affineAdd (a b : List (Var × F) × F) : List (Var × F) × F :=
  (b.1.foldr (fun t acc => insertCoeff t.1 t.2 acc) a.1, a.2 + b.2)

def affineScale (s : F) (a : List (Var × F) × F) : List (Var × F) × F :=
  if s = 0 then ([], 0)
  else (a.1.map fun t => (t.1, s * t.2), s * a.2)

theorem affineAdd_denote (w : Var → F) (a b : List (Var × F) × F) :
    affineDenote w (affineAdd a b) = affineDenote w a + affineDenote w b := by
  unfold affineDenote affineAdd
  suffices ∀ ts : List (Var × F),
      ((ts.foldr (fun t acc => insertCoeff t.1 t.2 acc) a.1).map fun t => t.2 * w t.1).sum =
        (ts.map fun t => t.2 * w t.1).sum + (a.1.map fun t => t.2 * w t.1).sum by
    rw [this b.1]; ring
  intro ts
  induction ts with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, insertCoeff_denote, ih]
      ring

theorem affineScale_denote (w : Var → F) (s : F) (a : List (Var × F) × F) :
    affineDenote w (affineScale s a) = s * affineDenote w a := by
  unfold affineDenote affineScale
  split
  · rename_i hs; subst hs; simp
  · suffices ∀ ts : List (Var × F),
        ((ts.map fun t => (t.1, s * t.2)).map fun t => t.2 * w t.1).sum =
          s * (ts.map fun t => t.2 * w t.1).sum by
      rw [this a.1]; ring
    intro ts
    induction ts with
    | nil => simp
    | cons t rest ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring

/-- Extract the exact affine form of `e` if it is affine. -/
def affineOf : ArithExpr F → Option (List (Var × F) × F)
  | .const c => some ([], c)
  | .var v => some ([(v, 1)], 0)
  | .add x y => do return affineAdd (← affineOf x) (← affineOf y)
  | .sub x y => do return affineAdd (← affineOf x) (affineScale (-1) (← affineOf y))
  | .mul x y => do
      let ax ← affineOf x
      let ay ← affineOf y
      if ax.1.isEmpty then some (affineScale ax.2 ay)
      else if ay.1.isEmpty then some (affineScale ay.2 ax)
      else none

theorem affineOf_denote (w : Var → F) :
    ∀ {e : ArithExpr F} {a : List (Var × F) × F},
      affineOf e = some a → e.denote w = affineDenote w a
  | .const c, a, h => by
      simp only [affineOf, Option.some.injEq] at h
      subst h; simp [Scalar.Circuit.ArithExpr.denote, affineDenote]
  | .var v, a, h => by
      simp only [affineOf, Option.some.injEq] at h
      subst h; simp [Scalar.Circuit.ArithExpr.denote, affineDenote]
  | .add x y, a, h => by
      simp only [affineOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ax, hx, ay, hy, rfl⟩ := h
      simp [Scalar.Circuit.ArithExpr.denote, affineOf_denote w hx, affineOf_denote w hy,
        affineAdd_denote]
  | .sub x y, a, h => by
      simp only [affineOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ax, hx, ay, hy, rfl⟩ := h
      simp only [Scalar.Circuit.ArithExpr.denote, affineOf_denote w hx, affineOf_denote w hy,
        affineAdd_denote, affineScale_denote]
      ring
  | .mul x y, a, h => by
      simp only [affineOf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ax, hx, ay, hy, hstep⟩ := h
      have hdx := affineOf_denote w hx
      have hdy := affineOf_denote w hy
      simp only [Scalar.Circuit.ArithExpr.denote, hdx, hdy]
      split at hstep
      · rename_i hempty
        simp only [Option.some.injEq] at hstep
        subst hstep
        have hnil : ax.1 = [] := List.isEmpty_iff.mp hempty
        rw [affineScale_denote]
        simp [affineDenote, hnil]
      · split at hstep
        · rename_i hempty
          simp only [Option.some.injEq] at hstep
          subst hstep
          have hnil : ay.1 = [] := List.isEmpty_iff.mp hempty
          rw [affineScale_denote]
          simp [affineDenote, hnil, mul_comm]
        · cases hstep

/-- Check whether a list of variables is strictly ascending (hence duplicate-free). -/
def isStrictAsc : List Var → Bool
  | [] | [_] => true
  | x :: y :: rest => decide (x < y) && isStrictAsc (y :: rest)

theorem isStrictAsc_gt_all {x : Var} :
    ∀ {xs : List Var}, isStrictAsc (x :: xs) = true → ∀ y ∈ xs, x < y
  | [], _, _, hy => by cases hy
  | z :: rest, h, y, hy => by
      simp only [isStrictAsc, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h.1
      · exact Nat.lt_trans h.1 (isStrictAsc_gt_all h.2 y hy')

theorem isStrictAsc_nodup : ∀ {xs : List Var}, isStrictAsc xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | x :: y :: rest, h => by
      have hgt := isStrictAsc_gt_all h
      simp only [isStrictAsc, Bool.and_eq_true, decide_eq_true_eq] at h
      exact List.nodup_cons.mpr ⟨fun hx => Nat.lt_irrefl x (hgt x hx), isStrictAsc_nodup h.2⟩

/-- For a nonempty uniform affine form `k·Σ_A x + c` with distinct variables `A`,
return `(A, -c / k)` where `Σ_A x = -c / k` iff the form vanishes. -/
def uniformOf (a : List (Var × F) × F) : Option (List Var × F) :=
  match a.1 with
  | [] => none
  | (_, k) :: rest =>
      let vs := a.1.map Prod.fst
      if k != 0 && rest.all (fun t => t.2 == k) && isStrictAsc vs then
        some (vs, -a.2 * k⁻¹)
      else none

theorem uniformOf_sound {a : List (Var × F) × F} {vs : List Var} {r : F}
    (h : uniformOf a = some (vs, r)) :
    vs.Nodup ∧ ∀ w : Var → F, affineDenote w a = 0 → (vs.map w).sum = r := by
  unfold uniformOf at h
  cases ha : a.1 with
  | nil => simp [ha] at h
  | cons hd rest =>
    rcases hd with ⟨v0, k⟩
    simp only [ha] at h
    split at h
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨hk, hall⟩, hasc⟩ := hcond
      refine ⟨isStrictAsc_nodup hasc, fun w hzero => ?_⟩
      unfold affineDenote at hzero
      rw [ha] at hzero
      have hfactor : ∀ ts : List (Var × F), (∀ t ∈ ts, t.2 = k) →
          (ts.map fun t => t.2 * w t.1).sum = k * ((ts.map Prod.fst).map w).sum := by
        intro ts hts
        induction ts with
        | nil => simp
        | cons t tl ih =>
            have htk : t.2 = k := hts t (List.mem_cons_self ..)
            have htl := ih (fun x hx => hts x (List.mem_cons_of_mem _ hx))
            simp only [List.map_cons, List.sum_cons, htk, htl, mul_add]
      have hsum := hfactor ((v0, k) :: rest) fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht'
        · rfl
        · exact hall t ht'
      rw [hsum] at hzero
      have hmul : k * (((v0, k) :: rest).map Prod.fst |>.map w).sum = -a.2 :=
        eq_neg_of_add_eq_zero_left hzero
      have := congrArg (· * k⁻¹) hmul
      rw [mul_comm k, mul_assoc, mul_inv_cancel₀ hk, mul_one] at this
      exact this
    · cases h

/-- Strip leading negations and nonzero constant factors without changing the zero set. -/
def peelScale : ArithExpr F → ArithExpr F
  | .sub (.const c) x => if c == 0 then peelScale x else .sub (.const c) x
  | .mul (.const k) x => if k != 0 then peelScale x else .mul (.const k) x
  | .mul x (.const k) => if k != 0 then peelScale x else .mul x (.const k)
  | e => e

theorem peelScale_zero_iff (w : Var → F) :
    ∀ e : ArithExpr F, (peelScale e).denote w = 0 → e.denote w = 0
  | .const _ => id
  | .var _ => id
  | .add _ _ => id
  | .sub (.const c) x => by
      unfold peelScale
      split
      · rename_i hc
        have hc0 : c = 0 := beq_iff_eq.mp hc
        intro h
        have hx := peelScale_zero_iff w x h
        simp [Scalar.Circuit.ArithExpr.denote, hc0, hx]
      · exact id
  | .sub (.var _) _ => id
  | .sub (.add _ _) _ => id
  | .sub (.sub _ _) _ => id
  | .sub (.mul _ _) _ => id
  | .mul (.const k) x => by
      unfold peelScale
      split
      · intro h
        have hx := peelScale_zero_iff w x h
        simp [Scalar.Circuit.ArithExpr.denote, hx]
      · exact id
  | .mul (.var v) (.const k) => by
      unfold peelScale
      split
      · intro h
        have hx := peelScale_zero_iff w (.var v) h
        simp [Scalar.Circuit.ArithExpr.denote] at hx ⊢
        simp [hx]
      · exact id
  | .mul (.add a b) (.const k) => by
      unfold peelScale
      split
      · intro h
        have hx := peelScale_zero_iff w (.add a b) h
        change ArithExpr.denote w (.add a b) * k = 0
        rw [hx, zero_mul]
      · exact id
  | .mul (.sub a b) (.const k) => by
      unfold peelScale
      split
      · intro h
        have hx := peelScale_zero_iff w (.sub a b) h
        change ArithExpr.denote w (.sub a b) * k = 0
        rw [hx, zero_mul]
      · exact id
  | .mul (.mul a b) (.const k) => by
      unfold peelScale
      split
      · intro h
        have hx := peelScale_zero_iff w (.mul a b) h
        change ArithExpr.denote w (.mul a b) * k = 0
        rw [hx, zero_mul]
      · exact id
  | .mul (.var _) (.var _) => id
  | .mul (.var _) (.add _ _) => id
  | .mul (.var _) (.sub _ _) => id
  | .mul (.var _) (.mul _ _) => id
  | .mul (.add _ _) (.var _) => id
  | .mul (.add _ _) (.add _ _) => id
  | .mul (.add _ _) (.sub _ _) => id
  | .mul (.add _ _) (.mul _ _) => id
  | .mul (.sub _ _) (.var _) => id
  | .mul (.sub _ _) (.add _ _) => id
  | .mul (.sub _ _) (.sub _ _) => id
  | .mul (.sub _ _) (.mul _ _) => id
  | .mul (.mul _ _) (.var _) => id
  | .mul (.mul _ _) (.add _ _) => id
  | .mul (.mul _ _) (.sub _ _) => id
  | .mul (.mul _ _) (.mul _ _) => id

theorem peelScale_of_zero (w : Var → F) :
    ∀ e : ArithExpr F, e.denote w = 0 → (peelScale e).denote w = 0
  | .const _ => id
  | .var _ => id
  | .add _ _ => id
  | .sub (.const c) x => by
      unfold peelScale
      split
      · rename_i hc
        have hc0 : c = 0 := beq_iff_eq.mp hc
        intro h
        simp only [Scalar.Circuit.ArithExpr.denote, hc0, zero_sub, neg_eq_zero] at h
        exact peelScale_of_zero w x h
      · exact id
  | .sub (.var _) _ => id
  | .sub (.add _ _) _ => id
  | .sub (.sub _ _) _ => id
  | .sub (.mul _ _) _ => id
  | .mul (.const k) x => by
      unfold peelScale
      split
      · rename_i hk
        have hk0 : k ≠ 0 := bne_iff_ne.mp hk
        intro h
        simp only [Scalar.Circuit.ArithExpr.denote] at h
        exact peelScale_of_zero w x ((mul_eq_zero.mp h).resolve_left hk0)
      · exact id
  | .mul (.var v) (.const k) => by
      unfold peelScale
      split
      · rename_i hk
        have hk0 : k ≠ 0 := bne_iff_ne.mp hk
        intro h
        simp only [Scalar.Circuit.ArithExpr.denote] at h
        exact peelScale_of_zero w (.var v) ((mul_eq_zero.mp h).resolve_right hk0)
      · exact id
  | .mul (.add a b) (.const k) => by
      unfold peelScale
      split
      · rename_i hk
        have hk0 : k ≠ 0 := bne_iff_ne.mp hk
        intro h
        simp only [Scalar.Circuit.ArithExpr.denote] at h
        exact peelScale_of_zero w (.add a b) ((mul_eq_zero.mp h).resolve_right hk0)
      · exact id
  | .mul (.sub a b) (.const k) => by
      unfold peelScale
      split
      · rename_i hk
        have hk0 : k ≠ 0 := bne_iff_ne.mp hk
        intro h
        simp only [Scalar.Circuit.ArithExpr.denote] at h
        exact peelScale_of_zero w (.sub a b) ((mul_eq_zero.mp h).resolve_right hk0)
      · exact id
  | .mul (.mul a b) (.const k) => by
      unfold peelScale
      split
      · rename_i hk
        have hk0 : k ≠ 0 := bne_iff_ne.mp hk
        intro h
        simp only [Scalar.Circuit.ArithExpr.denote] at h
        exact peelScale_of_zero w (.mul a b) ((mul_eq_zero.mp h).resolve_right hk0)
      · exact id
  | .mul (.var _) (.var _) => id
  | .mul (.var _) (.add _ _) => id
  | .mul (.var _) (.sub _ _) => id
  | .mul (.var _) (.mul _ _) => id
  | .mul (.add _ _) (.var _) => id
  | .mul (.add _ _) (.add _ _) => id
  | .mul (.add _ _) (.sub _ _) => id
  | .mul (.add _ _) (.mul _ _) => id
  | .mul (.sub _ _) (.var _) => id
  | .mul (.sub _ _) (.add _ _) => id
  | .mul (.sub _ _) (.sub _ _) => id
  | .mul (.sub _ _) (.mul _ _) => id
  | .mul (.mul _ _) (.var _) => id
  | .mul (.mul _ _) (.add _ _) => id
  | .mul (.mul _ _) (.sub _ _) => id
  | .mul (.mul _ _) (.mul _ _) => id

/-- True when no integer `m ∈ [start, start + len)` casts to `r` in `F`.
This requires no external `SmallCast` bound and is unconditionally sound in every field. -/
def noRootFrom (start len : Nat) (r : F) : Bool :=
  (List.range' start len).all fun m => (m : F) != r

theorem noRootFrom_spec {start len m : Nat} {r : F}
    (h : noRootFrom start len r = true) (hlo : start ≤ m) (hhi : m < start + len) :
    (m : F) ≠ r := by
  unfold noRootFrom at h
  have hmem : m ∈ List.range' start len := by
    rw [List.mem_range'_1]
    exact ⟨hlo, hhi⟩
  exact bne_iff_ne.mp ((List.all_eq_true.mp h) m hmem)

theorem sum_eq_card_bits {vs : List Var} {w : Var → F}
    (hnd : vs.Nodup) (hbits : ∀ v ∈ vs, w v = 0 ∨ w v = 1) :
    (vs.map w).sum = ((vs.toFinset.filter fun v => w v = 1).card : F) ∧
      (vs.toFinset.filter fun v => w v = 1).card ≤ vs.length := by
  have hbf : ∀ v ∈ vs.toFinset, w v = 0 ∨ w v = 1 :=
    fun v hv => hbits v (List.mem_toFinset.mp hv)
  refine ⟨?_, (Finset.card_filter_le _ _).trans (List.toFinset_card_le vs)⟩
  rw [← List.sum_toFinset _ hnd, finset_sum_bits hbf]

theorem sum_ne_of_one_mem {vs : List Var} {w : Var → F} {r : F} {x : Var}
    (hnd : vs.Nodup) (hbits : ∀ v ∈ vs, w v = 0 ∨ w v = 1)
    (hno : noRootFrom 1 vs.length r = true) (hx : x ∈ vs) (hx1 : w x = 1) :
    (vs.map w).sum ≠ r := by
  obtain ⟨hsum, hle⟩ := sum_eq_card_bits hnd hbits
  rw [hsum]
  have hmem : x ∈ vs.toFinset.filter (fun v => w v = 1) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hx, hx1⟩
  have hpos : 1 ≤ (vs.toFinset.filter fun v => w v = 1).card :=
    Finset.one_le_card.mpr ⟨x, hmem⟩
  exact noRootFrom_spec hno hpos (by omega)

theorem sum_ne_of_two_mem {vs : List Var} {w : Var → F} {r : F} {x y : Var}
    (hnd : vs.Nodup) (hbits : ∀ v ∈ vs, w v = 0 ∨ w v = 1)
    (hno : noRootFrom 2 (vs.length - 1) r = true)
    (hx : x ∈ vs) (hy : y ∈ vs) (hne : x ≠ y) (hx1 : w x = 1) (hy1 : w y = 1) :
    (vs.map w).sum ≠ r := by
  obtain ⟨hsum, hle⟩ := sum_eq_card_bits hnd hbits
  rw [hsum]
  have hmx : x ∈ vs.toFinset.filter (fun v => w v = 1) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hx, hx1⟩
  have hmy : y ∈ vs.toFinset.filter (fun v => w v = 1) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hy, hy1⟩
  have htwo : 2 ≤ (vs.toFinset.filter fun v => w v = 1).card :=
    Finset.one_lt_card.mpr ⟨x, hmx, y, hmy, hne⟩
  exact noRootFrom_spec hno htwo (by omega)

/-- Soundness invariants on the precomputed per-chip fact tables. -/
def BoolSound (w : Var → F) (S : Std.HashSet Var) : Prop :=
  ∀ v, S.contains v = true → w v = 0 ∨ w v = 1

def ForcedSound (w : Var → F) (S : Std.HashSet Var) : Prop :=
  ∀ v, S.contains v = true → w v = 0

def ExclSound (w : Var → F) (S : Std.HashSet (Var × Var)) : Prop :=
  ∀ x y, S.contains (x, y) = true → ¬ (w x = 1 ∧ w y = 1)

theorem boolSound_empty (w : Var → F) : BoolSound w {} := by
  intro v hv; simp at hv

theorem forcedSound_empty (w : Var → F) : ForcedSound w {} := by
  intro v hv; simp at hv

theorem exclSound_empty (w : Var → F) : ExclSound w {} := by
  intro x y hxy; simp at hxy

theorem boolSound_insert {w : Var → F} {S : Std.HashSet Var} {v : Var}
    (hS : BoolSound w S) (hv : w v = 0 ∨ w v = 1) : BoolSound w (S.insert v) := by
  intro u hu
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hu
  rcases hu with rfl | hu'
  · exact hv
  · exact hS u hu'

theorem forcedSound_insert {w : Var → F} {S : Std.HashSet Var} {v : Var}
    (hS : ForcedSound w S) (hv : w v = 0) : ForcedSound w (S.insert v) := by
  intro u hu
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hu
  rcases hu with rfl | hu'
  · exact hv
  · exact hS u hu'

theorem exclSound_insert {w : Var → F} {S : Std.HashSet (Var × Var)} {x y : Var}
    (hS : ExclSound w S) (hxy : ¬ (w x = 1 ∧ w y = 1)) : ExclSound w (S.insert (x, y)) := by
  intro a b hab
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | hab'
  · exact hxy
  · exact hS a b hab'

def insertAllVars (S : Std.HashSet Var) (vs : List Var) : Std.HashSet Var :=
  vs.foldl (fun acc v => acc.insert v) S

theorem forcedSound_insertAllVars {w : Var → F} {S : Std.HashSet Var} {vs : List Var}
    (hS : ForcedSound w S) (hvs : ∀ v ∈ vs, w v = 0) :
    ForcedSound w (insertAllVars S vs) := by
  unfold insertAllVars
  induction vs generalizing S with
  | nil => exact hS
  | cons v rest ih =>
      exact ih (forcedSound_insert hS (hvs v (List.mem_cons_self ..)))
        (fun u hu => hvs u (List.mem_cons_of_mem _ hu))

def insertAllPairs (S : Std.HashSet (Var × Var)) (xs ys : List Var) : Std.HashSet (Var × Var) :=
  xs.foldl (fun acc x =>
    ys.foldl (fun acc2 y =>
      if x != y then (acc2.insert (x, y)).insert (y, x) else acc2) acc) S

theorem exclSound_insertAllPairs {w : Var → F} {S : Std.HashSet (Var × Var)} {xs ys : List Var}
    (hS : ExclSound w S) (hxy : ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y → ¬ (w x = 1 ∧ w y = 1)) :
    ExclSound w (insertAllPairs S xs ys) := by
  have inner : ∀ (x : Var) (zs : List Var) (T : Std.HashSet (Var × Var)),
      ExclSound w T → (∀ y ∈ zs, x ≠ y → ¬ (w x = 1 ∧ w y = 1)) →
      ExclSound w (zs.foldl (fun acc2 y =>
        if x != y then (acc2.insert (x, y)).insert (y, x) else acc2) T) := by
    intro x zs
    induction zs with
    | nil => intro T hT _; exact hT
    | cons y zs' ihy =>
        intro T hT hx
        apply ihy
        · dsimp only
          split
          · rename_i hne
            have hne' : x ≠ y := bne_iff_ne.mp hne
            have hno := hx y (List.mem_cons_self ..) hne'
            exact exclSound_insert (exclSound_insert hT hno) (fun ⟨hy1, hx1⟩ => hno ⟨hx1, hy1⟩)
          · exact hT
        · intro z hz; exact hx z (List.mem_cons_of_mem _ hz)
  unfold insertAllPairs
  induction xs generalizing S with
  | nil => exact hS
  | cons x rest ih =>
      apply ih
      · exact inner x ys S hS (fun y hy => hxy x (List.mem_cons_self ..) y hy)
      · intro a ha b hb; exact hxy a (List.mem_cons_of_mem _ ha) b hb

/-- Pass 1: collect all variables forced into `{0, 1}` by univariate degree-≤-2 constraints. -/
def collectBoolVars (cs : List (ArithExpr F)) : Std.HashSet Var :=
  cs.foldl (fun acc c =>
    match univarBoolVar c with
    | some v => acc.insert v
    | none => acc) {}

theorem collectBoolVars_sound {cs : List (ArithExpr F)} {w : Var → F}
    (sat : Scalar.Circuit.Satisfies cs w) : BoolSound w (collectBoolVars cs) := by
  unfold collectBoolVars
  suffices ∀ (ds : List (ArithExpr F)) (acc : Std.HashSet Var),
      BoolSound w acc → Scalar.Circuit.Satisfies ds w →
      BoolSound w (ds.foldl (fun acc c =>
        match univarBoolVar c with | some v => acc.insert v | none => acc) acc) by
    exact this cs {} (boolSound_empty w) sat
  intro ds
  induction ds with
  | nil => intro acc hacc _; exact hacc
  | cons c rest ih =>
      intro acc hacc hsat
      apply ih
      · dsimp only
        cases hu : univarBoolVar c with
        | none => exact hacc
        | some v => exact boolSound_insert hacc (univarBoolVar_sound hu (hsat c (List.mem_cons_self ..)))
      · intro d hd; exact hsat d (List.mem_cons_of_mem _ hd)

/-- Update `(forcedSet, exclSet)` from one constraint `c` using `boolSet`. -/
def recordConstraintFacts (boolSet : Std.HashSet Var)
    (acc : Std.HashSet Var × Std.HashSet (Var × Var)) (c : ArithExpr F) :
    Std.HashSet Var × Std.HashSet (Var × Var) :=
  let (forced, excl) := acc
  match affineOf c with
  | some aff =>
      match uniformOf aff with
      | some (vs, r) =>
          if vs.all boolSet.contains then
            let forced := if noRootFrom 1 vs.length r then insertAllVars forced vs else forced
            let excl := if noRootFrom 2 (vs.length - 1) r then insertAllPairs excl vs vs else excl
            (forced, excl)
          else (forced, excl)
      | none => (forced, excl)
  | none =>
      match peelScale c with
      | .mul lhs rhs =>
          match affineOf lhs, affineOf rhs with
          | some affA, some affB =>
              match uniformOf affA, uniformOf affB with
              | some (A, ra), some (B, rb) =>
                  if A.all boolSet.contains && B.all boolSet.contains then
                    let forced :=
                      if A == B && noRootFrom 1 A.length ra && noRootFrom 1 A.length rb then
                        insertAllVars forced A
                      else forced
                    let forced :=
                      if noRootFrom 1 A.length ra && noRootFrom 1 B.length rb then
                        insertAllVars forced (A.filter (· ∈ B))
                      else forced
                    let excl :=
                      if A == B && noRootFrom 2 (A.length - 1) ra && noRootFrom 2 (A.length - 1) rb then
                        insertAllPairs excl A A
                      else excl
                    let excl :=
                      if noRootFrom 1 A.length ra && noRootFrom 1 B.length rb then
                        insertAllPairs excl A B
                      else excl
                    let excl :=
                      if noRootFrom 1 A.length ra && noRootFrom 2 (B.length - 1) rb && A.all (· ∈ B) then
                        insertAllPairs excl A B
                      else excl
                    let excl :=
                      if noRootFrom 1 B.length rb && noRootFrom 2 (A.length - 1) ra && B.all (· ∈ A) then
                        insertAllPairs excl B A
                      else excl
                    (forced, excl)
                  else (forced, excl)
              | _, _ => (forced, excl)
          | _, _ => (forced, excl)
      | _ => (forced, excl)

theorem recordConstraintFacts_sound {boolSet : Std.HashSet Var}
    {forced : Std.HashSet Var} {excl : Std.HashSet (Var × Var)}
    {c : ArithExpr F} {w : Var → F}
    (hb : BoolSound w boolSet) (hf : ForcedSound w forced) (he : ExclSound w excl)
    (hc : c.denote w = 0) :
    ForcedSound w (recordConstraintFacts boolSet (forced, excl) c).1 ∧
      ExclSound w (recordConstraintFacts boolSet (forced, excl) c).2 := by
  unfold recordConstraintFacts
  dsimp only
  cases haff : affineOf c with
  | some aff =>
    dsimp only
    cases huni : uniformOf aff with
    | none => exact ⟨hf, he⟩
    | some pair =>
      rcases pair with ⟨vs, r⟩
      dsimp only
      split
      · rename_i hall
        have hbits : ∀ v ∈ vs, w v = 0 ∨ w v = 1 :=
          fun v hv => hb v ((List.all_eq_true.mp hall) v hv)
        obtain ⟨hnd, hsumEq⟩ := uniformOf_sound huni
        have hden := affineOf_denote w haff
        rw [hc] at hden
        have hsum : (vs.map w).sum = r := hsumEq w hden.symm
        constructor
        · dsimp only
          split
          · rename_i hno1
            apply forcedSound_insertAllVars hf
            intro v hv
            rcases hbits v hv with h0 | h1
            · exact h0
            · exact False.elim (sum_ne_of_one_mem hnd hbits hno1 hv h1 hsum)
          · exact hf
        · dsimp only
          split
          · rename_i hno2
            apply exclSound_insertAllPairs he
            intro x hx y hy hne ⟨hx1, hy1⟩
            exact sum_ne_of_two_mem hnd hbits hno2 hx hy hne hx1 hy1 hsum
          · exact he
      · exact ⟨hf, he⟩
  | none =>
    dsimp only
    cases hpeel : peelScale c with
    | mul lhs rhs =>
      dsimp only
      cases haffA : affineOf lhs with
      | none => exact ⟨hf, he⟩
      | some affA =>
        cases haffB : affineOf rhs with
        | none => exact ⟨hf, he⟩
        | some affB =>
          dsimp only
          cases huniA : uniformOf affA with
          | none => exact ⟨hf, he⟩
          | some pairA =>
            cases huniB : uniformOf affB with
            | none => exact ⟨hf, he⟩
            | some pairB =>
              rcases pairA with ⟨A, ra⟩
              rcases pairB with ⟨B, rb⟩
              dsimp only
              split
              · rename_i hall
                simp only [Bool.and_eq_true, List.all_eq_true] at hall
                have hbitsA : ∀ v ∈ A, w v = 0 ∨ w v = 1 := fun v hv => hb v (hall.1 v hv)
                have hbitsB : ∀ v ∈ B, w v = 0 ∨ w v = 1 := fun v hv => hb v (hall.2 v hv)
                obtain ⟨hndA, hsumA⟩ := uniformOf_sound huniA
                obtain ⟨hndB, hsumB⟩ := uniformOf_sound huniB
                have hzero : (peelScale c).denote w = 0 := peelScale_of_zero w c hc
                rw [hpeel] at hzero
                simp only [Scalar.Circuit.ArithExpr.denote] at hzero
                have hor : (A.map w).sum = ra ∨ (B.map w).sum = rb := by
                  rcases mul_eq_zero.mp hzero with hl | hr
                  · exact Or.inl (hsumA w ((affineOf_denote w haffA).symm.trans hl))
                  · exact Or.inr (hsumB w ((affineOf_denote w haffB).symm.trans hr))
                let forced1 :=
                  if A == B && noRootFrom 1 A.length ra && noRootFrom 1 A.length rb then
                    insertAllVars forced A
                  else forced
                have hf1 : ForcedSound w forced1 := by
                  dsimp only [forced1]
                  split
                  · rename_i hcond
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    obtain ⟨⟨rfl, hnoA⟩, hnoB⟩ := hcond
                    apply forcedSound_insertAllVars hf
                    intro v hv
                    rcases hbitsA v hv with h0 | h1
                    · exact h0
                    · rcases hor with hA | hB
                      · exact False.elim (sum_ne_of_one_mem hndA hbitsA hnoA hv h1 hA)
                      · exact False.elim (sum_ne_of_one_mem hndA hbitsA hnoB hv h1 hB)
                  · exact hf
                let forced2 :=
                  if noRootFrom 1 A.length ra && noRootFrom 1 B.length rb then
                    insertAllVars forced1 (A.filter (· ∈ B))
                  else forced1
                have hf2 : ForcedSound w forced2 := by
                  dsimp only [forced2]
                  split
                  · rename_i hcond
                    simp only [Bool.and_eq_true] at hcond
                    apply forcedSound_insertAllVars hf1
                    intro v hv
                    have hv' := List.mem_filter.mp hv
                    have hvA := hv'.1
                    have hvB : v ∈ B := decide_eq_true_eq.mp hv'.2
                    rcases hbitsA v hvA with h0 | h1
                    · exact h0
                    · rcases hor with hA | hB
                      · exact False.elim (sum_ne_of_one_mem hndA hbitsA hcond.1 hvA h1 hA)
                      · exact False.elim (sum_ne_of_one_mem hndB hbitsB hcond.2 hvB h1 hB)
                  · exact hf1
                let excl1 :=
                  if A == B && noRootFrom 2 (A.length - 1) ra && noRootFrom 2 (A.length - 1) rb then
                    insertAllPairs excl A A
                  else excl
                have he1 : ExclSound w excl1 := by
                  dsimp only [excl1]
                  split
                  · rename_i hcond
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    obtain ⟨⟨rfl, hnoA⟩, hnoB⟩ := hcond
                    apply exclSound_insertAllPairs he
                    intro x hx y hy hne ⟨hx1, hy1⟩
                    rcases hor with hA | hB
                    · exact sum_ne_of_two_mem hndA hbitsA hnoA hx hy hne hx1 hy1 hA
                    · exact sum_ne_of_two_mem hndA hbitsA hnoB hx hy hne hx1 hy1 hB
                  · exact he
                let excl2 :=
                  if noRootFrom 1 A.length ra && noRootFrom 1 B.length rb then
                    insertAllPairs excl1 A B
                  else excl1
                have he2 : ExclSound w excl2 := by
                  dsimp only [excl2]
                  split
                  · rename_i hcond
                    simp only [Bool.and_eq_true] at hcond
                    apply exclSound_insertAllPairs he1
                    intro x hx y hy _ ⟨hx1, hy1⟩
                    rcases hor with hA | hB
                    · exact sum_ne_of_one_mem hndA hbitsA hcond.1 hx hx1 hA
                    · exact sum_ne_of_one_mem hndB hbitsB hcond.2 hy hy1 hB
                  · exact he1
                let excl3 :=
                  if noRootFrom 1 A.length ra && noRootFrom 2 (B.length - 1) rb && A.all (· ∈ B) then
                    insertAllPairs excl2 A B
                  else excl2
                have he3 : ExclSound w excl3 := by
                  dsimp only [excl3]
                  split
                  · rename_i hcond
                    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcond
                    obtain ⟨⟨hnoA, hnoB⟩, hsub⟩ := hcond
                    apply exclSound_insertAllPairs he2
                    intro x hx y hy hne ⟨hx1, hy1⟩
                    rcases hor with hA | hB
                    · exact sum_ne_of_one_mem hndA hbitsA hnoA hx hx1 hA
                    · exact sum_ne_of_two_mem hndB hbitsB hnoB (hsub x hx) hy hne hx1 hy1 hB
                  · exact he2
                let excl4 :=
                  if noRootFrom 1 B.length rb && noRootFrom 2 (A.length - 1) ra && B.all (· ∈ A) then
                    insertAllPairs excl3 B A
                  else excl3
                have he4 : ExclSound w excl4 := by
                  dsimp only [excl4]
                  split
                  · rename_i hcond
                    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcond
                    obtain ⟨⟨hnoB, hnoA⟩, hsub⟩ := hcond
                    apply exclSound_insertAllPairs he3
                    intro x hx y hy hne ⟨hx1, hy1⟩
                    rcases hor with hA | hB
                    · exact sum_ne_of_two_mem hndA hbitsA hnoA (hsub x hx) hy hne hx1 hy1 hA
                    · exact sum_ne_of_one_mem hndB hbitsB hnoB hx hx1 hB
                  · exact he3
                exact ⟨hf2, he4⟩
              · exact ⟨hf, he⟩
    | const _ => exact ⟨hf, he⟩
    | var _ => exact ⟨hf, he⟩
    | add _ _ => exact ⟨hf, he⟩
    | sub _ _ => exact ⟨hf, he⟩

/-- Pass 2: collect forced-zero variables and pairwise exclusions from `cs`. -/
def collectFacts (boolSet : Std.HashSet Var) (cs : List (ArithExpr F)) :
    Std.HashSet Var × Std.HashSet (Var × Var) :=
  cs.foldl (recordConstraintFacts boolSet) ({}, {})

theorem collectFacts_sound {boolSet : Std.HashSet Var} {cs : List (ArithExpr F)} {w : Var → F}
    (hb : BoolSound w boolSet) (sat : Scalar.Circuit.Satisfies cs w) :
    ForcedSound w (collectFacts boolSet cs).1 ∧ ExclSound w (collectFacts boolSet cs).2 := by
  unfold collectFacts
  suffices ∀ (ds : List (ArithExpr F)) (acc : Std.HashSet Var × Std.HashSet (Var × Var)),
      ForcedSound w acc.1 → ExclSound w acc.2 → Scalar.Circuit.Satisfies ds w →
      ForcedSound w (ds.foldl (recordConstraintFacts boolSet) acc).1 ∧
        ExclSound w (ds.foldl (recordConstraintFacts boolSet) acc).2 by
    exact this cs ({}, {}) (forcedSound_empty w) (exclSound_empty w) sat
  intro ds
  induction ds with
  | nil => intro acc hf he _; exact ⟨hf, he⟩
  | cons c rest ih =>
      intro acc hf he hsat
      rcases acc with ⟨forced, excl⟩
      have hstep := recordConstraintFacts_sound hb hf he (hsat c (List.mem_cons_self ..))
      exact ih _ hstep.1 hstep.2 (fun d hd => hsat d (List.mem_cons_of_mem _ hd))

/-- Check that every distinct pair of variables in `vs` is mutually exclusive. -/
def allPairsExcl (excl : Std.HashSet (Var × Var)) : List Var → Bool
  | [] => true
  | x :: rest => rest.all (fun y => excl.contains (x, y)) && allPairsExcl excl rest

theorem sum_bool_of_allPairsExcl {excl : Std.HashSet (Var × Var)} {w : Var → F}
    (he : ExclSound w excl) :
    ∀ {vs : List Var},
      (∀ v ∈ vs, w v = 0 ∨ w v = 1) →
      allPairsExcl excl vs = true →
      (vs.map w).sum = 0 ∨ (vs.map w).sum = 1
  | [], _, _ => Or.inl rfl
  | x :: rest, hbits, hp => by
      simp only [allPairsExcl, Bool.and_eq_true, List.all_eq_true] at hp
      have hrest := sum_bool_of_allPairsExcl he
        (fun v hv => hbits v (List.mem_cons_of_mem _ hv)) hp.2
      simp only [List.map_cons, List.sum_cons]
      rcases hbits x (List.mem_cons_self ..) with hx0 | hx1
      · rw [hx0, zero_add]; exact hrest
      · have hzeros : ∀ v ∈ rest, w v = 0 := by
          intro v hv
          rcases hbits v (List.mem_cons_of_mem _ hv) with hv0 | hv1
          · exact hv0
          · exact False.elim (he x v (hp.1 v hv) ⟨hx1, hv1⟩)
        have hsum0 : (rest.map w).sum = 0 := by
          clear hx1 hp hrest hbits
          induction rest with
          | nil => rfl
          | cons y tl ih =>
              simp [hzeros y (List.mem_cons_self ..), ih (fun z hz => hzeros z (List.mem_cons_of_mem _ hz))]
        rw [hx1, hsum0, add_zero]
        exact Or.inr rfl

/-- Fast affine check: after dropping forced-zero terms, `e` is a constant `0`/`1`,
a sum `Σ x_i` of pairwise-exclusive boolean variables, or its complement `1 − Σ x_i`. -/
def boolAffineCheck (boolSet forcedSet : Std.HashSet Var) (exclSet : Std.HashSet (Var × Var))
    (e : ArithExpr F) : Bool :=
  match affineOf e with
  | none => false
  | some (terms, c) =>
      let live := terms.filter fun t => !forcedSet.contains t.1
      if live.isEmpty then c == 0 || c == 1
      else
        let isPos := c == 0 && live.all (fun t => t.2 == 1 && boolSet.contains t.1)
        let isNeg := c == 1 && live.all (fun t => t.2 == -1 && boolSet.contains t.1)
        (isPos || isNeg) && allPairsExcl exclSet (live.map Prod.fst)

theorem affine_filter_forced {forcedSet : Std.HashSet Var} {w : Var → F}
    (hf : ForcedSound w forcedSet) :
    ∀ ts : List (Var × F),
      ((ts.filter fun t => !forcedSet.contains t.1).map fun t => t.2 * w t.1).sum =
        (ts.map fun t => t.2 * w t.1).sum
  | [] => rfl
  | (v, k) :: rest => by
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      cases hfv : forcedSet.contains v with
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, affine_filter_forced hf rest,
          hf v hfv, mul_zero, zero_add]
      | false =>
        simp only [Bool.not_false, ↓reduceIte, List.map_cons, List.sum_cons,
          affine_filter_forced hf rest]

theorem boolAffineCheck_sound {boolSet forcedSet : Std.HashSet Var}
    {exclSet : Std.HashSet (Var × Var)} {e : ArithExpr F} {w : Var → F}
    (hb : BoolSound w boolSet) (hf : ForcedSound w forcedSet) (he : ExclSound w exclSet)
    (hok : boolAffineCheck boolSet forcedSet exclSet e = true) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  unfold boolAffineCheck at hok
  cases haff : affineOf e with
  | none => simp [haff] at hok
  | some pair =>
    rcases pair with ⟨terms, c⟩
    simp only [haff] at hok
    have hden := affineOf_denote w haff
    unfold affineDenote at hden
    rw [← affine_filter_forced hf terms] at hden
    set live := terms.filter fun t => !forcedSet.contains t.1
    split at hok
    · rename_i hempty
      have hnil : live = [] := List.isEmpty_iff.mp hempty
      rw [hnil] at hden
      simp only [List.map_nil, List.sum_nil, zero_add] at hden
      simp only [Bool.or_eq_true, beq_iff_eq] at hok
      rw [hden]; exact hok
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at hok
      obtain ⟨hpos | hneg, hpairs⟩ := hok
      · obtain ⟨rfl, hall⟩ := hpos
        have hbits : ∀ v ∈ live.map Prod.fst, w v = 0 ∨ w v = 1 := by
          intro v hv
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
          exact hb t.1 (hall t ht).2
        have hsum := sum_bool_of_allPairsExcl he hbits hpairs
        have hrewAux : ∀ ls : List (Var × F), (∀ t ∈ ls, t.2 = 1) →
            (ls.map fun t => t.2 * w t.1).sum = ((ls.map Prod.fst).map w).sum := by
          intro ls
          induction ls with
          | nil => intro _; rfl
          | cons t tl ih =>
              intro hls
              have ht1 : t.2 = 1 := hls t (List.mem_cons_self ..)
              simp [ht1, ih (fun x hx => hls x (List.mem_cons_of_mem _ hx))]
        have hrew := hrewAux live (fun t ht => (hall t ht).1)
        rw [hden, hrew, add_zero]
        exact hsum
      · obtain ⟨rfl, hall⟩ := hneg
        have hbits : ∀ v ∈ live.map Prod.fst, w v = 0 ∨ w v = 1 := by
          intro v hv
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
          exact hb t.1 (hall t ht).2
        have hsum := sum_bool_of_allPairsExcl he hbits hpairs
        have hrewAux : ∀ ls : List (Var × F), (∀ t ∈ ls, t.2 = -1) →
            (ls.map fun t => t.2 * w t.1).sum = -((ls.map Prod.fst).map w).sum := by
          intro ls
          induction ls with
          | nil => intro _; simp
          | cons t tl ih =>
              intro hls
              have ht1 : t.2 = -1 := hls t (List.mem_cons_self ..)
              simp only [List.map_cons, List.sum_cons, ht1, neg_one_mul,
                ih (fun x hx => hls x (List.mem_cons_of_mem _ hx))]
              ring
        have hrew := hrewAux live (fun t ht => (hall t ht).1)
        rw [hden, hrew]
        rcases hsum with h0 | h1
        · right; rw [h0]; simp
        · left; rw [h1]; simp

/-- Early-pruned, fuel-bounded branch-and-bound DFS over boolean variables.
Each step `(v, ready)` decides `v ∈ {0, 1}` and checks constraints `ready`
whose variables are now all decided. Returns `(true, remainingFuel)` only when
every satisfying 0/1 extension yields `e ∈ {0, 1}`. -/
def dfsSteps (e : ArithExpr F) (forced : Std.HashSet Var) (excl : Std.HashSet (Var × Var))
    (assigned : List Var) (fuel : Nat) : List (Var × List (ArithExpr F)) → Bool × Nat
  | [] =>
      (decide (e.denote (indicator assigned) = 0) || decide (e.denote (indicator assigned) = 1), fuel)
  | (v, ready) :: rest =>
      match fuel with
      | 0 => (false, 0)
      | fuel' + 1 =>
          let (ok0, f1) :=
            if ready.all fun c => decide (c.denote (indicator assigned) = 0) then
              dfsSteps e forced excl assigned fuel' rest
            else (true, fuel')
          if !ok0 then (false, f1)
          else if forced.contains v || assigned.any (fun u => excl.contains (u, v)) then
            (true, f1)
          else
            let assigned1 := v :: assigned
            if ready.all fun c => decide (c.denote (indicator assigned1) = 0) then
              dfsSteps e forced excl assigned1 f1 rest
            else (true, f1)

theorem dfsSteps_sound {e : ArithExpr F} {forced : Std.HashSet Var}
    {excl : Std.HashSet (Var × Var)} {w : Var → F}
    (hf : ForcedSound w forced) (he : ExclSound w excl) :
    ∀ (steps : List (Var × List (ArithExpr F))) (fixed assigned : List Var) (fuel : Nat),
      (dfsSteps e forced excl assigned fuel steps).1 = true →
      (∀ u ∈ assigned, u ∈ fixed) →
      (∀ u ∈ fixed, w u = indicator assigned u) →
      (∀ v ∈ steps.map Prod.fst, w v = 0 ∨ w v = 1) →
      (∀ v ∈ steps.map Prod.fst, v ∉ fixed) →
      (steps.map Prod.fst).Nodup →
      (∀ i : Fin steps.length, ∀ c ∈ steps[i].2,
        c.denote w = 0 ∧
          ∀ u ∈ varsOf c, u ∈ (steps.take (i.1 + 1)).map Prod.fst ++ fixed) →
      (∀ u ∈ varsOf e, u ∈ steps.map Prod.fst ++ fixed) →
      e.denote w = 0 ∨ e.denote w = 1
  | [], fixed, assigned, fuel, hok, _, hagree, _, _, _, _, hevars => by
      simp only [dfsSteps, Bool.or_eq_true, decide_eq_true_eq] at hok
      have hcongr : e.denote w = e.denote (indicator assigned) :=
        denote_congr_vars e fun u hu => hagree u (by simpa using hevars u hu)
      rw [hcongr]
      exact hok
  | (v, ready) :: rest, fixed, assigned, fuel, hok, hassSub, hagree, hbits, hdisj, hnd, hready, hevars => by
      cases fuel with
      | zero => simp [dfsSteps] at hok
      | succ fuel' =>
        have hv_bits : w v = 0 ∨ w v = 1 := hbits v (List.mem_cons_self ..)
        have hv_nfixed : v ∉ fixed := hdisj v (List.mem_cons_self ..)
        have hv_nass : v ∉ assigned := fun h => hv_nfixed (hassSub v h)
        have hnd' := List.nodup_cons.mp hnd
        have hready0 : ∀ c ∈ ready, c.denote w = 0 ∧ ∀ u ∈ varsOf c, u ∈ v :: fixed := by
          intro c hc
          have h0 := hready ⟨0, by simp⟩ c hc
          simpa using h0
        have hreadyRest : ∀ i : Fin rest.length, ∀ c ∈ rest[i].2,
            c.denote w = 0 ∧ ∀ u ∈ varsOf c, u ∈ (rest.take (i.1 + 1)).map Prod.fst ++ (v :: fixed) := by
          intro i c hc
          have hi := hready ⟨i.1 + 1, by simp⟩ c hc
          refine ⟨hi.1, fun u hu => ?_⟩
          have hm := hi.2 u hu
          simp only [List.take_succ_cons, List.map_cons, List.cons_append, List.mem_cons,
            List.mem_append] at hm ⊢
          rcases hm with rfl | hm' | hm'
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hm'
          · exact Or.inr (Or.inr hm')
        have hevars' : ∀ u ∈ varsOf e, u ∈ rest.map Prod.fst ++ (v :: fixed) := by
          intro u hu
          have hm := hevars u hu
          simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hm ⊢
          rcases hm with rfl | hm' | hm'
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hm'
          · exact Or.inr (Or.inr hm')
        have hdisj' : ∀ u ∈ rest.map Prod.fst, u ∉ v :: fixed := by
          intro u hu hmem
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · exact hnd'.1 hu
          · exact hdisj u (List.mem_cons_of_mem _ hu) hmem'
        have hbits' : ∀ u ∈ rest.map Prod.fst, w u = 0 ∨ w u = 1 :=
          fun u hu => hbits u (List.mem_cons_of_mem _ hu)
        -- Step into dfsSteps
        unfold dfsSteps at hok
        dsimp only at hok
        rcases hv_bits with hv0 | hv1
        · have hagree0 : ∀ u ∈ v :: fixed, w u = indicator assigned u := by
            intro u hu
            rcases List.mem_cons.mp hu with rfl | hu'
            · simp [indicator, hv_nass, hv0]
            · exact hagree u hu'
          have hreadyTrue : (ready.all fun c => decide (c.denote (indicator assigned) = 0)) = true := by
            apply List.all_eq_true.mpr
            intro c hc
            have hce : c.denote w = c.denote (indicator assigned) :=
              denote_congr_vars c fun u hu => hagree0 u ((hready0 c hc).2 u hu)
            rw [decide_eq_true_eq, ← hce]
            exact (hready0 c hc).1
          simp only [hreadyTrue, ↓reduceIte] at hok
          cases hrec : dfsSteps e forced excl assigned fuel' rest with
          | mk ok0 f1 =>
            simp only [hrec] at hok
            cases ok0 with
            | false => simp at hok
            | true =>
              exact dfsSteps_sound hf he rest (v :: fixed) assigned fuel'
                (by simp [hrec]) (fun u hu => List.mem_cons_of_mem _ (hassSub u hu))
                hagree0 hbits' hdisj' hnd'.2 hreadyRest hevars'
        · have hagree1 : ∀ u ∈ v :: fixed, w u = indicator (v :: assigned) u := by
            intro u hu
            rcases List.mem_cons.mp hu with rfl | hu'
            · simp [indicator, hv1]
            · have huv : u ≠ v := fun heq => hv_nfixed (heq ▸ hu')
              have : (indicator (v :: assigned) u : F) = indicator assigned u := by
                simp [indicator, huv]
              rw [this]
              exact hagree u hu'
          have hreadyTrue1 : (ready.all fun c => decide (c.denote (indicator (v :: assigned)) = 0)) = true := by
            apply List.all_eq_true.mpr
            intro c hc
            have hce : c.denote w = c.denote (indicator (v :: assigned)) :=
              denote_congr_vars c fun u hu => hagree1 u ((hready0 c hc).2 u hu)
            rw [decide_eq_true_eq, ← hce]
            exact (hready0 c hc).1
          have hnotForced : forced.contains v = false := by
            cases hfc : forced.contains v with
            | false => rfl
            | true =>
              have : (1 : F) = 0 := hv1 ▸ hf v hfc
              exact False.elim (one_ne_zero this)
          have hnotExcl : assigned.any (fun u => excl.contains (u, v)) = false := by
            cases hxe : assigned.any (fun u => excl.contains (u, v)) with
            | false => rfl
            | true =>
              obtain ⟨u, hu, hex⟩ := List.any_eq_true.mp hxe
              have hu1 : w u = 1 := by
                rw [hagree u (hassSub u hu)]
                simp [indicator, hu]
              exact False.elim (he u v hex ⟨hu1, hv1⟩)
          cases hbranch0 : (if ready.all fun c => decide (c.denote (indicator assigned) = 0)
              then dfsSteps e forced excl assigned fuel' rest else (true, fuel')) with
          | mk ok0 f1 =>
            simp only [hbranch0] at hok
            cases ok0 with
            | false => simp at hok
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnotForced, hnotExcl,
                Bool.or_false, hreadyTrue1] at hok
              exact dfsSteps_sound hf he rest (v :: fixed) (v :: assigned) f1
                hok (fun u hu => by
                  rcases List.mem_cons.mp hu with rfl | hu'
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _ (hassSub u hu'))
                hagree1 hbits' hdisj' hnd'.2 hreadyRest hevars'

/-- Bucket `localCs` along `cols`, placing each constraint at the first step
where all its variables are in `v :: fixed`. -/
def bucketStepsAux (fixed : List Var) :
    List Var → List (ArithExpr F) → List (Var × List (ArithExpr F))
  | [], _ => []
  | v :: vs, remCs =>
      let fixed' := v :: fixed
      let (ready, later) := remCs.partition fun c => (varsOf c).all (· ∈ fixed')
      (v, ready) :: bucketStepsAux fixed' vs later

theorem bucketStepsAux_map_fst (fixed : List Var) :
    ∀ (cols : List Var) (remCs : List (ArithExpr F)),
      (bucketStepsAux fixed cols remCs).map Prod.fst = cols
  | [], _ => rfl
  | v :: vs, remCs => by
      simp [bucketStepsAux, bucketStepsAux_map_fst (v :: fixed) vs]

theorem bucketStepsAux_ready {w : Var → F} :
    ∀ (cols : List Var) (fixed : List Var) (remCs : List (ArithExpr F)),
      (∀ c ∈ remCs, c.denote w = 0) →
      ∀ i : Fin (bucketStepsAux fixed cols remCs).length,
        ∀ c ∈ (bucketStepsAux fixed cols remCs)[i].2,
          c.denote w = 0 ∧
            ∀ u ∈ varsOf c,
              u ∈ ((bucketStepsAux fixed cols remCs).take (i.1 + 1)).map Prod.fst ++ fixed
  | [], _, _, _, i, _, _ => Fin.elim0 i
  | v :: vs, fixed, remCs, hrem, ⟨0, _⟩, c, hc => by
      simp only [bucketStepsAux, List.partition_eq_filter_filter, Fin.getElem_fin,
        List.getElem_cons_zero, List.mem_filter, List.all_eq_true, decide_eq_true_eq] at hc
      refine ⟨hrem c hc.1, fun u hu => ?_⟩
      simpa [bucketStepsAux] using hc.2 u hu
  | v :: vs, fixed, remCs, hrem, ⟨k + 1, hk⟩, c, hc => by
      simp only [bucketStepsAux, List.partition_eq_filter_filter, Fin.getElem_fin,
        List.getElem_cons_succ, List.length_cons, Nat.add_lt_add_iff_right] at hk hc ⊢
      have hlater : ∀ d ∈ remCs.filter (not ∘ fun c => (varsOf c).all (· ∈ v :: fixed)), d.denote w = 0 :=
        fun d hd => hrem d (List.mem_filter.mp hd).1
      have ih := bucketStepsAux_ready vs (v :: fixed) _ hlater ⟨k, hk⟩ c hc
      refine ⟨ih.1, fun u hu => ?_⟩
      have hm := ih.2 u hu
      simp only [List.take_succ_cons, List.map_cons, List.cons_append, List.mem_cons,
        List.mem_append] at hm ⊢
      rcases hm with hm' | rfl | hm'
      · exact Or.inr (Or.inl hm')
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hm')

/-- Verified DFS wrapper: validates the candidate column order `cols` and
constraint indices `cIdxs` against `csArr` and `boolSet`, then runs `dfsSteps`. -/
def runVerifiedDfs (csArr : Array (ArithExpr F)) (boolSet forcedSet : Std.HashSet Var)
    (exclSet : Std.HashSet (Var × Var)) (e : ArithExpr F)
    (cols : List Var) (cIdxs : List Nat) (fuel : Nat) : Bool :=
  if decide cols.Nodup && cols.all boolSet.contains && (varsOf e).all (· ∈ cols) then
    let localCs := cIdxs.filterMap fun idx => csArr[idx]?
    let steps := bucketStepsAux [] cols localCs
    (dfsSteps e forcedSet exclSet [] fuel steps).1
  else false

theorem runVerifiedDfs_sound {cs : List (ArithExpr F)}
    {boolSet forcedSet : Std.HashSet Var} {exclSet : Std.HashSet (Var × Var)}
    {e : ArithExpr F} {cols : List Var} {cIdxs : List Nat} {fuel : Nat} {w : Var → F}
    (sat : Scalar.Circuit.Satisfies cs w)
    (hb : BoolSound w boolSet) (hf : ForcedSound w forcedSet) (he : ExclSound w exclSet)
    (hok : runVerifiedDfs cs.toArray boolSet forcedSet exclSet e cols cIdxs fuel = true) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  unfold runVerifiedDfs at hok
  split at hok
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcond
    obtain ⟨⟨hnd, hbool⟩, hesub⟩ := hcond
    set localCs := cIdxs.filterMap fun idx => cs.toArray[idx]?
    have hlocalSat : ∀ c ∈ localCs, c.denote w = 0 := by
      intro c hc
      obtain ⟨idx, _, hget⟩ := List.mem_filterMap.mp hc
      have hmem : c ∈ cs := by
        cases hlt : decide (idx < cs.toArray.size) with
        | false =>
          have hge : ¬ idx < cs.toArray.size := by simpa using hlt
          simp [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hget
        | true =>
          have hlt' : idx < cs.toArray.size := of_decide_eq_true hlt
          rw [Array.getElem?_eq_getElem hlt', Option.some.injEq] at hget
          subst hget
          exact Array.getElem_mem_toList hlt'
      exact sat c hmem
    set steps := bucketStepsAux [] cols localCs
    have hfst : steps.map Prod.fst = cols := bucketStepsAux_map_fst [] cols localCs
    exact dfsSteps_sound hf he steps [] [] fuel hok
      (fun _ hu => by cases hu)
      (fun _ hu => by cases hu)
      (fun v hv => hb v (hbool v (hfst ▸ hv)))
      (fun _ _ hu => by cases hu)
      (hfst ▸ hnd)
      (bucketStepsAux_ready cols [] localCs hlocalSat)
      (fun u hu => by simp [hfst, hesub u hu])
  · cases hok

/-- Untrusted heuristic: close `seed` under small boolean constraints touching it
up to `cap` variables, then greedily order columns to complete constraints early. -/
def planDfsOrder (boolZeros : Array (Nat × List Var)) (varToZeros : Std.HashMap Var (Array Nat))
    (seed : List Var) (cap : Nat) (expand : Bool) : List Var × List Nat := Id.run do
  let mut s : List Var := seed.dedup
  let mut inS : Std.HashSet Var := s.foldl (fun acc v => acc.insert v) {}
  if expand && s.length < cap then
    for _ in List.range cap do
      let mut candIdxs : Std.HashSet Nat := {}
      let mut cands : Array (List Var) := #[]
      for v in s do
        for zi in varToZeros.getD v #[] do
          if !candIdxs.contains zi then
            candIdxs := candIdxs.insert zi
            if let some (_, zs) := boolZeros[zi]? then
              if zs.any (fun u => !inS.contains u) then
                cands := cands.push zs
      let sorted := cands.qsort (fun a b => a.length < b.length)
      let mut grew := false
      for zs in sorted do
        let extra := zs.filter fun u => !inS.contains u
        if !extra.isEmpty && s.length + extra.length ≤ cap then
          for u in extra do
            inS := inS.insert u
            s := u :: s
          grew := true
      if !grew then break
  -- Collect local boolean constraints whose variables all lie in `inS`.
  let mut seenZ : Std.HashSet Nat := {}
  let mut localZ : Array (Nat × List Var) := #[]
  for v in s do
    for zi in varToZeros.getD v #[] do
      if !seenZ.contains zi then
        seenZ := seenZ.insert zi
        if let some (cIdx, zs) := boolZeros[zi]? then
          if zs.all inS.contains then
            localZ := localZ.push (cIdx, zs)
  -- Greedy variable ordering: prefer variables completing the most constraints.
  let mut ordered : List Var := []
  let mut done : Std.HashSet Var := {}
  let mut rem : Array Var := s.toArray
  while !rem.isEmpty do
    let mut bestIdx := 0
    let mut bestKey : Nat × Nat := (0, 0)
    for i in List.range rem.size do
      let v := rem[i]!
      let mut complete := 0
      let mut incident := 0
      for (_, zs) in localZ do
        if zs.contains v then
          incident := incident + 1
          if zs.all (fun u => u == v || done.contains u) then
            complete := complete + 1
      if i == 0 || complete > bestKey.1 || (complete == bestKey.1 && incident > bestKey.2) then
        bestIdx := i
        bestKey := (complete, incident)
    let chosen := rem[bestIdx]!
    done := done.insert chosen
    ordered := chosen :: ordered
    rem := rem.eraseIdx! bestIdx
  return (ordered.reverse, localZ.toList.map Prod.fst)

/-- Run bounded, verified DFS over either `e`'s own support (`expand = false`) or
its closed boolean neighborhood (`expand = true`), evaluated lazily only when
faster structural and affine checks do not already certify `e`. -/
def checkExprDfs (csArr : Array (ArithExpr F))
    (boolSet forcedSet : Std.HashSet Var) (exclSet : Std.HashSet (Var × Var))
    (boolZeros : Array (Nat × List Var)) (varToZeros : Std.HashMap Var (Array Nat))
    (e : ArithExpr F) (expand : Bool) (fuel : Nat) : Bool :=
  let seed := (varsOf e).dedup
  if !expand && seed.length > 18 then false
  else
    let plan := planDfsOrder boolZeros varToZeros seed 18 expand
    runVerifiedDfs csArr boolSet forcedSet exclSet e plan.1 plan.2 fuel

theorem checkExprDfs_sound {cs : List (ArithExpr F)}
    {boolSet forcedSet : Std.HashSet Var} {exclSet : Std.HashSet (Var × Var)}
    {boolZeros : Array (Nat × List Var)} {varToZeros : Std.HashMap Var (Array Nat)}
    {w : Var → F} {e : ArithExpr F} {expand : Bool} {fuel : Nat}
    (sat : Scalar.Circuit.Satisfies cs w)
    (hb : BoolSound w boolSet) (hf : ForcedSound w forcedSet) (he : ExclSound w exclSet)
    (h : checkExprDfs cs.toArray boolSet forcedSet exclSet boolZeros varToZeros e expand fuel = true) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  simp only [checkExprDfs] at h
  split at h
  · cases h
  · exact runVerifiedDfs_sound sat hb hf he h

/-- Fallback check for non-trivial expressions: affine exclusions, bounded DFS
over the expression's support (and then its closed boolean neighborhood), and
direct polynomial identity against `±e·(e − 1)`. -/
def checkExprFallback (cs : List (ArithExpr F)) (csArr : Array (ArithExpr F))
    (boolSet forcedSet : Std.HashSet Var) (exclSet : Std.HashSet (Var × Var))
    (boolZeros : Array (Nat × List Var)) (varToZeros : Std.HashMap Var (Array Nat))
    (e : ArithExpr F) : Bool :=
  boolAffineCheck boolSet forcedSet exclSet e ||
    checkExprDfs csArr boolSet forcedSet exclSet boolZeros varToZeros e false (1 <<< 14) ||
    checkExprDfs csArr boolSet forcedSet exclSet boolZeros varToZeros e true (1 <<< 20) ||
    boolDirect cs e

theorem checkExprFallback_sound {cs : List (ArithExpr F)}
    {boolSet forcedSet : Std.HashSet Var} {exclSet : Std.HashSet (Var × Var)}
    {boolZeros : Array (Nat × List Var)} {varToZeros : Std.HashMap Var (Array Nat)}
    {w : Var → F} {e : ArithExpr F}
    (sat : Scalar.Circuit.Satisfies cs w)
    (hb : BoolSound w boolSet) (hf : ForcedSound w forcedSet) (he : ExclSound w exclSet)
    (h : checkExprFallback cs cs.toArray boolSet forcedSet exclSet boolZeros varToZeros e = true) :
    e.denote w = 0 ∨ e.denote w = 1 := by
  unfold checkExprFallback at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((haff | h1) | h2) | hdir
  · exact boolAffineCheck_sound hb hf he haff
  · exact checkExprDfs_sound sat hb hf he h1
  · exact checkExprDfs_sound sat hb hf he h2
  · exact boolDirect_sound hdir sat

/-- Fast, terminating, kernel-proved-sound enable checker for one expression `e`
under chip constraints `cs`. -/
def checkExprFast (cs : List (ArithExpr F)) (csArr : Array (ArithExpr F))
    (boolSet forcedSet : Std.HashSet Var) (exclSet : Std.HashSet (Var × Var))
    (boolZeros : Array (Nat × List Var)) (varToZeros : Std.HashMap Var (Array Nat)) :
    ArithExpr F → Bool
  | .const k => k == 0 || k == 1
  | .var v => forcedSet.contains v || boolSet.contains v
  | .mul x y =>
      (checkExprFast cs csArr boolSet forcedSet exclSet boolZeros varToZeros x &&
        checkExprFast cs csArr boolSet forcedSet exclSet boolZeros varToZeros y) ||
      checkExprFallback cs csArr boolSet forcedSet exclSet boolZeros varToZeros (.mul x y)
  | .sub x y =>
      (Poly.Identical (Poly.ofExpr x) (Poly.const 1) &&
        checkExprFast cs csArr boolSet forcedSet exclSet boolZeros varToZeros y) ||
      checkExprFallback cs csArr boolSet forcedSet exclSet boolZeros varToZeros (.sub x y)
  | .add x y =>
      checkExprFallback cs csArr boolSet forcedSet exclSet boolZeros varToZeros (.add x y)

theorem checkExprFast_sound {cs : List (ArithExpr F)}
    {boolSet forcedSet : Std.HashSet Var} {exclSet : Std.HashSet (Var × Var)}
    {boolZeros : Array (Nat × List Var)} {varToZeros : Std.HashMap Var (Array Nat)}
    {w : Var → F}
    (sat : Scalar.Circuit.Satisfies cs w)
    (hb : BoolSound w boolSet) (hf : ForcedSound w forcedSet) (he : ExclSound w exclSet) :
    ∀ {e : ArithExpr F},
      checkExprFast cs cs.toArray boolSet forcedSet exclSet boolZeros varToZeros e = true →
      e.denote w = 0 ∨ e.denote w = 1
  | .const k, h => by
      simp only [checkExprFast, Bool.or_eq_true, beq_iff_eq] at h
      simpa [Scalar.Circuit.ArithExpr.denote] using h
  | .var v, h => by
      simp only [checkExprFast, Bool.or_eq_true] at h
      simp only [Scalar.Circuit.ArithExpr.denote]
      rcases h with hforced | hbool
      · exact Or.inl (hf v hforced)
      · exact hb v hbool
  | .mul x y, h => by
      simp only [checkExprFast, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hx, hy⟩ | hfb
      · have bx := checkExprFast_sound sat hb hf he hx
        have byy := checkExprFast_sound sat hb hf he hy
        simp only [Scalar.Circuit.ArithExpr.denote]
        rcases bx with bx | bx <;> rcases byy with byy | byy <;> simp [bx, byy]
      · exact checkExprFallback_sound sat hb hf he hfb
  | .sub x y, h => by
      simp only [checkExprFast, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hx, hy⟩ | hfb
      · have one := Poly.Identical.denote w hx
        rw [Poly.denote_ofExpr] at one
        simp only [Poly.denote, Poly.const, Mono.eval, List.map_cons, List.map_nil,
          List.prod_nil, mul_one, List.sum_cons, List.sum_nil, add_zero] at one
        have byy := checkExprFast_sound sat hb hf he hy
        simp only [Scalar.Circuit.ArithExpr.denote, one]
        rcases byy with byy | byy <;> simp [byy]
      · exact checkExprFallback_sound sat hb hf he hfb
  | .add x y, h => checkExprFallback_sound sat hb hf he h

/-- Build the inverted index of boolean-only constraints once per chip. -/
def buildBoolZeroIndex (cs : List (ArithExpr F)) (boolSet : Std.HashSet Var) :
    Array (Nat × List Var) × Std.HashMap Var (Array Nat) := Id.run do
  let mut zeros : Array (Nat × List Var) := #[]
  let mut byVar : Std.HashMap Var (Array Nat) := {}
  let mut cIdx := 0
  for c in cs do
    let vs := (varsOf c).dedup
    if !vs.isEmpty && vs.all boolSet.contains then
      let zi := zeros.size
      zeros := zeros.push (cIdx, vs)
      for v in vs do
        byVar := byVar.insert v ((byVar.getD v #[]).push zi)
    cIdx := cIdx + 1
  return (zeros, byVar)

/-- Fast, complete, terminating boolean-enable certificate for an unactivated
chip `c`. Checks every unique send and memory enable of `c` against `c.constraints`
(discharging `Boolean c w` for `Activation.compile c` via `boolean_of_checkChipEnables`). -/
def checkChipEnables (c : Chip F) : Bool :=
  let enables := (c.sends.map (·.enable) ++ c.memory.map (·.enable)).dedup
  if enables.isEmpty then true
  else
    let cs := c.constraints
    let csArr := cs.toArray
    let boolSet := collectBoolVars cs
    let facts := collectFacts boolSet cs
    let idx := buildBoolZeroIndex cs boolSet
    enables.all (checkExprFast cs csArr boolSet facts.1 facts.2 idx.1 idx.2)

theorem checkChipEnables_unactivated_sound {c : Chip F}
    (ok : checkChipEnables c = true) {w : Var → F}
    (sat : Scalar.Circuit.Satisfies c.constraints w) :
    (∀ s ∈ c.sends, s.enable.denote w = 0 ∨ s.enable.denote w = 1) ∧
      ∀ m ∈ c.memory, m.enable.denote w = 0 ∨ m.enable.denote w = 1 := by
  simp only [checkChipEnables] at ok
  set enables := (c.sends.map (·.enable) ++ c.memory.map (·.enable)).dedup
  have hmemS : ∀ s ∈ c.sends, s.enable ∈ enables := fun s hs =>
    List.mem_dedup.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
  have hmemM : ∀ m ∈ c.memory, m.enable ∈ enables := fun m hm =>
    List.mem_dedup.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨m, hm, rfl⟩))
  split at ok
  · rename_i hempty
    have hnil : enables = [] := List.isEmpty_iff.mp hempty
    refine ⟨fun s hs => by have := hmemS s hs; simp [hnil] at this,
      fun m hm => by have := hmemM m hm; simp [hnil] at this⟩
  · have hb := collectBoolVars_sound sat
    have ⟨hf, he⟩ := collectFacts_sound hb sat
    have hall := List.all_eq_true.mp ok
    exact ⟨fun s hs => checkExprFast_sound sat hb hf he (hall s.enable (hmemS s hs)),
      fun m hm => checkExprFast_sound sat hb hf he (hall m.enable (hmemM m hm))⟩

/-- `checkChipEnables` discharges `Boolean` on every row satisfying the activated
chip's constraints, with no `SmallCast` side condition. -/
theorem boolean_of_checkChipEnables {c : Chip F}
    (ok : checkChipEnables c = true) {w : Var → F}
    (sat : Scalar.Circuit.Satisfies (Activation.compile c).constraints w) : Boolean c w := by
  have hsel : w c.numVars = 0 ∨ w c.numVars = 1 := by
    have h := sat (Activation.boolean c.numVars) (by simp [Activation.compile])
    simpa [Activation.boolean, Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] using h
  rcases hsel with h0 | h1
  · constructor
    · intro s hs
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
      have hguard : (Activation.send c.numVars s0).enable ∈ Activation.guards c :=
        List.mem_dedup.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨s0, hs0, rfl⟩))
      have hsil := sat (Activation.silent c.numVars (Activation.send c.numVars s0).enable)
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hguard, rfl⟩)))
      simp only [Activation.silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote,
        h0, sub_zero, one_mul] at hsil
      exact Or.inl hsil
    · intro m hm
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
      have hguard : (Activation.memory c.numVars m0).enable ∈ Activation.guards c :=
        List.mem_dedup.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨m0, hm0, rfl⟩))
      have hsil := sat (Activation.silent c.numVars (Activation.memory c.numVars m0).enable)
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hguard, rfl⟩)))
      simp only [Activation.silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote,
        h0, sub_zero, one_mul] at hsil
      exact Or.inl hsil
  · have hsat0 : Scalar.Circuit.Satisfies c.constraints w := by
      intro p hp
      have hp' := sat (Activation.polynomial c.numVars p)
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)))
      simpa [Activation.polynomial_active c.numVars p w h1] using hp'
    obtain ⟨hS, hM⟩ := checkChipEnables_unactivated_sound ok hsat0
    constructor
    · intro s hs
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
      simpa [Activation.send, Activation.polynomial_active c.numVars s0.enable w h1] using hS s0 hs0
    · intro m hm
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
      simpa [Activation.memory, Activation.polynomial_active c.numVars m0.enable w h1] using hM m0 hm0

section SelfTests

private local instance : Fact (Nat.Prime 97) := ⟨by decide⟩
private local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def testChip (F : Type) [Field F] [DecidableEq F] (n : Nat)
    (cs : List (ArithExpr F)) (enables : List (ArithExpr F)) : Chip F :=
  { name := "test"
    numVars := n
    inputs := []
    output := .tuple []
    constraints := cs
    sends := enables.map fun e => ⟨"callee", [], .tuple [], e⟩
    memory := [] }

private def mkBool (F : Type) [Field F] (v : Var) : ArithExpr F :=
  .mul (.var v) (.sub (.var v) (.const 1))

private def mkSum (F : Type) [Field F] (vs : List Var) : ArithExpr F :=
  vs.foldl (fun acc v => .add acc (.var v)) (.const 0)

-- Positive controls: boolean selector, complement, product, mutually exclusive pair.
#guard checkChipEnables (testChip (ZMod 97) 3 [mkBool (ZMod 97) 0] [.var 0]) == true
#guard checkChipEnables (testChip (ZMod 97) 3 [mkBool (ZMod 97) 0] [.sub (.const 1) (.var 0)]) == true
#guard checkChipEnables (testChip (ZMod 97) 3
  [mkBool (ZMod 97) 0, mkBool (ZMod 97) 1] [.mul (.var 0) (.var 1)]) == true
#guard checkChipEnables (testChip (ZMod 97) 3
  [mkBool (ZMod 97) 0, mkBool (ZMod 97) 1, .mul (.var 0) (.var 1)]
  [.add (.var 0) (.var 1)]) == true

-- 20-variable pairwise mutually exclusive sum (exceeds legacy 12-variable cap).
#guard checkChipEnables (testChip (ZMod 97) 21
  ((List.range 20).map (mkBool (ZMod 97)) ++
    (List.range 20).flatMap fun i =>
      (List.range i).map fun j => .mul (.var i) (.var j))
  [mkSum (ZMod 97) (List.range 20)]) == true

-- 15-variable forced-zero sum S·(S + 1) = 0 (accepted with constraint, rejected without).
#guard checkChipEnables (testChip (ZMod 97) 16
  ((List.range 15).map (mkBool (ZMod 97)) ++
    [.mul (mkSum (ZMod 97) (List.range 15))
      (.add (mkSum (ZMod 97) (List.range 15)) (.const 1))])
  [.add (.var 0) (.var 1)]) == true
#guard checkChipEnables (testChip (ZMod 97) 16
  ((List.range 15).map (mkBool (ZMod 97)))
  [.add (.var 0) (.var 1)]) == false

-- Small-characteristic soundness: in ZMod 5 with 4 vars, S·(S + 1) = 0 allows S = 4 = -1,
-- so v0 + v1 can evaluate to 2 and MUST be rejected.
#guard checkChipEnables (testChip (ZMod 5) 5
  ((List.range 4).map (mkBool (ZMod 5)) ++
    [.mul (mkSum (ZMod 5) (List.range 4))
      (.add (mkSum (ZMod 5) (List.range 4)) (.const 1))])
  [.add (.var 0) (.var 1)]) == false

-- Nested match-arm bridge resolved by early-pruned DFS:
-- a + a' = p, b + b' = q, p * q = 0 => a + b is boolean.
#guard checkChipEnables (testChip (ZMod 97) 6
  ((List.range 6).map (mkBool (ZMod 97)) ++
    [.sub (.add (.var 0) (.var 1)) (.var 4),
     .sub (.add (.var 2) (.var 3)) (.var 5),
     .mul (.var 4) (.var 5)])
  [.add (.var 0) (.var 2)]) == true

-- Negative controls: unconstrained, doubled, negated, non-exclusive sum.
#guard checkChipEnables (testChip (ZMod 97) 2 [] [.var 0]) == false
#guard checkChipEnables (testChip (ZMod 97) 2 [mkBool (ZMod 97) 0] [.add (.var 0) (.var 0)]) == false
#guard checkChipEnables (testChip (ZMod 97) 2 [mkBool (ZMod 97) 0] [.sub (.const 0) (.var 0)]) == false
#guard checkChipEnables (testChip (ZMod 97) 3
  [mkBool (ZMod 97) 0, mkBool (ZMod 97) 1] [.add (.var 0) (.var 1)]) == false

end SelfTests

end FastEnables

end Aiur.Tiling.Bridge
