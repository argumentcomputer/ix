import Aiur.Tiling.Refinement
import Aiur.Optimized.Grouping.Memo

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

end Aiur.Tiling.Bridge
