import Aiur.Optimized.Grouping.Selection

/-!
# Certified Booleanity, Mutual Exclusion, and Zero-When-Off Checks (`C2`)

Executable, proved-sound checkers over a physical `Chip`'s actual constraint
list `cs : List (Polynomial F)`. Used by `Grouping.certify` to certify
intra-chip mutually-exclusive raw-packet compaction without trusting the
compiler's choice metadata or heuristics.

`ExclCtx.ofConstraints` normalizes and fingerprints `cs` once per member and
extracts certified choice-tree `(child, parent)` edges once per member, so
checking every compacted slot and argument word is fast even on large chips.

Zero `sorry`, standard axioms only.
-/

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

/-- Structural polynomial fingerprint ignoring coefficients (same design as
`equationKey` in `Certificate.lean`). Collisions still undergo exact normal-form
equality and have no effect on soundness. -/
def polyKey : Polynomial F → UInt64
  | .const _ => 1
  | .var v => v.toUInt64 * 1099511628211 + 3
  | .add a b => ((polyKey a * 1099511628211) ^^^ polyKey b) + 5
  | .sub a b => ((polyKey a * 1099511628211) ^^^ polyKey b) + 7
  | .mul a b => ((polyKey a * 1099511628211) ^^^ polyKey b) + 11

private theorem poly_eq_of_beq {p q : Polynomial F} (h : (p == q) = true) : p = q :=
  (Polynomial.beq_eq p q).mp h

private theorem denote_eq_of_nf_beq {p q : Polynomial F}
    (h : (Polynomial.normalForm p == Polynomial.normalForm q) = true) (a : Nat → F) :
    p.denote a = q.denote a := by
  have hd := congrArg (fun x : Polynomial F => x.denote a) (poly_eq_of_beq h)
  simpa [Polynomial.eval_normalForm] using hd

/-- Pre-normalized constraint, direct boolean, and choice-parent context for one member chip. -/
structure ExclCtx (F : Type) where
  zeroNF : Polynomial F
  oneNF : Polynomial F
  normCs : List (UInt64 × Polynomial F)
  bools : List (UInt64 × Polynomial F)
  parents : List (Polynomial F × Polynomial F)

/-- Soundness invariant of an `ExclCtx` relative to a constraint list `cs`. -/
def ExclCtx.Valid (ctx : ExclCtx F) (cs : List (Polynomial F)) : Prop :=
  ctx.zeroNF = Polynomial.normalForm (.const (0 : F)) ∧
  ctx.oneNF = Polynomial.normalForm (.const (1 : F)) ∧
  (∀ pair ∈ ctx.normCs, ∀ a, Satisfies cs a → pair.2.denote a = 0) ∧
  (∀ pair ∈ ctx.bools, ∀ a, Satisfies cs a → pair.2.denote a = 0 ∨ pair.2.denote a = 1) ∧
  (∀ pair ∈ ctx.parents, ∀ a, Satisfies cs a → pair.1.denote a ≠ 0 → pair.2.denote a ≠ 0)

/-- Executable check that `p` vanishes on every assignment satisfying `cs`. -/
def ExclCtx.isZeroOf (ctx : ExclCtx F) (p : Polynomial F) : Bool :=
  let n := Polynomial.normalForm p
  if n == ctx.zeroNF then true
  else
    let k := polyKey n
    ctx.normCs.any fun (qk, qn) => qk == k && qn == n

theorem ExclCtx.isZeroOf_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {p : Polynomial F} (h : ctx.isZeroOf p = true)
    {a : Nat → F} (valid : Satisfies cs a) : p.denote a = 0 := by
  unfold ExclCtx.isZeroOf at h
  dsimp only at h
  split at h
  · rename_i hz
    have heq : Polynomial.normalForm p = Polynomial.normalForm (.const (0 : F)) :=
      (poly_eq_of_beq hz).trans hctx.1
    have hd := congrArg (fun x : Polynomial F => x.denote a) heq
    simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] using hd
  · obtain ⟨pair, hmem, hmatch⟩ := List.any_eq_true.mp h
    have heq : pair.2 = Polynomial.normalForm p :=
      poly_eq_of_beq (Bool.and_eq_true_iff.mp hmatch).2
    have hqz : pair.2.denote a = 0 := hctx.2.2.1 pair hmem a valid
    have hd := congrArg (fun x : Polynomial F => x.denote a) heq.symm
    simpa [Polynomial.eval_normalForm, hqz] using hd

/-- Direct check that `e` is boolean (`0` or `1`) from `ctx`. -/
def ExclCtx.isDirectBool (ctx : ExclCtx F) (e : Polynomial F) : Bool :=
  let n := Polynomial.normalForm e
  let k := polyKey n
  n == ctx.zeroNF ||
  n == ctx.oneNF ||
  ctx.bools.any (fun (bk, bn) => bk == k && bn == n) ||
  ctx.isZeroOf (.mul e (.sub e (.const 1))) ||
  ctx.isZeroOf (.mul (.sub e (.const 1)) e) ||
  ctx.isZeroOf (.mul e (.add e (.const (-1)))) ||
  ctx.isZeroOf (.mul (.add e (.const (-1))) e) ||
  ctx.isZeroOf (.mul e (.sub (.const 1) e)) ||
  ctx.isZeroOf (.mul (.sub (.const 1) e) e)

theorem ExclCtx.isDirectBool_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e : Polynomial F} (h : ctx.isDirectBool e = true)
    {a : Nat → F} (valid : Satisfies cs a) : e.denote a = 0 ∨ e.denote a = 1 := by
  unfold ExclCtx.isDirectBool at h
  dsimp only at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((((((h0 | h1) | hb) | h2) | h3) | h4) | h5) | h6) | h7)
  · left
    have hd := congrArg (fun x : Polynomial F => x.denote a) ((poly_eq_of_beq h0).trans hctx.1)
    simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] using hd
  · right
    have hd := congrArg (fun x : Polynomial F => x.denote a) ((poly_eq_of_beq h1).trans hctx.2.1)
    simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] using hd
  · obtain ⟨pair, hmem, hmatch⟩ := List.any_eq_true.mp hb
    have heq : pair.2 = Polynomial.normalForm e :=
      poly_eq_of_beq (Bool.and_eq_true_iff.mp hmatch).2
    have hqb := hctx.2.2.2.1 pair hmem a valid
    have hd : e.denote a = pair.2.denote a := by
      have h := congrArg (fun x : Polynomial F => x.denote a) heq.symm
      simpa [Polynomial.eval_normalForm] using h
    rw [hd]
    exact hqb
  · have hz := ctx.isZeroOf_sound hctx h2 valid
    simp only [Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] at hz
    exact hz
  · have hz := ctx.isZeroOf_sound hctx h3 valid
    simp only [Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] at hz
    exact hz.symm
  · have hz := ctx.isZeroOf_sound hctx h4 valid
    simp only [Scalar.Circuit.ArithExpr.denote, mul_eq_zero] at hz
    rcases hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h1))
  · have hz := ctx.isZeroOf_sound hctx h5 valid
    simp only [Scalar.Circuit.ArithExpr.denote, mul_eq_zero] at hz
    rcases hz with h1 | h0
    · exact Or.inr (eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h1))
    · exact Or.inl h0
  · have hz := ctx.isZeroOf_sound hctx h6 valid
    simp only [Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] at hz
    rcases hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr h1.symm
  · have hz := ctx.isZeroOf_sound hctx h7 valid
    simp only [Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] at hz
    rcases hz with h1 | h0
    · exact Or.inr h1.symm
    · exact Or.inl h0

/-- Direct check that `e₁ * e₂ = 0` follows immediately from `ctx`. -/
def ExclCtx.isDirectExcl (ctx : ExclCtx F) (e₁ e₂ : Polynomial F) : Bool :=
  ctx.isZeroOf (.mul e₁ e₂) || ctx.isZeroOf (.mul e₂ e₁)

theorem ExclCtx.isDirectExcl_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e₁ e₂ : Polynomial F} (h : ctx.isDirectExcl e₁ e₂ = true)
    {a : Nat → F} (valid : Satisfies cs a) : e₁.denote a * e₂.denote a = 0 := by
  unfold ExclCtx.isDirectExcl at h
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  · simpa [Scalar.Circuit.ArithExpr.denote] using ctx.isZeroOf_sound hctx h1 valid
  · have hz := ctx.isZeroOf_sound hctx h2 valid
    simpa [Scalar.Circuit.ArithExpr.denote, mul_comm] using hz

/-- Flatten a sum tree into its non-zero summands. -/
def flattenAdd : Polynomial F → List (Polynomial F)
  | .const c => if c = 0 then [] else [.const c]
  | .add a b => flattenAdd a ++ flattenAdd b
  | p => [p]

theorem flattenAdd_sum (p : Polynomial F) (a : Nat → F) :
    ((flattenAdd p).map fun q => q.denote a).sum = p.denote a := by
  induction p with
  | const c =>
      unfold flattenAdd
      split
      · rename_i hc; simp [Scalar.Circuit.ArithExpr.denote, hc]
      · simp [Scalar.Circuit.ArithExpr.denote]
  | add x y ihx ihy =>
      simp [flattenAdd, List.map_append, List.sum_append, ihx, ihy, Scalar.Circuit.ArithExpr.denote]
  | var _ | sub _ _ | mul _ _ => simp [flattenAdd]

/-- Check pairwise direct exclusion across every distinct pair in `ts`. -/
def allPairwiseDirectExcl (ctx : ExclCtx F) : List (Polynomial F) → Bool
  | [] => true
  | x :: xs => xs.all (ctx.isDirectExcl x) && allPairwiseDirectExcl ctx xs

theorem pairwise_direct_excl_sum_eq {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {ts : List (Polynomial F)}
    (hpw : allPairwiseDirectExcl ctx ts = true) {a : Nat → F} (valid : Satisfies cs a) :
    ∀ t ∈ ts, t.denote a ≠ 0 → (ts.map fun q => q.denote a).sum = t.denote a := by
  induction ts with
  | nil => intro _ ht; cases ht
  | cons x xs ih =>
      simp only [allPairwiseDirectExcl, Bool.and_eq_true, List.all_eq_true] at hpw
      intro t ht hne
      rcases List.mem_cons.mp ht with rfl | ht'
      · have hxs : (xs.map fun q => q.denote a).sum = 0 := by
          apply List.sum_eq_zero
          intro v hv
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
          have hmul := ctx.isDirectExcl_sound hctx (hpw.1 y hy) valid
          rcases mul_eq_zero.mp hmul with hx0 | hy0
          · exact absurd hx0 hne
          · exact hy0
        simp [hxs]
      · have hx0 : x.denote a = 0 := by
          have hmul := ctx.isDirectExcl_sound hctx (hpw.1 t ht') valid
          rcases mul_eq_zero.mp hmul with hx0 | ht0
          · exact hx0
          · exact absurd ht0 hne
        simp [hx0, ih hpw.2 t ht' hne]

/-- Extract certified `(child, parent)` activation edges from coverage equations
`total - parent = 0` (or `parent - total = 0`) in `cs` where `total` is a sum of
pairwise directly-exclusive terms (as emitted by `Control.Certificate`). -/
def extractParents (ctx : ExclCtx F) (cs : List (Polynomial F)) :
    List (Polynomial F × Polynomial F) :=
  cs.flatMap fun q =>
    match q with
    | .sub lhs rhs =>
        let tsL := flattenAdd lhs
        let fromL :=
          if tsL.length ≥ 2 && allPairwiseDirectExcl ctx tsL then
            tsL.map fun child => (child, rhs)
          else []
        let tsR := flattenAdd rhs
        let fromR :=
          if tsR.length ≥ 2 && allPairwiseDirectExcl ctx tsR then
            tsR.map fun child => (child, lhs)
          else []
        fromL ++ fromR
    | _ => []

theorem extractParents_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {child parent : Polynomial F}
    (hmem : (child, parent) ∈ extractParents ctx cs) {a : Nat → F} (valid : Satisfies cs a)
    (hactive : child.denote a ≠ 0) : parent.denote a ≠ 0 := by
  obtain ⟨q, hq, hmemq⟩ := List.mem_flatMap.mp hmem
  cases q with
  | sub lhs rhs =>
      simp only [] at hmemq
      have hqz : lhs.denote a - rhs.denote a = 0 := valid (.sub lhs rhs) hq
      have heq : lhs.denote a = rhs.denote a := sub_eq_zero.mp hqz
      rcases List.mem_append.mp hmemq with hL | hR
      · split at hL
        · rename_i hcond
          have hpw := (Bool.and_eq_true_iff.mp hcond).2
          obtain ⟨c, hc, hpair⟩ := List.mem_map.mp hL
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
          have hsum := pairwise_direct_excl_sum_eq hctx hpw valid c hc hactive
          rw [flattenAdd_sum] at hsum
          intro hr
          exact hactive (hsum.symm.trans (heq.trans hr))
        · cases hL
      · split at hR
        · rename_i hcond
          have hpw := (Bool.and_eq_true_iff.mp hcond).2
          obtain ⟨c, hc, hpair⟩ := List.mem_map.mp hR
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
          have hsum := pairwise_direct_excl_sum_eq hctx hpw valid c hc hactive
          rw [flattenAdd_sum] at hsum
          intro hl
          exact hactive (hsum.symm.trans (heq.symm.trans hl))
        · cases hR
  | const _ | var _ | add _ _ | mul _ _ => simp at hmemq

/-- Check whether `a` and `b` satisfy `b = a - 1` (covering all affine forms
emitted by `simplifyConstraints`, including `(x + 1) * x = 0` and
`x * (x + (-1)) = 0`). -/
private def isPlusOne (a b : Polynomial F) : Bool :=
  let na := Polynomial.normalForm a
  let nb := Polynomial.normalForm b
  na == Polynomial.normalForm (.add nb (.const 1)) ||
  na == Polynomial.normalForm (.add (.const 1) nb) ||
  nb == Polynomial.normalForm (.add na (.const (-1))) ||
  nb == Polynomial.normalForm (.add (.const (-1)) na) ||
  nb == Polynomial.normalForm (.sub na (.const 1))

private theorem isPlusOne_sound {a b : Polynomial F} (h : isPlusOne a b = true) (x : Nat → F) :
    b.denote x = a.denote x - 1 := by
  unfold isPlusOne at h
  dsimp only at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((h1 | h2) | h3) | h4) | h5)
  · have hd := congrArg (fun p : Polynomial F => p.denote x) (poly_eq_of_beq h1)
    simp only [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] at hd
    exact eq_sub_of_add_eq hd.symm
  · have hd := congrArg (fun p : Polynomial F => p.denote x) (poly_eq_of_beq h2)
    simp only [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] at hd
    exact eq_sub_of_add_eq (by rw [add_comm]; exact hd.symm)
  · have hd := congrArg (fun p : Polynomial F => p.denote x) (poly_eq_of_beq h3)
    simp only [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] at hd
    simpa [sub_eq_add_neg] using hd
  · have hd := congrArg (fun p : Polynomial F => p.denote x) (poly_eq_of_beq h4)
    simp only [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] at hd
    simpa [sub_eq_add_neg, add_comm] using hd
  · have hd := congrArg (fun p : Polynomial F => p.denote x) (poly_eq_of_beq h5)
    simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] using hd

/-- Extract certified boolean expressions directly from `u * v = 0` constraints
in `cs` where `u = v + 1` or `v = u + 1`. -/
def extractDirectBools (cs : List (Polynomial F)) : List (UInt64 × Polynomial F) :=
  cs.flatMap fun q =>
    match q with
    | .mul u v =>
        let fromU :=
          if isPlusOne u v then
            let nu := Polynomial.normalForm u
            [(polyKey nu, nu)]
          else []
        let fromV :=
          if isPlusOne v u then
            let nv := Polynomial.normalForm v
            [(polyKey nv, nv)]
          else []
        fromU ++ fromV
    | _ => []

theorem extractDirectBools_sound {cs : List (Polynomial F)} {pair : UInt64 × Polynomial F}
    (hmem : pair ∈ extractDirectBools cs) {a : Nat → F} (valid : Satisfies cs a) :
    pair.2.denote a = 0 ∨ pair.2.denote a = 1 := by
  obtain ⟨q, hq, hmemq⟩ := List.mem_flatMap.mp hmem
  cases q with
  | mul u v =>
      simp only [] at hmemq
      have hqz : Scalar.Circuit.ArithExpr.denote a u * Scalar.Circuit.ArithExpr.denote a v = 0 :=
        valid (.mul u v) hq
      rcases List.mem_append.mp hmemq with hU | hV
      · by_cases hcond : isPlusOne u v = true
        · rw [if_pos hcond] at hU
          simp only [List.mem_singleton] at hU
          subst hU
          have hsub : Scalar.Circuit.ArithExpr.denote a v = Scalar.Circuit.ArithExpr.denote a u - 1 :=
            isPlusOne_sound hcond a
          rw [hsub, mul_eq_zero, sub_eq_zero] at hqz
          simpa [Polynomial.eval_normalForm] using hqz
        · rw [if_neg hcond] at hU; cases hU
      · by_cases hcond : isPlusOne v u = true
        · rw [if_pos hcond] at hV
          simp only [List.mem_singleton] at hV
          subst hV
          have hsub : Scalar.Circuit.ArithExpr.denote a u = Scalar.Circuit.ArithExpr.denote a v - 1 :=
            isPlusOne_sound hcond a
          rw [hsub, mul_eq_zero, sub_eq_zero] at hqz
          rcases hqz with h1 | h0
          · right; simpa [Polynomial.eval_normalForm] using h1
          · left; simpa [Polynomial.eval_normalForm] using h0
        · rw [if_neg hcond] at hV; cases hV
  | const _ | var _ | add _ _ | sub _ _ => simp at hmemq

/-- Build the pre-normalized exclusion context once for a chip's constraints `cs`. -/
def ExclCtx.ofConstraints (cs : List (Polynomial F)) : ExclCtx F :=
  let zeroNF := Polynomial.normalForm (.const (0 : F))
  let oneNF := Polynomial.normalForm (.const (1 : F))
  let normCs := cs.flatMap fun q =>
    let n1 := Polynomial.normalForm q
    let n2 := Polynomial.normalForm (.sub (.const 0) q)
    [(polyKey n1, n1), (polyKey n2, n2)]
  let bools := extractDirectBools cs
  let base : ExclCtx F := ⟨zeroNF, oneNF, normCs, bools, []⟩
  { base with parents := extractParents base cs }

theorem ExclCtx.ofConstraints_valid (cs : List (Polynomial F)) :
    (ExclCtx.ofConstraints cs).Valid cs := by
  let normCs := cs.flatMap fun q =>
    let n1 := Polynomial.normalForm q
    let n2 := Polynomial.normalForm (.sub (.const 0) q)
    [(polyKey n1, n1), (polyKey n2, n2)]
  have hnorm : ∀ pair ∈ normCs, ∀ a, Satisfies cs a → pair.2.denote a = 0 := by
    intro pair hmem a valid
    obtain ⟨q, hq, hpair⟩ := List.mem_flatMap.mp hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    rcases hpair with rfl | rfl
    · simpa [Polynomial.eval_normalForm] using valid q hq
    · have hqz := valid q hq
      simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote, hqz]
  have hbools : ∀ pair ∈ extractDirectBools cs, ∀ a, Satisfies cs a →
      pair.2.denote a = 0 ∨ pair.2.denote a = 1 :=
    fun pair hmem a valid => extractDirectBools_sound hmem valid
  have hbase : (ExclCtx.mk (Polynomial.normalForm (.const (0 : F)))
      (Polynomial.normalForm (.const (1 : F))) normCs (extractDirectBools cs) []).Valid cs :=
    ⟨rfl, rfl, hnorm, hbools, fun _ h => by cases h⟩
  refine ⟨rfl, rfl, hnorm, hbools, fun pair hmem a valid hne => ?_⟩
  exact extractParents_sound hbase hmem valid hne

/-- Walk up certified parent edges from `e` up to `fuel` steps, returning `e`
and all reached ancestors (every one is nonzero whenever `e` is nonzero). -/
def ExclCtx.ancestors (ctx : ExclCtx F) : Nat → Polynomial F → List (Polynomial F)
  | 0, e => [e]
  | fuel + 1, e =>
      let en := Polynomial.normalForm e
      let next := ctx.parents.filterMap fun (c, p) =>
        if Polynomial.normalForm c == en then some p else none
      e :: next.flatMap (ctx.ancestors fuel)

theorem ExclCtx.ancestors_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {a : Nat → F} (valid : Satisfies cs a) :
    ∀ (fuel : Nat) (e anc : Polynomial F),
      anc ∈ ctx.ancestors fuel e → e.denote a ≠ 0 → anc.denote a ≠ 0
  | 0, e, anc, hmem, hne => by
      simp only [ExclCtx.ancestors, List.mem_singleton] at hmem
      rwa [hmem]
  | fuel + 1, e, anc, hmem, hne => by
      simp only [ExclCtx.ancestors, List.mem_cons, List.mem_flatMap] at hmem
      rcases hmem with rfl | ⟨p, hp, hanc⟩
      · exact hne
      · obtain ⟨⟨c, p'⟩, hcp, hfilt⟩ := List.mem_filterMap.mp hp
        split at hfilt
        · rename_i hcn
          injection hfilt with hpp
          subst hpp
          have hce : c.denote a = e.denote a := denote_eq_of_nf_beq hcn a
          have hpne : p'.denote a ≠ 0 :=
            hctx.2.2.2.2 (c, p') hcp a valid (by rwa [hce])
          exact ctx.ancestors_sound hctx valid fuel p' anc hanc hpne
        · cases hfilt

/-- Recursive structural decomposition step of `isExclWith`. -/
def ExclCtx.isExclStep (ctx : ExclCtx F) (rec : Polynomial F → Polynomial F → Bool) :
    Polynomial F → Polynomial F → Bool
  | .add x y, e₂ => rec x e₂ && rec y e₂
  | e₁, .add x y => rec e₁ x && rec e₁ y
  | .mul x y, e₂ => rec x e₂ || rec y e₂
  | e₁, .mul x y => rec e₁ x || rec e₁ y
  | .sub (.const c) x, y =>
      c == 1 && Polynomial.normalForm x == Polynomial.normalForm y && ctx.isDirectBool y
  | y, .sub (.const c) x =>
      c == 1 && Polynomial.normalForm x == Polynomial.normalForm y && ctx.isDirectBool y
  | _, _ => false

private theorem ExclCtx.isExclStep_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {a : Nat → F} (valid : Satisfies cs a)
    {rec : Polynomial F → Polynomial F → Bool}
    (hrec : ∀ u v, rec u v = true → u.denote a * v.denote a = 0) :
    ∀ e₁ e₂, ctx.isExclStep rec e₁ e₂ = true → e₁.denote a * e₂.denote a = 0
  | .add x y, e₂, h => by
      simp only [ExclCtx.isExclStep, Bool.and_eq_true] at h
      change (x.denote a + y.denote a) * e₂.denote a = 0
      rw [add_mul, hrec x e₂ h.1, hrec y e₂ h.2, add_zero]
  | .const c, .add x y, h | .var c, .add x y, h | .sub c _, .add x y, h | .mul c _, .add x y, h => by
      simp only [ExclCtx.isExclStep, Bool.and_eq_true] at h
      change _ * (x.denote a + y.denote a) = 0
      rw [mul_add, hrec _ x h.1, hrec _ y h.2, add_zero]
  | .mul x y, .const c, h | .mul x y, .var c, h | .mul x y, .sub c _, h | .mul x y, .mul c _, h => by
      simp only [ExclCtx.isExclStep, Bool.or_eq_true] at h
      change (x.denote a * y.denote a) * _ = 0
      rcases h with h1 | h2
      · rw [mul_right_comm, hrec x _ h1, zero_mul]
      · rw [mul_assoc, hrec y _ h2, mul_zero]
  | .const c, .mul x y, h | .var c, .mul x y, h | .sub c _, .mul x y, h => by
      simp only [ExclCtx.isExclStep, Bool.or_eq_true] at h
      change _ * (x.denote a * y.denote a) = 0
      rcases h with h1 | h2
      · rw [← mul_assoc, hrec _ x h1, zero_mul]
      · rw [mul_comm (x.denote a) (y.denote a), ← mul_assoc, hrec _ y h2, zero_mul]
  | .sub (.const c) x, .const k, h | .sub (.const c) x, .var k, h | .sub (.const c) x, .sub k _, h => by
      simp only [ExclCtx.isExclStep, Bool.and_eq_true] at h
      obtain ⟨⟨hc1, hxy⟩, hbool⟩ := h
      have hcEq : c = 1 := beq_iff_eq.mp hc1
      subst hcEq
      have hx : Scalar.Circuit.ArithExpr.denote a x = Scalar.Circuit.ArithExpr.denote a _ :=
        denote_eq_of_nf_beq hxy a
      change (1 - Scalar.Circuit.ArithExpr.denote a x) * Scalar.Circuit.ArithExpr.denote a _ = 0
      rw [hx]
      rcases ctx.isDirectBool_sound hctx hbool valid with hb | hb
      · change Scalar.Circuit.ArithExpr.denote a _ = 0 at hb; simp [hb]
      · change Scalar.Circuit.ArithExpr.denote a _ = 1 at hb; simp [hb]
  | .const k, .sub (.const c) x, h | .var k, .sub (.const c) x, h
  | .sub (.var _) _, .sub (.const c) x, h | .sub (.add _ _) _, .sub (.const c) x, h
  | .sub (.sub _ _) _, .sub (.const c) x, h | .sub (.mul _ _) _, .sub (.const c) x, h => by
      simp only [ExclCtx.isExclStep, Bool.and_eq_true] at h
      obtain ⟨⟨hc1, hxy⟩, hbool⟩ := h
      have hcEq : c = 1 := beq_iff_eq.mp hc1
      subst hcEq
      have hx : Scalar.Circuit.ArithExpr.denote a x = Scalar.Circuit.ArithExpr.denote a _ :=
        denote_eq_of_nf_beq hxy a
      change Scalar.Circuit.ArithExpr.denote a _ * (1 - Scalar.Circuit.ArithExpr.denote a x) = 0
      rw [hx]
      rcases ctx.isDirectBool_sound hctx hbool valid with hb | hb
      · change Scalar.Circuit.ArithExpr.denote a _ = 0 at hb; simp [hb]
      · change Scalar.Circuit.ArithExpr.denote a _ = 1 at hb; simp [hb]
  | .sub (.var _) _, .const _, h | .sub (.var _) _, .var _, h
  | .sub (.var _) _, .sub (.var _) _, h | .sub (.var _) _, .sub (.add _ _) _, h
  | .sub (.var _) _, .sub (.sub _ _) _, h | .sub (.var _) _, .sub (.mul _ _) _, h
  | .sub (.add _ _) _, .const _, h | .sub (.add _ _) _, .var _, h
  | .sub (.add _ _) _, .sub (.var _) _, h | .sub (.add _ _) _, .sub (.add _ _) _, h
  | .sub (.add _ _) _, .sub (.sub _ _) _, h | .sub (.add _ _) _, .sub (.mul _ _) _, h
  | .sub (.sub _ _) _, .const _, h | .sub (.sub _ _) _, .var _, h
  | .sub (.sub _ _) _, .sub (.var _) _, h | .sub (.sub _ _) _, .sub (.add _ _) _, h
  | .sub (.sub _ _) _, .sub (.sub _ _) _, h | .sub (.sub _ _) _, .sub (.mul _ _) _, h
  | .sub (.mul _ _) _, .const _, h | .sub (.mul _ _) _, .var _, h
  | .sub (.mul _ _) _, .sub (.var _) _, h | .sub (.mul _ _) _, .sub (.add _ _) _, h
  | .sub (.mul _ _) _, .sub (.sub _ _) _, h | .sub (.mul _ _) _, .sub (.mul _ _) _, h
  | .const _, .const _, h | .const _, .var _, h
  | .const _, .sub (.var _) _, h | .const _, .sub (.add _ _) _, h
  | .const _, .sub (.sub _ _) _, h | .const _, .sub (.mul _ _) _, h
  | .var _, .const _, h | .var _, .var _, h
  | .var _, .sub (.var _) _, h | .var _, .sub (.add _ _) _, h
  | .var _, .sub (.sub _ _) _, h | .var _, .sub (.mul _ _) _, h => by
      simp [ExclCtx.isExclStep] at h

/-- Recognize a syntactic complement `1 - x` in any form produced by the
compiler (`1 - x`, `(-1) * x + 1`, `1 + (-1) * x`, `x * (-1) + 1`, `1 + x * (-1)`). -/
def complementOf : Polynomial F → Option (Polynomial F)
  | .sub (.const c) x => if c = 1 then some x else none
  | .add (.mul (.const c) x) (.const d) => if c = -1 && d = 1 then some x else none
  | .add (.mul x (.const c)) (.const d) => if c = -1 && d = 1 then some x else none
  | .add (.const d) (.mul (.const c) x) => if c = -1 && d = 1 then some x else none
  | .add (.const d) (.mul x (.const c)) => if c = -1 && d = 1 then some x else none
  | _ => none

theorem complementOf_sound {e x : Polynomial F} (h : complementOf e = some x) (a : Nat → F) :
    e.denote a = 1 - x.denote a := by
  unfold complementOf at h
  split at h
  · split at h
    · rename_i hc; injection h with hx; subst hc; subst hx; rfl
    · cases h
  · split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      injection h with hx; subst hx
      simp [Scalar.Circuit.ArithExpr.denote, hc.1, hc.2, sub_eq_add_neg, add_comm]
    · cases h
  · split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      injection h with hx; subst hx
      simp [Scalar.Circuit.ArithExpr.denote, hc.1, hc.2, sub_eq_add_neg, add_comm]
    · cases h
  · split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      injection h with hx; subst hx
      simp [Scalar.Circuit.ArithExpr.denote, hc.1, hc.2, sub_eq_add_neg]
    · cases h
  · split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      injection h with hx; subst hx
      simp [Scalar.Circuit.ArithExpr.denote, hc.1, hc.2, sub_eq_add_neg]
    · cases h
  · cases h

private def isComplementExcl (ctx : ExclCtx F) (e₁ e₂ : Polynomial F) : Bool :=
  match complementOf e₁ with
  | some x => Polynomial.normalForm x == Polynomial.normalForm e₂ && ctx.isDirectBool e₂
  | none => false

private theorem isComplementExcl_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e₁ e₂ : Polynomial F} (h : isComplementExcl ctx e₁ e₂ = true)
    {a : Nat → F} (valid : Satisfies cs a) : e₁.denote a * e₂.denote a = 0 := by
  unfold isComplementExcl at h
  cases hc : complementOf e₁ with
  | none => simp [hc] at h
  | some x =>
      simp only [hc, Bool.and_eq_true] at h
      rw [complementOf_sound hc a, denote_eq_of_nf_beq h.1 a]
      rcases ctx.isDirectBool_sound hctx h.2 valid with hb | hb <;> simp [hb]

/-- Check mutual exclusion (`e₁ * e₂ = 0`) using direct constraints, certified
choice-tree ancestry, complement, sum decomposition, and product inheritance. -/
def ExclCtx.isExclWith (ctx : ExclCtx F) : Nat → Polynomial F → Polynomial F → Bool
  | 0, e₁, e₂ => ctx.isDirectExcl e₁ e₂
  | fuel + 1, e₁, e₂ =>
      if ctx.isDirectExcl e₁ e₂ then true
      else if isComplementExcl ctx e₁ e₂ || isComplementExcl ctx e₂ e₁ then true
      else
        let a₁ := ctx.ancestors 8 e₁
        let a₂ := ctx.ancestors 8 e₂
        if a₁.any (fun x => a₂.any (ctx.isDirectExcl x)) then true
        else ctx.isExclStep (ctx.isExclWith fuel) e₁ e₂

theorem ExclCtx.isExclWith_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {a : Nat → F} (valid : Satisfies cs a) :
    ∀ (fuel : Nat) (e₁ e₂ : Polynomial F),
      ctx.isExclWith fuel e₁ e₂ = true → e₁.denote a * e₂.denote a = 0
  | 0, e₁, e₂, h => ctx.isDirectExcl_sound hctx h valid
  | fuel + 1, e₁, e₂, h => by
      unfold ExclCtx.isExclWith at h
      by_cases hdir : ctx.isDirectExcl e₁ e₂ = true
      · exact ctx.isDirectExcl_sound hctx hdir valid
      rw [if_neg hdir] at h
      by_cases hcomp : (isComplementExcl ctx e₁ e₂ || isComplementExcl ctx e₂ e₁) = true
      · rcases Bool.or_eq_true_iff.mp hcomp with h1 | h2
        · exact isComplementExcl_sound hctx h1 valid
        · rw [mul_comm]; exact isComplementExcl_sound hctx h2 valid
      rw [if_neg hcomp] at h
      dsimp only at h
      by_cases hanc : ((ctx.ancestors 8 e₁).any
          (fun x => (ctx.ancestors 8 e₂).any (ctx.isDirectExcl x))) = true
      · obtain ⟨x, hx, hya⟩ := List.any_eq_true.mp hanc
        obtain ⟨y, hy, hxy⟩ := List.any_eq_true.mp hya
        by_contra hmul
        have h1 : e₁.denote a ≠ 0 := left_ne_zero_of_mul hmul
        have h2 : e₂.denote a ≠ 0 := right_ne_zero_of_mul hmul
        have hxne := ctx.ancestors_sound hctx valid 8 e₁ x hx h1
        have hyne := ctx.ancestors_sound hctx valid 8 e₂ y hy h2
        exact mul_ne_zero hxne hyne (ctx.isDirectExcl_sound hctx hxy valid)
      rw [if_neg hanc] at h
      exact ctx.isExclStep_sound hctx valid (ctx.isExclWith_sound hctx valid fuel) e₁ e₂ h

def ExclCtx.isExcl (ctx : ExclCtx F) (e₁ e₂ : Polynomial F) : Bool :=
  ctx.isExclWith 8 e₁ e₂

theorem ExclCtx.isExcl_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e₁ e₂ : Polynomial F} (h : ctx.isExcl e₁ e₂ = true)
    {a : Nat → F} (valid : Satisfies cs a) : e₁.denote a * e₂.denote a = 0 :=
  ctx.isExclWith_sound hctx valid 8 e₁ e₂ h

/-- Check that `e` is boolean (`0` or `1`) on every assignment satisfying `cs`. -/
def ExclCtx.isBoolWith (ctx : ExclCtx F) : Nat → Polynomial F → Bool
  | 0, e => ctx.isDirectBool e
  | fuel + 1, e =>
      if ctx.isDirectBool e then true
      else match complementOf e with
      | some x => ctx.isBoolWith fuel x
      | none => match e with
        | .add x y =>
            ctx.isBoolWith fuel x && ctx.isBoolWith fuel y && ctx.isExclWith 8 x y
        | .mul x y =>
            ctx.isBoolWith fuel x && ctx.isBoolWith fuel y
        | _ => false

theorem ExclCtx.isBoolWith_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {a : Nat → F} (valid : Satisfies cs a) :
    ∀ (fuel : Nat) (e : Polynomial F),
      ctx.isBoolWith fuel e = true → e.denote a = 0 ∨ e.denote a = 1
  | 0, e, h => ctx.isDirectBool_sound hctx h valid
  | fuel + 1, e, h => by
      unfold ExclCtx.isBoolWith at h
      by_cases hdir : ctx.isDirectBool e = true
      · exact ctx.isDirectBool_sound hctx hdir valid
      rw [if_neg hdir] at h
      cases hcomp : complementOf e with
      | some x =>
          simp only [hcomp] at h
          rw [complementOf_sound hcomp a]
          rcases ctx.isBoolWith_sound hctx valid fuel x h with hx0 | hx1
          · right; simp [hx0]
          · left; simp [hx1]
      | none =>
          simp only [hcomp] at h
          cases e with
          | add x y =>
              simp only [Bool.and_eq_true] at h
              obtain ⟨⟨hx, hy⟩, hex⟩ := h
              have hbx := ctx.isBoolWith_sound hctx valid fuel x hx
              have hby := ctx.isBoolWith_sound hctx valid fuel y hy
              have hmul := ctx.isExclWith_sound hctx valid 8 x y hex
              change x.denote a + y.denote a = 0 ∨ x.denote a + y.denote a = 1
              rcases hbx with hx0 | hx1 <;> rcases hby with hy0 | hy1
              · left; simp [hx0, hy0]
              · right; simp [hx0, hy1]
              · right; simp [hx1, hy0]
              · simp [hx1, hy1] at hmul
          | mul x y =>
              simp only [Bool.and_eq_true] at h
              change x.denote a * y.denote a = 0 ∨ x.denote a * y.denote a = 1
              rcases ctx.isBoolWith_sound hctx valid fuel x h.1 with hx | hx <;>
                rcases ctx.isBoolWith_sound hctx valid fuel y h.2 with hy | hy <;>
                simp [hx, hy]
          | const _ | var _ | sub _ _ => simp at h

def ExclCtx.isBool (ctx : ExclCtx F) (e : Polynomial F) : Bool :=
  ctx.isBoolWith 8 e

theorem ExclCtx.isBool_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e : Polynomial F} (h : ctx.isBool e = true)
    {a : Nat → F} (valid : Satisfies cs a) : e.denote a = 0 ∨ e.denote a = 1 :=
  ctx.isBoolWith_sound hctx valid 8 e h

private def isZeroWhenCompOn (ctx : ExclCtx F) (e p : Polynomial F) : Bool :=
  match complementOf e with
  | some c => ctx.isExcl c p
  | none => false

private theorem isZeroWhenCompOn_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e p : Polynomial F} (h : isZeroWhenCompOn ctx e p = true)
    {a : Nat → F} (valid : Satisfies cs a) (he0 : e.denote a = 0) : p.denote a = 0 := by
  unfold isZeroWhenCompOn at h
  cases hc : complementOf e with
  | none => simp [hc] at h
  | some c =>
      simp only [hc] at h
      have hce : 1 - c.denote a = 0 := (complementOf_sound hc a).symm.trans he0
      have hc1 : c.denote a = 1 := (sub_eq_zero.mp hce).symm
      have hmul := ctx.isExcl_sound hctx h valid
      simpa [hc1] using hmul

/-- Check that `p` vanishes whenever `e` vanishes (`e = 0 → p = 0`) on every
assignment satisfying `cs`. Lets already-gated deg-2 lookup arguments avoid an
extra multiplication by `e` during `C2` compaction. -/
def ExclCtx.isZeroWhenOffWith (ctx : ExclCtx F) : Nat → Polynomial F → Polynomial F → Bool
  | 0, _, p => Polynomial.normalForm p == ctx.zeroNF
  | fuel + 1, e, p =>
      if Polynomial.normalForm p == ctx.zeroNF then true
      else if Polynomial.normalForm p == Polynomial.normalForm e then true
      else if isZeroWhenCompOn ctx e p then true
      else if ctx.isZeroOf (.mul (.sub (.const 1) e) p) ||
              ctx.isZeroOf (.mul p (.sub (.const 1) e)) then true
      else if (ctx.ancestors 8 p).any (fun anc => Polynomial.normalForm anc == Polynomial.normalForm e) then true
      else match p with
      | .mul x y =>
          ctx.isZeroWhenOffWith fuel e x || ctx.isZeroWhenOffWith fuel e y
      | .add x y =>
          ctx.isZeroWhenOffWith fuel e x && ctx.isZeroWhenOffWith fuel e y
      | .sub x y =>
          ctx.isZeroWhenOffWith fuel e x && ctx.isZeroWhenOffWith fuel e y
      | _ =>
          match e with
          | .add e₁ e₂ =>
              if ctx.isBoolWith 6 e₁ && ctx.isBoolWith 6 e₂ && ctx.isExclWith 8 e₁ e₂ then
                ctx.isZeroWhenOffWith fuel e₁ p || ctx.isZeroWhenOffWith fuel e₂ p
              else false
          | _ => false

theorem ExclCtx.isZeroWhenOffWith_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {a : Nat → F} (valid : Satisfies cs a) :
    ∀ (fuel : Nat) (e p : Polynomial F),
      ctx.isZeroWhenOffWith fuel e p = true → e.denote a = 0 → p.denote a = 0
  | 0, _, p, h, _ => by
      have hd := congrArg (fun x : Polynomial F => x.denote a) ((poly_eq_of_beq h).trans hctx.1)
      simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] using hd
  | fuel + 1, e, p, h, he0 => by
      unfold ExclCtx.isZeroWhenOffWith at h
      by_cases hp0 : (Polynomial.normalForm p == ctx.zeroNF) = true
      · have hd := congrArg (fun x : Polynomial F => x.denote a) ((poly_eq_of_beq hp0).trans hctx.1)
        simpa [Polynomial.eval_normalForm, Scalar.Circuit.ArithExpr.denote] using hd
      rw [if_neg hp0] at h
      by_cases hpe : (Polynomial.normalForm p == Polynomial.normalForm e) = true
      · exact (denote_eq_of_nf_beq hpe a).trans he0
      rw [if_neg hpe] at h
      by_cases hcomp : isZeroWhenCompOn ctx e p = true
      · exact isZeroWhenCompOn_sound hctx hcomp valid he0
      rw [if_neg hcomp] at h
      by_cases hguard : (ctx.isZeroOf (.mul (.sub (.const 1) e) p) ||
          ctx.isZeroOf (.mul p (.sub (.const 1) e))) = true
      · rcases Bool.or_eq_true_iff.mp hguard with h1 | h2
        · have hz := ctx.isZeroOf_sound hctx h1 valid
          simpa [Scalar.Circuit.ArithExpr.denote, he0] using hz
        · have hz := ctx.isZeroOf_sound hctx h2 valid
          simpa [Scalar.Circuit.ArithExpr.denote, he0] using hz
      rw [if_neg hguard] at h
      by_cases hanc : ((ctx.ancestors 8 p).any
          (fun anc => Polynomial.normalForm anc == Polynomial.normalForm e)) = true
      · obtain ⟨anc, hmem, hEq⟩ := List.any_eq_true.mp hanc
        have hance : anc.denote a = e.denote a := denote_eq_of_nf_beq hEq a
        by_contra hpne
        exact ctx.ancestors_sound hctx valid 8 p anc hmem hpne (hance.trans he0)
      rw [if_neg hanc] at h
      cases p with
      | mul x y =>
          simp only [Bool.or_eq_true] at h
          change ArithExpr.denote a x * ArithExpr.denote a y = 0
          rcases h with hx | hy
          · rw [ctx.isZeroWhenOffWith_sound hctx valid fuel e x hx he0, zero_mul]
          · rw [ctx.isZeroWhenOffWith_sound hctx valid fuel e y hy he0, mul_zero]
      | add x y =>
          simp only [Bool.and_eq_true] at h
          change ArithExpr.denote a x + ArithExpr.denote a y = 0
          rw [ctx.isZeroWhenOffWith_sound hctx valid fuel e x h.1 he0,
              ctx.isZeroWhenOffWith_sound hctx valid fuel e y h.2 he0, add_zero]
      | sub x y =>
          simp only [Bool.and_eq_true] at h
          change ArithExpr.denote a x - ArithExpr.denote a y = 0
          rw [ctx.isZeroWhenOffWith_sound hctx valid fuel e x h.1 he0,
              ctx.isZeroWhenOffWith_sound hctx valid fuel e y h.2 he0, sub_zero]
      | const _ | var _ =>
          cases e with
          | add e₁ e₂ =>
              by_cases hcond : (ctx.isBoolWith 6 e₁ && ctx.isBoolWith 6 e₂ && ctx.isExclWith 8 e₁ e₂) = true
              · simp only [hcond, ↓reduceIte, Bool.false_eq_true] at h
                simp only [Bool.and_eq_true] at hcond
                obtain ⟨⟨hb1, hb2⟩, hex⟩ := hcond
                have h1 : Scalar.Circuit.ArithExpr.denote a e₁ = 0 ∨ Scalar.Circuit.ArithExpr.denote a e₁ = 1 :=
                  ctx.isBoolWith_sound hctx valid 6 e₁ hb1
                have h2 : Scalar.Circuit.ArithExpr.denote a e₂ = 0 ∨ Scalar.Circuit.ArithExpr.denote a e₂ = 1 :=
                  ctx.isBoolWith_sound hctx valid 6 e₂ hb2
                have hmul : Scalar.Circuit.ArithExpr.denote a e₁ * Scalar.Circuit.ArithExpr.denote a e₂ = 0 :=
                  ctx.isExclWith_sound hctx valid 8 e₁ e₂ hex
                have hsum0 : Scalar.Circuit.ArithExpr.denote a e₁ + Scalar.Circuit.ArithExpr.denote a e₂ = 0 := he0
                have ⟨he1, he2⟩ : Scalar.Circuit.ArithExpr.denote a e₁ = 0 ∧ Scalar.Circuit.ArithExpr.denote a e₂ = 0 := by
                  rcases h1 with h10 | h11 <;> rcases h2 with h20 | h21
                  · exact ⟨h10, h20⟩
                  · rw [h10, h21, zero_add] at hsum0; exact absurd hsum0 one_ne_zero
                  · rw [h11, h20, add_zero] at hsum0; exact absurd hsum0 one_ne_zero
                  · rw [h11, h21, one_mul] at hmul; exact absurd hmul one_ne_zero
                rcases Bool.or_eq_true_iff.mp h with hleft | hright
                · exact ctx.isZeroWhenOffWith_sound hctx valid fuel e₁ _ hleft he1
                · exact ctx.isZeroWhenOffWith_sound hctx valid fuel e₂ _ hright he2
              · simp [hcond] at h
          | const _ | var _ | sub _ _ | mul _ _ => simp at h

def ExclCtx.isZeroWhenOff (ctx : ExclCtx F) (e p : Polynomial F) : Bool :=
  ctx.isZeroWhenOffWith 8 e p

theorem ExclCtx.isZeroWhenOff_sound {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e p : Polynomial F} (h : ctx.isZeroWhenOff e p = true)
    {a : Nat → F} (valid : Satisfies cs a) (he0 : e.denote a = 0) : p.denote a = 0 :=
  ctx.isZeroWhenOffWith_sound hctx valid 8 e p h he0

/-- Canonical gated argument word for intra-chip raw-packet compaction (`C2`):
leaves `p` unmultiplied when `isZeroWhenOff` already proves `e = 0 → p = 0`,
and otherwise gates by `e * p`. -/
def ExclCtx.gatedWord (ctx : ExclCtx F) (e p : Polynomial F) : Polynomial F :=
  if ctx.isZeroWhenOff e p then p else Polynomial.simplify (.mul e p)

theorem ExclCtx.gatedWord_active {ctx : ExclCtx F} {e p : Polynomial F} {a : Nat → F}
    (he1 : e.denote a = 1) :
    (ctx.gatedWord e p).denote a = p.denote a := by
  unfold ExclCtx.gatedWord
  split
  · rfl
  · simp [Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, he1]

theorem ExclCtx.gatedWord_inactive {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {e p : Polynomial F} {a : Nat → F}
    (valid : Satisfies cs a) (he0 : e.denote a = 0) :
    (ctx.gatedWord e p).denote a = 0 := by
  unfold ExclCtx.gatedWord
  split
  · exact ctx.isZeroWhenOff_sound hctx (by assumption) valid he0
  · simp [Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, he0]

/-- Check pairwise mutual exclusion across every distinct pair using `ctx.isExcl`. -/
def ExclCtx.allPairwiseExcl (ctx : ExclCtx F) : List (Polynomial F) → Bool
  | [] => true
  | x :: xs => xs.all (ctx.isExcl x) && ctx.allPairwiseExcl xs

private theorem sum_map_cons_denote (f : Nat → Polynomial F) (k : Nat) (ks : List Nat) (a : Nat → F) :
    (sum ((k :: ks).map f)).denote a = (f k).denote a + (sum (ks.map f)).denote a := by
  simp only [sum_denote, List.map_cons, List.sum_cons]

private theorem sum_map_eq_zero_of_all {f : Nat → Polynomial F} {ks : List Nat} {a : Nat → F}
    (h : ∀ k ∈ ks, (f k).denote a = 0) : (sum (ks.map f)).denote a = 0 := by
  rw [sum_denote]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  exact h k hk

/-- Master bucket-superposition theorem for `C2` intra-chip raw-packet compaction:
if every lookup in `B` has a certified boolean enable and all pairs in `B` are
certified mutually exclusive under `cs`, then on any satisfying assignment `a`,
either all enables in `B` vanish (and the summed enable and every summed
`gatedWord` vanish), or a unique `k ∈ B` has enable `1` (and the summed enable
is `1` and every summed `gatedWord` equals `f k`). -/
theorem ExclCtx.allPairwiseExcl_cases {ctx : ExclCtx F} {cs : List (Polynomial F)}
    (hctx : ctx.Valid cs) {enables : Nat → Polynomial F} {B : List Nat}
    (hbool : ∀ k ∈ B, ctx.isBool (enables k) = true)
    (hexcl : ctx.allPairwiseExcl (B.map enables) = true)
    {a : Nat → F} (valid : Satisfies cs a) :
    ((∀ k ∈ B, (enables k).denote a = 0) ∧
      (sum (B.map enables)).denote a = 0 ∧
      ∀ (f : Nat → Polynomial F),
        (sum (B.map fun k => ctx.gatedWord (enables k) (f k))).denote a = 0) ∨
    (∃ k ∈ B,
      (enables k).denote a = 1 ∧
      (∀ k' ∈ B, k' ≠ k → (enables k').denote a = 0) ∧
      (sum (B.map enables)).denote a = 1 ∧
      ∀ (f : Nat → Polynomial F),
        (sum (B.map fun k => ctx.gatedWord (enables k) (f k))).denote a = (f k).denote a) := by
  induction B with
  | nil =>
      left
      refine ⟨(fun _ h => by cases h), ?_, fun _ => ?_⟩ <;>
        simp [sum_denote]
  | cons k ks ih =>
      simp only [List.map_cons, ExclCtx.allPairwiseExcl, Bool.and_eq_true, List.all_eq_true,
        List.mem_map] at hexcl
      have hhead : ∀ k' ∈ ks, ctx.isExcl (enables k) (enables k') = true := fun k' hk' =>
        hexcl.1 _ ⟨k', hk', rfl⟩
      have hbk := ctx.isBool_sound hctx (hbool k List.mem_cons_self) valid
      rcases hbk with hk0 | hk1
      · have hih := ih (fun k' hk' => hbool k' (List.mem_cons_of_mem _ hk')) hexcl.2
        rcases hih with ⟨hall0, hsum0, hgate0⟩ | ⟨k0, hk0mem, hk01, hrest0, hsum1, hgate1⟩
        · left
          refine ⟨?_, ?_, ?_⟩
          · intro k' hk'
            rcases List.mem_cons.mp hk' with rfl | hk'
            · exact hk0
            · exact hall0 k' hk'
          · rw [sum_map_cons_denote, hk0, hsum0, zero_add]
          · intro f
            rw [sum_map_cons_denote, ctx.gatedWord_inactive hctx valid hk0, hgate0 f, zero_add]
        · right
          refine ⟨k0, List.mem_cons_of_mem _ hk0mem, hk01, ?_, ?_, ?_⟩
          · intro k' hk' hne
            rcases List.mem_cons.mp hk' with rfl | hk'
            · exact hk0
            · exact hrest0 k' hk' hne
          · rw [sum_map_cons_denote, hk0, hsum1, zero_add]
          · intro f
            rw [sum_map_cons_denote, ctx.gatedWord_inactive hctx valid hk0, hgate1 f, zero_add]
      · right
        have hks0 : ∀ k' ∈ ks, (enables k').denote a = 0 := by
          intro k' hk'
          have hmul := ctx.isExcl_sound hctx (hhead k' hk') valid
          simpa [hk1] using hmul
        refine ⟨k, List.mem_cons_self, hk1, ?_, ?_, ?_⟩
        · intro k' hk' hne
          rcases List.mem_cons.mp hk' with rfl | hk'
          · exact absurd rfl hne
          · exact hks0 k' hk'
        · rw [sum_map_cons_denote, hk1, sum_map_eq_zero_of_all hks0, add_zero]
        · intro f
          rw [sum_map_cons_denote, ctx.gatedWord_active hk1,
            sum_map_eq_zero_of_all (fun k' hk' => ctx.gatedWord_inactive hctx valid (hks0 k' hk')),
            add_zero]

end Aiur.Optimized.Grouping
