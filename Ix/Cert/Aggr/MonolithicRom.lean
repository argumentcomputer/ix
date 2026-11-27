import CertiFriProofs.Theory.Oracle.FiatShamir
import CertiFriProofs.Theory.Oracle.Collision
import Ix.Cert.Aggr.Shapes

/-! # Monolithic Single-Oracle ROM Extraction for Multi-Node Aggregation (`Ix.Cert.Aggr.MonolithicRom`)

Eliminates the `-log₂ M` union-bound penalty of `Ix.Cert.Aggr.tree_rom_error_bound`
(`M * Q * ε_max`) by modeling straight-line single-oracle extraction over ONE shared
random-oracle log `l` (no rewinding, directly within `CertiFri.Oracle.OracleComp`):

1. **Unique Instance Prefixing (`ProofInstance`, `MultiQuery`, `MultiAnswer`):**
   Every challenge query `.chal inst t m` pins a unique `(vkDigest, claims, commitments)`
   prefix `inst`, so each adversary query targets at most ONE verification instance and ONE
   round. Consequently, the per-query bad-event probability for the global flip predicate
   `GlobalFlip` across ALL `M` nodes is bounded by `ε_max` — **NOT** `M * ε_max`.
2. **Straight-Line Single-Log Multi-Node Extraction (`monolithic_doomed_of_supports`,
   `monolithic_multiNode_rom_sound`, `monolithic_multiNode_rom_sound_collision`):**
   Over an `M`-verification aggregation DAG/tree run against the same shared oracle
   (`Q` adversary queries + `M_verif` total verifier queries, `N = Q + M_verif`), global
   multi-node forgery probability satisfies:
   $$\Pr[\exists k \in \mathrm{Fin}\; M,\; \text{node } k \text{ forges}] \le
     (Q + M_{\text{verif}}) \cdot \varepsilon_{\max} + \frac{c \cdot N^2}{|D|}$$
   (with NO `M * Q` factor!).
3. **Composition with 19-Shape Aggregation (`monolithic_aggrTree_rom_sound`):**
   Upgrades `AcceptedAggrTree` soundness with the monolithic single-oracle bound.
4. **Concrete `GoldilocksExt3` (`|F| ≥ 2^191`) + RFC 7693 `BLAKE2b-512` (`|D| = 2^512`, `c = 3/2`)
   128-Bit Post-Quantum Bounds, Strict Comparison vs Union Bound, and Negative Controls:**
   - `monolithic_goldilocksExt3_blake2b512_rate_128`: `≤ N / 2^128` for all `N = Q + M_verif ≤ 2^128`
     with `M_verif ≤ 2^20`.
   - `monolithic_goldilocksExt3_blake2b512_concrete_prob_128`: literal `≤ 1 / 2^128` bound.
   - `monolithic_strictly_tighter_than_union_bound` & `monolithic_beats_union_bound_2_pow_20`.
   - Negative controls rejecting `Fp^2` (`negControl_fp2_below_128`) and 32-byte digests at
     `N = 2^128` (`negControl_digest32_saturates_at_2_128`).
   - Note: `BLAKE3-XOF48`/`BLAKE3-XOF64` are excluded from concrete 128-bit PQ instantiation
     because BLAKE3's 256-bit internal `cv` caps concrete BHT collision resistance at `85.3b`,
     whereas RFC 7693 `BLAKE2b-512` has a true 512-bit internal state (`170.7b` BHT / `204.8b` CNS
     / `256b` Grover). Production 128-bit classical deployments continue to use 32-byte `BLAKE3-256`.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`,
strictly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ix.Cert.Aggr.MonolithicRom

open CertiFri.Oracle
open CertiFri.Oracle.OracleComp

universe u v u'

/-! ## 1. Domain-Separated Proof Instances & Shared Multi-Node Random Oracle -/

/-- Unique domain-separated prefix fixing a recursive proof instance inside a shared
random oracle: `(vkDigest, claims, commitments)`. Every Fiat–Shamir challenge query carries
its exact `ProofInstance`, so no single oracle query can simultaneously target two distinct
nodes of an aggregation DAG/tree. -/
structure ProofInstance (Vk Claims Comm : Type u) where
  vkDigest    : Vk
  claims      : Claims
  commitments : Comm
  deriving DecidableEq, Repr

/-- Queries to the single shared random oracle across an arbitrary multi-node aggregation
DAG/tree:
- `chal inst t m`: Fiat–Shamir challenge query for round `i` of instance `inst`,
- `hash x`: Merkle / sponge hash query. -/
inductive MultiQuery (Inst Msg : Type u) (Chal : ℕ → Type v) (X' : Type u') : Type (max u v u')
  | chal (inst : Inst) {i : ℕ} (t : Transcript Msg Chal i) (m : Msg) : MultiQuery Inst Msg Chal X'
  | hash (x : X') : MultiQuery Inst Msg Chal X'

/-- Answer type family for `MultiQuery`. -/
def MultiAnswer {Inst Msg : Type u} (Chal : ℕ → Type v) {X' : Type u'} (Y' : X' → Type v) :
    MultiQuery Inst Msg Chal X' → Type v
  | .chal _ (i := i) _ _ => Chal i
  | .hash x => Y' x

instance {Inst Msg : Type u} {Chal : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}
    [∀ i, Fintype (Chal i)] [∀ x, Fintype (Y' x)] :
    ∀ x : MultiQuery Inst Msg Chal X', Fintype (MultiAnswer Chal Y' x)
  | .chal _ (i := i) _ _ => inferInstanceAs (Fintype (Chal i))
  | .hash x => inferInstanceAs (Fintype (Y' x))

instance {Inst Msg : Type u} {Chal : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}
    [∀ i, Nonempty (Chal i)] [∀ x, Nonempty (Y' x)] :
    ∀ x : MultiQuery Inst Msg Chal X', Nonempty (MultiAnswer Chal Y' x)
  | .chal _ (i := i) _ _ => inferInstanceAs (Nonempty (Chal i))
  | .hash x => inferInstanceAs (Nonempty (Y' x))

instance {Inst Msg : Type u} {Chal : ℕ → Type v} {X' : Type u'}
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X'] :
    DecidableEq (MultiQuery Inst Msg Chal X')
  | .chal inst₁ (i := i) t₁ m₁, .chal inst₂ (i := j) t₂ m₂ =>
    if hi : i = j then by
      subst hi
      exact decidable_of_iff (inst₁ = inst₂ ∧ t₁ = t₂ ∧ m₁ = m₂)
        (by rw [MultiQuery.chal.injEq]; simp)
    else isFalse fun h => by cases h; exact hi rfl
  | .chal _ _ _, .hash _ => isFalse fun h => by cases h
  | .hash _, .chal _ _ _ => isFalse fun h => by cases h
  | .hash x₁, .hash x₂ => decidable_of_iff (x₁ = x₂) (by rw [MultiQuery.hash.injEq])

/-! ## 2. Global Single-Oracle Flip Bad Event & Straight-Line Single-Log Extraction -/

section MonolithicExtraction

variable {Inst Msg : Type u} {Chal : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}

/-- Family of round-by-round sound protocols indexed by proof instance `inst : Inst`,
each having `r inst` rounds and per-round error `ε inst i`. -/
def MultiRbrSound [∀ i, Fintype (Chal i)]
    (r : Inst → ℕ)
    (doomed : Inst → ∀ i, Transcript Msg Chal i → Prop)
    (ε : Inst → ℕ → ℝ) : Prop :=
  ∀ inst : Inst, RbrSound (r inst) (doomed inst) (ε inst)

/-- **Global single-oracle state-flip predicate (`GlobalFlip`):**
A query `x` with answer `y` flips the state of the unique instance `inst` named by `x`.
Because `.chal inst t m` fixes a single `inst` and a single round `i`, its fraction of bad
answers is at most `ε inst i ≤ εmax` — with **NO** factor of `M`! -/
def GlobalFlip (r : Inst → ℕ) (doomed : Inst → ∀ i, Transcript Msg Chal i → Prop)
    (x : MultiQuery Inst Msg Chal X') : MultiAnswer Chal Y' x → Prop :=
  match x with
  | .chal inst (i := i) t m =>
    fun c => i < r inst ∧ doomed inst i t ∧ ¬ doomed inst (i + 1) (t.snoc m c)
  | .hash _ => fun _ => False

/-- **Key Zero-Factor Lemma (`fractionLE_globalFlip`):**
Under `MultiRbrSound` with uniform per-round bound `εmax ≥ 0`, for EVERY query `x` to the
shared random oracle, at most a fraction `εmax` of answers triggers `GlobalFlip` (independent
of the number of nodes `M` in the aggregation DAG/tree!). -/
theorem fractionLE_globalFlip [∀ i, Fintype (Chal i)] [∀ x, Fintype (Y' x)]
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax) :
    ∀ x : MultiQuery Inst Msg Chal X', FractionLE (GlobalFlip (Y' := Y') r doomed x) εmax
  | .hash _ => FractionLE.false.mono_right h0
  | .chal inst (i := i) t m => by
    by_cases hcond : i < r inst ∧ doomed inst i t
    · have hfrac := hsound inst i hcond.1 t m hcond.2
      exact (hfrac.mono_right (hε inst i hcond.1)).mono_left fun c hc => hc.2.2
    · refine (FractionLE.false.mono_right h0).mono_left fun c hc => ?_
      exact hcond ⟨hc.1, hc.2.1⟩

/-- Transcript `t` of proof instance `inst` is supported by the shared oracle log `l`:
every round `j < i` of `t` was answered in `l` at query `.chal inst t_prefix m_j`. -/
def MultiSupports (inst : Inst) :
    ∀ {i : ℕ}, Transcript Msg Chal i → Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop
  | _, .nil, _ => True
  | _, .snoc t m c, l =>
    MultiSupports inst t l ∧ ⟨MultiQuery.chal inst t m, c⟩ ∈ l

/-- **Straight-Line Single-Log Extraction Lemma (`monolithic_doomed_of_supports`):**
In ANY shared random-oracle log `l` containing no `GlobalFlip` entry, EVERY transcript `t`
of EVERY instance `inst` supported by `l` (starting from `doomed inst 0 .nil`) remains doomed!
No rewinding and no per-node union bound is required. -/
theorem monolithic_doomed_of_supports
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {l : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y')}
    (hno : ¬ HasBad (fun _ => GlobalFlip r doomed) l)
    (inst : Inst) (hnil : doomed inst 0 .nil) :
    ∀ {i : ℕ} (_hi : i ≤ r inst) (t : Transcript Msg Chal i),
      MultiSupports inst t l → doomed inst i t
  | 0, _, .nil, _ => hnil
  | i + 1, hi, .snoc t m c, ⟨hsupp, hmem⟩ => by
    have hprev : doomed inst i t :=
      monolithic_doomed_of_supports hno inst hnil (Nat.le_of_succ_le hi) t hsupp
    by_contra hnot
    apply hno
    rw [hasBad_const_iff]
    exact ⟨⟨MultiQuery.chal inst t m, c⟩, hmem, hi, hprev, hnot⟩

private theorem sum_range_two_mul_cast (c : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (2 * c) * (i : ℝ) = c * (N : ℝ) * ((N : ℝ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_range_const_cast (εmax : ℝ) (N : ℕ) :
    ∑ _i ∈ Finset.range N, εmax = (N : ℝ) * εmax := by
  simp [Finset.sum_const, nsmul_eq_mul]

/-- **Monolithic Single-Oracle Multi-Node ROM Soundness (`monolithic_multiNode_rom_sound`):**
Consider an arbitrary `M`-node aggregation DAG/tree verified against a single shared random
oracle:
- Adversary `adv` makes at most `Q` queries (`adv.QueryBound Q`), outputting an arbitrary
  witness `a : A` specifying `M` verification nodes `instOf a : Fin M → Inst` and their
  transcripts;
- `verifyAll a` runs all `M` node verifications against the **same shared oracle** using at
  most `M_verif` total verifier queries (`∀ a, (verifyAll a).QueryBound M_verif`);
- `hashBad` models hash/sponge binding failure with per-query fraction
  `≤ (2 * c * l.length) / Fintype.card D` (`c = 1/2` for plain Merkle collisions, `c = 3/2`
  for incremental sponge chaining);
- Whenever any node `k : Fin M` forges (`NodeForges b k l'`), the shared log `l'` supports
  node `k`'s transcript from a doomed root while acceptance implies `¬ doomed` absent `hashBad`.

Then the probability that **ANY** node `k : Fin M` forges is bounded by:
$$(Q + M_{\text{verif}}) \cdot \varepsilon_{\max} + \frac{c \cdot ((Q : \mathbb{R}) + M_{\text{verif}})^2}{|D|}$$
with **NO `M * Q` factor** (completely eliminating the `-log₂ M` union-bound penalty!). -/
theorem monolithic_multiNode_rom_sound
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type*} [Fintype D] [Nonempty D]
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax c : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax) (hc0 : 0 ≤ c)
    (hashBad : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') →
      (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Prop)
    (hHashBad : ∀ l x, l.dlookup x = none →
      FractionLE (hashBad l x) ((2 * c) * (l.length : ℝ) / (Fintype.card D : ℝ)))
    {A B : Type*} {M : ℕ}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (NodeForges : B → Fin M → Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin M, NodeForges b k l') →
      ¬ HasBad hashBad l' →
      ∃ (inst : Inst) (t : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst t l' ∧ ¬ doomed inst (r inst) t) :
    prob (fun b l' => ∃ k : Fin M, NodeForges b k l') (adv.bind verifyAll) [] ≤
      ((Q + M_verif : ℕ) : ℝ) * εmax +
        c * ((Q + M_verif : ℕ) : ℝ) ^ 2 / (Fintype.card D : ℝ) := by
  have hQ : (adv.bind verifyAll).QueryBound (Q + M_verif) := hadv.bind hver
  have hImp : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin M, NodeForges b k l') →
      HasBad (fun _ => GlobalFlip r doomed) l' ∨ HasBad hashBad l' := by
    intro b l' hout hforge
    by_cases hH : HasBad hashBad l'
    · exact Or.inr hH
    · left
      by_contra hnoFlip
      obtain ⟨inst, t, hnil, hsupp, hnot⟩ := hExtract b l' hout hforge hH
      exact hnot (monolithic_doomed_of_supports hnoFlip inst hnil (le_refl _) t hsupp)
  have hSplit := prob_le_add_of_outcome hImp
  have hFlipBound :
      prob (fun _ l' => HasBad (fun _ => GlobalFlip r doomed) l') (adv.bind verifyAll) [] ≤
        ((Q + M_verif : ℕ) : ℝ) * εmax := by
    have h := prob_hasBad_le (bad := fun _ => GlobalFlip r doomed) (ε := fun _ => εmax)
      (fun _ => h0)
      (fun _ x _ => fractionLE_globalFlip hsound hε h0 x) hQ
    rwa [sum_range_const_cast] at h
  have hHashBound :
      prob (fun _ l' => HasBad hashBad l') (adv.bind verifyAll) [] ≤
        c * ((Q + M_verif : ℕ) : ℝ) ^ 2 / (Fintype.card D : ℝ) := by
    have hDpos : (0 : ℝ) < (Fintype.card D : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have h := prob_hasBad_le (bad := hashBad)
      (ε := fun n => (2 * c) * (n : ℝ) / (Fintype.card D : ℝ))
      (fun n => by positivity) hHashBad hQ
    have hsum :
        ∑ i ∈ Finset.range (Q + M_verif), (2 * c) * (i : ℝ) / (Fintype.card D : ℝ) =
          c * ((Q + M_verif : ℕ) : ℝ) * (((Q + M_verif : ℕ) : ℝ) - 1) / (Fintype.card D : ℝ) := by
      rw [← Finset.sum_div, sum_range_two_mul_cast]
    have hle :
        c * ((Q + M_verif : ℕ) : ℝ) * (((Q + M_verif : ℕ) : ℝ) - 1) / (Fintype.card D : ℝ) ≤
          c * ((Q + M_verif : ℕ) : ℝ) ^ 2 / (Fintype.card D : ℝ) := by
      apply div_le_div_of_nonneg_right _ hDpos.le
      have hN0 : (0 : ℝ) ≤ ((Q + M_verif : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact h.trans (hsum.le.trans hle)
  exact hSplit.trans (add_le_add hFlipBound hHashBound)

/-- Observation lift of hash-oracle digests onto `MultiQuery` (`chal` queries are unobserved). -/
def liftMultiObs {Z : Type*} (obs : (x : X') → Y' x → Option Z) :
    (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Option Z
  | .chal _ _ _, _ => none
  | .hash x, y => obs x y

/-- **Specialized Collision-Resistance Monolithic Soundness (`monolithic_multiNode_rom_sound_collision`):**
Instantiates `monolithic_multiNode_rom_sound` directly on CertiFRI's concrete `LogCollision`
(`HitsDigest`, prefactor `c = 1 / 2`) over digest space `D`. -/
theorem monolithic_multiNode_rom_sound_collision
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type*} [Fintype D] [Nonempty D]
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax)
    (obs : (x : X') → Y' x → Option D)
    (hobs : ∀ (x : X') (z : D), FractionLE (fun y : Y' x => obs x y = some z) (1 / Fintype.card D))
    {A B : Type*} {M : ℕ}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (NodeForges : B → Fin M → Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin M, NodeForges b k l') →
      ¬ LogCollision (liftMultiObs obs) l' →
      ∃ (inst : Inst) (t : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst t l' ∧ ¬ doomed inst (r inst) t) :
    prob (fun b l' => ∃ k : Fin M, NodeForges b k l') (adv.bind verifyAll) [] ≤
      ((Q + M_verif : ℕ) : ℝ) * εmax +
        (1 / 2 : ℝ) * ((Q + M_verif : ℕ) : ℝ) ^ 2 / (Fintype.card D : ℝ) := by
  have hκ0 : (0 : ℝ) ≤ 1 / (Fintype.card D : ℝ) := by positivity
  have hLiftObs : ∀ (x : MultiQuery Inst Msg Chal X') (z : D),
      FractionLE (fun y : MultiAnswer Chal Y' x => liftMultiObs obs x y = some z)
        (1 / Fintype.card D) := by
    intro x z
    cases x with
    | chal _ _ _ => exact (FractionLE.false.mono_right hκ0).mono_left fun _ h => nomatch h
    | hash x' => exact hobs x' z
  apply monolithic_multiNode_rom_sound (D := D) (c := 1 / 2)
    hsound hε h0 (by norm_num) (HitsDigest (liftMultiObs obs))
  · intro l x _
    have hf := fractionLE_hitsDigest hκ0 hLiftObs l x
    refine hf.mono_right (le_of_eq ?_)
    ring
  · exact hadv
  · exact hver
  · intro b l' hout hforge hNoBad
    rw [← logCollision_iff_hasBad] at hNoBad
    exact hExtract b l' hout hforge hNoBad

end MonolithicExtraction

/-! ## 3. Composition with 19-Shape Aggregation (`AcceptedAggrTree`) -/

/-- **Monolithic ROM Upgrade for `AcceptedAggrTree` (`monolithic_aggrTree_rom_sound`):**
Replaces the per-node union bound `tree_rom_error_bound` (`M * Q * ε`) in `Ix.Cert.Aggr.EndToEnd`
with the monolithic single-oracle extraction bound `(Q + M_verif) * εmax + c * N^2 / |D|`,
while preserving full 19-shape derivation soundness (`AggrNodeHolds sem rootStmt`) and
verified child proof witness extraction. -/
theorem monolithic_aggrTree_rom_sound
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt)
    {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type}
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type} [Fintype D] [Nonempty D]
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax c : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax) (hc0 : 0 ≤ c)
    (hashBad : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') →
      (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Prop)
    (hHashBad : ∀ l x, l.dlookup x = none →
      FractionLE (hashBad l x) ((2 * c) * (l.length : ℝ) / (Fintype.card D : ℝ)))
    {A B : Type}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (NodeForges : B → Fin t.verificationCount →
      Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin t.verificationCount, NodeForges b k l') →
      ¬ HasBad hashBad l' →
      ∃ (inst : Inst) (tr : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst tr l' ∧ ¬ doomed inst (r inst) tr) :
    prob (fun b l' => ∃ k : Fin t.verificationCount, NodeForges b k l') (adv.bind verifyAll) [] ≤
      ((Q + M_verif : ℕ) : ℝ) * εmax +
        c * ((Q + M_verif : ℕ) : ℝ) ^ 2 / (Fintype.card D : ℝ) ∧
    _root_.Aggr.AggrNodeHolds sem rootStmt ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  obtain ⟨hDeriv, hChildOk⟩ := Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19 t
  exact ⟨monolithic_multiNode_rom_sound hsound hε h0 hc0 hashBad hHashBad adv hadv verifyAll hver
    NodeForges hExtract, _root_.Aggr.aggrDerivation19_invariant hDeriv, hChildOk⟩

/-! ## 4. Concrete `GoldilocksExt3` + RFC 7693 `BLAKE2b-512` (`c = 3 / 2`) 128-Bit PQ Instantiation -/

/-- Goldilocks cubic extension field size `p^3` is strictly above `2^191`. -/
theorem goldilocksExt3_card_ge_two_pow_191 :
    (2 : ℕ) ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ 3 := by
  have h1 : 7 * 2 ^ 61 < CertiFri.P3.Goldilocks.order := by decide
  have h2 : (7 * 2 ^ 61) ^ 3 < CertiFri.P3.Goldilocks.order ^ 3 :=
    Nat.pow_lt_pow_left h1 (by decide)
  have h3 : (2 : ℕ) ^ 191 ≤ (7 * 2 ^ 61) ^ 3 := by
    have ha : (7 * 2 ^ 61) ^ 3 = 343 * 2 ^ 183 := by ring
    have hb : (2 : ℕ) ^ 191 = 256 * 2 ^ 183 := by
      rw [show (256 : ℕ) = 2 ^ 8 by decide, ← pow_add]
    omega
  exact h3.trans h2.le

/-- Clean standalone lower bound `2^191 ≤ p^3` over `ℝ`. -/
theorem goldilocksExt3_card_ge_two_pow_191_real :
    (2 : ℝ) ^ 191 ≤ (CertiFri.P3.Goldilocks.order : ℝ) ^ 3 := by
  exact_mod_cast goldilocksExt3_card_ge_two_pow_191

/-- Monolithic ROM quantitative error formula `(Q + M_verif) * εmax + c * (Q + M_verif)^2 / |D|`. -/
noncomputable def monolithicRomBound (Q M_verif : ℕ) (εmax c digestCard : ℝ) : ℝ :=
  ((Q + M_verif : ℕ) : ℝ) * εmax + c * ((Q + M_verif : ℕ) : ℝ) ^ 2 / digestCard

/-- **Concrete 128-Bit Security Rate Bound at `GoldilocksExt3` + RFC 7693 `BLAKE2b-512` (`c = 3/2`):**
For ANY `M_verif ≤ 2^20` total verifier queries and `Q ≤ 2^128` adversary queries
(total `N = Q + M_verif ≤ 2^128`) with 64-byte RFC 7693 `BLAKE2b-512` (`|D| = 2^512`, true
512-bit internal state), incremental sponge prefactor `c = 3 / 2`, and per-round RBR error
`εmax ≤ (1 / 2) / 2^128`:
$$\mathrm{monolithicRomBound}\; Q\; M_{\text{verif}}\; \varepsilon_{\max}\; (3/2)\; 2^{512} \le
  \frac{Q + M_{\text{verif}}}{2^{128}}$$
(full 128-bit ROM security `t / ε ≥ 2^128`, with ZERO `-log₂ M` penalty!). -/
theorem monolithic_goldilocksExt3_blake2b512_rate_128
    (Q M_verif : ℕ) (_hM : M_verif ≤ 2 ^ 20) (hN : Q + M_verif ≤ 2 ^ 128)
    {εmax : ℝ} (hε : εmax ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128) :
    monolithicRomBound Q M_verif εmax (3 / 2) ((2 : ℝ) ^ 512) ≤
      ((Q + M_verif : ℕ) : ℝ) / (2 : ℝ) ^ 128 := by
  unfold monolithicRomBound
  set N : ℝ := ((Q + M_verif : ℕ) : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNle : N ≤ (2 : ℝ) ^ 128 := by dsimp only [N]; exact_mod_cast hN
  have hterm1 : N * εmax ≤ N * ((1 / 2 : ℝ) / (2 : ℝ) ^ 128) :=
    mul_le_mul_of_nonneg_left hε hN0
  have hterm2 : (3 / 2 : ℝ) * N ^ 2 / (2 : ℝ) ^ 512 ≤ N * ((1 / 2 : ℝ) / (2 : ℝ) ^ 128) := by
    have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
    have hpos512 : (0 : ℝ) < (2 : ℝ) ^ 512 := by positivity
    have hN2 : N ^ 2 ≤ N * (2 : ℝ) ^ 128 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hNle hN0
    have hstep : (3 / 2 : ℝ) * N ^ 2 / (2 : ℝ) ^ 512 ≤
        (3 / 2 : ℝ) * (N * (2 : ℝ) ^ 128) / (2 : ℝ) ^ 512 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN2 (by norm_num)) hpos512.le
    refine hstep.trans ?_
    have hsimp : (3 / 2 : ℝ) * (N * (2 : ℝ) ^ 128) / (2 : ℝ) ^ 512 =
        N * ((3 / 2 : ℝ) / (2 : ℝ) ^ 384) := by
      have h512 : (2 : ℝ) ^ 512 = (2 : ℝ) ^ 128 * (2 : ℝ) ^ 384 := by rw [← pow_add]
      rw [h512]
      field_simp [hpos128.ne']
    rw [hsimp]
    apply mul_le_mul_of_nonneg_left _ hN0
    have h384 : (3 : ℝ) * (2 : ℝ) ^ 128 ≤ (2 : ℝ) ^ 384 := by
      have h2 : (3 : ℝ) ≤ (2 : ℝ) ^ 256 := by
        have : (3 : ℕ) ≤ 2 ^ 256 := by decide
        exact_mod_cast this
      have hmul : (3 : ℝ) * (2 : ℝ) ^ 128 ≤ (2 : ℝ) ^ 256 * (2 : ℝ) ^ 128 :=
        mul_le_mul_of_nonneg_right h2 hpos128.le
      have hpow : (2 : ℝ) ^ 256 * (2 : ℝ) ^ 128 = (2 : ℝ) ^ 384 := by rw [← pow_add]
      rw [hpow] at hmul
      exact hmul
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (3 / 2 : ℝ) * (2 : ℝ) ^ 128
        = (1 / 2 : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ 128) := by ring
      _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ 384 := mul_le_mul_of_nonneg_left h384 (by norm_num)
  exact (add_le_add hterm1 hterm2).trans_eq (by ring)

/-- **Concrete `≤ 1 / 2^128` Probability Bound at `GoldilocksExt3` + RFC 7693 `BLAKE2b-512` (`c = 3/2`):**
Whenever `M_verif ≤ 2^20`, `Q ≤ 2^128` with total oracle budget `Q + M_verif ≤ 2^127` and
`((Q + M_verif : ℕ) : ℝ) * εmax ≤ (1 / 2) / 2^128` (for instance `Q ≤ 2^61, M_verif ≤ 2^20`
with `GoldilocksExt3` single-round field soundness `εmax = 1 / p^3 ≤ 1 / 2^191`, or any
`Q + M_verif ≤ 2^127` with `εmax ≤ 1 / 2^256`), the monolithic multi-node forgery
probability is literally `≤ 1 / 2^128`! -/
theorem monolithic_goldilocksExt3_blake2b512_concrete_prob_128
    (Q M_verif : ℕ) (_hM : M_verif ≤ 2 ^ 20) (hN : Q + M_verif ≤ 2 ^ 127)
    {εmax : ℝ} (hε : ((Q + M_verif : ℕ) : ℝ) * εmax ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128) :
    monolithicRomBound Q M_verif εmax (3 / 2) ((2 : ℝ) ^ 512) ≤ 1 / (2 : ℝ) ^ 128 := by
  unfold monolithicRomBound
  set N : ℝ := ((Q + M_verif : ℕ) : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNle : N ≤ (2 : ℝ) ^ 127 := by dsimp only [N]; exact_mod_cast hN
  have hNsq : N ^ 2 ≤ ((2 : ℝ) ^ 127) ^ 2 := by nlinarith
  have hterm2 : (3 / 2 : ℝ) * N ^ 2 / (2 : ℝ) ^ 512 ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128 := by
    have hstep : (3 / 2 : ℝ) * N ^ 2 / (2 : ℝ) ^ 512 ≤
        (3 / 2 : ℝ) * ((2 : ℝ) ^ 127) ^ 2 / (2 : ℝ) ^ 512 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNsq (by norm_num)) (by positivity)
    refine hstep.trans ?_
    have h254 : ((2 : ℝ) ^ 127) ^ 2 = (2 : ℝ) ^ 254 := by rw [← pow_mul]
    rw [h254, div_le_div_iff₀ (by positivity) (by positivity)]
    have hL : (3 / 2 : ℝ) * (2 : ℝ) ^ 254 * (2 : ℝ) ^ 128 = (3 / 2 : ℝ) * (2 : ℝ) ^ 382 := by
      rw [mul_assoc, ← pow_add]
    have hR : (1 / 2 : ℝ) * (2 : ℝ) ^ 512 = (2 : ℝ) ^ 511 := by
      have h512 : (2 : ℝ) ^ 512 = 2 * (2 : ℝ) ^ 511 := by
        rw [show (512 : ℕ) = 1 + 511 by decide, pow_add, pow_one]
      rw [h512, ← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
    rw [hL, hR]
    have h32 : (3 / 2 : ℝ) * (2 : ℝ) ^ 382 ≤ (2 : ℝ) ^ 383 := by
      have h383 : (2 : ℝ) ^ 383 = 2 * (2 : ℝ) ^ 382 := by
        rw [show (383 : ℕ) = 1 + 382 by decide, pow_add, pow_one]
      rw [h383]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact h32.trans (pow_le_pow_right₀ (by norm_num) (by decide))
  exact (add_le_add hε hterm2).trans_eq (by ring)

/-- **Concrete `GoldilocksExt3` Single-Field-Challenge Bound (`≤ 1 / 2^128`):**
With `εmax = 1 / |GoldilocksExt3| = 1 / p^3` (`p^3 ≥ 2^191`), `M_verif ≤ 2^20`, and `Q ≤ 2^61`,
the total monolithic ROM bound with RFC 7693 `BLAKE2b-512` (`|D| = 2^512`, `c = 3 / 2`) is
strictly `≤ 1 / 2^128`. -/
theorem monolithic_goldilocksExt3_field_128
    (Q M_verif : ℕ) (hQ : Q ≤ 2 ^ 61) (hM : M_verif ≤ 2 ^ 20) :
    monolithicRomBound Q M_verif (1 / (CertiFri.P3.Goldilocks.order : ℝ) ^ 3)
      (3 / 2) ((2 : ℝ) ^ 512) ≤ 1 / (2 : ℝ) ^ 128 := by
  apply monolithic_goldilocksExt3_blake2b512_concrete_prob_128 Q M_verif hM (by omega)
  have hp3 : (2 : ℝ) ^ 191 ≤ (CertiFri.P3.Goldilocks.order : ℝ) ^ 3 :=
    goldilocksExt3_card_ge_two_pow_191_real
  have hNle : ((Q + M_verif : ℕ) : ℝ) ≤ (2 : ℝ) ^ 62 := by
    have : Q + M_verif ≤ 2 ^ 62 := by omega
    exact_mod_cast this
  have hinv : (1 : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ) ^ 3 ≤ 1 / (2 : ℝ) ^ 191 :=
    one_div_le_one_div_of_le (by positivity) hp3
  calc ((Q + M_verif : ℕ) : ℝ) * (1 / (CertiFri.P3.Goldilocks.order : ℝ) ^ 3)
      ≤ (2 : ℝ) ^ 62 * (1 / (2 : ℝ) ^ 191) := by
        exact mul_le_mul hNle hinv (by positivity) (by positivity)
    _ = (1 / 2 : ℝ) / (2 : ℝ) ^ 128 := by
        have h191 : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 62 * 2 * (2 : ℝ) ^ 128 := by ring
        rw [h191]
        have h62 : (2 : ℝ) ^ 62 ≠ 0 := by positivity
        have h128 : (2 : ℝ) ^ 128 ≠ 0 := by positivity
        field_simp [h62, h128]

/-! ## 5. Strict Scaling Comparison vs Naive `M`-Node Union Bound & Negative Controls -/

/-- **Strict Scaling Comparison (`monolithic_strictly_tighter_than_union_bound`):**
Whenever `2 ≤ M`, `0 < εmax`, and `M_verif < (M - 1) * Q`, the monolithic RBR term
`(Q + M_verif) * εmax` is strictly tighter than the naive union bound `M * Q * εmax`! -/
theorem monolithic_strictly_tighter_than_union_bound
    (M Q M_verif : ℕ) (hM : 2 ≤ M) (hLt : M_verif < (M - 1) * Q)
    {εmax : ℝ} (hε : 0 < εmax) :
    ((Q + M_verif : ℕ) : ℝ) * εmax < (M : ℝ) * (Q : ℝ) * εmax := by
  have hNat : Q + M_verif < M * Q := by
    have hsplit : M * Q = Q + (M - 1) * Q := by
      have : M = 1 + (M - 1) := by omega
      conv_lhs => rw [this]
      ring
    omega
  have hReal : ((Q + M_verif : ℕ) : ℝ) < (M : ℝ) * (Q : ℝ) := by exact_mod_cast hNat
  exact mul_lt_mul_of_pos_right hReal hε

/-- **Concrete `2^20`-Node Separation (`monolithic_beats_union_bound_2_pow_20`):**
At `M = 2^20`, `Q = 2^108`, `M_verif = 2^20`, and `εmax = 1 / 2^128`:
- Naive union bound `M * Q * εmax = 1` (completely vacuous — loses all 20 bits of margin!),
- Monolithic single-oracle ROM bound with RFC 7693 `BLAKE2b-512` (`|D| = 2^512`, `c = 3/2`)
  is `< 1 / 2^19`! -/
theorem monolithic_beats_union_bound_2_pow_20 :
    ((2 ^ 20 : ℕ) : ℝ) * ((2 ^ 108 : ℕ) : ℝ) * (1 / (2 : ℝ) ^ 128) = 1 ∧
    monolithicRomBound (2 ^ 108) (2 ^ 20) (1 / (2 : ℝ) ^ 128) (3 / 2) ((2 : ℝ) ^ 512) <
      1 / (2 : ℝ) ^ 19 := by
  constructor
  · rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    have hne : (2 : ℝ) ^ 128 ≠ 0 := by positivity
    field_simp [hne]
  · unfold monolithicRomBound
    have hN : (((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ)) < (3 / 2 : ℝ) * (2 : ℝ) ^ 108 := by
      have hlt : 2 * (2 ^ 108 + 2 ^ 20) < 3 * 2 ^ 108 := by decide
      have hltR : (2 : ℝ) * ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) < 3 * (2 : ℝ) ^ 108 := by
        exact_mod_cast hlt
      linarith
    have hN0 : (0 : ℝ) ≤ ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht1 : ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) * (1 / (2 : ℝ) ^ 128) <
        (3 / 2 : ℝ) * (2 : ℝ) ^ 108 * (1 / (2 : ℝ) ^ 128) :=
      mul_lt_mul_of_pos_right hN (by positivity)
    have ht1' : (3 / 2 : ℝ) * (2 : ℝ) ^ 108 * (1 / (2 : ℝ) ^ 128) = (3 / 4 : ℝ) / (2 : ℝ) ^ 19 := by
      have h128 : (2 : ℝ) ^ 128 = (2 : ℝ) ^ 108 * 2 * (2 : ℝ) ^ 19 := by
        have h1 : (2 : ℝ) ^ 128 = (2 : ℝ) ^ 108 * (2 : ℝ) ^ 1 * (2 : ℝ) ^ 19 := by
          rw [← pow_add, ← pow_add]
        simpa using h1
      rw [h128]
      have h108 : (2 : ℝ) ^ 108 ≠ 0 := by positivity
      have h19 : (2 : ℝ) ^ 19 ≠ 0 := by positivity
      field_simp [h108, h19]
      ring
    have hNle : ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 109 := by
      have : 2 ^ 108 + 2 ^ 20 ≤ 2 ^ 109 := by decide
      exact_mod_cast this
    have ht2 : (3 / 2 : ℝ) * ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ 512 ≤
        (1 / 4 : ℝ) / (2 : ℝ) ^ 19 := by
      have hsq : ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 109) ^ 2 := by nlinarith
      have hstep : (3 / 2 : ℝ) * ((2 ^ 108 + 2 ^ 20 : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ 512 ≤
          (3 / 2 : ℝ) * ((2 : ℝ) ^ 109) ^ 2 / (2 : ℝ) ^ 512 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
      refine hstep.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h218 : ((2 : ℝ) ^ 109) ^ 2 = (2 : ℝ) ^ 218 := by rw [← pow_mul]
      rw [h218]
      have hcmp : (3 / 2 : ℝ) * (2 : ℝ) ^ 218 * (2 : ℝ) ^ 19 = (3 / 2 : ℝ) * (2 : ℝ) ^ 237 := by
        rw [mul_assoc, ← pow_add]
      have hcmp2 : (1 / 4 : ℝ) * (2 : ℝ) ^ 512 = (2 : ℝ) ^ 510 := by
        have h512 : (2 : ℝ) ^ 512 = (2 : ℝ) ^ 2 * (2 : ℝ) ^ 510 := by rw [← pow_add]
        rw [h512, ← mul_assoc, show (1 / 4 : ℝ) * (2 : ℝ) ^ 2 = 1 by norm_num, one_mul]
      rw [hcmp, hcmp2]
      have hle : (2 : ℝ) ^ 238 ≤ (2 : ℝ) ^ 510 :=
        pow_le_pow_right₀ (by norm_num) (by decide)
      have h32 : (3 / 2 : ℝ) * (2 : ℝ) ^ 237 ≤ (2 : ℝ) ^ 238 := by
        have : (2 : ℝ) ^ 238 = 2 * (2 : ℝ) ^ 237 := by
          rw [show (238 : ℕ) = 1 + 237 by decide, pow_add, pow_one]
        linarith [show (0 : ℝ) ≤ (2 : ℝ) ^ 237 by positivity]
      exact h32.trans hle
    exact (add_lt_add_of_lt_of_le (ht1.trans_eq ht1') ht2).trans_eq (by ring)

/-- **Constructive Negative Control 1 (`negControl_fp2_below_128`):**
Quadratic extension `Fp^2` over Goldilocks has cardinality `p^2 < 2^128`, so even a SINGLE
random extension challenge has collision probability `1 / p^2 > 1 / 2^128` (strictly failing
128-bit security!). -/
theorem negControl_fp2_below_128 :
    CertiFri.P3.Goldilocks.order ^ 2 < 2 ^ 128 ∧
    (1 : ℝ) / (2 : ℝ) ^ 128 < 1 / (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 := by
  have hlt : CertiFri.P3.Goldilocks.order ^ 2 < 2 ^ 128 := by
    have h1 : CertiFri.P3.Goldilocks.order < 2 ^ 64 := by decide
    have h2 : CertiFri.P3.Goldilocks.order ^ 2 < (2 ^ 64) ^ 2 :=
      Nat.pow_lt_pow_left h1 (by decide)
    simpa [← pow_mul] using h2
  refine ⟨hlt, ?_⟩
  have hltR : (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 < (2 : ℝ) ^ 128 := by exact_mod_cast hlt
  have hpos : (0 : ℝ) < (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 := by
    have : 0 < CertiFri.P3.Goldilocks.order := by decide
    positivity
  exact one_div_lt_one_div_of_lt hpos hltR

/-- **Constructive Negative Control 2 (`negControl_digest32_saturates_at_2_128`):**
With a 32-byte digest (`|D| = 2^256`, production 128-bit classical `BLAKE3-256`) at `N = 2^128`
oracle queries:
- Incremental sponge collision term `(3/2) * (2^128)^2 / 2^256 = 3 / 2 > 1` (completely vacuous!),
- Even plain birthday collision term `(1/2) * (2^128)^2 / 2^256 = 1 / 2 > 1 / 2^128`!
Therefore RFC 7693 `BLAKE2b-512` (`|D| = 2^512`, true 512-bit internal state) is required for
128-bit post-quantum ROM security (whereas `BLAKE3-XOF48`/`XOF64` remain capped at 256-bit
internal `cv` → `85.3b` BHT). -/
theorem negControl_digest32_saturates_at_2_128 :
    (3 / 2 : ℝ) * ((2 : ℝ) ^ 128) ^ 2 / (2 : ℝ) ^ 256 = 3 / 2 ∧
    (1 : ℝ) < (3 / 2 : ℝ) * ((2 : ℝ) ^ 128) ^ 2 / (2 : ℝ) ^ 256 ∧
    (1 / 2 : ℝ) * ((2 : ℝ) ^ 128) ^ 2 / (2 : ℝ) ^ 256 = 1 / 2 := by
  have h256 : ((2 : ℝ) ^ 128) ^ 2 = (2 : ℝ) ^ 256 := by ring
  have hne : (2 : ℝ) ^ 256 ≠ 0 := by positivity
  rw [h256]
  refine ⟨by field_simp [hne], ?_, by field_simp [hne]⟩
  have h : (3 / 2 : ℝ) * (2 : ℝ) ^ 256 / (2 : ℝ) ^ 256 = 3 / 2 := by field_simp [hne]
  rw [h]; norm_num

end Ix.Cert.Aggr.MonolithicRom
