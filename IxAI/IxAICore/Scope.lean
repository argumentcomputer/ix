import IxAICore.Triage
import IxAICore.TriagePolicy

/-!
# The domain of the triage gate

`Formula.atom` takes any `Nat`, but `Formula.valid` counts only the eight assignments to
`P0 … P2`. For a formula with a larger atom the two come apart: `valid (P3 → P0)` is `true`,
while the assignment making only `P3` true falsifies it. `act_publish_sound` concludes
`f.valid = true`, which is a statement about those eight assignments.

`Formula.inScope` is the domain on which `valid` means truth under every assignment
(`Formula.valid_iff_forall_eval`). The training generator only produces scoped formulas
(`Formula.gen_scoped`, `Triage.data_scoped`, `Triage.test_scoped`), and `Triage.admit` is the
gate's entry for formulas from outside: it refuses a formula outside the domain and otherwise acts
as `Triage.act`, so a published formula is true under every assignment
(`Triage.admit_publish_true`).
-/

namespace IxAICore

namespace Formula

/-- Every atom is below `k`. -/
def atomsBelow (k : Nat) : Formula → Bool
  | atom n => decide (n < k)
  | top => true
  | imp a b | and a b => a.atomsBelow k && b.atomsBelow k

/-- All atoms are among `P0 … P2`, the atoms `valid` enumerates. -/
def inScope (f : Formula) : Bool := f.atomsBelow 3

/-- A formula's value depends only on its atoms. -/
theorem eval_congr (k : Nat) (v w : Nat → Bool) (hvw : ∀ n, n < k → v n = w n) :
    ∀ f : Formula, f.atomsBelow k = true → f.eval v = f.eval w
  | atom n, h => by
    simp only [atomsBelow, decide_eq_true_eq] at h
    exact hvw n h
  | top, _ => rfl
  | imp a b, h => by
    simp only [atomsBelow, Bool.and_eq_true] at h
    simp only [eval, eval_congr k v w hvw a h.1, eval_congr k v w hvw b h.2]
  | and a b, h => by
    simp only [atomsBelow, Bool.and_eq_true] at h
    simp only [eval, eval_congr k v w hvw a h.1, eval_congr k v w hvw b h.2]

/-- The assignment `models` reads from the bits of `bits`. -/
def ofBits (bits : Nat) : Nat → Bool := fun n => (bits >>> n) % 2 == 1

/-- The bits of an assignment's values at `P0 … P2`. -/
def bitsOf (v : Nat → Bool) : Nat :=
  (if v 0 then 1 else 0) + (if v 1 then 2 else 0) + (if v 2 then 4 else 0)

theorem bitsOf_lt (v : Nat → Bool) : bitsOf v < 8 := by
  unfold bitsOf
  cases v 0 <;> cases v 1 <;> cases v 2 <;> decide

theorem ofBits_bitsOf (v : Nat → Bool) : ∀ n, n < 3 → ofBits (bitsOf v) n = v n := by
  intro n hn
  unfold ofBits bitsOf
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    (match n, hn with
     | 0, _ => simp [h0]
     | 1, _ => simp [h1]
     | 2, _ => simp [h2])

theorem valid_iff_all (f : Formula) :
    f.valid = true ↔ ∀ bits, bits < 8 → f.eval (ofBits bits) = true := by
  have hl : (List.range 8).length = 8 := List.length_range
  unfold valid models
  constructor
  · intro h bits hb
    have hall := List.length_filter_eq_length_iff.mp
      (by rw [hl]; exact (beq_iff_eq.mp h))
    exact hall bits (List.mem_range.mpr hb)
  · intro h
    have hf : (List.range 8).filter (fun bits => f.eval (ofBits bits)) = List.range 8 :=
      List.filter_eq_self.mpr fun a ha => h a (List.mem_range.mp ha)
    show ((List.range 8).filter (fun bits => f.eval (ofBits bits))).length == 8
    rw [hf, hl]
    rfl

/-- On scoped formulas, `valid` is truth under every assignment. -/
theorem valid_iff_forall_eval (f : Formula) (hs : f.inScope = true) :
    f.valid = true ↔ ∀ v : Nat → Bool, f.eval v = true := by
  rw [valid_iff_all]
  constructor
  · intro h v
    rw [← eval_congr 3 (ofBits (bitsOf v)) v (ofBits_bitsOf v) f hs]
    exact h _ (bitsOf_lt v)
  · intro h bits _
    exact h _

theorem leaf_scoped (k : Nat) (hk : k < 4) : (leaf k).inScope = true := by
  unfold leaf inScope
  split
  · rfl
  · rename_i h
    simp only [atomsBelow, decide_eq_true_eq]
    have : k ≠ 3 := fun e => h (by rw [e]; rfl)
    omega

theorem below_lt (r : Rng) (n : Nat) (hn : 0 < n) : (r.below n).1 < n :=
  Nat.mod_lt _ hn

/-- The generator stays within `P0 … P2`. -/
theorem gen_scoped : ∀ (d : Nat) (r : Rng), (gen d r).1.inScope = true
  | 0, r => leaf_scoped _ (below_lt r 4 (by decide))
  | d + 1, r => by
    have ha := gen_scoped d (r.below 5).2
    have hb := gen_scoped d (gen d (r.below 5).2).2
    unfold inScope at ha hb ⊢
    show (if (r.below 5).1 < 2 then (gen d (r.below 5).2).1
      else if (r.below 5).1 == 4 then and (gen d (r.below 5).2).1 (gen d (gen d (r.below 5).2).2).1
      else imp (gen d (r.below 5).2).1 (gen d (gen d (r.below 5).2).2).1).atomsBelow 3 = true
    split
    · exact ha
    · split <;> simp only [atomsBelow, ha, hb, Bool.and_self]

theorem genFormulas_scoped (depth : Nat) :
    ∀ (n : Nat) (r : Rng), ∀ f ∈ (genFormulas depth n r).1, f.inScope = true
  | 0, _, f, h => by simp [genFormulas] at h
  | n + 1, r, f, h => by
    simp only [genFormulas, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact gen_scoped depth r
    · exact genFormulas_scoped depth n _ f h

end Formula

theorem Spec.sampleN_mem {σ : Type} (s : Spec σ) (p : σ → Prop) (hs : ∀ r, p (s.sample r).1) :
    ∀ (n : Nat) (r : Rng), ∀ x ∈ (s.sampleN n r).1, p x
  | 0, _, x, h => by simp [Spec.sampleN] at h
  | n + 1, r, x, h => by
    simp only [Spec.sampleN, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact hs r
    · exact Spec.sampleN_mem s p hs n _ x h

namespace Triage

theorem spec_sample_scoped (r : Rng) : (spec.sample r).1.inScope = true := Formula.gen_scoped 3 r

/-- Every training formula is in the gate's domain. -/
theorem data_scoped (c : Config) : ∀ f ∈ c.data spec, f.inScope = true :=
  Spec.sampleN_mem spec _ spec_sample_scoped _ _

/-- Every held-out formula is in the gate's domain. -/
theorem test_scoped (c : Config) : ∀ f ∈ c.test spec, f.inScope = true :=
  Spec.sampleN_mem spec _ spec_sample_scoped _ _

theorem policy_data_scoped (c : Config) : ∀ f ∈ c.data policySpec, f.inScope = true :=
  Spec.sampleN_mem policySpec _ spec_sample_scoped _ _

theorem policy_test_scoped (c : Config) : ∀ f ∈ c.test policySpec, f.inScope = true :=
  Spec.sampleN_mem policySpec _ spec_sample_scoped _ _

/-- For a scoped formula, whatever the weights, a published formula is true under every
assignment. -/
theorem act_publish_true (g : Gate) (m : Model) (f : Formula) (hs : f.inScope = true)
    (h : act g m f = .publish) : ∀ v : Nat → Bool, f.eval v = true :=
  (Formula.valid_iff_forall_eval f hs).mp (act_publish_sound g m f h)

/-- The gate's entry for a formula from outside: `none` when the formula is outside the domain,
otherwise the gate's action. -/
def admit (g : Gate) (m : Model) (f : Formula) : Option Action :=
  if f.inScope then some (act g m f) else none

theorem admit_none_iff (g : Gate) (m : Model) (f : Formula) :
    admit g m f = none ↔ f.inScope = false := by
  unfold admit
  cases f.inScope <;> simp

theorem admit_of_scoped (g : Gate) (m : Model) (f : Formula) (hs : f.inScope = true) :
    admit g m f = some (act g m f) := by
  simp [admit, hs]

/-- Whatever the weights, a formula published through `admit` is true under every assignment. -/
theorem admit_publish_true (g : Gate) (m : Model) (f : Formula) (h : admit g m f = some .publish) :
    ∀ v : Nat → Bool, f.eval v = true := by
  unfold admit at h
  split at h
  · rename_i hs
    exact act_publish_true g m f hs (Option.some.inj h)
  · cases h

/-- For a scoped formula, whatever the weights, a formula the routing policy publishes is true
under every assignment. -/
theorem outcome_publish_true (m : Model) (f : Formula) (hs : f.inScope = true)
    (h : outcome m f = .publish) : ∀ v : Nat → Bool, f.eval v = true :=
  (Formula.valid_iff_forall_eval f hs).mp (outcome_publish_sound m f h)

end Triage

end IxAICore
