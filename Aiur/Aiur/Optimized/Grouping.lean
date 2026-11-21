import Aiur.Optimized.Activation

/-! Function grouping preserves logical call identities. Members share data
columns, while columns needed to silence cubic constraints and lookup enables
are private. A quadratic constraint may acquire a member selector; a cubic
constraint is retained only after checking that private zeroes silence it.
The construction does not assume a field characteristic or a group-size bound.
-/
namespace Aiur.Optimized.Grouping

open Circuit
variable {F : Type} [Field F] [DecidableEq F]

def erase (privateCols : List Nat) (p : Polynomial F) : Polynomial F :=
  (p.subst fun v => if privateCols.contains v then .const 0 else .var v).simplify

def silent (privateCols : List Nat) (p : Polynomial F) : Bool :=
  erase privateCols p == .const 0

theorem silent_zero {privateCols : List Nat} {p : Polynomial F}
    (checked : silent privateCols p = true) (a : Nat → F)
    (zero : ∀ v ∈ privateCols, a v = 0) : p.denote a = 0 := by
  have equal : erase privateCols p = .const 0 := Polynomial.beq_eq _ _ |>.mp checked
  have h := congrArg (fun p : Polynomial F => p.denote a) equal
  simp only [erase, Polynomial.denote_simplify, Polynomial.denote_subst] at h
  have same : (fun v => (if privateCols.contains v then Polynomial.const 0 else .var v).denote a) = a := by
    funext v
    by_cases member : v ∈ privateCols
    · simp [member, Scalar.Circuit.ArithExpr.denote, zero v member]
    · simp [member, Scalar.Circuit.ArithExpr.denote]
  simpa only [same, Scalar.Circuit.ArithExpr.denote] using h

def gate (selector : Nat) (privateCols : List Nat) (p : Polynomial F) : Polynomial F :=
  if silent privateCols p then p else .mul (.var selector) p

@[simp] theorem gate_active (selector : Nat) (privateCols : List Nat) (p : Polynomial F)
    (a : Nat → F) (active : a selector = 1) :
    (gate selector privateCols p).denote a = p.denote a := by
  unfold gate
  split <;> simp [Scalar.Circuit.ArithExpr.denote, active]

theorem gate_inactive (selector : Nat) (privateCols : List Nat) (p : Polynomial F)
    (a : Nat → F) (inactive : a selector = 0)
    (zero : ∀ v ∈ privateCols, a v = 0) :
    (gate selector privateCols p).denote a = 0 := by
  unfold gate
  split
  · exact silent_zero ‹_› a zero
  · simp [Scalar.Circuit.ArithExpr.denote, inactive]

def privateZero (selector column : Nat) : Polynomial F :=
  .mul (.sub (.const 1) (.var selector)) (.var column)

def member (source : Chip F) (selector : Nat) (privateCols : List Nat) : Chip F :=
  { source with constraints := source.constraints.map (gate selector privateCols) ++
      privateCols.map (privateZero selector) }

theorem member_active (source : Chip F) (selector : Nat) (privateCols : List Nat)
    (a : Nat → F) (active : a selector = 1) :
    (member source selector privateCols).ValidAssignment rom a ↔ source.ValidAssignment rom a := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    intro p hp
    have h := h.1 _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    simpa only [gate_active _ _ _ _ active] using h
  · intro h
    refine ⟨?_, h.2⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa only [gate_active _ _ _ _ active] using h.1 q hq
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
      simp [privateZero, Scalar.Circuit.ArithExpr.denote, active]

theorem member_private_zero (source : Chip F) (selector : Nat) (privateCols : List Nat)
    (a : Nat → F) (valid : (member source selector privateCols).ValidAssignment rom a)
    (inactive : a selector = 0) (v : Nat) (present : v ∈ privateCols) : a v = 0 := by
  have h := valid.1 (privateZero selector v)
    (List.mem_append_right _ (List.mem_map.mpr ⟨v, present, rfl⟩))
  simpa [privateZero, Scalar.Circuit.ArithExpr.denote, inactive] using h

theorem member_inactive (source : Chip F) (selector : Nat) (privateCols : List Nat)
    (quiet : ∀ m ∈ source.memory, silent privateCols m.enable = true)
    (a : Nat → F) (inactive : a selector = 0) (zero : ∀ v ∈ privateCols, a v = 0) :
    (member source selector privateCols).ValidAssignment rom a := by
  refine ⟨?_, ?_⟩
  · intro p present
    rcases List.mem_append.mp present with present | present
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp present
      exact gate_inactive _ _ _ _ inactive zero
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp present
      simp [privateZero, Scalar.Circuit.ArithExpr.denote, zero v hv]
  · intro m present
    have h := silent_zero (quiet m present) a zero
    simp [MemoryLookup.Valid, h]

theorem requirements_inactive (source : Chip F) (privateCols : List Nat)
    (quiet : ∀ s ∈ source.sends, silent privateCols s.enable = true)
    (a : Nat → F) (zero : ∀ v ∈ privateCols, a v = 0) : source.requirements a = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro s present
  simp [silent_zero (quiet s present) a zero]

/-- The selected member recovers the original finite-row local rule. This is
the same interface used by Physical.Prepared's source-correctness theorem;
grouping changes neither the conclusion nor its constrained call premises. -/
theorem selected_member_sound (source : Chip F) (formed : source.wellFormed = true)
    (privateCols : List Nat) (a : Nat → F)
    (valid : (member (Activation.compile source) source.numVars privateCols).ValidAssignment rom a)
    (active : a source.numVars = 1) :
    source.LocalRule rom (source.conclusion a) ((Activation.compile source).requirements a) := by
  have activated := (member_active _ _ _ _ active).mp valid
  have original := (Activation.valid_active_iff source a active).mp activated
  have finite := source.finiteAssignment formed a rom
  refine ⟨Row.ofAssignment source.name source.numVars a, rfl,
    ⟨formed, Row.ofAssignment_length _ _ _, finite.1.mp original⟩, finite.2.1.symm, ?_⟩
  exact finite.2.2.symm.trans (Activation.requirements_active source a active).symm

theorem selected_member_complete (source : Chip F) (privateCols : List Nat)
    (a : Nat → F) (valid : source.ValidAssignment rom a) (active : a source.numVars = 1) :
    (member (Activation.compile source) source.numVars privateCols).ValidAssignment rom a :=
  (member_active _ _ _ _ active).mpr ((Activation.valid_active_iff source a active).mpr valid)

omit [DecidableEq F] in
/-- A shared message argument of degree two can be materialized in one private
column without increasing the maximum constraint degree. -/
theorem private_value_iff (s value witness : F) (boolean : s = 0 ∨ s = 1) :
    (s * (witness - value) = 0 ∧ (1 - s) * witness = 0) ↔ witness = s * value := by
  rcases boolean with rfl | rfl <;> simp [sub_eq_zero]

/-- Prefix exclusion is linear in the group size and sound in every field,
including characteristic two. No unchecked cast of the group size is used. -/
def Exclusive : List F → Prop
  | [] => True
  | s :: ss => (s = 0 ∨ s = 1) ∧ s * ss.sum = 0 ∧ Exclusive ss

omit [DecidableEq F] in
theorem exclusive_sum {ss : List F} (valid : Exclusive ss) : ss.sum = 0 ∨ ss.sum = 1 := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rcases valid with ⟨hs, cross, tail⟩
    rcases hs with rfl | rfl
    · simpa using ih tail
    · have sum : ss.sum = 0 := by simpa using cross
      simp [sum]

omit [DecidableEq F] in
theorem exclusive_zero {ss : List F} (valid : Exclusive ss) (zero : ss.sum = 0) :
    ∀ s ∈ ss, s = 0 := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rcases valid with ⟨hs, cross, tail⟩
    rcases hs with rfl | rfl
    · have sum : ss.sum = 0 := by simpa using zero
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rfl
      · exact ih tail sum v hv
    · have sum : ss.sum = 0 := by simpa using cross
      simp [sum] at zero

omit [DecidableEq F] in
theorem exclusive_unique {ss : List F} (valid : Exclusive ss) :
    ss = ss.map (fun _ => (0 : F)) ∨ ∃ left right,
      ss = left ++ 1 :: right ∧ (∀ s ∈ left, s = 0) ∧ (∀ s ∈ right, s = 0) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rcases valid with ⟨hs, cross, tail⟩
    rcases hs with rfl | rfl
    · rcases ih tail with zero | ⟨left, right, same, hl, hr⟩
      · exact Or.inl (by simpa using congrArg (List.cons 0) zero)
      · refine Or.inr ⟨0 :: left, right, by simp [same], ?_, hr⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · rfl
        · exact hl v hv
    · have sum : ss.sum = 0 := by simpa using cross
      exact Or.inr ⟨[], ss, rfl, by simp, exclusive_zero tail sum⟩

omit [DecidableEq F] in
/-- Superposing a lookup slot preserves exactly the active member's argument
(and multiplicity). Applies independently to every padded argument position;
the channel and callable/ROM-width identity are positions in that same slot. -/
theorem superpose_selected (left right : List F) (selected : F)
    (before : ∀ x ∈ left, x = 0) (after : ∀ x ∈ right, x = 0) :
    (left ++ selected :: right).sum = selected := by
  have hl : left.sum = 0 := List.sum_eq_zero before
  have hr : right.sum = 0 := List.sum_eq_zero after
  simp [hl, hr]

omit [DecidableEq F] in
/-- If the complete row is padding, the provider multiplicity must vanish. -/
theorem inactive_count (s count : F) (inactive : s = 0)
    (guard : (1 - s) * count = 0) : count = 0 := by
  simpa [inactive] using guard

end Aiur.Optimized.Grouping
