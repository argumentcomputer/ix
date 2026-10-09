import Ix.CompileCert.Canon.FreshNames

/-!
Prefix-separation lemmas for the generated allocation families.
These proofs change no executable code.

`old.isPrefixOf (keyName aux) = false` below is an INTERNAL allocation-state
invariant: old constructor roots must not contain the current auxiliary root.
It must be derived from the generated-root forest and source-read coverage,
never appended to the caller/domain assumptions of the final theorem.
All statements concern Lean.Name structure after keyName erases cached fields.
-/

namespace Ix.Compile.Canon.FreshFamilySeparation

/-- Separation of whole suffix families in both prefix directions. -/
def Apart (a b : Lean.Name) : Prop :=
  a.isPrefixOf b = false ∧ b.isPrefixOf a = false

theorem Apart.symm {a b : Lean.Name} (h : Apart a b) : Apart b a :=
  ⟨h.2, h.1⟩

theorem prefix_refl (n : Lean.Name) : n.isPrefixOf n = true := by
  cases n <;> simp [Lean.Name.isPrefixOf]

theorem prefix_parts_le {a b : Lean.Name} (h : a.isPrefixOf b = true) :
    a.getNumParts ≤ b.getNumParts := by
  induction b with
  | anonymous =>
    have equal : a = .anonymous := by simpa [Lean.Name.isPrefixOf] using h
    subst a
    exact Nat.le_refl _
  | str b s ih =>
    have step : a = .str b s ∨ a.isPrefixOf b = true := by
      simpa [Lean.Name.isPrefixOf] using h
    rcases step with rfl | ancestor
    · exact Nat.le_refl _
    · have bound := ih ancestor
      simp only [Lean.Name.getNumParts]
      omega
  | num b k ih =>
    have step : a = .num b k ∨ a.isPrefixOf b = true := by
      simpa [Lean.Name.isPrefixOf] using h
    rcases step with rfl | ancestor
    · exact Nat.le_refl _
    · have bound := ih ancestor
      simp only [Lean.Name.getNumParts]
      omega

theorem prefix_trans {a b c : Lean.Name} (hab : a.isPrefixOf b = true)
    (hbc : b.isPrefixOf c = true) : a.isPrefixOf c = true := by
  induction c with
  | anonymous =>
    have equal : b = .anonymous := by simpa [Lean.Name.isPrefixOf] using hbc
    subst b
    exact hab
  | str c s ih =>
    have step : b = .str c s ∨ b.isPrefixOf c = true := by
      simpa [Lean.Name.isPrefixOf] using hbc
    rcases step with rfl | ancestor
    · exact hab
    · have hac := ih ancestor
      simp [Lean.Name.isPrefixOf, hac]
  | num c k ih =>
    have step : b = .num c k ∨ b.isPrefixOf c = true := by
      simpa [Lean.Name.isPrefixOf] using hbc
    rcases step with rfl | ancestor
    · exact hab
    · have hac := ih ancestor
      simp [Lean.Name.isPrefixOf, hac]

theorem prefix_eq_of_parts_eq {a b : Lean.Name}
    (parts : a.getNumParts = b.getNumParts) (h : a.isPrefixOf b = true) : a = b := by
  cases b with
  | anonymous => simpa [Lean.Name.isPrefixOf] using h
  | str b s =>
    have step : a = .str b s ∨ a.isPrefixOf b = true := by
      simpa [Lean.Name.isPrefixOf] using h
    rcases step with equal | ancestor
    · exact equal
    · have bound := prefix_parts_le ancestor
      simp only [Lean.Name.getNumParts] at parts
      omega
  | num b k =>
    have step : a = .num b k ∨ a.isPrefixOf b = true := by
      simpa [Lean.Name.isPrefixOf] using h
    rcases step with equal | ancestor
    · exact equal
    · have bound := prefix_parts_le ancestor
      simp only [Lean.Name.getNumParts] at parts
      omega

theorem str_not_prefix_parent (parent : Lean.Name) (label : String) :
    (Lean.Name.str parent label).isPrefixOf parent = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have bound := prefix_parts_le h
  simp only [Lean.Name.getNumParts] at bound
  omega

/-! Fresh numeric children: the finite numeric bound proves one direction
without a parent premise. Only the inverse direction needs the old root not
to be an ancestor of the parent. -/

theorem numeric_child_not_prefix_old (reserved : List Lean.Name)
    (parent : Lean.Name) (label : String) (old : Lean.Name) (hold : old ∈ reserved) :
    (Lean.Name.str (.num parent (numeralBound reserved)) label).isPrefixOf old = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have lower := nameNumeralBound_prefix h
  have upper := nameNumeralBound_le hold
  simp only [nameNumeralBound] at lower
  omega

theorem old_not_prefix_numeric_child (reserved : List Lean.Name)
    (parent : Lean.Name) (label : String) (old : Lean.Name) (hold : old ∈ reserved)
    (hparent : old.isPrefixOf parent = false) :
    old.isPrefixOf (.str (.num parent (numeralBound reserved)) label) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have upper := nameNumeralBound_le hold
  have first : old = .str (.num parent (numeralBound reserved)) label ∨
      old.isPrefixOf (.num parent (numeralBound reserved)) = true := by
    simpa [Lean.Name.isPrefixOf] using h
  rcases first with rfl | ancestor
  · simp only [nameNumeralBound] at upper
    omega
  · have second : old = .num parent (numeralBound reserved) ∨
        old.isPrefixOf parent = true := by
      simpa [Lean.Name.isPrefixOf] using ancestor
    rcases second with rfl | ancestor
    · simp only [nameNumeralBound] at upper
      omega
    · rw [hparent] at ancestor
      cases ancestor

theorem numeric_child_apart (reserved : List Lean.Name)
    (parent : Lean.Name) (label : String) (old : Lean.Name) (hold : old ∈ reserved)
    (hparent : old.isPrefixOf parent = false) :
    Apart (.str (.num parent (numeralBound reserved)) label) old :=
  ⟨numeric_child_not_prefix_old reserved parent label old hold,
   old_not_prefix_numeric_child reserved parent label old hold hparent⟩

theorem suffix_not_prefix_aux (aux : Ix.Name) (old : Lean.Name)
    (hold : old ∈ auxSuffixFamilies aux) : old.isPrefixOf (keyName aux) = false := by
  unfold auxSuffixFamilies at hold
  obtain ⟨label, _, rfl⟩ := List.mem_map.mp hold
  exact str_not_prefix_parent _ _

/-- Proof abbreviations matching the runtime fallback definition exactly. -/
abbrev ctorReserved (forbidden : List Lean.Name) (aux : Ix.Name)
    (ctorRoots : List Lean.Name) : List Lean.Name :=
  keyName aux :: auxSuffixFamilies aux ++ ctorRoots ++ forbidden

abbrev ctorFallback (forbidden : List Lean.Name) (aux : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) : Ix.Name :=
  Ix.Name.mkStr (Ix.Name.mkNat aux (numeralBound (ctorReserved forbidden aux ctorRoots)))
    s!"_ctor_{index}"

theorem fallback_apart_suffix (forbidden : List Lean.Name) (aux : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) (old : Lean.Name)
    (hold : old ∈ auxSuffixFamilies aux) :
    Apart (keyName (ctorFallback forbidden aux index ctorRoots)) old := by
  exact numeric_child_apart (ctorReserved forbidden aux ctorRoots) (keyName aux)
    s!"_ctor_{index}" old (by simp [ctorReserved, hold])
    (suffix_not_prefix_aux aux old hold)

theorem fallback_apart_ctorRoot (forbidden : List Lean.Name) (aux : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) (old : Lean.Name)
    (hold : old ∈ ctorRoots) (hparent : old.isPrefixOf (keyName aux) = false) :
    Apart (keyName (ctorFallback forbidden aux index ctorRoots)) old := by
  exact numeric_child_apart (ctorReserved forbidden aux ctorRoots) (keyName aux)
    s!"_ctor_{index}" old (by simp [ctorReserved, hold]) hparent

private theorem apart_of_check {a b : Lean.Name}
    (h : (!b.isPrefixOf a && !a.isPrefixOf b) = true) : Apart a b := by
  cases hab : a.isPrefixOf b <;> cases hba : b.isPrefixOf a <;>
    simp_all [Apart]

theorem checked_apart_suffix {forbidden : List Lean.Name} {aux candidate : Ix.Name}
    {ctorRoots : List Lean.Name} (hfree : ctorFamilyFree forbidden aux candidate ctorRoots = true)
    {old : Lean.Name} (hold : old ∈ auxSuffixFamilies aux) : Apart (keyName candidate) old := by
  have tested : (auxSuffixFamilies aux).all (fun root =>
      !root.isPrefixOf (keyName candidate) && !(keyName candidate).isPrefixOf root) = true := by
    cases ht : (auxSuffixFamilies aux).all (fun root =>
        !root.isPrefixOf (keyName candidate) && !(keyName candidate).isPrefixOf root) with
    | false => simp [ctorFamilyFree, ht] at hfree
    | true => rfl
  exact apart_of_check ((List.all_eq_true.mp tested) old hold)

theorem checked_apart_ctorRoot {forbidden : List Lean.Name} {aux candidate : Ix.Name}
    {ctorRoots : List Lean.Name} (hfree : ctorFamilyFree forbidden aux candidate ctorRoots = true)
    {old : Lean.Name} (hold : old ∈ ctorRoots) : Apart (keyName candidate) old := by
  have tested : ctorRoots.all (fun root =>
      !root.isPrefixOf (keyName candidate) && !(keyName candidate).isPrefixOf root) = true := by
    cases ht : ctorRoots.all (fun root =>
        !root.isPrefixOf (keyName candidate) && !(keyName candidate).isPrefixOf root) with
    | false => simp [ctorFamilyFree, ht] at hfree
    | true => rfl
  exact apart_of_check ((List.all_eq_true.mp tested) old hold)

/-- Every returned constructor family is apart from each future auxiliary
suffix family, without a caller/state premise. -/
theorem freshCtorFamily_apart_suffix (forbidden : List Lean.Name) (aux candidate : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) (old : Lean.Name)
    (hold : old ∈ auxSuffixFamilies aux) :
    Apart (keyName (freshCtorFamily forbidden aux candidate index ctorRoots)) old := by
  unfold freshCtorFamily
  split
  · rename_i hfree
    exact checked_apart_suffix hfree hold
  · exact fallback_apart_suffix forbidden aux index ctorRoots old hold

/-- Internal-state version: the old constructor root cannot contain the
current auxiliary root. The allocation forest must establish `hparent`. -/
theorem freshCtorFamily_apart_ctorRoot (forbidden : List Lean.Name) (aux candidate : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name) (old : Lean.Name)
    (hold : old ∈ ctorRoots) (hparent : old.isPrefixOf (keyName aux) = false) :
    Apart (keyName (freshCtorFamily forbidden aux candidate index ctorRoots)) old := by
  unfold freshCtorFamily
  split
  · rename_i hfree
    exact checked_apart_ctorRoot hfree hold
  · exact fallback_apart_ctorRoot forbidden aux index ctorRoots old hold hparent

theorem freshCtorFamily_apart_families (forbidden : List Lean.Name) (aux candidate : Ix.Name)
    (index : Nat) (ctorRoots : List Lean.Name)
    (forest : ∀ old ∈ ctorRoots, old.isPrefixOf (keyName aux) = false) :
    ∀ old ∈ auxSuffixFamilies aux ++ ctorRoots,
      Apart (keyName (freshCtorFamily forbidden aux candidate index ctorRoots)) old := by
  intro old hold
  rcases List.mem_append.mp hold with suffix | ctor
  · exact freshCtorFamily_apart_suffix forbidden aux candidate index ctorRoots old suffix
  · exact freshCtorFamily_apart_ctorRoot forbidden aux candidate index ctorRoots old ctor
      (forest old ctor)

/-! Fixed-parent root shapes. Shape alone excludes proper prefixes; source
protection or the allocated-name list is still needed to exclude equality. -/

inductive AuxRoot (parent : Lean.Name) : Lean.Name → Prop
  | direct (label : String) : AuxRoot parent (.str parent label)
  | fresh (index : Nat) (label : String) : AuxRoot parent (.str (.num parent index) label)

theorem freshFamily_shape (names : List Lean.Name) (parent : Ix.Name) (label : String) :
    AuxRoot (keyName parent) (keyName (freshFamily names parent label)) := by
  unfold freshFamily
  dsimp only
  split
  · exact AuxRoot.direct _
  · exact AuxRoot.fresh _ _

theorem auxRoot_prefix_eq {parent a b : Lean.Name} (ha : AuxRoot parent a)
    (hb : AuxRoot parent b) (h : a.isPrefixOf b = true) : a = b := by
  cases ha with
  | direct la =>
    cases hb with
    | direct lb =>
      exact prefix_eq_of_parts_eq (by simp [Lean.Name.getNumParts]) h
    | fresh k lb =>
      have step : Lean.Name.str parent la = .str (.num parent k) lb ∨
          (Lean.Name.str parent la).isPrefixOf (.num parent k) = true := by
        simpa [Lean.Name.isPrefixOf] using h
      rcases step with equal | ancestor
      · exact equal
      · have impossible : Lean.Name.str parent la = .num parent k :=
          prefix_eq_of_parts_eq (by simp [Lean.Name.getNumParts]) ancestor
        cases impossible
  | fresh k la =>
    cases hb with
    | direct lb =>
      have impossible := prefix_parts_le h
      simp only [Lean.Name.getNumParts] at impossible
      omega
    | fresh j lb =>
      exact prefix_eq_of_parts_eq (by simp [Lean.Name.getNumParts]) h

theorem auxRoot_apart_of_ne {parent a b : Lean.Name} (ha : AuxRoot parent a)
    (hb : AuxRoot parent b) (hne : a ≠ b) : Apart a b := by
  constructor
  · apply Bool.eq_false_iff.mpr
    intro h
    exact hne (auxRoot_prefix_eq ha hb h)
  · apply Bool.eq_false_iff.mpr
    intro h
    exact hne (auxRoot_prefix_eq hb ha h).symm

/-- The internal premise of `freshCtorFamily_apart_ctorRoot` follows once
the state invariant records an old constructor as a strict descendant of
some auxiliary root with the common parent. Its owner may be the current
auxiliary or any earlier auxiliary. No distinct-owner premise is needed. -/
theorem ctorRoot_not_prefix_auxRoot {parent owner current old : Lean.Name}
    (ownerShape : AuxRoot parent owner) (currentShape : AuxRoot parent current)
    (child : owner.isPrefixOf old = true) (strict : old ≠ owner) :
    old.isPrefixOf current = false := by
  apply Bool.eq_false_iff.mpr
  intro backwards
  have owners := auxRoot_prefix_eq ownerShape currentShape (prefix_trans child backwards)
  have forwardBound := prefix_parts_le child
  have backwardBound := prefix_parts_le backwards
  rw [← owners] at backwardBound
  have equal : owner = old := prefix_eq_of_parts_eq (by omega) child
  exact strict equal.symm

/-- A previous auxiliary root is apart from the next allocation provided
its actual structural name is in the forbidden list. No cached-hash law. -/
theorem freshFamily_apart_old_aux (names : List Lean.Name) (parent : Ix.Name)
    (label : String) (old : Lean.Name) (hold : old ∈ names)
    (shape : AuxRoot (keyName parent) old) :
    Apart (keyName (freshFamily names parent label)) old := by
  have free := freshFamily_free names parent label old hold
  have different : keyName (freshFamily names parent label) ≠ old := by
    intro equal
    rw [equal, prefix_refl] at free
    cases free
  exact auxRoot_apart_of_ne (freshFamily_shape names parent label) shape different

end Ix.Compile.Canon.FreshFamilySeparation
