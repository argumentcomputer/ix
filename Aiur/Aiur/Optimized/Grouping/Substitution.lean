import Aiur.Optimized.Grouping.Selection

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

def replacement (bindings : List (Nat × Polynomial F)) (v : Nat) : Polynomial F :=
  ((bindings.find? (fun b => b.1 == v)).map Prod.snd).getD (.var v)

omit [DecidableEq F] in
theorem replacement_sound (bindings : List (Nat × Polynomial F)) (a : Nat → F)
    (sound : ∀ b ∈ bindings, b.2.denote a = a b.1) (v : Nat) :
    (replacement bindings v).denote a = a v := by
  cases found : bindings.find? (fun b => b.1 == v) with
  | none => simp [replacement, found, Scalar.Circuit.ArithExpr.denote]
  | some b =>
    have index_eq : b.1 = v := beq_iff_eq.mp (List.find?_some (p := fun b : Nat × Polynomial F => b.1 == v) found)
    simpa [replacement, found, index_eq] using sound b (List.mem_of_find?_eq_some found)

def Layout.baseBindings (g : Layout F) (mode : Option Nat) : List (Nat × Polynomial F) :=
  g.members.flatMap fun m =>
    (m.selector, .const (selected mode m)) ::
      if mode = some m.selector then [] else
        m.privateCols.map fun v => (m.columns[v]?.getD 0, .const 0)

def Layout.base (g : Layout F) (mode : Option Nat) := replacement (g.baseBindings mode)

theorem Layout.base_sound (g : Layout F) (shapes : ∀ m ∈ g.members, m.Shape)
    (a : Nat → F) (valid : Satisfies g.constraints a) (mode : Option Nat)
    (selectors : ∀ m ∈ g.members, a m.selector = selected mode m) (v : Nat) :
    (g.base mode v).denote a = a v := by
  apply replacement_sound
  intro b hb
  obtain ⟨m, hm, hb⟩ := List.mem_flatMap.mp hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact (selectors m hm).symm
  · split at hb
    · simp at hb
    · rename_i different
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      have off : a m.selector = 0 := by simpa [selected, different] using selectors m hm
      exact (g.private_zero m hm (shapes m hm) a valid off v hv).symm

def Layout.backBindings (g : Layout F) (mode : Option Nat) : List (Nat × Polynomial F) :=
  let base := g.base mode
  g.members.flatMap fun m => m.writes.map fun (column, value) =>
    (column, if mode = some m.selector then value.subst base else .const 0)

def Layout.back (g : Layout F) (mode : Option Nat) : Nat → Polynomial F :=
  replacement (g.backBindings mode ++ g.baseBindings mode)

theorem Layout.write_equations (g : Layout F) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a) (w : Nat × Polynomial F) (hw : w ∈ m.writes) :
    a m.selector * (a w.1 - w.2.denote a) = 0 ∧ (1 - a m.selector) * a w.1 = 0 := by
  have h := g.member_satisfies m hm a valid
  constructor
  · exact h (.mul (.var m.selector) (.sub (.var w.1) w.2))
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨w, hw, by simp⟩))
  · exact h (privateZero m.selector w.1)
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨w, hw, by simp⟩))

theorem Layout.back_sound (g : Layout F) (shapes : ∀ m ∈ g.members, m.Shape)
    (a : Nat → F) (valid : Satisfies g.constraints a) (mode : Option Nat)
    (selectors : ∀ m ∈ g.members, a m.selector = selected mode m) (v : Nat) :
    (g.back mode v).denote a = a v := by
  have base := g.base_sound shapes a valid mode selectors
  apply replacement_sound
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨m, hm, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
    have eqs := g.write_equations m hm a valid w hw
    have sel := selectors m hm
    by_cases on : mode = some m.selector
    · have on' : a m.selector = 1 := by simpa [selected, on] using sel
      have equal : w.2.denote a = a w.1 := (sub_eq_zero.mp (by simpa [on'] using eqs.1)).symm
      change (if mode = some m.selector then w.2.subst (g.base mode) else .const 0).denote a = a w.1
      rw [ite_eq_left on, Polynomial.denote_subst]
      simpa only [base] using equal
    · have off : a m.selector = 0 := by simpa [selected, on] using sel
      simpa [on, Scalar.Circuit.ArithExpr.denote, off] using eqs.2.symm
  · obtain ⟨m, hm, hb⟩ := List.mem_flatMap.mp hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (selectors m hm).symm
    · split at hb
      · simp at hb
      · rename_i different
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
        have off : a m.selector = 0 := by simpa [selected, different] using selectors m hm
        exact (g.private_zero m hm (shapes m hm) a valid off v hv).symm

/-- A concrete extension of a source row: source columns, activation, then
private lifted arguments. The certificate checks this proposed extension;
no property of the placement heuristic is assumed. -/
def Member.embeddingBase (m : Member F) : Nat → Polynomial F :=
  replacement (((List.range m.origin.numVars).map fun v => (m.columns[v]?.getD 0, .var v)) ++
    [(m.selector, .const 1)])

def Member.embedding (m : Member F) : Nat → Polynomial F :=
  let columns := m.columns.toList
  let original := m.embeddingBase
  let base := fun column => if columns.contains column then original column else .const 0
  let writes := m.writes.map fun (column, value) => (column, value.subst base)
  fun v => match writes.find? (fun w => w.1 == v) with
    | some w => w.2
    | none => base v

end Aiur.Optimized.Grouping
