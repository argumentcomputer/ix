module

public import IxC.Kernel.Verify.Rename.UnionJoin
public import IxC.Kernel.Units

@[expose] public section

/-!
# The units check, proved (S1)

The fold's units check (`checkUnits`, `IxC/Kernel/Units.lean`, run by
`Cached.checkDecls` after it accepts) decides what the union of two accepted
lists (`Cached.AcceptsRef.union`) takes of each list:

- `unitsOf` splits a list into units and flattens back to it
  (`unitsOf_flatten`); behind a front of ungenerated declarations, the front's
  declarations are units of their own (`unitsOf_append_front`);
- the check passes exactly when no unit holds a basis record and no two units
  declare a common base (`checkUnitsGo_ok_iff`);
- so a passing check over `front ++ rest`, whose front declares every prelude
  role, gives `UnitsOk front (unitsOf rest)` (`unitsOk_of_check`).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md : Mode}

theorem unitBases_eq (u : List (Declaration md)) : unitBases u = basesOf u := rfl

/-! ## Units of a list -/

theorem unitsGo_flatten : ∀ (acc ds : List (Declaration md)),
    (unitsGo acc ds).flatten = acc.reverse ++ ds
  | acc, [] => by
    unfold unitsGo
    split
    · rename_i h
      rw [List.isEmpty_iff.mp h]
      rfl
    · simp
  | acc, d :: ds => by
    unfold unitsGo
    split
    · rw [unitsGo_flatten]
      simp
    · rw [List.flatten_cons, unitsGo_flatten]
      simp

/-- **A list's units flatten back to it.** -/
theorem unitsOf_flatten (ds : List (Declaration md)) : (unitsOf ds).flatten = ds := by
  show (unitsGo [] ds).flatten = ds
  simpa using unitsGo_flatten [] ds

/-- **Behind a front of ungenerated declarations**, each front declaration is
a unit of its own. -/
theorem unitsOf_append_front : ∀ (front rest : List (Declaration md)),
    (∀ d ∈ front, d.isGenerated = false) →
      unitsOf (front ++ rest) = front.map (fun d => [d]) ++ unitsOf rest
  | [], _, _ => rfl
  | d :: front, rest, h => by
    have hd := h d List.mem_cons_self
    have ih := unitsOf_append_front front rest (fun d' h' => h d' (List.mem_cons_of_mem _ h'))
    unfold unitsOf at ih ⊢
    rw [List.cons_append, unitsGo, if_neg (by rw [hd]; exact Bool.false_ne_true), ih]
    rfl

/-- **A lowering**: generated records, then one declaration that is not
(a record's lowering: a mutual or nested block's model records and its
`indDecl`; any other record's one declaration). -/
def IsLowering (l : List (Declaration md)) : Prop :=
  ∃ gs d, l = gs ++ [d] ∧ (∀ g ∈ gs, g.isGenerated = true) ∧ d.isGenerated = false

theorem unitsGo_lowering : ∀ (acc gs : List (Declaration md)) (d : Declaration md)
    (rest : List (Declaration md)), (∀ g ∈ gs, g.isGenerated = true) → d.isGenerated = false →
      unitsGo acc (gs ++ d :: rest) = (acc.reverse ++ gs ++ [d]) :: unitsGo [] rest
  | acc, [], d, rest, _, hd => by
    rw [List.nil_append, unitsGo, if_neg (by rw [hd]; exact Bool.false_ne_true)]
    simp
  | acc, g :: gs, d, rest, hg, hd => by
    rw [List.cons_append, unitsGo, if_pos (hg g List.mem_cons_self),
      unitsGo_lowering (g :: acc) gs d rest (fun g' h => hg g' (List.mem_cons_of_mem _ h)) hd]
    simp

/-- **Lowerings are their own units**: the units of a concatenation of
lowerings are the lowerings. -/
theorem unitsOf_lowerings : ∀ ls : List (List (Declaration md)), (∀ l ∈ ls, IsLowering l) →
    unitsOf ls.flatten = ls
  | [], _ => rfl
  | l :: ls, h => by
    obtain ⟨gs, d, rfl, hg, hd⟩ := h l List.mem_cons_self
    have ih := unitsOf_lowerings ls (fun l' h' => h l' (List.mem_cons_of_mem _ h'))
    unfold unitsOf at ih ⊢
    rw [List.flatten_cons, List.append_assoc, List.singleton_append,
      unitsGo_lowering [] gs d _ hg hd, ih]
    simp

/-! ## The check, decided -/

theorem contains_foldl_insert (i : Nat) : ∀ (l : List (Key md)) (m : Std.HashMap (Key md) Nat)
    (k : Key md), (l.foldl (fun m j => m.insert j i) m).contains k = true ↔
      m.contains k = true ∨ k ∈ l
  | [], m, k => by simp
  | j :: l, m, k => by
    rw [List.foldl_cons, contains_foldl_insert i l, Std.HashMap.contains_insert, List.mem_cons]
    simp only [Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h

/-- **A prelude role's key**, decided. -/
theorem Key.isPreludeRole_iff : ∀ {k : Key md}, k.isPreludeRole = true ↔ IsPre k
  | .id _ => by simp [Key.isPreludeRole, IsPre]
  | .aux _ _ => by simp [Key.isPreludeRole, IsPre]
  | .role r => by
    have h : preludeShape.any (·.contains r) = true ↔ r ∈ preludeRoles := by
      cases r <;> decide
    simp only [Key.isPreludeRole, IsPre, Key.role.injEq]
    rw [h]
    exact ⟨fun h => ⟨r, h, rfl⟩, fun ⟨r', h, e⟩ => e ▸ h⟩

/-- **Past the front**: every unit at a position past the front's
(`preludeSize`) declares no prelude role. -/
def PastFront : List (List (Declaration md)) → Nat → Prop
  | [], _ => True
  | u :: us, i => (preludeSize ≤ i → ∀ j ∈ basesOf u, j.isPreludeRole = false) ∧
      PastFront us (i + u.length)

theorem PastFront.append : ∀ {xs ys : List (List (Declaration md))} {i : Nat},
    PastFront (xs ++ ys) i → PastFront ys (i + xs.flatten.length)
  | [], _, i, h => by simpa using h
  | x :: xs, ys, i, h => by
    have := PastFront.append h.2
    rwa [List.flatten_cons, List.length_append, ← Nat.add_assoc]

theorem PastFront.all : ∀ {us : List (List (Declaration md))} {i : Nat}, PastFront us i →
    preludeSize ≤ i → ∀ u ∈ us, ∀ j ∈ basesOf u, j.isPreludeRole = false
  | [], _, _, _ => fun _ h => nomatch h
  | u :: us, i, h, hi => by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1 hi
    · exact PastFront.all h.2 (by omega) v hv

/-- **The units check passes exactly when** no unit holds a basis record,
every unit has its shape (`unitShapeOk`), no unit declares a base `seen`
holds, no two units declare a common base, and no unit past the front
declares a prelude role. -/
theorem checkUnitsGo_ok_iff : ∀ (seen : Std.HashMap (Key md) Nat)
    (us : List (List (Declaration md))) (i : Nat),
    checkUnitsGo seen us i = .ok () ↔
      (∀ u ∈ us, ∀ d ∈ u, d.isBasis = false) ∧ (∀ u ∈ us, unitShapeOk u = true) ∧
        (∀ u ∈ us, ∀ j ∈ basesOf u, seen.contains j = false) ∧
          (us.Pairwise fun u v => ∀ j ∈ basesOf u, j ∉ basesOf v) ∧ PastFront us i
  | seen, [], i => by simp [checkUnitsGo, PastFront]; rfl
  | seen, u :: us, i => by
    unfold checkUnitsGo
    by_cases hb : u.any Declaration.isBasis = true
    · rw [if_pos hb]
      constructor
      · intro h; exact nomatch h
      · rintro ⟨h1, -, -, -, -⟩
        obtain ⟨d, hd, hdb⟩ := List.any_eq_true.mp hb
        rw [h1 u List.mem_cons_self d hd] at hdb
        exact nomatch hdb
    · rw [if_neg hb]
      have hnb : ∀ d ∈ u, d.isBasis = false := fun d hd => by
        cases hdb : d.isBasis
        · rfl
        · exact absurd (List.any_eq_true.mpr ⟨d, hd, hdb⟩) hb
      by_cases hs : unitShapeOk u = true
      · rw [if_neg (by simp [hs])]
        cases hp : (if preludeSize ≤ i then (unitBases u).find? Key.isPreludeRole else none) with
        | some j =>
          constructor
          · intro h; exact nomatch h
          · rintro ⟨-, -, -, -, hpf, -⟩
            by_cases hi : preludeSize ≤ i
            · rw [if_pos hi] at hp
              have hj := List.mem_of_find?_eq_some hp
              have hc := List.find?_some hp
              rw [hpf hi j hj] at hc
              exact nomatch hc
            · rw [if_neg hi] at hp
              exact nomatch hp
        | none =>
          have hpf : preludeSize ≤ i → ∀ j ∈ basesOf u, j.isPreludeRole = false :=
            fun hi j hj => by
              rw [if_pos hi] at hp
              have := List.find?_eq_none.mp hp j hj
              simpa using this
          cases hf : (unitBases u).find? seen.contains with
          | some j =>
            constructor
            · intro h; exact nomatch h
            · rintro ⟨-, -, h2, -, -⟩
              have hj := List.mem_of_find?_eq_some hf
              have hc := List.find?_some hf
              rw [h2 u List.mem_cons_self j hj] at hc
              exact nomatch hc
          | none =>
            have hu : ∀ j ∈ basesOf u, seen.contains j = false := fun j hj => by
              have := List.find?_eq_none.mp hf j hj
              simpa using this
            rw [checkUnitsGo_ok_iff _ us _]
            simp only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons, PastFront]
            constructor
            · rintro ⟨h1, h0, h2, h3, h4⟩
              refine ⟨⟨hnb, h1⟩, ⟨hs, h0⟩, ⟨hu, fun v hv j hj => ?_⟩,
                ⟨fun v hv j hj hjv => ?_, h3⟩, hpf, h4⟩
              · cases hc : seen.contains j
                · rfl
                · have := h2 v hv j hj
                  rw [← Bool.not_eq_true, contains_foldl_insert] at this
                  exact absurd (Or.inl hc) this
              · have := h2 v hv j hjv
                rw [← Bool.not_eq_true, contains_foldl_insert] at this
                exact this (Or.inr hj)
            · rintro ⟨⟨-, h1⟩, ⟨-, h0⟩, ⟨-, h2⟩, ⟨h3, h4⟩, -, h5⟩
              refine ⟨h1, h0, fun v hv j hj => ?_, h4, h5⟩
              rw [← Bool.not_eq_true, contains_foldl_insert]
              rintro (hc | hc)
              · rw [h2 v hv j hj] at hc; exact nomatch hc
              · exact h3 v hv j hc hj
      · rw [if_pos (by simpa using hs)]
        constructor
        · intro h; exact nomatch h
        · rintro ⟨-, h0, -, -, -⟩
          exact (hs (h0 u List.mem_cons_self)).elim

/-! ## Well formed units -/

theorem flatten_singletons {α : Type} : ∀ (l : List α), (l.map fun d => [d]).flatten = l
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.flatten_cons, flatten_singletons l]; rfl

/-- **The units check gives well formed units.** A fold input that is a front
of `preludeSize` ungenerated declarations followed by `rest`, and that passes
the units check: `rest`'s units are well formed after the front (`UnitsOk`),
and flatten back to `rest`. -/
theorem unitsOk_of_check {ds : Array (Declaration md)} {front rest : List (Declaration md)}
    (hds : ds.toList = front ++ rest) (hgen : ∀ d ∈ front, d.isGenerated = false)
    (hlen : front.length = preludeSize) (h : checkUnits ds = .ok ()) :
    UnitsOk front (unitsOf rest) ∧ (unitsOf rest).flatten = rest := by
  unfold checkUnits at h
  rw [hds, unitsOf_append_front front rest hgen] at h
  obtain ⟨hnb, -, -, hpw, hpast⟩ := (checkUnitsGo_ok_iff {} _ 0).mp h
  have hrest := hpast.append
  have hflat : (front.map fun d => [d]).flatten.length = front.length := by
    rw [flatten_singletons]
  rw [hflat, Nat.zero_add, hlen] at hrest
  have hpre := hrest.all (Nat.le_refl _)
  rw [List.pairwise_append] at hpw
  obtain ⟨-, hpr, hcross⟩ := hpw
  have hfront : ∀ u ∈ unitsOf rest, ∀ j ∈ basesOf u, j ∉ basesOf front := by
    intro u hu j hju hjf
    obtain ⟨d, hd, n, hn, rfl⟩ := mem_basesOf.mp hjf
    exact hcross [d] (List.mem_map_of_mem hd) u hu n.base
      (mem_basesOf.mpr ⟨d, List.mem_singleton_self d, n, hn, rfl⟩) hju
  refine ⟨UnitsOk.of_names hpr hfront (fun u hu j hju hj => ?_) ?_, unitsOf_flatten rest⟩
  · have := hpre u hu j hju
    rw [Key.isPreludeRole_iff.mpr hj] at this
    exact nomatch this
  · intro u hu d hd k hk
    have := hnb u (List.mem_append_right _ hu) d hd
    rw [hk] at this
    exact nomatch this

end Ix.Kernel
