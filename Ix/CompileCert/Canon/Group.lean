import Ix.CompileCert.Canon.Sort
import Batteries.Tactic.OpenPrivate

/-!
# M7 L1, the refinement: grouping adjacent equal members

`Ix.Compile.Canon.groupAdjacent eq xs` (in `CmpM`) cuts `xs` into groups, comparing each
element with its predecessor (`eq later earlier`). `groupAdjP` is the same function in
`Except`; `groupAdjacent_sim` says the cached run returns its result. `groupAdjP_spec`: the
groups concatenate to the input, are nonempty, adjacent members of a group compare equal,
and the first member of each group differs from the last member of the group before.
-/

open private Ix.Compile.Canon.groupAdjacent.go from Ix.Compile.Canon.Classes

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (MutConst)

/-! ## Sorted lists under append -/

theorem sorted_append_iff {α : Type} {R : α → α → Prop} :
    ∀ (l₁ l₂ : List α), Sorted R (l₁ ++ l₂) ↔
      Sorted R l₁ ∧ Sorted R l₂ ∧ (∀ x y, l₁.getLast? = some x → l₂.head? = some y → R x y)
  | [], l₂ => by simp [Sorted]
  | [x], [] => by simp [Sorted]
  | [x], y :: l₂ => by
    simp only [List.singleton_append, sorted_cons_cons, List.getLast?_singleton, List.head?_cons,
      Option.some.injEq]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨trivial, h', fun a b ha hb => by subst ha; subst hb; exact h⟩
    · rintro ⟨-, h', h⟩; exact ⟨h x y rfl rfl, h'⟩
  | x :: x' :: l₁, l₂ => by
    rw [List.cons_append, List.cons_append, sorted_cons_cons, ← List.cons_append,
      sorted_append_iff (x' :: l₁) l₂, sorted_cons_cons]
    have : (x :: x' :: l₁).getLast? = (x' :: l₁).getLast? := by simp [List.getLast?_cons]
    rw [this]
    constructor
    · rintro ⟨h, h1, h2, h3⟩; exact ⟨⟨h, h1⟩, h2, h3⟩
    · rintro ⟨⟨h, h1⟩, h2, h3⟩; exact ⟨h, h1, h2, h3⟩

/-! ## The pure grouping -/

section
variable {α : Type} (eq : α → α → Except String Bool)

/-- `groupAdjacent.go` in `Except`. -/
def groupGoP (prev : α) (cur : List α) (acc : List (List α)) : List α → Except String (List (List α))
  | [] => pure (cur.reverse :: acc).reverse
  | a :: as => do
    if ← eq a prev then groupGoP a (a :: cur) acc as else groupGoP a [a] (cur.reverse :: acc) as

/-- `groupAdjacent` in `Except`. -/
def groupAdjP : List α → Except String (List (List α))
  | [] => pure []
  | x :: xs => groupGoP eq x [x] [] xs

/-- Consecutive groups: the first member of the later one differs from the last member of the
earlier one. -/
def Breaks (g g' : List α) : Prop := ∀ x y, g.getLast? = some x → g'.head? = some y → eq y x = .ok false

/-- What a grouping guarantees. -/
structure GroupsOK (gs : List (List α)) : Prop where
  nonempty : ∀ g ∈ gs, g ≠ []
  inner : ∀ g ∈ gs, Sorted (fun x y => eq y x = .ok true) g
  breaks : Sorted (Breaks eq) gs

end

theorem groupsOK_extend {α : Type} {eq : α → α → Except String Bool} {L : List (List α)}
    {g : List α} {prev a : α} (hok : GroupsOK eq (L ++ [g])) (hlast : g.getLast? = some prev)
    (hb : eq a prev = .ok true) : GroupsOK eq (L ++ [g ++ [a]]) := by
  obtain ⟨hne, hin, hbr⟩ := hok
  have hg : g ≠ [] := fun e => by rw [e] at hlast; cases hlast
  refine ⟨fun h hh => ?_, fun h hh => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hne h (by simp [hh])
    · simp
  · simp only [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hin h (by simp [hh])
    · refine (sorted_append_iff _ _).2 ⟨hin g (by simp), trivial, fun x y hx hy => ?_⟩
      rw [hlast] at hx; cases hx; simp at hy; subst hy; exact hb
  · obtain ⟨h1, -, h3⟩ := (sorted_append_iff _ _).1 hbr
    refine (sorted_append_iff _ _).2 ⟨h1, trivial, fun x y hx hy => ?_⟩
    simp only [List.head?_cons, Option.some.injEq] at hy; subst hy
    intro u v hu hv
    have hv' : g.head? = some v := by
      cases g with
      | nil => exact absurd rfl hg
      | cons c g => simpa using hv
    exact h3 x g hx rfl u v hu hv'

theorem groupsOK_new {α : Type} {eq : α → α → Except String Bool} {L : List (List α)}
    {g : List α} {prev a : α} (hok : GroupsOK eq (L ++ [g])) (hlast : g.getLast? = some prev)
    (hb : eq a prev = .ok false) : GroupsOK eq (L ++ [g] ++ [[a]]) := by
  obtain ⟨hne, hin, hbr⟩ := hok
  refine ⟨fun h hh => ?_, fun h hh => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hne h (by simpa using hh)
    · simp
  · simp only [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hin h (by simpa using hh)
    · trivial
  · refine (sorted_append_iff _ _).2 ⟨hbr, trivial, fun x y hx hy => ?_⟩
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hx
    simp only [List.head?_cons, Option.some.injEq] at hy
    subst hx; subst hy
    intro u v hu hv
    rw [hlast] at hu; cases hu; simp at hv; subst hv; exact hb

theorem groupGoP_spec {α : Type} (eq : α → α → Except String Bool) :
    ∀ (rest : List α) (prev : α) (cur : List α) (acc : List (List α)) (gs : List (List α)),
      cur.head? = some prev → GroupsOK eq (acc.reverse ++ [cur.reverse]) →
      groupGoP eq prev cur acc rest = .ok gs →
      GroupsOK eq gs ∧ gs.flatten = (acc.reverse ++ [cur.reverse]).flatten ++ rest := by
  intro rest
  induction rest with
  | nil =>
    intro prev cur acc gs _ hok h
    simp only [groupGoP, pure, Except.pure, Except.ok.injEq] at h; subst h
    simp only [List.reverse_cons, List.append_nil]
    exact ⟨hok, by simp⟩
  | cons a as ih =>
    intro prev cur acc gs hhd hok h
    simp only [groupGoP] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok.1 h
    have hlast : (cur.reverse).getLast? = some prev := by rw [List.getLast?_reverse]; exact hhd
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      have hok' : GroupsOK eq (acc.reverse ++ [(a :: cur).reverse]) := by
        simpa using groupsOK_extend hok hlast hb
      obtain ⟨r1, r2⟩ := ih a (a :: cur) acc gs rfl hok' h
      exact ⟨r1, by rw [r2]; simp⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hok' : GroupsOK eq ((cur.reverse :: acc).reverse ++ [[a].reverse]) := by
        simpa using groupsOK_new hok hlast hb
      obtain ⟨r1, r2⟩ := ih a [a] (cur.reverse :: acc) gs rfl hok' h
      exact ⟨r1, by rw [r2]; simp⟩

/-- **The grouping**: the groups concatenate to the input, are nonempty, adjacent members of a
group compare equal, and consecutive groups break. -/
theorem groupAdjP_spec {α : Type} (eq : α → α → Except String Bool) (xs : List α)
    (gs : List (List α)) (h : groupAdjP eq xs = .ok gs) : GroupsOK eq gs ∧ gs.flatten = xs := by
  cases xs with
  | nil =>
    simp only [groupAdjP, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨⟨by simp, by simp, trivial⟩, rfl⟩
  | cons x xs =>
    simp only [groupAdjP] at h
    obtain ⟨r1, r2⟩ := groupGoP_spec eq xs x [x] [] gs rfl
      ⟨by simp, by simp [Sorted], trivial⟩ h
    exact ⟨r1, by rw [r2]; simp⟩

/-! ## The cached grouping is the pure one -/

theorem groupGo_sim {Inv : CmpState → Prop} {S : MutConst → Prop}
    {eqM : MutConst → MutConst → CmpM Bool} {eqE : MutConst → MutConst → Except String Bool}
    (hsim : ∀ a b, S a → S b → Sim Inv (eqM a b) (eqE a b)) :
    ∀ (rest : List MutConst) (prev : MutConst) (cur : List MutConst) (acc : List (List MutConst)),
      S prev → (∀ x ∈ rest, S x) →
      Sim Inv (Ix.Compile.Canon.groupAdjacent.go eqM prev cur acc rest) (groupGoP eqE prev cur acc rest) := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _; exact Sim.pure' _
  | cons a as ih =>
    intro prev cur acc hp hr
    simp only [Ix.Compile.Canon.groupAdjacent.go, groupGoP]
    refine Sim.bind (hsim a prev (hr a (by simp)) hp) fun b _ => ?_
    cases b
    · exact ih a [a] (cur.reverse :: acc) (hr a (by simp)) (fun x hx => hr x (by simp [hx]))
    · exact ih a (a :: cur) acc (hr a (by simp)) (fun x hx => hr x (by simp [hx]))

theorem groupAdjacent_sim {Inv : CmpState → Prop} {S : MutConst → Prop}
    {eqM : MutConst → MutConst → CmpM Bool} {eqE : MutConst → MutConst → Except String Bool}
    (hsim : ∀ a b, S a → S b → Sim Inv (eqM a b) (eqE a b)) (xs : List MutConst)
    (hxs : ∀ x ∈ xs, S x) : Sim Inv (groupAdjacent eqM xs) (groupAdjP eqE xs) := by
  cases xs with
  | nil => exact Sim.pure' _
  | cons x xs =>
    simp only [groupAdjacent, groupAdjP]
    exact groupGo_sim hsim xs x [x] [] (hxs x (by simp)) (fun y hy => hxs y (by simp [hy]))

end Ix.CompileCert.Canon
