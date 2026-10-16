import Ix.CompileCert.Canon.Sort

/-! # Pass 1's refinement: grouping adjacent equal members

CS-01, ported from the donor `a9cf3607` (`Canon/Group`) and adapted to
today's grouping. The donor's `groupAdjacent` is gone: `refineClass` groups
with `Ix.Common`'s `List.groupByM`, which also compares each element with
its predecessor (`eq later earlier`) but leaves its last group reversed.

* `groupAdjP` (the donor's grouping, in `Except`): the groups concatenate
  to the input, are nonempty, adjacent members of a group compare equal, and
  the first member of each group differs from the last member of the group
  before (`groupAdjP_spec`);
* `groupByM_eq`: `List.groupByM` in `Except` is `groupAdjP` with its last
  group reversed (`lastRev`), so group by group the same members
  (`lastRev_getElem_mem`, `mem_lastRev`); only membership matters, since
  `refineClass` re-sorts every group by name hash;
* `groupByM_sim`: the grouping run in `CmpM` with a cached comparison is the
  pure one. -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (MutConst)
open Ix.CompileCert.Loop (except_bind_ok)

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
variable {α ε : Type} (eq : α → α → Except ε Bool)

/-- `groupAdjacent.go` in `Except`. -/
def groupGoP (prev : α) (cur : List α) (acc : List (List α)) : List α → Except ε (List (List α))
  | [] => pure (cur.reverse :: acc).reverse
  | a :: as => do
    if ← eq a prev then groupGoP a (a :: cur) acc as else groupGoP a [a] (cur.reverse :: acc) as

/-- `groupAdjacent` in `Except`. -/
def groupAdjP : List α → Except ε (List (List α))
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

theorem groupsOK_extend {α ε : Type} {eq : α → α → Except ε Bool} {L : List (List α)}
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

theorem groupsOK_new {α ε : Type} {eq : α → α → Except ε Bool} {L : List (List α)}
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

theorem groupGoP_spec {α ε : Type} (eq : α → α → Except ε Bool) :
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
theorem groupAdjP_spec {α ε : Type} (eq : α → α → Except ε Bool) (xs : List α)
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


/-! ## `List.groupByM` is the reference grouping with its last group reversed -/

/-- The last group reversed. -/
def lastRev {α : Type} : List (List α) → List (List α)
  | [] => []
  | [g] => [g.reverse]
  | g :: g' :: gs => g :: lastRev (g' :: gs)

theorem lastRev_append_single {α : Type} (g : List α) :
    ∀ (L : List (List α)), lastRev (L ++ [g]) = L ++ [g.reverse]
  | [] => rfl
  | [x] => rfl
  | x :: y :: L => by
    show lastRev (x :: (y :: L ++ [g])) = _
    simp only [List.cons_append]
    show x :: lastRev (y :: (L ++ [g])) = _
    rw [← List.cons_append, lastRev_append_single g (y :: L)]
    rfl

theorem groupByMAux_eq {α ε : Type} (eq : α → α → Except ε Bool) :
    ∀ (as : List α) (prev : α) (g : List α) (acc : List (List α)),
      List.groupByMAux eq as ((prev :: g) :: acc) = (groupGoP eq prev (prev :: g) acc as).map lastRev := by
  intro as
  induction as with
  | nil =>
    intro prev g acc
    simp [List.groupByMAux, groupGoP, pure, Except.pure, Except.map, lastRev_append_single]
  | cons a as ih =>
    intro prev g acc
    simp only [List.groupByMAux, groupGoP]
    cases h : eq a prev with
    | error e => rfl
    | ok b =>
      cases b with
      | true =>
        simp only [bind, Except.bind, ↓reduceIte]
        exact ih a (prev :: g) acc
      | false =>
        simp only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
        exact ih a [] ((prev :: g).reverse :: acc)

/-- **`List.groupByM` is the reference grouping with its last group
reversed.** -/
theorem groupByM_eq {α ε : Type} (eq : α → α → Except ε Bool) (xs : List α) :
    List.groupByM eq xs = (groupAdjP eq xs).map lastRev := by
  cases xs with
  | nil => rfl
  | cons x xs => exact groupByMAux_eq eq xs x [] []

theorem lastRev_length {α : Type} : ∀ (L : List (List α)), (lastRev L).length = L.length
  | [] | [_] => rfl
  | _ :: g' :: gs => by simp [lastRev, lastRev_length (g' :: gs)]

theorem lastRev_getElem_mem {α : Type} :
    ∀ (L : List (List α)) (i : Nat) (h₁ : i < (lastRev L).length) (h₂ : i < L.length) (x : α),
      x ∈ (lastRev L)[i] ↔ x ∈ L[i]
  | [], _, _, h₂, _ => absurd h₂ (by simp)
  | [g], 0, _, _, x => by simp [lastRev]
  | [g], i + 1, _, h₂, _ => absurd h₂ (by simp)
  | g :: g' :: gs, 0, _, _, x => Iff.rfl
  | g :: g' :: gs, i + 1, h₁, h₂, x => by
    have h₁' : i < (lastRev (g' :: gs)).length := by
      simpa [lastRev] using h₁
    exact lastRev_getElem_mem (g' :: gs) i h₁' (by simpa using h₂) x

theorem mem_lastRev {α : Type} {L : List (List α)} {g : List α} (h : g ∈ lastRev L) :
    ∃ g' ∈ L, ∀ x, x ∈ g ↔ x ∈ g' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have hi' : i < L.length := by rw [lastRev_length] at hi; exact hi
  exact ⟨L[i], List.getElem_mem hi', fun x => lastRev_getElem_mem L i hi hi' x⟩

/-! ## The cached grouping is the pure one -/

theorem groupByMAux_sim {Inv : CmpState → Prop} {S : MutConst → Prop}
    {eqM : MutConst → MutConst → CmpM Bool} {eqE : MutConst → MutConst → Except CmpError Bool}
    (hsim : ∀ a b, S a → S b → Sim Inv (eqM a b) (eqE a b)) :
    ∀ (as : List MutConst) (acc : List (List MutConst)), (∀ x ∈ as, S x) → (∀ g ∈ acc, ∀ x ∈ g, S x) →
      Sim Inv (List.groupByMAux eqM as acc) (List.groupByMAux eqE as acc) := by
  intro as
  induction as with
  | nil => intro acc _ _; simp only [List.groupByMAux]; exact Sim.pure' _
  | cons a as ih =>
    intro acc has hacc
    match acc, hacc with
    | [], _ => simp only [List.groupByMAux]; exact Sim.pure' _
    | [] :: gs, _ => simp only [List.groupByMAux]; exact Sim.pure' _
    | (ag :: g) :: gs, hacc =>
      simp only [List.groupByMAux]
      refine Sim.bind (hsim a ag (has a (by simp)) (hacc (ag :: g) (by simp) ag (by simp))) fun b _ => ?_
      cases b with
      | true =>
        refine ih _ (fun x hx => has x (by simp [hx])) ?_
        intro g' hg' x hx
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · simp only [List.mem_cons] at hx
          rcases hx with hx | hx | hx
          · exact hx ▸ has _ (by simp)
          · exact hacc (ag :: g) (by simp) x (by simp [hx])
          · exact hacc (ag :: g) (by simp) x (by simp [hx])
        · exact hacc g' (by simp [hg']) x hx
      | false =>
        refine ih _ (fun x hx => has x (by simp [hx])) ?_
        intro g' hg' x hx
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | rfl | hg'
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; exact has _ (by simp)
        · exact hacc (ag :: g) (by simp) x (List.mem_reverse.mp hx)
        · exact hacc g' (by simp [hg']) x hx

theorem groupByM_sim {Inv : CmpState → Prop} {S : MutConst → Prop}
    {eqM : MutConst → MutConst → CmpM Bool} {eqE : MutConst → MutConst → Except CmpError Bool}
    (hsim : ∀ a b, S a → S b → Sim Inv (eqM a b) (eqE a b)) (xs : List MutConst)
    (hxs : ∀ x ∈ xs, S x) : Sim Inv (List.groupByM eqM xs) (List.groupByM eqE xs) := by
  cases xs with
  | nil => exact Sim.pure' _
  | cons x xs =>
    simp only [List.groupByM]
    exact groupByMAux_sim hsim xs [[x]] (fun y hy => hxs y (by simp [hy]))
      (fun g hg y hy => by simp at hg; subst hg; simp at hy; subst hy; exact hxs y (by simp))

end Ix.CompileCert.Canon
