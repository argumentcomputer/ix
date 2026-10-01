/-
  Fast pinned table order (phase-1 finish and phase 2).

  `pinnedOrder` places one term at a time: among the remaining terms whose
  nearest stored descendants are all placed, the one with the larger in-degree,
  then the smaller ID. The specification scans every remaining term at every
  step (quadratic in the stored terms). `pinnedOrderFast` keeps the ready terms
  in a `Std.TreeSet` of priority keys (`pinnedKey`, in-degree descending then
  ID ascending) and, after each placement, adds the users of the placed term
  that became ready: O((k + edges) log k). The nearest stored descendants are
  still computed by `pinnedDeps`.

  `pinnedOrder_eq_fast : @pinnedOrder = @pinnedOrderFast` (`@[csimp]`) holds
  for every input: the fast placement runs when the stored terms are strictly
  increasing (the case of every caller), and the specification otherwise.
-/
module

public import Ix.Sharing.Exact.Uniform
public import Ix.Sharing.Exact.PinnedDeps
import all Ix.Sharing.Exact.Uniform
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas
import Std.Data.TreeSet.Lemmas

public section

namespace Ix.Sharing.Exact

/-! ## The placement -/

/-- Priority key of a term in the pinned order (smaller first): the larger
in-degree first, then the smaller ID, for terms below `B` with in-degree at
most `D`. -/
@[inline] def pinnedKey (deg : Array Nat) (D B t : Nat) : Nat := (D - deg[t]!) * B + t

/-- Whether every nearest stored descendant of `t` is placed. -/
@[inline] def pinnedReady (deps : Std.HashMap Nat (Array Nat)) (placed : Std.HashSet Nat)
    (t : Nat) : Bool :=
  (deps.getD t #[]).all placed.contains

/-- The users of every term: `u` (once per occurrence) for each stored `u`
with `d` among its nearest stored descendants, at `d`. -/
def pinnedUsers (deps : Std.HashMap Nat (Array Nat)) (stored : Array Nat) :
    Std.HashMap Nat (Array Nat) :=
  stored.foldl (fun us u => (deps.getD u #[]).foldl
    (fun us d => us.alter d fun o => some ((o.getD #[]).push u)) us) {}

/-- Add the keys of the unplaced terms of `us` that are ready. -/
def pinnedWake (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) (D B : Nat)
    (placed : Std.HashSet Nat) (us : Array Nat) (ready : Std.TreeSet Nat) : Std.TreeSet Nat :=
  us.foldl (fun r u =>
    if !placed.contains u && pinnedReady deps placed u then r.insert (pinnedKey deg D B u)
    else r) ready

/-- `pinnedPlace` with the ready terms kept as keys in `ready`; the unplaced
terms are the stored terms not in `placed`. -/
def pinnedPlaceFast (deg : Array Nat) (deps users : Std.HashMap Nat (Array Nat)) (D B : Nat)
    (stored : Array Nat) :
    Nat → Array Nat → Std.HashSet Nat → Std.TreeSet Nat → Array Nat
  | 0, order, placed, _ => order ++ stored.filter (!placed.contains ·)
  | fuel + 1, order, placed, ready =>
    match ready.min? with
    | none => order ++ stored.filter (!placed.contains ·)
    | some key =>
      let pick := key % B
      let placed := placed.insert pick
      pinnedPlaceFast deg deps users D B stored fuel (order.push pick) placed
        (pinnedWake deg deps D B placed (users.getD pick #[]) (ready.erase key))

/-- Strictly increasing. -/
def incList : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a < b) && incList (b :: l)

/-- `pinnedOrder` with a priority set of ready terms (module doc). -/
def pinnedOrderFast (dag : Dag) (deg : Array Nat) (stored : Array Nat) : Array Nat :=
  if incList stored.toList then
    let deps := pinnedDeps dag stored
    let D := stored.foldl (fun m t => max m deg[t]!) 0
    let B := stored.foldl (fun m t => max m (t + 1)) 0
    let ready := pinnedWake deg deps D B {} stored {}
    pinnedPlaceFast deg deps (pinnedUsers deps stored) D B stored stored.size #[] {} ready
  else pinnedOrder dag deg stored

/-! ## Keys -/

theorem lex_lt {x y t a B : Nat} (ht : t < B) (ha : a < B) :
    x * B + t < y * B + a ↔ x < y ∨ (x = y ∧ t < a) := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · exact Or.inl hxy
    · subst hxy; exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h1 : (y + 1) * B ≤ x * B := Nat.mul_le_mul_right B hxy
      rw [Nat.succ_mul] at h1
      omega
  · rintro (h | ⟨rfl, h⟩)
    · have h1 : (x + 1) * B ≤ y * B := Nat.mul_le_mul_right B h
      rw [Nat.succ_mul] at h1
      omega
    · omega

/-- The terms the keys are taken over: below `B`, in-degree at most `D`. -/
def KeyOK (deg : Array Nat) (D B t : Nat) : Prop := t < B ∧ deg[t]! ≤ D

theorem pinnedKey_mod {deg : Array Nat} {D B t : Nat} (h : KeyOK deg D B t) :
    pinnedKey deg D B t % B = t := by
  unfold pinnedKey
  rw [Nat.mul_comm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt h.1

theorem pinnedKey_inj {deg : Array Nat} {D B t a : Nat} (ht : KeyOK deg D B t)
    (ha : KeyOK deg D B a) (h : pinnedKey deg D B t = pinnedKey deg D B a) : t = a := by
  have := congrArg (· % B) h
  simp only [pinnedKey_mod ht, pinnedKey_mod ha] at this
  exact this

/-- The tie order of `pinnedPick` is the key order. -/
theorem better_iff_key {deg : Array Nat} {D B t a : Nat} (ht : KeyOK deg D B t)
    (ha : KeyOK deg D B a) :
    (deg[t]! > deg[a]! || (deg[t]! == deg[a]! && t < a)) = true ↔
      pinnedKey deg D B t < pinnedKey deg D B a := by
  unfold pinnedKey
  rw [lex_lt ht.1 ha.1]
  have h1 := ht.2
  have h2 := ha.2
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  omega

/-! ## The pick -/

/-- The fold of `pinnedPick` (any step function `f` with its two equations):
the least key of the list, or `none`. -/
theorem pinnedPick_fold {deg : Array Nat} {D B : Nat} (f : Option Nat → Nat → Option Nat)
    (hf1 : ∀ t, f none t = some t)
    (hf2 : ∀ a t, f (some a) t =
      if (deg[t]! > deg[a]! || (deg[t]! == deg[a]! && t < a)) = true then some t else some a) :
    ∀ (L : List Nat) (acc : Option Nat),
      (∀ t ∈ L, KeyOK deg D B t) → (∀ a, acc = some a → KeyOK deg D B a) →
      (L.foldl f acc = none ↔ acc = none ∧ L = []) ∧
        ∀ m, L.foldl f acc = some m → (m ∈ L ∨ acc = some m) ∧ KeyOK deg D B m ∧
          (∀ x ∈ L, pinnedKey deg D B m ≤ pinnedKey deg D B x) ∧
          (∀ a, acc = some a → pinnedKey deg D B m ≤ pinnedKey deg D B a) := by
  intro L
  induction L with
  | nil =>
    intro acc _ hacc
    simp only [List.foldl_nil]
    refine ⟨by simp, fun m hm => ⟨Or.inr hm, hacc m hm, fun x hx => by simp at hx, fun a ha => ?_⟩⟩
    rw [hm] at ha; cases ha; exact Nat.le_refl _
  | cons t ts ih =>
    intro acc hL hacc
    simp only [List.foldl_cons]
    have ht := hL t (List.mem_cons_self)
    have hts : ∀ x ∈ ts, KeyOK deg D B x := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    cases acc with
    | none =>
      rw [hf1]
      obtain ⟨hnone, hsome⟩ := ih (some t) hts (fun a ha => by cases ha; exact ht)
      refine ⟨⟨fun h => absurd (hnone.mp h).1 (by simp), fun h => by simp at h⟩, fun m hm => ?_⟩
      obtain ⟨hmem, hok, hle, hlea⟩ := hsome m hm
      refine ⟨?_, hok, fun x hx => ?_, fun a ha => by cases ha⟩
      · rcases hmem with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · cases h; exact Or.inl List.mem_cons_self
      · rcases List.mem_cons.mp hx with h | h
        · subst h; exact hlea x rfl
        · exact hle x h
    | some a =>
      rw [hf2]
      have ha := hacc a rfl
      by_cases hb : (deg[t]! > deg[a]! || (deg[t]! == deg[a]! && t < a)) = true
      · simp only [hb, ite_true]
        have hlt := (better_iff_key ht ha).mp hb
        obtain ⟨hnone, hsome⟩ := ih (some t) hts (fun a ha => by cases ha; exact ht)
        refine ⟨⟨fun h => absurd (hnone.mp h).1 (by simp), fun h => by simp at h⟩, fun m hm => ?_⟩
        obtain ⟨hmem, hok, hle, hlea⟩ := hsome m hm
        have hmt := hlea t rfl
        refine ⟨?_, hok, fun x hx => ?_, fun a' ha' => ?_⟩
        · rcases hmem with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · cases h; exact Or.inl List.mem_cons_self
        · rcases List.mem_cons.mp hx with h | h
          · subst h; exact hmt
          · exact hle x h
        · cases ha'; omega
      · simp only [hb, Bool.false_eq_true, ite_false]
        have hge : pinnedKey deg D B a ≤ pinnedKey deg D B t := by
          have := mt (better_iff_key ht ha).mpr hb
          omega
        obtain ⟨hnone, hsome⟩ := ih (some a) hts (fun a' ha' => by cases ha'; exact ha)
        refine ⟨⟨fun h => absurd (hnone.mp h).1 (by simp), fun h => by simp at h⟩, fun m hm => ?_⟩
        obtain ⟨hmem, hok, hle, hlea⟩ := hsome m hm
        have hma := hlea a rfl
        refine ⟨?_, hok, fun x hx => ?_, hlea⟩
        · rcases hmem with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
        · rcases List.mem_cons.mp hx with h | h
          · subst h; omega
          · exact hle x h

/-- `pinnedPick_spec` for a generic step function. -/
theorem pinnedPick_spec_aux {deg : Array Nat} {D B : Nat} {deps : Std.HashMap Nat (Array Nat)}
    {placed : Std.HashSet Nat} {remaining : Array Nat}
    (hok : ∀ t ∈ remaining.toList, KeyOK deg D B t) (f : Option Nat → Nat → Option Nat)
    (hf1 : ∀ t, f none t = some t)
    (hf2 : ∀ a t, f (some a) t =
      if (deg[t]! > deg[a]! || (deg[t]! == deg[a]! && t < a)) = true then some t else some a) :
    ((remaining.toList.filter fun t => (deps.getD t #[]).all placed.contains).foldl f none = none ↔
        ∀ t ∈ remaining.toList, pinnedReady deps placed t = false) ∧
      ∀ m, (remaining.toList.filter fun t => (deps.getD t #[]).all placed.contains).foldl f none
          = some m →
        m ∈ remaining.toList ∧ pinnedReady deps placed m = true ∧
          ∀ x ∈ remaining.toList, pinnedReady deps placed x = true →
            pinnedKey deg D B m ≤ pinnedKey deg D B x := by
  have hL : ∀ t ∈ remaining.toList.filter (fun t => (deps.getD t #[]).all placed.contains),
      KeyOK deg D B t := fun t ht => hok t (List.mem_filter.mp ht).1
  obtain ⟨hnone, hsome⟩ := pinnedPick_fold (deg := deg) (D := D) (B := B) f hf1 hf2 _ none hL
    (fun a ha => by cases ha)
  refine ⟨?_, fun m hm => ?_⟩
  · rw [hnone]
    simp only [true_and, List.filter_eq_nil_iff, pinnedReady]
    constructor
    · intro h t ht; simpa using h t ht
    · intro h t ht; simpa using h t ht
  · obtain ⟨hmem, _, hle, _⟩ := hsome m hm
    rcases hmem with hmem | hmem
    · obtain ⟨h1, h2⟩ := List.mem_filter.mp hmem
      exact ⟨h1, h2, fun x hx hr => hle x (List.mem_filter.mpr ⟨hx, hr⟩)⟩
    · cases hmem

/-- The pick of the specification is the term of least key among the ready
remaining terms. -/
theorem pinnedPick_spec {deg : Array Nat} {D B : Nat} {deps : Std.HashMap Nat (Array Nat)}
    {placed : Std.HashSet Nat} {remaining : Array Nat}
    (hok : ∀ t ∈ remaining.toList, KeyOK deg D B t) :
    (pinnedPick deg deps placed remaining = none ↔
        ∀ t ∈ remaining.toList, pinnedReady deps placed t = false) ∧
      ∀ m, pinnedPick deg deps placed remaining = some m →
        m ∈ remaining.toList ∧ pinnedReady deps placed m = true ∧
          ∀ x ∈ remaining.toList, pinnedReady deps placed x = true →
            pinnedKey deg D B m ≤ pinnedKey deg D B x := by
  unfold pinnedPick
  rw [← Array.foldl_toList, Array.toList_filter]
  refine pinnedPick_spec_aux hok _ ?_ ?_
  · intro t; rfl
  · intro a t; rfl

/-! ## Users, wake-ups, bounds -/

theorem users_inner (u : Nat) :
    ∀ (ds : List Nat) (us : Std.HashMap Nat (Array Nat)) (x d : Nat),
      x ∈ ((ds.foldl (fun us d => us.alter d fun o => some ((o.getD #[]).push u)) us).getD
          d #[]).toList ↔
        x ∈ (us.getD d #[]).toList ∨ (x = u ∧ d ∈ ds) := by
  intro ds
  induction ds with
  | nil => intro us x d; simp
  | cons d0 ds ih =>
    intro us x d
    simp only [List.foldl_cons]
    rw [ih]
    rw [Std.HashMap.getD_alter]
    by_cases hd : d0 = d
    · subst hd
      have hp : ∀ a : Array Nat, x ∈ (a.push u).toList ↔ x ∈ a.toList ∨ x = u := by
        intro a; simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      simp only [beq_self_eq_true, ite_true, Option.getD_some, hp,
        ← Std.HashMap.getD_eq_getD_getElem?, List.mem_cons_self, and_true]
      constructor
      · rintro ((h | h) | ⟨h, _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
    · have h1 : (d0 == d) = false := by simpa using hd
      simp only [h1, Bool.false_eq_true, ite_false, List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inr h2⟩
      · rintro (h | ⟨h1, h2 | h2⟩)
        · exact Or.inl h
        · exact absurd h2.symm hd
        · exact Or.inr ⟨h1, h2⟩

theorem users_outer (deps : Std.HashMap Nat (Array Nat)) :
    ∀ (l : List Nat) (us : Std.HashMap Nat (Array Nat)) (x d : Nat),
      x ∈ ((l.foldl (fun us u => (deps.getD u #[]).foldl
          (fun us d => us.alter d fun o => some ((o.getD #[]).push u)) us) us).getD d #[]).toList ↔
        x ∈ (us.getD d #[]).toList ∨ (x ∈ l ∧ d ∈ (deps.getD x #[]).toList) := by
  intro l
  induction l with
  | nil => intro us x d; simp
  | cons u l ih =>
    intro us x d
    simp only [List.foldl_cons]
    rw [ih, ← Array.foldl_toList, users_inner]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_self, h⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inl (Or.inr ⟨rfl, h2⟩)
        · exact Or.inr ⟨h1, h2⟩

theorem pinnedUsers_mem (deps : Std.HashMap Nat (Array Nat)) (stored : Array Nat) (x d : Nat) :
    x ∈ ((pinnedUsers deps stored).getD d #[]).toList ↔
      x ∈ stored.toList ∧ d ∈ (deps.getD x #[]).toList := by
  unfold pinnedUsers
  rw [← Array.foldl_toList, users_outer]
  simp

theorem wake_mem (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) (D B : Nat)
    (placed : Std.HashSet Nat) :
    ∀ (us : List Nat) (ready : Std.TreeSet Nat) (key : Nat),
      key ∈ us.foldl (fun r u =>
          if (!placed.contains u && pinnedReady deps placed u) = true then
            r.insert (pinnedKey deg D B u)
          else r) ready ↔
        key ∈ ready ∨ ∃ u ∈ us, placed.contains u = false ∧ pinnedReady deps placed u = true ∧
          key = pinnedKey deg D B u := by
  intro us
  induction us with
  | nil => intro ready key; simp
  | cons u us ih =>
    intro ready key
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      rw [Std.TreeSet.mem_insert, Nat.compare_eq_eq]
      constructor
      · rintro ((h | h) | ⟨v, hv, h⟩)
        · exact Or.inr ⟨u, List.mem_cons_self, hc.1, hc.2, h.symm⟩
        · exact Or.inl h
        · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, h⟩
      · rintro (h | ⟨v, hv, h⟩)
        · exact Or.inl (Or.inr h)
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inl (Or.inl h.2.2.symm)
          · exact Or.inr ⟨v, hv, h⟩
    · rename_i hc
      constructor
      · rintro (h | ⟨v, hv, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, h⟩
      · rintro (h | ⟨v, hv, h⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact absurd (by simp [h.1, h.2.1]) hc
          · exact Or.inr ⟨v, hv, h⟩

theorem pinnedWake_mem (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) (D B : Nat)
    (placed : Std.HashSet Nat) (us : Array Nat) (ready : Std.TreeSet Nat) (key : Nat) :
    key ∈ pinnedWake deg deps D B placed us ready ↔
      key ∈ ready ∨ ∃ u ∈ us.toList, placed.contains u = false ∧
        pinnedReady deps placed u = true ∧ key = pinnedKey deg D B u := by
  unfold pinnedWake
  rw [← Array.foldl_toList]
  exact wake_mem deg deps D B placed us.toList ready key

theorem foldl_max_ge (f : Nat → Nat) :
    ∀ (l : List Nat) (init : Nat),
      init ≤ l.foldl (fun m t => max m (f t)) init ∧
        ∀ t ∈ l, f t ≤ l.foldl (fun m t => max m (f t)) init
  | [], init => ⟨Nat.le_refl _, fun t ht => by simp at ht⟩
  | a :: l, init => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (max init (f a))
    simp only [List.foldl_cons]
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 t ht

theorem incList_lt : ∀ (a : Nat) (l : List Nat), incList (a :: l) = true → ∀ x ∈ l, a < x
  | a, [], _, x, hx => by simp at hx
  | a, b :: l, h, x, hx => by
    simp only [incList, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (incList_lt b l h.2 x hx)

theorem incList_nodup : ∀ (l : List Nat), incList l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => by simp
  | a :: b :: l, h => by
    have hlt := incList_lt a (b :: l) h
    have h2 : incList (b :: l) = true := by
      simp only [incList, Bool.and_eq_true] at h
      exact h.2
    exact List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl a (hlt a hm), incList_nodup (b :: l) h2⟩

theorem toList_erase' (xs : Array Nat) (a : Nat) : (xs.erase a).toList = xs.toList.erase a := by
  rcases xs with ⟨xs⟩
  simp

/-! ## The simulation -/

/-- The fast state represents the specification's: the remaining terms are the
unplaced stored terms (in order), and the ready set holds the keys of the
ready remaining terms. -/
def SimInv (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) (D B : Nat)
    (stored remaining : Array Nat) (placed : Std.HashSet Nat) (ready : Std.TreeSet Nat) : Prop :=
  remaining.toList = stored.toList.filter (fun t => !placed.contains t) ∧
    ∀ key, key ∈ ready ↔ ∃ t ∈ remaining.toList, pinnedReady deps placed t = true ∧
      key = pinnedKey deg D B t

theorem pinnedReady_insert {deps : Std.HashMap Nat (Array Nat)} {placed : Std.HashSet Nat}
    {t m : Nat} (h : pinnedReady deps placed t = true) :
    pinnedReady deps (placed.insert m) t = true := by
  unfold pinnedReady at *
  rw [Array.all_eq_true] at *
  intro i hi
  rw [Std.HashSet.contains_insert, h i hi, Bool.or_true]

theorem pinnedPlace_eq_fast (deg : Array Nat) (deps : Std.HashMap Nat (Array Nat)) (D B : Nat)
    (stored : Array Nat) (hnd : stored.toList.Nodup)
    (hok : ∀ t ∈ stored.toList, KeyOK deg D B t) :
    ∀ (fuel : Nat) (order remaining : Array Nat) (placed : Std.HashSet Nat)
      (ready : Std.TreeSet Nat),
      SimInv deg deps D B stored remaining placed ready →
      pinnedPlace deg deps fuel order remaining placed =
        pinnedPlaceFast deg deps (pinnedUsers deps stored) D B stored fuel order placed ready := by
  intro fuel
  induction fuel with
  | zero =>
    intro order remaining placed ready ⟨hrem, _⟩
    simp only [pinnedPlace, pinnedPlaceFast]
    congr 1
    apply Array.toList_inj.mp
    rw [hrem, Array.toList_filter]
  | succ fuel ih =>
    intro order remaining placed ready ⟨hrem, hready⟩
    have hokr : ∀ t ∈ remaining.toList, KeyOK deg D B t := by
      intro t ht
      rw [hrem] at ht
      exact hok t (List.mem_filter.mp ht).1
    obtain ⟨hpnone, hpsome⟩ := pinnedPick_spec (deps := deps) (placed := placed) hokr
    simp only [pinnedPlace, pinnedPlaceFast]
    cases hpick : pinnedPick deg deps placed remaining with
    | none =>
      have hmin : ready.min? = none := by
        rw [Std.TreeSet.min?_eq_none_iff, Std.TreeSet.isEmpty_iff_forall_not_mem]
        intro key hkey
        obtain ⟨t, ht, hr, _⟩ := (hready key).mp hkey
        rw [(hpnone.mp hpick) t ht] at hr
        cases hr
      rw [hmin]
      simp only
      congr 1
      apply Array.toList_inj.mp
      rw [hrem, Array.toList_filter]
    | some m =>
      obtain ⟨hmrem, hmready, hmle⟩ := hpsome m hpick
      have hmok := hokr m hmrem
      have hmin : ready.min? = some (pinnedKey deg D B m) := by
        rw [Std.TreeSet.min?_eq_some_iff_mem_and_forall]
        refine ⟨(hready _).mpr ⟨m, hmrem, hmready, rfl⟩, fun k hk => ?_⟩
        obtain ⟨t, ht, hr, rfl⟩ := (hready k).mp hk
        rw [Nat.isLE_compare]
        exact hmle t ht hr
      rw [hmin]
      simp only [pinnedKey_mod hmok]
      apply ih
      -- the invariant after placing `m`
      have hndr : remaining.toList.Nodup := by
        rw [hrem]; exact hnd.sublist List.filter_sublist
      refine ⟨?_, fun key => ?_⟩
      · rw [toList_erase', hndr.erase_eq_filter, hrem, List.filter_filter]
        apply List.filter_congr
        intro t _
        rw [Std.HashSet.contains_insert]
        by_cases htm : t = m
        · subst htm; simp
        · have h1 : (m == t) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => htm h.symm
          have h2 : (t != m) = true := by simpa using htm
          simp [h1, h2]
      · rw [pinnedWake_mem, Std.TreeSet.mem_erase, ne_eq, Nat.compare_eq_eq, hready, toList_erase']
        simp only [hndr.mem_erase_iff]
        constructor
        · rintro (⟨hne, t, ht, hr, rfl⟩ | ⟨u, hu, hpl, hur, rfl⟩)
          · have htm : t ≠ m := fun h => hne (by rw [h])
            exact ⟨t, ⟨htm, ht⟩, pinnedReady_insert hr, rfl⟩
          · obtain ⟨hus, _⟩ := (pinnedUsers_mem deps stored u m).mp hu
            rw [Std.HashSet.contains_insert] at hpl
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hpl
            refine ⟨u, ⟨fun h => hpl.1 h.symm, ?_⟩, hur, rfl⟩
            rw [hrem]
            exact List.mem_filter.mpr ⟨hus, by simp [hpl.2]⟩
        · rintro ⟨t, ⟨htm, ht⟩, hr, rfl⟩
          by_cases hr0 : pinnedReady deps placed t = true
          · refine Or.inl ⟨fun h => htm (pinnedKey_inj (hokr t ht) hmok h.symm), t, ht, hr0, rfl⟩
          · refine Or.inr ⟨t, ?_, ?_, hr, rfl⟩
            · -- `t` waited for `m`
              rw [pinnedUsers_mem]
              have htst : t ∈ stored.toList := by
                rw [hrem] at ht; exact (List.mem_filter.mp ht).1
              refine ⟨htst, ?_⟩
              unfold pinnedReady at hr hr0
              rw [Array.all_eq_true] at hr
              have hr0f : (deps.getD t #[]).all placed.contains = false := by simpa using hr0
              rw [Array.all_eq_false] at hr0f
              obtain ⟨i, hi, hni⟩ := hr0f
              have := hr i hi
              rw [Std.HashSet.contains_insert] at this
              simp only [Bool.or_eq_true, beq_iff_eq] at this
              rcases this with h | h
              · rw [h]; exact Array.getElem_mem_toList hi
              · exact absurd h hni
            · rw [Std.HashSet.contains_insert]
              have hnp : placed.contains t = false := by
                rw [hrem] at ht
                simpa using (List.mem_filter.mp ht).2
              have h1 : (m == t) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => htm h.symm
              rw [h1, hnp, Bool.or_false]

theorem pinnedOrder_eq_fast_apply (dag : Dag) (deg : Array Nat) (stored : Array Nat) :
    pinnedOrder dag deg stored = pinnedOrderFast dag deg stored := by
  unfold pinnedOrderFast
  split
  · rename_i hinc
    unfold pinnedOrder
    have hnd := incList_nodup _ hinc
    have hok : ∀ t ∈ stored.toList,
        KeyOK deg (stored.foldl (fun m t => max m deg[t]!) 0)
          (stored.foldl (fun m t => max m (t + 1)) 0) t := by
      intro t ht
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      exact ⟨(foldl_max_ge (· + 1) _ 0).2 t ht, (foldl_max_ge (fun t => deg[t]!) _ 0).2 t ht⟩
    apply pinnedPlace_eq_fast deg _ _ _ stored hnd hok
    refine ⟨(List.filter_eq_self.mpr fun _ _ => by simp).symm, fun key => ?_⟩
    rw [pinnedWake_mem]
    simp only [Std.TreeSet.not_mem_emptyc, false_or, Std.HashSet.contains_empty, true_and]
  · rfl

@[csimp] theorem pinnedOrder_eq_fast : @pinnedOrder = @pinnedOrderFast := by
  funext dag deg stored
  exact pinnedOrder_eq_fast_apply dag deg stored

end Ix.Sharing.Exact

end
