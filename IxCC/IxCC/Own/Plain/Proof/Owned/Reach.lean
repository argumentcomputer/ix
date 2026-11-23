import IxCC.Own.Rc.Reuse
import IxCC.Own.Rc.Proof.Transfer
import IxCC.Own.Plain.Proof.Environment

/-! # Reachability from external roots (caller-backed borrows)

A caller-backed borrowed parameter (`pbrw`) is backed by the caller's external ownership count
(`external : Nat → Nat`): either it is an immediate value, an external root itself
(`0 < external l`), or reachable by field projections from an external root (`ReachableFrom`).

`ReachablePreserved before after external` says the heap does not shrink and every live cell
reachable from `external` keeps its exact body and mode (`live rc' m b`) in `after`.
Unlike plain `ExternalPreserved` (which only talks about root readback), `ReachablePreserved`
preserves both `ReachableFrom` and `Proof.Den` of *every* projected descendant across `inc`,
`alloc`, `dec` (`dropAll`), in-place `reuseCell`, and non-tail calls, while also implying
`ExternalPreserved`. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc

/-- `v` is backed by `external` in heap `H`: immediate, an external root, or reachable by
projecting fields from an external root. -/
inductive ReachableFrom (H : Heap) (external : Nat → Nat) : RVal → Prop where
  | imm {v : RVal} (h : ImmVal v) : ReachableFrom H external v
  | root {l : Nat} (h : 0 < external l) : ReachableFrom H external (.loc l)
  | field {l rc : Nat} {m : OMode} {b : Body} {u : RVal}
      (hr : ReachableFrom H external (.loc l))
      (hc : H.cell? l = some (.live rc m b))
      (hm : u ∈ b.fields) : ReachableFrom H external u

/-- Every live cell reachable from `external` in `before` stays live with the same mode and body
in `after`, and the heap does not shrink. -/
def ReachablePreserved (before after : Heap) (external : Nat → Nat) : Prop :=
  before.size ≤ after.size ∧
  ∀ l rc m b, ReachableFrom before external (.loc l) →
    before.cell? l = some (.live rc m b) →
    ∃ rc', after.cell? l = some (.live rc' m b)

namespace ReachableFrom

theorem of_externalRoot {H : Heap} {external : Nat → Nat} {v : RVal}
    (h : ExternalRoot external v) : ReachableFrom H external v := by
  cases v with
  | loc l => exact .root h
  | lit _ => exact .imm (fun _ h => by cases h)
  | ctor0 _ => exact .imm (fun _ h => by cases h)
  | erased => exact .imm (fun _ h => by cases h)

theorem mono_ext {H : Heap} {ext₁ ext₂ : Nat → Nat} (hle : ∀ l, ext₁ l ≤ ext₂ l)
    {v : RVal} (hr : ReachableFrom H ext₁ v) : ReachableFrom H ext₂ v := by
  induction hr with
  | imm h => exact .imm h
  | root h => exact .root (Nat.lt_of_lt_of_le h (hle _))
  | field _ hc hm ih => exact .field ih hc hm

theorem canDup {H : Heap} {external : Nat → Nat} {owned : List RVal}
    (hb : Balance H external owned) {v : RVal} (hr : ReachableFrom H external v) : CanDup H v := by
  cases hr with
  | imm himm =>
    cases v with
    | loc l => exact absurd rfl (himm l)
    | lit _ | ctor0 _ | erased => trivial
  | @root l hpos =>
    have h := hb l
    change 0 < dynCount H l
    omega
  | field _ hc hm =>
    cases v with
    | loc k =>
      have h := hb k
      have he := refsIn_fields_le hc k
      have hp := refsIn_pos hm
      change 0 < dynCount H k
      omega
    | lit _ | ctor0 _ | erased => trivial

theorem transport {H₀ H₁ : Heap} {external : Nat → Nat}
    (hp : ReachablePreserved H₀ H₁ external) {v : RVal}
    (hr : ReachableFrom H₀ external v) : ReachableFrom H₁ external v := by
  induction hr with
  | imm h => exact .imm h
  | root h => exact .root h
  | field hpar hc hm ih =>
    obtain ⟨rc', hc'⟩ := hp.2 _ _ _ _ hpar hc
    exact .field ih hc' hm

theorem not_of_zero {H : Heap} {external : Nat → Nat} {l : Nat}
    (hext : external l = 0) (hedge : edgeCount H l = 0) :
    ¬ ReachableFrom H external (.loc l) := by
  intro hr
  cases hr with
  | imm himm => exact himm l rfl
  | root hpos => omega
  | field _ hc hm => exact fields_avoid hedge hc hm

theorem asCtor_field {H : Heap} {external : Nat → Nat} {K : Lam.Known}
    {parent v : RVal} {key : Key.CtorKey} {fields : List RVal}
    (hr : ReachableFrom H external parent) (hc : parent.asCtor K H = some (key, fields))
    (hm : v ∈ fields) : ReachableFrom H external v := by
  cases parent with
  | loc l =>
    cases hl : H.cell? l with
    | none => simp [RVal.asCtor, hl] at hc
    | some cell =>
      cases cell with
      | dead => simp [RVal.asCtor, hl] at hc
      | live rc m b =>
        have he : b.ctor.key = key ∧ b.fields = fields := by simpa [RVal.asCtor, hl] using hc
        rw [← he.2] at hm
        exact .field hr hl hm
  | lit lit =>
    cases lit with
    | str _ => simp [RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have he : v = .lit (.nat n) := by simpa using hm
        subst he
        exact .imm (fun _ h => by cases h)
  | ctor0 c =>
    have he : c.key = key ∧ [] = fields := by simpa [RVal.asCtor] using hc
    rw [← he.2] at hm
    simp at hm
  | erased => simp [RVal.asCtor] at hc

end ReachableFrom

namespace ReachablePreserved

theorem refl (H : Heap) (external : Nat → Nat) : ReachablePreserved H H external :=
  ⟨Nat.le_refl _, fun _ rc _ _ _ hc => ⟨rc, hc⟩⟩

theorem trans {H₀ H₁ H₂ : Heap} {external : Nat → Nat}
    (h₁ : ReachablePreserved H₀ H₁ external) (h₂ : ReachablePreserved H₁ H₂ external) :
    ReachablePreserved H₀ H₂ external :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun l rc m b hr hc => by
    obtain ⟨rc₁, hc₁⟩ := h₁.2 l rc m b hr hc
    exact h₂.2 l rc₁ m b (hr.transport h₁) hc₁⟩

theorem mono_ext {H₀ H₁ : Heap} {ext₁ ext₂ : Nat → Nat} (hle : ∀ l, ext₁ l ≤ ext₂ l)
    (hp : ReachablePreserved H₀ H₁ ext₂) : ReachablePreserved H₀ H₁ ext₁ :=
  ⟨hp.1, fun l rc m b hr hc => hp.2 l rc m b (hr.mono_ext hle) hc⟩

private theorem toFir_preserved {H₀ H₁ : Heap} {external : Nat → Nat}
    (hp : ReachablePreserved H₀ H₁ external) :
    ∀ fuel fuel', fuel ≤ fuel' → ∀ v w,
      ReachableFrom H₀ external v → toFir H₀ fuel v = some w → toFir H₁ fuel' v = some w
  | 0, fuel', _, v, w, _, hw => by
    cases v with
    | loc _ => simp [toFir] at hw
    | lit l => cases fuel' <;> simpa [toFir] using hw
    | ctor0 c => cases fuel' <;> simpa [toFir] using hw
    | erased => cases fuel' <;> simpa [toFir] using hw
  | fuel + 1, fuel', hle, v, w, hr, hw => by
    obtain ⟨k', rfl⟩ : ∃ k', fuel' = k' + 1 := ⟨fuel' - 1, by omega⟩
    have hle' : fuel ≤ k' := by omega
    have hlist : ∀ vs ws, (∀ u, u ∈ vs → ReachableFrom H₀ external u) →
        toFirList H₀ fuel vs = some ws → toFirList H₁ k' vs = some ws := by
      intro vs
      induction vs with
      | nil => intro ws _ h; simpa [toFirList] using h
      | cons u us ih =>
        intro ws hmem h
        cases hu : toFir H₀ fuel u with
        | none => simp [toFirList, hu] at h
        | some wu =>
          cases hus : toFirList H₀ fuel us with
          | none => simp [toFirList, hu, hus] at h
          | some wus =>
            have hws : wu :: wus = ws := by simpa [toFirList, hu, hus] using h
            subst hws
            have hu' := toFir_preserved hp fuel k' hle' u wu (hmem u List.mem_cons_self) hu
            have hus' := ih wus (fun z hz => hmem z (List.mem_cons_of_mem _ hz)) hus
            simp [toFirList, hu', hus']
    cases v with
    | lit l => simpa [toFir] using hw
    | ctor0 c => simpa [toFir] using hw
    | erased => simpa [toFir] using hw
    | loc l =>
      cases hc : H₀.cell? l with
      | none => simp [toFir, hc] at hw
      | some cell =>
        cases cell with
        | dead => simp [toFir, hc] at hw
        | live rc m b =>
          obtain ⟨rc', hc'⟩ := hp.2 l rc m b hr hc
          cases hfs : toFirList H₀ fuel b.fields with
          | none => simp [toFir, hc, hfs] at hw
          | some ws =>
            have hw' : Fir.Val.ctor b.ctor ws = w := by simpa [toFir, hc, hfs] using hw
            subst hw'
            have hfs' := hlist b.fields ws (fun u hu => .field hr hc hu) hfs
            simp [toFir, hc', hfs']

/-- Any reachable value keeps its full FIR denotation. -/
theorem den {H₀ H₁ : Heap} {external : Nat → Nat} (hp : ReachablePreserved H₀ H₁ external)
    {v : RVal} {w : Fir.Val} (hr : ReachableFrom H₀ external v) (hd : Proof.Den H₀ v w) :
    Proof.Den H₁ v w :=
  toFir_preserved hp (H₀.size + 1) (H₁.size + 1) (Nat.add_le_add_right hp.1 1) v w hr hd

theorem inc {H H' : Heap} {external : Nat → Nat} {u : RVal} (hi : Rc.inc H u 1 = some H') :
    ReachablePreserved H H' external := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; exact refl H external
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.inc, changeCount, hc] at hi
    | some cell =>
      cases cell with
      | dead => simp [Rc.inc, changeCount, hc] at hi
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; exact refl H external
        | dyn =>
          by_cases hz : rc = 0
          · simp [Rc.inc, changeCount, hc, hz] at hi
          · rw [inc_dyn hc (by omega) 1] at hi
            cases hi
            have hl : l < H.size := Proof.cell?_some hc
            refine ⟨by simp [setCell_size], fun k rk mk bk _ hck => ?_⟩
            rw [setCell_cell H l _ hl k]
            by_cases he : l = k
            · subst he
              rw [hc] at hck
              obtain ⟨-, rfl, rfl⟩ := Cell.live.inj (Option.some.inj hck)
              exact ⟨rc + 1, by simp⟩
            · rw [ite_eq_right he]
              exact ⟨rk, hck⟩

theorem alloc (H : Heap) (external : Nat → Nat) (b : Body) :
    ReachablePreserved H (H.alloc .rc b).2 external := by
  refine ⟨by simp [Heap.alloc, Heap.size], fun l rc m b' _ hc => ?_⟩
  have hl : l < H.size := Proof.cell?_some hc
  have hne : l ≠ H.cells.size := Nat.ne_of_lt hl
  refine ⟨rc, ?_⟩
  simp only [Heap.alloc, Heap.cell?, Array.getElem?_push, hne, ↓reduceIte]
  exact hc

theorem releaseOne {H H' : Heap} {external : Nat → Nat} {v : RVal} {pending pending' : List RVal}
    (hb : Balance H external (v :: pending)) (hop : Rc.releaseOne H v pending = some (H', pending')) :
    ReachablePreserved H H' external := by
  cases v with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop; exact refl H external
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.releaseOne, hc] at hop
    | some cell =>
      cases cell with
      | dead => simp [Rc.releaseOne, hc] at hop
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop; exact refl H external
        | dyn =>
          cases rc with
          | zero => simp [Rc.releaseOne, hc] at hop
          | succ rc =>
            cases rc with
            | zero =>
              simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              have hl : l < H.size := Proof.cell?_some hc
              have hbal := hb l
              simp [dynCount, hc, refsIn] at hbal
              refine ⟨by simp [setCell_size], fun k rk mk bk hr hck => ?_⟩
              have hne : l ≠ k := by
                intro he; subst he
                exact ReachableFrom.not_of_zero (by omega) (by omega) hr
              rw [setCell_cell H l .dead hl k, ite_eq_right hne]
              exact ⟨rk, hck⟩
            | succ rc =>
              simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              have hl : l < H.size := Proof.cell?_some hc
              refine ⟨by simp [setCell_size], fun k rk mk bk _ hck => ?_⟩
              rw [setCell_cell H l _ hl k]
              by_cases he : l = k
              · subst he
                rw [hc] at hck
                obtain ⟨-, rfl, rfl⟩ := Cell.live.inj (Option.some.inj hck)
                exact ⟨rc + 1, by simp⟩
              · rw [ite_eq_right he]
                exact ⟨rk, hck⟩

theorem dropAll (H : Heap) (pending : List RVal) {external : Nat → Nat} {H' : Heap}
    (hb : Balance H external pending) (hd : Rc.dropAll H pending = some H') :
    ReachablePreserved H H' external := by
  match pending with
  | [] =>
    simp only [Rc.dropAll, Option.some.injEq] at hd
    subst hd; exact refl H external
  | v :: ps =>
    obtain ⟨H₁, ps₁, hstep, hb₁⟩ := releaseOne_balance hb
    rw [Rc.dropAll, hstep] at hd
    exact (releaseOne hb hstep).trans (dropAll H₁ ps₁ hb₁ hd)
termination_by (mass H, pending.length)
decreasing_by
  have hdec := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hdec with hdec | ⟨he, hdec⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

theorem reuseCell {H H' : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest : List RVal} {r : RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hb : Balance H external (.loc l :: rest))
    (hr : Rc.reuseCell H l b' = some (r, H')) : ReachablePreserved H H' external := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hr
  obtain ⟨hext, _, hedge, _, _, _, _⟩ := reuse_exclusive hc hb
  have hl : l < H.size := Proof.cell?_some hc
  refine ⟨by rw [reusedHeap_size]; omega, fun k rk mk bk hreach hck => ?_⟩
  have hk : k < H.size := Proof.cell?_some hck
  have hne : l ≠ k := by
    intro he; subst he; exact ReachableFrom.not_of_zero hext hedge hreach
  rw [reusedHeap_cell hl b' k, ite_eq_right (Nat.ne_of_lt hk), ite_eq_right hne]
  exact ⟨rk, hck⟩

theorem of_holdRoots {H₀ H₁ : Heap} {external : Nat → Nat} {held : List RVal}
    (hp : ReachablePreserved H₀ H₁ (holdRoots external held)) :
    ReachablePreserved H₀ H₁ external :=
  hp.mono_ext (fun l => by simp [holdRoots])

/-- `reuseCell` preserves all live cells reachable from external owners, old fields, and kept tokens,
with no `HeapOk` assumption. -/
theorem reuseCell_hold {H H' : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest : List RVal} {r : RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hb : Balance H external (.loc l :: rest))
    (hr : Rc.reuseCell H l b' = some (r, H')) :
    ReachablePreserved H H' (holdRoots external (b.fields ++ rest)) := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hr
  obtain ⟨hext, hrest, hedge, hbf, _, _, _⟩ := reuse_exclusive hc hb
  have hl : l < H.size := Proof.cell?_some hc
  refine ⟨by rw [reusedHeap_size]; omega, fun k rk mk bk hreach hck => ?_⟩
  have hk : k < H.size := Proof.cell?_some hck
  have hzero : holdRoots external (b.fields ++ rest) l = 0 := by
    simp only [holdRoots, refsIn_append]; omega
  have hne : l ≠ k := by
    intro he; subst he; exact ReachableFrom.not_of_zero hzero hedge hreach
  rw [reusedHeap_cell hl b' k, ite_eq_right (Nat.ne_of_lt hk), ite_eq_right hne]
  exact ⟨rk, hck⟩

/-- The fresh cell written by `reuseCell` denotes `.ctor b'.ctor ws` without requiring `HeapOk H`. -/
theorem reuseCell_den {H H' : Heap} {external : Nat → Nat} {l : Nat} {b b' : Body}
    {rest : List RVal} {r : RVal} {ws : List Fir.Val}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hb : Balance H external (.loc l :: rest))
    (hr : Rc.reuseCell H l b' = some (r, H'))
    (hds : Sem.Forall2 (Proof.Den H) b'.fields ws)
    (hreach : ∀ u, u ∈ b'.fields → ReachableFrom H (holdRoots external (b.fields ++ rest)) u) :
    Proof.Den H' r (.ctor b'.ctor ws) := by
  obtain ⟨rfl, rfl⟩ := reuseCell_of_some hc hr
  have hp := reuseCell_hold hc hb hr
  have hsz : (reusedHeap H l b').size = H.size + 1 := reusedHeap_size H l b'
  have hnew : (reusedHeap H l b').cell? H.size = some (.live 1 .dyn b') := reusedHeap_new H l b'
  have hlist : ∀ (us : List RVal) (ws' : List Fir.Val),
      Sem.Forall2 (Proof.Den H) us ws' →
      (∀ u, u ∈ us → ReachableFrom H (holdRoots external (b.fields ++ rest)) u) →
      toFirList (reusedHeap H l b') (H.size + 1) us = some ws' := by
    intro us
    induction us with
    | nil =>
      intro ws' h _; cases h; simp [toFirList]
    | cons u us ih =>
      intro ws' h hru
      cases h with
      | cons hu hus =>
        have hu' := toFir_preserved hp (H.size + 1) (H.size + 1) (Nat.le_refl _) u _
          (hru u List.mem_cons_self) hu
        have hus' := ih _ hus (fun z hz => hru z (List.mem_cons_of_mem _ hz))
        simp [toFirList, hu', hus']
  show toFir (reusedHeap H l b') ((reusedHeap H l b').size + 1) (.loc H.size) = some (.ctor b'.ctor ws)
  rw [hsz]
  simp only [toFir, hnew, hlist b'.fields ws hds hreach, Option.map_some]

/-- `asCtor` of a reachable value is preserved verbatim. -/
theorem asCtor {H₀ H₁ : Heap} {external : Nat → Nat} {K : Lam.Known}
    (hp : ReachablePreserved H₀ H₁ external) {v : RVal} {key : Key.CtorKey} {fields : List RVal}
    (hr : ReachableFrom H₀ external v) (hc : v.asCtor K H₀ = some (key, fields)) :
    v.asCtor K H₁ = some (key, fields) := by
  cases v with
  | lit lit => cases lit with | str _ => exact hc | nat n => cases n <;> exact hc
  | ctor0 _ | erased => exact hc
  | loc l =>
    cases hl : H₀.cell? l with
    | none => simp [RVal.asCtor, hl] at hc
    | some cell =>
      cases cell with
      | dead => simp [RVal.asCtor, hl] at hc
      | live rc m b =>
        obtain ⟨rc', hl'⟩ := hp.2 l rc m b hr hl
        simp only [RVal.asCtor, hl, hl'] at hc ⊢
        exact hc

end ReachablePreserved

/-! ## Edge counts under RC operations -/

theorem inc_edgeCount {H H' : Heap} {u : RVal} (hi : Rc.inc H u 1 = some H') (k : Nat) :
    edgeCount H' k = edgeCount H k := by
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; rfl
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.inc, changeCount, hc] at hi
    | some cell =>
      cases cell with
      | dead => simp [Rc.inc, changeCount, hc] at hi
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; rfl
        | dyn =>
          by_cases hz : rc = 0
          · simp [Rc.inc, changeCount, hc, hz] at hi
          · rw [inc_dyn hc (by omega) 1] at hi
            cases hi
            exact edgeCount_set_count (rc' := rc + 1) hc k

theorem releaseOne_edgeCount_le {H H' : Heap} {v : RVal} {pending pending' : List RVal}
    (hop : Rc.releaseOne H v pending = some (H', pending')) (k : Nat) :
    edgeCount H' k ≤ edgeCount H k := by
  cases v with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop; exact Nat.le_refl _
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.releaseOne, hc] at hop
    | some cell =>
      cases cell with
      | dead => simp [Rc.releaseOne, hc] at hop
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop; exact Nat.le_refl _
        | dyn =>
          cases rc with
          | zero => simp [Rc.releaseOne, hc] at hop
          | succ rc =>
            cases rc with
            | zero =>
              simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              have he := edgeCount_free hc k
              omega
            | succ rc =>
              simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              rw [edgeCount_set_count (rc' := rc + 1) hc k]
              exact Nat.le_refl _

theorem dropAll_edgeCount_le (H : Heap) (pending : List RVal) {H' : Heap}
    (hd : Rc.dropAll H pending = some H') (k : Nat) :
    edgeCount H' k ≤ edgeCount H k := by
  match pending with
  | [] =>
    simp only [Rc.dropAll, Option.some.injEq] at hd
    subst hd; exact Nat.le_refl _
  | v :: ps =>
    cases hstep : Rc.releaseOne H v ps with
    | none => rw [Rc.dropAll, hstep] at hd; cases hd
    | some pair =>
      obtain ⟨H₁, ps₁⟩ := pair
      rw [Rc.dropAll, hstep] at hd
      exact Nat.le_trans (dropAll_edgeCount_le H₁ ps₁ hd k) (releaseOne_edgeCount_le hstep k)
termination_by (mass H, pending.length)
decreasing_by
  have hdec := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hdec with hdec | ⟨he, hdec⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

/-! ## Epoch-borrowed, statically unique, and private-frame predicates -/

/-- An epoch-borrowed projection's value: either immediate or backed by at least one live cell edge. -/
def BorrowVal (H : Heap) (v : RVal) : Prop :=
  match v with
  | .loc k => 0 < edgeCount H k
  | _ => True

namespace BorrowVal

theorem canDup {H : Heap} {external : Nat → Nat} {owned : List RVal}
    (hb : Balance H external owned) {v : RVal} (h : BorrowVal H v) : CanDup H v := by
  cases v with
  | loc k =>
    have hk := hb k
    change 0 < edgeCount H k at h
    change 0 < dynCount H k
    omega
  | lit _ | ctor0 _ | erased => trivial

theorem asCtor_field {H : Heap} {K : Lam.Known} {parent v : RVal} {key : Key.CtorKey}
    {fields : List RVal} (hc : parent.asCtor K H = some (key, fields)) (hm : v ∈ fields) :
    BorrowVal H v := by
  cases parent with
  | loc l =>
    cases hl : H.cell? l with
    | none => simp [RVal.asCtor, hl] at hc
    | some cell =>
      cases cell with
      | dead => simp [RVal.asCtor, hl] at hc
      | live rc m b =>
        have he : b.ctor.key = key ∧ b.fields = fields := by simpa [RVal.asCtor, hl] using hc
        rw [← he.2] at hm
        cases v with
        | loc k =>
          have hle := refsIn_fields_le hl k
          have hpos := refsIn_pos hm
          change 0 < edgeCount H k
          omega
        | lit _ | ctor0 _ | erased => trivial
  | lit lit =>
    cases lit with
    | str _ => simp [RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc; simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have he : v = .lit (.nat n) := by simpa using hm
        subst he; trivial
  | ctor0 c =>
    have he : c.key = key ∧ [] = fields := by simpa [RVal.asCtor] using hc
    rw [← he.2] at hm; simp at hm
  | erased => simp [RVal.asCtor] at hc

theorem inc {H H' : Heap} {u v : RVal} (hv : BorrowVal H v) (hi : Rc.inc H u 1 = some H') :
    BorrowVal H' v := by
  cases v with
  | loc k =>
    change 0 < edgeCount H' k
    rw [inc_edgeCount hi k]
    exact hv
  | lit _ | ctor0 _ | erased => trivial

theorem alloc {H : Heap} {v : RVal} (hv : BorrowVal H v) (b : Body) :
    BorrowVal (H.alloc .rc b).2 v := by
  cases v with
  | loc k =>
    change 0 < edgeCount (H.alloc .rc b).2 k
    rw [edgeCount_alloc]
    change 0 < edgeCount H k at hv
    omega
  | lit _ | ctor0 _ | erased => trivial

theorem reuseShell {H H' : Heap} {l : Nat} {b b' : Body} {r v : RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hzero : ∀ k, refsIn k b.fields = 0)
    (hr : Rc.reuseCell H l b' = some (r, H')) (hv : BorrowVal H v) : BorrowVal H' v := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hr
  cases v with
  | loc k =>
    change 0 < edgeCount (reusedHeap H l b') k
    rw [reusedHeap, edgeCount_alloc]
    have hfree := edgeCount_free hc k
    have hz := hzero k
    change 0 < edgeCount H k at hv
    omega
  | lit _ | ctor0 _ | erased => trivial

end BorrowVal

/-- A table-valid immediate value: safe to pass to `@unique` parameters and return from `@unique`
functions without colliding with any positive-arity constructor key. -/
def ImmUniq (ctors : List Lam.CtorInfo) (v : RVal) : Prop :=
  ImmVal v ∧
    match v with
    | .ctor0 c => ∀ info, Fir.CtorInfo.ofKey ctors c.key = some info → info.arity = 0
    | _ => True

/-- A statically unique value: either a dynamic cell with `rc = 1`, zero external owners, zero
incoming heap edges, and exactly one reference among `owned`, or a table-valid immediate. -/
def UniqVal (ctors : List Lam.CtorInfo) (H : Heap) (external : Nat → Nat)
    (owned : List RVal) (v : RVal) : Prop :=
  match v with
  | .loc l =>
    ∃ b, H.cell? l = some (.live 1 .dyn b) ∧
      external l = 0 ∧ edgeCount H l = 0 ∧ refsIn l owned = 1
  | .ctor0 c =>
    ∀ info, Fir.CtorInfo.ofKey ctors c.key = some info → info.arity = 0
  | .lit _ | .erased => True

theorem ImmUniq.toUniqVal {ctors : List Lam.CtorInfo} {H : Heap} {external : Nat → Nat}
    {owned : List RVal} {v : RVal} (h : ImmUniq ctors v) :
    UniqVal ctors H external owned v := by
  cases v with
  | loc l => exact absurd rfl (h.1 l)
  | ctor0 c => exact h.2
  | lit _ | erased => trivial

theorem UniqVal.sameRefs {ctors : List Lam.CtorInfo} {H : Heap} {external : Nat → Nat}
    {a b : List RVal} {v : RVal} (hs : ∀ k, refsIn k a = refsIn k b)
    (h : UniqVal ctors H external a v) : UniqVal ctors H external b v := by
  cases v with
  | loc l =>
    obtain ⟨body, hc, he, hed, hr⟩ := h
    exact ⟨body, hc, he, hed, by rw [← hs l]; exact hr⟩
  | ctor0 _ | lit _ | erased => exact h

/-- Locations hidden from the current call stay untouched with zero incoming heap edges. -/
def PrivPreserved (before after : Heap) (priv : Nat → Prop) : Prop :=
  ∀ l, priv l → after.cell? l = before.cell? l ∧ edgeCount after l = 0

namespace PrivPreserved

theorem refl {H : Heap} {priv : Nat → Prop} (he : ∀ l, priv l → edgeCount H l = 0) :
    PrivPreserved H H priv :=
  fun l hl => ⟨rfl, he l hl⟩

theorem trans {H₀ H₁ H₂ : Heap} {priv : Nat → Prop}
    (h₁ : PrivPreserved H₀ H₁ priv) (h₂ : PrivPreserved H₁ H₂ priv) :
    PrivPreserved H₀ H₂ priv :=
  fun l hl => ⟨(h₂ l hl).1.trans (h₁ l hl).1, (h₂ l hl).2⟩

theorem mono {H₀ H₁ : Heap} {p₁ p₂ : Nat → Prop} (hsub : ∀ l, p₁ l → p₂ l)
    (hp : PrivPreserved H₀ H₁ p₂) : PrivPreserved H₀ H₁ p₁ :=
  fun l hl => hp l (hsub l hl)

theorem inc {H H' : Heap} {priv : Nat → Prop} {u : RVal}
    (he : ∀ l, priv l → edgeCount H l = 0) (hne : ∀ l, priv l → u ≠ .loc l)
    (hi : Rc.inc H u 1 = some H') : PrivPreserved H H' priv := by
  intro l hl
  refine ⟨?_, by rw [inc_edgeCount hi l]; exact he l hl⟩
  cases u with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; rfl
  | loc k =>
    have hkl : k ≠ l := fun h => hne l hl (by rw [h])
    cases hc : H.cell? k with
    | none => simp [Rc.inc, changeCount, hc] at hi
    | some cell =>
      cases cell with
      | dead => simp [Rc.inc, changeCount, hc] at hi
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; rfl
        | dyn =>
          by_cases hz : rc = 0
          · simp [Rc.inc, changeCount, hc, hz] at hi
          · rw [inc_dyn hc (by omega) 1] at hi
            cases hi
            have hk : k < H.size := Proof.cell?_some hc
            rw [setCell_cell H k _ hk l, ite_eq_right hkl]

theorem alloc {H : Heap} {priv : Nat → Prop} {b : Body}
    (hlt : ∀ l, priv l → l < H.size) (he : ∀ l, priv l → edgeCount H l = 0)
    (hbf : ∀ l, priv l → refsIn l b.fields = 0) :
    PrivPreserved H (H.alloc .rc b).2 priv := by
  intro l hl
  have hne : l ≠ H.cells.size := Nat.ne_of_lt (hlt l hl)
  refine ⟨?_, ?_⟩
  · simp only [Heap.alloc, Heap.cell?, Array.getElem?_push, hne, ↓reduceIte]
  · rw [edgeCount_alloc, he l hl, hbf l hl]

theorem releaseOne {H H' : Heap} {priv : Nat → Prop} {v : RVal} {pending pending' : List RVal}
    (he : ∀ l, priv l → edgeCount H l = 0) (hv : ∀ l, priv l → v ≠ .loc l)
    (hop : Rc.releaseOne H v pending = some (H', pending')) :
    PrivPreserved H H' priv ∧ ∀ l, priv l → ∀ u, u ∈ pending' → u ≠ .loc l → u ∈ pending ∨ True := by
  refine ⟨fun l hl => ?_, fun _ _ _ _ _ => Or.inr trivial⟩
  have hedge' : edgeCount H' l = 0 := by
    have := releaseOne_edgeCount_le hop l
    have := he l hl; omega
  refine ⟨?_, hedge'⟩
  cases v with
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.releaseOne, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop; rfl
  | loc k =>
    have hkl : k ≠ l := fun h => hv l hl (by rw [h])
    cases hc : H.cell? k with
    | none => simp [Rc.releaseOne, hc] at hop
    | some cell =>
      cases cell with
      | dead => simp [Rc.releaseOne, hc] at hop
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop; rfl
        | dyn =>
          cases rc with
          | zero => simp [Rc.releaseOne, hc] at hop
          | succ rc =>
            cases rc with
            | zero =>
              simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              rw [setCell_cell H k .dead (Proof.cell?_some hc) l, ite_eq_right hkl]
            | succ rc =>
              simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hop
              obtain ⟨rfl, rfl⟩ := hop
              rw [setCell_cell H k _ (Proof.cell?_some hc) l, ite_eq_right hkl]

theorem dropAll (H : Heap) (pending : List RVal) {priv : Nat → Prop} {H' : Heap}
    (he : ∀ l, priv l → edgeCount H l = 0) (hp : ∀ l, priv l → refsIn l pending = 0)
    (hd : Rc.dropAll H pending = some H') : PrivPreserved H H' priv := by
  match pending with
  | [] =>
    simp only [Rc.dropAll, Option.some.injEq] at hd
    subst hd; exact refl he
  | v :: ps =>
    cases hstep : Rc.releaseOne H v ps with
    | none => rw [Rc.dropAll, hstep] at hd; cases hd
    | some pair =>
      obtain ⟨H₁, ps₁⟩ := pair
      rw [Rc.dropAll, hstep] at hd
      have hv : ∀ l, priv l → v ≠ .loc l := fun l hl h => by
        have := hp l hl; subst h; simp [refsIn] at this
      have hps : ∀ l, priv l → refsIn l ps = 0 := fun l hl => by
        have := hp l hl; simp [refsIn] at this; omega
      have hp1 := (releaseOne he hv hstep).1
      have hps1 : ∀ l, priv l → refsIn l ps₁ = 0 := fun l hl => by
        cases v with
        | lit _ | ctor0 _ | erased =>
          simp only [Rc.releaseOne, Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨_, rfl⟩ := hstep; exact hps l hl
        | loc k =>
          cases hc : H.cell? k with
          | none => simp [Rc.releaseOne, hc] at hstep
          | some cell =>
            cases cell with
            | dead => simp [Rc.releaseOne, hc] at hstep
            | live rc m b =>
              cases m with
              | static =>
                simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨_, rfl⟩ := hstep; exact hps l hl
              | dyn =>
                cases rc with
                | zero => simp [Rc.releaseOne, hc] at hstep
                | succ rc =>
                  cases rc with
                  | zero =>
                    simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hstep
                    obtain ⟨_, rfl⟩ := hstep
                    rw [refsIn_append]
                    have hbf := refsIn_fields_le hc l
                    have := he l hl; have := hps l hl; omega
                  | succ rc =>
                    simp only [Rc.releaseOne, hc, Option.some.injEq, Prod.mk.injEq] at hstep
                    obtain ⟨_, rfl⟩ := hstep; exact hps l hl
      exact hp1.trans (dropAll H₁ ps₁ (fun l hl => (hp1 l hl).2) hps1 hd)
termination_by (mass H, pending.length)
decreasing_by
  have hdec := Prod.lex_def.mp (releaseOne_decreases hstep)
  apply Prod.lex_def.mpr
  rcases hdec with hdec | ⟨he, hdec⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨he, by omega⟩

theorem reuseCell {H H' : Heap} {priv : Nat → Prop} {l0 : Nat} {b b' : Body} {r : RVal}
    (hc : H.cell? l0 = some (.live 1 .dyn b)) (hr : Rc.reuseCell H l0 b' = some (r, H'))
    (hlt : ∀ l, priv l → l < H.size) (hne : ∀ l, priv l → l0 ≠ l)
    (he : ∀ l, priv l → edgeCount H l = 0) (hbf : ∀ l, priv l → refsIn l b'.fields = 0) :
    PrivPreserved H H' priv := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hr
  have hl0 : l0 < H.size := Proof.cell?_some hc
  intro l hl
  refine ⟨?_, ?_⟩
  · rw [reusedHeap_cell hl0 b' l, ite_eq_right (Nat.ne_of_lt (hlt l hl)), ite_eq_right (hne l hl)]
  · rw [reusedHeap, edgeCount_alloc]
    have hfree := edgeCount_free hc l
    have := he l hl; have := hbf l hl; omega

end PrivPreserved

end IxCC.Own.Plain
