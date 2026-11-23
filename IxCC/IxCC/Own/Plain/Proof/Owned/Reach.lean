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

end ReachablePreserved

end IxCC.Own.Plain
