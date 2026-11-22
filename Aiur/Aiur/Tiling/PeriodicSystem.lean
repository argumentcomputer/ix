import Aiur.Tiling.PeriodicLedger

/-!
# The logical system of a sharded layout

`Sharded.system` concatenates every shard's logical templates. Circuit `f'`
of shard `k` is circuit `base k + f'` of the logical system, with the same
instance count, and its invocation ids are the shard's local ids shifted by
`idOffset k` (`system_instId`).
-/

namespace Aiur.Tiling.Periodic

variable {F : Type}

theorem getElem?_flatMap_base {α β : Type} (g : β → List α) : ∀ (ls : List β) {k f' : Nat}
    (hk : k < ls.length), f' < (g ls[k]).length →
    (ls.flatMap g)[((ls.take k).map fun b => (g b).length).sum + f']? = (g ls[k])[f']?
  | [], _, _, hk, _ => absurd hk (by simp)
  | b :: ls, 0, f', _, hf => by
      simp only [List.flatMap_cons, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.getElem_cons_zero] at hf ⊢
      rw [List.getElem?_append_left hf]
  | b :: ls, k + 1, f', hk, hf => by
      simp only [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ] at hf ⊢
      rw [show (g b).length + ((ls.take k).map fun b => (g b).length).sum + f' =
          (g b).length + (((ls.take k).map fun b => (g b).length).sum + f') by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact getElem?_flatMap_base g ls (by simpa using hk) hf

theorem sum_take_congr {β : Type} (ls : List β) (g h : β → Nat) (eq : ∀ b ∈ ls, g b = h b) (k : Nat) :
    ((ls.take k).map g).sum = ((ls.take k).map h).sum := by
  rw [List.map_congr_left (fun b hb => eq b (List.mem_of_mem_take hb))]

namespace Sharded

variable [Field F] [DecidableEq F] (S : Sharded F)

/-- Every layout has one circuit and one capacity per template. -/
def Lengths : Prop := ∀ L ∈ S.shards, L.circuits.length = L.templates.length ∧ L.caps.length = L.templates.length

variable {S}

theorem layout_eq {k : Nat} (hk : k < S.shards.length) : S.layout k = S.shards[k] := by
  simp [layout, List.getElem?_eq_getElem hk]

theorem system_template (k : Nat) (hk : k < S.shards.length) {f' : Nat}
    (hf : f' < (S.layout k).templates.length) :
    S.system.templates[S.base k + f']? = ((S.layout k).templates[f']?).map Template2.logical := by
  rw [layout_eq hk] at hf ⊢
  have := getElem?_flatMap_base (fun L : Layout F => L.templates.map Template2.logical) S.shards hk
    (f' := f') (by simpa using hf)
  simp only [List.length_map] at this
  simp only [system, base]
  rw [this]
  simp

theorem system_circuit (lens : S.Lengths) (k : Nat) (hk : k < S.shards.length) {f' : Nat}
    (hf : f' < (S.layout k).templates.length) :
    S.system.circuits[S.base k + f']? = (S.layout k).circuits[f']? := by
  rw [layout_eq hk] at hf ⊢
  have := getElem?_flatMap_base (fun L : Layout F => L.circuits) S.shards hk (f' := f')
    (by rw [(lens _ (List.getElem_mem hk)).1]; exact hf)
  simp only [system, base]
  rw [sum_take_congr S.shards (fun L => L.templates.length) (fun L => L.circuits.length)
    (fun L hL => (lens L hL).1.symm), this]

theorem system_cap (lens : S.Lengths) (k : Nat) (hk : k < S.shards.length) {f' : Nat}
    (hf : f' < (S.layout k).templates.length) :
    S.system.cap (S.base k + f') = ((S.layout k).shadow S.width).cap f' := by
  rw [layout_eq hk] at hf ⊢
  have := getElem?_flatMap_base (fun L : Layout F => L.caps) S.shards hk (f' := f')
    (by rw [(lens _ (List.getElem_mem hk)).2]; exact hf)
  simp only [System.cap, system, base, Layout.shadow, List.getD_eq_getElem?_getD]
  rw [sum_take_congr S.shards (fun L => L.templates.length) (fun L => L.caps.length)
    (fun L hL => (lens L hL).2.symm), this]

theorem system_instId (lens : S.Lengths) (k : Nat) (hk : k < S.shards.length) {f' : Nat}
    (hf : f' < (S.layout k).templates.length) (i : Nat) :
    S.system.instId (S.base k + f') i = S.idOffset k + ((S.layout k).shadow S.width).instId f' i := by
  simp only [idOffset, System.instId, List.range_add, List.map_append, List.sum_append, List.map_map,
    Nat.add_zero]
  have : ((List.range f').map (S.system.cap ∘ fun g => S.base k + g)).sum =
      ((List.range f').map ((S.layout k).shadow S.width).cap).sum := by
    congr 1
    apply List.map_congr_left
    intro g hg
    exact system_cap lens k hk (by have := List.mem_range.mp hg; omega)
  rw [this]
  omega


end Sharded

/-! ## Locating a logical circuit -/

/-- `(shard, local circuit)` of logical circuit `f`, for shard sizes `lens`. -/
def locate : List Nat → Nat → Nat × Nat
  | [], f => (0, f)
  | n :: ns, f => if f < n then (0, f) else ((locate ns (f - n)).1 + 1, (locate ns (f - n)).2)

theorem locate_cons_ge {n f : Nat} {ns : List Nat} (h : n ≤ f) :
    locate (n :: ns) f = ((locate ns (f - n)).1 + 1, (locate ns (f - n)).2) := by
  simp [locate, show ¬ f < n by omega]

theorem locate_base : ∀ (lens : List Nat) {k f' : Nat} (hk : k < lens.length), f' < lens[k] →
    locate lens ((lens.take k).sum + f') = (k, f')
  | [], _, _, hk, _ => absurd hk (by simp)
  | n :: ns, 0, f', _, hf => by simp at hf; simp [locate, hf]
  | n :: ns, k + 1, f', hk, hf => by
      simp only [List.getElem_cons_succ] at hf
      have ih := locate_base ns (by simpa using hk) hf
      rw [List.take_succ_cons, List.sum_cons, locate_cons_ge (by omega),
        show n + (ns.take k).sum + f' - n = (ns.take k).sum + f' by omega, ih]

theorem locate_spec : ∀ (lens : List Nat) {f : Nat}, f < lens.sum →
    ∃ k f', ∃ hk : k < lens.length, f' < lens[k] ∧ f = (lens.take k).sum + f'
  | [], _, hf => by simp at hf
  | n :: ns, f, hf => by
      by_cases lt : f < n
      · exact ⟨0, f, by simp, by simpa using lt, by simp⟩
      · obtain ⟨k, f', hk, hf', eq⟩ := locate_spec ns (f := f - n) (by simp at hf; omega)
        exact ⟨k + 1, f', by simpa using hk, by simpa using hf', by simp; omega⟩

namespace Sharded

variable [Field F] [DecidableEq F] {S : Sharded F}

def lens (S : Sharded F) : List Nat := S.shards.map (·.templates.length)

theorem base_eq (k : Nat) : S.base k = (S.lens.take k).sum := by
  simp [base, lens, List.map_take]

theorem length_system_templates : S.system.templates.length = S.lens.sum := by
  simp [system, lens, List.length_flatMap]

theorem lens_getElem {k : Nat} (hk : k < S.lens.length) :
    S.lens[k] = (S.layout k).templates.length := by
  have hk' : k < S.shards.length := by simpa [lens] using hk
  simp [lens, layout_eq hk']

/-- Every logical circuit is circuit `f'` of some shard `k`. -/
theorem decompose {f : Nat} (hf : f < S.system.templates.length) :
    ∃ k f', k < S.shards.length ∧ f' < (S.layout k).templates.length ∧ f = S.base k + f' := by
  rw [length_system_templates] at hf
  obtain ⟨k, f', hk, hf', eq⟩ := locate_spec S.lens hf
  refine ⟨k, f', by simpa [lens] using hk, by rw [← lens_getElem hk]; exact hf', by rw [base_eq]; exact eq⟩

theorem locate_at {k f' : Nat} (hk : k < S.shards.length) (hf : f' < (S.layout k).templates.length) :
    locate S.lens (S.base k + f') = (k, f') := by
  rw [base_eq]
  exact locate_base S.lens (by simpa [lens] using hk) (by rw [lens_getElem]; exact hf)

/-! ## Slot values of the logical system -/

variable (S) in
/-- The value of slot `s` of instance `i` of logical circuit `f`: the
invocation id for an invocation slot, the definition of a virtual slot over
physical values, else the shard's value at the slot's physical anchor. -/
def valV (main : Nat → Nat → Nat → F) (f i s : Nat) : F :=
  if (S.system.templates[f]?.bind fun T => T.slots[s]?) = some .invocation then (S.system.instId f i : F)
  else
    let phys := ((S.layout (locate S.lens f).1).shadow S.width).slotValue (main (locate S.lens f).1)
      (locate S.lens f).2 i
    match (S.layout (locate S.lens f).1).templates[(locate S.lens f).2]? with
    | some T2 => if s ∈ T2.virtual then T2.virtualValue phys s else phys s
    | none => phys s

variable (S) in
/-- A trace of the logical system holding `valV` at every logical cell. -/
def mainV (main : Nat → Nat → Nat → F) (p j : Nat) : F :=
  match S.system.places[p]? with
  | some (f, i, r) =>
      match S.system.templates[f]? with
      | some T =>
          match T.cell r j with
          | some s => S.valV main f i s
          | none => 0
      | none => 0
  | none => 0

/-- At a slot that occurs in a cell, the logical system reads `valV`. -/
theorem slotValue_mainV {main : Nat → Nat → Nat → F} {f i : Nat} (hf : f < S.system.templates.length)
    (hi : i < S.system.cap f) {T : Template F} (hT : S.system.templates[f]? = some T)
    {r j s : Nat} (hr : r < T.rows.length) (hj : j < T.width) (cell : T.cell r j = some s)
    (lt : s < T.slots.length) :
    S.system.slotValue (S.mainV main) f i s = S.valV main f i s := by
  obtain ⟨ra, ja, anchor⟩ := Template.anchor_exists hr hj cell
  obtain ⟨hra, _, acell⟩ := Template.anchor_spec anchor
  obtain ⟨T', hT', count, _⟩ := S.system.templates_getElem? hf
  rw [hT] at hT'
  cases hT'
  have place : (f, i, ra) ∈ S.system.places := S.system.mem_places.mpr ⟨hf, hi, by omega⟩
  have at_row : S.system.places[S.system.row f i ra]? = some (f, i, ra) := by
    rw [List.getElem?_eq_getElem (S.system.row_lt place), S.system.places_row place]
  have ne : s ≠ T.idVar := by simp [Template.idVar]; omega
  simp [System.slotValue, hT, ne, anchor, mainV, at_row, acell]

theorem slotValue_idVar {main : Nat → Nat → Nat → F} {f i : Nat} {T : Template F}
    (hT : S.system.templates[f]? = some T) :
    S.system.slotValue (S.mainV main) f i T.idVar = (S.system.instId f i : F) := by
  simp [System.slotValue, hT]

end Sharded

end Aiur.Tiling.Periodic
