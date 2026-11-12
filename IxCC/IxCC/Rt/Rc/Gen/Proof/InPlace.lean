import IxCC.Rt.Rc.Gen.Proof.Rewrite
import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata
import IxCC.Own.Rc.Reuse

/-! # In-place reuse of a unique cell

`inPlace_ready`: when the caller holds the only reference to a live cell (`Own.Rc.uniqueOf`, the
answer `isUnique` gives), rewriting that cell's storage with a new body of the same class
(`writeCell`) is the abstract reuse (`Own.Rc.reuseCell`: the cell dies, a fresh location with the
new body is appended) on an allocator-ready heap: the general invariant holds afterwards with the
fresh location mapped to the old address, the slot relabelled, and no free list, bump pointer or
other cell changed. The caller's tokens move as `Own.Rc.reuseCell_balance` says.

Premises a reuse site must establish: the cell is unique and the caller's token for it is among
the balanced tokens (`h`, `hc`); the new body's layout is valid and of the old cell's class
(`hlayout`, `hclass`; a larger class would overwrite the next cell, a smaller one is outside the
invariant, which ties a cell's header class to its layout's); its fields are accounted by the
caller's tokens (`hmass`); and every field has a word (`hwords`: a value word at a scanned
position, a literal below 2⁶⁴ at a scalar one). `hwords` is the premise the allocation path
already has (each field is a variable held as a word); asking it only of scalar positions is not
enough: a scanned string literal or `Nat` ≥ 2⁶³ has no word, the rewrite stores `0` there, and the
release of the reused cell takes that `0` for a cell (the negative controls F and F′ of
`IxCCTests.Rt.Rc.GenReuseControls`). Nothing in the pipeline emits a reuse yet. -/

set_option autoImplicit false
namespace IxCC.Rt.Rc.Gen
open Lir
open IxCC.Rt.Proof
open IxCC.Rt.Rc.Procs (AddressMap valueWord Slot SlotKind ObjectFrame FreeChain cursorTokens
  flattenPending)
open IxCC.Own (Heap RVal Body Cell)
open IxCC.Own.Rc (Balance refsIn edgeCount dynCount reuseCell reusedHeap)

/-! ## Relabelling the reused cell's slot -/

/-- The slot of location `old` becomes the slot of location `fresh`; every other slot is kept. -/
def relabelSlot (old fresh : Nat) (slot : Slot) : Slot :=
  match slot.kind with
  | .live k => if k = old then { slot with kind := .live fresh } else slot
  | _ => slot

@[simp] theorem relabelSlot_address (old fresh : Nat) (slot : Slot) :
    (relabelSlot old fresh slot).address = slot.address := by
  unfold relabelSlot
  split
  · split <;> rfl
  · rfl

@[simp] theorem relabelSlot_cls (old fresh : Nat) (slot : Slot) :
    (relabelSlot old fresh slot).cls = slot.cls := by
  unfold relabelSlot
  split
  · split <;> rfl
  · rfl

theorem relabelSlot_kind (old fresh : Nat) (slot : Slot) :
    (slot.kind = .live old ∧ (relabelSlot old fresh slot).kind = .live fresh) ∨
      (slot.kind ≠ .live old ∧ (relabelSlot old fresh slot).kind = slot.kind) := by
  unfold relabelSlot
  cases h : slot.kind with
  | live k =>
    by_cases hk : k = old
    · subst hk; left; simp
    · right
      refine ⟨fun e => hk (SlotKind.live.inj e), ?_⟩
      simp [hk, h]
  | pending d u p => right; exact ⟨fun e => (by cases e), h⟩
  | free => right; exact ⟨fun e => (by cases e), h⟩
  | reserved => right; exact ⟨fun e => (by cases e), h⟩

theorem relabelSlot_free (old fresh : Nat) (slot : Slot) :
    (relabelSlot old fresh slot).kind = .free ↔ slot.kind = .free := by
  rcases relabelSlot_kind old fresh slot with ⟨hold, hnew⟩ | ⟨_, hsame⟩
  · rw [hnew, hold]
    constructor <;> intro e <;> cases e
  · rw [hsame]

/-- Two slots of different kinds are different slots, so their storage is disjoint. -/
theorem ArenaPartition.separate {cmax : Nat} {heap : Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (p : ArenaPartition cmax heap addresses base bump limit slots) {s t : Slot}
    (hs : s ∈ slots) (ht : t ∈ slots) (hne : s.kind ≠ t.kind) :
    s.address.toNat + 8 * classWords s.cls ≤ t.address.toNat ∨
      t.address.toNat + 8 * classWords t.cls ≤ s.address.toNat := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem ht
  apply p.disjoint i j s t hi hj
  intro e
  subst e
  rw [hi] at hj
  cases hj
  exact hne rfl

/-- The partition after the reuse: the reused cell's slot is the fresh location's, at the same
address and class. -/
theorem ArenaPartition.relabel {cmax : Nat} {heap : Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (p : ArenaPartition cmax heap addresses base bump limit slots)
    {l : Nat} {a : Word} {b b' : Body} (hc : heap.cell? l = some (.live 1 .dyn b))
    (ha : addresses l = some a) (hclass : classOf b'.ctor = classOf b.ctor) :
    ArenaPartition cmax (reusedHeap heap l b') (fun k => if k = heap.size then some a else addresses k)
      base bump limit (slots.map (relabelSlot l heap.size)) := by
  have hl : l < heap.size := Own.Proof.cell?_some hc
  refine {
    bounds := p.bounds
    valid := ?_
    bounded := ?_
    disjoint := ?_
    accounted := ?_
    live := ?_
    placed := ?_
    pending := ?_ }
  · intro slot hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    simpa using p.valid s hs
  · intro slot hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    simpa using p.bounded s hs
  · intro i j si sj hi hj hne
    rw [List.getElem?_map] at hi hj
    cases hsi : slots[i]? with
    | none => simp [hsi] at hi
    | some s =>
      cases hsj : slots[j]? with
      | none => simp [hsj] at hj
      | some t =>
        simp only [hsi, hsj, Option.map_some, Option.some.injEq] at hi hj
        subst hi hj
        simpa using p.disjoint i j s t hsi hsj hne
  · intro n lo hi
    obtain ⟨s, hs, h⟩ := p.accounted n lo hi
    exact ⟨relabelSlot l heap.size s, List.mem_map.mpr ⟨s, hs, rfl⟩, by simpa using h⟩
  · intro slot hm location hk
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    rcases relabelSlot_kind l heap.size s with ⟨hold, hnew⟩ | ⟨hne, hsame⟩
    · rw [hnew] at hk
      cases hk
      obtain ⟨r0, b0, hc0, hm0, hcls⟩ := p.live s hs l hold
      rw [hc] at hc0
      obtain ⟨-, -, hb0⟩ := Own.Cell.live.inj (Option.some.inj hc0)
      refine ⟨1, b', Own.Rc.reusedHeap_new heap l b', ?_, ?_⟩
      · show (if heap.size = heap.size then some a else addresses heap.size) =
          some (relabelSlot l heap.size s).address
        rw [ite_eq_left rfl, relabelSlot_address, ← hm0, ha]
      · rw [relabelSlot_cls, hcls, ← hb0, hclass]
    · rw [hsame] at hk
      have hkl : location ≠ l := by intro e; subst e; exact hne hk
      obtain ⟨r0, b0, hc0, hm0, hcls⟩ := p.live s hs location hk
      have hloc : location < heap.size := Own.Proof.cell?_some hc0
      refine ⟨r0, b0, ?_, ?_, by simpa using hcls⟩
      · rw [Own.Rc.reusedHeap_cell hl, ite_eq_right (Nat.ne_of_lt hloc), ite_eq_right (Ne.symm hkl)]
        exact hc0
      · show (if location = heap.size then some a else addresses location) =
          some (relabelSlot l heap.size s).address
        rw [ite_eq_right (Nat.ne_of_lt hloc), relabelSlot_address]
        exact hm0
  · intro location refs body hk
    rw [Own.Rc.reusedHeap_cell hl] at hk
    by_cases hks : location = heap.size
    · subst hks
      obtain ⟨s, hs, hsk⟩ := p.placed l 1 b hc
      refine ⟨relabelSlot l heap.size s, List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
      rcases relabelSlot_kind l heap.size s with ⟨_, hnew⟩ | ⟨hne, _⟩
      · exact hnew
      · exact absurd hsk hne
    · rw [ite_eq_right hks] at hk
      by_cases hlk : l = location
      · rw [ite_eq_left hlk] at hk
        cases hk
      · rw [ite_eq_right hlk] at hk
        obtain ⟨s, hs, hsk⟩ := p.placed location refs body hk
        refine ⟨relabelSlot l heap.size s, List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
        rcases relabelSlot_kind l heap.size s with ⟨hold, _⟩ | ⟨_, hsame⟩
        · rw [hsk] at hold
          cases hold
          exact absurd rfl hlk
        · rw [hsame]
          exact hsk
  · intro slot hm location suffix pred hk
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    rcases relabelSlot_kind l heap.size s with ⟨_, hnew⟩ | ⟨_, hsame⟩
    · rw [hnew] at hk
      cases hk
    · rw [hsame] at hk
      have hd := p.pending s hs location suffix pred hk
      have hloc : location < heap.size := Own.Proof.cell?_some hd
      rw [Own.Rc.reusedHeap_cell hl, ite_eq_right (Nat.ne_of_lt hloc)]
      by_cases hlk : l = location
      · rw [ite_eq_left hlk]
      · rw [ite_eq_right hlk]
        exact hd

/-! ## Helpers -/

theorem freeChain_frame {before after : X86.Memory} {chain : List Word}
    (free : FreeChain before chain)
    (frame : ∀ address ∈ chain, ∀ word, WordAt before address word → WordAt after address word) :
    FreeChain after chain := by
  induction chain with
  | nil => trivial
  | cons address tail ih =>
    exact ⟨frame address (by simp) _ free.1,
      ih free.2 (fun x hx word hw => frame x (by simp [hx]) word hw)⟩

/-- At the idle cutpoint the balanced tokens are the external ones. -/
theorem balance_idle {heap : Heap} {external : Nat → Nat} {tokens : List RVal} :
    Balance heap (fun k => external k + refsIn k tokens) ((none : Option RVal).toList ++ cursorTokens []) ↔
      Balance heap external tokens := by
  have z : ∀ k, refsIn k ((none : Option RVal).toList ++ cursorTokens []) = 0 := by
    intro k
    simp [cursorTokens, flattenPending, refsIn]
  constructor
  · intro hb k
    have e := hb k
    rw [z] at e
    dsimp only at e
    omega
  · intro hb k
    have e := hb k
    rw [z]
    dsimp only
    omega

theorem live_of_dynCount {heap : Heap} {k : Nat} (h : 0 < dynCount heap k) :
    ∃ r body, heap.cell? k = some (.live r .dyn body) := by
  unfold dynCount at h
  split at h
  · next r body hcell => exact ⟨r, body, hcell⟩
  · omega

/-! ## In-place reuse -/

/-- In-place reuse: a unique cell's storage holds the new body when the new body has the same
class and every field has a word. No free list, bump pointer or other cell changes; the fresh
abstract location is mapped to the old address. -/
theorem inPlace_ready {cmax : Nat} {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    {external : Nat → Nat} {l : Nat} {a : Word} {b b' : Body} {rest kept : List RVal}
    (h : AllocatorReady cmax heap addresses mem (fun k => external k + refsIn k (.loc l :: rest))
      context base bump limit slots lists)
    (hc : heap.cell? l = some (.live 1 .dyn b)) (ha : addresses l = some a)
    (hlayout : (layoutOf b'.ctor).ok = true)
    (harity : b'.fields.length = b'.ctor.nobj + b'.ctor.nscalar)
    (hshared : b'.ctor.fieldKinds = List.replicate b'.ctor.nobj .shared)
    (hclass : classOf b'.ctor = classOf b.ctor)
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept))
    (hwords : ∀ j value, b'.fields[j]? = some value → (fieldWord addresses b'.ctor j value).isSome) :
    ∃ heap' slots',
      reuseCell heap l b' = some (.loc heap.size, heap') ∧
      AllocatorReady cmax heap' (fun k => if k = heap.size then some a else addresses k)
        (writeCell mem addresses a b' (classOf b.ctor))
        (fun k => external k + refsIn k (.loc heap.size :: kept))
        context base bump limit slots' lists := by
  have idle := h.idle
  have hl : l < heap.size := Own.Proof.cell?_some hc
  have hb : Balance heap external (.loc l :: rest) := balance_idle.mp idle.balance
  obtain ⟨_, _, h3, _, _, h6, _⟩ := Own.Rc.reuse_exclusive hc hb
  obtain ⟨a1, _, a3, _⟩ := Own.Rc.reuse_mass_avoid hc hb hmass
  obtain ⟨H', hreuse, hbal'⟩ := Own.Rc.reuseCell_balance hc hb hmass
  rw [Own.Rc.reuseCell_some hc] at hreuse
  cases hreuse
  refine ⟨reusedHeap heap l b', slots.map (relabelSlot l heap.size), Own.Rc.reuseCell_some hc, ?_⟩
  -- the reused cell and its slot
  obtain ⟨-, a0, ha0, oldCell0⟩ := idle.live.cell l 1 .dyn b hc
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  have oldCell : LiveCell addresses mem a 1 b := ea0 ▸ oldCell0
  obtain ⟨sa, hsa, hsak⟩ := idle.partition.placed l 1 b hc
  obtain ⟨r0, b0, hc0, hsaddr, hscls⟩ := idle.partition.live sa hsa l hsak
  rw [hc] at hc0
  obtain ⟨-, -, hb0⟩ := Own.Cell.live.inj (Option.some.inj hc0)
  rw [← hb0] at hscls
  rw [ha] at hsaddr
  have hsaa : sa.address = a := (Option.some.inj hsaddr).symm
  have hslot : 8 * classWords sa.cls = cellBytesOf b.ctor := by rw [hscls]; rfl
  have hvalid := idle.partition.valid sa hsa
  have hbd := idle.partition.bounds
  -- the rewritten words lie in the old cell
  have hbytes : cellBytesOf b'.ctor = cellBytesOf b.ctor := by unfold cellBytesOf; rw [hclass]
  have hlen := (cellBytesOf_le hlayout).2.1
  have hfit := oldCell.fit
  have hw : a.toNat + 8 * (1 + b'.fields.length) ≤ 2^64 := by omega
  have hregion : a.toNat + 8 * (1 + b'.fields.length) ≤ a.toNat + cellBytesOf b.ctor := by omega
  -- the new map agrees with the old one on every old location and on the new body's fields
  have hmapNew : ∀ k, RVal.loc k ∈ b'.fields →
      (fun k => if k = heap.size then some a else addresses k) k = addresses k := by
    intro k hk
    have hne : k ≠ heap.size := by
      intro e; subst e; exact Own.Rc.refsIn_eq_zero a3 hk
    exact ite_eq_right hne
  have newCell := oldCell.rewrite hlayout harity hshared hclass hwords hmapNew
  have keep : ∀ k c, heap.cell? k = some c → k ≠ l → (reusedHeap heap l b').cell? k = some c := by
    intro k c hk hkl
    have hks : k ≠ heap.size := Nat.ne_of_lt (Own.Proof.cell?_some hk)
    rw [Own.Rc.reusedHeap_cell hl, ite_eq_right hks, ite_eq_right (Ne.symm hkl)]
    exact hk
  have oldLive : ∀ k r body x, k ≠ l → heap.cell? k = some (.live r .dyn body) →
      addresses k = some x →
      LiveCell (fun k => if k = heap.size then some a else addresses k)
        (writeCell mem addresses a b' (classOf b.ctor)) x r body := by
    intro k r body x hkl hk hx
    obtain ⟨-, x0, hx0, cell0⟩ := idle.live.cell k r .dyn body hk
    have ex0 : x0 = x := Option.some.inj (hx0.symm.trans hx)
    have cell : LiveCell addresses mem x r body := ex0 ▸ cell0
    have hdis := idle.live.disjoint l k 1 r b body a x hc hk ha hx (fun e => hkl e.symm)
    have hcf := cell.fit
    have frame : ObjectFrame mem (writeCell mem addresses a b' (classOf b.ctor)) x
        (cellBytesOf body.ctor) :=
      writeCell_objectFrame hw (by omega) (by omega)
    refine (cell.frame frame).remap (fun j hj => ?_)
    have hne : j ≠ heap.size := by
      intro e; subst e; exact Own.Rc.fields_avoid h6 hk hj
    exact ite_eq_right hne
  -- every live cell after the reuse is the new one or an old one other than `l`
  have classify : ∀ k r body x, (reusedHeap heap l b').cell? k = some (.live r .dyn body) →
      (fun k => if k = heap.size then some a else addresses k) k = some x →
      (k = heap.size ∧ body = b' ∧ x = a) ∨
        (k ≠ heap.size ∧ k ≠ l ∧ heap.cell? k = some (.live r .dyn body) ∧ addresses k = some x) := by
    intro k r body x hk hx
    rw [Own.Rc.reusedHeap_cell hl] at hk
    by_cases hks : k = heap.size
    · subst hks
      rw [ite_eq_left rfl] at hk
      have hx' : (if heap.size = heap.size then some a else addresses heap.size) = some x := hx
      rw [ite_eq_left rfl] at hx'
      cases hk
      cases hx'
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_right hks] at hk
      have hx' : (if k = heap.size then some a else addresses k) = some x := hx
      rw [ite_eq_right hks] at hx'
      by_cases hlk : l = k
      · rw [ite_eq_left hlk] at hk
        cases hk
      · rw [ite_eq_right hlk] at hk
        exact Or.inr ⟨hks, Ne.symm hlk, hk, hx'⟩
  have live' : HeapLive (reusedHeap heap l b') (fun k => if k = heap.size then some a else addresses k)
      (writeCell mem addresses a b' (classOf b.ctor)) := by
    refine { cell := ?_, fields_live := ?_, disjoint := ?_ }
    · intro k r m body hk
      have hk0 := hk
      rw [Own.Rc.reusedHeap_cell hl] at hk0
      by_cases hks : k = heap.size
      · subst hks
        rw [ite_eq_left rfl] at hk0
        cases hk0
        exact ⟨rfl, a, ite_eq_left rfl, newCell⟩
      · rw [ite_eq_right hks] at hk0
        by_cases hlk : l = k
        · rw [ite_eq_left hlk] at hk0
          cases hk0
        · rw [ite_eq_right hlk] at hk0
          obtain ⟨hm, x, hx, _⟩ := idle.live.cell k r m body hk0
          subst hm
          exact ⟨rfl, x, (ite_eq_right hks).trans hx, oldLive k r body x (Ne.symm hlk) hk0 hx⟩
    · intro k r body child hk hchild
      rw [Own.Rc.reusedHeap_cell hl] at hk
      by_cases hks : k = heap.size
      · rw [ite_eq_left hks] at hk
        cases hk
        have hp := Own.Rc.refsIn_pos hchild
        have hd := Own.Rc.reuse_mass_live hb hc hmass (k := child)
          (by rw [Own.Rc.refsIn_append]; omega)
        obtain ⟨cr, cb, hcell⟩ := live_of_dynCount hd
        have hcl : child ≠ l := by
          intro e; subst e; exact Own.Rc.refsIn_eq_zero a1 hchild
        exact ⟨cr, cb, keep child _ hcell hcl⟩
      · rw [ite_eq_right hks] at hk
        by_cases hlk : l = k
        · rw [ite_eq_left hlk] at hk
          cases hk
        · rw [ite_eq_right hlk] at hk
          obtain ⟨cr, cb, hcell⟩ := idle.live.fields_live k r body child hk hchild
          have hcl : child ≠ l := by
            intro e; subst e; exact Own.Rc.fields_avoid h3 hk hchild
          exact ⟨cr, cb, keep child _ hcell hcl⟩
    · intro l₁ l₂ r₁ r₂ b₁ b₂ x₁ x₂ h₁ h₂ m₁ m₂ hne
      rcases classify l₁ r₁ b₁ x₁ h₁ m₁ with ⟨e₁, eb₁, ex₁⟩ | ⟨s₁, n₁, c₁, d₁⟩ <;>
        rcases classify l₂ r₂ b₂ x₂ h₂ m₂ with ⟨e₂, eb₂, ex₂⟩ | ⟨s₂, n₂, c₂, d₂⟩
      · exact absurd (e₁.trans e₂.symm) hne
      · rw [eb₁, ex₁, hbytes]
        exact idle.live.disjoint l l₂ 1 r₂ b b₂ a x₂ hc c₂ ha d₂ (fun e => n₂ e.symm)
      · rw [eb₂, ex₂, hbytes]
        exact idle.live.disjoint l₁ l r₁ 1 b₁ b x₁ a c₁ hc d₁ ha n₁
      · exact idle.live.disjoint l₁ l₂ r₁ r₂ b₁ b₂ x₁ x₂ c₁ c₂ d₁ d₂ hne
  have inv : ReleaseInvariant cmax (reusedHeap heap l b')
      (fun k => if k = heap.size then some a else addresses k)
      (writeCell mem addresses a b' (classOf b.ctor))
      (fun k => external k + refsIn k (.loc heap.size :: kept)) none []
      context base bump limit (slots.map (relabelSlot l heap.size)) lists := by
    refine {
      balance := balance_idle.mpr hbal'
      live := live'
      partition := idle.partition.relabel hc ha hclass
      cursors := trivial
      cursor_distinct := by simp
      cursor_nonzero := by simp
      cursor_layout := by simp
      cursor_access := by simp
      cursor_class := by simp
      cursor_scan := by simp
      cursors_placed := ?_
      pending_exact := ?_
      free_exact := ?_
      free_distinct := idle.free_distinct
      free_placed := ?_
      free_chains := ?_
      free_heads := ?_
      head_writable := ?_
      head_fit := idle.head_fit
      context_fit := idle.context_fit
      head_disjoint := ?_ }
    · intro earlier frame tail impossible
      have lengths := congrArg List.length impossible
      simp at lengths
    · intro slot hm location suffix pred
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
      have old := idle.pending_exact s hs location suffix pred
      constructor
      · intro hk
        exfalso
        rcases relabelSlot_kind l heap.size s with ⟨_, hnew⟩ | ⟨_, hsame⟩
        · rw [hnew] at hk
          cases hk
        · rw [hsame] at hk
          obtain ⟨earlier, frame, tail, he, _⟩ := old.mp hk
          have lengths := congrArg List.length he
          simp at lengths
      · rintro ⟨earlier, frame, tail, he, _⟩
        have lengths := congrArg List.length he
        simp at lengths
    · intro slot hm
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
      rw [relabelSlot_free, relabelSlot_address, relabelSlot_cls]
      exact idle.free_exact s hs
    · intro cls x hx
      obtain ⟨s, hs, hsx, hsc, hsk⟩ := idle.free_placed cls x hx
      exact ⟨relabelSlot l heap.size s, List.mem_map.mpr ⟨s, hs, rfl⟩, by simpa using hsx,
        by simpa using hsc, (relabelSlot_free l heap.size s).mpr hsk⟩
    · intro cls
      apply freeChain_frame (idle.free_chains cls)
      intro x hx word hwx
      obtain ⟨f, hf, hfx, _, hfk⟩ := idle.free_placed cls x hx
      have hsep := idle.partition.separate hsa hf (by rw [hsak, hfk]; intro e; cases e)
      have hfv := idle.partition.valid f hf
      subst hfx
      rw [hsaa, hslot] at hsep
      exact writeCell_wordAt hw (by omega) (by omega) hwx
    · intro cls lo hi
      have hd := idle.head_disjoint cls lo hi sa hsa
      rw [hsaa, hslot] at hd
      exact writeCell_wordAt hw (idle.head_fit cls lo hi) (by omega) (idle.free_heads cls lo hi)
    · intro cls lo hi j hj
      rw [writeCell_writable]
      exact idle.head_writable cls lo hi j hj
    · intro cls lo hi slot hm
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
      simpa using idle.head_disjoint cls lo hi s hs
  have hlo : base.toNat ≤ a.toNat := by rw [← hsaa]; exact hvalid.2.2.2.1
  have hhi : a.toNat + 8 * (1 + b'.fields.length) ≤ bump.toNat := by
    have := hvalid.2.2.2.2.1
    rw [hsaa, hslot] at this
    omega
  exact h.after_protected (writeCell_protected (context := context) hw hlo hhi) inv

end IxCC.Rt.Rc.Gen
