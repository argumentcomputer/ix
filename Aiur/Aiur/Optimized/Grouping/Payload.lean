import Aiur.Optimized.Grouping.Substitution
import Aiur.Optimized.Grouping.Exclusions
import Aiur.Circuit.Erasure

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

/-- Logical schemas accompany the actual scalar message expressions. The
numeric channel/width tags are checked separately, including unused slots. -/
structure Payload (α : Type) where
  root : Message α
  calls : List (α × Message α)
  cells : List (α × α × WireValue α)
  deriving DecidableEq

def mapMessage (f : α → β) (m : Message α) : Message β :=
  ⟨m.channel, m.args.map (WireValue.map f), m.result.map f⟩

@[simp] theorem mapMessage_map (f : α → β) (g : β → γ) (m : Message α) :
    mapMessage g (mapMessage f m) = mapMessage (g ∘ f) m := by
  simp [mapMessage, WireValue.map_map, List.map_map, Function.comp_def]

def Payload.map (f : α → β) (p : Payload α) : Payload β :=
  ⟨mapMessage f p.root, p.calls.map (fun (e, m) => (f e, mapMessage f m)),
    p.cells.map (fun (e, address, value) => (f e, f address, value.map f))⟩

@[simp] theorem Payload.map_map (f : α → β) (g : β → γ) (p : Payload α) :
    (p.map f).map g = p.map (g ∘ f) := by
  cases p
  simp [Payload.map, List.map_map, Function.comp_def, WireValue.map_map]

def Payload.denote (p : Payload (Polynomial F)) (a : Nat → F) : Payload F :=
  p.map (fun p => p.denote a)

def Payload.subst (p : Payload (Polynomial F)) (r : Nat → Polynomial F) : Payload (Polynomial F) :=
  p.map (Polynomial.subst r)

omit [DecidableEq F] in
@[simp] theorem Payload.denote_subst (p : Payload (Polynomial F)) (r : Nat → Polynomial F)
    (a : Nat → F) : (p.subst r).denote a = p.denote (fun v => (r v).denote a) := by
  simp [Payload.denote, Payload.subst, Function.comp_def]

def Payload.Identical (p q : Payload (Polynomial F)) : Prop :=
  p.map Polynomial.simplify = q.map Polynomial.simplify

instance (p q : Payload (Polynomial F)) : Decidable (p.Identical q) := by
  unfold Payload.Identical
  infer_instance

theorem Payload.Identical.denote {p q : Payload (Polynomial F)} (h : p.Identical q) (a : Nat → F) :
    p.denote a = q.denote a := by
  have h := congrArg (fun p : Payload (Polynomial F) => p.denote a) h
  simpa [Payload.denote, Function.comp_def] using h

def Payload.MemoryValid (p : Payload F) (rom : WireROM F) : Prop :=
  ∀ cell ∈ p.cells, cell.1 = 1 → (cell.2.1, cell.2.2) ∈ rom.entries

def Payload.requirements (p : Payload F) : List (Message F) :=
  p.calls.filterMap fun (e, m) => if e = 1 then some m else none

/-- Active equivalence of two concrete payloads: equal root, equal enables on
every call and memory entry, and equal payloads whenever enabled (`e = 1`).
Used when intra-chip `C2` compaction shares a physical slot across mutually
exclusive lookups so inactive entries hold another branch's words. -/
def Payload.ActiveEquiv (p q : Payload F) : Prop :=
  p.root = q.root ∧
  List.Forall₂ (fun (c₁ c₂ : F × Message F) => c₁.1 = c₂.1 ∧ (c₁.1 = 1 → c₁.2 = c₂.2))
    p.calls q.calls ∧
  List.Forall₂ (fun (c₁ c₂ : F × F × WireValue F) =>
    c₁.1 = c₂.1 ∧ (c₁.1 = 1 → c₁.2.1 = c₂.2.1 ∧ c₁.2.2 = c₂.2.2)) p.cells q.cells

theorem Payload.ActiveEquiv.of_eq {p q : Payload F} (h : p = q) : p.ActiveEquiv q := by
  subst h
  refine ⟨rfl, List.forall₂_iff_get.mpr ⟨rfl, fun _ _ _ => ⟨rfl, fun _ => rfl⟩⟩,
    List.forall₂_iff_get.mpr ⟨rfl, fun _ _ _ => ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩⟩⟩

theorem Payload.ActiveEquiv.root_eq {p q : Payload F} (h : p.ActiveEquiv q) :
    p.root = q.root := h.1

theorem Payload.ActiveEquiv.requirements_eq {p q : Payload F} (h : p.ActiveEquiv q) :
    p.requirements = q.requirements := by
  unfold Payload.requirements
  have go : ∀ {xs ys : List (F × Message F)},
      List.Forall₂ (fun c₁ c₂ => c₁.1 = c₂.1 ∧ (c₁.1 = 1 → c₁.2 = c₂.2)) xs ys →
      (xs.filterMap fun (e, m) => if e = 1 then some m else none) =
        (ys.filterMap fun (e, m) => if e = 1 then some m else none) := by
    intro xs ys hrel
    induction hrel with
    | nil => rfl
    | @cons x y xs ys hxy _ ih =>
        rcases x with ⟨e₁, m₁⟩
        rcases y with ⟨e₂, m₂⟩
        rcases hxy with ⟨he, hm⟩
        dsimp only at he hm
        subst he
        by_cases h1 : e₁ = 1
        · simp [h1, hm h1, ih]
        · simp [h1, ih]
  exact go h.2.1

theorem Payload.ActiveEquiv.memoryValid_iff {p q : Payload F} (h : p.ActiveEquiv q)
    (rom : WireROM F) : p.MemoryValid rom ↔ q.MemoryValid rom := by
  unfold Payload.MemoryValid
  have go : ∀ {xs ys : List (F × F × WireValue F)},
      List.Forall₂ (fun c₁ c₂ => c₁.1 = c₂.1 ∧ (c₁.1 = 1 → c₁.2.1 = c₂.2.1 ∧ c₁.2.2 = c₂.2.2)) xs ys →
      ((∀ cell ∈ xs, cell.1 = 1 → (cell.2.1, cell.2.2) ∈ rom.entries) ↔
        (∀ cell ∈ ys, cell.1 = 1 → (cell.2.1, cell.2.2) ∈ rom.entries)) := by
    intro xs ys hrel
    induction hrel with
    | nil => simp
    | @cons x y xs ys hxy _ ih =>
        rcases x with ⟨e₁, a₁, v₁⟩
        rcases y with ⟨e₂, a₂, v₂⟩
        rcases hxy with ⟨he, hval⟩
        dsimp only at he hval
        subst he
        simp only [List.mem_cons, forall_eq_or_imp]
        refine and_congr ?_ ih
        by_cases h1 : e₁ = 1
        · obtain ⟨ha, hv⟩ := hval h1
          simp [h1, ha, hv]
        · simp [h1]
  exact go h.2.2

def ofChip (c : Chip F) : Payload (Polynomial F) :=
  ⟨⟨c.name, c.inputs.map (WireValue.map .var), c.output⟩,
    c.sends.map (fun s => (s.enable, ⟨s.channel, s.args, s.result.map .var⟩)),
    c.memory.map (fun m => (m.enable, m.address, m.value))⟩

omit [DecidableEq F] in
theorem ofChip_root (c : Chip F) (a : Nat → F) :
    ((ofChip c).denote a).root = c.conclusion a := by
  simp [ofChip, Payload.denote, Payload.map, mapMessage, Chip.conclusion,
    WireValue.map_map, List.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote]

theorem ofChip_requirements (c : Chip F) (a : Nat → F) :
    ((ofChip c).denote a).requirements = c.requirements a := by
  simp [ofChip, Payload.denote, Payload.map, Payload.requirements, Chip.requirements,
    List.filterMap_map, Function.comp_def, Send.message, mapMessage, WireValue.map_map,
    Scalar.Circuit.ArithExpr.denote]

omit [DecidableEq F] in
theorem ofChip_memory (c : Chip F) (a : Nat → F) (rom : WireROM F) :
    ((ofChip c).denote a).MemoryValid rom ↔ ∀ m ∈ c.memory, m.Valid rom a := by
  simp [ofChip, Payload.denote, Payload.map, Payload.MemoryValid, MemoryLookup.Valid]

def word (ps : List (Polynomial F)) (i : Nat) : Polynomial F := ps[i]?.getD (.const 0)

/-- Decode with the static source signature, but read every word from the
emitted shared lookup. Extra padding and numeric tags are covered by Packets. -/
def decodeMessage (shape : Message α) (words : List β) : Message β :=
  ⟨shape.channel, Erasure.readWords (shape.args.map Erasure.shape) (words.drop 2),
    ⟨shape.result.type, (words.drop (2 + (shape.args.flatMap WireValue.words).length)).take shape.result.words.length⟩⟩

private theorem readWords_map {α β : Type} (f : α → β) :
    ∀ (shapes : List (Ty × Nat)) (ws : List α),
      (Erasure.readWords shapes ws).map (WireValue.map f) =
        Erasure.readWords shapes (ws.map f)
  | [], _ => rfl
  | (ty, width) :: rest, ws => by
      simp [Erasure.readWords, WireValue.map, List.map_take, List.map_drop, readWords_map f rest]

theorem mapMessage_decodeMessage {α β γ : Type} (f : β → γ) (shape : Message α) (words : List β) :
    mapMessage f (decodeMessage shape words) = decodeMessage shape (words.map f) := by
  simp [mapMessage, decodeMessage, WireValue.map, readWords_map, List.map_drop, List.map_take]

private theorem readWords_prefix {α : Type} :
    ∀ (values : List (WireValue α)) (extra : List α),
      Erasure.readWords (values.map Erasure.shape) (values.flatMap WireValue.words ++ extra) = values
  | [], _ => rfl
  | v :: vs, extra => by
      simp only [List.map_cons, List.flatMap_cons, List.append_assoc, Erasure.shape, Erasure.readWords,
        List.take_left, List.drop_left, readWords_prefix vs extra]

private theorem list_eq_append_drop {α : Type} {xs ys : List α}
    (hlen : ys.length ≤ xs.length)
    (hget : ∀ (j : Nat) (hj : j < ys.length), xs[j]'(Nat.lt_of_lt_of_le hj hlen) = ys[j]'hj) :
    xs = ys ++ xs.drop ys.length := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi _
    by_cases hlt : i < ys.length
    · rw [List.getElem_append_left hlt]
      exact hget i hlt
    · rw [List.getElem_append_right (Nat.not_lt.mp hlt), List.getElem_drop]
      congr 1; omega

theorem decodeMessage_of_prefix {α : Type} (shape : Message α) (target : Message F)
    (hchan : shape.channel = target.channel)
    (hargsShape : shape.args.map Erasure.shape = target.args.map Erasure.shape)
    (hargsLen : (shape.args.flatMap WireValue.words).length =
      (target.args.flatMap WireValue.words).length)
    (hresTy : shape.result.type = target.result.type)
    (hresLen : shape.result.words.length = target.result.words.length)
    (words : List F)
    (hlen : 2 + (target.args.flatMap WireValue.words ++ target.result.words).length ≤ words.length)
    (hget : ∀ (j : Nat) (hj : j < (target.args.flatMap WireValue.words ++ target.result.words).length),
      words[2 + j]'(by omega) = (target.args.flatMap WireValue.words ++ target.result.words)[j]'hj) :
    decodeMessage shape words = target := by
  set argsW := target.args.flatMap WireValue.words
  set resW := target.result.words
  have hdrop2 : words.drop 2 = (argsW ++ resW) ++ (words.drop 2).drop (argsW ++ resW).length := by
    refine list_eq_append_drop (by simp only [List.length_drop]; omega) (fun j hj => ?_)
    rw [List.getElem_drop]
    exact hget j hj
  unfold decodeMessage
  rw [hchan, hargsShape, hargsLen, hresTy, hresLen]
  have hargs : Erasure.readWords (target.args.map Erasure.shape) (words.drop 2) = target.args := by
    rw [hdrop2, List.append_assoc]
    exact readWords_prefix target.args _
  have hres : (words.drop (2 + argsW.length)).take resW.length = resW := by
    have hdrop : words.drop (2 + argsW.length) = (words.drop 2).drop argsW.length := by
      rw [List.drop_drop, Nat.add_comm]
    rw [hdrop, hdrop2, List.append_assoc, List.drop_left, List.take_left]
  cases target with
  | mk ch args res =>
      cases res with
      | mk rty rwords =>
          dsimp only at hargs hres ⊢
          rw [hargs, hres]

/-- Un-tagged enable and payload words (at positions `≥ 2`, matching `messages`)
for logical lookup `k` of member `m` (calls first, then memory cells). Used by
`Certificate` without depending on callable IDs. -/
def Member.rawPayloadAt (m : Member F) (k : Nat) : Polynomial F × List (Polynomial F) :=
  if hk : k < m.origin.sends.length then
    let s := m.origin.sends[k]'hk
    (s.enable, [.const 0, .const 0] ++ s.args.flatMap WireValue.words ++ s.result.words.map .var)
  else if hm : k - m.origin.sends.length < m.origin.memory.length then
    let mem := m.origin.memory[k - m.origin.sends.length]'hm
    (mem.enable, [.const 0, .const 0, mem.address] ++ mem.value.words)
  else
    (.const 0, [])

def Layout.slot (g : Layout F) (i : Nat) : Lookup F :=
  g.sends[i]?.getD ⟨.const 0, []⟩

def Layout.view (g : Layout F) (m : Member F) : Payload (Polynomial F) :=
  let source := ofChip m.origin
  ⟨decodeMessage source.root g.receive,
    source.calls.zipIdx.map fun ((origEnable, call), i) =>
      let s := m.slotIndex i
      let slot := g.slot s
      let enable := if (m.bucket s).length ≤ 1 then slot.enable else rename m.columns origEnable
      (enable, decodeMessage call slot.args),
    source.cells.zipIdx.map fun ((origEnable, _, value), i) =>
      let s := m.slotIndex (source.calls.length + i)
      let slot := g.slot s
      let enable := if (m.bucket s).length ≤ 1 then slot.enable else rename m.columns origEnable
      (enable, slot.args[2]?.getD (.const 0),
        ⟨value.type, (slot.args.drop 3).take value.words.length⟩)⟩

/-- This predicate checks memory using the words in the emitted shared
messages. Source-memory membership is a consequence of the certificate. -/
def Layout.ValidRow (g : Layout F) (rom : WireROM F) (a : Nat → F) : Prop :=
  Satisfies g.constraints a ∧ g.activation.denote a = 1 ∧
    ∀ m ∈ g.members, a m.selector = 1 → ((g.view m).denote a).MemoryValid rom

def Layout.LocalRule (g : Layout F) (rom : WireROM F) (root : Message F)
    (premises : List (Message F)) : Prop :=
  ∃ a m, m ∈ g.members ∧ g.ValidRow rom a ∧ a m.selector = 1 ∧
    ((g.view m).denote a).root = root ∧ ((g.view m).denote a).requirements = premises

end Aiur.Optimized.Grouping
