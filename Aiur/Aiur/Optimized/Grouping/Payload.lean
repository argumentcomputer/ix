import Aiur.Optimized.Grouping.Substitution
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

/-- Decode with the static source signature, but read every word from the
emitted shared lookup. Extra padding and numeric tags are covered by Packets. -/
def decodeMessage (shape : Message α) (words : List β) : Message β :=
  ⟨shape.channel, Erasure.readWords (shape.args.map Erasure.shape) (words.drop 2),
    ⟨shape.result.type, (words.drop (2 + (shape.args.flatMap WireValue.words).length)).take shape.result.words.length⟩⟩

def Layout.slot (g : Layout F) (i : Nat) : Lookup F :=
  g.sends[i]?.getD ⟨.const 0, []⟩

def Layout.view (g : Layout F) (m : Member F) : Payload (Polynomial F) :=
  let source := ofChip m.origin
  ⟨decodeMessage source.root g.receive,
    source.calls.zipIdx.map fun ((_, call), i) =>
      let slot := g.slot i
      (slot.enable, decodeMessage call slot.args),
    source.cells.zipIdx.map fun ((_, _, value), i) =>
      let slot := g.slot (source.calls.length + i)
      (slot.enable, slot.args[2]?.getD (.const 0),
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
