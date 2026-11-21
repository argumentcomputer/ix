import Aiur.Declarations
import Mathlib.Algebra.Field.Basic

namespace Aiur

/-- Circuit values carry static types and a fixed number of field columns. -/
structure WireValue (α : Type) where
  type : Ty
  words : List α
  deriving Repr, BEq, DecidableEq

def WireValue.field (value : α) : WireValue α := ⟨.field, [value]⟩
def WireValue.ptr (target : Ty) (address : α) : WireValue α := ⟨.ptr target, [address]⟩
def WireValue.tuple (values : List (WireValue α)) : WireValue α :=
  ⟨.tuple (values.map WireValue.type), values.flatMap WireValue.words⟩

instance [OfNat α n] : OfNat (WireValue α) n := ⟨.field (OfNat.ofNat n)⟩

def WireValue.map (f : α → β) (value : WireValue α) : WireValue β :=
  ⟨value.type, value.words.map f⟩

/-- Correct column count, without requiring a valid tag or canonical payload. -/
def WireValue.Sized (decls : Declarations) (value : WireValue α) : Prop :=
  ∃ layout, decls.layout value.type = .ok layout ∧ value.words.length = layout.width

namespace Layout

def payloadWidth (constructors : List (String × Layout)) : Nat :=
  (constructors.map (fun c => c.2.width)).foldr max 0

mutual
  /-- Only multiple-constructor enums store a tag. Unused payload words are zero. -/
  def encode [NatCast F] [Zero F] : Layout → Value F → Option (List F)
    | .field, .field value => some [value]
    | .ptr target, .ptr actual address => if target = actual then some [address] else none
    | .tuple layouts, .tuple values => encodeList layouts values
    | .enum name constructors, .construct actual ctor args => do
        if name ≠ actual then none else do
          let (index, payload) ← encodeConstructor constructors ctor args 0
          return enumWords constructors.length (index : F)
            (payload ++ List.replicate (payloadWidth constructors - payload.length) 0)
    | _, _ => none
  termination_by layout _ => sizeOf layout

  def encodeList [NatCast F] [Zero F] : List Layout → List (Value F) → Option (List F)
    | [], [] => some []
    | layout :: layouts, value :: values => do
        return (← encode layout value) ++ (← encodeList layouts values)
    | _, _ => none
  termination_by layouts _ => sizeOf layouts

  def encodeConstructor [NatCast F] [Zero F] : List (String × Layout) → String →
      List (Value F) → Nat → Option (Nat × List F)
    | [], _, _, _ => none
    | (name, layout) :: rest, ctor, args, index =>
        if name = ctor then do return (index, ← encode layout (.tuple args))
        else encodeConstructor rest ctor args (index + 1)
  termination_by layouts _ _ _ => sizeOf layouts
end

mutual
  /-- Decoding validates the active tag and all canonical padding; it never follows pointers. -/
  def decode [NatCast F] [Zero F] [DecidableEq F] : Layout → List F → Option (Value F)
    | .field, [value] => some (.field value)
    | .ptr target, [address] => some (.ptr target address)
    | .tuple layouts, words => return .tuple (← decodeList layouts words)
    | .enum name constructors, words => do
        let (tag, payload) ← enumParts constructors.length ((0 : Nat) : F) words
        if payload.length = payloadWidth constructors then do
          let (ctor, args) ← decodeConstructor constructors tag payload 0
          return .construct name ctor args
        else none
    | _, _ => none
  termination_by layout _ => sizeOf layout

  def decodeList [NatCast F] [Zero F] [DecidableEq F] : List Layout → List F → Option (List (Value F))
    | [], [] => some []
    | layout :: layouts, words => do
        return (← decode layout (words.take layout.width)) ::
          (← decodeList layouts (words.drop layout.width))
    | [], _ :: _ => none
  termination_by layouts _ => sizeOf layouts

  def decodeConstructor [NatCast F] [Zero F] [DecidableEq F] : List (String × Layout) →
      F → List F → Nat → Option (String × List (Value F))
    | [], _, _, _ => none
    | (name, layout) :: rest, tag, payload, index =>
        if tag = (index : F) then do
          let .tuple args ← decode layout (payload.take layout.width) | none
          if (payload.drop layout.width).all (fun x => decide (x = 0)) then
            return (name, args)
          else none
        else decodeConstructor rest tag payload (index + 1)
  termination_by layouts _ _ _ => sizeOf layouts
end

end Layout

/-- Entry decoding is type-directed, including nominal enum identity. -/
def WireValue.decode [NatCast F] [Zero F] [DecidableEq F] (decls : Declarations)
    (value : WireValue F) : Option (Value F) := do
  let layout ← (decls.layout value.type).toOption
  let decoded ← layout.decode value.words
  if decoded.hasType decls value.type then some decoded else none

def Value.encode [NatCast F] [Zero F] (decls : Declarations) (value : Value F) :
    Option (WireValue F) := do
  if !value.wellFormed decls then none else do
    let layout ← (decls.layout value.type).toOption
    return ⟨value.type, ← layout.encode value⟩

/-- Natural-number constructor tags must remain distinct in the actual field. -/
def Declarations.tagsValid (F : Type) [NatCast F] [DecidableEq F] (decls : Declarations) : Bool :=
  decls.all fun decl => decide ((List.range decl.constructors.length).map (fun i : Nat => (i : F))).Nodup

theorem Declarations.tagsValid_spec [NatCast F] [DecidableEq F] (decls : Declarations) :
    decls.tagsValid F = true ↔
      ∀ decl ∈ decls, ((List.range decl.constructors.length).map (fun i : Nat => (i : F))).Nodup := by
  simp [tagsValid, List.all_eq_true]

/-- The prover chooses raw typed cells. Invalid unused encodings impose no extra requirement. -/
structure WireROM (F : Type) where
  entries : List (F × WireValue F) := []
  deriving Repr, BEq

/-- Functionality is type-directed. Physical width tables need no nominal tag:
their words can have several static typed views at the same address. -/
def WireROM.Valid (rom : WireROM F) : Prop :=
  ∀ a ∈ rom.entries, ∀ b ∈ rom.entries,
    a.1 = b.1 → a.2.type = b.2.type → a.2 = b.2

instance WireROM.instDecidableValid [DecidableEq F] (rom : WireROM F) : Decidable rom.Valid :=
  inferInstanceAs (Decidable (∀ a ∈ rom.entries, ∀ b ∈ rom.entries,
    a.1 = b.1 → a.2.type = b.2.type → a.2 = b.2))

end Aiur
