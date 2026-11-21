import Aiur.Generic.Aliases
import Aiur.Wire

namespace Aiur.Execution

/-- Structured, address-free data supplied by the host. Array element types
are explicit so empty arrays still carry their complete type. Nominal values
use source types (including generic arguments), never layout tags or offsets. -/
inductive DataValue (F : Type) where
  | field (value : F)
  | tuple (items : List (DataValue F))
  | array (element : Generic.Ty) (items : List (DataValue F))
  | record (type : Generic.Ty) (fields : List (String × DataValue F))
  | construct (type : Generic.Ty) (constructor : String) (args : List (DataValue F))
  deriving Repr

mutual
  def DataValue.beq [BEq F] : DataValue F → DataValue F → Bool
    | .field x, .field y => x == y
    | .tuple xs, .tuple ys => DataValue.listBeq xs ys
    | .array t xs, .array t' ys => t == t' && DataValue.listBeq xs ys
    | .record t fs, .record t' fs' => t == t' && DataValue.fieldsBeq fs fs'
    | .construct t c xs, .construct t' c' ys => t == t' && c == c' && DataValue.listBeq xs ys
    | _, _ => false
  termination_by left _ => sizeOf left

  def DataValue.listBeq [BEq F] : List (DataValue F) → List (DataValue F) → Bool
    | [], [] => true
    | x :: xs, y :: ys => DataValue.beq x y && DataValue.listBeq xs ys
    | _, _ => false
  termination_by left _ => sizeOf left

  def DataValue.fieldsBeq [BEq F] : List (String × DataValue F) → List (String × DataValue F) → Bool
    | [], [] => true
    | (n, v) :: xs, (n', v') :: ys => n == n' && DataValue.beq v v' && DataValue.fieldsBeq xs ys
    | _, _ => false
  termination_by left _ => sizeOf left
end

instance [BEq F] : BEq (DataValue F) := ⟨DataValue.beq⟩

instance [OfNat F n] : OfNat (DataValue F) n := ⟨.field (OfNat.ofNat n)⟩

def DataValue.type : DataValue F → Generic.Ty
  | .field _ => .field
  | .tuple items => .tuple (items.map DataValue.type)
  | .array element items => .array element items.length
  | .record type _ | .construct type _ _ => type
termination_by value => sizeOf value

def DataValue.map (f : F → G) : DataValue F → DataValue G
  | .field x => .field (f x)
  | .tuple items => .tuple (items.map (DataValue.map f))
  | .array element items => .array element (items.map (DataValue.map f))
  | .record type fields => .record type (fields.map fun entry => (entry.1, entry.2.map f))
  | .construct type ctor args => .construct type ctor (args.map (DataValue.map f))
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals first | omega | cases ‹String × DataValue F›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Retained only on the Lean side, for preparing structured execution data.
The Rust package still contains just concrete layouts and flat values. -/
structure DataTypes where
  enums : List Generic.EnumDecl := []
  structs : List Generic.StructDecl := []
  aliases : List Generic.AliasDecl := []
  opaqueNames : List String := []
  deriving Repr, BEq

def DataTypes.ofSource (p : Generic.Program F) (opaqueNames : List String) : DataTypes :=
  ⟨p.enums, p.structs, p.aliases, opaqueNames⟩

def DataTypes.program (types : DataTypes) : Generic.Program Unit :=
  { functions := [], enums := types.enums, structs := types.structs, aliases := types.aliases }

/-- Normalize transparent aliases and nominal arguments without erasing array
shapes or struct identity. The prepared program already checked alias cycles. -/
def DataTypes.resolve (types : DataTypes) : Nat → Generic.Ty → Except String Generic.Ty
  | 0, _ => throw "execution data type depth exceeded"
  | fuel + 1, type => do
      match type with
      | .field => return .field
      | .param _ => throw "execution data requires a concrete type"
      | .ptr _ => throw "execution data cannot contain pointers"
      | .tuple items => return .tuple (← items.mapM (types.resolve fuel))
      | .array element length =>
          Generic.checkArrayLength length
          return .array (← types.resolve fuel element) length
      | .named name args =>
          if types.opaqueNames.contains name then throw s!"execution data cannot contain opaque type {name}"
          let args ← args.mapM (types.resolve fuel)
          if let some decl := types.aliases.find? (·.name == name) then
            let env ← Generic.arguments decl.typeParams args
            types.resolve fuel (decl.target.subst env)
          else
            let some decl := types.program.findEnum? name | throw s!"unknown execution data type {name}"
            let _ ← Generic.arguments decl.typeParams args
            return .named name args

end Aiur.Execution
