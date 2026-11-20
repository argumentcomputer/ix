import IxAICore.Decision

/-!
# Options and inputs as Lean types

A decision's **options** are a finite Lean type: an `IxAICore.Finite` instance lists its values in
a fixed order, and that order fixes which model output scores which option. `finiteOf` builds the
instance from the list alone; `Finite.Lawful` is the decidable check that the listing and the
index agree.

A decision's **input** is any Lean type with an `Encode` instance, which turns a value into a
fixed-width vector of small integers, the model's features. Instances follow the type's
structure:

| Type | Encoding | Width |
|---|---|---|
| `Bool` | `0` or `1` | 1 |
| any `Finite` type (an enumeration) | one-hot | number of values |
| `Fin (n + 1)` (an ordered level) | thermometer: `k` ones, then zeros | `n` |
| `α × β` | concatenation | sum |
| `Option α` | a presence flag, then `α` or zeros | `1 +` width of `α` |

A record is encoded through a projection to a product of its model-visible fields
(`Encode.via`), so the fields the model may see are stated in one place, and fields it must not
see (exact amounts, identifiers) are simply left out.

Features are integers because `IxAICore.Spec.inputs` reads them with `Fx.ofInt`. A quantity has
to be bucketed into a small ordered level first; there is no encoding of free text.
-/

namespace IxAIDecide

open IxAICore

/-- Position of the first element equal to `a`, or the list's length if there is none. -/
def indexOf {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | b :: bs, a => if b = a then 0 else indexOf bs a + 1

/-- The `Finite` instance whose values are `all`, in that order. -/
@[instance_reducible] def finiteOf {α : Type} [DecidableEq α] (all : List α) : Finite α :=
  ⟨all, indexOf all⟩

/-- The number of options. -/
def arity (α : Type) [Finite α] : Nat := (Finite.all : List α).length

/-- The listing is non-empty, has no duplicates, and `index` returns each value's position.
Decidable, so it is checked by `decide` for a concrete option type. Completeness (every value is
listed) is not decidable in general and is left to the instance's author; `finiteOf` on a list
missing a value gives that value the index `arity`, which no model output scores. -/
def Finite.Lawful (α : Type) [Finite α] : Bool :=
  arity α > 0 && (withIndex (Finite.all : List α) 0).all fun (a, i) => Finite.index a == i

/-- How a value becomes the model's features. -/
class Encode (α : Type) where
  /-- The number of features. -/
  width : Nat
  encode : α → List Int

namespace Encode

def ofBool (b : Bool) : Int := if b then 1 else 0

instance : Encode Bool := ⟨1, fun b => [ofBool b]⟩

/-- One-hot over the options' order. -/
def oneHot {α : Type} [Finite α] (a : α) : List Int :=
  (List.range (arity α)).map fun k => ofBool (k == Finite.index a)

/-- Any enumeration with a `Finite` instance is encoded one-hot. `Bool`'s own instance takes
precedence. -/
instance (priority := low) {α : Type} [Finite α] : Encode α := ⟨arity α, oneHot⟩

/-- An ordered level `k` of `0 … n` as `k` ones then `n - k` zeros, so a model sees "at least
`j`" for every `j` directly. -/
def thermometer (n k : Nat) : List Int := (List.range n).map fun j => ofBool (decide (j < k))

instance {n : Nat} : Encode (Fin (n + 1)) := ⟨n, fun k => thermometer n k.val⟩

instance {α β : Type} [Encode α] [Encode β] : Encode (α × β) :=
  ⟨width α + width β, fun (a, b) => encode a ++ encode b⟩

instance {α : Type} [Encode α] : Encode (Option α) :=
  ⟨1 + width α, fun
    | some a => 1 :: encode a
    | none => 0 :: (List.range (width α)).map fun _ => 0⟩

/-- Encode a record through a projection to a type that already has an encoding. -/
@[instance_reducible] def via {α β : Type} [Encode β] (f : α → β) : Encode α :=
  ⟨width β, fun a => encode (f a)⟩

/-- Every encoding in `xs` has the declared width. -/
def widthOK {α : Type} [Encode α] (xs : List α) : Bool :=
  xs.all fun x => (encode x).length == width α

end Encode

end IxAIDecide
