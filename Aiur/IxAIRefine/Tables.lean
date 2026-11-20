import IxAIStep
import Aiur.Library.U8

/-! The `Fixed` program's tables, from the table generator (`Aiur.Library.U8.tables`): the
byte tables of the module `UInt8`, with their elaborated row types and their rows over `F`.
`IxAIRefine.Check` checks that they are the native preparation's. -/

namespace IxAIStep.Fixed
open Aiur.Generic

abbrev F := IxAIAiur.F

/-- The elaborated row types of the byte tables, in the generator's order:
`UInt8::U8` is the opaque alias of `Field`, and `Parts4`, `Parts7` of
`(Field, Field)`. -/
def tableRowTypes : List Ty :=
  [.tuple [.field], .field, .array .field 8, .tuple [.field, .field], .tuple [], .field,
    .tuple [.field, .field], .tuple [.field, .field], .tuple [.field, .field],
    .tuple [.field, .field], .tuple [.field, .field], .tuple [.field], .field]

/-- The prepared program's tables. -/
def genericTables : List (Aiur.Generic.Table F) :=
  (Aiur.Library.U8.tables.zip tableRowTypes).map fun (t, rowType) =>
    { name := "UInt8::" ++ t.name, rowType, rows := t.rows.map (Aiur.Generic.Expr.map Nat.cast) }

end IxAIStep.Fixed
