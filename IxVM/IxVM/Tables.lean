import IxVM.Field
import Aiur.Library.U8

/-! The checked IxVM program's tables, from the table generator
(`Aiur.Library.U8.tables`): the byte tables of the module `UInt8`, with their
elaborated row types and their rows over `F`. The test suite
`ixvm-source` checks that they are the native preparation's. -/

namespace IxVM
open Aiur.Generic

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

end IxVM
