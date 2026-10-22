import Aiur.Frontend
import Aiur.Eval
import Mathlib.Algebra.Field.Rat

open Aiur

/-- Three maps share the same input trace. Rows are generated outside Aiur. -/
def tableProgram : Program Nat := aiur% "
table bits: (Field, Field) {
    (0, 0), (0, 1), (1, 0), (1, 1),
}
table sums: Field { 0, 1, 1, 2, }
table products: Field { 0, 0, 0, 1, }
table xors: Field { 0, 1, 1, 0, }
map bit_add(a: Field, b: Field) -> Field = bits => sums;
map bit_mul(a: Field, b: Field) -> Field = bits => products;
map bit_xor(a: Field, b: Field) -> Field = bits => xors;
fn combine(a: Field, b: Field) -> (Field, Field, Field) {
    (bit_add(a, b), bit_mul(a, b), bit_xor(a, b))
}
"

#eval eval (tableProgram.toField Rat) "combine" [1, 1]
-- .ok (.tuple [2, 1, 0])
#eval eval (tableProgram.toField Rat) "bit_xor" [1, 0]
-- .ok 1
#eval eval (tableProgram.toField Rat) "bit_add" [2, 0]
-- .error (.missingMapInput "bit_add")

/-- Generate shared inputs and two output traces directly in Lean. -/
def generatedMaps (bound : Nat) : Program Nat :=
  let pairs := (List.range bound).flatMap fun a => (List.range bound).map fun b => (a, b)
  {
    functions := []
    tables := [
      { name := "inputs", rowType := .tuple [.field, .field]
        rows := pairs.map fun (a, b) => .tuple [.field a, .field b] },
      { name := "sums", rowType := .field
        rows := pairs.map fun (a, b) => .field (a + b) },
      { name := "products", rowType := .field
        rows := pairs.map fun (a, b) => .field (a * b) }
    ]
    maps := [
      ⟨"add", [("a", .field), ("b", .field)], .field, "inputs", "sums"⟩,
      ⟨"mul", [("a", .field), ("b", .field)], .field, "inputs", "products"⟩
    ]
  }

#eval eval ((generatedMaps 4).toField Rat) "add" [2, 3]
-- .ok 5
#eval eval ((generatedMaps 4).toField Rat) "mul" [2, 3]
-- .ok 6
