import Aiur.Modules
import Aiur.Library.Carry
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurCarryTests

open Aiur

set_option maxRecDepth 10000

instance : Fact (Nat.Prime 1009) := ⟨by decide⟩

def declarations : Program Nat := aiur% "
table inputs: (Field,) {}
table bytes: Field {}
table parts: (Field, Field) {}
map sum_byte(sum: Field) -> Field = inputs => bytes;
map old_split_sum(sum: Field) -> (Field, Field) = inputs => parts;
fn split_sum(sum: Field) -> (Field, Field) {
    let byte = sum_byte(sum);
    (byte, (sum - byte) / 256)
}
"

def source : Program Nat :=
  let rows := Library.Carry.rows 256 768
  { declarations with tables := [
    ⟨"inputs", .tuple [.field], rows.map fun (n, _) => .tuple [.field n]⟩,
    ⟨"bytes", .field, rows.map fun (_, byte) => .field byte⟩,
    ⟨"parts", .tuple [.field, .field],
      (Library.Carry.fullRows Nat 256 768).map fun (_, byte, carry) =>
        .tuple [.field byte, .field carry]⟩] }

private def ensure (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def checkField (F : Type) [Field F] [DecidableEq F] : IO Unit := do
  let program := source.toField F
  let compiled ← get <| Optimized.compile program ["split_sum"]
  let some chip := compiled.system.findChip? "split_sum" |
    throw (IO.userError "missing split_sum chip")
  ensure "carry requires an extra column, equation, or lookup"
    (chip.numVars == 2 && chip.constraints.isEmpty && chip.sends.length == 1 &&
      chip.sends.all (·.result.words.length == 1) && chip.stats.maxLookupDegree == 1)
  for n in List.range 768 do
    let byte : F := (n % 256 : Nat)
    let carry : F := (n / 256 : Nat)
    ensure "field carry disagrees with natural carry" (((n : F) - byte) / 256 == carry)
    let root : Circuit.Message F := ⟨"split_sum", [.field n], .tuple [.field byte, .field carry]⟩
    let row : Circuit.Row F := ⟨"split_sum", [n, byte]⟩
    let _ ← get <| compiled.check ⟨[]⟩ root [row]
    let _ ← get <| compiled.checkMemo ⟨[]⟩ root [⟨row, 1⟩]
    let wrong := { root with result := .tuple [.field byte, .field (carry + 1)] }
    ensure "checker accepted a wrong reconstructed carry"
      (compiled.check ⟨[]⟩ wrong [row]).toOption.isNone
    ensure "checker accepted an incorrect table byte"
      (compiled.check ⟨[]⟩ root [⟨"split_sum", [n, byte + 1]⟩]).toOption.isNone
  for n in ([(-1), 768] : List F) do
    let root : Circuit.Message F := ⟨"split_sum", [.field n], .tuple [.field 0, .field (n / 256)]⟩
    let row : Circuit.Row F := ⟨"split_sum", [n, 0]⟩
    ensure "slim table admitted an input outside the original domain"
      ((compiled.check ⟨[]⟩ root [row]).toOption.isNone &&
        (compiled.checkMemo ⟨[]⟩ root [⟨row, 1⟩]).toOption.isNone)
  for n in [0, 255, 256, 511, 512, 767] do
    ensure "slim wrapper changed source evaluation"
      (eval program "split_sum" [.field n] == eval program "old_split_sum" [.field n])
  ensure "executor accepted a missing sum"
    (eval program "split_sum" [.field 768]).toOption.isNone

def run : IO Unit := do
  checkField Rat
  checkField (ZMod 1009)
  IO.println "Passed carry checks: all 768 rows over Rat and F1009, both checkers, wrong outputs, and domain boundaries."

#print axioms Library.Carry.recover
#print axioms Library.Carry.fullRows_iff
#print axioms Library.Carry.mapEntries_iff

end AiurCarryTests
