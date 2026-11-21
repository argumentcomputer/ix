import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def source : Program Nat := aiur% "
enum Reply { Missing, Found((Field, Field)) }
fn read(reply: Reply) -> Field {
  let Reply::Found((0, value)) = reply;
  value
}
"

#eval eval (source.toField Rat) "read" [.construct "Reply" "Found" [.tuple [0, 8]]]
-- .ok 8

#eval eval (source.toField Rat) "read" [.construct "Reply" "Missing" []]
-- .error .patternMismatch

#eval (Circuit.compile (source.toField Rat)).isOk
-- true
