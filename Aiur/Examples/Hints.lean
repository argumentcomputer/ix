import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

namespace AiurExamples.Hints

/-- A small preimage example: the witness is private to the function body. -/
def source : Program Nat := aiur% "
fn square_preimage(h: Field) -> () {
  let p = hint::<Field>(\"preimage\", h);
  let 0 = p * p - h;
  ()
}
"

def program := source.toField Rat

/-- The prover supplies a known preimage. The adapter checks its Aiur type. -/
def provider : HintProvider Rat program.enums :=
  HintProvider.checked program.enums fun channel key =>
    match channel, key with
    | "preimage", .field 49 => .ok (.field 7)
    | _, _ => .error .unavailable

#eval eval program "square_preimage" [49] (hints := provider)
-- Except.ok (Aiur.Value.tuple [])

example : EvalCall program "square_preimage" [49] (.tuple []) :=
  eval_spec (by decide +kernel : eval program "square_preimage" [49] 16 provider = .ok (.tuple []))

/-- A well-typed answer still has to satisfy the program's equations. -/
example : eval program "square_preimage" [49] 16
    (HintProvider.checked program.enums fun _ _ => .ok 8) = .error .patternMismatch := by
  decide +kernel

end AiurExamples.Hints
