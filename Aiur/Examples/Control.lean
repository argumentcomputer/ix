import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

-- Labels are lexical; return always targets the current function.
def source : Generic.Program Nat := aiur% "
fn choose(x: Field) -> Field {
  let y = 'selected: {
    match x {
      0 => break 'selected 7,
      1 => return 20,
      _ => (),
    };
    9
  };
  y + 1
}
"

#eval do
  let s ← Generic.prepare (source.toField Rat)
  [0, 1, 2].mapM fun x => s.run "choose" [x]
-- Except.ok [(8, []), (20, []), (10, [])], with field-valued results.

#eval do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["choose"]
  let _ ← q.compile
  [0, 1, 2].mapM fun x => q.coreRun "choose" [x]
-- The same values and heaps after control lowering and circuit compilation.

#check Generic.ControlLower.function_correct
#check Generic.Specialized.native_entry_iff
#check Generic.Specialized.checker_heap_complete
#check Generic.Specialized.checker_heap_sound
#check Generic.Specialized.checkerMemo_acyclic_heap_sound
