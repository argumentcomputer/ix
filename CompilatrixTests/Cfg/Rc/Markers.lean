import Compilatrix.Cfg.Rc.Prefix

/-! Independent hostile-neighbor controls for the provisional marker gate.
These use explicit instruction encodings rather than the marker producer. -/
namespace CompilatrixTests.Cfg.Rc.Markers
open Compilatrix Compilatrix.Cfg.Rc
open Compilatrix.Cfg (Instr)

private def code : List Instr :=
  [.bind 8 (.fir (.call 3 [.var 0, .lit (.nat 1)])),
   .bind 9 (.fir (.call 4 [.var 1]))]

private def table : ActionTable :=
  (Src.NatMap.leaf.insert 9 (.dec 1)).insert 8 (.inc 0 1)

example : checkMarkers 3 8 code table = true := by decide
example : checkMarkers 3 8 code .leaf = false := by decide
example : checkMarkers 3 8 code (table.insert 10 (.dec 0)) = false := by decide
example : checkMarkers 3 8 code (table.insert 8 (.inc 0 2)) = false := by decide
example : checkMarkers 3 8 code (table.insert 9 (.dec 0)) = false := by decide
example : collect 3 8
    [.bind 8 (.fir (.call 3 [.var 0, .lit (.nat 1)])),
     .bind 8 (.fir (.call 4 [.var 1]))] = none := by decide
example : collect 3 8 [.bind 8 (.fir (.call 3 [.var 0]))] = none := by decide
example : collect 3 8 [.bind 7 (.fir (.call 4 [.var 0]))] = none := by decide
example : collect 3 8 [.bind 8 (.fir (.arg (.var 0)))] = none := by decide
example : collect 3 8 [.bind 0 (.fir (.call 5 [.var 0]))] = none := by decide
example : checkMarkers 3 8 [.bind 0 (.fir (.call 2 [.var 1]))] .leaf = true := by decide

end CompilatrixTests.Cfg.Rc.Markers
