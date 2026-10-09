import Compilatrix.Rt.Rc.Procs
import Compilatrix.Lir.Semantics
import Compilatrix.Own.Plain.Semantics

namespace CompilatrixTests.Cfg.Rc.IncrementControls
open Compilatrix Compilatrix.Rt.Rc.Procs

/-- Exact one-procedure program from the original Increment fixture. -/
private def incProgram : Lir.Program := { funcs := #[inc], main := 0 }
def expect (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError label)
  IO.println ("PASS " ++ label)
def memory (count : Lir.Word) : X86.Memory :=
  (X86.Memory.flat.write .w32 4096 197121).write .w32 4100 count
def heapFailure : Sem.Result (List Lir.Word × X86.Memory) → Bool
  | .resource .heap => true
  | _ => false
def successCount (expected : Lir.Word) : Sem.Result (List Lir.Word × X86.Memory) → Bool
  | .ok (values, mem) => values.isEmpty && mem.read .w32 4100 == expected && mem.read .w32 4096 == 197121
  | _ => false
def tests : IO Unit := do
  expect "actual immediate inc leaves memory" (successCount 37 (Lir.eval incProgram 0 [1] (memory 37) 64))
  expect "actual unique inc produces physical count1" (successCount 1 (Lir.eval incProgram 0 [4096] (memory 0) 64))
  expect "actual max-minus-one increments to max" (successCount 2147483647
    (Lir.eval incProgram 0 [4096] (memory 2147483646) 64))
  expect "actual maxCount refuses with heap resource" (heapFailure
    (Lir.eval incProgram 0 [4096] (memory 2147483647) 64))
  let ctor : Fir.CtorInfo := { key := .src 902, tag := 0, nobj := 1, fieldKinds := [.shared] }
  let body : Own.Body := { ctor, fields := [.lit (.nat 7)] }
  let H : Own.Heap := { cells := #[.live 2147483648 .dyn body] }
  let env : Own.Env := Src.NatMap.ofList [(0, .loc 0)]
  expect "source unbounded count still increments at target limit" (decide
    (Own.Plain.evalAction env H (.inc 0 1) = .ok {cells := #[.live 2147483649 .dyn body]}))
  expect "carried duplicate counts separately from original live root"
    (Own.Rc.refsIn 0 ([Own.RVal.loc 0] ++ [.loc 0]) == 2)
end CompilatrixTests.Cfg.Rc.IncrementControls
