import IxCC.Cfg.Rc.Run
import IxCC.Cfg.Rc.Scoped
import IxCC.Own.Plain.Program
import IxCC.Own.Plain.Semantics

/-! Bounded compiled controls for actual intercepted Cfg execution. Expected
heaps and values are independent literals, not results from either evaluator. -/
namespace IxCCTests.Cfg.Rc.Runtime
open IxCC IxCC.Cfg.Rc
open IxCC.Cfg (Instr)

private def info : Fir.CtorInfo :=
  { key := .src 940, tag := 0, nobj := 1, fieldKinds := [.shared] }

private def initial : Own.Heap :=
  { cells := #[.live 1 .dyn {ctor := info, fields := [.lit (.nat 7)]}] }

private def source (body : Fir.Code) (vars : Nat) : Fir.Program :=
  { funs := Src.NatMap.ofDense [
      { key := .const 941 [], params := [(0, .tobj)], body, vars },
      { key := .const 942 [], params := [(0, .tobj)], vars := 1, body := .ret (.var 0) }]
    size := 2, exports := [0], ctors := [], known := {} }

private def check (name : String) (body : Fir.Code) (vars : Nat)
    (expected : Sem.Result (Own.RVal × Own.Heap)) : IO Unit := do
  let F := source body vars
  let plain := Own.Plain.Program.canonical F
  let some candidate := generate F plain.bodies
    | throw (IO.userError s!"{name}: generation failed")
  unless checkScopedProgram F plain.bodies candidate do
    throw (IO.userError s!"{name}: scoped gate rejected fixture")
  let actual := run candidate 32 0 [.loc 0] initial
  unless decide (actual = expected) do
    throw (IO.userError s!"{name}: Cfg expected {repr expected}, got {repr actual}")
  let abstract := Own.Plain.evalCall plain 32 0 [.loc 0] initial
  unless decide (abstract = expected) do
    throw (IO.userError s!"{name}: Plain expected {repr expected}, got {repr abstract}")
  for clock in [:4] do
    if decide (Own.Plain.evalCall plain clock 0 [.loc 0] initial = .timeout) then
      unless decide (run candidate clock 0 [.loc 0] initial = .timeout) do
        throw (IO.userError s!"{name}: timeout mismatch at clock {clock}")

def suite : IO Unit := do
  check "shared call and result transfer" (.bind 1 (.call 1 [.var 0]) (.ret (.var 1))) 2
    (.ok (.loc 0, initial))
  check "join argument ownership transfer" (.jp 0 [1] false (.ret (.var 1)) (.jmp 0 [.var 0])) 2
    (.ok (.loc 0, initial))
  check "unused root final release" (.ret (.lit (.nat 42))) 1
    (.ok (.lit (.nat 42), {cells := #[.dead]}))
  check "trap" .trap 1 .trap
  IO.println "H3 runtime: 4 independent complete value/heap controls and bounded timeout controls passed"

end IxCCTests.Cfg.Rc.Runtime
