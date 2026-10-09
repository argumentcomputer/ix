import Compilatrix.Own.Plain.Semantics

namespace CompilatrixTests.Cfg.Rc.DecrementControls
open Compilatrix Compilatrix.Own
def ctor : Fir.CtorInfo := { key := .src 901, tag := 0, nobj := 1, fieldKinds := [.shared] }
def body : Body := { ctor, fields := [.lit (.nat 7)] }
def heap (refs : Nat) : Heap := { cells := #[.live refs .dyn body] }
def env : Env := (Src.NatMap.ofList [(0, RVal.loc 0), (1, RVal.loc 0)])
def expect (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError label)
  IO.println ("PASS " ++ label)
def tests : IO Unit := do
  expect "one of two aliased tokens decremented" (decide
    (Plain.evalAction env (heap 2) (.dec 0) = .ok (heap 1)))
  expect "stale lexical entry remains after final release" (decide
    (Plain.evalAction env (heap 1) (.dec 0) = .ok { cells := #[.dead] }) &&
    decide (env.get? 0 = some (.loc 0)))
  expect "held caller token retains exact count" (decide
    (Plain.evalAction env (heap 3) (.dec 0) = .ok (heap 2)))
  expect "missing variable refuses" (decide
    (Plain.evalAction env (heap 1) (.dec 2) = .stuck))
  expect "dead-cell stale variable refuses" (decide
    (Plain.evalAction env { cells := #[.dead] } (.dec 0) = .stuck))
  expect "alias multiplicity not deduplicated" (Rc.refsIn 0 [.loc 0, .loc 0] == 2)
end CompilatrixTests.Cfg.Rc.DecrementControls
