import Compilatrix.Own.Plain.Check

/-! Pin controls deliberately keep function bodies and scopes identical.
Only the primitive Boolean constructor's physical field count changes. -/

set_option autoImplicit false
namespace CompilatrixTests.Own.Plain.CheckedTests
open Compilatrix
open Own.Plain

private def body : Fir.Code := .ret (.var 0)
private def source (falseFields trueFields : Nat) : Fir.Program :=
  { funs := Src.NatMap.ofDense [{ key := .const 810 [], params := [(0, .tobj)], body }]
    size := 1, exports := [0]
    ctors := [{ key := .src 810, tag := 0, arity := falseFields },
      { key := .src 811, tag := 1, arity := trueFields }]
    known := { boolFalse := some (.src 810), boolTrue := some (.src 811) } }

example : checkPlainFunction (source 0 0) 0 (lowerCode [0] [] body) = true := by decide +kernel
example : checkFunction (source 1 0) 0 (lowerCode [0] [] body) = true := by decide +kernel
example : checkPlainFunction (source 1 0) 0 (lowerCode [0] [] body) = false := by decide +kernel
example : checkPlainFunction (source 0 1) 0 (lowerCode [0] [] body) = false := by decide +kernel
example : checkBoolPins { source 0 0 with known := default } = true := by decide +kernel

end CompilatrixTests.Own.Plain.CheckedTests
