import Compilatrix.Own.Plain.Check

set_option autoImplicit false
namespace CompilatrixTests.Own.Plain.CandidateTests
open Compilatrix
open Own.Plain

private def source : Fir.Program :=
  { funs := Src.NatMap.ofDense [
      { key := .const 820 [], params := [(0, .tobj)], body := .tcall 1 [.var 0] },
      { key := .const 821 [], params := [(0, .tobj)], body := .ret (.var 0) }]
    size := 2, exports := [0], ctors := [], known := default }

private def candidate := (Program.canonical source).bodies

example : checkPlainMap source candidate = true := by decide +kernel
-- The selected root stays identical; changing only its callee must fail.
example : checkPlainMap source (candidate.insert 1 .trap) = false := by decide +kernel
example : checkPlainMap source (candidate.erase 1) = false := by decide +kernel
example : checkPlainMap source (candidate.insert 2 .trap) = false := by decide +kernel
-- An empty node is extensionally empty but is outside this exact-image format.
example : bodyMapEq .leaf (.node none .leaf .leaf) = false := by decide +kernel

end CompilatrixTests.Own.Plain.CandidateTests
