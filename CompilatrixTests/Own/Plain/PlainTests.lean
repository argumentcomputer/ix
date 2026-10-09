import Compilatrix.Own.Plain.Check

/-! Focused canonical-transfer controls. Expected action sequences are written
independently; mutants exercise the safety obligations the later refinement
must discharge. These checks do not stand in for a Fir/RC differential suite. -/

namespace CompilatrixTests.Own.Plain.PlainTests

open Compilatrix Compilatrix.Own.Plain
open Compilatrix.Fir (Var)

private def initialActions : Code → List Action
  | .act a k => a :: initialActions k
  | _ => []

private def omitFirstAction : Code → Code
  | .act _ k => k
  | c => c

private def omitFirstDrop : Code → Code
  | .act (.dec _) k => k
  | .act a k => .act a (omitFirstDrop k)
  | .bind x r k => .bind x r (omitFirstDrop k)
  | c => c

private def aliasedCall : Fir.Code :=
  .bind 1 (.call 0 [.var 0, .var 0]) (.ret (.var 1))

example : initialActions (lowerCode [0] [] aliasedCall) = [.inc 0 1, .inc 0 1] := by decide +kernel
example : checkBody [(0, 2)] [0] aliasedCall (lowerCode [0] [] aliasedCall) = true := by decide +kernel
example : checkBody [(0, 2)] [0] aliasedCall (omitFirstAction (lowerCode [0] [] aliasedCall)) = false := by decide +kernel
example : checkBody [(0, 2)] [0] aliasedCall (omitFirstDrop (lowerCode [0] [] aliasedCall)) = false := by decide +kernel
example : checkBody [(0, 2)] [0] aliasedCall (.act (.dec 0) (lowerCode [0] [] aliasedCall)) = false := by decide +kernel

private def wrongArity : Fir.Code :=
  .bind 1 (.call 0 [.var 0]) (.ret (.var 1))
example : checkBody [(0, 2)] [0] wrongArity (lowerCode [0] [] wrongArity) = false := by decide +kernel

private def recursiveJoin : Fir.Code :=
  .jp 0 [1] true (.jmp 0 [.var 1]) (.jmp 0 [.var 0])

-- Declaration creates no new owned tokens. The recursive body keeps capture
-- zero, duplicates parameter one for transfer, then drops the old parameter.
private def joinActions : Code → Option (List Var × List Action × List Action)
  | .jp _ _ captured _ body k => some (captured, initialActions body, initialActions k)
  | _ => none

example : joinActions (lowerCode [0] [] recursiveJoin) =
    some ([0], [.inc 1 1, .dec 1], [.inc 0 1]) := by decide +kernel
example : checkBody [] [0] recursiveJoin (lowerCode [0] [] recursiveJoin) = true := by decide +kernel

private def loseCapture : Code → Code
  | .jp j ps _ rec body k => .jp j ps [] rec body k
  | c => c
example : checkBody [] [0] recursiveJoin (loseCapture (lowerCode [0] [] recursiveJoin)) = false := by decide +kernel

private def unknownJoin : Fir.Code := .jmp 7 [.var 0]
example : checkBody [] [0] unknownJoin (lowerCode [0] [] unknownJoin) = false := by decide +kernel

private def illegalSelf : Fir.Code :=
  .jp 0 [1] false (.jmp 0 [.var 1]) (.jmp 0 [.var 0])
example : checkBody [] [0] illegalSelf (lowerCode [0] [] illegalSelf) = false := by decide +kernel

private def projection : Fir.Code :=
  .bind 1 (.proj 0 (.src 700) 0) (.ret (.var 1))
private def omitProjectionDup : Code → Code
  | .bind x r (.act (.inc _ _) k) => .bind x r k
  | c => c

example : checkBody [] [0] projection (lowerCode [0] [] projection) = true := by decide +kernel
example : checkBody [] [0] projection (omitProjectionDup (lowerCode [0] [] projection)) = false := by decide +kernel

-- Explicit contract-domain declines, without changing the body or its scopes.
private def ordinary : Fir.Fun :=
  { key := .const 800 [], params := [(0, .tobj)], body := .ret (.var 0) }
example : funDomain ordinary = true := by decide +kernel
example : funDomain { ordinary with result := Ixon.V3.ValueContract.unique } = false := by decide +kernel
example : funDomain { ordinary with contracts := [Ixon.V3.BinderContract.linear] } = false := by decide +kernel

private def caller : Fir.Fun :=
  { ordinary with body := .tcall 1 [.var 0] }

private def twoFunctions (callee : Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofDense [caller, callee], size := 2,
    exports := [0], ctors := [], known := default }

-- Same body and same arity: only the transitive callee contract changes.
example : checkFunction (twoFunctions ordinary) 0
    (lowerCode [0] [] caller.body) = true := by decide +kernel
example : checkFunction (twoFunctions { ordinary with result := .unique }) 0
    (lowerCode [0] [] caller.body) = false := by decide +kernel
example : checkFunction (twoFunctions { ordinary with contracts := [.linear] }) 0
    (lowerCode [0] [] caller.body) = false := by decide +kernel
example : checkProgram (twoFunctions ordinary)
    [lowerCode [0] [] caller.body, lowerCode [0] [] ordinary.body] = true := by decide +kernel
example : checkProgram (twoFunctions ordinary)
    [lowerCode [0] [] caller.body] = false := by decide +kernel

private def oneField : Fir.CtorInfo :=
  { key := .src 900, tag := 0, nobj := 1, fieldKinds := [.shared] }
private def construct (c : Fir.CtorInfo) : Fir.Code :=
  .bind 1 (.ctor c [.var 0]) (.ret (.var 1))
example : checkBody [] [0] (construct oneField)
    (lowerCode [0] [] (construct oneField)) = true := by decide +kernel
example : checkBody [] [0] (construct { oneField with fieldKinds := [] })
    (lowerCode [0] [] (construct { oneField with fieldKinds := [] })) = false := by decide +kernel
example : checkBody [] [0] (construct { oneField with fieldKinds := [.unique false] })
    (lowerCode [0] [] (construct { oneField with fieldKinds := [.unique false] })) = false := by decide +kernel

end CompilatrixTests.Own.Plain.PlainTests
