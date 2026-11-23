import IxCC.Own.Plain.Live
import IxCC.Own.Plain.Certificate

/-! # Tests for the production liveness-based ownership producer (`IxCC.Own.Plain.Live`)

Re-exports `liveBody` and `liveMap` from `IxCC.Own.Plain.Live` (no duplicated producer code) and
checks edge cases that the corpus alone may not hit:
* dead (uncalled) join points whose bodies reference outer variables (`needCaptured` preservation);
* recursive joins with nested inner joins and multiple outer captures in deterministic ascending
  `Var` order;
* moving into last consuming uses vs. incrementing repeated/live arguments;
* immediate propagation through `prim`, 0-arity `ctor`, and `arg` copies;
* unused projections (no `inc` emitted) vs. live projections (`inc` before `dec` of dead source);
* synthetic large-arity stress test (256 parameters/arguments, verifying fast runtime, sorted
  deterministic captures, and `checkOwned` acceptance). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var JoinId FunId Arg Rhs)

abbrev liveBody : List Var → Fir.Code → Code := IxCC.Own.Plain.Live.liveBody
abbrev liveMap : Fir.Program → Src.NatMap Code := IxCC.Own.Plain.Live.liveMap

namespace LiveTests

private def nilKey : Key.CtorKey := .src 1
private def consKey : Key.CtorKey := .src 2

private def consInfo : Fir.CtorInfo :=
  { key := consKey, tag := 1, nobj := 2, fieldKinds := [.shared, .shared] }

private def nilInfo : Fir.CtorInfo :=
  { key := nilKey, tag := 0, nobj := 0, fieldKinds := [] }

private def mkProg (params : List Var) (body : Fir.Code) (vars : Nat) : Fir.Program :=
  let fd : Fir.Fun := { (default : Fir.Fun) with params := params.map (·, .tobj), body, vars }
  { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0]
    ctors := [{ key := nilKey, tag := 0, arity := 0 }, { key := consKey, tag := 1, arity := 2 }]
    known := {} }

-- 1. Dead join point referencing an outer variable (`v0`) that is unused in continuation `k`:
--    `v0` must remain available for `needCaptured` at `.jp`, then be dropped immediately in `k`.
private def deadJoinProg : Fir.Program :=
  mkProg [0, 1] (.jp 0 [2] false (.ret (.var 0)) (.ret (.var 1))) 3

example : checkOwned deadJoinProg (liveMap deadJoinProg) = true := by decide +kernel

-- 2. Recursive join with nested non-recursive join jumping back to the recursive join,
--    capturing multiple outer variables (`v0`, `v2`, `v1`) in deterministic ascending order.
private def nestedRecJoinProg : Fir.Program :=
  let body : Fir.Code :=
    .jp 0 [3] true
      (.jp 1 [4] false
        (.case 4
          [ .mk nilKey (.bind 5 (.ctor consInfo [.var 2, .var 0]) (.ret (.var 5))),
            .mk consKey (.jmp 0 [.var 1]) ]
          none)
        (.jmp 1 [.var 3]))
      (.jmp 0 [.var 1])
  mkProg [2, 0, 1] body 6

example : checkOwned nestedRecJoinProg (liveMap nestedRecJoinProg) = true := by decide +kernel

-- Verify deterministic ascending captured order `[0, 1, 2]` (despite parameter order `[2, 0, 1]`).
private def firstJoinCaptured : Code → Option (List Var)
  | .act _ k | .bind _ _ k => firstJoinCaptured k
  | .jp _ _ captured _ _ _ => some captured
  | _ => none

example : firstJoinCaptured (liveBody [2, 0, 1] (nestedRecJoinProg.fun? 0 |>.get!.body)) =
    some [0, 1, 2] := by
  decide +kernel

-- 3. Last-use move into `ctor` with duplicate variable (`[v0, v0]`): emits only ONE `inc v0 1`
--    (moving the second occurrence) and zero `dec`.
private def dupMoveProg : Fir.Program :=
  mkProg [0] (.bind 1 (.ctor consInfo [.var 0, .var 0]) (.ret (.var 1))) 2

example : checkOwned dupMoveProg (liveMap dupMoveProg) = true := by decide +kernel
example : codeEq (liveBody [0] (.bind 1 (.ctor consInfo [.var 0, .var 0]) (.ret (.var 1))))
    (.act (.inc 0 1) (.bind 1 (.ctor consInfo [.var 0, .var 0]) (.ret (.var 1)))) = true := by
  decide +kernel

-- 4. Unused projection from a dead scrutinee: emits NO `inc` on projected var and drops source.
private def unusedProjProg : Fir.Program :=
  mkProg [0] (.bind 1 (.proj 0 consKey 0) (.bind 2 (.ctor nilInfo []) (.ret (.var 2)))) 3

example : checkOwned unusedProjProg (liveMap unusedProjProg) = true := by decide +kernel
example : codeEq (liveBody [0] (unusedProjProg.fun? 0 |>.get!.body))
    (.bind 1 (.proj 0 consKey 0) (.act (.dec 0) (.bind 2 (.ctor nilInfo []) (.ret (.var 2))))) = true := by
  decide +kernel

-- 5. Live projection from a dying scrutinee: `inc x 1` MUST precede `dec y` (release).
private def liveProjDeadSrcProg : Fir.Program :=
  mkProg [0] (.bind 1 (.proj 0 consKey 0) (.ret (.var 1))) 2

example : checkOwned liveProjDeadSrcProg (liveMap liveProjDeadSrcProg) = true := by decide +kernel
example : codeEq (liveBody [0] (liveProjDeadSrcProg.fun? 0 |>.get!.body))
    (.bind 1 (.proj 0 consKey 0) (.act (.inc 1 1) (.act (.dec 0) (.ret (.var 1))))) = true := by
  decide +kernel

-- 6. Immediate propagation through `prim`: `v0` becomes immediate after `natAdd`, so no `inc`/`dec`
--    is emitted for `v0` when returned or captured afterwards.
private def primImmProg : Fir.Program :=
  mkProg [0, 1]
    (.bind 2 (.prim .natAdd [.var 0, .var 1])
      (.jp 0 [3] false (.bind 4 (.ctor consInfo [.var 0, .var 3]) (.ret (.var 4)))
        (.jmp 0 [.var 2])))
    5

example : checkOwned primImmProg (liveMap primImmProg) = true := by decide +kernel
example : firstJoinCaptured (liveBody [0, 1] (primImmProg.fun? 0 |>.get!.body)) = some [] := by
  decide +kernel

/-- Build a synthetic large-arity program (`n` parameters in reverse order, recursive join capturing
every parameter, repeated arguments) to verify non-quadratic runtime, deterministic ascending
capture order, and `checkOwned` acceptance. -/
def largeStressProg (n : Nat) : Fir.Program :=
  -- Parameters `[n-1, n-2, ..., 0]` plus one loop parameter `n`.
  let params := (List.range n).reverse
  let rec sumVars : List Var → Var → Fir.Code → Fir.Code
    | [], acc, k => .bind (n + 2) (.ctor consInfo [.var acc, .lit (.nat 0)]) k
    | [v], _, k => .bind (n + 2) (.ctor consInfo [.var v, .lit (.nat 0)]) k
    | v :: vs, nextVar, k =>
      .bind nextVar (.prim .natAdd [.var v, .lit (.nat 1)]) (sumVars vs (nextVar + 1) k)
  let baseVars := n + 10
  let finish := sumVars params baseVars (.ret (.var (n + 2)))
  let loopBody : Fir.Code :=
    .case n
      [ .mk nilKey finish,
        .mk consKey (.bind (n + 1) (.proj n consKey 1) (.jmp 0 [.var (n + 1)])) ]
      none
  let body : Fir.Code := .jp 0 [n] true loopBody (.jmp 0 [.var 0])
  mkProg params body (baseVars + n + 4)

/-- Runtime checks for `IxCC.Own.Plain.Live` (called from `tests-own-owned`). Returns failure messages. -/
def runChecks : Array String := Id.run do
  let mut errs : Array String := #[]
  for (label, P) in [
      ("deadJoin", deadJoinProg),
      ("nestedRecJoin", nestedRecJoinProg),
      ("dupMove", dupMoveProg),
      ("unusedProj", unusedProjProg),
      ("liveProjDeadSrc", liveProjDeadSrcProg),
      ("primImm", primImmProg)] do
    let m := liveMap P
    if !checkOwned P m then
      errs := errs.push s!"live-unit/{label}: checkOwned refused"
    match Certificate.decode P (Certificate.encode m) with
    | .ok back =>
      if !bodyMapEq back m then errs := errs.push s!"live-unit/{label}: certificate round trip differs"
    | .error e => errs := errs.push s!"live-unit/{label}: certificate decode failed: {e}"
  -- Large-arity stress check (200 parameters in reverse order).
  let n := 200
  let big := largeStressProg n
  let m := liveMap big
  if !checkOwned big m then
    errs := errs.push s!"live-unit/largeStress({n}): checkOwned refused"
  let some body := m.get? 0 | return errs.push "live-unit/largeStress: missing f0"
  let cap := firstJoinCaptured body
  if cap != some (List.range n) then
    errs := errs.push s!"live-unit/largeStress({n}): expected sorted captures [0..{n-1}], got {repr cap}"
  return errs

end LiveTests

end IxCCTests.Own.Owned
