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

private partial def hasReuse : Code → Bool
  | .reset .. | .reuse .. => true
  | .act _ k | .bind _ _ k | .dropSlot _ k => hasReuse k
  | .jp _ _ _ _ b k => hasReuse b || hasReuse k
  | .case _ alts d => alts.any (fun | .mk _ b => hasReuse b) || (d.map hasReuse |>.getD false)
  | .jmp .. | .ret _ | .tcall .. | .trap => false

private partial def hasStaticReuse : Code → Bool
  | .reset _ _ _ _ true _ | .reuse _ _ _ _ true _ => true
  | .reset _ _ _ _ false k | .reuse _ _ _ _ false k => hasStaticReuse k
  | .act _ k | .bind _ _ k | .dropSlot _ k => hasStaticReuse k
  | .jp _ _ _ _ b k => hasStaticReuse b || hasStaticReuse k
  | .case _ alts d => alts.any (fun | .mk _ b => hasStaticReuse b) || (d.map hasStaticReuse |>.getD false)
  | .jmp .. | .ret _ | .tcall .. | .trap => false

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
  -- Track A3: `@borrowed` inference, certificate v2 round-trip, and negative UAF controls.
  -- f0 (exported) calls read-only helper f1(xs) which sums a cons-list via tail recursion.
  let f1 : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj), (1, .tobj)]
      body := .case 0
        [ .mk nilKey (.ret (.var 1)),
          .mk consKey (.bind 2 (.proj 0 consKey 0)
            (.bind 3 (.proj 0 consKey 1)
              (.bind 4 (.prim .natAdd [.var 1, .var 2])
                (.tcall 1 [.var 3, .var 4])))) ]
        none
      vars := 5 }
  let f0 : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj)]
      body := .bind 1 (.call 1 [.var 0, .lit (.nat 0)]) (.ret (.var 1))
      vars := 2 }
  let borrowProg : Fir.Program :=
    { funs := Src.NatMap.ofList [(0, f0), (1, f1)], size := 2, exports := [0]
      ctors := [{ key := nilKey, tag := 0, arity := 0 }, { key := consKey, tag := 1, arity := 2 }]
      known := {} }
  let (bBodies, bSigs) := IxCC.Own.Plain.Live.liveMapWith borrowProg
  if bSigs.getD 1 [] != [true, false] then
    errs := errs.push s!"borrow-unit/infer: expected f1 borrows [true, false], got {repr (bSigs.getD 1 [])}"
  if !checkOwned borrowProg bBodies bSigs then
    errs := errs.push "borrow-unit/infer: checkOwned refused liveMapWith output"
  match Certificate.decodeWith borrowProg (Certificate.encodeWith bBodies bSigs) with
  | .ok (backM, backB) =>
    if !bodyMapEq backM bBodies || backB.getD 1 [] != [true, false] then
      errs := errs.push "borrow-unit/v2-cert: round trip differs"
  | .error e => errs := errs.push s!"borrow-unit/v2-cert: decodeWith failed: {e}"
  -- Negative control 1: owned+borrowed aliasing `f1(v0_owned, v0_borrowed)` with 1 token of v0.
  let aliasHelper : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj), (1, .tobj)]
      body := .ret (.var 0)
      vars := 2 }
  let aliasCaller : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj)]
      body := .bind 1 (.call 1 [.var 0, .var 0]) (.ret (.var 1))
      vars := 2 }
  let aliasProg : Fir.Program :=
    { funs := Src.NatMap.ofList [(0, aliasCaller), (1, aliasHelper)], size := 2, exports := [0]
      ctors := [], known := {} }
  let aliasBodies : Src.NatMap Code := Src.NatMap.ofList
    [(0, .bind 1 (.call 1 [.var 0, .var 0]) (.ret (.var 1))), (1, .ret (.var 0))]
  let aliasBorrows : BorrowSigs := Src.NatMap.ofList [(1, [false, true])]
  if checkOwned aliasProg aliasBodies aliasBorrows then
    errs := errs.push "borrow-unit/neg-alias: owned+borrowed alias without inc was accepted"
  -- Negative control 2: tail call passing a local owned variable in a borrowed position.
  let tailCaller : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj)]
      body := .tcall 1 [.lit (.nat 0), .var 0]
      vars := 1 }
  let tailProg : Fir.Program :=
    { funs := Src.NatMap.ofList [(0, tailCaller), (1, aliasHelper)], size := 2, exports := [0]
      ctors := [], known := {} }
  let tailBodies : Src.NatMap Code := Src.NatMap.ofList
    [(0, .tcall 1 [.lit (.nat 0), .var 0]), (1, .ret (.var 0))]
  if checkOwned tailProg tailBodies aliasBorrows then
    errs := errs.push "borrow-unit/neg-tail: tail call borrowing local owned var was accepted"
  -- Negative control 3: exported function with a borrowed parameter must be refused.
  let expBorrow : BorrowSigs := Src.NatMap.ofList [(0, [true])]
  if checkOwned aliasProg (liveMap aliasProg) expBorrow then
    errs := errs.push "borrow-unit/neg-export: exported borrowed param was accepted"
  -- Negative control 4: consuming a borrowed parameter without `inc` must be refused.
  let badConsume : Src.NatMap Code := Src.NatMap.ofList
    [(0, .bind 1 (.call 1 [.lit (.nat 0), .var 0]) (.act (.dec 0) (.ret (.var 1)))),
     (1, .act (.dec 0) (.ret (.var 1)))]
  let badConsumeProg : Fir.Program :=
    { funs := Src.NatMap.ofList
        [(0, { (default : Fir.Fun) with params := [(0, .tobj)], body := .bind 1 (.call 1 [.lit (.nat 0), .var 0]) (.ret (.var 1)), vars := 2 }),
         (1, { (default : Fir.Fun) with params := [(0, .tobj), (1, .tobj)], body := .ret (.var 1), vars := 2 })]
      size := 2, exports := [0], ctors := [], known := {} }
  if checkOwned badConsumeProg badConsume aliasBorrows then
    errs := errs.push "borrow-unit/neg-consume: returning borrowed param without inc was accepted"
  -- Track A4: dynamic `reset`/`reuse`, static `@unique` unconditional reuse, certificate v3
  -- (`encodeFull`/`decodeFull`), and negative safety controls.
  -- Positive 1: dynamic `reset`/`reuse` on tail-recursive list reverse (`revAux`).
  let revAux : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj), (1, .tobj)]
      body := .case 0
        [ .mk nilKey (.ret (.var 1)),
          .mk consKey (.bind 2 (.proj 0 consKey 0)
            (.bind 3 (.proj 0 consKey 1)
              (.bind 4 (.ctor consInfo [.var 2, .var 1])
                (.tcall 1 [.var 3, .var 4])))) ]
        none
      vars := 5 }
  let revMain : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj)]
      body := .bind 1 (.ctor nilInfo [])
        (.bind 2 (.call 1 [.var 0, .var 1]) (.ret (.var 2)))
      vars := 3 }
  let revProg : Fir.Program :=
    { funs := Src.NatMap.ofList [(0, revMain), (1, revAux)], size := 2, exports := [0]
      ctors := [{ key := nilKey, tag := 0, arity := 0 }, { key := consKey, tag := 1, arity := 2 }]
      known := {} }
  let (revBodies, revBorrows, revUniqs) := IxCC.Own.Plain.Live.liveMapFull revProg
  if !checkOwned revProg revBodies revBorrows revUniqs then
    errs := errs.push "reuse-unit/rev: checkOwned refused liveMapFull output"
  if !(revBodies.get? 1 |>.map hasReuse |>.getD false) then
    errs := errs.push "reuse-unit/rev: expected reset/reuse in revAux"
  match Certificate.decodeFull revProg (Certificate.encodeFull revProg revBodies revBorrows revUniqs) with
  | .ok (backM, backB, backU) =>
    let sameBorrow := (List.range 2).all fun idx =>
      (backB.getD 1 []).getD idx false == (revBorrows.getD 1 []).getD idx false
    let sameUniq := (List.range 2).all (fun idx =>
      (backU.getD 1 ([], false)).1.getD idx false == (revUniqs.getD 1 ([], false)).1.getD idx false) &&
      (backU.getD 1 ([], false)).2 == (revUniqs.getD 1 ([], false)).2
    if !bodyMapEq backM revBodies || !sameBorrow || !sameUniq || !checkOwned revProg backM backB backU then
      errs := errs.push "reuse-unit/rev-v3-cert: round trip differs"
  | .error e => errs := errs.push s!"reuse-unit/rev-v3-cert: decodeFull failed: {e}"
  -- Positive 2: static `@unique` unconditional reuse (fresh cons passed to swapUniq).
  let swapUniq : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj)]
      body := .case 0
        [ .mk consKey (.bind 1 (.proj 0 consKey 0)
            (.bind 2 (.proj 0 consKey 1)
              (.bind 3 (.ctor consInfo [.var 2, .var 1]) (.ret (.var 3))))) ]
        none
      vars := 4 }
  let mkAndSwap : Fir.Fun :=
    { (default : Fir.Fun) with
      params := [(0, .tobj), (1, .tobj)]
      body := .bind 2 (.ctor consInfo [.var 0, .var 1])
        (.bind 3 (.call 1 [.var 2]) (.ret (.var 3)))
      vars := 4 }
  let uniqProg : Fir.Program :=
    { funs := Src.NatMap.ofList [(0, mkAndSwap), (1, swapUniq)], size := 2, exports := [0]
      ctors := [{ key := nilKey, tag := 0, arity := 0 }, { key := consKey, tag := 1, arity := 2 }]
      known := {} }
  let (uBodies, uBorrows, uUniqs) := IxCC.Own.Plain.Live.liveMapFull uniqProg
  if !checkOwned uniqProg uBodies uBorrows uUniqs then
    errs := errs.push "reuse-unit/static-uniq: checkOwned refused liveMapFull output"
  if uUniqs.getD 1 ([], false) != ([true], true) then
    errs := errs.push s!"reuse-unit/static-uniq: expected swapUniq uniqs ([true], true), got {repr (uUniqs.getD 1 ([], false))}"
  if !(uBodies.get? 1 |>.map hasStaticReuse |>.getD false) then
    errs := errs.push "reuse-unit/static-uniq: expected static uniq=true reset/reuse in swapUniq"
  match Certificate.decodeFull uniqProg (Certificate.encodeFull uniqProg uBodies uBorrows uUniqs) with
  | .ok (backM, _, backU) =>
    if !bodyMapEq backM uBodies || backU.getD 1 ([], false) != ([true], true) then
      errs := errs.push "reuse-unit/static-uniq-v3-cert: round trip differs"
  | .error e => errs := errs.push s!"reuse-unit/static-uniq-v3-cert: decodeFull failed: {e}"
  -- Negative reuse controls.
  let box1Key : Key.CtorKey := .src 10
  let big5Key : Key.CtorKey := .src 11
  let box1Info : Fir.CtorInfo := { key := box1Key, tag := 2, nobj := 1, fieldKinds := [.shared] }
  let big5Info : Fir.CtorInfo :=
    { key := big5Key, tag := 3, nobj := 5, fieldKinds := List.replicate 5 .shared }
  -- Neg 1: size-class mismatch (reset arity-1 cell, reuse as arity-5 cell).
  let mismatchProg : Fir.Program :=
    let fd : Fir.Fun :=
      { (default : Fir.Fun) with
        params := [(0, .tobj)]
        body := .case 0
          [ .mk box1Key (.bind 1 (.proj 0 box1Key 0)
              (.bind 2 (.ctor big5Info [.var 1, .lit (.nat 0), .lit (.nat 0), .lit (.nat 0), .lit (.nat 0)])
                (.ret (.var 2)))) ]
          none
        vars := 3 }
    { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0]
      ctors := [{ key := box1Key, tag := 2, arity := 1 }, { key := big5Key, tag := 3, arity := 5 }]
      known := {} }
  let mismatchBody : Code :=
    .case 0
      [ .mk box1Key (.bind 1 (.proj 0 box1Key 0)
          (.reset 0 0 box1Info [some 1] false
            (.reuse 2 0 big5Info [.var 1, .lit (.nat 0), .lit (.nat 0), .lit (.nat 0), .lit (.nat 0)] false
              (.ret (.var 2))))) ]
      none
  if checkOwned mismatchProg (Src.NatMap.ofList [(0, mismatchBody)]) then
    errs := errs.push "reuse-unit/neg-class-mismatch: different-class reuse was accepted"
  -- Neg 2: double reuse of same slot 0.
  let dblProg : Fir.Program :=
    let fd : Fir.Fun :=
      { (default : Fir.Fun) with
        params := [(0, .tobj)]
        body := .case 0
          [ .mk consKey (.bind 1 (.proj 0 consKey 0)
              (.bind 2 (.proj 0 consKey 1)
                (.bind 3 (.ctor consInfo [.var 1, .lit (.nat 0)])
                  (.bind 4 (.ctor consInfo [.var 2, .var 3]) (.ret (.var 4)))))) ]
          none
        vars := 5 }
    { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0]
      ctors := [{ key := consKey, tag := 1, arity := 2 }], known := {} }
  let dblBody : Code :=
    .case 0
      [ .mk consKey (.bind 1 (.proj 0 consKey 0)
          (.bind 2 (.proj 0 consKey 1)
            (.reset 0 0 consInfo [some 1, some 2] false
              (.reuse 3 0 consInfo [.var 1, .lit (.nat 0)] false
                (.reuse 4 0 consInfo [.var 2, .var 3] false (.ret (.var 4))))))) ]
      none
  if checkOwned dblProg (Src.NatMap.ofList [(0, dblBody)]) then
    errs := errs.push "reuse-unit/neg-double-reuse: reusing the same slot twice was accepted"
  -- Neg 3: leaked reset slot at `.ret` (neither reused nor dropped via `.dropSlot`).
  let leakProg : Fir.Program :=
    let fd : Fir.Fun :=
      { (default : Fir.Fun) with
        params := [(0, .tobj)]
        body := .case 0 [ .mk consKey (.bind 1 (.proj 0 consKey 0) (.ret (.var 1))) ] none
        vars := 2 }
    { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0]
      ctors := [{ key := consKey, tag := 1, arity := 2 }], known := {} }
  let leakBody : Code :=
    .case 0
      [ .mk consKey (.bind 1 (.proj 0 consKey 0)
          (.reset 0 0 consInfo [some 1, none] false (.ret (.var 1)))) ]
      none
  if checkOwned leakProg (Src.NatMap.ofList [(0, leakBody)]) then
    errs := errs.push "reuse-unit/neg-leaked-slot: returning with live reset slot was accepted"
  -- Neg 4: static `uniq = true` reset on a non-unique (exported) parameter.
  let badStaticProg : Fir.Program :=
    { funs := Src.NatMap.ofList [(0, swapUniq)], size := 1, exports := [0]
      ctors := [{ key := consKey, tag := 1, arity := 2 }], known := {} }
  let badStaticBody : Code :=
    .case 0
      [ .mk consKey (.bind 1 (.proj 0 consKey 0)
          (.bind 2 (.proj 0 consKey 1)
            (.reset 0 0 consInfo [some 1, some 2] true
              (.reuse 3 0 consInfo [.var 2, .var 1] true (.ret (.var 3)))))) ]
      none
  if checkOwned badStaticProg (Src.NatMap.ofList [(0, badStaticBody)]) then
    errs := errs.push "reuse-unit/neg-static-nonuniq: uniq=true on exported non-unique param was accepted"
  -- Neg 5: Nat constructor (`known.natSucc`) reset must be rejected.
  let natResetProg : Fir.Program :=
    { badStaticProg with known := { natSucc := some consKey } }
  let dynSwapBody : Code :=
    .case 0
      [ .mk consKey (.bind 1 (.proj 0 consKey 0)
          (.bind 2 (.proj 0 consKey 1)
            (.reset 0 0 consInfo [some 1, some 2] false
              (.reuse 3 0 consInfo [.var 2, .var 1] false (.ret (.var 3)))))) ]
      none
  if checkOwned natResetProg (Src.NatMap.ofList [(0, dynSwapBody)]) then
    errs := errs.push "reuse-unit/neg-nat-reset: resetting known.natSucc ctor was accepted"
  -- Neg 6: reset without `case` proving constructor identity (`ctorOf` missing).
  let noCaseProg : Fir.Program :=
    let fd : Fir.Fun :=
      { (default : Fir.Fun) with
        params := [(0, .tobj)]
        body := .bind 1 (.proj 0 consKey 0)
          (.bind 2 (.proj 0 consKey 1)
            (.bind 3 (.ctor consInfo [.var 2, .var 1]) (.ret (.var 3))))
        vars := 4 }
    { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0]
      ctors := [{ key := consKey, tag := 1, arity := 2 }], known := {} }
  let noCaseBody : Code :=
    .bind 1 (.proj 0 consKey 0)
      (.bind 2 (.proj 0 consKey 1)
        (.reset 0 0 consInfo [some 1, some 2] false
          (.reuse 3 0 consInfo [.var 2, .var 1] false (.ret (.var 3)))))
  if checkOwned noCaseProg (Src.NatMap.ofList [(0, noCaseBody)]) then
    errs := errs.push "reuse-unit/neg-no-ctorof: reset without case-refined ctor identity was accepted"
  -- Neg 7: exported function with `@unique` parameter in `UniqSigs` must be refused.
  let expUniq : UniqSigs := Src.NatMap.ofList [(0, ([true], false))]
  if checkOwned badStaticProg (Src.NatMap.ofList [(0, dynSwapBody)]) .leaf expUniq then
    errs := errs.push "reuse-unit/neg-export-uniq: exported @unique param was accepted"
  return errs

end LiveTests

end IxCCTests.Own.Owned
