import IxCC.Own.Plain.Check

/-! Focused canonical-transfer controls. Expected action sequences are written
independently; mutants exercise the safety obligations the later refinement
must discharge. These checks do not stand in for a Fir/RC differential suite. -/

namespace IxCCTests.Own.Plain.PlainTests

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var)

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

example : initialActions (lowerCode [0] [] (.ret (.var 0))) = [] := by decide +kernel
example : initialActions (lowerCode [0, 1] [] (.tcall 0 [.var 0, .var 1])) = [] := by decide +kernel
example : initialActions (lowerCode [0, 1] [] (.tcall 0 [.var 0, .var 0])) = [.inc 0 1, .dec 1] := by decide +kernel

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
-- zero and moves parameter one directly into the tail jump without inc/dec.
private def joinActions : Code → Option (List Var × List Action × List Action)
  | .jp _ _ captured _ body k => some (captured, initialActions body, initialActions k)
  | _ => none

example : joinActions (lowerCode [0] [] recursiveJoin) =
    some ([0], [], [.inc 0 1]) := by decide +kernel
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

-- Contract-aware admission and automatic RC policy selection (`selectRcPolicy`).
example : contractFunDomain { ordinary with result := Ixon.V3.ValueContract.unique } = true := by decide +kernel
example : contractFunDomain { ordinary with contracts := [Ixon.V3.BinderContract.linear] } = true := by decide +kernel
example : contractFunDomain { ordinary with contracts := [Ixon.V3.BinderContract.erased] } = true := by decide +kernel
example : contractFunDomain { ordinary with contracts := [Ixon.V3.BinderContract.affine] } = true := by decide +kernel
example : checkContractPlainMap (twoFunctions { ordinary with contracts := [.linear] })
    (Program.canonical (twoFunctions { ordinary with contracts := [.linear] })).bodies = true := by decide +kernel

private def heapFun (contracts : List Ixon.V3.BinderContract)
    (letContracts : List (Var × Ixon.V3.LetContract) := []) : Fir.Fun :=
  { key := .const 901 [], params := [(0, .tobj)], body := construct oneField,
    contracts, letContracts }

private def singleProgram (f : Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofDense [f], size := 1, exports := [0], ctors := [], known := default }

-- Scalar functions select `.zeroRc`.
example : selectRcPolicy (singleProgram ordinary) = .zeroRc := by decide +kernel

-- Heap-allocating functions with `.many` or omitted contracts select `.plainRc`.
example : selectRcPolicy (singleProgram (heapFun [.many])) = .plainRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [])) = .plainRc := by decide +kernel

-- Heap-allocating functions whose contracts allow zero-RC (`0`, `1`, `&`, `~`, `!`, `let borrow`) select `.zeroRc`.
example : selectRcPolicy (singleProgram (heapFun [.erased])) = .zeroRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [.linear])) = .zeroRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [.affine])) = .zeroRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [{ value := .localShared }])) = .zeroRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [{ value := .unique }])) = .zeroRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [.linear] [(1, Ixon.V3.LetContract.borrow true)])) = .zeroRc := by decide +kernel
example : selectRcPolicy (singleProgram (heapFun [.linear] [(1, Ixon.V3.LetContract.lean true)])) = .plainRc := by decide +kernel

/-! ## Comprehensive Usage, Ownership, Locality, and Borrow Fixture Patterns -/

private def nilKey : Key.CtorKey := .src 910
private def consKey : Key.CtorKey := .src 911
private def natZeroKey : Key.CtorKey := .src 912
private def natSuccKey : Key.CtorKey := .src 913

private def nilInfo : Fir.CtorInfo :=
  { key := nilKey, tag := 0, nobj := 0, fieldKinds := [] }

private def consInfo : Fir.CtorInfo :=
  { key := consKey, tag := 1, nobj := 2, fieldKinds := [.shared, .shared] }

private def listKnown : Lam.Known :=
  { natZero := some natZeroKey, natSucc := some natSuccKey }

private def listCtors : List Lam.CtorInfo :=
  [ { key := nilKey, tag := 0, arity := 0 },
    { key := consKey, tag := 1, arity := 2 },
    { key := natZeroKey, tag := 0, arity := 0 },
    { key := natSuccKey, tag := 1, arity := 1 } ]

private def listProgram (funs : List Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofDense funs,
    size := funs.length,
    exports := List.range funs.length,
    ctors := listCtors,
    known := listKnown }

-- 1. `0` (`Uses.erased`): scalar erased ghost parameter vs heap list traversal `len {0 α} (xs : List α)`.
private def scalarErasedFun : Fir.Fun :=
  { key := .const 920 [],
    params := [(0, .tobj), (1, .tobj)],
    body := .case 1
      [ .mk natZeroKey (.ret (.lit (.nat 1))),
        .mk natSuccKey (.bind 2 (.proj 1 natSuccKey 0) (.ret (.var 2))) ]
      none,
    contracts := [.erased, .many] }

private def lenBody : Fir.Code :=
  .case 1
    [ .mk nilKey (.ret (.lit (.nat 0))),
      .mk consKey
        (.bind 2 (.proj 1 consKey 1)
          (.bind 3 (.call 0 [.erased, .var 2])
            (.bind 4 (.prim .natAdd [.var 3, .lit (.nat 1)])
              (.ret (.var 4))))) ]
    none

private def lenErasedManyFun : Fir.Fun :=
  { key := .const 921 [],
    params := [(0, .tobj), (1, .tobj)],
    body := lenBody,
    contracts := [.erased, .many] }

private def lenErasedBorrowedFun : Fir.Fun :=
  { lenErasedManyFun with
    key := .const 922 [],
    contracts := [.erased, { value := .localShared }] }

-- Scalar `Nat.succ` peeling does not touch the heap, so `0` + `.many` on scalars is `.zeroRc`.
example : codeAllocsOrProjs listKnown scalarErasedFun.body = false := by decide +kernel
example : funDomain scalarErasedFun = false := by decide +kernel
example : contractFunDomain scalarErasedFun = true := by decide +kernel
example : contractProgramDomain (listProgram [scalarErasedFun]) = true := by decide +kernel
example : checkContractPlainMap (listProgram [scalarErasedFun])
    (Program.canonical (listProgram [scalarErasedFun])).bodies = true := by decide +kernel
example : selectRcPolicy (listProgram [scalarErasedFun]) = .zeroRc := by decide +kernel

-- `len {0 α} (xs : List α)` projects `consKey` on an unannotated `.many` list parameter -> `.plainRc`,
-- whereas `len {0 α} (~ xs : List α)` discharges both parameters -> `.zeroRc`.
example : codeAllocsOrProjs listKnown lenBody = true := by decide +kernel
example : funDomain lenErasedManyFun = false := by decide +kernel
example : contractFunDomain lenErasedManyFun = true := by decide +kernel
example : contractProgramDomain (listProgram [lenErasedManyFun]) = true := by decide +kernel
example : checkContractPlainMap (listProgram [lenErasedManyFun])
    (Program.canonical (listProgram [lenErasedManyFun])).bodies = true := by decide +kernel
example : selectRcPolicy (listProgram [lenErasedManyFun]) = .plainRc := by decide +kernel
example : contractProgramDomain (listProgram [lenErasedBorrowedFun]) = true := by decide +kernel
example : selectRcPolicy (listProgram [lenErasedBorrowedFun]) = .zeroRc := by decide +kernel

-- 2. `1` (`Uses.linear`): linear list consumer / constructor (`linCons (1 xs : List Nat)` -> `.zeroRc`).
private def linConsBody : Fir.Code :=
  .bind 1 (.arg (.lit (.nat 42)))
    (.bind 2 (.ctor consInfo [.var 1, .var 0])
      (.ret (.var 2)))

private def linConsFun : Fir.Fun :=
  { key := .const 923 [],
    params := [(0, .tobj)],
    body := linConsBody,
    contracts := [.linear] }

private def manyConsFun : Fir.Fun :=
  { linConsFun with key := .const 924 [], contracts := [.many] }

example : codeAllocsOrProjs listKnown linConsBody = true := by decide +kernel
example : funDomain linConsFun = false := by decide +kernel
example : contractFunDomain linConsFun = true := by decide +kernel
example : contractProgramDomain (listProgram [linConsFun]) = true := by decide +kernel
example : checkContractPlainMap (listProgram [linConsFun])
    (Program.canonical (listProgram [linConsFun])).bodies = true := by decide +kernel
example : selectRcPolicy (listProgram [linConsFun]) = .zeroRc := by decide +kernel
example : selectRcPolicy (listProgram [manyConsFun]) = .plainRc := by decide +kernel

-- 3. `&` (`Uses.affine`): affine list consumer with early exit branch (`affHead (& xs : List Nat)` -> `.zeroRc`).
private def affHeadBody : Fir.Code :=
  .case 0
    [ .mk nilKey (.ret (.lit (.nat 0))),
      .mk consKey (.bind 1 (.proj 0 consKey 0) (.ret (.var 1))) ]
    none

private def affHeadFun : Fir.Fun :=
  { key := .const 925 [],
    params := [(0, .tobj)],
    body := affHeadBody,
    contracts := [.affine] }

private def manyHeadFun : Fir.Fun :=
  { affHeadFun with key := .const 926 [], contracts := [.many] }

example : codeAllocsOrProjs listKnown affHeadBody = true := by decide +kernel
example : funDomain affHeadFun = false := by decide +kernel
example : contractFunDomain affHeadFun = true := by decide +kernel
example : contractProgramDomain (listProgram [affHeadFun]) = true := by decide +kernel
example : checkContractPlainMap (listProgram [affHeadFun])
    (Program.canonical (listProgram [affHeadFun])).bodies = true := by decide +kernel
example : selectRcPolicy (listProgram [affHeadFun]) = .zeroRc := by decide +kernel
example : selectRcPolicy (listProgram [manyHeadFun]) = .plainRc := by decide +kernel

-- 4. `~` (`Locality.local`) & `let borrow` (`LetKind.borrowShared`):
-- borrowed list length / lookup (`borrowLen (~ xs : List Nat)` with `let borrow (~ v) := xs` -> `.zeroRc`).
private def borrowLenBody : Fir.Code :=
  .bind 1 (.arg (.var 0))
    (.jp 0 [2, 3] true
      (.case 2
        [ .mk nilKey (.ret (.var 3)),
          .mk consKey
            (.bind 4 (.proj 2 consKey 1)
              (.bind 5 (.prim .natAdd [.var 3, .lit (.nat 1)])
                (.jmp 0 [.var 4, .var 5]))) ]
        none)
      (.jmp 0 [.var 1, .lit (.nat 0)]))

private def borrowLenFun : Fir.Fun :=
  { key := .const 927 [],
    params := [(0, .tobj)],
    body := borrowLenBody,
    result := .localShared,
    contracts := [{ value := .localShared }],
    letContracts := [(1, Ixon.V3.LetContract.borrow true)] }

private def borrowLenUnannotatedLetFun : Fir.Fun :=
  { borrowLenFun with
    key := .const 928 [],
    letContracts := [(1, Ixon.V3.LetContract.lean true)] }

example : codeAllocsOrProjs listKnown borrowLenBody = true := by decide +kernel
example : funDomain borrowLenFun = false := by decide +kernel
example : contractFunDomain borrowLenFun = true := by decide +kernel
example : contractProgramDomain (listProgram [borrowLenFun]) = true := by decide +kernel
example : checkContractPlainMap (listProgram [borrowLenFun])
    (Program.canonical (listProgram [borrowLenFun])).bodies = true := by decide +kernel
example : selectRcPolicy (listProgram [borrowLenFun]) = .zeroRc := by decide +kernel
example : selectRcPolicy (listProgram [borrowLenUnannotatedLetFun]) = .plainRc := by decide +kernel

-- 5. `!` (`Owned.unique`): unique in-place list reversal / accumulator
-- (`revUnique (! xs : List Nat) (! acc : List Nat) : ! List Nat` -> `.zeroRc`)
-- contrasted against `.many` (`revMany` -> `.plainRc`) and half-annotated (`revHalfUnique` -> `.plainRc`).
private def revAccBody : Fir.Code :=
  .case 0
    [ .mk nilKey (.ret (.var 1)),
      .mk consKey
        (.bind 2 (.proj 0 consKey 0)
          (.bind 3 (.proj 0 consKey 1)
            (.bind 4 (.ctor consInfo [.var 2, .var 1])
              (.tcall 0 [.var 3, .var 4])))) ]
    none

private def revUniqueFun : Fir.Fun :=
  { key := .const 929 [],
    params := [(0, .tobj), (1, .tobj)],
    body := revAccBody,
    result := .unique,
    contracts := [{ value := .unique }, { value := .unique }] }

private def revManyFun : Fir.Fun :=
  { key := .const 930 [],
    params := [(0, .tobj), (1, .tobj)],
    body := revAccBody,
    result := .shared,
    contracts := [.many, .many] }

private def revHalfUniqueFun : Fir.Fun :=
  { key := .const 931 [],
    params := [(0, .tobj), (1, .tobj)],
    body := revAccBody,
    result := .unique,
    contracts := [.many, { value := .unique }] }

example : codeAllocsOrProjs listKnown revAccBody = true := by decide +kernel
example : funDomain revUniqueFun = false := by decide +kernel
example : funDomain revManyFun = true := by decide +kernel
example : contractFunDomain revUniqueFun = true := by decide +kernel
example : contractFunDomain revManyFun = true := by decide +kernel
example : contractFunDomain revHalfUniqueFun = true := by decide +kernel
example : contractProgramDomain (listProgram [revUniqueFun]) = true := by decide +kernel
example : contractProgramDomain (listProgram [revManyFun]) = true := by decide +kernel
example : contractProgramDomain (listProgram [revHalfUniqueFun]) = true := by decide +kernel
example : checkContractPlainMap (listProgram [revUniqueFun])
    (Program.canonical (listProgram [revUniqueFun])).bodies = true := by decide +kernel
example : selectRcPolicy (listProgram [revUniqueFun]) = .zeroRc := by decide +kernel
example : selectRcPolicy (listProgram [revManyFun]) = .plainRc := by decide +kernel
example : selectRcPolicy (listProgram [revHalfUniqueFun]) = .plainRc := by decide +kernel

-- 6. Multi-function program combining all zero-RC annotations (`0`, `1`, `&`, `~`, `let borrow`, `!`)
-- selects `.zeroRc`, and flips to `.plainRc` as soon as an unannotated `.many` heap function is included.
private def allZeroRcProgram : Fir.Program :=
  listProgram [lenErasedBorrowedFun, linConsFun, affHeadFun, borrowLenFun, revUniqueFun, scalarErasedFun]

private def mixedRcProgram : Fir.Program :=
  listProgram [lenErasedBorrowedFun, linConsFun, affHeadFun, borrowLenFun, revUniqueFun, revManyFun]

example : contractProgramDomain allZeroRcProgram = true := by decide +kernel
example : checkContractPlainMap allZeroRcProgram (Program.canonical allZeroRcProgram).bodies = true := by decide +kernel
example : selectRcPolicy allZeroRcProgram = .zeroRc := by decide +kernel

example : contractProgramDomain mixedRcProgram = true := by decide +kernel
example : checkContractPlainMap mixedRcProgram (Program.canonical mixedRcProgram).bodies = true := by decide +kernel
example : selectRcPolicy mixedRcProgram = .plainRc := by decide +kernel

-- 7. Static immediate (`imm`) RC elision: variables bound by `.prim`, fieldless `.ctor` (`arity == 0`),
-- immediate `.arg`, `.prim` operands, and `.proj` of immediate parents emit zero `.inc` or `.dec` actions.
private def immElisionCode : Fir.Code :=
  .bind 1 (.prim .natAdd [.var 0, .lit (.nat 1)])
    (.bind 2 (.ctor nilInfo [])
      (.bind 3 (.arg (.var 1))
        (.bind 4 (.proj 1 natSuccKey 0)
          (.bind 5 (.ctor consInfo [.var 4, .var 2])
            (.ret (.var 5))))))

example : lowerCode [0, 9] [] immElisionCode =
    .bind 1 (.prim .natAdd [.var 0, .lit (.nat 1)])
      (.bind 2 (.ctor nilInfo [])
        (.bind 3 (.arg (.var 1))
          (.bind 4 (.proj 1 natSuccKey 0)
            (.bind 5 (.ctor consInfo [.var 4, .var 2])
              (.act (.dec 9) (.ret (.var 5))))))) := rfl
example : checkBody [] [0, 9] immElisionCode (lowerCode [0, 9] [] immElisionCode) = true := by decide +kernel

end IxCCTests.Own.Plain.PlainTests
