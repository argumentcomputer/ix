import IxCC.Anf.Defun
import IxCC.Anf.Defun.Flow
import IxCC.Anf.Defun.Narrow
import IxCC.Anf.DeadParam
import IxCC.Anf.Pipeline.Closures
import IxCC.Recheck.Json
import IxCC.Fir.Lower
import IxCCTests.Anf.Defun

/-! # Tests for Wave 1 Tracks C1+C2: known-dispatch shrink, P9 flow narrowing, P5 dead-param stripping

Covers:
1. Post-P8 known-dispatch shrink (`Walk.Fires.knownDispatch > 0`, dead-`con`
   elimination, and `Prune` removing the dead dispatcher + lifted lambdas).
2. P9 flow analysis (`Flow.analyse`) and dispatch narrowing (`Narrow.run`):
   - multi-closure program with 6 closure keys where sites only receive 1–2 keys;
   - no default arms (`Rt.checkSwitches`-compatible), `Fir.lower` accepts;
   - dishonest / wrong / out-of-bounds certificates fall back safely to `P` unchanged.
3. P5 erased/dead-parameter stripping (`DeadParam.run`):
   - 8-parameter helper with 4 erased/unused slots (`StateT.bind` shape) shrinks
     to a 4-parameter worker (`≤ 7` tail-call register limit);
   - transitive dead parameters over 2 rounds;
   - all-dead parameters keep ≥ 1 parameter; roots and dispatchers stay untouched.
4. `PostCert` + `Recheck.CertJson.mid` / `mid?` round-trip and plain omission. -/

namespace IxCCTests.Anf.ClosuresOpt

open IxCC.Anf
open IxCCTests.Src (Assert expect)
open IxCCTests.Anf (runAnf anfOutcome)
open IxCCTests.Anf.Defun (prog gd b x lit add mul fn checkOutput)

private def isDisp (gd : GDef) : Bool :=
  match gd.key with | .dispatch _ => true | _ => false

private def countDisps (P : Program) : Nat :=
  (P.globalList.filter fun (_, g) => isDisp g).length

mutual

private def hasDefaultCase : Exp → Bool
  | .bind _ _ e => hasDefaultCase e
  | .join _ _ b e => hasDefaultCase b || hasDefaultCase e
  | .case _ alts d => d.isSome || hasDefaultAlts alts
  | .tick e => hasDefaultCase e
  | _ => false

private def hasDefaultAlts : List Alt → Bool
  | [] => false
  | .mk _ _ b :: rest => hasDefaultCase b || hasDefaultAlts rest

end

/-! ## 1. Known-dispatch shrink + dead-con + prune -/

def testKnownDispatch (a : Assert) : IO String := do
  -- root(n) = let f = fn [x] => add x n in app f [7]
  -- After P8: root constructs clo(lam, [n]) and calls dispatch 1.
  -- Post-P8 shrink fires `knownDispatch`, inlines/shrinks the arm, eliminates dead `con`,
  -- and `Prune` removes the dispatcher.
  let p := prog [
    gd 0 1 (b (fn 1 (b (add (x 0) (x 1)) (.ret (x 0))))
            (b (.app (x 0) [lit 7]) (.ret (x 0))))
  ] [0]
  let q8 ← IO.ofExcept (IxCC.Anf.defun p)
  expect a (countDisps q8 == 1) s!"known-dispatch: expected 1 dispatcher after P8, got {countDisps q8}"
  let (cert, _, fires) ← IO.ofExcept (IxCC.Anf.Shrink.produce {} q8)
  expect a (fires.knownDispatch > 0)
    s!"known-dispatch: expected fires.knownDispatch > 0, got {fires.render}"
  let q2r ← IO.ofExcept (IxCC.Anf.Shrink.run {} cert q8)
  let qp := IxCC.Anf.Prune.run q2r
  expect a (countDisps qp == 0)
    s!"known-dispatch: expected 0 dispatchers after shrink+prune, got {countDisps qp}\n{qp.render}"
  checkOutput a p qp "known-dispatch"
  for n in [0, 5, 42] do
    let r1 ← runAnf p 100 0 [n]
    let r2 ← runAnf qp 100 0 [n]
    expect a (anfOutcome r1 == anfOutcome r2)
      s!"known-dispatch({n}): {anfOutcome r1} vs {anfOutcome r2}"
    expect a (anfOutcome r2 == s!"ok lit {n + 7}")
      s!"known-dispatch({n}): expected ok lit {n + 7}, got {anfOutcome r2}"
  -- Also test via full `Anf.Pipeline.closures`: collapses to 0 dispatchers.
  let qc ← IO.ofExcept (IxCC.Anf.Pipeline.closures [1] p)
  expect a (countDisps qc == 0)
    s!"known-dispatch closures: expected 0 dispatchers, got {countDisps qc}"
  let rc ← runAnf qc 100 (qc.roots.headD 0) [13]
  expect a (anfOutcome rc == "ok lit 20") s!"known-dispatch closures(13): {anfOutcome rc}"
  return s!"known-dispatch: fires={fires.knownDispatch}, dispatchers 1→0 (shrink+prune & closures)"

/-! ## 2. P9 flow-directed dispatch narrowing (honest + dishonest certs) -/

/-- Build a program with 6 distinct 1-arg closures in `dispatch 1`, where helper
`applyPair` only ever receives 2 of them (selected dynamically by a Nat arg `k`),
and helper `applyOther` only receives 4 of them — so `Flow.analyse P 2` narrows
`applyPair`'s dispatch site from 6 arms to 2 arms while keeping `applyOther` on
the dispatcher (or `Flow.analyse P 4` narrows both!). -/
private def mkMultiCloProg : Program :=
  -- g0(sel, v): if sel == 0 then fn y => y + 1 else fn y => y + 2
  -- g1(sel, v): chooses among 4 more closures (y + 3, y + 4, y + 5, y + 6)
  -- g2(f, v): app f [v]   (not inlined into g0/g1 if we make g2 recursive or call via P8 directly)
  -- To prevent P2 from folding `f` statically at `g2`, `g0` passes the dynamically chosen `f` to `g2`.
  let mkAdd (k : Nat) : Bind := fn 1 (b (add (x 0) (lit k)) (.ret (x 0)))
  let body0 : Exp :=
    .case (x 1)
      [.mk Defun.natZ 0 (b (mkAdd 1) (b (.call 2 [x 0, x 1]) (.ret (x 0)))),
       .mk Defun.natS 1 (b (mkAdd 2) (b (.call 2 [x 0, x 2]) (.ret (x 0))))]
      none
  let body1 : Exp :=
    .case (x 1)
      [.mk Defun.natZ 0 (b (mkAdd 3) (b (.call 3 [x 0, x 1]) (.ret (x 0)))),
       .mk Defun.natS 1
         (.case (x 0)
           [.mk Defun.natZ 0 (b (mkAdd 4) (b (.call 3 [x 0, x 2]) (.ret (x 0)))),
            .mk Defun.natS 1
              (.case (x 0)
                [.mk Defun.natZ 0 (b (mkAdd 5) (b (.call 3 [x 0, x 3]) (.ret (x 0)))),
                 .mk Defun.natS 1 (b (mkAdd 6) (b (.call 3 [x 0, x 4]) (.ret (x 0))))]
                none)]
           none)]
      none
  -- g2(f, v) = app f [v]; g3(f, v) = app f [v]
  let bodyApply : Exp := b (.app (x 1) [x 0]) (.ret (x 0))
  -- root(sel, v) = let a = call g0 [sel, v]; let b = call g1 [sel, v]; add a b
  let bodyRoot : Exp :=
    b (.call 0 [x 1, x 0])
      (b (.call 1 [x 2, x 1])
        (b (add (x 1) (x 0)) (.ret (x 0))))
  prog [
    gd 0 2 body0,
    gd 1 2 body1,
    gd 2 2 bodyApply,
    gd 3 2 bodyApply,
    gd 4 2 bodyRoot
  ] [4]

def testNarrowing (a : Assert) : IO String := do
  let p := mkMultiCloProg
  let q8 ← IO.ofExcept (IxCC.Anf.defun p)
  expect a (countDisps q8 == 1) s!"P9: expected 1 mega-dispatcher after P8, got {countDisps q8}"
  -- Analyze with maxArms = 4: both g2 (2 keys) and g3 (4 keys) narrow from 6 arms!
  let some cert := IxCC.Anf.Defun.Flow.analyse q8 4
    | do expect a false "P9: Flow.analyse returned none on 6-closure multi-site program"; return ""
  expect a (IxCC.Anf.Defun.Narrow.checkCert cert) "P9: Flow.analyse produced cert failing checkCert"
  let qn := IxCC.Anf.Defun.Narrow.run cert q8
  -- Verify no default arms were introduced (Rt.checkSwitches compatibility!)
  expect a (qn.globalList.all fun (_, g) => !hasDefaultCase g.body)
    "P9: Narrow.run introduced a case default arm"
  let qp := IxCC.Anf.Prune.run qn
  expect a (countDisps qp == 0)
    s!"P9: expected mega-dispatcher eliminated after narrow+prune, got {countDisps qp}\n{qp.render}"
  checkOutput a p qp "P9 narrowed"
  -- Check semantic agreement on all 4 selector branches
  for (sel, v, want) in [(0, 10, 24), (1, 10, 26), (2, 10, 27), (3, 10, 28)] do
    let r8 ← runAnf q8 200 4 [sel, v]
    let rn ← runAnf qp 200 (qp.roots.headD 0) [sel, v]
    expect a (anfOutcome r8 == s!"ok lit {want}") s!"P9 q8({sel},{v}): {anfOutcome r8}"
    expect a (anfOutcome rn == s!"ok lit {want}") s!"P9 qp({sel},{v}): {anfOutcome rn}"
  -- Dishonest / adversarial certificates must fail validation and leave q8 unchanged!
  let bogusEmpty : IxCC.Anf.Defun.Narrow.Cert :=
    { maxArms := 4, params := [(2, [some [], some []]), (3, [some [], some []])] }
  let qBad1 := IxCC.Anf.Defun.Narrow.run bogusEmpty q8
  expect a (qBad1.beq q8) "P9: bogus empty-flow cert should be rejected and return P unchanged"
  let bogusWrongKey : IxCC.Anf.Defun.Narrow.Cert :=
    { cert with params := cert.params.map fun (g, ps) =>
        if g == 2 then (g, [some [0], some []]) else (g, ps) }
  let qBad2 := IxCC.Anf.Defun.Narrow.run bogusWrongKey q8
  expect a (qBad2.beq q8) "P9: bogus missing-key cert should be rejected and return P unchanged"
  let bogusOob : IxCC.Anf.Defun.Narrow.Cert :=
    { cert with params := [(2, [some [9999], some []])] }
  let qBad3 := IxCC.Anf.Defun.Narrow.run bogusOob q8
  -- Out-of-bounds index decodes to `none` (⊤), which is sound and does not narrow site 2.
  checkOutput a p qBad3 "P9 oob cert"
  for (sel, v, want) in [(0, 10, 24), (1, 10, 26)] do
    let r ← runAnf qBad3 200 4 [sel, v]
    expect a (anfOutcome r == s!"ok lit {want}") s!"P9 qBad3({sel},{v}): {anfOutcome r}"
  return "P9 flow narrowing: 6-arm mega-dispatcher narrowed (2+4 arms) and pruned to 0; dishonest certs safely refused"

/-! ## 3. P5 erased/dead-parameter stripping -/

def testDeadParam (a : Assert) : IO String := do
  -- `helper` has 8 params [p0..p7] (like StateT.bind): only p2, p4, p6, p7 are used;
  -- p0, p1, p3, p5 are erased `□` slots (occ == 0).
  -- In de Bruijn indices (param i of 8 is var (7 - i)):
  --   p2 = var 5, p4 = var 3, p6 = var 1, p7 = var 0
  let helperBody : Exp :=
    b (add (x 5) (x 3))
      (b (add (x 0) (x 2))
        (b (add (x 0) (x 2)) (.ret (x 0))))
  -- `caller` has 5 params [a, dead1, b, c, d]; passes dead1 only to helper's erased slot p1!
  -- Round 1 strips helper (8 → 4 params) and rewrites caller's call to drop dead1.
  -- Round 2 sees dead1 now has occ == 0 in caller and strips caller (5 → 4 params)!
  -- In caller (5 params): a=x4, dead1=x3, b=x2, c=x1, d=x0
  let callerBody : Exp :=
    b (.call 0 [.box, x 3, x 4, .box, x 2, .box, x 1, x 0]) (.ret (x 0))
  -- `allDead` has 3 params, uses none (returns lit 99): keeps 1 param (arity stays > 0).
  let allDeadBody : Exp := .ret (lit 99)
  -- `root` has 2 params [u, v] where u is unused: roots MUST NOT be stripped!
  let rootBody : Exp :=
    b (.call 1 [x 0, lit 777, lit 10, lit 20, lit 30])
      (b (.call 2 [lit 1, lit 2, lit 3])
        (b (add (x 1) (x 0)) (.ret (x 0))))
  let p := prog [
    gd 0 8 helperBody,
    gd 1 5 callerBody,
    gd 2 3 allDeadBody,
    gd 3 2 rootBody
  ] [3]
  -- Round 1 + prune
  let p1 := IxCC.Anf.Prune.run (IxCC.Anf.DeadParam.run p)
  checkOutput a p p1 "P5 round 1"
  -- Helper (was 8 params) is now pruned; its worker has 4 params (≤ 7)!
  expect a (p1.globalList.all fun (_, g) => g.ps.length ≤ 5)
    s!"P5 round 1: expected all globals ≤ 5 params, got {p1.globalList.map fun (i, g) => (i, g.ps.length)}"
  -- Root stays at arity 2!
  expect a (p1.arity? (p1.roots.headD 0) == some 2)
    s!"P5 round 1: root arity changed to {p1.arity? (p1.roots.headD 0)}"
  -- Round 2 + prune: `caller` (5 params, with `dead1` now unused) shrinks 5 → 4!
  let p2 := IxCC.Anf.Prune.run (IxCC.Anf.DeadParam.run p1)
  checkOutput a p p2 "P5 round 2"
  expect a (p2.globalList.all fun (_, g) => g.ps.length ≤ 4)
    s!"P5 round 2: expected all globals ≤ 4 params (transitive strip), got {p2.globalList.map fun (i, g) => (i, g.ps.length)}"
  -- All-dead helper kept ≥ 1 param (never drops to 0-arity CAF)
  expect a (p2.globalList.all fun (_, g) => g.ps.length ≥ 1)
    s!"P5 round 2: a function global dropped to arity 0"
  -- Semantic agreement
  for (u, v) in [(0, 1), (5, 7), (100, 25)] do
    let r0 ← runAnf p 100 3 [u, v]
    let r2 ← runAnf p2 100 (p2.roots.headD 0) [u, v]
    expect a (anfOutcome r0 == s!"ok lit {v + 10 + 20 + 30 + 99}")
      s!"P5 source({u},{v}): {anfOutcome r0}"
    expect a (anfOutcome r2 == anfOutcome r0)
      s!"P5 stripped({u},{v}): {anfOutcome r2} vs {anfOutcome r0}"
  return "P5 dead-param stripping: 8→4 worker, transitive 5→4 in round 2, all-dead≥1, root preserved"

/-! ## 4. `PostCert` + `CertJson.mid` / `mid?` round-trip -/

def testCertJson (a : Assert) : IO String := do
  -- Plain cert (`post = none`) omits `"post"` key for byte-identical compatibility
  let plainCert : IxCC.Anf.Pipeline.Cert := { shrink := {}, steps := [.prune], post := none }
  let plainJson := IxCC.Recheck.CertJson.mid plainCert
  expect a (!(plainJson.getObjVal? "post").isOk) "CertJson.mid: plain cert should omit 'post' field"
  let plainBack ← IO.ofExcept (IxCC.Recheck.CertJson.mid? plainJson)
  expect a (plainBack.post.isNone) "CertJson.mid?: plain cert did not round-trip post=none"
  -- Non-empty post cert with all 5 PostStep kinds round-trips identically
  let nc : IxCC.Anf.Defun.Narrow.Cert :=
    { maxArms := 4
      params := [(1, [some [0, 2], none])]
      rets := [(1, some [0])]
      fields := [(0, [some [], some [2]])]
      joins := [(1, [[some [0]]])]
      siteRets := [(1, [some []])] }
  let pc : IxCC.Anf.Pipeline.PostCert :=
    { baseSize := 12
      shrink := { caseOfCase := 256, smallJoin := 16 }
      steps := [.shrink [2, 1, 0], .inline [(0, [1, 2])], .prune, .narrow nc, .deadParam] }
  let fullCert : IxCC.Anf.Pipeline.Cert := { shrink := {}, steps := [.prune], post := some pc }
  let j1 := IxCC.Recheck.CertJson.mid fullCert
  let back ← IO.ofExcept (IxCC.Recheck.CertJson.mid? j1)
  let j2 := IxCC.Recheck.CertJson.mid back
  expect a (j1.compress == j2.compress)
    s!"CertJson.mid round-trip mismatch:\n  {j1.compress}\n  {j2.compress}"
  -- Over-budget P9 cert (maxArms > 16) is rejected by `CertJson.mid?`
  let badNc : IxCC.Anf.Defun.Narrow.Cert := { maxArms := 99 }
  let badCert : IxCC.Anf.Pipeline.Cert :=
    { shrink := {}, steps := [], post := some { baseSize := 1, steps := [.narrow badNc] } }
  match IxCC.Recheck.CertJson.mid? (IxCC.Recheck.CertJson.mid badCert) with
  | .error _ => expect a true ""
  | .ok _ => expect a false "CertJson.mid?: accepted over-budget P9 cert (maxArms=99)"
  return "CertJson post-P8 codec: plain omits 'post'; all 5 PostStep kinds round-trip; over-budget refused"

def run (a : Assert) : IO (Array String) := do
  let l1 ← testKnownDispatch a
  let l2 ← testNarrowing a
  let l3 ← testDeadParam a
  let l4 ← testCertJson a
  return #[l1, l2, l3, l4]

end IxCCTests.Anf.ClosuresOpt
