import IxCCTests.Pipeline.Rc.Support
import IxCCTests.Rt.Native

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc.Levels
open IxCC

def one (c : Compiled) (n seed : Nat) : IO (List (String × Sem.Obs)) := do
  let f := c.artifact.front
  let some root := c.artifact.roots.head? | throw (IO.userError "no RC root")
  let some lamRoot := f.lam.roots.head? | throw (IO.userError "no Lam root")
  let some firRoot := f.fir.exports.head? | throw (IO.userError "no Fir root")
  let some cfgRoot := f.cfg.base.exports.head? | throw (IO.userError "no Cfg root")
  let some (sig, ty) := root.ty | throw (IO.userError "no complete result signature")
  let args := [n, seed]
  let fargs := args.map fun x => Fir.Val.lit (.nat x)
  let rargs := args.map fun x => Own.RVal.lit (.nat x)
  let wordRead := fun (m : X86.Memory) w => Rt.readback sig (regionSize / 8) m ty w
  let want := expected c.name n seed
  let mut rows : List (String × Sem.Obs) := []
  let src ← observation "Src" (Src.readback f.src f.checked.keeps)
    (← IO.lazyPure fun _ => Src.run f.src clock root.const (args.map .lit))
  rows := rows ++ [("src", src)]
  let lam ← observation "Lam" (Lam.readback f.lam)
    (← IO.lazyPure fun _ => Lam.run f.lam clock lamRoot (args.map fun x => .lit (.nat x)))
  rows := rows ++ [("lam", lam)]
  for ((label, P), i) in c.anf.zipIdx do
    let some entry := P.roots.head? | throw (IO.userError "no Anf root")
    let value ← observation "Anf" (Anf.readback P)
      (← IO.lazyPure fun _ => Anf.run P clock entry (args.map fun x => .lit (.nat x)))
    rows := rows ++ [(s!"anf{i}.{label}", value)]
  let fir ← observation "Fir" Fir.readback
    (← IO.lazyPure fun _ => Fir.run f.fir clock firRoot fargs)
  rows := rows ++ [("fir", fir)]
  let own ← observation "Own.Plain" (fun (v, H) => H.readback v)
    (← IO.lazyPure fun _ => Own.Plain.run f.own clock firRoot rargs)
  rows := rows ++ [("own.plain", own)]
  let cfg ← observation "Cfg.Rc" (fun (v, H) => H.readback v)
    (← IO.lazyPure fun _ => Cfg.Rc.run f.cfg clock cfgRoot rargs)
  rows := rows ++ [("cfg.rc", cfg)]
  let memory ← IO.ofExcept (IxCCTests.Rt.initRegion f.lowered regionSize)
  let words := args.map IxCCTests.Rt.tag
  for (label, evaluate) in [
      ("lir", fun (_ : Unit) => Lir.eval { f.lowered.program with main := root.fn } clock words memory IxCCTests.Rt.ctx),
      ("xv", fun (_ : Unit) => Xv.eval { c.machine.xv with main := root.fn } clock words memory IxCCTests.Rt.ctx),
      ("xl", fun (_ : Unit) => Xv.Xl.eval { c.machine.xl with main := root.fn } (f.env {}) clock words memory IxCCTests.Rt.ctx)] do
    let result ← IO.lazyPure evaluate
    let value ← match result with
      | .ok ([word], mem) =>
        let some obs := wordRead mem word | throw (IO.userError (label ++ ": readback failed"))
        pure obs
      | _ => throw (IO.userError (label ++ ": " ++ IxCCTests.Rt.lirOutcome result))
    rows := rows ++ [(label, value)]
  let machines ← IO.ofExcept (IxCCTests.Rt.Machine.initMachines c.machine regionSize)
  let (typed, typedState, _) ← IO.ofExcept (← IO.lazyPure fun _ =>
    IxCCTests.Rt.Machine.runExportTyped c.machine root.symbol
      (args.map UInt64.ofNat) machines.typed 5000000)
  let (bytes, bytesState, _) ← IO.ofExcept (← IO.lazyPure fun _ =>
    IxCCTests.Rt.Machine.runExportBytes c.machine root.symbol
      (args.map UInt64.ofNat) machines.bytes 5000000)
  for (label, exit, state) in [("x86", typed, typedState), ("bytes", bytes, bytesState)] do
    check (label ++ ": nonzero status") (exit.status == 0)
    let some value := wordRead state.memory exit.value | throw (IO.userError (label ++ ": readback failed"))
    rows := rows ++ [(label, value)]
  for (label, value) in rows do
    check s!"{c.name} {n} {seed} {label}: {Rt.renderObs value}, expected {Rt.renderObs want}"
      (value == want)
  return rows

/-! ## Mixed Annotated Heap + Unannotated Scalar Parameters and Synthesized Helpers -/

private def nilKey : Key.CtorKey := .src 940
private def consKey : Key.CtorKey := .src 941
private def natZeroKey : Key.CtorKey := .src 942
private def natSuccKey : Key.CtorKey := .src 943
private def boolFalseKey : Key.CtorKey := .src 944
private def boolTrueKey : Key.CtorKey := .src 945

private def consInfo : Fir.CtorInfo :=
  { key := consKey, tag := 1, nobj := 2, fieldKinds := [.shared, .shared] }

private def testKnown : Lam.Known :=
  { natZero := some natZeroKey
    natSucc := some natSuccKey
    boolFalse := some boolFalseKey
    boolTrue := some boolTrueKey }

private def testCtors : List Lam.CtorInfo :=
  [ { key := nilKey, tag := 0, arity := 0 },
    { key := consKey, tag := 1, arity := 2 },
    { key := natZeroKey, tag := 0, arity := 0 },
    { key := natSuccKey, tag := 1, arity := 1 },
    { key := boolFalseKey, tag := 0, arity := 0 },
    { key := boolTrueKey, tag := 1, arity := 0 } ]

private def mkTestProg (funs : List Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofDense funs
    size := funs.length
    exports := List.range funs.length
    ctors := testCtors
    known := testKnown }

/-- `build (n : Nat) (1 acc : List Nat)`: `n` is unannotated `.many` scalar `Nat`,
`acc` carries `1` (`.linear`). -/
private def buildMixedFun : Fir.Fun :=
  { key := .const 950 []
    params := [(0, .tobj), (1, .tobj)]
    body := .case 0
      [ .mk natZeroKey (.ret (.var 1)),
        .mk natSuccKey
          (.bind 2 (.proj 0 natSuccKey 0)
            (.bind 3 (.ctor consInfo [.var 0, .var 1])
              (.tcall 0 [.var 2, .var 3]))) ]
      none
    contracts := [.many, .linear] }

/-- `sumL (~ xs : List Nat) (acc : Nat)`: `xs` carries `~` (`.localShared`),
`acc` is unannotated `.many` scalar `Nat` threaded through a recursive join point. -/
private def sumBorrowedScalarFun : Fir.Fun :=
  { key := .const 951 []
    params := [(0, .tobj), (1, .tobj)]
    body := .jp 0 [2, 3] true
      (.case 2
        [ .mk nilKey (.ret (.var 3)),
          .mk consKey
            (.bind 4 (.proj 2 consKey 0)
              (.bind 5 (.proj 2 consKey 1)
                (.bind 6 (.prim .natAdd [.var 3, .var 4])
                  (.jmp 0 [.var 5, .var 6])))) ]
        none)
      (.jmp 0 [.var 0, .var 1])
    result := .localShared
    contracts := [{ value := .localShared }, .many] }

/-- `choose (b : Bool) (! xs : List Nat) (! ys : List Nat)`: `b` is unannotated
`.many` scalar `Bool`, `xs` and `ys` carry `!` (`.unique`). -/
private def chooseBoolUniqueFun : Fir.Fun :=
  { key := .const 952 []
    params := [(0, .tobj), (1, .tobj), (2, .tobj)]
    body := .case 0
      [ .mk boolFalseKey (.bind 3 (.ctor consInfo [.lit (.nat 0), .var 1]) (.ret (.var 3))),
        .mk boolTrueKey (.bind 4 (.ctor consInfo [.lit (.nat 1), .var 2]) (.ret (.var 4))) ]
      none
    result := .unique
    contracts := [.many, { value := .unique }, { value := .unique }] }

/-- `headOr (& xs : List Nat) (dflt : Nat)`: `xs` carries `&` (`.affine`),
`dflt` is unannotated `.many` used affinely. -/
private def affHeadDefaultFun : Fir.Fun :=
  { key := .const 953 []
    params := [(0, .tobj), (1, .tobj)]
    body := .case 0
      [ .mk nilKey (.ret (.var 1)),
        .mk consKey (.bind 2 (.proj 0 consKey 0) (.ret (.var 2))) ]
      none
    contracts := [.affine, .many] }

/-- Negative control: unannotated `.many` heap parameter duplicated in `.ctor`. -/
private def dupUnannotatedHeapFun : Fir.Fun :=
  { key := .const 954 []
    params := [(0, .tobj), (1, .tobj)]
    body := .bind 2 (.ctor consInfo [.var 1, .var 1]) (.ret (.var 2))
    contracts := [.linear, .many] }

/-- Compiler-synthesized `.spec` helper with a nested hole inside `.con`. -/
private def specRevFun : Fir.Fun :=
  { key := .spec (.const 950 []) [.hole 0, .con consKey [.hole 1, .con nilKey []]]
    params := [(0, .tobj), (1, .tobj)]
    body := buildMixedFun.body
    contracts := [] }

/-- Compiler-synthesized `.worker` helper keeping parameters 0 and 1. -/
private def workerSumFun : Fir.Fun :=
  { key := .worker (.const 951 []) [true, true]
    params := [(0, .tobj), (1, .tobj)]
    body := sumBorrowedScalarFun.body
    contracts := [] }

/-- Compiler-synthesized `.lam` helper with empty contracts performing affine
pattern-match deconstruction and construction. -/
private def lamHelperFun : Fir.Fun :=
  { key := .lam (.const 950 []) [0, 1]
    params := [(0, .tobj), (1, .tobj)]
    body := .case 0
      [ .mk nilKey (.ret (.var 1)),
        .mk consKey
          (.bind 2 (.proj 0 consKey 0)
            (.bind 3 (.proj 0 consKey 1)
              (.bind 4 (.ctor consInfo [.var 2, .var 1])
                (.tcall 0 [.var 3, .var 4])))) ]
      none
    contracts := [] }

/-- Compiler-synthesized `.dispatch` helper with empty contracts forwarding
arguments affinely. -/
private def dispatchHelperFun : Fir.Fun :=
  { key := .dispatch 2
    params := [(0, .tobj), (1, .tobj)]
    body := .bind 2 (.ctor consInfo [.var 0, .var 1]) (.ret (.var 2))
    contracts := [] }

/-- Negative control: synthesized `.lam` helper that duplicates a heap parameter. -/
private def lamDupHelperFun : Fir.Fun :=
  { key := .lam (.const 950 []) [0, 2]
    params := [(0, .tobj)]
    body := .bind 1 (.ctor consInfo [.var 0, .var 0]) (.ret (.var 1))
    contracts := [] }

example : Own.Plain.selectRcPolicy (mkTestProg [buildMixedFun]) = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicy (mkTestProg [sumBorrowedScalarFun]) = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicy (mkTestProg [chooseBoolUniqueFun]) = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicy (mkTestProg [affHeadDefaultFun]) = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicy (mkTestProg [dupUnannotatedHeapFun]) = .plainRc := by decide +kernel

private def synthZeroRcProg : Fir.Program :=
  mkTestProg [buildMixedFun, sumBorrowedScalarFun, chooseBoolUniqueFun, affHeadDefaultFun,
    specRevFun, workerSumFun, lamHelperFun, dispatchHelperFun]

private def synthDupPlainRcProg : Fir.Program :=
  mkTestProg [buildMixedFun, lamDupHelperFun]

private def partialConstDupPlainRcProg : Fir.Program :=
  mkTestProg [buildMixedFun, dupUnannotatedHeapFun]

private def rootedTestSrc : Src.Program :=
  { (default : Src.Program) with roots := [(default, 950)] }

private def mkAliasChainBody (n : Nat) (dup : Bool) : Fir.Code :=
  let rhs : Fir.Rhs :=
    if dup then .ctor consInfo [.var n, .var n]
    else .ctor consInfo [.var n, .lit (.nat 0)]
  let base : Fir.Code := .bind (n + 1) rhs (.ret (.var (n + 1)))
  (List.range n).foldr (fun i k => .bind (i + 1) (.arg (.var i)) k) base

private def mkAliasChainProg (n : Nat) (dup : Bool) : Fir.Program :=
  let helper : Fir.Fun :=
    { key := .lam (.const 950 []) [0, 3]
      params := [(0, .tobj)]
      body := mkAliasChainBody n dup
      contracts := [] }
  mkTestProg [buildMixedFun, helper]

example : Own.Plain.selectRcPolicy synthZeroRcProg = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicy synthDupPlainRcProg = .plainRc := by decide +kernel
example : Own.Plain.selectRcPolicy partialConstDupPlainRcProg = .plainRc := by decide +kernel
example : Own.Plain.selectRcPolicy (mkAliasChainProg 64 false) = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicy (mkAliasChainProg 64 true) = .plainRc := by decide +kernel

private def enrichedSynthProg : Fir.Program :=
  Own.Plain.enrichFirContracts default synthZeroRcProg

example : (enrichedSynthProg.fun? 4).map (·.contracts) =
    some [.many, .linear] := by decide +kernel
example : (enrichedSynthProg.fun? 5).map (·.contracts) =
    some [{ value := .localShared }, .many] := by decide +kernel
example : Own.Plain.selectRcPolicyForSrc default synthZeroRcProg = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicyForSrc rootedTestSrc synthZeroRcProg = .zeroRc := by decide +kernel
example : Own.Plain.selectRcPolicyForSrc rootedTestSrc synthDupPlainRcProg = .plainRc := by decide +kernel
example : Own.Plain.selectRcPolicyForSrc rootedTestSrc partialConstDupPlainRcProg = .plainRc := by decide +kernel

private def setPiContracts : List Ixon.V3.BinderContract → Src.Term → Src.Term
  | c :: cs, .pi b r d body => .pi { b with contract := c } r d (setPiContracts cs body)
  | _, t => t

private def setLamContracts : List Ixon.V3.BinderContract → Src.Term → Src.Term
  | c :: cs, .lam b d body => .lam { b with contract := c } d (setLamContracts cs body)
  | _, t => t

/-- Verify on the real-source `OS16-plain` closure (`build`, `revAcc`, `sumL`)
that annotating ONLY the heap `List Nat` parameters (`build`: `[.many, 1]`,
`revAcc`: `[!, !]`, `sumL`: `[~, .many]`) while leaving the scalar `Nat`
parameters (`n : Nat` on `build`, `acc : Nat` on `sumL`) unannotated selects
`.zeroRc` via `selectPolicy` and `produceAuto`. -/
def verifyMixedScalarRealSource : IO Unit := do
  let bytes ← IO.FS.readBinFile "fixtures/ownership/OS16-plain.ixe"
  let eqs ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "fixtures/ownership/OS16-plain.equations.json"))
  let baseInp ← IO.ofExcept ((Recheck.ingress bytes eqs ["entry"] false).mapError (·.message))
  let p0 := baseInp.program
  let cLinear : Ixon.V3.BinderContract := { uses := .linear }
  let cUnique : Ixon.V3.BinderContract := { value := { owned := .unique } }
  let cBorrow : Ixon.V3.BinderContract := { value := { locality := .local } }
  let lookupDef (name : String) : IO (Src.CId × Src.CId) := do
    let some prop := baseInp.hints.proposals.find? (·.name? == some name)
      | throw (IO.userError s!"OS16: missing equation proposal for {name}")
    let some f := p0.lookup prop.subject
      | throw (IO.userError s!"OS16: missing definition {name}")
    let some thm := prop.theorem?.bind p0.lookup
      | throw (IO.userError s!"OS16: missing equation theorem for {name}")
    pure (f, thm)
  let (buildId, buildEqId) ← lookupDef "build"
  let (revId, revEqId) ← lookupDef "revAcc"
  let (sumId, sumEqId) ← lookupDef "sumL"
  let specs : List (Src.CId × Src.CId × List Ixon.V3.BinderContract) :=
    [(buildId, buildEqId, [{}, cLinear]),
     (revId, revEqId, [cUnique, cUnique]),
     (sumId, sumEqId, [cBorrow, {}])]
  let mut consts := p0.consts
  for (f, thm, cs) in specs do
    let some fEntry := consts.get? f | throw (IO.userError s!"OS16: missing const {f}")
    let Src.Decl.defn .defn .safe n tf vf := fEntry.decl
      | throw (IO.userError s!"OS16: unexpected decl for {f}")
    let some thmEntry := consts.get? thm | throw (IO.userError s!"OS16: missing eq const {thm}")
    let Src.Decl.defn .thm .safe n' tθ vθ := thmEntry.decl
      | throw (IO.userError s!"OS16: unexpected eq decl for {thm}")
    consts := consts.insert f { fEntry with decl := .defn .defn .safe n (setPiContracts cs tf) (setLamContracts cs vf) }
    consts := consts.insert thm { thmEntry with decl := .defn .thm .safe n' (setPiContracts cs tθ) vθ }
  let some eqId := p0.known.eq | throw (IO.userError "OS16: missing pinned Eq")
  let eqPairs : Array (Ixon.Address × Ixon.Address) :=
    specs.toArray.map fun (f, thm, _) => (p0.addr f, p0.addr thm)
  let profile : Src.Resource.Profile := { eqType := some (p0.addr eqId), equations := eqPairs }
  let profBytes := profile.bytes
  let profAddr := Ixon.Address.blake3Pure profBytes
  let checkedPairs : List Src.Resource.Pair :=
    specs.filterMap fun (f, thm, _) =>
      match consts.get? f with
      | some entry => some
        { definition := p0.addr f
          equation := p0.addr thm
          profile := profAddr
          contracts := Src.Resource.headers entry.decl.type }
      | none => none
  let ctx : Src.Resource.Context :=
    { address := profAddr, bytes := profBytes, pairs := checkedPairs }
  let annotatedInp : Recheck.Input := { baseInp with program := { p0 with consts, resource := some ctx } }
  let cfg := (Recheck.Config.forInput { names := ["entry"] } annotatedInp)
  let pol ← IO.ofExcept ((Recheck.RcReplay.selectPolicy cfg annotatedInp).mapError (·.message))
  check s!"OS16 mixed scalar/heap contracts expected .zeroRc, got {repr pol}" (pol == .zeroRc)
  match ← IO.ofExcept ((Recheck.RcReplay.produceAuto cfg annotatedInp).mapError (·.message)) with
  | .zeroRc .. => pure ()
  | .plainRc .. => throw (IO.userError "OS16 mixed scalar/heap produceAuto selected .plainRc instead of .zeroRc")

def run (logs : System.FilePath) : IO Unit := do
  IxCCTests.Recheck.Rc.Fixtures.verify
  check "mixed scalar/contract + synthesized helpers select .zeroRc"
    (Own.Plain.selectRcPolicyForSrc default synthZeroRcProg == .zeroRc)
  check "duplicating synthesized helper selects .plainRc"
    (Own.Plain.selectRcPolicyForSrc default synthDupPlainRcProg == .plainRc)
  check "rooted partially-annotated program with duplicating helper selects .plainRc"
    (Own.Plain.selectRcPolicyForSrc rootedTestSrc synthDupPlainRcProg == .plainRc)
  check "rooted partially-annotated program with duplicating .const selects .plainRc"
    (Own.Plain.selectRcPolicyForSrc rootedTestSrc partialConstDupPlainRcProg == .plainRc)
  let chainZero := mkAliasChainProg 400 false
  let chainPlain := mkAliasChainProg 400 true
  let t0 ← IO.monoMsNow
  let polZero := Own.Plain.selectRcPolicy chainZero
  let polPlain := Own.Plain.selectRcPolicy chainPlain
  let t1 ← IO.monoMsNow
  check "400-let affine alias chain selects .zeroRc" (polZero == .zeroRc)
  check "400-let duplicating alias chain selects .plainRc" (polPlain == .plainRc)
  check s!"400-let alias chain selectRcPolicy took {t1 - t0} ms (expected < 50 ms)" (t1 - t0 < 50)
  check "Certificate.ofText rejects scientific notation before Json.parse"
    (!(Own.Plain.Certificate.ofText default "[1e100000000000]").isOk)
  check "Certificate.ofTextContract rejects scientific notation before Json.parse"
    (!(Own.Plain.Certificate.ofTextContract default "[1e100000000000]").isOk)
  verifyMixedScalarRealSource
  let mut report : List String := []
  for name in IxCCTests.Recheck.Rc.Fixtures.roots do
    let c ← compile name
    check (name ++ ": unannotated RC fixture must select .plainRc")
      (Own.Plain.selectRcPolicyForSrc c.artifact.front.src c.artifact.front.fir == .plainRc)
    save logs c
    for (n, seed) in cases do
      let rows ← one c n seed
      for (label, value) in rows do
        report := report ++ [s!"{name}\t{n}\t{seed}\t{label}\t{Rt.renderObs value}"]
      IO.println s!"PASS {name} {n} {seed}: {rows.length} actual RC pipeline levels, complete value"
  IO.FS.writeFile (logs / "levels.tsv") (String.intercalate "\n" report ++ "\n")

def native (logs : System.FilePath) : IO Unit := do
  IxCCTests.Recheck.Rc.Fixtures.verify
  IO.FS.createDirAll logs
  let mut report : List String := []
  for name in IxCCTests.Recheck.Rc.Fixtures.roots do
    let c ← compile name
    save logs c
    let some root := c.artifact.roots.head? | throw (IO.userError "no root")
    let some (sig, ty) := root.ty | throw (IO.userError "no root type")
    let exe ← IxCCTests.Rt.Native.link { work := logs } s!"levels-{name}" c.artifact.backend.object root.symbol
    let rows ← runNative logs ("native-" ++ name) exe
      { region := regionSize, stack := 1048576, ty := root.ty, dump := true }
      (cases.map fun (n, seed) => [n, seed])
    check "native row count" (rows.length == cases.length)
    for ((n, seed), row) in cases.zip rows do
      let want := expected name n seed
      check s!"{name} {n} {seed}: independent C/Lean full native observation"
        (row.status == 0 && row.ok && !row.init && row.obs == some (Rt.renderObs want) &&
          row.readback regionSize sig ty == some want)
      report := report ++ [s!"{name}\t{n}\t{seed}\tnative\t{Rt.renderObs want}"]
      IO.println s!"PASS native {name} {n} {seed}: complete C+Lean value"
  IO.FS.writeFile (logs / "native-levels.tsv") (String.intercalate "\n" report ++ "\n")

end IxCCTests.Pipeline.Rc.Levels
