import LSpec
import Tests.Ix.Compile.AuxCert
import Tests.Ix.AuxGen.ProbeReport
import Ix.AuxGen.Kernel

namespace Tests.Ix.Compile.AuxCertLeanExpect

open LSpec Tests.Ix.Compile.AuxCert

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def check : IO Nat := do
  ensure (fixtures.all fun f => f.knownFails.all (·.1 != "lean")) "old Lean allowances remain"
  let selected := fixtures.filter (!·.leanRefusals.isEmpty)
  ensure (selected.map (·.stem) == ["NestedSortU", "NestedSortUK", "NestShapes", "UnsafeI", "KernelSpec"]) "unexpected refusal fixtures"
  ensure ((selected.map (·.leanRefusals.length)).foldl (· + ·) 0 == 134) "all 134 measured labels are required"
  let some fixture := selected.find? (·.stem == "NestedSortUK") | throw (IO.userError "missing NestedSortUK record")
  let specs := fixture.leanRefusals
  ensure (specs.length == 5) "exactly five measured expectations are required"
  let block : Ixon.Constant := {
    info := .muts #[.indc {
      isUnsafe := false, lvls := 0, params := 0, indices := 0
      typ := .sort 0, ctors := #[] }]
    refs := #[], sharing := #[], univs := #[.succ .zero] }
  let owner := Address.blake3 (Ixon.serConstant block)
  let projection : Ixon.Constant := {
    info := .iPrj { idx := 0, block := owner }, refs := #[], sharing := #[], univs := #[] }
  let address := Address.blake3 (Ixon.serConstant projection)
  let name := _root_.Ix.Name.fromLeanName `NestedSortUK.T
  let env := (({} : Ixon.Env).storeConst owner block).storeConst address projection
    |>.registerName name { addr := address, constMeta := .empty }
  ensure (owner != address) "projection/owner control is vacuous"
  let expected ← IO.ofExcept (specs.toArray.mapM (·.expected env))
  ensure ((expected.extract 0 4).all (fun r => r.outcome == "decline" && r.reason ==
    s!"decline: reader: in-process model of #{(toString address).take 12}: small eliminator on a non-Prop block") &&
    expected[4]?.map (·.reason) == some s!"blocked: {owner}") "addresses were not derived from the artifact"
  let ctor : Ixon.Constant := { projection with info := .cPrj { idx := 0, cidx := 0, block := owner } }
  let ctorAddr := Address.blake3 (Ixon.serConstant ctor)
  let withCtor := (env.storeConst ctorAddr ctor).registerName (_root_.Ix.Name.fromLeanName `NestedSortUK.T.mk) { addr := ctorAddr, constMeta := .empty }
  let minor ← IO.ofExcept ((LeanRefusal.minorMismatch "Example" "NestedSortUK.T" "NestedSortUK.T.mk").expected withCtor)
  ensure (ctorAddr != address && minor.reason == s!"decline: reader: in-process model of #{(toString address).take 12}: minor 1 (#{(toString ctorAddr).take 12}): 1 inductive hypotheses for 0 recursive fields") "minor mismatch lost exact type/constructor evidence"
  ensure (((LeanRefusal.minorMismatch "Example" "NestedSortUK.T" "NestedSortUK.T.mk").expected env) matches .error _) "missing constructor evidence accepted"
  let unsafeRow ← IO.ofExcept ((LeanRefusal.unsafeInductive "NestedSortUK.T").expected env)
  ensure (unsafeRow.outcome == "decline" && unsafeRow.reason == "decline: reader: unsafe inductive declaration") "unsafe record changed outcome/reason"
  let accept : Tests.Ix.Compile.LeanReport.Row := { label := "Ordinary", outcome := "accept" }
  let typed : Tests.Ix.Compile.LeanReport.Row := { label := "Unsafe", outcome := "typed" }
  let actual := #[accept, typed] ++ expected
  ensure (leanOutcomeProblems expected actual).isEmpty "exact measured refusals were rejected"
  let altered := fun (i : Nat) (f : Tests.Ix.Compile.LeanReport.Row → Tests.Ix.Compile.LeanReport.Row) =>
    #[accept, typed] ++ expected.modify i f
  let cases := [
    ("missing", actual.pop),
    ("extra", actual.push { label := "Extra", outcome := "decline", reason := "decline: other" }),
    ("duplicate", actual ++ expected.extract 0 1),
    ("different status", altered 0 fun r => { r with outcome := "blocked" }),
    ("ordinary reject at recorded label", altered 0 fun r => { r with outcome := "reject", reason := "reject: type mismatch" }),
    ("recorded refusal became accept", altered 0 fun r => { r with outcome := "accept", reason := "" }),
    ("recorded refusal became typed", altered 0 fun r => { r with outcome := "typed", reason := "" }),
    ("different reason", altered 0 fun r => { r with reason := "decline: different modeller boundary" }),
    ("wrong blocked owner", altered 4 fun r => { r with reason := s!"blocked: {address}" }),
    ("ordinary rejection", actual.modify 0 fun r => { r with outcome := "reject", reason := "reject: bad type" })]
  for (label, changed) in cases do
    ensure (!(leanOutcomeProblems expected changed).isEmpty) s!"{label} satisfied the exact record"
  ensure (!(leanOutcomeProblems (expected ++ expected.extract 0 1) actual).isEmpty)
    "duplicate expectation was accepted"
  ensure (!(leanOutcomeProblems #[] actual).isEmpty) "refusals passed without a record"
  for broken in [
      { env with named := {} }, { env with consts := env.consts.erase address },
      { env with consts := env.consts.erase owner }] do
    ensure (specs.toArray.mapM (LeanRefusal.expected broken) matches .error _)
      "missing artifact evidence was accepted"
  ensure (cases.length == 10) "expectation controls did not all run"
  IO.println "AuxCert IxC records: five measured fixtures/134 labels; exact address-derived reasons and all 15 prior refusal controls retained"
  return 19

private def traceControls : IO Unit := do
  let key := _root_.Ix.Name.fromLeanName `TraceProfile
  let good := _root_.Ix.AuxGen.IxcStats.line key
    { queries := 1, answered := 1, recWhnf := 1, recBeta := 1, elim := 1,
      leanRecSame := 1, familyInstalled := 1, unsafeBlock := 1, tier := 1 }
  for stem in ["BelowNRec", "UnsafeI", "F5_SigmaNestedNested"] do
    ensure (checkedTrace good stem matches .ok _) "valid checked trace refused"
  let refuses text stem why : IO Unit := match checkedTrace text stem with
    | .error e => ensure (e == "checked trace: " ++ why) s!"wrong trace refusal: {e}"
    | .ok _ => throw (IO.userError "bad trace passed")
  -- Exact row from all five frozen134 whole-file captures (row SHA54cd00a3).
  -- Both unsafe definitions stay Source-blocked; this wrapper asks no IxC work.
  let idle := "[auxgen-ixc] Lean.Meta.FindSplitImpl.visit: queries 0 tcFast 0 ixcFast 0 answered 0 equal 0 differ 0 refused 0 scopesRefused 0 flat 0/0 decisions 0 decisionsEqual 0 decisionsDiffer 0 exprQueries 0 exprAnswered 0 below 0/0 recWhnf 0 recStuck 0 recSame 0 recReplayed 0 recBeta 0 recRefused 0 recEqual 0 recDiffer 0 recDiffName 0 recDiffInfo 0 recDiffLevel 0 recDiffOther 0 recDecisionDiffer 0 recSkipped 0 recSkipDiffer 0 recForced 0 elim 0 elimEqual 0 elimDiffer 0 elimRefused 0 leanRecSame 0 leanRecDiffer 0 family 0/0 unsafe 1 tier 0 asked 0"
  let (idleCounts, idleTails) ← IO.ofExcept (checkedTrace idle "SortUDecl")
  ensure (idleTails == 1 && idleCounts.get? "unsafe" == some 1 && idleCounts.get? "tier" == some 0 &&
    idleCounts.get? "asked" == some 0) "captured zero-work row disappeared from coverage"
  let producerWords := (((good.splitOn ": ")[1]!).splitOn " ").filter (!·.isEmpty) |>.toArray
  for i in [:producerWords.size / 2] do
    let k := producerWords[2*i]!; let v := producerWords[2*i+1]!
    refuses (good.replace s!" {k} {v}" "") "TraceProfile"
      (if k == "queries" then "malformed tail header" else "missing required counter")
  let idleWords := (((idle.splitOn ": ")[1]!).splitOn " ").filter (!·.isEmpty) |>.toArray
  for i in [:idleWords.size / 2] do
    let k := idleWords[2*i]!; let v := idleWords[2*i+1]!
    if k == "unsafe" || k == "tier" then continue
    let parts := (v.splitOn "/").toArray
    for j in [:parts.size] do
      let changed := String.intercalate "/" (parts.set! j "1").toList
      refuses (idle.replace s!" {k} {v}" s!" {k} {changed}") "SortUDecl"
        (if k == "queries" || k == "answered" then "answered/query coverage differs" else "unsafe tail lacks its tier")
  refuses (idle ++ " futureCounter 1") "SortUDecl" "unsafe tail lacks its tier"
  refuses (idle.replace "unsafe 1 tier 0" "unsafe 0 tier 1") "SortUDecl" "tier marker without unsafe block"
  for (k, v) in [("unsafe", "1"), ("tier", "0"), ("asked", "0")] do
    refuses (idle.replace s!" {k} {v}" s!" {k} 2") "SortUDecl" "non-Boolean trace flag"
  refuses (good.replace "unsafe 1 tier 1" "unsafe 0 tier 0" ++ "\n" ++ idle) "UnsafeI" "unsafe profile is empty"
  for (text, why) in [("", "no tail coverage"), (good ++ "\n" ++ good, "empty/duplicate tail key"),
      (good.replace ": queries" ": query", "malformed tail header"),
      (good ++ " dangling", "dangling counter"), (good.replace "answered 1" "answered nope", "nonnumeric counter"),
      (good.replace "answered 1" "answered 0", "answered/query coverage differs"),
      (good.replace " answered 1" "", "missing required counter"), (good.replace "below 0/0" "below 0", "counter shape"),
      (good ++ " queries 1", "duplicate counter"), (good.replace "refused 0" "refused 1", "refused is nonzero"),
      (good.replace "tier 1" "tier 0", "unsafe tail lacks its tier")] do refuses text "BelowNRec" why
  for (stem, text, why) in [("BelowNRec", good.replace "family 1/0" "family 0/0", "Prop family profile is empty"),
      ("UnsafeI", good.replace "unsafe 1 tier 1" "unsafe 0 tier 0", "unsafe profile is empty"),
      ("F5_SigmaNestedNested", good.replace "recBeta 1" "recBeta 0", "named beta profile is empty")] do refuses text stem why
  let complete := Tests.Ix.AuxGen.ProbeReport.complete
  ensure (complete {} && !complete { blocks := 1, accepted := 2 } &&
    !complete { blocks := 65, notAccepted := Array.replicate 64 (key, "refused") } &&
    !complete { groupsRefused := 65, refused := Array.replicate 64 ("group", "refused") } &&
    complete { groupsRefused := 64, refused := (Array.range 64).map fun i => (s!"group{i}", "refused") }) "Source report completeness guard changed"
  IO.println "checked trace: malformed/missing/duplicate/refusal/profile controls; malformed/truncated/exact-cap Source reports"
  IO.println "captured unsafe wrapper retained; full producer schema, every work component/new field and Boolean flags checked"

def suite : List TestSeq := [
  .individualIO "measured IxC refusals require exact labels, outcomes, reasons and owners" none (do
    let n ← check
    traceControls
    return (true, n, 0, none)) .done]

end Tests.Ix.Compile.AuxCertLeanExpect
