import LSpec
import Tests.Ix.Compile.AuxCert

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

def suite : List TestSeq := [
  .individualIO "measured IxC refusals require exact labels, outcomes, reasons and owners" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Compile.AuxCertLeanExpect
