import IxCCTests.Own.AnnotatedFixture
import IxCCTests.Src.Support
import IxCC.Own.Plain.Certificate
import IxCC.Own.Plain.Semantics
import IxCC.Own.Immortal
import IxCC.Own.Semantics
import IxCC.Src.Readback
import IxCC.Src.Semantics
import IxCC.Fir.Semantics
import IxCC.Src.Relevance.Annotate
import IxCC.Ixon.V3.Tc.Driver
import IxCC.Recheck.Produce

open Lean System IxCC
namespace IxCCTests.Own.AnnotatedRecursion
open IxCCTests.Own.AnnotatedFixture (need field normalizedResource)

def names : List String := ["entry", "len", "len.eq_def", "Nat.add", "Nat.add.eq_def"]
def inputs : List Nat := [0, 1, 2, 5, 10, 20]
def clock : Nat := 10000

def address (dir : FilePath) (variant name : String) : IO String := do
  let value := (← IO.FS.readFile (dir / s!"{variant}.address-{name}.stdout")).trimAscii.toString
  need (IxCC.Tools.Check.isHex 64 value) s!"{name}: noncanonical addr-of output"
  return value

def sidecar (dir : FilePath) (variant : String) : IO Json := do
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / s!"{variant}.anon.json")))
  let named ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / s!"{variant}.named.json")))
  need (raw == named) "fresh anonymous/named equation sidecars differ"
  need ((← IO.ofExcept (← field raw "format").getStr?) == "ix/compile-equations/1") "fresh producer sidecar format"
  let equations ← IO.ofExcept (← field raw "equations").getArr?
  let actualNames ← equations.toList.mapM fun q => do
    return (← IO.ofExcept (← field q "definition").getStr?,
      ← IO.ofExcept (← field q "equation").getStr?)
  need (actualNames == [("Nat.add", "Nat.add.eq_def"), ("len", "len.eq_def")])
    "review required: fresh OS04 equation inventory changed"
  need ((← IO.ofExcept (← field raw "failures").getArr?).isEmpty) "producer equation failures"
  let pairs ← equations.mapM fun q => do
    let d ← IO.ofExcept (← field q "definition").getStr?
    let e ← IO.ofExcept (← field q "equation").getStr?
    return Json.mkObj [("definition", toJson d), ("definition_address", toJson (← address dir variant d)),
      ("equation", toJson e), ("equation_address", toJson (← address dir variant e))]
  let root ← address dir variant "entry"
  let mut extra : List (String × Json) := []
  if variant == "Annotated" then
    let adapted ← normalizedResource raw
    extra := [("resource_profile", ← field adapted "resource_profile"),
      ("resource_checked", ← field adapted "resource_checked")]
    let some context ← IO.ofExcept (Src.Hints.resourceOfJson adapted)
      | throw (IO.userError "fresh annotated producer omitted resource context")
    let profile ← IO.ofExcept (Src.Resource.Profile.ofBytes context.bytes)
    need (profile.steps == 100000 && profile.depth == 256) "fresh original budget changed"
    need (context.pairs.length == 1) "fresh annotated checked-pair count"
    let verified ← IO.ofExcept (IxCCTests.Corpus.verifiedPairs
      (← IO.FS.readFile (dir / "Annotated.check-equations.stdout")) (toString context.address))
    need (verified.length == context.pairs.length) "fresh checked-equation receipt count"
    for (v, q) in verified.zip context.pairs do
      need (v.definition == "len" && v.equation == "len.eq_def" &&
        v.definitionAddress == toString q.definition && v.equationAddress == toString q.equation &&
        v.definitionAddress == (← address dir variant "len") &&
        v.equationAddress == (← address dir variant "len.eq_def")) "fresh checked pair/addr-of disagreement"
  else
    AnnotatedFixture.legacyPlainEmpty raw
  return Json.mkObj ([
    ("format", toJson ("ixcc/k1-equations/1" : String)),
    ("roots", Json.arr #[Json.mkObj [("name", toJson ("entry" : String)), ("address", toJson root)]]),
    ("equations", Json.arr pairs), ("failures", Json.arr #[])] ++ extra)

def headName (p : Src.Program) : Src.Term → String
  | .const c _ => s!"const {c} {p.addr c} selection={repr (p.table.resolveOf c)}"
  | t => s!"nonconstant {repr t}"

def application (p : Src.Program) (t : Src.Term) : List String := Id.run do
  let (head, args) := t.spine
  let mut rows := [s!"application head={headName p head} argc={args.length}"]
  for ((arg, mode, rel), i) in args.zipIdx do
    rows := rows ++ [s!"  argument {i}: mode={repr mode} relevance={repr rel} term={repr arg}"]
  if let .const c _ := head then
    let selected := match p.table.resolveOf c with
      | some (.case r) => some (r, true)
      | none => some (c, false)
      | _ => none
    if let some (r, caseWrapper) := selected then
      if let some (.recr _ _ _ np nmot nmin ni _ rules _) := p.decl? r then
        let arity := np + nmot + nmin + ni + 1
        rows := rows ++ [s!"  route={if caseWrapper then "checked-case" else "direct-recursor"} recursor={p.addr r} arity={arity} extra={args.length - arity} minors={nmin}"]
        for (rule, j) in rules.zipIdx do
          rows := rows ++ [s!"  rule {j}: fields={rule.fields} ihCount={repr (Src.Table.ruleIhs np nmot nmin j rule)} rhs={repr rule.rhs}"]
  return rows

/-- Report maximal runtime application spines and their actual installed modes.
The full terms are retained as well; this is not a dynamic event counter. -/
def routes (p : Src.Program) : Nat → Bool → Src.Term → List String
  | 0, _, _ => ["ROUTE REPORT TRUNCATED"]
  | fuel + 1, top, t@(.app f a _ rel) =>
    (if top then application p t else []) ++ routes p fuel false f ++
      (if rel.alwaysIrr then [] else routes p fuel true a)
  | fuel + 1, _, .lam _ _ body => routes p fuel true body
  | fuel + 1, _, .letE _ rel _ value body =>
    (if rel.alwaysIrr then [] else routes p fuel true value) ++ routes p fuel true body
  | fuel + 1, _, .proj _ _ e => routes p fuel true e
  | _, _, _ => []

def observe {α : Type} (label : String) (read : α → Option Sem.Obs)
    (result : Sem.Result α) : IO Unit := do
  match result with
  | .ok value => need (read value == some (.nat 3)) (label ++ ": expected complete independent Nat3")
  | .timeout => throw (IO.userError (label ++ ": timeout"))
  | .stuck => throw (IO.userError (label ++ ": stuck"))
  | .trap => throw (IO.userError (label ++ ": trap"))
  | .resource r => throw (IO.userError s!"{label}: resource {repr r}")

def ownershipDiagnostic (fir : Fir.Program) (proposal : String) : IO String := do
  let decoded ← IO.ofExcept (Own.Plain.Certificate.decode fir (← IO.ofExcept (Json.parse proposal)))
  let mut rows := [s!"size={fir.size} exports={repr fir.exports}",
    s!"programDomain={Own.Plain.programDomain fir}",
    s!"checkBoolPins={Own.Plain.checkBoolPins fir}",
    s!"bodyMapEq={Own.Plain.bodyMapEq (Own.Plain.Program.canonical fir).bodies decoded}",
    s!"checkPlainMap={Own.Plain.checkPlainMap fir decoded}"]
  for f in List.range fir.size do
    match fir.fun? f with
    | none => rows := rows ++ [s!"function {f}: MISSING"]
    | some fd =>
      rows := rows ++ [s!"function {f} key={repr fd.key}",
        s!"  result={repr fd.result} shared={decide (fd.result = Ixon.V3.ValueContract.shared)}",
        s!"  params={repr fd.params} allTobj={fd.params.all fun p => decide (p.2 = .tobj)}",
        s!"  contracts={repr fd.contracts} allMany={fd.contracts.all fun c => decide (c = Ixon.V3.BinderContract.many)}",
        s!"  letContracts={repr fd.letContracts} allOrdinary={fd.letContracts.all fun p => decide (p.2.kind = .value) && decide (p.2.binder = Ixon.V3.BinderContract.many)}",
        s!"  funDomain={Own.Plain.funDomain fd} fresh={Own.Plain.fresh [] (fd.params.map (·.1))} scopeOk={Own.Plain.scopeOk (Own.Plain.signatures fir) (fd.params.map (·.1)) [] fd.body}",
        s!"  body={repr fd.body}"]
  return String.intercalate "\n" rows ++ "\n"

/-- The historical bytes are unbound (`0xE4`), written by a producer that
predates the role-bound envelope, so ingress (`Recheck.ingress`, the certified
kernel's acceptance, which admits only role-bound environments) refuses them.
This part reads them as the front end did before the switch: decoded, typed by
IxCC's erased checker (`Tc.checkEnv`), the `entry` root's program read by IxCC's own conversion with the pins of IxCC's
fixed table (`Src.Ingress.ofEnv`), the resource binding validated, and the
relevance annotation from the earlier annotator (`Src.Relevance.annotate`),
These are slated for deletion with the erased checker; this
part goes or is rebuilt on role-bound bytes before then. -/
structure LegacyInput where
  env : Ixon.V3.Env
  hints : Src.Hints
  program : Src.Program

def legacyIngress (bytes : ByteArray) (equations : Json) (root : String) : Except String LegacyInput := do
  let env ← Ixon.V3.decodeAnonymousEnv bytes
  Ixon.V3.Tc.checkEnv env
  let hints ← Src.Hints.ofK1Json equations
  let some r := hints.roots.find? (·.2 == some root) | throw s!"no root named {root}"
  let hints := { hints with roots := #[r] }
  let p ← Src.Ingress.ofEnv env #[r.1]
  let p := { p with known := Src.Pinned.known p, resource := hints.resource }
  Src.Resource.validate p
  pure { env, hints, program := p }

def runFixture (dir : FilePath) (variant : String) (phaseOne := false) : IO Unit := do
  need (["Annotated", "Plain"].contains variant) "unknown source variant"
  let equations ← sidecar dir variant
  IO.FS.writeFile (dir / s!"{variant}.consumer.json") (equations.pretty ++ "\n")
  let bytes ← IO.FS.readBinFile (dir / s!"{variant}.ixe")
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / s!"{variant}.anon.json")))
  -- ingress refuses the unbound envelope; the legacy reading takes it
  let refusal : String := match IxCC.Recheck.ingress bytes equations ["entry"] with
    | .ok _ => "accepted"
    | .error e => if e.code == "kernel" then e.message else s!"{e.code}: {e.message}"
  need ((refusal.splitOn "unbound").length > 1)
    s!"{variant}: ingress did not refuse the unbound envelope as unbound: {refusal}"
  let input ← IO.ofExcept (legacyIngress bytes equations "entry")
  need (toString input.env.root == (← IO.ofExcept (← field raw "root").getStr?)) "fresh anonymous Merkle root/sidecar disagreement"
  let p := input.program
  let (table, diagnostics, _) := Src.Table.build {} p input.hints.proposals
  IO.FS.writeFile (dir / s!"{variant}.table-diags.txt") (String.intercalate "\n" (diagnostics.toList.map (·.render)) ++ "\n")
  let replay ← IO.ofExcept (Src.Table.ofCert {} p (Src.Table.TableCert.ofTable table))
  need (Src.Table.TableCert.ofTable replay == Src.Table.TableCert.ofTable table) "fresh table certificate replay differs"
  let p0 := { p with table := replay }
  let ann ← IO.ofExcept (Src.Relevance.annotate input.env p0)
  let (src, checked) ← match Src.Recheck.run {} p0 ann with
    | .ok result => pure result
    | .error (.table e) => throw (IO.userError ("table: " ++ e))
    | .error (.install e) => throw (IO.userError ("annotation: " ++ e))
    | .error (.relevance es) => throw (IO.userError (String.intercalate "; " (es.toList.map (·.render p0))))
  let some entryAddress := Ixon.Address.fromString (← address dir variant "entry")
    | throw (IO.userError "invalid authenticated entry address")
  let some (sourceAddress, root) := src.roots.head?
    | throw (IO.userError "missing checked Src entry")
  need (src.roots.length == 1 && sourceAddress == entryAddress && src.addr root == entryAddress)
    "exactly one Src root must match actual named entry address"
  let some lenAddress := Ixon.Address.fromString (← address dir variant "len")
    | throw (IO.userError "invalid authenticated len address")
  let some lenId := src.lookup lenAddress | throw (IO.userError "missing actual len")
  match src.table.resolveOf lenId with
  | some (.eqn _ (.lam binder _ body)) =>
    need (body.mentions lenId) "fresh len selected RHS must really recur"
    if variant == "Annotated" then
      need (binder.contract.uses == .erased) "fresh selected len must retain its written erased type header"
  | _ => throw (IO.userError "fresh len must select its genuine equation lambda")
  let some lenRel := checked.constRel? lenId | throw (IO.userError "checked len relevance missing")
  need (lenRel.params.length == 2 && (lenRel.params.filter (!·.alwaysIrr)).length == 1)
    "actual len has exactly one relevant parameter among its two written parameters"
  let admitted ← match Src.admit src (Recheck.sidecarName input.hints) {} with
    | .ok a => pure a
    | .error es => throw (IO.userError (String.intercalate "; " (es.toList.map (·.render))))
  let mut report : List String := [s!"variant={variant} root={← address dir variant "entry"} reached={repr admitted.instances}"]
  for key in checked.keys do
    let some term := src.termOf key | throw (IO.userError "checked runtime term missing")
    report := report ++ [s!"KEY {repr key} TERM {repr term}"] ++ routes src (term.nodes + 1) true term
  need (!report.contains "ROUTE REPORT TRUNCATED") "route report fuel insufficient"
  IO.FS.writeFile (dir / s!"{variant}.routes.txt") (String.intercalate "\n" report ++ "\n")
  let (lam, _) ← IO.ofExcept ((Lam.erase src checked).mapError fun e => (Recheck.Err.ofErase e).message)
  let trace ← IO.ofExcept (Anf.Pipeline.produce {} lam)
  let anf ← IO.ofExcept (Anf.Pipeline.run trace.cert lam)
  let some (_, producedAnf) := trace.stages.getLast? | throw (IO.userError "no produced Anf")
  need (anf.beq producedAnf) "actual Anf certificate endpoint differs"
  let fir ← IO.ofExcept ((Fir.lower anf).mapError fun e => (Recheck.Err.ofFir e).message)
  let proposal := Own.Plain.Certificate.toText (Own.Plain.Program.canonical fir).bodies
  IO.FS.writeFile (dir / s!"{variant}.own.json") (proposal ++ "\n")
  IO.FS.writeFile (dir / s!"{variant}.own-diagnostic.txt") (← ownershipDiagnostic fir proposal)
  let some firRoot := fir.exports.head? | throw (IO.userError "missing actual Fir entry")
  let some firEntry := fir.fun? firRoot | throw (IO.userError "missing actual Fir entry function")
  need (fir.exports.length == 1 && firEntry.arity == 1) "actual Fir must have exactly one unary exported entry"
  let mut rows : List String := []
  for n in inputs do
    observe s!"{variant} entry({n}) Src" (Src.readback src checked.keeps)
      (← IO.lazyPure fun _ => Src.run src clock root [.lit n])
    observe s!"{variant} entry({n}) Fir" Fir.readback
      (← IO.lazyPure fun _ => Fir.run fir clock firRoot [.lit (.nat n)])
    rows := rows ++ [s!"{variant}\t{n}\tsrc\t3", s!"{variant}\t{n}\tfir\t3"]
    IO.println s!"PASS {variant} entry({n}): actual Src/Fir complete Nat3; Own admission not yet accepted"
  IO.FS.writeFile (dir / s!"{variant}.source-observations.tsv") (String.intercalate "\n" rows ++ "\n")
  if phaseOne then
    need (variant == "Annotated") "scoped P4 gate currently pins the authenticated annotated case"
    let decoded ← IO.ofExcept (Own.Plain.Certificate.decode fir (← IO.ofExcept (Json.parse proposal)))
    need (fir.size == 2 && Own.Plain.checkBoolPins fir &&
      Own.Plain.bodyMapEq (Own.Plain.Program.canonical fir).bodies decoded)
      "annotated Plain decline requires two actual functions, valid bool pins and exact canonical candidate"
    let some first := fir.fun? 0 | throw (IO.userError "actual entry function missing")
    let some len := fir.fun? 1 | throw (IO.userError "actual len function missing")
    need (decide (len.key = Key.GKey.const lenId []) &&
      decide (len.params = [(0, Fir.Rep.tobj), (1, Fir.Rep.tobj)]) &&
      decide (len.contracts = [Ixon.V3.BinderContract.erased, Ixon.V3.BinderContract.many]))
      "actual recursive len retains exactly its erased/many contracts and two physical slots"
    for fd in [first, len] do
      need (decide (fd.result = Ixon.V3.ValueContract.shared) &&
        fd.params.all (fun p => decide (p.2 = .tobj)) &&
        fd.letContracts.all (fun p => decide (p.2.kind = .value) &&
          decide (p.2.binder = Ixon.V3.BinderContract.many)) &&
        Own.Plain.fresh [] (fd.params.map (·.1)) &&
        Own.Plain.scopeOk (Own.Plain.signatures fir) (fd.params.map (·.1)) [] fd.body)
        "annotated Plain decline must not hide a result, representation, let, freshness or scope failure"
    need (Own.Plain.funDomain first && !Own.Plain.funDomain len &&
      !Own.Plain.programDomain fir && !Own.Plain.checkPlainMap fir decoded)
      "annotated Plain domain refusal must remain the erased len contract boundary"
    need (Own.Plain.contractFunDomain first && Own.Plain.contractFunDomain len &&
      Own.Plain.contractProgramDomain fir && Own.Plain.checkContractPlainMap fir decoded &&
      Own.Plain.selectRcPolicy fir == .plainRc)
      "contract-aware Plain domain must accept OS-04 erased len and select plainRc while xs is unannotated .many"
    let zeroRcFir : Fir.Program :=
      { fir with
        funs := (fir.funs.insert 0 { first with contracts := first.params.map fun _ => { value := .localShared } })
          |>.insert 1 { len with contracts := [Ixon.V3.BinderContract.erased, { value := .localShared }] } }
    need (Own.Plain.contractProgramDomain zeroRcFir &&
      Own.Plain.checkContractPlainMap zeroRcFir decoded &&
      Own.Plain.selectRcPolicy zeroRcFir == .zeroRc)
      "annotating OS-04 list binders with ~ local borrow must switch selectRcPolicy to zeroRc"
    let own := Own.immortal fir
    need (Own.checkImmortal own) "actual Phase1 Own image must pass its production checker"
    for n in inputs do
      observe s!"{variant} entry({n}) Own.immortal" (fun (v, H) => H.readback v)
        (← IO.lazyPure fun _ => Own.run .immortal own clock firRoot [.lit (.nat n)])
      rows := rows ++ [s!"{variant}\t{n}\town.immortal\t3"]
      IO.println s!"PASS {variant} entry({n}): actual Phase1 Own complete Nat3; no RC acceptance claim"
    -- This is an independent negative boundary, not a fallback from Plain.
    match Own.Plain.Certificate.ofText fir proposal with
    | .ok _ => throw (IO.userError "review required: pinned unsupported erased-contract Plain boundary changed")
    | .error reason =>
      need (reason == "own.cert.check: ownership proposal or source domain refused")
        "unexpected Plain refusal stage/reason"
      IO.FS.writeFile (dir / s!"{variant}.plain-refusal.txt") (reason ++ "\n")
    IO.FS.writeFile (dir / s!"{variant}.phase-one-observations.tsv") (String.intercalate "\n" rows ++ "\n")
    return
  let own ← match Own.Plain.Certificate.ofText fir proposal with
    | .ok own =>
      IO.FS.writeFile (dir / s!"{variant}.own-admission.txt") "accepted\n"
      pure own
    | .error reason =>
      IO.FS.writeFile (dir / s!"{variant}.own-admission.txt") (reason ++ "\n")
      throw (IO.userError reason)
  for n in inputs do
    observe s!"{variant} entry({n}) Own.Plain" (fun (v, H) => H.readback v)
      (← IO.lazyPure fun _ => Own.Plain.run own clock firRoot [.lit (.nat n)])
    rows := rows ++ [s!"{variant}\t{n}\town.plain\t3"]
    IO.println s!"PASS {variant} entry({n}): actual Src/Fir/Own.Plain complete Nat3"
  IO.FS.writeFile (dir / s!"{variant}.observations.tsv") (String.intercalate "\n" rows ++ "\n")

def fixtureDirectory : FilePath := "fixtures/ownership/historical/annotated-recursion-cb68"

-- Replaced only when this exact independent historical fixture inventory is
-- intentionally reviewed. It is not the final selected-producer corpus.
def fixtureInventorySha : String := "e469b3dcf277439f1ea202e6b365236fe8ecb1c541f1cd1fb5678bdbe76e22be"

def checkedCopy (sourceRoot destination : FilePath) : IO Unit := do
  let manifest := sourceRoot / "inputs.sha256"
  need ((← IxCC.Tools.Check.sha256 manifest) == fixtureInventorySha)
    "historical recursion fixture inventory differs"
  IO.FS.createDirAll destination
  for line in (← IO.FS.readFile manifest).splitOn "\n" do
    if line.isEmpty then continue
    let hash := (line.take 64).toString
    let name := (line.drop 66).toString
    need (IxCC.Tools.Check.isHex 64 hash && !name.isEmpty &&
      (name.splitOn "/").length == 1 && (name.splitOn "\\").length == 1 && name != "." && name != "..")
      "malformed historical fixture inventory row"
    let source := sourceRoot / name
    need ((← IxCC.Tools.Check.sha256 source) == hash) s!"historical fixture changed: {name}"
    IO.FS.writeBinFile (destination / name) (← IO.FS.readBinFile source)
    need ((← IxCC.Tools.Check.sha256 (destination / name)) == hash)
      s!"historical copied fixture changed: {name}"

def legacyControls (a : IxCCTests.Src.Assert) : IO Unit := do
  let cases : List (String × Json × Bool) := [
    ("absent", Json.mkObj [], true),
    ("empty", Json.mkObj [("resourceChecked", Json.arr #[])], true),
    ("orphan", Json.mkObj [("resourceChecked", Json.arr #[Json.mkObj []])], false),
    ("malformed", Json.mkObj [("resourceChecked", Json.str "empty")], false),
    ("profile-only", Json.mkObj [("resourceProfile", Json.mkObj [])], false),
    ("profile-and-empty", Json.mkObj [("resourceProfile", Json.mkObj []),
      ("resourceChecked", Json.arr #[])], false)]
  for (label, raw, expected) in cases do
    let accepted ← try
      AnnotatedFixture.legacyPlainEmpty raw
      pure true
    catch _ => pure false
    IxCCTests.Src.expect a (accepted == expected) ("historical legacy adapter: " ++ label)

/-- Genuine historical producer bytes at the Phase1 Src/Own boundary, plus
the distinct plain-RC acceptance/refusal boundary. No external ix is needed. -/
def run (a : IxCCTests.Src.Assert) (work : FilePath)
    (fixtures : FilePath := fixtureDirectory) : IO (Array String) := do
  let output := work / "annotated-recursion"
  checkedCopy fixtures output
  legacyControls a
  AnnotatedFixture.run (output / "Annotated.ixe") (output / "Annotated.anon.json")
    (output / "Annotated.check-equations.stdout")
  IxCCTests.Src.expect a true "genuine structural selected recursion and five refusals completed"
  runFixture output "Annotated" true
  runFixture output "Plain"
  for (variant, own, file) in [("Annotated", "own.immortal", "Annotated.phase-one-observations.tsv"),
      ("Plain", "own.plain", "Plain.observations.tsv")] do
    let rows := ((← IO.FS.readFile (output / file)).splitOn "\n").filter (!·.isEmpty)
    IxCCTests.Src.expect a (rows.length == 18) (variant ++ ": eighteen complete observations")
    for n in inputs do
      for level in ["src", "fir", own] do
        IxCCTests.Src.expect a (rows.contains s!"{variant}\t{n}\t{level}\t3")
          s!"{variant} {n} {level}: literal independent Nat3"
    let reference := ((← IO.FS.readFile (output / (variant ++ ".reference.stdout"))).splitOn "\n").filter (!·.isEmpty)
    IxCCTests.Src.expect a (reference == ["3", "3", "3", "3", "3", "3"])
      (variant ++ ": pinned independent source reference")
  IxCCTests.Src.expect a
    ((← IO.FS.readFile (output / "Annotated.plain-refusal.txt")).trimAscii.toString ==
      "own.cert.check: ownership proposal or source domain refused")
    "annotated erased contract remains outside Plain domain"
  return #["historical cb68/core100k: five structural refusal controls and six local legacy controls",
    "36 complete observations: annotated Src/Fir/checked immortal Own; plain Src/Fir/checked Plain Own",
    "annotated Plain refusal preserved; no selected-producer/final-refreeze or H4 recycling claim"]

end IxCCTests.Own.AnnotatedRecursion
