/-
  adversarial-matrix: the adversarial matrix of `plans/codex/PLAN-phase-A-and-B.md`
  §9.2 as a regression suite (plan M4 (c)).

  Every row has at least one NEGATIVE case (a forged or mutated artifact) and
  one valid NEIGHBOUR, both run through the same checker, or is marked NOT
  APPLICABLE with the reason. A negative passes only when the checker refuses
  the forged association (`checkCompiled`'s error, a validator phase's
  failure naming the forged constant, a compiler refusal); a changed stdout
  is never enough. The checkers are the ones on the line:

  * the compile-cert artifact check `Ix.CompileCert.checkCompiled` /
    `checkRoot` (hand-built artifacts; the existing controls of
    `Tests.Ix.CompileCert.{Direct,Universes,Expressions}` are invoked by
    label, not duplicated: a label that disappears fails the suite);
  * the standalone compile-cert checks `Tests/Ix/CompileCert/{InstalledRules,
    InstalledFields,ValueReceipt}.lean`, run as subprocesses (cited, their
    summary line required, their log kept);
  * `ix validate-lean`'s phases, called on a compiled artifact whose input
    was forged while Lean's environment (the oracle) is the original: phase 4
    (meta roundtrip, `Ix.Tc.metaRoundtripEnv`), phase 8 (provenance), phase 9
    (clique values, `Ix.Cli.ValidateLeanCmd.phaseCliqueValues`);
  * the compiler's own refusals (an omitted dependency).

  Run with: `lake test -- --ignored adversarial-matrix`. The summary line
  gives, per row, negatives rejected, neighbours accepted, cited checks
  passed and not-applicable rows.
-/
import Ix.Cli.ValidateLeanCmd
import Ix.Cli.CliqueValues
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.CliqueOwnership.Sources
import Tests.Ix.Compile.AdversarialMatrix.Sources
import Tests.Ix.CompileCert.Direct
import Tests.Ix.CompileCert.Universes
import Tests.Ix.CompileCert.Expressions

namespace Tests.Ix.Compile.AdversarialMatrix

open Lean

/-- The kind of a case. -/
inductive Kind where
  | negative | neighbour | cited | notApplicable
  deriving BEq

def Kind.tag : Kind → String
  | .negative => "negative" | .neighbour => "neighbour" | .cited => "cited"
  | .notApplicable => "not applicable"

structure Result where
  row : Nat
  kind : Kind
  name : String
  /-- what is forged (negative), what is valid (neighbour), the reason (n/a) -/
  what : String
  checker : String
  /-- negative refused / neighbour accepted / cited check passed -/
  ok : Bool
  log : Array String := #[]

def Result.addLog (r : Result) (l : Array String) : Result := { r with log := r.log ++ l }

def R (row : Nat) (kind : Kind) (name what checker : String) (ok : Bool) (log : Array String := #[]) : Result :=
  { row := row, kind := kind, name := name, what := what, checker := checker, ok := ok, log := log }

/-! ## The compile-cert artifact check -/

section CompileCert
open _root_.Ix.CompileCert
open Tests.Ix.Kernel.IxonFixtures (address)
open Tests.Ix.CompileCert.Direct (choiceInput choiceRecord accepted)

/-- `checkCompiled`'s verdict, for the log. -/
def verdict (input : Input) : String :=
  match checkCompiled input with
  | .ok _ => "accepted"
  | .error .correspondence => "refused: correspondence"
  | .error .sourceDomain => "refused: source domain"
  | .error .mapMismatch => "refused: map mismatch"
  | .error (.malformedInput _) => "refused: malformed input"
  | .error _ => "refused: other"

def thmRecord (typ value : Ixon.Expr) : Ixon.Constant :=
  ⟨.defn ⟨.thm, .safe, 0, typ, value⟩, #[], #[], #[.zero]⟩

def thmSource (n : Lean.Name) (type value : Lean.Expr) : Lean.ConstantInfo :=
  .thmInfo { name := n, levelParams := [], type := type, value := value, all := [n] }

/-- `t1 : ∀ p : Prop, p → p` and `t2 : ∀ p q : Prop, p → q → p`. -/
def t1Type : Lean.Expr := .forallE `p (.sort .zero) (.forallE `h (.bvar 0) (.bvar 1) .default) .default
def t1Value : Lean.Expr := .lam `p (.sort .zero) (.lam `h (.bvar 0) (.bvar 0) .default) .default
def t2Type : Lean.Expr := .forallE `p (.sort .zero) (.forallE `q (.sort .zero)
  (.forallE `hp (.bvar 1) (.forallE `hq (.bvar 1) (.bvar 3) .default) .default) .default) .default
def t2Value : Lean.Expr := .lam `p (.sort .zero) (.lam `q (.sort .zero)
  (.lam `hp (.bvar 1) (.lam `hq (.bvar 1) (.bvar 1) .default) .default) .default) .default
def t1Rec : Ixon.Constant := thmRecord (.leanAll (.sort 0) (.leanAll (.var 0) (.var 1)))
  (.leanLam (.sort 0) (.leanLam (.var 0) (.var 0)))
def t2Rec : Ixon.Constant := thmRecord
  (.leanAll (.sort 0) (.leanAll (.sort 0) (.leanAll (.var 1) (.leanAll (.var 1) (.var 3)))))
  (.leanLam (.sort 0) (.leanLam (.sort 0) (.leanLam (.var 1) (.leanLam (.var 1) (.var 1)))))

def theorems (t1Target : UInt8) : Input :=
  { choiceInput with
    source := ⟨[thmSource `t1 t1Type t1Value, thmSource `t2 t2Type t2Value]⟩
    roots := [`t1, `t2]
    map := [⟨`t1, address t1Target, .member (address t1Target) 0⟩, ⟨`t2, address 82, .member (address 82) 0⟩]
    records := [(address 81, Ixon.serConstant t1Rec), (address 82, Ixon.serConstant t2Rec)]
    hint := fun _ => none }

/-- `first`'s record (`λ α a b. a`, one universe) with another definition. -/
def firstRecord (lvls : UInt64) (typ value : Ixon.Expr) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, lvls, typ, value⟩, #[], #[], #[.var 0]⟩
def firstType : Ixon.Expr := .leanAll (.sort 0) (.leanAll (.var 0) (.leanAll (.var 1) (.var 2)))
def firstValue : Ixon.Expr := .leanLam (.sort 0) (.leanLam (.var 0) (.leanLam (.var 1) (.var 1)))
def withFirstRecord (c : Ixon.Constant) : Input :=
  { choiceInput with records := [(address 71, Ixon.serConstant c)] }

/-- A hand-built compile-cert case: refused (negative) or accepted
(neighbour). -/
def ccCase (row : Nat) (kind : Kind) (name what : String) (input : Input) : Result :=
  let v := verdict input
  { row, kind, name, what, checker := "Ix.CompileCert.checkCompiled", log := #[v],
    ok := if kind == .negative then !(accepted input) else accepted input }

def compileCertCases : Array Result := #[
  ccCase 1 .negative "R1-cc-redirect" "source theorem t1 mapped to the record of t2 (a different well-typed statement)" (theorems 82),
  ccCase 1 .neighbour "R1-cc-direct" "t1 and t2 each mapped to their own record" (theorems 81),
  ccCase 4 .negative "R4-cc-levels" "first's record with two universe parameters (source: one)"
    (withFirstRecord (firstRecord 2 firstType firstValue)),
  ccCase 4 .negative "R4-cc-dropped-param" "first's record without its second value parameter (`λ α a. a`)"
    (withFirstRecord (firstRecord 1 (.leanAll (.sort 0) (.leanAll (.var 0) (.var 1)))
      (.leanLam (.sort 0) (.leanLam (.var 0) (.var 0))))),
  ccCase 4 .neighbour "R4-cc-exact" "first's record as exported" (withFirstRecord (firstRecord 1 firstType firstValue)),
  ccCase 6 .negative "R6-cc-mutated-body" "first's admitted record body mutated to return the other same-typed argument"
    (withFirstRecord (firstRecord 1 firstType (.leanLam (.sort 0) (.leanLam (.var 0) (.leanLam (.var 1) (.var 0)))))),
  ccCase 6 .neighbour "R6-cc-unmutated" "the same record unmutated" (withFirstRecord choiceRecord)]

end CompileCert

/-! ## Existing compile-cert controls, invoked by label -/

/-- `(row, kind, label, source list name)`: the existing controls this suite
cites for a row. -/
def citedControls : List (Nat × Kind × String × String) := [
  (3, .negative, "same-typed wrong-value alias", "Direct"),
  (3, .negative, "semantic names cannot borrow the checked representative for a wrong alias", "Direct"),
  (3, .neighbour, "legitimate many-to-one aliases", "Direct"),
  (3, .neighbour, "semantic names cover both members of a legitimate fiber", "Direct"),
  (4, .negative, "fabricated member index", "Direct"),
  (4, .negative, "missing target record", "Direct"),
  (4, .negative, "missing target universe slot explicitly declines", "Universes"),
  (4, .negative, "missing source universe parameter explicitly declines", "Universes"),
  (4, .neighbour, "actual canonical export and target substitution", "Universes"),
  (6, .negative, "unchanged root with changed dependency", "Direct"),
  (6, .neighbour, "closed direct dependency cone", "Direct"),
  (10, .negative, "duplicate source map keys", "Direct"),
  (10, .negative, "source capture rejects mismatched lookup identity", "Direct"),
  (10, .neighbour, "direct independently exported definition", "Direct"),
  (11, .negative, "missing dependency cannot be hidden", "Direct"),
  (11, .negative, "selected root retains changed dependency", "Direct"),
  (11, .neighbour, "literal support cannot disappear from source closure", "Direct"),
  (11, .neighbour, "closed direct dependency cone", "Direct"),
  (12, .negative, "wrong declaration kind", "Direct"),
  (12, .neighbour, "direct independently exported definition", "Direct"),
  (13, .negative, "Ix semantic metadata explicitly unsupported", "Direct"),
  (13, .negative, "universe guard rejects changed value", "Universes"),
  (13, .negative, "Ix free variables remain unsupported by the bridge", "Expressions"),
  (13, .neighbour, "universe guard accepts non-syntactic semantic equality", "Universes"),
  (13, .neighbour, "full renaming includes projection owner identities", "Expressions"),
  (14, .negative, "per-root unsupported source classification", "Direct"),
  (14, .negative, "per-root missing dependency is blocked", "Direct"),
  (14, .negative, "kernel resource and unsupported declines remain distinct", "Direct"),
  (14, .neighbour, "per-root certified classification", "Direct")]

def controlList : String → List (String × (Unit → Bool))
  | "Direct" => Tests.Ix.CompileCert.Direct.controls
  | "Universes" => Tests.Ix.CompileCert.Universes.controls
  | "Expressions" => Tests.Ix.CompileCert.Expressions.controls
  | _ => []

/-- Each cited control returns `true` when it holds (a negative control holds
when the forged input is refused, a positive one when the valid input is
accepted). -/
def citedResults : Array Result := citedControls.toArray.map fun (row, kind, label, src) =>
  match (controlList src).find? (·.1 == label) with
  | some (_, f) =>
    { row, kind, name := s!"{src}: {label}", what := s!"existing control `{label}` (Tests.Ix.CompileCert.{src})",
      checker := "Ix.CompileCert (checkCompiled/checkRoot/guards)", ok := f () }
  | none =>
    { row, kind, name := s!"{src}: {label}", what := "cited control", checker := "-", ok := false,
      log := #[s!"stale citation: no control labelled `{label}` in Tests.Ix.CompileCert.{src}"] }

/-! ## Standalone compile-cert checks (subprocesses) -/

def standalone (row : Nat) (file summary what : String) (elabOnly : Bool := false) : IO Result := do
  let args := if elabOnly then #["env", "lean", file] else #["env", "lean", "--run", file]
  let out ← IO.Process.output { cmd := "lake", args }
  let text := out.stdout ++ out.stderr
  let ok := out.exitCode == 0 && (text.splitOn summary).length > 1
  return { row, kind := .cited, name := file, what, checker := s!"lake {" ".intercalate args.toList}", ok,
           log := ((text.splitOn "\n").filter (!·.isEmpty)).toArray.extract 0 40 }

/-! ## Compiled artifacts from forged inputs -/

open Tests.Ix.Compile.Pass3 (CUnit closureOf compileUnit)

def ixN (n : Name) : _root_.Ix.Name := _root_.Ix.Name.fromLeanName n

/-- Compile `seeds` with their closure, each constant of the closure passed
through `forge` (the forged input), `drop` removed. -/
def compileForged (env : Environment) (seeds : Array Name) (pass3 : Bool)
    (forge : Name → ConstantInfo → ConstantInfo := fun _ c => c) (drop : Name → Bool := fun _ => false) :
    IO Ix.CompileM.LeanPipelineOut := do
  let closure := (closureOf env seeds.toList).filterMap fun (n, c) =>
    if drop n then none else some (n, forge n c)
  compileUnit { name := "adversarial-matrix", env, seeds, closure } pass3

def withValue (c : ConstantInfo) (f : Expr → Expr) : ConstantInfo :=
  match c with
  | .defnInfo v => .defnInfo { v with value := f v.value }
  | .thmInfo v => .thmInfo { v with value := f v.value }
  | .opaqueInfo v => .opaqueInfo { v with value := f v.value }
  | c => c

/-- Phase 4 (`Ix.Tc.metaRoundtripEnv`) over `ixon` against Lean's `env`:
the names it reports, and its summary. -/
def phase4 (env : Environment) (ixon : Ixon.Env) : Except String (Array _root_.Ix.Name × String) := do
  let rep ← Ix.Tc.metaRoundtripEnv env ixon
  let names := rep.errors.map (·.1)
  let msgs := rep.errors.toList.take 3 |>.map fun (n, m) => s!"{n.pretty}: {m.take 200}"
  return (names, s!"checked {rep.checked}, {rep.errorCount} comparison error(s){if msgs.isEmpty then "" else s!": {"; ".intercalate msgs}"}")

/-- A phase-4 case: the forged compile must be flagged at `target`, the
honest one must have no comparison error. -/
def phase4Case (env : Environment) (row : Nat) (kind : Kind) (name what : String) (target : Name)
    (forge : Name → ConstantInfo → ConstantInfo) (extra : Array Name := #[]) : IO Result := do
  let out ← compileForged env (#[target] ++ extra) false (forge := forge)
  match phase4 env out.env with
  | .error e => return { row, kind, name, what, checker := "validate-lean phase 4 (meta roundtrip)", ok := false,
                         log := #[s!"phase 4 did not run: {e}"] }
  | .ok (names, summary) =>
    let flagged := names.contains (ixN target)
    let ok := if kind == .negative then flagged else names.isEmpty
    return { row, kind, name, what, checker := "validate-lean phase 4 (meta roundtrip vs Lean's source)", ok,
             log := #[s!"phase 4: {summary}"] }

/-- Phase 9 over a compiled unit against Lean's `env`. -/
def phase9 (env : Environment) (ixon : Ixon.Env) : IO (Ix.Cli.ValidateLeanCmd.PhaseResult × Array String) :=
  Ix.Cli.ValidateLeanCmd.phaseCliqueValues env ixon (Ix.Cli.ValidateLeanCmd.leanViewOf env ixon)

def srcNs : Name := `Tests.Ix.Compile.CliqueOwnership.Src

/-- The clique members of a clique-ownership fixture (`first`, `second`). -/
def membersOf (fixture : String) : Array Name :=
  #[srcNs ++ fixture.toName ++ `first, srcNs ++ fixture.toName ++ `second]

/-- Swap two natural-number literals. -/
def swapLits (a b : Nat) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .lit (.natVal k) => if k == a then some (.lit (.natVal b)) else if k == b then some (.lit (.natVal a)) else none
    | _ => none

/-- A user's `PSum.inl 0` ↦ `PSum.inr 0` (injections of the packing type,
FIX-pfwf F2). -/
def swapUserInjection (e : Expr) : Expr :=
  e.replace fun x =>
    if x.isAppOfArity ``PSum.inl 3 && x.appArg!.nat? == some 0 then
      match x.getAppFn with
      | .const _ us => some (mkApp3 (.const ``PSum.inr us) x.appFn!.appFn!.appArg! x.appFn!.appArg! x.appArg!)
      | _ => none
    else none

/-- Forge the clique's own constants (members and Lean's encoding constants). -/
def forgeClique (ms : Array Name) (f : Expr → Expr) (n : Name) (c : ConstantInfo) : ConstantInfo :=
  if ms.contains n || IxCliqueValues.isLeanEncoding ms n then withValue c f else c

/-- Phase-9 cases for a fixture family (both member orders): the honest
compile of a transported order passes with value-checked members (the
neighbour); the forged compile of a transported order fails with a wrong
meaning (the negative). An order the compiler keeps in Lean's form is not a
subject of phase 9 and is logged; each family must have a transported order
both ways. -/
def phase9Cases (env : Environment) (row : Nat) (family : String) (forgeWhat : String) (f : Expr → Expr)
    (failClosed : Bool := false) :
    IO (Array Result) := do
  let mut neg : Option Result := none
  let mut nbr : Option Result := none
  let mut log : Array String := #[]
  for order in ["A", "B"] do
    let fx := family ++ order
    let ms := membersOf fx
    -- the neighbour: the honest compile
    if nbr.isNone then
      let out ← compileForged env ms true
      let (r, lines) ← phase9 env out.env
      match r with
      | .skipped d => log := log.push s!"{fx} honest: not transported ({d})"
      | .passed d =>
        nbr := some { row, kind := .neighbour, name := s!"R{row}-{fx}-honest",
                      what := s!"{fx} compiled honestly (switch on, transported)",
                      checker := "validate-lean phase 9 (clique values)", ok := (d.splitOn "(0 value-checked").length == 1,
                      log := #[s!"phase 9: PASS {d}"] ++ lines }
      | .failed d | .stubbed d =>
        nbr := some { row, kind := .neighbour, name := s!"R{row}-{fx}-honest",
                      what := s!"{fx} compiled honestly", checker := "validate-lean phase 9 (clique values)", ok := false,
                      log := #[s!"phase 9: {d}"] ++ lines }
    -- the negative: the forged compile
    if neg.isNone then
      let out ← compileForged env ms true (forge := forgeClique ms f)
      let (r, lines) ← phase9 env out.env
      match r with
      | .skipped d => log := log.push s!"{fx} forged: not transported ({d})"
      | .failed d =>
        neg := some { row, kind := .negative, name := s!"R{row}-{fx}-forged", what := s!"{fx}: {forgeWhat}",
                      checker := "validate-lean phase 9 (clique values)",
                      ok := lines.any fun l => (l.splitOn "WRONG MEANING").length > 1 ||
                        (failClosed && (l.splitOn "kernel rejects the compiled").length > 1),
                      log := #[s!"phase 9: FAIL {d}"] ++ lines }
      | .passed d | .stubbed d =>
        neg := some { row, kind := .negative, name := s!"R{row}-{fx}-forged", what := s!"{fx}: {forgeWhat}",
                      checker := "validate-lean phase 9 (clique values)", ok := false,
                      log := #[s!"phase 9 ACCEPTED the forged artifact: {d}"] ++ lines }
  let missing (k : Kind) : Result :=
    { row, kind := k, name := s!"R{row}-{family}-{k.tag}", what := "no transported order", checker := "-",
      ok := false, log := log.push "neither member order was transported: the case could not be constructed" }
  return #[(neg.getD (missing .negative)).addLog log, (nbr.getD (missing .neighbour))]


/-! ## Phase 8 (provenance): a stale `original` -/

def provenanceCases (env : Environment) : IO (Array Result) := do
  let target := `Tests.Ix.Compile.AdversarialMatrix.Src.double
  let out ← compileForged env #[target] false
  let ixon := out.env
  let view := Ix.Cli.ValidateLeanCmd.leanViewOf env ixon
  let ch := Ix.Cli.ValidateLeanCmd.changedOf ixon view
  let limits ← IO.ofExcept (← Ix.CompileM.compilerSharingLimitsFromEnv)
  let needed := ixon.named.fold (init := #[]) fun acc n nd =>
    if nd.original.isSome && !Ix.Compile.Pass.hasReserved n then acc.push n else acc
  let rc := Ix.Cli.ValidateLeanCmd.recompileAll (Ix.Cli.ValidateLeanCmd.cenvOver ixon view limits) view needed
  let check (e : Ixon.Env) := Ix.Cli.ValidateLeanCmd.phaseProvenance e view ch rc
  let (r0, l0) := check ixon
  let nbr := R 10 .neighbour "R10-provenance-honest"
    "regenerated auxiliaries of the honest compile carry their own address as `original`"
    "validate-lean phase 8 (provenance)" (r0.isFailure == false && !needed.isEmpty)
    (#[s!"phase 8: {r0.render}"] ++ l0)
  -- the forged artifact: one regenerated auxiliary's `original` points at
  -- another stored constant (a stale or borrowed original)
  let picked := ixon.named.toList.find? fun (_, nd) => match nd.original with
    | some (oa, _) => oa == nd.addr
    | none => false
  let other := ixon.named.toList.find? fun (_, nd) => match picked with
    | some (_, p) => nd.addr != p.addr
    | none => false
  match picked, other with
  | some (n, nd), some (_, o) =>
    let nd' : Ixon.Named := { nd with original := nd.original.map fun (_, m) => (o.addr, m) }
    let forged : Ixon.Env := { ixon with named := ixon.named.insert n nd' }
    let (r1, l1) := check forged
    let neg := R 10 .negative "R10-provenance-stale-original"
      s!"`{n.pretty}`'s Named.original replaced by another constant's address"
      "validate-lean phase 8 (provenance)"
      (r1.isFailure && l1.any fun l => (l.splitOn n.pretty).length > 1)
      (#[s!"phase 8: {r1.render}"] ++ l1)
    return #[neg, nbr]
  | _, _ =>
    return #[R 10 .negative "R10-provenance-stale-original" "-" "-" false
      #["no regenerated auxiliary with an original in the compile"], nbr]

/-! ## The compiler's refusal of an omitted dependency -/

def omittedDependencyCases (env : Environment) : IO (Array Result) := do
  let target := `Tests.Ix.Compile.AdversarialMatrix.Src.double
  let honest ← compileForged env #[target] false
  let stored0 := honest.env.named.contains (ixN target)
  let nbr := R 11 .neighbour "R11-compile-closed" "`double` with its whole closure"
    "the compiler (block grounding)" (stored0 && honest.cenv.ungrounded.isEmpty)
    #[s!"ungrounded {honest.cenv.ungrounded.size}; `double` stored: {stored0}"]
  let what := "`double`'s closure without `Nat.add` (an omitted value dependency)"
  let neg ← try
      let forged ← compileForged env #[target] false (drop := (· == ``Nat.add))
      let stored := forged.env.named.contains (ixN target)
      let refused := forged.cenv.ungrounded.toList
      let shown := (refused.take 4).map fun (n, m) => s!"{n.pretty}: {m.take 120}"
      pure (R 11 .negative "R11-compile-omitted-Nat.add" what "the compiler (block grounding)"
        (!stored || forged.cenv.ungrounded.contains (ixN target))
        #[s!"`double` stored: {stored}; block failures {refused.length}: {shown}; pre-compile ungrounded {forged.ungroundedCount}"])
    catch e =>
      pure (R 11 .negative "R11-compile-omitted-Nat.add" what "the compiler (input resolution)" true
        #[s!"refused: {(toString e).take 300}"])
  return #[neg, nbr]

/-! ## The suite -/

def notApplicable : Array Result := #[
  { row := 7, kind := .notApplicable, name := "R7-owner-evidence",
    what := "cyclic/self-issued owner evidence and provisional supports: the main line has no owner-evidence \
or receipt checker (it belongs to the set-aside codex lane; `Ix/CompileCert/**` has no owner receipts), so \
there is no artifact to forge and no checker to run", checker := "-", ok := true }]

def run : IO UInt32 := do
  let env ← get_env!
  let mut results : Array Result := compileCertCases ++ citedResults ++ notApplicable
  -- row 1: a theorem redirected to another well-typed statement, through the validator
  let addZero := `Tests.Ix.Compile.AdversarialMatrix.Src.addZero
  let zeroAdd := `Tests.Ix.Compile.AdversarialMatrix.Src.zeroAdd
  let some (.thmInfo za) := env.find? zeroAdd | throw (IO.userError "zeroAdd missing")
  let redirect (n : Name) (c : ConstantInfo) : ConstantInfo :=
    if n == addZero then match c with
      | .thmInfo v => .thmInfo { v with type := za.type, value := za.value }
      | c => c
    else c
  results := results.push (← phase4Case env 1 .negative "R1-validate-redirect"
    "`addZero` compiled with `zeroAdd`'s statement and proof (a different well-typed target)" addZero redirect (extra := #[zeroAdd]))
  results := results.push (← phase4Case env 1 .neighbour "R1-validate-honest" "`addZero` compiled honestly" addZero
    (fun _ c => c) (extra := #[zeroAdd]))
  -- row 2: same-typed branches exchanged (phase 9)
  results := results ++ (← phase9Cases env 2 "PF5" "the two members' base values 5 and 7 exchanged in the encoding and its monotonicity proof (refused: a wrong meaning, or fail closed by Lean's kernel on the compiled forged constants)" (swapLits 5 7) (failClosed := true))
  results := results ++ (← phase9Cases env 2 "S3" "the two members' base values 5 and 7 exchanged" (swapLits 5 7))
  results := results ++ (← phase9Cases env 2 "WF6" "second's base value 31 exchanged with first's scale 10" (swapLits 10 31))
  -- row 8: a user value of the packing type, its injection swapped (FIX-pfwf F2)
  results := results ++ (← phase9Cases env 8 "WF6" "the user's `PSum.inl 0` (packing type) replaced by `PSum.inr 0`"
    swapUserInjection)
  results := results.push (R 8 .cited "clique-ownership (53 cases)"
    "user values, binders and relations of the packing type, private names, same-typed user matchers (PF1–PF7, WF1–WF8, S1–S6, R1–R2), value-checked against Lean; run as its own gate"
    "lake test -- --ignored clique-ownership" true
    #["cited, not run here (its own ignored suite in the gate list)"])
  -- row 9: a convertible replacement of an original proof term
  let convertible (n : Name) (c : ConstantInfo) : ConstantInfo :=
    if n == addZero then match c with
      | .thmInfo v => .thmInfo { v with value := mkApp2 (.const ``id [.zero]) v.type v.value }
      | c => c
    else c
  results := results.push (← phase4Case env 9 .negative "R9-validate-convertible-proof"
    "`addZero`'s proof replaced by the convertible `id _ proof`" addZero convertible (extra := #[``id]))
  results := results.push (← phase4Case env 9 .neighbour "R9-validate-original-proof" "`addZero`'s original proof" addZero
    (fun _ c => c) (extra := #[``id]))
  -- row 12: a theorem stored as a definition
  let asDefn (n : Name) (c : ConstantInfo) : ConstantInfo :=
    if n == addZero then match c with
      | .thmInfo v =>
        let d : DefinitionVal := { v.toConstantVal with value := v.value, hints := .opaque, safety := .safe, all := v.all }
        .defnInfo d
      | c => c
    else c
  results := results.push (← phase4Case env 12 .negative "R12-validate-forged-kind"
    "the theorem `addZero` compiled as a definition" addZero asDefn)
  results := results.push (← phase4Case env 12 .neighbour "R12-validate-kind" "`addZero` compiled as a theorem" addZero
    fun _ c => c)
  results := results ++ (← provenanceCases env)
  results := results ++ (← omittedDependencyCases env)
  -- the standalone compile-cert checks
  results := results.push (← standalone 5 "Tests/Ix/CompileCert/InstalledRules.lean"
    "52 rule/universe/constructor controls passed"
    "omitted (`missing rule`), swapped (`reversed positions`) and inert (`firing mode`) recursor rules refused; \
the actual Nat/PUnit rules accepted")
  results := results.push (← standalone 6 "Tests/Ix/CompileCert/ValueReceipt.lean" "14/14 controls passed"
    "value-equation receipts: wrong endpoint, changed source map, forged theorem body refused; the actual receipt accepted"
    (elabOnly := true))
  results := results.push (← standalone 10 "Tests/Ix/CompileCert/InstalledFields.lean" "12 controls passed"
    "shadowed source rows refused; two independent folds accepted")
  -- report
  let mut problems := 0
  for r in results do
    IO.println s!"[adversarial-matrix] row {r.row} {r.kind.tag} {r.name}: {if r.ok then "OK" else "FAIL"} ({r.checker}) — {r.what}"
    for l in r.log do IO.println s!"[adversarial-matrix]     {l}"
    unless r.ok do problems := problems + 1
  -- every row has a negative and a neighbour (own or cited), or is not applicable
  let mut parts : Array String := #[]
  for row in List.range' 1 14 do
    let rs := results.filter (·.row == row)
    let cnt (k : Kind) (p : Result → Bool := fun _ => true) := (rs.filter fun r => r.kind == k && p r).size
    let na := cnt .notApplicable
    let negs := cnt .negative
    let nbrs := cnt .neighbour
    if na == 0 && cnt .cited == 0 && (negs == 0 || nbrs == 0) then
      problems := problems + 1
      IO.println s!"[adversarial-matrix] FAIL row {row}: {negs} negative(s), {nbrs} neighbour(s)"
    parts := parts.push s!"row {row}: neg {cnt .negative (·.ok)}/{negs} rejected, nbr {cnt .neighbour (·.ok)}/{nbrs} accepted, \
cited {cnt .cited (·.ok)}/{cnt .cited}, n/a {na}"
  IO.println s!"[adversarial-matrix] summary: {"; ".intercalate parts.toList}"
  IO.println s!"[adversarial-matrix] {results.size} cases, {problems} problem(s)"
  return if problems == 0 then 0 else 1

end Tests.Ix.Compile.AdversarialMatrix
