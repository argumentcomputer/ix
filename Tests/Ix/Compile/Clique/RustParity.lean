/-
  clique-rust-parity: the Rust clique transport library
  (`crates/compile/src/compile/pass3/clique`) against the Lean one
  (`Ix.Compile.Pass.Clique`), on the plan of a clique and its rows. Neither
  is wired into a compiler yet, so this suite is the libraries' lockstep
  evidence (the wiring adds whole-compile parity).

  * **Bounds.** Rust's `bounds()` (test-only FFI `rs_clique_bounds`,
    `crates/ffi/src/clique.rs`) equals Lean's `bounds`: names and values, in
    order.
  * **Plans.** For every clique of the library suites' fixtures (the clique
    twins, `Tests/Ix/Compile/Twins/Cliques.lean`, the library's own,
    `Tests/Ix/Compile/Clique/Fixtures.lean`, and the ownership suite's,
    `Tests/Ix/Compile/Clique/Ownership/{Sources,Lemmas}.lean`, loaded at run
    time with the twins: Lean's `EqnInfo` cliques and the theorem cliques), with the
    members' equation lemmas realised (`eq_def`, `eq_<k>`), with and without
    the carried lemmas (the clique table's: the members' equation lemmas that
    reference a member and one of Lean's encoding constants), under a
    name-hash and a content address: Lean's `planClique` against Rust's
    `plan_clique` (`rs_clique_plan`). Lean reads the whole input; the Rust
    side receives the clique's closure only: the members, the carried lemmas
    and the constants the library reads by name (the encoding's
    `all₀._mutual`, `all₀.mutual`, `m._f`, and `transportPrereqs`, e.g.
    `monotone_compose`), then everything their types and values mention,
    transitively through the values of the constants under the clique's
    namespace and through the types of every other constant, with each
    inductive's block, constructors and recursors and its
    `below`/`brecOn`/`casesOn` family (what `authenticatedFamily`,
    `filterHeads` and the structural transport read; their values
    followed). When Lean transports the clique, the closure also carries
    the library constants Lean's transported constants mention (the
    composition fallback's monotonicity lemmas, which `planClique` requires
    in the input), through their types; a constant only Rust's transport
    would introduce stays absent. The address lookup is Lean's restricted to
    the names the closure mentions. A constant or an address the Rust side
    needs outside the closure therefore shows up as a difference, never as
    agreement.
  * **Adversarial plans.** The inputs of `clique-recognition` that reach
    `planClique`: the `SA` cliques over an altered `Nat.brecOn`, and the
    decoy `m._f`s beside the functionals the members pass (`SA`/`SP`, both
    decoy kinds), as overlays of the environment.
  * **Rows.** For every plan Lean transports (each case, both addresses):
    Lean's `rowsOf` over its input against Rust's `rows_of` over Rust's own
    plan of the same closure (`rs_clique_rows`): the refusal text, or the
    copies and the rows in order, each record compared raw-exactly (kind,
    name, level parameters, type, value, hints, safety, `all`). A
    well-founded plan has copies and rows; a plan of another encoding none,
    on both sides.

  Every field of the outcome is compared raw-exactly: the tag, the reason,
  the encoding and cause tags, the order source (tag and description); for a
  transported clique `all`, `σ`, the classes, the members (by name), the
  canonical constants with their Lean sources, the functionals, the causes
  (constant, tag, reason), the aliases and the side-car record. Names
  compare structurally (`RawExact.nameEq`, cached addresses included),
  expressions by their content hash and structurally (`RawExact.exprEq`),
  strings exactly.

  Verdicts: `SAME`; `DIFF` (the first differing field, both values
  truncated); `RUST-ERR` (the FFI refused its input); `ERROR` (the case did
  not run). Lean's `planClique` is total and cannot fail. The comparison's
  control: on every transported plan found `SAME`, Rust's outcome with one
  field perturbed (a canonical constant's value, a member's value, the
  record) must be `DIFF` at that field; on every rows comparison found
  `SAME`, Rust's copies and rows with one field perturbed (the first copy's
  value, the first row's value, the first row's `all`; a refusal's text)
  likewise. The run passes iff the bounds agree, every plan and every rows
  comparison is `SAME` and every control is found; it prints the counts by
  outcome and encoding, and the rows' counts.

  Invoked as `lake test -- clique-rust-parity`.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Image.RawExact
import Ix.Compile.Pass.Clique
import Tests.Ix.Compile.Clique.Common
import Tests.Ix.Compile.Clique.Transport
import Tests.Ix.Compile.Clique.Recognition

open Lean Meta

namespace Tests.Ix.Compile.Clique.RustParity

open Tests.Ix.Compile.Clique.Common
open _root_.Ix.Compile.Pass.Clique (Decl CliqueOutcome CliquePlan constOccurrences foldDistinct
  renameConsts memberEqLemmas isEncodingName)

private def say (s : String) : IO Unit := IO.println s!"[clique-rust-parity] {s}"

/-! ## The Rust side (test-only FFI, `crates/ffi/src/clique.rs`) -/

/-- A Rust declaration (`clique::basic::Decl`). Layout: four object fields,
then `isThm` as a byte. -/
structure RsDecl where
  name : IxName
  levelParams : Array IxName
  type : IxExpr
  value : IxExpr
  isThm : Bool
  deriving Inhabited

/-- Rust's `CliqueOutcome` as plain data (fifteen object fields, no
scalars). The fields a variant does not have are empty. -/
structure RsOutcome where
  /-- 0 notEncoded, 1 unchanged, 2 baseline, 3 transported -/
  tag : Nat
  /-- notEncoded and baseline: the reason -/
  reason : String
  /-- unchanged, baseline, transported: `Encoding.tag` -/
  encoding : String
  /-- baseline: `Cause.tag` -/
  cause : String
  all : Array IxName
  sigma : Array Nat
  classes : Array (Array IxName)
  /-- unchanged and transported: `OrderSource.tag` -/
  sourceTag : String
  /-- unchanged and transported: `OrderSource.describe` -/
  sourceDescribe : String
  /-- the member map, in pretty-name order -/
  members : Array RsDecl
  canon : Array (RsDecl × IxName)
  functionals : Array IxName
  /-- constant, `Cause.tag`, reason -/
  causes : Array (IxName × String × String)
  aliases : Array (IxName × IxName)
  /-- `CliquePlan.record` -/
  record : String
  deriving Inhabited

/-- Rust's `plan_clique` over exactly the given constants (a name absent
from them is absent to it) and addresses (a name absent from them has
none). The error is a decoding failure. -/
@[extern "rs_clique_plan"]
opaque rsCliquePlan : @& Array IxConst → @& Array (IxName × Address) → @& Array IxName →
  @& Array IxName → Except String RsOutcome

/-- Rust's `bounds()`, by Lean name, in order. -/
@[extern "rs_clique_bounds"]
opaque rsCliqueBounds : Unit → Array (String × Nat)

/-- Rust's `rows_of` (the copies, then the rows) of its own plan of a clique,
over the same input as `rsCliquePlan`. The error is a decoding failure, a
plan that is not transported (`rs_clique_rows: …`) or the rows' refusal. -/
@[extern "rs_clique_rows"]
opaque rsCliqueRows : @& Array IxConst → @& Array (IxName × Address) → @& Array IxName →
  @& Array IxName → Except String (Array IxConst × Array IxConst)

/-! ## The cliques -/

/-- The fixtures' roots: the clique twins, the library's own fixtures and the
ownership suite's sources and lemma cliques. -/
def roots : List Name :=
  [`Tests.Ix.Compile.Twins.Cliques, fixturesRoot, `Tests.Ix.Compile.Clique.Ownership.Src,
   `Tests.Ix.Compile.Clique.Ownership.Lem]

def userName (n : Name) : Name := (Lean.privateToUserName? n).getD n

def underRoots (n : Name) : Bool := roots.any (·.isPrefixOf (userName n))

/-- Every clique of two or more members under the roots, in Lean's order:
the `EqnInfo` cliques (`declNames`) and the theorem cliques (`all`), each
once, by the first member in `Name.quickLt` order. -/
def cliques (env : Environment) : Array (Array Name) := Id.run do
  let eqn := Tests.Ix.Compile.Clique.Transport.eqnCliques env
  let names := (env.constants.fold (init := #[]) fun acc n _ =>
    if underRoots n then acc.push n else acc).qsort Name.quickLt
  let mut seen : Std.HashSet Name := {}
  let mut out : Array (Array Name) := #[]
  for n in names do
    if seen.contains n then continue
    let some ci := env.find? n | continue
    let order? : Option (Array Name) := match eqn.get? n with
      | some (_, ms) => some ms
      | none => match ci with
        | .thmInfo v => if v.all.length ≥ 2 then some v.all.toArray else none
        | _ => none
    let some order := order? | continue
    if order.size < 2 then continue
    for a in order do seen := seen.insert a
    out := out.push order
  return out

/-- The fixtures' environment with the members' equation lemmas realised
(`m.eq_def`, and `m.eq_<k>`), and how many were asked for successfully. -/
def withEqLemmas (env : Environment) (cls : Array (Array Name)) : IO (Environment × Nat) := do
  let act : MetaM (Environment × Nat) := do
    let mut n := 0
    for ms in cls do
      for m in ms do
        let some (.defnInfo _) := (← getEnv).find? m | continue
        for s in ["eq_def", "eq_1"] do
          try
            discard <| realizeGlobalConstNoOverloadCore (Name.str m s)
            n := n + 1
          catch _ => pure ()
    return ((← getEnv), n)
  let ctx : Core.Context := { fileName := "<clique-rust-parity>", fileMap := default,
                              maxHeartbeats := 0 }
  Prod.fst <$> act.toIO ctx { env }

/-- A definition, theorem or opaque's value. -/
def valueOf' : IxConst → Option IxExpr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants a constant's type and value mention. -/
def refsOf (ci : IxConst) : Array IxName :=
  constOccurrences (fun _ => true) ci.getCnst.type ++
    ((valueOf' ci).map (constOccurrences fun _ => true)).getD #[]

/-- The clique table's carried lemmas of a clique: the members' equation
lemmas (`memberEqLemmas`) that reference a member and one of Lean's encoding
constants of the clique, in pretty-name order. -/
def carriedOf (const? : IxName → Option IxConst) (all : Array IxName) : Array IxName :=
  let found := all.foldl (init := #[]) fun acc m =>
    (memberEqLemmas const? {} m).foldl (init := acc) fun acc c =>
      match const? c with
      | some ci =>
        let rs := refsOf ci
        if rs.any (isEncodingName all ·) && rs.any all.contains then acc.push c else acc
      | none => acc
  found.qsort fun a b => a.pretty < b.pretty

/-! ## The closure the Rust side receives -/

/-- `n` is under the namespace `ns` (by its user name, for a private name). -/
def isUnder (ns : Name) (n : IxName) : Bool := ns.isPrefixOf (userName (toLeanName n))

/-- The `below`/`brecOn` family and the eliminators of an inductive block,
which the library reads by name (missing names are skipped by the walk). -/
def familyOf (iv : _root_.Ix.InductiveVal) : Array IxName :=
  let mk := _root_.Ix.Name.mkStr
  let heads := iv.all.flatMap fun a =>
    #[mk a "below", mk a "brecOn", mk a "casesOn", mk a "recOn", mk a "binductionOn", mk a "ibelow"]
  let nested : Array IxName := match iv.all[0]? with
    | some a0 => (List.range iv.numNested).toArray.flatMap fun k =>
      #[mk a0 s!"below_{k + 1}", mk a0 s!"brecOn_{k + 1}", mk a0 s!"binductionOn_{k + 1}",
        mk a0 s!"ibelow_{k + 1}"]
    | none => #[]
  let hs := heads ++ nested
  hs ++ hs.flatMap fun h => #[mk h "go", mk h "eq"]

/-- The names a constant brings into the closure, each with whether its
value is followed whatever its namespace (an inductive's family). A
definition's value is followed when `deep`. -/
def neighbours (deep : Bool) : IxConst → Array (IxName × Bool)
  | .inductInfo iv =>
    let recs := iv.all.map (_root_.Ix.Name.mkStr · "rec") ++ match iv.all[0]? with
      | some a0 => (List.range iv.numNested).toArray.map fun k => _root_.Ix.Name.mkStr a0 s!"rec_{k + 1}"
      | none => #[]
    (constOccurrences (fun _ => true) iv.cnst.type ++ iv.all ++ iv.ctors ++ recs).map (·, false) ++
      (familyOf iv).map (·, true)
  | .ctorInfo cv => ((constOccurrences (fun _ => true) cv.cnst.type).push cv.induct).map (·, false)
  | .recInfo rv =>
    (constOccurrences (fun _ => true) rv.cnst.type ++ rv.all ++ rv.rules.map (·.ctor) ++
      rv.rules.flatMap (constOccurrences (fun _ => true) ·.rhs)).map (·, false)
  | ci =>
    (constOccurrences (fun _ => true) ci.getCnst.type ++
      (if deep then ((valueOf' ci).map (constOccurrences fun _ => true)).getD #[] else #[])).map (·, false)

/-- The closure walk: a name's value is followed when it is forced or under
`ns`; a name first reached shallowly and later deeply is revisited for its
value. -/
partial def closureGo (get? : IxName → Option IxConst) (ns : Name) :
    List (IxName × Bool) → Std.HashMap IxName Bool → Array IxConst → Array IxConst
  | [], _, out => out
  | (n, force) :: todo, seen, out =>
    let deep := force || isUnder ns n
    match seen.get? n with
    | some d =>
      if d || !deep then closureGo get? ns todo seen out
      else match get? n with
        | some ci => closureGo get? ns ((neighbours true ci).toList ++ todo) (seen.insert n true) out
        | none => closureGo get? ns todo (seen.insert n true) out
    | none =>
      match get? n with
      | some ci => closureGo get? ns ((neighbours deep ci).toList ++ todo) (seen.insert n deep) (out.push ci)
      | none => closureGo get? ns todo (seen.insert n deep) out

/-- The names an expression mentions: constants and projection structures. -/
def namesIn (acc : Std.HashSet IxName) (e : IxExpr) : Std.HashSet IxName :=
  foldDistinct (init := acc) (e := e) fun s x => match x with
    | .const n _ _ => .yield (s.insert n)
    | .proj t _ _ _ => .yield (s.insert t)
    | _ => .yield s

/-- The names of the closure and every name its constants mention: the
domain of the address table the Rust side receives. -/
def addrDomain (consts : Array IxConst) : Array IxName :=
  (consts.foldl (init := ({} : Std.HashSet IxName)) fun s ci =>
    let s := namesIn (s.insert ci.getCnst.name) ci.getCnst.type
    let s := match valueOf' ci with
      | some v => namesIn s v
      | none => s
    match ci with
    | .recInfo rv => rv.rules.foldl (fun s r => namesIn s r.rhs) s
    | _ => s).toArray

/-! ## Addresses -/

/-- A name-hash address: every name by its pretty form. -/
def nameAddr (n : IxName) : Option Address := some (Address.blake3 n.pretty.toUTF8)

/-- A content address: a constant under the clique's namespace by its type
and value with that namespace erased (so the same matcher in two
presentations has one address), any other name by its name. -/
def contentAddr (get? : IxName → Option IxConst) (ns : Name) (n : IxName) : Option Address :=
  if isUnder ns n then
    (get? n).map fun ci =>
      let rel := renameConsts fun m =>
        if isUnder ns m then some (ixName ((toLeanName m).replacePrefix ns `_pres)) else none
      let v := match valueOf' ci with
        | some e => toString (rel e).getHash
        | none => ""
      Address.blake3 s!"{(rel ci.getCnst.type).getHash}|{v}".toUTF8
  else some (Address.blake3 (toLeanName n).toString.toUTF8)

/-! ## Comparison -/

def tagOf : CliqueOutcome → Nat
  | .notEncoded _ => 0
  | .unchanged .. => 1
  | .baseline .. => 2
  | .transported _ => 3

def tagName : Nat → String
  | 0 => "notEncoded"
  | 1 => "unchanged"
  | 2 => "baseline"
  | 3 => "transported"
  | n => s!"tag {n}"

def encOf : CliqueOutcome → String
  | .notEncoded _ => "-"
  | .unchanged e _ => e.tag
  | .baseline e _ _ => e.tag
  | .transported p => p.encoding.tag

/-- The first differing field and both values. -/
abbrev Cmp := Except (String × String × String) Unit

def trunc (s : String) : String := if s.length ≤ 400 then s else (s.take 400).toString ++ "…"

def chk (field : String) (ok : Bool) (l r : Unit → String) : Cmp :=
  if ok then pure () else throw (field, trunc (l ()), trunc (r ()))

def namesEq (a b : Array IxName) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => _root_.Ix.Compile.Image.RawExact.nameEq x y

def showNames (a : Array IxName) : String := toString (a.map (·.pretty))

def exprSame (a b : IxExpr) : Bool := a == b && _root_.Ix.Compile.Image.RawExact.exprEq a b

def showExpr (e : IxExpr) : String := s!"{e.getHash} {toLeanExpr e}"

def cmpDecl (path : String) (l : Decl) (r : RsDecl) : Cmp := do
  chk s!"{path}.name" (_root_.Ix.Compile.Image.RawExact.nameEq l.name r.name)
    (fun _ => l.name.pretty) (fun _ => r.name.pretty)
  chk s!"{path}.levelParams" (namesEq l.levelParams r.levelParams)
    (fun _ => showNames l.levelParams) (fun _ => showNames r.levelParams)
  chk s!"{path}.isThm" (l.isThm == r.isThm) (fun _ => toString l.isThm) (fun _ => toString r.isThm)
  chk s!"{path}.type" (exprSame l.type r.type) (fun _ => showExpr l.type) (fun _ => showExpr r.type)
  chk s!"{path}.value" (exprSame l.value r.value) (fun _ => showExpr l.value) (fun _ => showExpr r.value)

/-- The fields of a transported plan. -/
def cmpPlan (p : CliquePlan) (r : RsOutcome) : Cmp := do
  let nameEq := _root_.Ix.Compile.Image.RawExact.nameEq
  chk "all" (namesEq p.all r.all) (fun _ => showNames p.all) (fun _ => showNames r.all)
  chk "sigma" (p.sigma == r.sigma) (fun _ => toString p.sigma) (fun _ => toString r.sigma)
  chk "classes" (p.classes.size == r.classes.size && (p.classes.zip r.classes).all fun (a, b) => namesEq a b)
    (fun _ => toString (p.classes.map showNames)) (fun _ => toString (r.classes.map showNames))
  chk "members.size" (p.members.size == r.members.size)
    (fun _ => toString (p.members.toArray.map (·.1.pretty))) (fun _ => toString (r.members.map (·.name.pretty)))
  for rd in r.members do
    match p.members.get? rd.name with
    | none => throw (s!"members[{rd.name.pretty}]", "absent", "present")
    | some ld => cmpDecl s!"members[{rd.name.pretty}]" ld rd
  chk "canon.size" (p.canon.size == r.canon.size)
    (fun _ => toString (p.canon.map (·.1.name.pretty))) (fun _ => toString (r.canon.map (·.1.name.pretty)))
  for ((ld, ls), (rd, rs), i) in (p.canon.zip r.canon).zipIdx.map (fun ((a, b), i) => (a, b, i)) do
    cmpDecl s!"canon[{i}]" ld rd
    chk s!"canon[{i}].source" (nameEq ls rs) (fun _ => ls.pretty) (fun _ => rs.pretty)
  chk "functionals" (namesEq p.functionals r.functionals)
    (fun _ => showNames p.functionals) (fun _ => showNames r.functionals)
  let showCauses (cs : Array (IxName × String × String)) := toString (cs.map fun (n, c, w) => s!"{n.pretty} {c}: {w}")
  let lcauses := p.causes.map fun (n, c, w) => (n, c.tag, w)
  chk "causes" (lcauses.size == r.causes.size && (lcauses.zip r.causes).all
      fun ((n, c, w), (n', c', w')) => nameEq n n' && c == c' && w == w')
    (fun _ => showCauses lcauses) (fun _ => showCauses r.causes)
  chk "aliases" (p.aliases.size == r.aliases.size && (p.aliases.zip r.aliases).all
      fun ((m, x), (m', x')) => nameEq m m' && nameEq x x')
    (fun _ => toString (p.aliases.map fun (m, x) => s!"{m.pretty} = {x.pretty}"))
    (fun _ => toString (r.aliases.map fun (m, x) => s!"{m.pretty} = {x.pretty}"))
  chk "record" (p.record == r.record) (fun _ => p.record) (fun _ => r.record)

/-- Every field of Lean's outcome against Rust's. -/
def cmpOutcome (l : CliqueOutcome) (r : RsOutcome) : Cmp := do
  chk "tag" (tagOf l == r.tag) (fun _ => l.tag)
    (fun _ => s!"{tagName r.tag} ({r.encoding}, {r.cause}, {r.sourceDescribe}: {r.reason}) {r.record}")
  let noPlan : Cmp := chk "plan fields of a plan-less outcome"
    (r.all.isEmpty && r.sigma.isEmpty && r.classes.isEmpty && r.members.isEmpty && r.canon.isEmpty &&
      r.functionals.isEmpty && r.causes.isEmpty && r.aliases.isEmpty && r.record.isEmpty)
    (fun _ => "empty") (fun _ => s!"all {showNames r.all}, record {r.record}")
  let source (s : _root_.Ix.Compile.Pass.Clique.OrderSource) : Cmp := do
    chk "source.tag" (s.tag == r.sourceTag) (fun _ => s.tag) (fun _ => r.sourceTag)
    chk "source.describe" (s.describe == r.sourceDescribe) (fun _ => s.describe) (fun _ => r.sourceDescribe)
  let noSource : Cmp := chk "source of a source-less outcome" (r.sourceTag.isEmpty && r.sourceDescribe.isEmpty)
    (fun _ => "") (fun _ => r.sourceDescribe)
  match l with
  | .notEncoded why =>
    chk "reason" (why == r.reason) (fun _ => why) (fun _ => r.reason)
    chk "encoding" r.encoding.isEmpty (fun _ => "") (fun _ => r.encoding)
    chk "cause" r.cause.isEmpty (fun _ => "") (fun _ => r.cause)
    noSource
    noPlan
  | .unchanged e s =>
    chk "encoding" (e.tag == r.encoding) (fun _ => e.tag) (fun _ => r.encoding)
    chk "reason" r.reason.isEmpty (fun _ => "") (fun _ => r.reason)
    chk "cause" r.cause.isEmpty (fun _ => "") (fun _ => r.cause)
    source s
    noPlan
  | .baseline e c why =>
    chk "encoding" (e.tag == r.encoding) (fun _ => e.tag) (fun _ => r.encoding)
    chk "cause" (c.tag == r.cause) (fun _ => c.tag) (fun _ => r.cause)
    chk "reason" (why == r.reason) (fun _ => why) (fun _ => r.reason)
    noSource
    noPlan
  | .transported p =>
    chk "encoding" (p.encoding.tag == r.encoding) (fun _ => p.encoding.tag) (fun _ => r.encoding)
    chk "reason" r.reason.isEmpty (fun _ => "") (fun _ => r.reason)
    chk "cause" r.cause.isEmpty (fun _ => "") (fun _ => r.cause)
    source p.source
    cmpPlan p r

/-! ## Rows -/

def kindOf : IxConst → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def showHints : Lean.ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular {h}"

def showSafety : Lean.DefinitionSafety → String
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

/-- A copy or a row, field by field (both are definitions or theorems). -/
def cmpConst (path : String) (l r : IxConst) : Cmp := do
  let nameEq := _root_.Ix.Compile.Image.RawExact.nameEq
  chk s!"{path}.kind" (kindOf l == kindOf r) (fun _ => kindOf l) (fun _ => kindOf r)
  let (lc, rc) := (l.getCnst, r.getCnst)
  chk s!"{path}.name" (nameEq lc.name rc.name) (fun _ => lc.name.pretty) (fun _ => rc.name.pretty)
  chk s!"{path}.levelParams" (namesEq lc.levelParams rc.levelParams)
    (fun _ => showNames lc.levelParams) (fun _ => showNames rc.levelParams)
  chk s!"{path}.type" (exprSame lc.type rc.type) (fun _ => showExpr lc.type) (fun _ => showExpr rc.type)
  match l, r with
  | .defnInfo a, .defnInfo b =>
    chk s!"{path}.value" (exprSame a.value b.value) (fun _ => showExpr a.value) (fun _ => showExpr b.value)
    chk s!"{path}.hints" (a.hints == b.hints) (fun _ => showHints a.hints) (fun _ => showHints b.hints)
    chk s!"{path}.safety" (a.safety == b.safety) (fun _ => showSafety a.safety) (fun _ => showSafety b.safety)
    chk s!"{path}.all" (namesEq a.all b.all) (fun _ => showNames a.all) (fun _ => showNames b.all)
  | .thmInfo a, .thmInfo b =>
    chk s!"{path}.value" (exprSame a.value b.value) (fun _ => showExpr a.value) (fun _ => showExpr b.value)
    chk s!"{path}.all" (namesEq a.all b.all) (fun _ => showNames a.all) (fun _ => showNames b.all)
  | _, _ => throw (s!"{path}.kind", "a definition or a theorem", kindOf r)

/-- Lean's `rowsOf` against Rust's: the refusal, or every copy and row. -/
def cmpRows (l r : Except String (Array IxConst × Array IxConst)) : Cmp := do
  let names (cs : Array IxConst) : String := showNames (cs.map (·.getCnst.name))
  match l, r with
  | .error a, .error b => chk "refusal" (a == b) (fun _ => a) (fun _ => b)
  | .error a, .ok (cs, rs) => throw ("refusal", a, s!"copies {names cs}, rows {names rs}")
  | .ok (cs, rs), .error b => throw ("refusal", s!"copies {names cs}, rows {names rs}", b)
  | .ok (lc, lr), .ok (rc, rr) =>
    chk "copies.size" (lc.size == rc.size) (fun _ => names lc) (fun _ => names rc)
    for ((a, b), i) in (lc.zip rc).zipIdx do cmpConst s!"copies[{i}]" a b
    chk "rows.size" (lr.size == rr.size) (fun _ => names lr) (fun _ => names rr)
    for ((a, b), i) in (lr.zip rr).zipIdx do cmpConst s!"rows[{i}]" a b

/-- `all` with one more name. -/
def pushAll (n : IxName) : IxConst → IxConst
  | .defnInfo v => .defnInfo { v with all := v.all.push n }
  | .thmInfo v => .thmInfo { v with all := v.all.push n }
  | ci => ci

/-- The control of the rows comparison: Rust's result equal to Lean's, with
one field perturbed (the first copy's value, the first row's value and
`all`; a refusal's text), must be `DIFF` at that field. -/
def rowsPerturbations : Except String (Array IxConst × Array IxConst) →
    Array (String × Except String (Array IxConst × Array IxConst))
  | .error e => #[("refusal", .error (e ++ " "))]
  | .ok (cs, rs) =>
    let withValue := _root_.Ix.Compile.Pass.Clique.withValue
    let copy := match cs[0]? with
      | some _ => #[("copies[0].value", .ok (cs.modify 0 fun ci => withValue ci ci.getCnst.type, rs))]
      | none => #[]
    let row := match rs[0]? with
      | some ci => #[("rows[0].value", .ok (cs, rs.modify 0 fun ci => withValue ci ci.getCnst.type)),
          ("rows[0].all", .ok (cs, rs.modify 0 (pushAll ci.getCnst.name)))]
      | none => #[]
    copy ++ row

/-! ## One case -/

/-- A clique to plan: Lean's input is the fixtures' environment under
`overlay` (replaced or added constants). -/
structure Case where
  label : String
  overlay : Std.HashMap IxName IxConst := {}
  /-- the clique's namespace (the closure's depth, the content address) -/
  ns : Name
  all : Array IxName
  carried : Array IxName

structure Row where
  label : String
  /-- `plan` or `rows` -/
  what : String := "plan"
  verdict : String
  outcome : String := ""
  msg : String := ""
  /-- the perturbed Rust outcomes compared (controls), and those not found
  different -/
  controls : Nat := 0
  missed : Array String := #[]
  /-- rows: Lean's copies and rows, or its refusal -/
  copies : Nat := 0
  rows : Nat := 0
  refusal : Bool := false

/-- The control of the comparison: a Rust outcome equal to Lean's, with one
field perturbed (a canonical constant's value, a member's value, the
record), must be `DIFF` at that field. -/
def perturbations (r : RsOutcome) : Array (String × RsOutcome) :=
  let canon := match r.canon[0]? with
    | some _ => #[("canon[0].value",
        { r with canon := r.canon.modify 0 fun (d, s) => ({ d with value := d.type }, s) })]
    | none => #[]
  let member := match r.members[0]? with
    | some d => #[(s!"members[{d.name.pretty}].value",
        { r with members := r.members.modify 0 fun d => { d with value := d.type } })]
    | none => #[]
  canon ++ member ++ #[("record", { r with record := r.record ++ " " })]

/-- Plan `c` with both compilers' libraries, under both addresses. -/
def runCase (env : Environment) (c : Case) : Array Row := Id.run do
  let base : _root_.Ix.Environment := ixEnvOf env c.overlay
  let seeds : Array IxName := c.all ++ c.carried ++ (match c.all[0]? with
    | some a0 => #[_root_.Ix.Name.mkStr a0 "_mutual", _root_.Ix.Name.mkStr a0 "mutual"]
    | none => #[]) ++ c.all.map (_root_.Ix.Name.mkStr · "_f")
  -- and the library constants the transport reads by name and may introduce
  -- (`transportPrereqs`: `monotone_compose`'s universe parameters, the
  -- regenerated case splits), through their types
  let start := seeds.toList.map (·, true) ++
    _root_.Ix.Compile.Pass.Clique.transportPrereqs.toList.map (·, false)
  let consts := closureGo base.get? c.ns start {} #[]
  -- Lean's input: the same constants (converted once), then the rest of the environment
  let leanEnv : _root_.Ix.Environment :=
    { base with consts := consts.foldl (fun m ci => m.insert ci.getCnst.name ci) c.overlay }
  let domain := addrDomain consts
  let oracleFor := SourceFamilyOracle.forLean env leanEnv c.all
  let mut rows := #[]
  for (aname, addr?) in [("name", nameAddr), ("content", contentAddr leanEnv.get? c.ns)] do
    let pairs := domain.filterMap fun n => (addr? n).map (n, ·)
    let table : Std.HashMap IxName Address := pairs.foldl (fun m (n, a) => m.insert n a) {}
    let addrL (n : IxName) : Option Address := (table.get? n).orElse fun _ => addr? n
    let label := s!"{c.label} carried={c.carried.size} addr={aname}"
    let lean := _root_.Ix.Compile.Pass.Clique.planClique oracleFor leanEnv addrL c.all c.carried
    let outcome := s!"{tagName (tagOf lean)} {encOf lean}"
    -- a transported plan's constants may mention library constants Lean's do
    -- not (the composition fallback's monotonicity lemmas); `planClique`
    -- requires them in the input, so the closure carries them, through their
    -- types (a constant only Rust's transport introduced stays absent)
    let produced : List (IxName × Bool) := match lean with
      | .transported p => (p.canon.map (·.1) ++ p.members.toArray.map (·.2)).toList.flatMap fun d =>
        (constOccurrences (fun _ => true) d.type ++ constOccurrences (fun _ => true) d.value).toList.map
          (·, false)
      | _ => []
    let consts := if produced.isEmpty then consts else closureGo base.get? c.ns (start ++ produced) {} #[]
    match rsCliquePlan consts pairs c.all c.carried with
    | .error e => rows := rows.push { label, verdict := "RUST-ERR", outcome, msg := e }
    | .ok r =>
      match cmpOutcome lean r with
      | .ok () =>
        let ps := if tagOf lean == 3 then perturbations r else #[]
        let missed := ps.filterMap fun (field, r') => match cmpOutcome lean r' with
          | .error (f, _, _) => if f == field then none else some s!"{field} (found {f})"
          | .ok () => some s!"{field} (found SAME)"
        rows := rows.push { label, verdict := "SAME", outcome, controls := ps.size, missed }
      | .error (field, lv, rv) =>
        rows := rows.push { label, verdict := "DIFF", outcome,
                            msg := s!"{field}: lean {lv} | rust {rv}" }
    -- the rows of a transported plan: Lean's over its plan, Rust's over its own
    if let .transported p := lean then
      let leanRows := _root_.Ix.Compile.Pass.Clique.rowsOf leanEnv.get? p
      let (copies, nrows, refusal) := match leanRows with
        | .ok (cs, rs) => (cs.size, rs.size, false)
        | .error _ => (0, 0, true)
      let row : Row := { label, what := "rows", verdict := "", outcome, copies, rows := nrows, refusal }
      let rustRows := rsCliqueRows consts pairs c.all c.carried
      match cmpRows leanRows rustRows with
      | .ok () =>
        let ps := rowsPerturbations rustRows
        let missed := ps.filterMap fun (field, r') => match cmpRows leanRows r' with
          | .error (f, _, _) => if f == field then none else some s!"{field} (found {f})"
          | .ok () => some s!"{field} (found SAME)"
        rows := rows.push { row with verdict := "SAME", controls := ps.size, missed }
      | .error (field, lv, rv) =>
        rows := rows.push { row with verdict := "DIFF", msg := s!"rows {field}: lean {lv} | rust {rv}" }
  return rows

/-! ## The adversarial inputs of `clique-recognition` -/

/-- The `SA` cliques over an altered `Nat.brecOn` (same name and type,
another body: not authenticated), and the decoy `m._f`s of
`Recognition.decoyInput`. -/
def adversarialCases (env : Environment) : IO (Array Case) := _root_.runMeta (do
  let const? := constOf env
  let mut cases : Array Case := #[]
  let natBrecOn := ixName ``Nat.brecOn
  let some (.defnInfo brecOnVal) := const? natBrecOn | throwError "Nat.brecOn is not a definition"
  let alteredValue := _root_.Ix.Expr.mkApp
    (_root_.Ix.Expr.mkLam (ixName `x) brecOnVal.cnst.type (_root_.Ix.Expr.mkBVar 0) .default) brecOnVal.value
  let altered : Std.HashMap IxName IxConst :=
    ({} : Std.HashMap IxName IxConst).insert natBrecOn (.defnInfo { brecOnVal with value := alteredValue })
  for p in ["P0", "P1"] do
    let ns := `Tests.Ix.Compile.Twins.Cliques.SA ++ p.toName
    let (all, _) ← Tests.Ix.Compile.Clique.Recognition.cliqueOf env (ns ++ `ev)
    cases := cases.push { label := s!"altered Nat.brecOn SA {p}", overlay := altered, ns, all, carried := #[] }
  let kinds := [Tests.Ix.Compile.Clique.Recognition.DecoyKind.body, .ref]
  for kind in kinds do
    for (fam, p) in [("SA", "P0"), ("SA", "P1"), ("SP", "P0"), ("SP", "P1")] do
      let ns := `Tests.Ix.Compile.Twins.Cliques ++ fam.toName ++ p.toName
      let (all, members) ← Tests.Ix.Compile.Clique.Recognition.cliqueOf env
        (ns ++ (if fam == "SA" then `ev else `fa))
      let fs ← members.mapM fun m => match declOf env (toLeanName m.name ++ `_f) with
        | some d => pure d
        | none => throwError "missing functional of {m.name.pretty}"
      let (overlay, _) := Tests.Ix.Compile.Clique.Recognition.decoyInput const? kind members fs
      cases := cases.push { label := s!"decoy {kind.tag} {fam} {p}", overlay, ns, all, carried := #[] }
  return cases) env

/-! ## The suite -/

def run : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let mut failures : Array String := #[]
  -- the bounds tables
  let rb := rsCliqueBounds ()
  let lb := _root_.Ix.Compile.Pass.Clique.bounds.toArray
  if rb == lb then say s!"bounds: SAME ({lb.size} entries)"
  else failures := failures.push s!"bounds: DIFF lean {lb} | rust {rb}"
  -- the fixtures' cliques, with their equation lemmas realised
  let env0 ← fixturesEnv
  let cls := cliques env0
  let (env, realised) ← withEqLemmas env0 cls
  let const? := constOf env
  let mut cases : Array Case := #[]
  let mut withCarried := 0
  for ms in cls do
    let all := ms.map ixName
    let ns := ((ms[0]?).map (·.getPrefix)).getD .anonymous
    let carried := carriedOf const? all
    if !carried.isEmpty then withCarried := withCarried + 1
    let label := toString (ms.map fun n => (userName n).replacePrefix ns .anonymous) ++ s!" in {ns}"
    cases := cases.push { label, ns, all, carried := #[] }
    unless carried.isEmpty do cases := cases.push { label, ns, all, carried }
  say s!"{cls.size} cliques ({withCarried} with carried lemmas; {realised} equation lemmas realised)"
  let adversarial ← adversarialCases env
  let mut rows : Array Row := #[]
  for c in cases ++ adversarial do
    try
      rows := rows ++ runCase env c
    catch e => rows := rows.push { label := c.label, verdict := "ERROR", msg := toString e }
  -- the counts
  let (planRows, rowRows) := rows.partition (·.what == "plan")
  let count (rs : Array Row) (v : String) := (rs.filter (·.verdict == v)).size
  say s!"plans {planRows.size} ({cases.size} cases, {adversarial.size} adversarial, two addresses each): \
    SAME {count planRows "SAME"}, DIFF {count planRows "DIFF"}, RUST-ERR {count planRows "RUST-ERR"}, \
    ERROR {count planRows "ERROR"}"
  let controlsOf (rs : Array Row) := rs.foldl (fun n r => n + r.controls) 0
  let missedOf (rs : Array Row) := rs.flatMap fun r => r.missed.map (s!"{r.label} {r.what}: {·}")
  say s!"controls: {controlsOf planRows} perturbed Rust outcomes of transported plans, \
    {controlsOf planRows - (missedOf planRows).size} found DIFF at the perturbed field"
  let wfRows := rowRows.filter (·.outcome == "transported well-founded")
  let sum (rs : Array Row) (f : Row → Nat) := rs.foldl (fun n r => n + f r) 0
  say s!"rows of {rowRows.size} transported plans ({wfRows.size} well-founded): SAME {count rowRows "SAME"}, \
    DIFF {count rowRows "DIFF"}; Lean's: {sum wfRows (·.copies)} copies and {sum wfRows (·.rows)} rows of the \
    well-founded plans, {(wfRows.filter (·.refusal)).size} refused, \
    {sum (rowRows.filter (·.outcome != "transported well-founded")) fun r => r.copies + r.rows} records of the others"
  say s!"rows controls: {controlsOf rowRows} perturbed Rust results, \
    {controlsOf rowRows - (missedOf rowRows).size} found DIFF at the perturbed field"
  if controlsOf planRows == 0 then failures := failures.push "no plan control ran"
  if controlsOf rowRows == 0 then failures := failures.push "no rows control ran"
  if wfRows.isEmpty then failures := failures.push "no well-founded plan's rows compared"
  for m in missedOf rows do failures := failures.push s!"control not found DIFF: {m}"
  let mut byOutcome : Std.HashMap String Nat := {}
  for r in planRows do
    unless r.outcome.isEmpty do byOutcome := byOutcome.insert r.outcome (byOutcome.getD r.outcome 0 + 1)
  let outcomes := byOutcome.toArray.qsort fun a b => a.1 < b.1
  say s!"by outcome and encoding (Lean's): {outcomes.toList.map fun (k, n) => s!"{k}: {n}"}"
  for r in rows do
    if r.verdict != "SAME" then
      failures := failures.push s!"{r.label} {r.what} [{r.outcome}]: {r.verdict} {r.msg}"
  for f in failures do say s!"FAIL {f}"
  say s!"{failures.size} failures ({(← IO.monoMsNow) - t0} ms)"
  return if failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Clique.RustParity
