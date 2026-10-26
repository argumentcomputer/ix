/-
  cone-validator: the changed-cone validator (`Ix.Cert.ConeValidator`,
  `Ix.Compile.ConeCheck`).

  1. **Coverage** on the aux-heavy fixture corpus (`validateAuxClosure`),
     compiled by the statements' compiler (`Ix.Cert.compileUnchecked`): every
     change kind has roots (direct causes `member`, `imageHead`, `caller`,
     `regenerated`, `clique`; the published clique rows; the cascade; the
     required image computation-rule rows), and the plan names every root and
     every rewritten record.
  2. **The verdict on the corpus**: the compiler publishes no image
     computation-rule rows yet, so the validator refuses, naming the rows.
     With that step set aside (the plan's missing rows cleared, a test-only
     view), the remaining steps pass on the clean artifact: the roots' closure
     is accepted and every rewritten record's Source form infers.
  3. **Injected defects**, each refused with its step's message: a corrupted
     record of each root kind that has a plain definition record (its value
     replaced by its type), a root whose record is missing from the store, a
     Source term that does not infer, and an order that is not one (the
     decider's control).
  4. `cone-validator-initstd` (landing): Init+Std end to end, with the time of
     each step (`IX_CONE_PER_SEED=1` also times the acceptance one root at a
     time).

  Run with: `lake test -- cone-validator` (and `cone-validator-initstd`).
-/
import Ix.Cert.ConeValidator
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Kernel.SourceIngressStep
import Ix.EnvScope

namespace Tests.Ix.Compile.ConeValidator

open _root_.Ix.Compile.ChangedSet (ChangedSet Cause)
open _root_.Ix.Compile
open _root_.Ix.Cert (ConeInput)
open _root_.Ix.Cert.ConeValidator

abbrev IxName := _root_.Ix.Name

def say (s : String) : IO Unit := do
  IO.println s!"[cone-validator] {s}"
  (← IO.getStdout).flush

/-- Time an `IO` action, in milliseconds. -/
def timed (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  return (a, (← IO.monoMsNow) - t0)

/-- A compile through the statements' compiler, as the validator receives it: the
input, the artifact, the failures and the changed set (`Ix.Cert.coneInput`, with
the compile's aux table taken from the same run). -/
def compileInput (env : _root_.Ix.Environment) : IO ConeInput := do
  let (ixe, failures, cenv) ← IO.ofExcept (← IO.lazyPure fun _ => _root_.Ix.Cert.compileUnchecked env)
  IO.ofExcept (_root_.Ix.Cert.checkReport env cenv (ixe, failures))
  let cs ← IO.lazyPure fun _ => _root_.Ix.Compile.ChangedSet.ofCompile { consts := env.consts }
    (_root_.Ix.Cert.compileBlocks env) cenv.auxReport.table ixe
  return ⟨env, ixe, failures, cs⟩

def setting (ixe : Ixon.Env) : IO ConeCheck.Setting :=
  IO.ofExcept (ConeCheck.defaultSetting ixe _root_.Ix.Resource.typingLimits)

/-- The default role table. -/
def roleTable : IO _root_.Ix.Kernel.RoleTable := IO.ofExcept _root_.Ix.Kernel.Reader.defaultTable

/-- The Source terms of the rewritten roots, as the validator reads them. -/
def sourceTermsOf (input : ConeInput) :
    IO (IxName → Except String (Option (List (_root_.Ix.Kernel.Expr .anon)))) := do
  let t ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultTable
  let pre ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinPrelude
  let b ← IO.ofExcept (_root_.Ix.RoleEvidence.committedBundle ())
  return sourceTerms input.env input.ixe t pre b (_root_.Ix.LeanIngress.fiberHintsMap input.ixe)

/-! ## Roots by kind -/

/-- The roots of each kind over the whole input, as the validator selects them. -/
structure Census where
  direct : Std.HashMap String Nat := {}
  cascade : Nat := 0
  /-- the cascade roots the selector (`SourceReverse.select`, no ground edges) finds -/
  selectorCascade : Nat := 0
  rows : Nat := 0
  imageRuleRows : Nat := 0
  imageRuleRowsMissing : Nat := 0
  imagedRecursors : Nat := 0

def census (input : ConeInput) (t : _root_.Ix.Kernel.RoleTable) : Census := Id.run do
  let roots := rootsOf input t
  let selector := _root_.Ix.Cert.SourceReverse.select input.env input.changed input.env input.ixe
  let mut c : Census := {}
  for r in roots do
    match r.reason with
    | .direct cause => c := { c with direct := c.direct.insert cause.tag (c.direct.getD cause.tag 0 + 1) }
    | .cascade => c := { c with cascade := c.cascade + 1 }
    | .row => c := { c with rows := c.rows + 1 }
  let rows := imageRuleRows input.env input.ixe input.changed
  let heads : Std.HashSet IxName := rows.foldl (fun s (h, _, _) => s.insert h) {}
  { c with
    selectorCascade := (selector.filter (·.reason == .cascade)).length
    imageRuleRows := rows.size, imageRuleRowsMissing := (rows.filter (·.2.2.isNone)).size,
    imagedRecursors := heads.size }

def Census.line (c : Census) : String :=
  let direct := ", ".intercalate (["member", "image-head", "caller", "regenerated", "clique"].map
    fun k => s!"{k} {c.direct.getD k 0}")
  s!"direct roots: {direct}; clique rows {c.rows}; cascade {c.cascade} (the selector without ground edges: {c.selectorCascade}); image rule rows \
{c.imageRuleRows} of {c.imagedRecursors} imaged recursors ({c.imageRuleRowsMissing} unpublished)"

/-- The input names whose closure meets an imaged recursor: the closures a
missing image rule row concerns. -/
def imagedCone (input : ConeInput) : Nat :=
  let heads : Std.HashSet IxName := (imageRuleRows input.env input.ixe input.changed).foldl
    (fun s (h, _, _) => s.insert h) {}
  if heads.isEmpty then 0
  else ((_root_.Ix.Cert.SourceReverse.walk (_root_.Ix.Cert.SourceReverse.build input.env) heads).seen).size

/-! ## Injected defects -/

/-- The artifact with the record published for `n` replaced by one whose value is
its type (ill-typed), published under `n` at its own address. Only a plain
definition record (not a projection into a block). -/
def corrupt (ixe : Ixon.Env) (n : IxName) : Option Ixon.Env := do
  let named ← ixe.named.get? n
  let c ← ConeCheck.recordAt ixe named.addr
  let d ← match c.info with
    | .defn d => some d
    | _ => none
  let lc := Ixon.LazyConstant.ofConstant { c with info := .defn { d with value := d.typ } }
  let a := Address.blake3 lc.rawBytes
  pure { ixe with consts := ixe.consts.insert a lc, named := ixe.named.insert n { named with addr := a } }

/-- The artifact with the record published for `n` removed from the store. -/
def drop (ixe : Ixon.Env) (n : IxName) : Option Ixon.Env := do
  let named ← ixe.named.get? n
  pure { ixe with consts := ixe.consts.erase named.addr }

/-- The plan without the image rule row step (a test-only view, to reach the
later steps on an artifact the first refuses). -/
def withoutRows (p : ConeCheck.Plan) : ConeCheck.Plan := { p with missingRows := #[] }

def expectRefusal (what : String) (r : Except String α) (needle : String) : IO (Option String) := do
  match r with
  | .ok _ => return some s!"{what}: accepted, expected a refusal"
  | .error e =>
    say s!"{what}: refused ({(e.replace "\n" " ").take 220})"
    if (e.splitOn needle).length < 2 then
      return some s!"{what}: refused for another reason: {e.take 300}"
    return none

/-- A root of a direct cause or the cascade whose record is a plain definition. -/
def plainRoot (input : ConeInput) (t : _root_.Ix.Kernel.RoleTable)
    (keep : _root_.Ix.Cert.SelectedRoots.Reason → Bool) : Option IxName :=
  let roots := rootsOf input t
  (roots.find? fun r => keep r.reason && match ConeCheck.recordAt input.ixe r.address with
    | some c => match c.info with | .defn _ => true | _ => false
    | none => false).map (·.source)

/-! ## What the certified entry needs beyond the reference tables

The reader declines an inductive block whose recursors are not in its input
(`Ix.Kernel.Reader.readInductive`). A record's reference table names the blocks
it uses, never their recursors, so the compiled closure over the reference tables
alone of a root that uses an inductive lacks them; the check's closure follows
the extra edges too (`Ix.Compile.ConeCheck.Extra`). Printed for the record: the
closure over the reference tables alone, and the closure of the published
addresses of the roots' Source closures (Source's closure relation takes an
inductive's recursors with it). -/

/-- The certified entry over a set of addresses, in the environment check's order
(no closure-order decision: a diagnostic). A reading failure names the record. -/
def runOver (s : ConeCheck.Setting) (ixe : Ixon.Env) (addresses : Array Address)
    (recs : Std.HashMap Address (Array Address) := {}) : Except String Nat :=
  let stored := addresses.filterMap fun a => (ConeCheck.recordAt ixe a).map (a, ·)
  let order := (addresses.filter fun a => !ixe.consts.contains a) ++
    Ixon.CheckOrder.wholeEnv s.table s.prelude stored
  match Ixon.Authenticated.checkBytes s.binding s.limits (ConeCheck.recordsOf ixe order.toList)
      (ConeCheck.blobsOf ixe order.toList) s.hints with
  | .ok _ => .ok order.size
  | .error e =>
    let at? : Option Nat := match e with
      | .read p _ => some p
      | _ => none
    let what := match at?.bind (order[·]?) with
      | some a =>
        let names := ixe.named.fold (init := (#[] : Array String)) fun (acc : Array String) (n : IxName) (d : Ixon.Named) =>
          if d.addr == a then acc.push n.pretty else acc
        let kind := match ConeCheck.recordAt ixe a with
          | some c => match c.info with
            | .muts ms => s!"block of {ms.size} ({(ms.filter fun (m : Ixon.MutConst) => m matches .indc _).size} inductives)"
            | _ => "not a block"
          | none => "unstored"
        s!" [record {a}: {kind}, names {names.toList.take 4}, recursor records in the artifact \
{(recs.getD a #[]).size}, of them in the input {((recs.getD a #[]).filter addresses.contains).size}]"
      | none => ""
    .error s!"{order.size} records: {e}{what}"

/-- The published addresses of the Source closure of the roots' names (Source's
`Seed` of that closure), with the rows' addresses. -/
def sourceClosureSeeds (input : ConeInput) (t : _root_.Ix.Kernel.RoleTable) (plan : ConeCheck.Plan) :
    Array Address :=
  let roots := rootsOf input t
  let sub := _root_.Ix.Cert.closure input.env (roots.map (·.source))
  let named := sub.consts.fold (init := #[]) fun acc n _ =>
    match input.ixe.named.get? n with
    | some d => acc.push d.addr
    | none => acc
  named ++ plan.seeds

/-- Whether the logical check declines a record for its safety: a definition that
is not safe or an unsafe opaque (`Ix.Kernel.Reader.safetyDecline`), an unsafe
axiom, inductive or recursor. Quotient Source declines every group with such a
member, so no closure the final statement covers holds one. -/
def declinedRecord (c : Ixon.Constant) : Bool :=
  let defn (d : Ixon.Definition) := (_root_.Ix.Kernel.Reader.safetyDecline d).isSome
  match c.info with
  | .defn d => defn d
  | .axio a => a.isUnsafe
  | .recr r => r.isUnsafe
  | .muts ms => ms.any fun m => match m with
    | .defn d => defn d
    | .indc i => i.isUnsafe
    | .recr r => r.isUnsafe
  | _ => false

/-- The seeds whose closure over the check's edges holds no record the logical
check declines for its safety, and the number of such records the seeds reach. -/
def safeSeeds (ixe : Ixon.Env) (extra : ConeCheck.Extra) (seeds : Array Address) :
    Array Address × Nat := Id.run do
  let r := ConeCheck.reach ixe extra seeds
  let mut back : Std.HashMap Address (Array Address) := {}
  for a in r.found do
    let direct := match ConeCheck.recordAt ixe a with
      | some c => ConeCheck.needs ixe a c
      | none => #[]
    for b in direct ++ (extra.getD a #[]).filter ixe.consts.contains do
      back := back.insert b ((back.getD b #[]).push a)
  let bad := r.found.filter fun a => (ConeCheck.recordAt ixe a).any declinedRecord
  let mut tainted : Std.HashSet Address := {}
  let mut todo := bad.toList
  for _ in [0:2 * r.found.size + 1] do
    match todo with
    | [] => break
    | a :: rest =>
      todo := rest
      if tainted.contains a then continue
      tainted := tainted.insert a
      todo := (back.getD a #[]).toList ++ todo
  return (seeds.filter (!tainted.contains ·), bad.size)

/-- The closures the certified entry declines and accepts, for the record: the
roots' compiled closure over the reference tables alone (no extra edges), and the
compiled closure of the published addresses of the roots' Source closures, over
the check's edges. -/
def needsDiagnostics (input : ConeInput) (t : _root_.Ix.Kernel.RoleTable) (plan : ConeCheck.Plan)
    (s : ConeCheck.Setting) :
    IO Unit := do
  let plain := (ConeCheck.reach input.ixe {} plan.seeds).found
  let (verdict, tPlain) ← timed (IO.lazyPure fun _ => runOver s input.ixe plain s.extra)
  say s!"compiled closure of the roots over the reference tables alone ({plain.size} addresses): \
{match verdict with | .ok n => s!"accepted, {n} records" | .error e => s!"refused: {e.take 600}"} \
in {tPlain} ms"
  let (seeds, tSeeds) ← timed (IO.lazyPure fun _ => sourceClosureSeeds input t plan)
  let (verdict, tRun) ← timed (IO.lazyPure fun _ =>
    runOver s input.ixe (ConeCheck.reach input.ixe s.extra seeds).found s.extra)
  say s!"compiled closure of the roots' Source closures ({seeds.size} seeds, {tSeeds} ms): \
{match verdict with | .ok n => s!"accepted, {n} records" | .error e => s!"refused: {e.take 600}"} \
in {tRun} ms"

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let mut ps : Array String := #[]
  -- The corpus, closed as a selected compile input (`Ix.EnvScope.collectSelectedDeps`):
  -- with recursors, whole logical units and checker support. `validateAuxClosure` alone
  -- follows references only, so it leaves out recursors that nothing references, and
  -- the reader declines an inductive block without its recursor (for instance the
  -- alias-collapsed class block of `LE` and `LT`, whose recursors the corpus lacks).
  let filtered := _root_.Ix.EnvScope.collectSelectedDeps leanEnv
    ((validateAuxClosure leanEnv).map (·.1))
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon filtered.toArray 8
  let input ← compileInput env
  say s!"corpus: {filtered.length} constants, {input.failures.toMap.size} failures, \
{input.changed.counts.summary}"
  -- 1. coverage
  let c := census input (← roleTable)
  say (c.line)
  for k in ["member", "image-head", "caller", "regenerated", "clique"] do
    if c.direct.getD k 0 == 0 then ps := ps.push s!"coverage: no {k} root on the corpus"
  if c.rows == 0 then ps := ps.push "coverage: no published clique row on the corpus"
  if c.cascade == 0 then ps := ps.push "coverage: no cascade root on the corpus"
  if c.imageRuleRows == 0 then ps := ps.push "coverage: no required image rule row on the corpus"
  let t ← roleTable
  let plan := planOf input t
  let roots := rootsOf input t
  let seeds : Std.HashSet Address := plan.seeds.foldl (·.insert ·) {}
  unless roots.all (seeds.contains ·.address) do
    ps := ps.push "the plan's seeds miss a root"
  let rewrittenWanted := (roots.filter fun r => match r.reason with
    | .direct cause => rewrites cause | _ => false).length
  unless plan.rewritten.size == rewrittenWanted do
    ps := ps.push s!"the plan names {plan.rewritten.size} rewritten roots, the selector {rewrittenWanted}"
  -- 2. the verdict, and the later steps on the clean artifact
  if let some p ← expectRefusal "the corpus" (validatorWith .union _root_.Ix.Resource.typingLimits input)
      "computation-rule row" then ps := ps.push p
  let s ← setting input.ixe
  let terms ← sourceTermsOf input
  let (clean, ms) ← timed (IO.lazyPure fun _ => ConeCheck.runWithStats s .union (withoutRows plan) terms input.ixe)
  match clean with
  | .ok st => say s!"later steps on the clean corpus: passed in {ms} ms: {repr st}"
  | .error e => ps := ps.push s!"later steps on the clean corpus: {e.take 400}"
  -- the roots whose closure holds no record the logical check declines for its safety
  let ((safe, bad), tSafe) ← timed (IO.lazyPure fun _ => safeSeeds input.ixe s.extra plan.seeds)
  let safeSet := ConeCheck.seedSet safe
  say s!"roots whose closure reaches a record the logical check declines for its safety: \
{(ConeCheck.seedSet plan.seeds).size - safeSet.size} of {(ConeCheck.seedSet plan.seeds).size} distinct seeds \
({bad} such records reached; {tSafe} ms)"
  let safePlan : ConeCheck.Plan :=
    { seeds := safe, rewritten := plan.rewritten.filter (safeSet.contains ·.2) }
  let (later, tLater) ← timed (IO.lazyPure fun _ => ConeCheck.runWithStats s .union safePlan terms input.ixe)
  match later with
  | .ok st => say s!"all steps on the other roots: passed in {tLater} ms: {repr st}"
  | .error e => say s!"all steps on the other roots: refused in {tLater} ms: {e.take 600}"
  needsDiagnostics input t plan s
  -- 3. injected defects
  let kinds : List (String × (_root_.Ix.Cert.SelectedRoots.Reason → Bool)) :=
    [("caller", (· == .direct .caller)), ("image head", (· == .direct .imageHead)),
     ("regenerated", (· == .direct .regenerated)), ("clique", (· == .direct .clique)),
     ("member", (· == .direct .member)), ("clique row", (· == .row)), ("cascade", (· == .cascade))]
  let mut injected := 0
  for (what, keep) in kinds do
    match plainRoot input t keep with
    | none => say s!"injected defect, {what}: no root with a plain definition record"
    | some n =>
      let some bad := corrupt input.ixe n | ps := ps.push s!"{what}: could not corrupt {n.pretty}"
      let input' := { input with ixe := bad }
      injected := injected + 1
      if let some p ← expectRefusal s!"corrupted {what} {n.pretty}"
          (ConeCheck.runWithStats (← setting bad) .union (withoutRows (planOf input' t)) terms bad)
          "not accepted" then ps := ps.push p
  if injected < 3 then ps := ps.push s!"only {injected} kinds had a root to corrupt"
  match roots.head? with
  | none => ps := ps.push "no root at all"
  | some r =>
    let some bad := drop input.ixe r.source | ps := ps.push "could not drop a record"
    if let some p ← expectRefusal s!"missing record of {r.source.pretty}"
        (ConeCheck.runWithStats (← setting bad) .union (withoutRows (planOf { input with ixe := bad } t))
          terms bad) "missing" then ps := ps.push p
  match plan.rewritten[0]? with
  | none => ps := ps.push "no rewritten root"
  | some (n, _) =>
    let ill : _root_.Ix.Kernel.Expr .anon := .app (.sort .zero) (.sort .zero)
    let terms' : IxName → Except String (Option (List (_root_.Ix.Kernel.Expr .anon))) :=
      fun m => if m == n then .ok (some [ill]) else terms m
    if let some p ← expectRefusal s!"ill-typed Source term for {n.pretty}"
        (ConeCheck.runWithStats s .union (withoutRows plan) terms' input.ixe) "does not infer" then
      ps := ps.push p
  -- the decider's control: the closure of the first seed, its order reversed
  match plan.seeds[0]? with
  | none => pure ()
  | some a =>
    let r := ConeCheck.reach input.ixe s.extra #[a]
    let order := ConeCheck.orderOf input.ixe s.table s.prelude r
    let positions := ConeCheck.positionsOf order
    let (parent, depth) := ConeCheck.certificateOf r order positions
    unless ConeCheck.closureOrderCheck input.ixe s.extra #[a] (· == a) order positions parent depth do
      ps := ps.push "the decider refuses the computed order"
    let rev := order.reverse
    let rpos := ConeCheck.positionsOf rev
    let (rparent, rdepth) := ConeCheck.certificateOf r rev rpos
    if order.size > 1 && ConeCheck.closureOrderCheck input.ixe s.extra #[a] (· == a) rev rpos rparent rdepth then
      ps := ps.push "the decider accepts a reversed order"
    let short := order.pop
    let spos := ConeCheck.positionsOf short
    let (sparent, sdepth) := ConeCheck.certificateOf r short spos
    if order.size > 0 && ConeCheck.closureOrderCheck input.ixe s.extra #[a] (· == a) short spos sparent sdepth then
      ps := ps.push "the decider accepts an order missing a record"
    say s!"decider control on a closure of {order.size} records: computed order accepted, \
reversed and shortened ones refused"
  for p in ps do IO.eprintln s!"[cone-validator] FAIL {p}"
  say (if ps.isEmpty then "ok" else s!"{ps.size} problems")
  return if ps.isEmpty then 0 else 1

/-! ## Init+Std -/

def runInitStd : IO UInt32 := do
  let mut ps : Array String := #[]
  let leanEnv ← getCompileEnv #[`Init, `Std]
  let consts := leanEnv.constants.toList.toArray
  let (env, tCanon) ← timed (IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts 32)
  let ((ixe, failures, cenv), tCompile) ← timed do
    IO.ofExcept (← IO.lazyPure fun _ => _root_.Ix.Cert.compileUnchecked env)
  IO.ofExcept (_root_.Ix.Cert.checkReport env cenv (ixe, failures))
  let (cs, tSet) ← timed (IO.lazyPure fun _ => _root_.Ix.Compile.ChangedSet.ofCompile
    { consts := env.consts } (_root_.Ix.Cert.compileBlocks env) cenv.auxReport.table ixe)
  let input : ConeInput := ⟨env, ixe, failures, cs⟩
  say s!"Init+Std: {consts.size} constants, {failures.toMap.size} failures, {ixe.consts.size} \
records; canon {tCanon} ms, compile {tCompile} ms, changed set {tSet} ms: {cs.counts.summary}"
  let t ← roleTable
  let (plan, tPlan) ← timed (IO.lazyPure fun _ => planOf input t)
  say s!"plan (reverse index, roots, image rule rows): {tPlan} ms: {plan.seeds.size} seeds, \
{plan.rewritten.size} rewritten, {plan.missingRows.size} unpublished image rule rows"
  say (census input t).line
  say s!"input names whose closure meets an imaged recursor: {imagedCone input}"
  let (s, tSetting) ← timed (setting ixe)
  say s!"setting (role table, prelude, extra edges over the artifact): {tSetting} ms, \
{s.extra.size} records with extra edges"
  let (accepted, tAccept) ← timed (IO.lazyPure fun _ => ConeCheck.acceptance s ixe .union plan.seeds)
  match accepted with
  | .ok n => say s!"acceptance of all roots, one run: {n} records in {tAccept} ms"
  | .error e => say s!"acceptance of all roots, one run: refused in {tAccept} ms: {e.take 400}"
  let ((safe, bad), tSafe) ← timed (IO.lazyPure fun _ => safeSeeds ixe s.extra plan.seeds)
  let distinct := (ConeCheck.seedSet plan.seeds).size
  let distinctSafe := (ConeCheck.seedSet safe).size
  say s!"roots whose closure reaches a record the logical check declines for its safety: \
{distinct - distinctSafe} of {distinct} distinct seeds ({bad} such records reached; {tSafe} ms)"
  let (acceptedSafe, tAcceptSafe) ← timed (IO.lazyPure fun _ => ConeCheck.acceptance s ixe .union safe)
  match acceptedSafe with
  | .ok n => say s!"acceptance of the other roots, one run: {n} records in {tAcceptSafe} ms"
  | .error e => ps := ps.push s!"acceptance of the other roots, one run: {e.take 400}"
  if (← IO.getEnv "IX_CONE_PER_SEED").isSome then
    let (perSeed, tPer) ← timed (IO.lazyPure fun _ => ConeCheck.acceptance s ixe .perSeed safe)
    match perSeed with
    | .ok n => say s!"acceptance of the other roots, one run per root: {n} records in {tPer} ms"
    | .error e => ps := ps.push s!"acceptance, one run per root: {e.take 400}"
  let terms ← sourceTermsOf input
  let pairs := ConeCheck.distinctPairs plan.rewritten
  let (read, tTerms) ← timed (IO.lazyPure fun _ => ConeCheck.parMap (fun (p : IxName × Address) =>
    (p.1, p.2, terms p.1)) pairs.toList)
  let declined := (read.filter fun x => x.2.2 matches .ok none).length
  let failed := read.filterMap fun (n, _, r) => match r with | .error e => some (n, e) | _ => none
  say s!"Source terms of {pairs.size} rewritten roots: {tTerms} ms ({declined} not prepared by \
Source, {failed.length} unreadable)"
  let safeSet := ConeCheck.seedSet safe
  let safePlan : ConeCheck.Plan := { seeds := safe, rewritten := plan.rewritten.filter (safeSet.contains ·.2) }
  let (later, tLater) ← timed (IO.lazyPure fun _ => ConeCheck.runWithStats s .union safePlan terms ixe)
  match later with
  | .ok st => say s!"all steps on the other roots: passed in {tLater} ms: {repr st}"
  | .error e => ps := ps.push s!"all steps on the other roots: refused in {tLater} ms: {e.take 600}"
  let (whole, tWhole) ← timed (IO.lazyPure fun _ => checkWith .union _root_.Ix.Resource.typingLimits input)
  match whole with
  | .ok st => say s!"validator end to end (after the changed set): passed in {tWhole} ms: {repr st}"
  | .error e => say s!"validator end to end (after the changed set): refused in {tWhole} ms: \
{e.take 600}"
  needsDiagnostics input t plan s
  for p in ps do IO.eprintln s!"[cone-validator] FAIL Init+Std: {p}"
  return if ps.isEmpty then 0 else 1

end Tests.Ix.Compile.ConeValidator
