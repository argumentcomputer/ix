import Tests.Ix.IxVM.RecGen
import Ix.IxVM.Model

/-!
# The declaration checker's shape guards on a compiled corpus

`ixvm-guard-corpus` (manual) runs the declaration checker's shape guards over a compiled
corpus (`IX_RECGEN_IXE`), with the witness and host machinery of `Tests.Ix.IxVM.RecGen`;
outputs go to `IX_RECGEN_OUT`. `IX_GUARD_CORPUS_MODE` selects:

* `blocks`: every block with an inductive member, one `check` claim per block with every
  record its reference table names assumed and the binding assumed. The claim walk runs
  `KernelCheck::check_const` on each member: the member-kind check, and on the native route
  the whole shape check with the later-use scan of every constructor. A block on the modeled
  route is served no payload here and is refused there; an unsafe block is refused at the
  seed. Everything else must be accepted, having called `KernelCheck::check_inductive_shape`.
* `static`: the two purely syntactic guards read off the records, as the program reads
  them: blocks that hold both an inductive and a recursor, and, for every recursor record
  and every recursor member of a block, a `let` in a motive's domain, an index's domain,
  the major premise's domain or the result, or a binder up to the major premise that is not
  a `∀`.

* `syntax`: claims that reach `Lean.Syntax` and no recursor of it, with no model served, or
  with the modeller's advice when `IX_GUARD_CORPUS_ADVICE` is set.
* `blockrefs`: the used references from a record to a block record (`Muts`), counted in the
  corpus and in the default table's closure.
* `families`: the modeled families (blocks of recursors only, with the inductive block each
  eliminates): the advice the modeller writes for each on the closure of those blocks and of
  the role binding, with its outside references by witness kind, then one `CheckEnv` claim
  per family through the program, which runs `KernelModeled::check_family`.

The recursor records themselves go through the program with `ixvm-recgen` (`honest`).
-/

namespace Tests.Ix.IxVM.GuardCorpus

open IxVM.ClaimHarness Tests.Ix.IxVM Tests.Ix.IxVM.RecGen

/-- A block with an inductive member. -/
structure Block where
  addr : Address
  name : String
  c : Ixon.Constant
  types : Nat
  recursors : Nat
  definitions : Nat
  isUnsafe : Bool
  deriving Inhabited

def namesOf (env : Ixon.Env) : Std.HashMap Address String := Id.run do
  let mut nameOf : Std.HashMap Address String := {}
  for (n, nm) in env.named.toArray do
    unless nameOf.contains nm.addr do nameOf := nameOf.insert nm.addr (toString n)
  return nameOf

/-- The blocks of `env` with an inductive member, by address. -/
def blocksOf (env : Ixon.Env) : Array Block := Id.run do
  let nameOf := namesOf env
  let mut out : Array Block := #[]
  for (a, lc) in env.consts.toArray do
    match lc.peekTag with
    | .ok .muts =>
      if let some c := lc.get? then
        if let .muts ms := c.info then
          let mut types := 0
          let mut recursors := 0
          let mut definitions := 0
          let mut isUnsafe := false
          let mut name := toString a
          for (m, i) in ms.zipIdx do
            match m with
            | .indc ind =>
              if types == 0 then
                name := nameOf.getD (projWrapperAddr (.iPrj ⟨i.toUInt64, a⟩)) (toString a)
              types := types + 1
              if ind.isUnsafe then isUnsafe := true
            | .recr _ => recursors := recursors + 1
            | .defn _ => definitions := definitions + 1
          if types > 0 then
            out := out.push { addr := a, name, c, types, recursors, definitions, isUnsafe }
    | _ => pure ()
  return out.qsort fun x y => x.addr.hash.data < y.addr.hash.data

def shapeFn : String := "KernelCheck::check_inductive_shape"

/-- Every block with an inductive member through the program. -/
def runBlocks (cp : Corpus) (h : Host) : IO UInt32 := do
  let limit ← envNat "IX_GUARD_CORPUS_LIMIT" 0
  let workers ← envNat "IX_RECGEN_WORKERS" 32
  let blocks := blocksOf cp.env
  let requested ← match ← IO.getEnv "IX_GUARD_CORPUS_ADDRESS_FILE" with
    | none => pure ([] : List String)
    | some path => pure (((← IO.FS.readFile path).splitOn "\n").map (fun s => s.trimAscii.toString) |>.filter (· != ""))
  let selected := if requested.isEmpty then blocks else blocks.filter fun b =>
    requested.contains (toString b.addr) || (match b.c.info with
      | .muts ms => ms.zipIdx.any fun (_, i) =>
          requested.contains (toString (projWrapperAddr (.iPrj ⟨i.toUInt64, b.addr⟩)))
      | _ => false)
  let chosen := sample selected limit 0
  let expected ← envNat "IX_GUARD_CORPUS_EXPECT_COUNT" 0
  if expected != 0 && chosen.size != expected then
    IO.eprintln s!"[ixvm-guard-corpus] selected {chosen.size}, expected {expected}"
    return 1
  let exercise := (← IO.getEnv "IX_GUARD_CORPUS_EXERCISE").getD shapeFn
  let requireAll := (← IO.getEnv "IX_GUARD_CORPUS_REQUIRE_ALL").isSome

  IO.println s!"[ixvm-guard-corpus] blocks: {chosen.size} of {blocks.size} blocks with an \
    inductive member, {workers} workers"
  let t0 ← IO.monoMsNow
  let outcomes ← parFor workers chosen.size fun i => do
    let b := chosen[i]!
    checkOne h cp s!"blocks{i}" s!"gb{i}x" b.addr b.c #[] true (some exercise)
  let mut lines : Array String := #[tsvLine ["index", "name", "address", "types", "recursors",
    "definitions", "unsafe", "verdict", "depth", "records", "ms"]]
  let mut accepted := 0
  let mut acceptedOne := 0
  let mut unreached : Array String := #[]
  let mut rejected : Array String := #[]
  let mut unresolved : Array String := #[]
  let mut reasons : Std.HashMap String (Nat × Nat) := {}
  let mut oneType := 0
  let mut mixed := 0
  let mut withDefinitions := 0
  let mut unsafeBlocks := 0
  for (b, i) in chosen.zipIdx do
    let o := outcomes[i]!
    if b.types == 1 then oneType := oneType + 1
    if b.recursors > 0 then mixed := mixed + 1
    if b.definitions > 0 then withDefinitions := withDefinitions + 1
    if b.isUnsafe then unsafeBlocks := unsafeBlocks + 1
    let row := s!"{b.name}\t{b.addr}\ttypes={b.types}\tunsafe={b.isUnsafe}"
    match o.verdict with
    | .accepted true =>
      accepted := accepted + 1
      if b.types == 1 then acceptedOne := acceptedOne + 1
    | .accepted false => unreached := unreached.push row
    | .rejected m =>
      let reason := rejectionReason m
      let (n, one) := reasons.getD reason (0, 0)
      reasons := reasons.insert reason (n + 1, if b.types == 1 then one + 1 else one)
      rejected := rejected.push s!"{row}\t{reason}"
    | .missing m => unresolved := unresolved.push s!"{row}\t{m}"
    | .noLine => unresolved := unresolved.push s!"{row}\tno verdict line"
    lines := lines.push (tsvLine [toString i, b.name, toString b.addr, toString b.types,
      toString b.recursors, toString b.definitions, toString b.isUnsafe, o.verdict.text,
      toString o.depth, toString o.records, toString o.ms])
  IO.FS.writeFile (h.dir / "blocks.tsv") ("\n".intercalate lines.toList ++ "\n")
  let mut summary : Array String := #[
    s!"blocks with an inductive member: {blocks.size}",
    s!"run: {chosen.size}",
    s!"  with one inductive member: {oneType}",
    s!"  with a recursor member: {mixed}",
    s!"  with a definition member: {withDefinitions}",
    s!"  unsafe: {unsafeBlocks}",
    s!"accepted, having called {exercise}: {accepted} (one inductive member: {acceptedOne})",
    s!"accepted without calling it: {unreached.size}",
    s!"rejected: {rejected.size}",
    s!"no verdict (witness incomplete or no line): {unresolved.size}",
    s!"elapsed ms: {(← IO.monoMsNow) - t0}",
    "", "rejections by reason (count, of which blocks with one inductive member):"]
  for (reason, n, one) in reasons.toArray.qsort (fun x y => x.2.1 > y.2.1) do
    summary := summary.push s!"{n}\t{one}\t{reason}"
  summary := summary.push ""
  summary := summary.push "REJECTED:"
  for r in rejected do summary := summary.push r
  summary := summary.push "UNRESOLVED:"
  for r in unresolved do summary := summary.push r
  summary := summary.push "ACCEPTED WITHOUT THE CALL:"
  for r in unreached do summary := summary.push r
  IO.FS.writeFile (h.dir / "blocks-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary.toList.take 120 do IO.println l
  return if unresolved.isEmpty && unreached.isEmpty && (!requireAll || accepted == chosen.size) then 0 else 1

/-- `e` with the sharing references at its head resolved. -/
partial def headOf (sh : Array E) : E → E
  | .share i => match sh[i.toNat]? with
    | some e => headOf sh e
    | none => .share i
  | e => e

/-- The domains of the first `n` binders of `e`, each a `∀`, and `e` under them. -/
def peel (sh : Array E) (what : String) : Nat → E → Except String (Array E × E)
  | 0, e => pure (#[], e)
  | n + 1, e => match headOf sh e with
    | .all d b => do
      let (ds, rest) ← peel sh what n b
      pure (#[d] ++ ds, rest)
    | _ => throw s!"a {what} binder is not a ∀"

/-- Whether a recursor's header carries a `let` in a motive's domain, an index's domain,
the major premise's domain, the result; an error when a binder up to the major premise is
not a `∀`. The walk of `KernelCheck::check_rec_header_lets`. -/
def headerLets (c : Ixon.Constant) (r : Ixon.Recursor) :
    Except String (Bool × Bool × Bool × Bool) := do
  let sh := c.sharing
  let has (e : E) : Bool := anyIn sh isLet e
  let (_, e1) ← peel sh "parameter" r.params.toNat r.typ
  let (motives, e2) ← peel sh "motive" r.motives.toNat e1
  let (_, e3) ← peel sh "minor premise" r.minors.toNat e2
  let (indices, e4) ← peel sh "index" r.indices.toNat e3
  let (major, result) ← peel sh "major premise" 1 e4
  return (motives.any has, indices.any has, major.any has, has result)

/-- The syntactic guards, read off the records. -/
def runStatic (env : Ixon.Env) (out : System.FilePath) : IO UInt32 := do
  let nameOf := namesOf env
  let mut blocks := 0
  let mut inductiveBlocks := 0
  let mut mixed : Array String := #[]
  let mut standalone := 0
  let mut members := 0
  let mut spine : Array String := #[]
  let mut inMotive : Array String := #[]
  let mut inIndex : Array String := #[]
  let mut inMajor : Array String := #[]
  let mut inResult : Array String := #[]
  let mut anyLet := 0
  for (a, lc) in env.consts.toArray do
    let mut recs : Array (String × Ixon.Constant × Ixon.Recursor) := #[]
    match lc.peekTag with
    | .ok .recr =>
      if let some c := lc.get? then
        if let .recr r := c.info then recs := recs.push (nameOf.getD a (toString a), c, r)
    | .ok .muts =>
      if let some c := lc.get? then
        if let .muts ms := c.info then
          blocks := blocks + 1
          let hasInd := ms.any fun m => match m with | .indc _ => true | _ => false
          let hasRec := ms.any fun m => match m with | .recr _ => true | _ => false
          if hasInd then inductiveBlocks := inductiveBlocks + 1
          if hasInd && hasRec then mixed := mixed.push (toString a)
          for (m, i) in ms.zipIdx do
            if let .recr r := m then
              let name := nameOf.getD (projWrapperAddr (.rPrj ⟨i.toUInt64, a⟩)) s!"{a}#{i}"
              recs := recs.push (name, c, r)
    | _ => pure ()
    for (name, c, r) in recs do
      match c.info with
      | .recr _ => standalone := standalone + 1
      | _ => members := members + 1
      if anyIn c.sharing isLet r.typ then anyLet := anyLet + 1
      match headerLets c r with
      | .error e => spine := spine.push s!"{name}\t{e}"
      | .ok (m, i, j, res) =>
        if m then inMotive := inMotive.push name
        if i then inIndex := inIndex.push name
        if j then inMajor := inMajor.push name
        if res then inResult := inResult.push name
  let mut summary : Array String := #[
    s!"blocks: {blocks}; with an inductive member: {inductiveBlocks}",
    s!"blocks with both an inductive and a recursor member: {mixed.size}",
    s!"recursors: {standalone + members} ({standalone} records of their own, {members} block members)",
    s!"recursors with a let anywhere in their type: {anyLet}",
    s!"a binder up to the major premise that is not a ∀: {spine.size}",
    s!"a let in a motive's domain: {inMotive.size}",
    s!"a let in an index's domain: {inIndex.size}",
    s!"a let in the major premise's domain: {inMajor.size}",
    s!"a let in the result: {inResult.size}"]
  for (title, xs) in [("MIXED BLOCKS:", mixed), ("NOT A ∀:", spine), ("MOTIVE:", inMotive),
      ("INDEX:", inIndex), ("MAJOR:", inMajor), ("RESULT:", inResult)] do
    summary := summary.push title
    for x in xs do summary := summary.push x
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "static-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary.toList.take 80 do IO.println l
  let clean := mixed.isEmpty && spine.isEmpty && inMotive.isEmpty && inIndex.isEmpty &&
    inMajor.isEmpty && inResult.isEmpty
  return if clean then 0 else 1

/-- The corpus restricted to what its modeled families need: every block of recursors only
with the inductive block it eliminates, the role binding's constants, everything those
name, and the recursor records of the inductive blocks among them (a container's recursor
is named by no block). With the family records and their inductive blocks. -/
def familyClosure (cp : Corpus) : Except String (Ixon.Env × Array (Address × Address)) := do
  let env := cp.env
  let mut families : Array (Address × Address) := #[]
  for (a, lc) in env.consts.toArray do
    match lc.peekTag with
    | .ok .muts =>
      if let some c := lc.get? then
        if let .muts ms := c.info then
          if ms.all (fun m => match m with | .recr _ => true | _ => false) then
            if let some (Ixon.MutConst.recr r) := ms[0]? then
              match parentOf env c r with
              | .ok p => families := families.push (a, p.blockAddr)
              | .error e => throw s!"family record {a}: {e}"
    | _ => pure ()
  let roots := families.map (·.1) ++ families.map (·.2) ++ bindingRoots env false
  let some first := closureTo env roots 1000000 closureCap
    | throw "the families' closure exceeds the record cap"
  let inFirst : Std.HashSet Address := first.foldl (·.insert ·) {}
  let recs := cp.targets.filterMap fun t => match t.parent with
    | .ok p => if inFirst.contains p.blockAddr then some t.addr else none
    | .error _ => none
  let some all := closureTo env (first ++ recs) 1000000 closureCap
    | throw "the families' closure exceeds the record cap"
  let keep : Std.HashSet Address := all.foldl (·.insert ·) {}
  return ({ env with consts := env.consts.filter fun a _ => keep.contains a }, families)

/-- The modeled families of the corpus: the advice the modeller writes for each (its outside
references by witness kind, the basis references by name), then every family through the
program, one `CheckEnv` claim per family owning the block, its recursor family record and
their projections, the frontier and the binding assumed. -/
def runFamilies (cp : Corpus) (out : System.FilePath) : IO UInt32 := do
  let (sub, families) ← IO.ofExcept (familyClosure cp)
  IO.println s!"[ixvm-guard-corpus] families: {families.size} blocks of recursors only; \
    {sub.consts.size} of {cp.env.consts.size} records kept"
  let t0 ← IO.monoMsNow
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport { sub with modelsAttached := false })
  IO.println s!"[ixvm-guard-corpus] families: advice generated in {(← IO.monoMsNow) - t0} ms"
  let nameOf := namesOf cp.env
  let blockName (b : Address) : String :=
    nameOf.getD (projWrapperAddr (.iPrj ⟨0, b⟩)) (toString b)
  let mut lines : Array String := #[]
  let mut withPayload := 0
  let mut basis : Std.HashMap String Nat := {}
  let mut kinds : Std.HashMap Nat Nat := {}
  for (b, r) in rep.blocks do
    match r with
    | .ok (n, outside) =>
      withPayload := withPayload + 1
      let mut names : Array String := #[]
      for (x, k) in outside do
        kinds := kinds.insert k (kinds.getD k 0 + 1)
        if k == 0 then
          let name := nameOf.getD x (toString x)
          names := names.push name
          basis := basis.insert name (basis.getD name 0 + 1)
      lines := lines.push s!"BLOCK {blockName b}\t{b}\trecords={n}\toutside={outside.size}\t\
        basis={(outside.filter (·.2 == 0)).size}\tclosure={(outside.filter (·.2 == 1)).size}\t\
        container-rec={(outside.filter (·.2 == 2)).size}\tprojection={(outside.filter (·.2 == 3)).size}\t\
        basis-names={names.qsort (· < ·)}"
    | .error e => lines := lines.push s!"BLOCK {blockName b}\t{b}\tnone: {e}"
  let mut summary : Array String := #[
    s!"blocks of recursors only: {families.size}",
    s!"modeled blocks the modeller reads: {rep.blocks.size}; with a payload: {withPayload}",
    s!"outside references by kind: basis {kinds.getD 0 0}, closure {kinds.getD 1 0}, \
      container recursor {kinds.getD 2 0}, projection of a closure block {kinds.getD 3 0}",
    "basis references (name, families naming it):"]
  for (name, n) in basis.toArray.qsort (fun x y => x.1 < y.1) do
    summary := summary.push s!"{n}\t{name}"
  summary := summary ++ lines
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "families-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary do IO.println l
  let mut groups : Std.HashMap Address (Array Address) := {}
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      let g := match c.info with
        | .iPrj p => p.block
        | .cPrj p => p.block
        | .rPrj p => p.block
        | .dPrj p => p.block
        | _ => a
      groups := groups.insert g ((groups.getD g #[]).push a)
  let fft := (← IO.getEnv "IX_GUARD_CORPUS_FFT").isSome
  let pin : Option Nat := if fft then some 0 else none
  -- `IX_GUARD_CORPUS_TYPES_ONLY`: each claim owns the inductive block and its projections only;
  -- the family check runs on the block's own arm and reads the family record through the advice
  let typesOnly := (← IO.getEnv "IX_GUARD_CORPUS_TYPES_ONLY").isSome
  -- `IX_GUARD_CORPUS_EXERCISE`: the function an accepted family claim must call
  let exercise := (← IO.getEnv "IX_GUARD_CORPUS_EXERCISE").getD "KernelModeled::check_family"
  let cases : Array Builder := rep.advice.map fun (b, adv) => fun _ => do
    let owned := groups.getD b #[] ++ (if typesOnly then #[] else groups.getD adv.layout.recBlock #[])
    let (_, witness) ← buildShardCheckEnvWitness env owned (assumeBinding := true)
    return { label := s!"family {blockName b}: {owned.size} owned, {adv.records.size} advice records",
             accept := true, exercises := some exercise,
             expectedFftCost := pin, witness }
  -- a claim that reaches a modeled block through a type and none of its recursors, with
  -- the models attached: `autoParam`, whose type names `Lean.Syntax`
  let reach : Array Builder := match env.getAddr? (Ix.Name.fromLeanName `autoParam) with
    | some a => #[fun _ => do
        let witness ← buildClaimWitness env (.check cp.ctx a none)
        return { label := "check autoParam, models attached", accept := true,
                 expectedFftCost := pin, witness }]
    | none => #[]
  let rc ← runCases "ixvm-guard-corpus-families" (cases ++ reach) (jobs := 6)
  return if rc == 0 && withPayload == rep.blocks.size then 0 else 1

/-- Claims that reach `Lean.Syntax` and no recursor of it, with no model served: `autoParam`
(its type names `Lean.Syntax`), then theorems of the corpus whose closure, of at most
`IX_GUARD_CORPUS_CAP` records, holds `Lean.Syntax`'s block. Each is a `check` claim that
walks its whole closure under an assumed binding. A program that checks a modeled block's
family at its types refuses each for want of advice (`IX_GUARD_CORPUS_BEFORE`); one that
checks the declared shape there accepts them. -/
def runSyntax (cp : Corpus) : IO UInt32 := do
  let env := cp.env
  let before := (← IO.getEnv "IX_GUARD_CORPUS_BEFORE").isSome
  let fft := (← IO.getEnv "IX_GUARD_CORPUS_FFT").isSome
  let limit ← envNat "IX_GUARD_CORPUS_LIMIT" 20
  let cap ← envNat "IX_GUARD_CORPUS_CAP" 3000
  let some syn := env.getAddr? (Ix.Name.fromLeanName `Lean.Syntax)
    | IO.eprintln "[ixvm-guard-corpus] the corpus has no Lean.Syntax"; return 1
  let some (Ixon.ConstantInfo.iPrj p) := (env.getConst? syn).map (·.info)
    | IO.eprintln "[ixvm-guard-corpus] Lean.Syntax is not an inductive's projection"; return 1
  let block := p.block
  let some recAddr := env.getAddr? (Ix.Name.fromLeanName `Lean.Syntax.rec)
    | IO.eprintln "[ixvm-guard-corpus] the corpus has no Lean.Syntax.rec"; return 1
  let some (Ixon.ConstantInfo.rPrj rp) := (env.getConst? recAddr).map (·.info)
    | IO.eprintln "[ixvm-guard-corpus] Lean.Syntax.rec is not a recursor's projection"; return 1
  let recBlock := rp.block
  let refusedRec := (← IO.getEnv "IX_GUARD_CORPUS_REFUSED").isSome
  let named := env.named.toArray.map (fun (n, nm) => (toString n, nm.addr))
  let sorted := named.qsort fun x y => x.1 < y.1
  let mut chosen : Array (String × Address × Array Address) := #[]
  if let some a := env.getAddr? (Ix.Name.fromLeanName `autoParam) then
    if let some cl := closureTo env #[a] 1000000 closureCap then
      chosen := chosen.push ("autoParam", a, cl)
  let isThm (a : Address) : Bool := match (env.getConst? a).map (·.info) with
    | some (Ixon.ConstantInfo.defn d) => d.kind == Ix.DefKind.thm
    | _ => false
  let theorems := sorted.filter fun (_, a) => isThm a
  let step := max 1 (theorems.size / 2000)
  let mut tried := 0
  for i in [0:theorems.size] do
    if i % step != 0 then continue
    if chosen.size ≥ 2 * limit + 2 then break
    let (name, a) := theorems[i]!
    tried := tried + 1
    if let some cl := closureTo env #[a] 1000000 cap then
      if cl.contains block then
        -- up to `limit` claims that reach the family's recursors and `limit` that do not
        let reaches := cl.contains recBlock
        if (chosen.filter fun (_, _, c) => c.contains recBlock == reaches).size ≤ limit then
          chosen := chosen.push (name, a, cl)
  IO.println s!"[ixvm-guard-corpus] syntax: {chosen.size} claims whose closure holds Lean.Syntax's \
    block ({tried} theorems tried, closures of at most {cap} records)"
  let advised := (← IO.getEnv "IX_GUARD_CORPUS_ADVICE").isSome
  -- with advice: the modeller's advice over the families' closure and the chosen claims'
  let advisedEnv ← if !advised then pure env else do
    let (sub, _) ← IO.ofExcept (familyClosure cp)
    let mut keep : Std.HashSet Address := {}
    for (x, _) in sub.consts do keep := keep.insert x
    for (_, a, _) in chosen do
      if let some sc := closureTo env (#[a] ++ cp.support) 1000000 closureCap then
        for x in sc do keep := keep.insert x
    let t0 ← IO.monoMsNow
    let (e, _) ← IO.ofExcept (IxVM.Model.generateReport
      { env with consts := env.consts.filter (fun x _ => keep.contains x), modelsAttached := false })
    IO.println s!"[ixvm-guard-corpus] syntax: advice generated over {keep.size} records in \
      {(← IO.monoMsNow) - t0} ms"
    pure e
  let cases : Array Builder := chosen.map fun (name, a, cl) => fun _ => do
    let reaches := cl.contains recBlock
    let kind := if reaches then "reaches the family's recursors" else "types and constructors only"
    if advised then
      let witness ← buildClaimWitness advisedEnv (.check cp.ctx a none)
      return { label := s!"check {name}, advice served ({kind}; {cl.size} records in its closure)",
               accept := !reaches,
               rejectsWith := if reaches then some modeledRecursorRefusal else none,
               witness }
    let some scope := closureTo env (#[a] ++ cp.support) 1000000 closureCap
      | throw s!"{name}: the witness exceeds the record cap"
    let b := buildWitness env cp.ctx #[] a #[] scope
    return { label := s!"check {name}, no model served ({kind}; {cl.size} records in its closure)",
             accept := !before && !reaches,
             rejectsWith := if before then some "no model advice"
               else if !reaches then none
               else if refusedRec then some "a recursor of a mutual or nested family is refused"
               else some "no model advice",
             expectedFftCost := if fft && !before && !reaches then some 0 else none,
             witness := b.witness }
  runCases "ixvm-guard-corpus-syntax" cases (jobs := 6)

/-! ## Claims that reach a recursor of a modeled family -/
/-- The reference-table indices an expression names as constants (`KernelClaim::const_idxs_expr`). -/
private partial def exprRefs : Ixon.Expr → Array Nat → Array Nat
  | .ref i _, acc => acc.push i.toNat
  | .prj i _ e, acc => exprRefs e (acc.push i.toNat)
  | .app f a, acc => exprRefs a (exprRefs f acc)
  | .lam t b, acc => exprRefs b (exprRefs t acc)
  | .all t b, acc => exprRefs b (exprRefs t acc)
  | .letE _ _ t v b, acc => exprRefs b (exprRefs v (exprRefs t acc))
  | _, acc => acc

/-- The reference-table indices a record uses as constants (`KernelClaim::const_idxs_of`). -/
private def usedRefs (c : Ixon.Constant) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  for e in c.sharing do acc := exprRefs e acc
  let member (m : Ixon.MutConst) (acc : Array Nat) : Array Nat := match m with
    | .defn d => exprRefs d.value (exprRefs d.typ acc)
    | .indc i => i.ctors.foldl (fun acc k => exprRefs k.typ acc) (exprRefs i.typ acc)
    | .recr r => r.rules.foldl (fun acc rl => exprRefs rl.rhs acc) (exprRefs r.typ acc)
  match c.info with
  | .defn d => exprRefs d.value (exprRefs d.typ acc)
  | .recr r => r.rules.foldl (fun acc rl => exprRefs rl.rhs acc) (exprRefs r.typ acc)
  | .axio a => exprRefs a.typ acc
  | .quot q => exprRefs q.typ acc
  | .muts ms => ms.foldl (fun acc m => member m acc) acc
  | _ => acc


/-- Whether the record at `a` is a theorem. -/
private def isTheoremAt (env : Ixon.Env) (a : _root_.Address) : Bool :=
  match (env.getConst? a).map (·.info) with
  | some (Ixon.ConstantInfo.defn d) => d.kind == Ix.DefKind.thm
  | _ => false

/-- The constants and theorem names whose reference closure holds a recursor record of a
modeled family: what a program that refuses such recursors turns away. The closure follows
references only (a projection's block, and the references a record uses), not the edge from
a block to its recursors. -/
def runReach (cp : Corpus) : IO UInt32 := do
  let env := cp.env
  let records := env.consts.toArray.filterMap fun (a, lc) => lc.get?.map fun c => (a, c)
  let edges (c : Ixon.Constant) : Array Address := Id.run do
    let mut out : Array Address := #[]
    for i in usedRefs c do
      if let some a := c.refs[i]? then out := out.push a
    match c.info with
    | Ixon.ConstantInfo.iPrj p => out := out.push p.block
    | Ixon.ConstantInfo.cPrj p => out := out.push p.block
    | Ixon.ConstantInfo.rPrj p => out := out.push p.block
    | Ixon.ConstantInfo.dPrj p => out := out.push p.block
    | _ => pure ()
    return out
  let mut users : Std.HashMap Address (Array Address) := {}
  let mut families : Array Address := #[]
  for (a, c) in records do
    for b in edges c do
      users := users.alter b fun | some arr => some (arr.push a) | none => some #[a]
    if let Ixon.ConstantInfo.muts ms := c.info then
      if !ms.isEmpty && ms.all (fun m => match m with | Ixon.MutConst.recr _ => true | _ => false) then
        families := families.push a
  let mut reached : Std.HashSet Address := {}
  let mut work := families
  for a in families do reached := reached.insert a
  while !work.isEmpty do
    let a := work.back!
    work := work.pop
    for u in users.getD a #[] do
      unless reached.contains u do
        reached := reached.insert u
        work := work.push u
  let mut names := 0
  let mut namesReach := 0
  let mut theorems := 0
  let mut theoremsReach := 0
  for (_, nm) in env.named.toArray do
    names := names + 1
    let hit := reached.contains nm.addr
    if hit then namesReach := namesReach + 1
    if isTheoremAt env nm.addr then
      theorems := theorems + 1
      if hit then theoremsReach := theoremsReach + 1
  IO.println s!"[ixvm-guard-corpus] reach: {records.size} records, {families.size} recursor records of modeled families"
  IO.println s!"names whose closure holds one: {namesReach} of {names}"
  IO.println s!"theorem names whose closure holds one: {theoremsReach} of {theorems}"
  return 0

/-- The addresses whose reference closure holds one of `seeds`: `seeds` and every record that
reaches one through a used reference or a projection's block. -/
def reachingSet (records : Array (Address × Ixon.Constant)) (seeds : Array Address) :
    Std.HashSet Address := Id.run do
  let edges (c : Ixon.Constant) : Array Address := Id.run do
    let mut out : Array Address := #[]
    for i in usedRefs c do
      if let some a := c.refs[i]? then out := out.push a
    match c.info with
    | Ixon.ConstantInfo.iPrj p => out := out.push p.block
    | Ixon.ConstantInfo.cPrj p => out := out.push p.block
    | Ixon.ConstantInfo.rPrj p => out := out.push p.block
    | Ixon.ConstantInfo.dPrj p => out := out.push p.block
    | _ => pure ()
    return out
  let mut users : Std.HashMap Address (Array Address) := {}
  for (a, c) in records do
    for b in edges c do
      users := users.alter b fun | some arr => some (arr.push a) | none => some #[a]
  let mut reached : Std.HashSet Address := {}
  let mut work := seeds
  for a in seeds do reached := reached.insert a
  while !work.isEmpty do
    let a := work.back!
    work := work.pop
    for u in users.getD a #[] do
      unless reached.contains u do
        reached := reached.insert u
        work := work.push u
  return reached

/-- The theorem names whose closure holds the block of one of the types `IX_GUARD_CORPUS_BLOCKS`
names (comma-separated) and no recursor record of a mutual or nested family: what F refuses
beyond `reach` once those blocks' family checks load such a recursor. -/
def runReachBlocks (cp : Corpus) : IO UInt32 := do
  let env := cp.env
  let names := ((← IO.getEnv "IX_GUARD_CORPUS_BLOCKS").getD "").splitOn ","
  let records := env.consts.toArray.filterMap fun (a, lc) => lc.get?.map fun c => (a, c)
  let mut families : Array Address := #[]
  for (a, c) in records do
    if let Ixon.ConstantInfo.muts ms := c.info then
      if !ms.isEmpty && ms.all (fun m => match m with | Ixon.MutConst.recr _ => true | _ => false) then
        families := families.push a
  let byRecursors := reachingSet records families
  let mut blocks : Array (String × Address) := #[]
  for n in names do
    let some a := env.getAddr? (Ix.Name.fromLeanName n.toName)
      | IO.eprintln s!"[ixvm-guard-corpus] no {n}"; return 1
    let some (Ixon.ConstantInfo.iPrj p) := (env.getConst? a).map (·.info)
      | IO.eprintln s!"[ixvm-guard-corpus] {n} is not an inductive's projection"; return 1
    blocks := blocks.push (n, p.block)
  let theoremNames := env.named.toArray.filter fun (_, nm) => isTheoremAt env nm.addr
  let count (s : Std.HashSet Address) (extra : Address → Bool) : Nat :=
    (theoremNames.filter fun (_, nm) => s.contains nm.addr && extra nm.addr).size
  IO.println s!"[ixvm-guard-corpus] reach-blocks: {theoremNames.size} theorem names; \
    {count byRecursors (fun _ => true)} hold a recursor record of a mutual or nested family"
  let mut union : Std.HashSet Address := {}
  for (n, b) in blocks do
    let s := reachingSet records #[b]
    for x in s do union := union.insert x
    IO.println s!"{n}: theorem names whose closure holds its block: {count s (fun _ => true)}; \
      of them without such a recursor: {count s (!byRecursors.contains ·)}"
  IO.println s!"together: {count union (fun _ => true)}; without such a recursor: \
    {count union (!byRecursors.contains ·)}"
  let sampleNames := (theoremNames.filter fun (_, nm) =>
    union.contains nm.addr && !byRecursors.contains nm.addr).toList.take 12
  for (n, _) in sampleNames do IO.println s!"  e.g. {n}"
  return 0

/-- The used references from a record of `env` to a block record (`Muts`): the walk of
`KernelClaim::walk_refs_transitive` loads such a reference's record as a constant. By
referencing record, as `name → target`. -/
def blockRefs (env : Ixon.Env) : Array String := Id.run do
  let nameOf := namesOf env
  let mut out : Array String := #[]
  for (a, lc) in env.consts.toArray do
    let some c := lc.get? | continue
    let mut seen : Std.HashSet Nat := {}
    for i in usedRefs c do
      if seen.contains i then continue
      seen := seen.insert i
      let some b := c.refs[i]? | continue
      if let some lb := env.consts[b]? then
        if let .ok .muts := lb.peekTag then
          let kind := match c.info with
            | .muts _ => "block" | .defn _ => "definition" | .recr _ => "recursor"
            | .axio _ => "axiom" | .quot _ => "quotient" | _ => "projection"
          out := out.push s!"{kind}\t{nameOf.getD a (toString a)}\t{a}\t{b}"
  return out

def runBlockRefs (leanEnv : Lean.Environment) (path : String) (out : System.FilePath) : IO UInt32 := do
  let corpus ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  let shared ← IxVM.ClaimHarness.loadSharedIxonEnv #[] leanEnv
  let inCorpus := blockRefs corpus
  let inShared := blockRefs shared
  let summary : Array String := #[
    s!"{path}: {corpus.consts.size} records; used references to a block record: {inCorpus.size}",
    s!"default table's closure: {shared.consts.size} records; used references to a block record: \
      {inShared.size}", "CORPUS:"] ++ inCorpus ++ #["DEFAULT:"] ++ inShared
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "blockrefs-summary.txt") ("\n".intercalate summary.toList ++ "\n")
  for l in summary.toList.take 60 do IO.println l
  return if inCorpus.isEmpty && inShared.isEmpty then 0 else 1

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let mode := (← IO.getEnv "IX_GUARD_CORPUS_MODE").getD "blocks"
  let some path ← IO.getEnv "IX_RECGEN_IXE"
    | IO.eprintln "[ixvm-guard-corpus] set IX_RECGEN_IXE to an .ixe file"; return 1
  let some out ← IO.getEnv "IX_RECGEN_OUT"
    | IO.eprintln "[ixvm-guard-corpus] set IX_RECGEN_OUT"; return 1
  match mode with
  | "static" =>
    let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
    IO.println s!"[ixvm-guard-corpus] {path}: {env.consts.size} records"
    runStatic env out
  | "families" => runFamilies (← Corpus.load path) out
  | "syntax" => runSyntax (← Corpus.load path)
  | "reach" => runReach (← Corpus.load path)
  | "blockrefs" => runBlockRefs leanEnv path out
  | "reach-blocks" => runReachBlocks (← Corpus.load path)
  | _ =>
    let h ← Host.make
    runBlocks (← Corpus.load path) h

end Tests.Ix.IxVM.GuardCorpus
