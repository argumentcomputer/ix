import Ix.KernelCheck.Meta
import Ix.KernelCheck.Binding
import Ix.KernelDisplay.Peek

/-! # `.meta`: the display table, the meta reader and the erasure run (untrusted harness)

IXC-PLAN §11 (step 6). `.meta` is the Ixon reading with display: its keys are
the `.anon` keys (record addresses, role keys, derived keys), and the reader's
output carries what the `.ixe`'s metadata says of the keys a record declares
(`Reader.Read.display`). It explains failures with names; it never decides.

* `displayTable`: what the metadata says of each key (`Reader.Display`): every
  Lean name the environment maps to the key's record address (an alias fiber
  has several), and, when the metadata is loaded in full (`Ixon.deEnv`), the
  level parameters' names. The key is the one a reading gives the address
  (`Reader.keyOfAddress`: a bound role's, else the address's own).
* `withDisplay`: the meta reader's last step, a `.meta` reading with the
  display of the keys it declares.
* `run` (`kernel-check-ixe --meta <input.ixe> <output.jsonl> [limit]`): **the
  erasure test.** Every record of the check order is read and checked twice,
  at `.anon` (as `kernel-check-ixe` does) and at `.meta` (the meta reader and
  the checker at `md = .meta`, under the same table, prelude, evidence and
  hints), and the two runs are compared record by record: the readings
  (declared keys exactly, terms by their cached hashes and term by term,
  `declAcross`), the outcome, the fold position and the failure itself, whose
  keys are mapped from `.anon` to `.meta` by `Key.map id` (the same addresses;
  display parts are subsingletons, so they never differ). The rows are the
  `.anon` run's, with a failure's reason rendered by `.meta`: keys by
  `Reader.spellWith`, then the terms the failure is about, printed with Lean's
  names (`Ix.KernelDisplay.renderFailure` with the display read). Any difference is printed and
  fails the run (exit 1).

Step 6b: the `.meta` reading's binders and lets carry the names the `.ixe`'s
metadata gives them (`Ix.KernelDisplay.nameRead`), and the run reports the
**name coverage**: of the binders and lets in the terms of constants with
metadata, the share the metadata names. A run below `minCoverage` fails.
-/

namespace Benchmarks.Kernel.CheckIxeMeta

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-! ## The erasure run -/

/-- An `.anon` key as a `.meta` key: the same address, role or shape. -/
def toMeta : Ix.Kernel.Key .anon → Ix.Kernel.Key .meta := Ix.Kernel.Key.map (fun a => a)

/-- A declaration's fingerprint up to its keys' mode: its kind, its declared
keys' and its terms' cached hashes (a term's hash is a function of its
structure and its keys' ids, the same in both modes), its level parameters
and counts. Terms are compared by hash: a structural comparison of two
readings would walk shared terms unshared. -/
def fingerprint : Ix.Kernel.Declaration md → List UInt64
  | .axiomDecl cv => [0] ++ cvPrint cv
  | .defnDecl cv v _ => [1] ++ cvPrint cv ++ [hash v]
  | .thmDecl cv v => [2] ++ cvPrint cv ++ [hash v]
  | .opaqueDecl cv v => [3] ++ cvPrint cv ++ [hash v]
  | .basisDecl _ => [4]
  | .indDecl block nP => [5, nP.toUInt64] ++ block.flatMap infoPrint
  | .quotDecl _ cv => [6] ++ cvPrint cv
where
  cvPrint (cv : Ix.Kernel.ConstantVal md) : List UInt64 :=
    [hash cv.name, cv.levelParams.length.toUInt64, hash cv.type]
  infoPrint (ci : Ix.Kernel.ConstantInfo md) : List UInt64 :=
    match ci with
    | .recInfo cv mI rP rules =>
      cvPrint cv ++ [mI.toUInt64, rP.toUInt64] ++
        rules.flatMap fun r => [hash r.ctor, r.nfields.toUInt64, hash r.rhs]
    | .ctorInfo cv nP nF => cvPrint cv ++ [nP.toUInt64, nF.toUInt64]
    | ci => cvPrint ci.toConstantVal

/-- A tier declaration's declared keys. -/
def tierKeys (d : Ix.Kernel.Tier.TierDecl md) : List (CName md) := d.names

/-- A tier declaration's fingerprint up to its keys' mode (as `fingerprint`). -/
def tierPrint : Ix.Kernel.Tier.TierDecl md → List UInt64
  | .defs s ms => [if s == .part then 7 else 8] ++
    ms.flatMap fun (cv, v) => fingerprint.cvPrint cv ++ [hash v]
  | .unsafeOpaque cv v => [9] ++ fingerprint.cvPrint cv ++ [hash v]
  | .unsafeAxiom cv => [10] ++ fingerprint.cvPrint cv

/-- Name coverage (per mille) under which the erasure run fails. -/
def minCoverage : Nat := 990

/-! ## Term-level erasure (step 6b) -/

/-- Pairs of an `.anon` and a `.meta` term proved the same, under their
common hash. -/
abbrev AcrossMemo := Std.HashMap UInt64 (List (Ix.Kernel.Expr .anon × Ix.Kernel.Expr .meta))

/-- **An `.anon` term and a `.meta` term are the same up to the keys' mode**
(`Key.map id`; display annotations are invisible to `==`): a lockstep walk,
memoized on the pairs it proved, a hit confirmed by `==` on both sides (a
pointer test at run time). Terms hash alike in the two modes (an address key's
hash is its address's), so the hashes filter first. -/
def exprAcross (a : Ix.Kernel.Expr .anon) (m : Ix.Kernel.Expr .meta) : StateM AcrossMemo Bool := do
  if hash a != hash m then return false
  let compound := match a with
    | .bvar _ | .sort _ | .const .. | .lit _ => false
    | _ => true
  if compound then
    if let some ps := (← get)[hash a]? then
      if ps.any fun (a', m') => a' == a && m' == m then return true
  let r ← match a, m with
    | .bvar i, .bvar j => pure (i == j)
    | .fvar i t, .fvar j u => if i == j then exprAcross t u else pure false
    | .sort u, .sort v => pure (u == v)
    | .const k us, .const k' vs => pure (toMeta k == k' && us == vs)
    | .app f x, .app g y => do pure ((← exprAcross f g) && (← exprAcross x y))
    | .lam t b mb, .lam t' b' mb' =>
      if mb == mb' then do pure ((← exprAcross t t') && (← exprAcross b b')) else pure false
    | .forallE t b mb, .forallE t' b' mb' =>
      if mb == mb' then do pure ((← exprAcross t t') && (← exprAcross b b')) else pure false
    | .letE t v b l, .letE t' v' b' l' =>
      if l == l' then do pure ((← exprAcross t t') && (← exprAcross v v') && (← exprAcross b b'))
      else pure false
    | .lit l, .lit l' => pure (l == l')
    | .proj s i e, .proj s' i' e' =>
      if toMeta s == s' && i == i' then exprAcross e e' else pure false
    | _, _ => pure false
  if r && compound then
    modify fun memo => memo.insert (hash a) ((a, m) :: memo.getD (hash a) [])
  return r

/-- A constant header across the modes. -/
def valAcross (a : Ix.Kernel.ConstantVal .anon) (m : Ix.Kernel.ConstantVal .meta) :
    StateM AcrossMemo Bool := do
  if toMeta a.name != m.name || a.levelParams != m.levelParams then return false
  exprAcross a.type m.type

/-- A block member across the modes: its header, and a definition's value or a
recursor's rules (their right-hand sides). -/
def infoAcross : Ix.Kernel.ConstantInfo .anon → Ix.Kernel.ConstantInfo .meta → StateM AcrossMemo Bool
  | .axiomInfo a, .axiomInfo m | .indInfo a _, .indInfo m _ | .ctorInfo a _ _, .ctorInfo m _ _ =>
    valAcross a m
  | .defnInfo a v _, .defnInfo m w _ | .thmInfo a v, .thmInfo m w => do
    pure ((← valAcross a m) && (← exprAcross v w))
  | .recInfo a _ _ rs, .recInfo m _ _ ws => do
    if rs.length != ws.length then return false
    let mut ok ← valAcross a m
    for (r, w) in rs.zip ws do
      ok := ok && toMeta r.ctor == w.ctor && r.nfields == w.nfields && (← exprAcross r.rhs w.rhs)
    pure ok
  | .projInfo _, .projInfo _ => pure true
  | _, _ => pure false

/-- **A declaration across the modes**, term by term. -/
def declAcross : Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .meta → StateM AcrossMemo Bool
  | .axiomDecl a, .axiomDecl m | .quotDecl _ a, .quotDecl _ m => valAcross a m
  | .defnDecl a v _, .defnDecl m w _ | .thmDecl a v, .thmDecl m w | .opaqueDecl a v, .opaqueDecl m w =>
    do pure ((← valAcross a m) && (← exprAcross v w))
  | .indDecl as n, .indDecl ms n' => do
    if n != n' || as.length != ms.length then return false
    let mut ok := true
    for (a, m) in as.zip ms do ok := ok && (← infoAcross a m)
    pure ok
  | .basisDecl _, .basisDecl _ => pure true
  | _, _ => pure false

/-- **A tier declaration across the modes**, member by member. -/
def tierAcross : Ix.Kernel.Tier.TierDecl .anon → Ix.Kernel.Tier.TierDecl .meta →
    StateM AcrossMemo Bool
  | .defs s ms, .defs s' ws => do
    if s != s' || ms.length != ws.length then return false
    let mut ok := true
    for ((a, v), (m, w)) in ms.zip ws do ok := ok && (← valAcross a m) && (← exprAcross v w)
    pure ok
  | .unsafeOpaque a v, .unsafeOpaque m w => do pure ((← valAcross a m) && (← exprAcross v w))
  | .unsafeAxiom a, .unsafeAxiom m => valAcross a m
  | _, _ => pure false

/-- Two failures are the same: the verdict and the message, keys included. -/
def sameError (a b : Ix.Kernel.CheckError .meta) : Bool :=
  a.verdictPrefix == b.verdictPrefix && a.msg == b.msg

structure Options where
  input : System.FilePath
  output : System.FilePath
  limit : Option Nat := none

def usage : String := "usage: kernel-check-ixe --meta <input.ixe> <output.jsonl> [limit]"

def parseArgs : List String → Option Options
  | [input, output] => some { input, output }
  | [input, output, limit] => do some { input, output, limit := some (← limit.toNat?) }
  | _ => none

/-- `kernel-check-ixe --meta`: the erasure test (module docstring). `unsafe`:
it prints failures with names, through the display-only read
(`Ix.KernelDisplay.Peek`); no verdict depends on it. -/
unsafe def run (args : List String) : IO UInt32 := do
  let some o := parseArgs args | IO.eprintln usage; return 2
  let started ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile o.input
  let env ← IO.ofExcept (Ixon.deEnv bytes)
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let (table, preA) ← IO.ofExcept (Ix.KernelCheck.Binding.context env)
  let preM ← IO.ofExcept (Ix.KernelCheck.Binding.metaPrelude env table preA)
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) table preA hints.lookup
  let (cxM, evM) := metaContext s (env.blobs[·]?) table preM hints.lookup
  let display := displayTable env cxM
  let nameCx : Ix.KernelDisplay.NameCx := ⟨env.names, Ix.KernelDisplay.metaTable env cxM⟩
  let names := reportNames env s.store
  let addresses := match o.limit with
    | some n => s.ordered.extract 0 (min n s.ordered.size)
    | none => s.ordered
  IO.eprintln s!"check-ixe --meta: {s.store.size} records, {addresses.size} in order, \
    {display.size} keys with display; loaded in {(← IO.monoMsNow) - started} ms"
  let handle ← IO.FS.Handle.mk o.output .write
  let counts ← IO.mkRef ({} : Std.HashMap String Nat)
  let failed ← IO.mkRef ({} : Std.HashMap Address Address)
  let diffs ← IO.mkRef (#[] : Array String)
  -- a record's rows (its own and its recursor records'), one outcome
  let note (address : Address) (v : RecordView) (outcome reason : String) (root : Address) :
      IO Unit := do
    let rows := #[(⟨address, names.getD address #[], v.kind, outcome, reason, 0, 0⟩ : Row)] ++
      v.recs.map fun r => (⟨r, names.getD r #[], "recursor", outcome, reason, 0, 0⟩ : Row)
    for row in rows do
      counts.modify fun c => c.insert outcome (c.getD outcome 0 + 1)
      if outcome != "accept" && outcome != "typed" then failed.modify (·.insert row.address root)
      handle.putStrLn row.json.compress
  let mut stA : State .anon := {}
  let mut stM : State .meta := {}
  let mut ca : Checker .anon := {}
  let mut cm : Checker .meta := {}
  let mut consumed : Std.HashSet Address := {}
  let mut displayed := 0
  -- the tier records (`Admission.isTierInfo`), read at both modes and deferred
  let mut deferred : Array (Address × RecordView × Ix.Kernel.Tier.TierDecl .anon ×
    Ix.Kernel.Tier.TierDecl .meta × Array Address) := #[]
  let mut coverage : Ix.KernelDisplay.Coverage := {}
  let mut types : Std.HashMap (Ix.Kernel.Key .meta) (Ix.Kernel.Expr .meta) := {}
  let mut nameCache : Std.HashMap Address Ix.Kernel.Name := {}
  let mut index := 0
  for address in addresses do
    index := index + 1
    if index % 10000 == 0 then
      IO.eprintln s!"check-ixe --meta: {index}/{addresses.size} after {(← IO.monoMsNow) - started} ms; \
        {(← counts.get).toList}; {(← diffs.get).size} differences"
    if consumed.contains address then continue
    let some v := s.view address | continue
    let some source := s.store[address]? | continue
    for r in v.recs do consumed := consumed.insert r
    if Ix.Kernel.Admission.isTierInfo source.info then
      match readTierAt s.cx address source, readTierAt cxM address source with
      | some (.ok dA), some (.ok dM) =>
        let (dM, cov, cache) := nameTier nameCx dM nameCache
        nameCache := cache
        coverage := coverage + cov
        for cv in dM.headers do types := types.insert cv.name cv.type
        unless tierKeys dA |>.map toMeta |> (· == tierKeys dM) do
          diffs.modify (·.push s!"{address}: tier readings differ in their keys")
        unless tierPrint dA == tierPrint dM && (tierAcross dA dM).run' {} do
          diffs.modify (·.push s!"{address}: tier readings differ")
        let deps := v.deps ()
        let f ← failed.get
        match deps.find? f.contains with
        | some blocker =>
          let root := f.getD blocker blocker
          note address v "blocked" (toString root) root
        | none => deferred := deferred.push (address, v, dA, dM, deps)
      | some (.error eA), some (.error eM) =>
        unless toString eA == toString eM do
          diffs.modify (·.push s!"{address}: tier read errors differ: {eA} / {eM}")
        let (outcome, reason) := readOutcome eA
        note address v outcome reason address
      | _, _ =>
        diffs.modify (·.push s!"{address}: one mode reads the tier record, the other does not")
        note address v "decline" "check-ixe --meta: the tier readings differ" address
      continue
    let readA := readRecord s.cx stA address source
    let readM := (readRecord cxM stM address source).map (withDisplay display)
    let readM ← match readM with
      | .ok rM => do
        let (rM, cov, cache) := Ix.KernelDisplay.nameRead nameCx rM nameCache
        nameCache := cache
        coverage := coverage + cov
        for (k, t) in Ix.KernelDisplay.declTypes rM.decls do types := types.insert k t
        pure (Except.ok rM)
      | .error e => pure (.error e)
    match readA, readM with
    | .error eA, .error eM =>
      unless toString eA == toString eM do
        diffs.modify (·.push s!"{address}: read errors differ: {eA} / {eM}")
      let (outcome, reason) := readOutcome eA
      note address v outcome reason address
    | .ok rA, .ok rM =>
      let keysA := (rA.decls.toList.flatMap declaredKeys).map toMeta
      let keysM := rM.decls.toList.flatMap declaredKeys
      unless keysA == keysM && rA.decls.toList.map fingerprint == rM.decls.toList.map fingerprint &&
          rA.generated == rM.generated do
        diffs.modify (·.push s!"{address}: readings differ")
      -- term-level erasure: the named reading is the anonymous one (a memo per
      -- record: a record's terms share through its sharing table)
      let same := ((rA.decls.toList.zip rM.decls.toList).allM
        (fun (a, m) => declAcross a m)).run' {}
      unless same && rA.decls.size == rM.decls.size do
        diffs.modify (·.push s!"{address}: readings differ term by term")
      displayed := displayed + rM.display.length
      stA := stA.commit rA
      stM := stM.commit rM
      let f ← failed.get
      match (v.deps ()).find? f.contains with
      | some blocker =>
        let root := f.getD blocker blocker
        note address v "blocked" (toString root) root
      | none =>
        let (ca', eA) := ca.steps s.evidence rA.decls
        let (cm', eM) := cm.steps evM rM.decls
        ca := ca'
        cm := cm'
        let same := ca'.pos == cm'.pos && match eA, eM with
          | none, none => true
          | some a, some m => sameError (a.mapKeys toMeta) m
          | _, _ => false
        unless same do
          diffs.modify (·.push s!"{address}: verdicts differ: .anon {eA.map toString} at {ca'.pos}, \
            .meta {eM.map toString} at {cm'.pos}")
        match eM with
        | none => note address v "accept" "" address
        | some e =>
          let (outcome, _) := checkOutcome e (spellWith display)
          let levelNames := match (rM.display.find? fun (_, d) => !d.levelNames.isEmpty) with
            | some (_, d) => d.levelNames
            | none => []
          let rcx := { Ix.KernelDisplay.metaCx display cm'.fe levelNames types with
            msgSpell := some (spellWith display) }
          note address v outcome (Ix.KernelDisplay.renderFailure { rcx with peek := Ix.KernelDisplay.peekAll } e) address
    | .ok _, .error eM =>
      diffs.modify (·.push s!"{address}: .anon reads, .meta does not: {eM}")
      note address v "decline" s!"check-ixe --meta: .meta does not read: {eM}" address
    | .error eA, .ok _ =>
      diffs.modify (·.push s!"{address}: .meta reads, .anon does not: {eA}")
      let (outcome, reason) := readOutcome eA
      note address v outcome reason address
  -- the typing tier at both modes, from each mode's checked index (also its
  -- logical view), staged as the tier fold stages it
  let logicalA := ca.fe
  let logicalM := cm.fe
  let feA ← IO.mkRef logicalA
  let feM ← IO.mkRef logicalM
  let mut typed := 0
  for (address, v, dA, dM, deps) in stageDeferred (·.2.2.1) deferred do
    let f ← failed.get
    match deps.find? f.contains with
    | some blocker =>
      let root := f.getD blocker blocker
      note address v "blocked" (toString root) root
    | none =>
      let a₀ ← feA.modifyGet fun x => (x, Ix.Kernel.mkFEnv Ix.Kernel.Env.empty)
      let m₀ ← feM.modifyGet fun x => (x, Ix.Kernel.mkFEnv Ix.Kernel.Env.empty)
      let (a₁, eA) := stepTier logicalA a₀ dA
      let (m₁, eM) := stepTier logicalM m₀ dM
      feA.set a₁
      feM.set m₁
      let same := match eA, eM with
        | none, none => true
        | some a, some m => sameError (a.mapKeys toMeta) m
        | _, _ => false
      unless same do
        diffs.modify (·.push s!"{address}: tier verdicts differ: .anon {eA.map toString}, \
          .meta {eM.map toString}")
      match eM with
      | none =>
        typed := typed + 1
        note address v "typed" (tierSafety dM).word address
      | some e =>
        let (outcome, reason) := tierOutcome (tierSafety dM) e (spellWith display)
        -- the failure's terms, printed with names, after the tier's reason
        let base := Ix.KernelDisplay.metaCx display m₀ [] types
        let full := Ix.KernelDisplay.renderFailure
          { base with peek := Ix.KernelDisplay.peekAll, msgSpell := some (spellWith display) } e
        let terms := String.join (((full.splitOn "\n").drop 1).map ("\n" ++ ·))
        note address v outcome (reason ++ terms) address
  handle.flush
  let diffs ← diffs.get
  IO.eprintln s!"check-ixe --meta: done in {(← IO.monoMsNow) - started} ms; {(← counts.get).toList}; \
    {displayed} declared keys with display; fold positions .anon {ca.pos}, .meta {cm.pos}; \
    {deferred.size} tier records, {typed} typed at both modes"
  let perMille := if coverage.binders == 0 then 1000 else coverage.named * 1000 / coverage.binders
  IO.eprintln s!"check-ixe --meta: name coverage {coverage.named}/{coverage.binders} binders and \
    lets of constants with metadata named ({perMille}‰; minimum {minCoverage}‰)"
  if perMille < minCoverage then
    IO.eprintln "check-ixe --meta: name coverage FAILED"
    return 1
  if diffs.isEmpty then
    IO.eprintln s!"check-ixe --meta: erasure: {addresses.size} records, .meta equals .anon on every \
      reading, outcome, position and failure"
    return 0
  IO.eprintln s!"check-ixe --meta: erasure FAILED: {diffs.size} records differ"
  for d in diffs.extract 0 50 do IO.eprintln s!"  {d}"
  return 1

end Benchmarks.Kernel.CheckIxeMeta
