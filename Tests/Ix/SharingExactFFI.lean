/-
  Lean/Rust differential test of the exact sharing constructions.

  Every check normalizes one Constant twice: in Lean (`normalizeConstantSharing`,
  `normalizeConstantSharingUniform`, `normalizeConstantSharingTiered` from
  `Ix.Sharing.Exact`) and in Rust through the `test-ffi` hooks
  `rs_exact_sharing_normalize`, `rs_uniform_sharing_normalize` and
  `rs_tiered_sharing_normalize` (crate `ixon::sharing_exact`). The two sides
  agree when both succeed with the same serialized bytes, or both fail with
  the same error category (malformed / format / resource / internal). One
  side exhausting a resource limit while the other succeeds is reported
  separately: the two implementations count work differently, and limits
  may change success but never the bytes of a success.

  Inputs: every §2 fixture, the generated families of the uniform and tiered
  tests, and, when `IX_SHARING_CORPUS` names an `.ixe` file, every constant of
  that corpus (expanded from its stored table). Corpus mode compares the
  modes listed in `IX_SHARING_CORPUS_MODES` (comma separated, default
  `tiered-tagN`; also `tiered-tag4`, `uniform-w<k>`, `exact`) and stops after
  `IX_SHARING_CORPUS_LIMIT` constants when that is set.
-/
module

public import Tests.Ix.SharingExact
public import Tests.Ix.SharingUniform
public import Tests.Ix.SharingTiered

public section

open LSpec Ixon Ix.Sharing.Exact Tests.SharingExact

-- Groups are functions run from deferred IO actions.
set_option compiler.extract_closed false

namespace Tests.SharingExactFFI

/-! ## Rust entry points (`test-ffi`) -/

@[extern "rs_exact_sharing_normalize"]
opaque rsExactNormalize : @& ByteArray → Except String ByteArray

@[extern "rs_uniform_sharing_normalize"]
opaque rsUniformNormalize : UInt64 → @& ByteArray → Except String ByteArray

/-- Layout code: 0 = Tag4, 1 = TagN. -/
@[extern "rs_tiered_sharing_normalize"]
opaque rsTieredNormalize : UInt8 → @& ByteArray → Except String ByteArray

/-! ## Modes and outcomes -/

/-- A sharing construction compared across the two implementations. -/
inductive Mode where
  | exact
  | uniform (w : Nat)
  | tiered (layout : ShareLayout)
  deriving BEq, Repr, Inhabited

def Mode.name : Mode → String
  | .exact => "exact"
  | .uniform w => s!"uniform-w{w}"
  | .tiered .tag4 => "tiered-tag4"
  | .tiered .tagN => "tiered-tagN"

def Mode.parse (s : String) : Option Mode :=
  if s == "exact" then some .exact
  else if s == "tiered-tag4" then some (.tiered .tag4)
  else if s == "tiered-tagN" then some (.tiered .tagN)
  else if s.startsWith "uniform-w" then (String.ofList (s.toList.drop 9)).toNat?.map .uniform
  else none

def layoutCode : ShareLayout → UInt8
  | .tag4 => 0
  | .tagN => 1

/-- One side's result: the serialized Constant, or an error category with
its detail. -/
inductive Outcome where
  | ok (bytes : ByteArray)
  | err (category detail : String)
  deriving Inhabited

def leanCategory : SharingError → String
  | .shareInExpandedInput .. | .shareOutOfRange .. | .nonBackwardShare ..
  | .rootCountMismatch .. => "malformed"
  | .formatBound .. => "format"
  | .resourceExhausted .. => "resource"
  | .internal _ => "internal"

def rustCategory (s : String) : String :=
  if s.startsWith "malformed sharing:" then "malformed"
  else if s.startsWith "format bound:" then "format"
  else if s.startsWith "resource exhausted:" then "resource"
  else if s.startsWith "internal error:" then "internal"
  else if s.startsWith "decode:" then "decode"
  else "unknown"

/-- The Lean construction under explicit limits. -/
def leanNormalize (m : Mode) (c : Constant) (limits : Limits) : Except SharingError Constant :=
  match m with
  | .exact => normalizeConstantSharing c limits
  | .uniform w => normalizeConstantSharingUniform w c limits
  | .tiered l => normalizeConstantSharingTiered l c limits

@[noinline] def leanSide (m : Mode) (c : Constant) : Outcome :=
  match leanNormalize m c {} with
  | .ok n => .ok (serConstant n)
  | .error e => .err (leanCategory e) (reprStr e)

@[noinline] def rustSide (m : Mode) (bytes : ByteArray) : Outcome :=
  let r := match m with
    | .exact => rsExactNormalize bytes
    | .uniform w => rsUniformNormalize w.toUInt64 bytes
    | .tiered l => rsTieredNormalize (layoutCode l) bytes
  match r with
  | .ok b => .ok b
  | .error s => .err (rustCategory s) s

/-- Index of the first differing byte (the shorter length if one is a
prefix of the other). -/
def firstDiff (a b : ByteArray) : Nat := Id.run do
  for i in [0:min a.size b.size] do
    if a.get! i != b.get! i then return i
  return min a.size b.size

/-- Comparison of the two sides. -/
inductive Verdict where
  | sameBytes
  | sameError (category : String)
  /-- One side exhausted a resource limit, the other succeeded. -/
  | resourceOnly (leanFailed : Bool)
  | differ (msg : String)
  deriving Inhabited

def compareOutcomes (lean rust : Outcome) : Verdict :=
  match lean, rust with
  | .ok a, .ok b =>
    if a == b then .sameBytes
    else .differ s!"bytes differ: Lean {a.size} B, Rust {b.size} B, first differing byte {firstDiff a b}"
  | .err ca da, .err cb db =>
    if ca == cb then .sameError ca else .differ s!"error categories differ: Lean {ca} ({da}), Rust {cb} ({db})"
  | .err "resource" _, .ok _ => .resourceOnly true
  | .ok _, .err "resource" _ => .resourceOnly false
  | .err ca da, .ok b => .differ s!"Lean error {ca} ({da}); Rust ok ({b.size} B)"
  | .ok a, .err cb db => .differ s!"Lean ok ({a.size} B); Rust error {cb} ({db})"

/-- Tallies of one batch of comparisons. -/
structure Tally where
  same : Nat := 0
  sameErr : Nat := 0
  resourceLean : Nat := 0
  resourceRust : Nat := 0
  differences : Array String := #[]
  /-- Labels of same-category errors and of one-sided resource exhaustion. -/
  notes : Array String := #[]
  leanNs : Nat := 0
  rustNs : Nat := 0
  deriving Inhabited

def Tally.add (t : Tally) (label : String) : Verdict → Tally
  | .sameBytes => { t with same := t.same + 1 }
  | .sameError c => { t with sameErr := t.sameErr + 1, notes := t.notes.push s!"{label}: both {c}" }
  | .resourceOnly true => { t with resourceLean := t.resourceLean + 1, notes := t.notes.push s!"{label}: Lean resource exhaustion, Rust ok" }
  | .resourceOnly false => { t with resourceRust := t.resourceRust + 1, notes := t.notes.push s!"{label}: Rust resource exhaustion, Lean ok" }
  | .differ msg => { t with differences := t.differences.push s!"{label}: {msg}" }

def Tally.summary (t : Tally) : String :=
  s!"{t.same} same bytes, {t.sameErr} same error category, {t.resourceLean} Lean-only and {t.resourceRust} Rust-only resource exhaustion, {t.differences.size} disagreements"

/-- Compare one Constant under one mode, timing both sides. -/
def compareOne (m : Mode) (c : Constant) (bytes : ByteArray) : IO (Verdict × Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let l ← IO.lazyPure fun _ => leanSide m c
  let t1 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => rustSide m bytes
  let t2 ← IO.monoNanosNow
  return (compareOutcomes l r, t1 - t0, t2 - t1)

/-- A limit's name and value. -/
def limitOf (l : Limits) : Resource → String × Nat
  | .exprVisits => ("maxExprVisits", l.maxExprVisits)
  | .depth => ("maxDepth", l.maxDepth)
  | .nodes => ("maxNodes", l.maxNodes)
  | .states => ("maxStates", l.maxStates)
  | .transitions => ("maxTransitions", l.maxTransitions)
  | .costEvals => ("maxCostEvals", l.maxCostEvals)
  | .outputBytes => ("maxOutputBytes", l.maxOutputBytes)
  | .materialize => ("maxMaterialize", l.maxMaterialize)
  | .materializeWork => ("maxMaterializeWork", l.maxMaterializeWork)
  | .oracleTables => ("maxOracleTables", l.maxOracleTables)
  | .oracleVariants => ("maxOracleVariants", l.maxOracleVariants)

/-- Double one limit. -/
def doubleLimit (l : Limits) : Resource → Limits
  | .exprVisits => { l with maxExprVisits := 2 * l.maxExprVisits }
  | .depth => { l with maxDepth := 2 * l.maxDepth }
  | .nodes => { l with maxNodes := 2 * l.maxNodes }
  | .states => { l with maxStates := 2 * l.maxStates }
  | .transitions => { l with maxTransitions := 2 * l.maxTransitions }
  | .costEvals => { l with maxCostEvals := 2 * l.maxCostEvals }
  | .outputBytes => { l with maxOutputBytes := 2 * l.maxOutputBytes }
  | .materialize => { l with maxMaterialize := 2 * l.maxMaterialize }
  | .materializeWork => { l with maxMaterializeWork := 2 * l.maxMaterializeWork }
  | .oracleTables => { l with maxOracleTables := 2 * l.maxOracleTables }
  | .oracleVariants => { l with maxOracleVariants := 2 * l.maxOracleVariants }

/-- For a Lean-only resource exhaustion: rerun Lean, doubling whichever
limit fires (at most 12 doublings in total), and report the limits that
fired, the values that sufficed, and whether the bytes then equal Rust's. -/
def diagnose (m : Mode) (c : Constant) (rust : Outcome) : String := Id.run do
  let mut limits : Limits := {}
  let mut fired : Array String := #[]
  let mut raised : Array Resource := #[]
  for _ in [0:13] do
    match leanNormalize m c limits with
    | .ok n =>
      let same := match rust with
        | .ok b => if serConstant n == b then "equal to Rust" else "DIFFERENT from Rust"
        | .err .. => "Rust failed"
      let final := raised.toList.map fun r =>
        let (name, v) := limitOf limits r
        s!"{name}={v}"
      return s!"Lean exhausted {fired.toList}; succeeded with {final}; bytes {same}"
    | .error (.resourceExhausted r lim) =>
      let (name, _) := limitOf limits r
      fired := fired.push s!"{name}={lim}"
      unless raised.contains r do raised := raised.push r
      limits := doubleLimit limits r
    | .error e => return s!"Lean exhausted {fired.toList}; then error {reprStr e}"
  return s!"Lean fired {fired.toList}; still exhausted after 12 doublings"

def compareMany (cases : Array (String × Constant)) (modes : Constant → List Mode) : IO Tally := do
  let mut t : Tally := {}
  for (label, c) in cases do
    let bytes := serConstant c
    for m in modes c do
      let (v, ln, rn) ← compareOne m c bytes
      t := { t.add s!"{label} [{m.name}]" v with leanNs := t.leanNs + ln, rustNs := t.rustNs + rn }
  return t

/-- A test group whose body runs in `IO` when the suite executes. -/
def ioGroup (descr : String) (run : IO (Bool × String)) : TestSeq :=
  .individualIO descr none (do
    let start ← IO.monoMsNow
    let (ok, msg) ← run
    IO.println msg
    IO.println s!"    [{descr}: {(← IO.monoMsNow) - start} ms]"
    return (ok, 0, 0, if ok then none else some s!"'{descr}' failed; see above")) .done

/-- Pass/fail and the printed report of a batch. With `expectAll`, every
comparison must be a byte-identical success. -/
def judge (descr : String) (t : Tally) (expectAll : Bool) : Bool × String :=
  let ok := t.differences.isEmpty &&
    (!expectAll || (t.resourceLean == 0 && t.resourceRust == 0 && t.sameErr == 0))
  let lines := (t.differences.toList.take 50).map (s!"      DISAGREEMENT {·}")
  (ok, String.intercalate "\n"
    (s!"    {descr}: {t.summary}; Lean {t.leanNs / 1000000} ms, Rust {t.rustNs / 1000000} ms" :: lines))

/-! ## Fixtures and generated families -/

def allModes : List Mode :=
  [.exact, .uniform 1, .uniform 2, .uniform 3, .uniform 5, .tiered .tag4, .tiered .tagN]

def fixtures : Array (String × Constant) :=
  let chains := #[1, 2, 3, 4, 7, 8, 9, 16, 32].map fun n =>
    (s!"T{n} → T{n}", axiomOf (arr (chain n) (chain n)))
  #[("T2 → T2", witness2), ("T16 → T16", witness16), ("nine Refs", nineRef.1),
    ("two 25-byte minima", axiomOf twoMinimaRoot #[.zero, .succ .zero])] ++ chains

/-- The exact width-state search is exponential: skip it on T32. -/
def fixtureModes (c : Constant) : List Mode :=
  if (serConstant c).size > 100 then allModes.filter (· != .exact) else allModes

def fixtureTests : TestSeq :=
  ioGroup "Lean/Rust: §2 fixtures" do
    let t ← compareMany fixtures fixtureModes
    return judge s!"§2 fixtures × {allModes.map Mode.name}" t true

/-- The generated families of the uniform and tiered tests. -/
def genFamily (i : Nat) : Tests.SharingExact.RGen (Array Ixon.Expr) :=
  match i % 7 with
  | 0 => Tests.SharingUniform.genPrefixes
  | 1 => Tests.SharingUniform.genSmallPayload
  | 2 => Tests.SharingUniform.genPairs
  | 3 => Tests.SharingUniform.genChain
  | 4 => Tests.SharingTiered.genHeavyParent
  | _ => genRoots 5 12 4

def generatedCases (n : Nat) : Array (String × Constant) :=
  runGen 83 do
    let mut out : Array (String × Constant) := #[]
    for i in [0:n] do
      let roots ← genFamily i
      out := out.push (s!"generated #{i} (family {i % 7})", wrapRoots roots i)
    return out

/-- The exact width-state search only on inputs with few candidates. -/
def generatedModes (c : Constant) : List Mode :=
  let small : Bool := match sharingProfile c with
    | .ok p => p.candidates ≤ 12
    | .error _ => false
  if small then allModes else allModes.filter (· != .exact)

def generatedTests : TestSeq :=
  ioGroup "Lean/Rust: generated families" do
    let t ← compareMany (generatedCases 350) generatedModes
    return judge "350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes" t false

/-! ## Corpus mode -/

def corpusTests (_ : Unit) : TestSeq :=
  .individualIO "init.ixe corpus (IX_SHARING_CORPUS)" none (do
    let some path ← IO.getEnv "IX_SHARING_CORPUS"
      | IO.println "    [corpus: IX_SHARING_CORPUS not set; skipped]"
        return (true, 0, 0, none)
    let modeNames := ((← IO.getEnv "IX_SHARING_CORPUS_MODES").getD "tiered-tagN").splitOn ","
    let modes := modeNames.filterMap Mode.parse
    if modes.length != modeNames.length then
      return (false, 0, 0, some s!"unknown mode in {modeNames}")
    let limit := ((← IO.getEnv "IX_SHARING_CORPUS_LIMIT").bind String.toNat?)
    let t0 ← IO.monoMsNow
    let bytes ← IO.FS.readBinFile path
    let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
    let entries := env.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
    -- Optional selection: a file of hex addresses, one per line.
    let select ← match ← IO.getEnv "IX_SHARING_CORPUS_SELECT" with
      | some p => do
        let lines := (← IO.FS.readFile p).splitOn "\n" |>.map String.trim |>.filter (· != "")
        pure (some (lines.foldl (fun (s : Std.HashSet String) l => s.insert l) {}))
      | none => pure none
    let entries := match select with
      | some s => entries.filter fun (e : Address × Ixon.LazyConstant) => s.contains (toString e.1)
      | none => entries
    let entries := match limit with
      | some n => entries.extract 0 n
      | none => entries
    IO.println s!"    [corpus: {path}, {env.consts.size} constants, comparing {entries.size} under {modes.map Mode.name}; loaded in {(← IO.monoMsNow) - t0} ms]"
    let mut tallies : Array Tally := Array.replicate modes.length {}
    let mut decodeFailures := 0
    let mut done := 0
    for (addr, lc) in entries do
      let c ← match lc.get with
        | .ok c => pure c
        | .error _ =>
          decodeFailures := decodeFailures + 1
          continue
      let raw := lc.rawBytes
      let label := match env.addrToName.get? addr with
        | some n => s!"{n} ({addr})"
        | none => s!"{addr}"
      for h : k in [0:modes.length] do
        let m := modes[k]
        let (v, ln, rn) ← compareOne m c raw
        -- Lean-only exhaustion: find the limit that fires and the value that suffices.
        let v ← match v with
          | .resourceOnly true => do
            let d := diagnose m c (rustSide m raw)
            IO.println s!"      DIAGNOSIS {label} [{m.name}]: {d}"
            pure v
          | _ => pure v
        let t := tallies[k]!
        tallies := tallies.set! k
          { t.add label v with leanNs := t.leanNs + ln, rustNs := t.rustNs + rn }
      done := done + 1
      if done % 5000 == 0 then
        IO.println s!"    [corpus progress: {done}/{entries.size}]"
    let mut ok := decodeFailures == 0
    for h : k in [0:modes.length] do
      let t := tallies[k]!
      IO.println s!"    [corpus {modes[k].name}: {done} constants; {t.summary}; Lean {t.leanNs / 1000000} ms, Rust {t.rustNs / 1000000} ms]"
      for d in t.notes do
        IO.println s!"      NOTE {d}"
      for d in t.differences do
        IO.println s!"      DISAGREEMENT {d}"
      unless t.differences.isEmpty do ok := false
    IO.println s!"    [corpus: decode failures {decodeFailures}; total {(← IO.monoMsNow) - t0} ms]"
    return (ok, 0, 0, if ok then none else some "corpus disagreements; see above")) .done

public def suite : List TestSeq := [
  fixtureTests,
  generatedTests,
  corpusTests (),
]

end Tests.SharingExactFFI

end
