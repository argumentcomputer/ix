/-
  The kernel-failure record of `pass3` (KF triage, 2026-10-05): every failure
  of the three checkers (`cert`, the certified checker; `rs`, `ix check-rs`;
  `lean`, `ix check-lean`, both in meta mode) on every unit, in Pass 3, each
  tagged with its cause. Until M6R slice 6 (2026-10-07) the record also held
  the failures with the switch off (the legacy call-site surgery, 192 rows);
  they went with the surgery, and every row's `switch` is `on`. The units'
  compile failures, which no checker sees, are recorded apart
  (`compileFailures`).

  A row covers the failures of one unit, switch state and leg whose message
  contains `msg`: exactly the names listed, or (a large uniform class)
  exactly `count` of them. The check runs both ways: a failure no row covers
  fails the suite, and so does a row whose names do not all fail or whose
  count is not met exactly (stale). A row of a meta-mode-only cause
  (`metaOnly`) covers a failure only where the certified checker accepts the
  same constant. Rows marked `varies` are the cells where the meta kernels'
  verdicts change from run to run on the same output (check-rs follows its
  hash order, check-lean its workers' scheduling; measured over six runs):
  there any failure of the row's class is covered where the certified checker
  and the anonymous kernels (run on that output for this) accept the same
  constant, and at least one must occur, except in a `varies` row that also
  carries `mayBeEmpty` (the cause, as text, why the class may occur zero
  times on a run): there the class may be absent. Only a `varies` row may
  carry it (a non-varying row with it fails the suite), and it relaxes
  nothing but the "at least one" of that row: the covering conditions are
  unchanged. One row carries it, `Neighbours (on)`'s `app type mismatch`
  (KF triage §4; M1-a measured it failing stale on one run and passing the
  next on the same tree; INT-fix, 2026-10-06). Each leg must also check every
  requested name (`check`).

  The causes:
  - `BB-F7`: `Ix.Tc`'s meta mode on the aliases of a collapsed block (members
    alpha-equivalent to each other or to an existing constant, for example
    `SurgCollapse.A`/`B`, which have `Nat`'s address): the aliases get no
    entry under their own names, so constants whose metadata names them fail
    (`unknown constant <address>`, or `app type mismatch` between two
    aliases), and the requested alias names match no work item. The
    certified checker and anonymous mode accept every one of them. The lean
    leg checks every item from a fresh worker state (`--clear-every 1`): the
    kernel's caches are keyed by name-insensitive expression addresses, so a
    warm cache can resolve an alias reference through another item's
    inference, and the count would depend on the work-stealing order (FU
    item 13).
  - `BB-F1`: the Rust kernel's counterpart (`AppTypeMismatch`,
    `ctor return type: head is not the inductive`); the certified checker
    and anonymous mode accept them.
  - `REFUSED-SIBLING (A0 …)`: the compile refused a block on purpose (A0's
    "not a one-motive recursor"); constants that reach the refused member
    through metadata cannot be resolved by the meta kernels (its named entry
    is absent). `Ix.Tc`'s whole-environment meta ingress stops at the first
    such entry, so the `lean` leg checks nothing in those units (name `*`,
    checked 0). Anonymous mode accepts them.
  - `BB-F6 (= WB-A2)` (history, switch off only): the same for the dependents
    of a constant whose compile fails (`F6_OrderIdxBrecOn`).
  - `WB-…`, `BB-F5`, `WB §6`: the documented compiler and checker defects of
    `aux-cert` (`Tests/Ix/Compile/AuxCert.lean`), on the same fixtures and
    their twins; `WB-B3` also covers the prototype's and the twins' split
    blocks with the same failures (`C2Split`, `C9Params`, `DQSplit`, `DQMut`,
    and the O9 fixture `O9Split`, whose structural functions over a split
    block the surgery path compiles the same way).
  - `KF-O1`, `KF-C7`, `KF-UNIVM`: default-path defects without an earlier id
    (KF triage; `KF-O1` and `KF-C7` history since M6R slice 6): with the switch off, `recOn` of a permuted mutual block
    (`PassO1.Src.Odd.viaRecOn`) and the `IndPredBelow` case split of a mutual
    Prop block (`C7b.Src.EvenP.toR.match_2`) are ill-typed for all three
    checkers; in both switch states, the nested recursors of
    `IxVMInd.UnivM` (two nested occurrences of one inductive at different
    universes) are rejected by both executable kernels in both modes
    (`canonical-order mismatch`), and accepted by the certified checker,
    which does not check auxiliary order.
  - `KF-O1C` (history since M6R slice 6; found when the O7–O12 fixtures joined the record, M1-b): with
    the switch off, `recOn` of a collapsed mutual block
    (`PassO7.Src.B.viaRecOn`, its value pin `viaRecOn_one`) is rejected by
    the certified checker (`application type mismatch`) and the Rust kernel;
    the call-site surgery family of `KF-O1`, not separately triaged; the
    switch-on output accepts it (Pass 3 compiles it through the image).
    Milestone M6 (the flip retires the surgery), with `KF-O1`.
  - `CERT-AXIOM`: the certified checker declines axioms outside its standard
    set (`Tests.Ix.Compile.LevelSpellings` declares its own).
  - CORPUS-IPB (M1-j), units `IPBCollapse2p1` and `IPBMixed` (the corpus
    shapes `M3_P_alpha2p1`, `M4_P_mixed`): Pass 3 refuses the family's images
    (`switchOnRefusals`); until M6R slice 6 the switch-off compile refused
    Lean's `IndPredBelow` block instead (`REFUSED-IPB-COLLAPSE`, deleted with
    the surgery). Their
    kernel failures are all meta-mode only, on the collapsed aliases
    (`BB-F1`, `BB-F7`; the same names in four runs): the certified checker
    and anonymous mode accept every checked constant. Their valid neighbour
    `IPBCollapseNone` has no failure.
-/

import Std.Data.HashSet

namespace Tests.Ix.Compile.Pass3Kernels

/-- Recorded failures of one unit, switch state and leg with a message class. -/
structure Expect where
  unit : String
  switch : String
  leg : String
  cause : String
  /-- a substring of every covered failure's message -/
  msg : String
  /-- the names, exactly; empty: `count` names -/
  names : List String := []
  count : Nat := 0
  /-- the failures vary between runs on the same output (the meta kernels'
  verdicts on collapsed aliases, BB-F1/BB-F7, follow check-rs's hash order
  and check-lean's scheduling): any failure of the class is covered where the
  certified checker and the anonymous kernels (run for this) accept the same
  constant, and at least one must occur -/
  varies : Bool := false
  /-- only with `varies`: the class may occur zero times on a run; the text is
  the cause (why a run can see none). Relaxes only the "at least one". -/
  mayBeEmpty : Option String := none

/-- Causes that are defects of the meta-mode kernels only: a failure is
covered only where the certified checker accepts the constant. -/
def metaOnly (cause : String) : Bool :=
  cause.startsWith "BB-F7" || cause.startsWith "BB-F1"

def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- Check the failures of one unit and switch state against `table`.
`failed` holds `(leg, name, message)`; `checked` each leg's checked count;
`requested` the number of names requested; `anon?` the `(leg, name)` failures
of the anonymous kernels on the same output, run where a row `varies`.
Returns the problems and one
summary line. -/
def check (table : List Expect) (unit switch : String)
    (failed : Array (String × String × String)) (checked : List (String × Nat))
    (requested : Nat) (anon? : Option (Std.HashSet (String × String)) := none) :
    Array String × String := Id.run do
  let rows := (table.filter fun e => e.unit == unit && e.switch == switch).toArray
  let certFail : Std.HashSet String := failed.foldl (fun s (l, n, _) =>
    if l == "cert" then s.insert n else s) {}
  let mut problems : Array String := #[]
  let mut hits : Array (Array String) := rows.map fun _ => #[]
  for (leg, n, m) in failed do
    -- a row naming the constant first, then a counted row
    let fits := fun (e : Expect) => e.leg == leg && hasSub m e.msg &&
      !(metaOnly e.cause && certFail.contains n) &&
      -- a varying row covers only what the anonymous kernels accept
      (!e.varies || anon?.any fun s => !s.contains (leg, n))
    let i? := match rows.findIdx? (fun e => fits e && e.names.contains n) with
      | some i => some i
      | none => rows.findIdx? fun e => fits e && e.names.isEmpty
    match i? with
    | some i => hits := hits.modify i (·.push n)
    | none =>
      problems := problems.push s!"{unit} ({switch}): {leg}: {n} fails, not recorded: {m.take 300}"
  for (e, hs) in rows.zip hits do
    if e.mayBeEmpty.isSome && !e.varies then
      problems := problems.push s!"{unit} ({switch}): {e.leg} [{e.cause}] '{e.msg}': \
        `mayBeEmpty` on a row that does not vary (record error)"
    if e.varies then
      if hs.isEmpty && e.mayBeEmpty.isNone then
        problems := problems.push s!"{unit} ({switch}): {e.leg} [{e.cause}] '{e.msg}': \
          no failure of the class occurs (stale)"
    else if e.names.isEmpty then
      if hs.size != e.count then
        problems := problems.push s!"{unit} ({switch}): {e.leg} [{e.cause}] '{e.msg}': \
          recorded {e.count} failure(s), {hs.size} occur{if hs.size < e.count then " (stale)" else ""}"
    else
      for n in e.names do
        unless hs.contains n do
          problems := problems.push s!"{unit} ({switch}): {e.leg}: {n} recorded as failing \
            ({e.cause}) but does not (stale)"
  -- each leg checked what was requested: cert and rs every name; lean every
  -- name but the selectors it reports as matching nothing, or nothing at all
  -- where a recorded `*` row says its ingress stops
  for (leg, k) in checked do
    let aborted := rows.any fun e => e.leg == leg && e.names == ["*"]
    let unmatched := (failed.filter fun (l, _, m) =>
      l == leg && m == "requested selector matched no checkable work item").size
    let want := if aborted then 0 else requested - unmatched
    if k != want then
      problems := problems.push s!"{unit} ({switch}): {leg} checked {k} constant(s), expected {want} \
        ({requested} requested{if unmatched > 0 then s!", {unmatched} unmatched" else ""}{if aborted then ", ingress stops" else ""})"
  -- failures per leg and cause, for the log
  let mut byCause : Array (String × Nat) := #[]
  for (e, hs) in rows.zip hits do
    if hs.isEmpty then continue
    let k := s!"{e.leg} {(e.cause.splitOn " (").headD e.cause}"
    byCause := match byCause.findIdx? (·.1 == k) with
      | some i => byCause.modify i fun (k, n) => (k, n + hs.size)
      | none => byCause.push (k, hs.size)
  let summary := s!"{failed.size} failure(s) in {rows.size} recorded row(s) \
    {byCause.toList.map fun (k, n) => s!"{k}: {n}"}; \
    checked {checked.map fun (l, k) => s!"{l} {k}"} of {requested}"
  -- a row that may be empty says how many of its class occurred on this run
  let maybe := (rows.zip hits).filterMap fun (e, hs) =>
    if e.mayBeEmpty.isSome then some s!"{e.leg} [{e.cause}] '{e.msg}' (may be empty): {hs.size} occur" else none
  let summary := if maybe.isEmpty then summary else s!"{summary}; {"; ".intercalate maybe.toList}"
  return (problems, summary)

/-- The record (generated by `PASS3_EXPECT_EMIT` from a dump, then reviewed). -/
def table : List Expect := [
  { unit := "SurgCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["SurgCollapse.A", "SurgCollapse.A.a", "SurgCollapse.A.nil"] },
  { unit := "SurgCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 71 },
  { unit := "SurgCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", names := ["SurgCollapse.B.g"] },
  { unit := "SurgCollapseEq", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["SurgCollapseEq.B", "SurgCollapseEq.B.b", "SurgCollapseEq.B.nil"] },
  { unit := "SurgCollapseEq", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 74 },
  { unit := "F4FlatAlphaUsers", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["F4FlatAlphaUsers.A", "F4FlatAlphaUsers.A.s", "F4FlatAlphaUsers.A.z"] },
  { unit := "F4FlatAlphaUsers", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 56 },
  { unit := "F4_NestedAlphaUsers", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["B", "B._ix.rec", "B.leaf", "B.node"] },
  { unit := "F4_NestedAlphaUsers", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 76 },
  { unit := "F3_SplitRoseRace", switch := "on", leg := "rs", cause := "REFUSED-SIBLING (A0 refuses the block of A: not a one-motive recursor)",
    msg := "Named entry for 'A", count := 10 },
  { unit := "F3_SplitRoseRace", switch := "on", leg := "lean", cause := "REFUSED-SIBLING (A0 refuses the block of A: not a one-motive recursor)",
    msg := "Named entry for 'A", names := ["*"] },
  { unit := "NestRoseSplit", switch := "on", leg := "rs", cause := "REFUSED-SIBLING (A0 refuses the block of NestRoseSplit.A: not a one-motive recursor)",
    msg := "Named entry for 'NestRoseSplit.A", count := 10 },
  { unit := "NestRoseSplit", switch := "on", leg := "lean", cause := "REFUSED-SIBLING (A0 refuses the block of NestRoseSplit.A: not a one-motive recursor)",
    msg := "Named entry for 'NestRoseSplit.A", names := ["*"] },
  { unit := "NestMutExt", switch := "on", leg := "rs", cause := "REFUSED-SIBLING (A0 refuses the block of NestMutExt.A: not a one-motive recursor)",
    msg := "Named entry for 'NestMutExt.A", count := 20 },
  { unit := "NestMutExt", switch := "on", leg := "lean", cause := "REFUSED-SIBLING (A0 refuses the block of NestMutExt.A: not a one-motive recursor)",
    msg := "Named entry for 'NestMutExt.A", names := ["*"] },
  { unit := "NestMutExtA", switch := "on", leg := "rs", cause := "REFUSED-SIBLING (A0 refuses the block of NestMutExtA.A: not a one-motive recursor)",
    msg := "Named entry for 'NestMutExtA.A", count := 10 },
  { unit := "NestMutExtA", switch := "on", leg := "lean", cause := "REFUSED-SIBLING (A0 refuses the block of NestMutExtA.A: not a one-motive recursor)",
    msg := "Named entry for 'NestMutExtA.A", names := ["*"] },
  { unit := "Neighbours", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 18 },
  { unit := "Neighbours", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 337 },
  { unit := "Neighbours", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", varies := true,
    mayBeEmpty := some "check-lean's verdict on the collapsed aliases depends on which work item a worker \
      meets first (KF triage §4): this cell's 'app type mismatch' class is small and some runs see none \
      (M1-a: failed stale on one run, passed the next, same tree)" },
  { unit := "NestShapes", switch := "on", leg := "cert", cause := "WB §6",
    msg := "blocked: ", count := 25 },
  { unit := "NestShapes", switch := "on", leg := "cert", cause := "WB §6",
    msg := "decline: reader: in-process model", names := ["NestShapes.R", "NestShapes.R.leaf", "NestShapes.R.mk", "NestShapes.R.rec", "NestShapes.R.rec_1"] },
  { unit := "PropCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["PropCollapse.Q", "PropCollapse.Q._ix.below", "PropCollapse.Q._ix.below.step", "PropCollapse.Q.step"] },
  { unit := "PropCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 29 },
  { unit := "RecAlias", switch := "on", leg := "cert", cause := "WB-B6",
    msg := "reject: function expected", names := ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] },
  { unit := "RecAlias", switch := "on", leg := "cert", cause := "WB-B6",
    msg := "blocked: ", names := ["RecAlias.PA.triv"] },
  { unit := "RecAlias", switch := "on", leg := "rs", cause := "WB-B6",
    msg := "FunExpected", names := ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] },
  { unit := "RecAlias", switch := "on", leg := "lean", cause := "WB-B6",
    msg := "function expected", names := ["RecAlias.PA.brecOn", "RecAlias.PA.triv.match_2"] },
  { unit := "SurgAlias", switch := "on", leg := "cert", cause := "WB-B5",
    msg := "blocked: ", names := ["SurgAlias.A._sizeOf_inst", "SurgAlias.A.a.sizeOf_spec", "SurgAlias.A.nil.sizeOf_spec"] },
  { unit := "SurgAlias", switch := "on", leg := "cert", cause := "WB-B5",
    msg := "reject: application type mismatch", names := ["SurgAlias.A._sizeOf_1"] },
  { unit := "SurgAlias", switch := "on", leg := "rs", cause := "WB-B5",
    msg := "AppTypeMismatch", names := ["SurgAlias.A._sizeOf_1"] },
  { unit := "SurgAlias", switch := "on", leg := "rs", cause := "WB-B5",
    msg := "declaration type mismatch", names := ["SurgAlias.A.a.sizeOf_spec"] },
  { unit := "SurgAlias", switch := "on", leg := "lean", cause := "WB-B5",
    msg := "app type mismatch", names := ["SurgAlias.A._sizeOf_1"] },
  { unit := "SurgAlias", switch := "on", leg := "lean", cause := "WB-B5",
    msg := "declaration type mismatch", names := ["SurgAlias.A.a.sizeOf_spec"] },
  { unit := "UnsafeI", switch := "on", leg := "rs", cause := "WB-B9",
    msg := "check_recursor: could not resolve inductive block", names := ["UnsafeI.UNestNeg.rec", "UnsafeI.UNestNeg.rec_1"] },
  { unit := "UnsafeI", switch := "on", leg := "lean", cause := "WB-B9",
    msg := "check_recursor: could not resolve inductive block", names := ["UnsafeI.UNestNeg.rec", "UnsafeI.UNestNeg.rec_1"] },
  { unit := "F1_Collapse2p1", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", count := 62 },
  { unit := "F1_Collapse2p1", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "ctor return type: head is not the inductive", count := 9 },
  { unit := "F1_Collapse2p1", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["B", "B._ix.rec", "B.s", "B.z"] },
  { unit := "F1_Collapse2p1", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 72 },
  { unit := "F1_Collapse2p1", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", count := 17 },
  { unit := "F5_SigmaNestedNested", switch := "on", leg := "rs", cause := "BB-F5",
    msg := "check_recursor: could not resolve inductive block", names := ["T.rec", "T.rec_1", "T.rec_2"] },
  { unit := "F5_SigmaNestedNested", switch := "on", leg := "lean", cause := "BB-F5",
    msg := "check_recursor: could not resolve inductive block", names := ["T.rec", "T.rec_1", "T.rec_2"] },
  { unit := "F7_AlphaVLean", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["B", "B.s", "B.z"] },
  { unit := "F7_AlphaVLean", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 56 },
  { unit := "KernelSpec", switch := "on", leg := "cert", cause := "WB-A7",
    msg := "blocked: ", count := 20 },
  { unit := "KernelSpec", switch := "on", leg := "cert", cause := "WB-A7",
    msg := "decline: reader: in-process model", names := ["KernelSpec.T", "KernelSpec.T.leaf", "KernelSpec.T.mk", "KernelSpec.T.rec", "KernelSpec.T.rec_1"] },
  { unit := "KernelSpec", switch := "on", leg := "rs", cause := "WB-A7",
    msg := "check_recursor: could not resolve inductive block", names := ["KernelSpec.T.rec", "KernelSpec.T.rec_1"] },
  { unit := "KernelSpec", switch := "on", leg := "lean", cause := "WB-A7",
    msg := "check_recursor: could not resolve inductive block", names := ["KernelSpec.T.rec", "KernelSpec.T.rec_1"] },
  { unit := "C4Evap", switch := "on", leg := "rs", cause := "REFUSED-SIBLING (A0 refuses the block of C4b.Src.A: not a one-motive recursor)",
    msg := "Named entry for 'C4b.Src.A", count := 156 },
  { unit := "C4Evap", switch := "on", leg := "lean", cause := "REFUSED-SIBLING (A0 refuses the block of C4b.Src.A: not a one-motive recursor)",
    msg := "Named entry for 'C4b.Src.A", names := ["*"] },
  { unit := "C5Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["C5.Src.B", "C5.Src.B.b", "C5.Src.B.nil"] },
  { unit := "C5Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 85 },
  { unit := "C6NestedCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["C6.Src.B", "C6.Src.B._ix.rec", "C6.Src.B.leaf", "C6.Src.B.node"] },
  { unit := "C6NestedCollapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 97 },
  { unit := "C7IndPred", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["C7.Src.P", "C7.Src.P._ix.below", "C7.Src.P._ix.below.base", "C7.Src.P._ix.below.step", "C7.Src.P.base", "C7.Src.P.step"] },
  { unit := "C7IndPred", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 40 },
  { unit := "C8Collapse3", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  { unit := "C8Collapse3", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 10 },
  { unit := "C8Collapse3", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 212 },
  { unit := "C8Collapse3", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", varies := true },
  { unit := "C9Params", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["C9b.Src.B", "C9b.Src.B.b", "C9b.Src.B.nil"] },
  { unit := "C9Params", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 74 },
  { unit := "O1Perm", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["PassO1.Col.A", "PassO1.Col.A.a", "PassO1.Col.A.nil"] },
  { unit := "O1Perm", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 59 },
  { unit := "O3Cases", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", names := ["PassO3.Col.A", "PassO3.Col.A.a", "PassO3.Col.A.nil"] },
  { unit := "O3Cases", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 59 },
  { unit := "twins", switch := "on", leg := "cert", cause := "WB-B6",
    msg := "reject: function expected", names := ["Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.brecOn", "Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.triv.match_1_7", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.brecOn", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.triv.match_1_7"] },
  { unit := "twins", switch := "on", leg := "cert", cause := "WB-B6",
    msg := "blocked: ", names := ["Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.triv", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.triv"] },
  { unit := "twins", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  { unit := "twins", switch := "on", leg := "rs", cause := "WB-B6",
    msg := "FunExpected", names := ["Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.brecOn", "Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.triv.match_1_7", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.brecOn", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.triv.match_1_7"] },
  { unit := "twins", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 41 },
  { unit := "twins", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 666 },
  { unit := "twins", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", varies := true },
  { unit := "twins", switch := "on", leg := "lean", cause := "WB-B6",
    msg := "function expected", names := ["Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.brecOn", "Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.triv.match_1_7", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.brecOn", "Tests.Ix.Compile.Twins.Repro.Twin.Tw.RecAlias.PA.triv.match_1_7"] },
  -- CORPUS-IPB (M1-j): the refused units' meta-mode failures on collapsed aliases (four runs, stable)
  { unit := "IPBCollapse2p1", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", count := 51 },
  { unit := "IPBCollapse2p1", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "ctor return type: head is not the inductive", count := 9 },
  { unit := "IPBCollapse2p1", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 12 },
  { unit := "IPBCollapse2p1", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 47 },
  { unit := "IPBCollapse2p1", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", names := ["IPBCollapse2p1.A.casesOn", "IPBCollapse2p1.A.rec", "IPBCollapse2p1.B.rec", "IPBCollapse2p1.C.rec"] },
  { unit := "IPBMixed", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", count := 58 },
  { unit := "IPBMixed", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "FunExpected", count := 11 },
  { unit := "IPBMixed", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 12 },
  { unit := "IPBMixed", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 63 },
  { unit := "IPBMixed", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", names := ["IPBMixed.A.rec", "IPBMixed.B.casesOn", "IPBMixed.B.rec", "IPBMixed.C.rec", "IPBMixed.D.rec"] },
  { unit := "corpus", switch := "on", leg := "cert", cause := "CERT-AXIOM",
    msg := "decline: non-standard axiom", count := 20 },
  { unit := "corpus", switch := "on", leg := "rs", cause := "KF-UNIVM",
    msg := "populate_recursor_rules_from_block: canonical-order mismatch", names := ["IxVMInd.UnivM.rec", "IxVMInd.UnivM.rec_1", "IxVMInd.UnivM.rec_2"] },
  { unit := "corpus", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 162 },
  -- re-recorded (FU item 13): 2457 → 2461. The lean leg now checks every item
  -- from a fresh worker state (`--clear-every 1`); warm caches let 4 BB-F7
  -- references resolve through another item's cached inference, depending on
  -- the work-stealing order (`…Canonicity.ProdNestedTwin1.A._sizeOf_6`,
  -- `…ProdNestedTwin2.X._sizeOf_4`, `…Mutual.NestedAuxOrderingProd.A._sizeOf_5`,
  -- `…NestedAuxOrderingProd.C2._sizeOf_5`; one gate run missed one rescue: 2458)
  { unit := "corpus", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 2461 },
  { unit := "corpus", switch := "on", leg := "lean", cause := "KF-UNIVM",
    msg := "populate_recursor_rules_from_block: canonical-order mismatch", names := ["IxVMInd.UnivM.rec", "IxVMInd.UnivM.rec_1", "IxVMInd.UnivM.rec_2"] },
  -- the per-pass fixtures of O7–O12 (M1-b: the units joined the record with the rebase of the
  -- A6p commits; written by `PASS3_EXPECT_EMIT` from a run, its anonymous recheck and three meta
  -- rechecks of the same outputs)
  { unit := "O7Collapse", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  { unit := "O7Collapse", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "ctor return type: head is not the inductive", count := 15 },
  { unit := "O7Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 7 },
  { unit := "O7Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 137 },
  { unit := "O7Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", varies := true },
  { unit := "O8Cases", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  { unit := "O8Cases", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 7 },
  { unit := "O8Cases", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", count := 139 },
  { unit := "O8Cases", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "app type mismatch", varies := true },
  { unit := "O10O12Collapse", switch := "on", leg := "rs", cause := "BB-F1",
    msg := "AppTypeMismatch", varies := true },
  { unit := "O10O12Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "requested selector matched no checkable work item", count := 10 },
  { unit := "O10O12Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "unknown constant ", varies := true },
  -- `app type mismatch` and `declaration type mismatch` (`C8.Src.h_ex`, `f_ex`): one varying
  -- class, since the latter is absent from some runs (measured: present in five runs, absent in
  -- the full-suite run)
  { unit := "O10O12Collapse", switch := "on", leg := "lean", cause := "BB-F7",
    msg := "type mismatch", varies := true }
]

/-- The root block failures of a unit, by exact name, with their cause and a
substring of their message: the refusals of Pass 2 (A0's "not a one-motive
recursor") and the compile totality defects (WB-A3, WB-A7). `pass3` checks them
both ways, and every other failure must be a consequence of one (its message
names a root or an earlier consequence, REFUSED-SIBLING) or a recorded image
refusal (`switchOnRefusals`). Until M6R slice 6 the roots were not recorded:
they were the constants failing in both switch states, read off the legacy
surgery's compile of the same unit; written from a run by
`PASS3_EMIT_FAILURES=1`, then reviewed (the causes are the `aux-cert` and
`validate-lean` records' for the same fixtures). -/
structure CompileFailure where
  unit : String
  cause : String
  msg : String
  names : List String

def compileFailures : List CompileFailure := [
]

/-- Step 2's decompile problems that are documented defects of the decompile
roundtrip, by unit and the constant each problem names (`decompile mismatch:
n`, `decompile error n: …`, `not decompiled: n`), with the defect. Until M6R
slice 6 they were exempted as "also with the switch off": the legacy
surgery's output of the same unit decompiled with the same problems
(`[pass3] … N problem(s) (N also with the switch off)` at `e020a72e`: RecAlias
6, UnsafeI 13, F5_SigmaNestedNested 18, twins 12); the slice-6 run measured
the same sets. `pass3` checks them both ways (an unrecorded problem fails, and
so does a recorded name with none). -/
structure DecompileKnown where
  unit : String
  cause : String
  names : List String

def decompileKnown : List DecompileKnown := [
]


/-- Compile failures that are refusals of Pass 3's own images, by unit and
exact name, recorded with their cause and a substring of their message. `pass3`
checks them both ways (an unrecorded failure and a recorded name that does not
fail so are both problems). -/
structure OnRefusal where
  unit : String
  cause : String
  msg : String
  names : List String

/-- CORPUS-IPB (M1-j): in `IPBCollapse2p1` (corpus `M3_P_alpha2p1`) and
`IPBMixed` (`M4_P_mixed`) Pass 3 refuses the images of the family's
`.below.rec`/`.below.casesOn` (a partially collapsed Prop block; a Pass 3 item
of M1). Until M6R slice 6 the switch-off compile refused Lean's `IndPredBelow`
block instead (`REFUSED-IPB-COLLAPSE`, deleted with the surgery); the name
`switchOnRefusals` is kept. -/
def switchOnRefusals : List OnRefusal := [
  { unit := "IPBCollapse2p1", msg := "image: ",
    cause := "CORPUS-IPB, switch on: Pass 3 images of a partially collapsed Prop block's IndPredBelow family",
    names := ["IPBCollapse2p1.A.below.rec", "IPBCollapse2p1.B.below.rec", "IPBCollapse2p1.C.below.rec",
      "IPBCollapse2p1.A.below.casesOn", "IPBCollapse2p1.B.below.casesOn", "IPBCollapse2p1.C.below.casesOn"] },
  { unit := "IPBMixed", msg := "image: ",
    cause := "CORPUS-IPB, switch on: Pass 3 images of a partially collapsed Prop block's IndPredBelow family",
    names := ["IPBMixed.A.below.rec", "IPBMixed.B.below.rec", "IPBMixed.C.below.rec", "IPBMixed.D.below.rec",
      "IPBMixed.A.below.casesOn", "IPBMixed.B.below.casesOn", "IPBMixed.C.below.casesOn",
      "IPBMixed.D.below.casesOn"] }
]

/-! ## Writing the record from a dump (`PASS3_EXPECT_EMIT=<rows.tsv>,<recheck.tsv>`) -/

/-- The message class of a failure: a substring every failure of the class
carries (addresses and terms vary). -/
def msgClass (m : String) : String := Id.run do
  if let some rest := (m.splitOn "Named entry for '")[1]? then
    if let some x := (rest.splitOn "'")[0]? then
      -- a refused block's members (`A`, `A2`) are named in hash order: the
      -- class is the name without its trailing digits
      let x := String.ofList (x.toList.reverse.dropWhile Char.isDigit).reverse
      return s!"Named entry for '{x}"
  for p in ["unknown constant ", "requested selector matched no checkable work item",
      "app type mismatch", "AppTypeMismatch", "ctor return type: head is not the inductive",
      "check_recursor: could not resolve inductive block", "universe param count",
      "incorrect number of universe levels", "blocked: ", "decline: reader: in-process model",
      "decline: non-standard axiom", "decline: projection on a non-structure",
      "reject: application type mismatch", "reject: function expected", "FunExpected",
      "function expected", "declaration type mismatch",
      "projection: type mismatch with declared struct", "projection: struct type is not a constant",
      "populate_recursor_rules_from_block: canonical-order mismatch"] do
    if hasSub m p then return p
  return (m.take 60).toString

/-- The documented defect a constant's failure in every mode belongs to, by
its name (the fixture families keep the fixtures' namespaces). -/
def defectOf (unit name : String) : String := Id.run do
  for (p, d) in [("RecAlias", "WB-B6"), ("SurgAlias", "WB-B5"), ("SurgSplit", "WB-B3"),
      ("C2.Src.", "WB-B3"), ("C9.Src.", "WB-B3"), ("DQSplit", "WB-B3"), ("DQMut", "WB-B3"),
      ("SurgIdx", "WB-A2"), ("UnsafeI", "WB-B9"),
      ("PropCollapse", "WB-B2"), ("PropSplit", "WB-B2"), ("Coind", "WB-B2"), ("C3.Src.", "WB-B2"),
      ("C3b.Src.", "WB-B2"), ("PassO5.", "WB-B2"), ("C7b.Src.", "KF-C7"), ("PassO1.Src.", "KF-O1"), ("PassO7.Src.", "KF-O1C"), ("PassO9.Src.", "WB-B3"),
      ("IxVMInd.UnivM", "KF-UNIVM"), ("NestShapes", "WB §6"), ("KernelSpec", "WB-A7")] do
    if hasSub name p then return d
  match unit with
  | "F5_SigmaNestedNested" => "BB-F5"
  | "KernelSpec" => "WB-A7"
  | "NestShapes" => "WB §6"
  | "L2_PropSplit" => "WB-B2"
  | _ => "UNCLASSIFIED"

/-- The cause of one failure. `anonFails`: the same leg rejects the name in
anonymous mode; `certFails`: the certified checker rejects it. -/
def causeOf (unit leg name msg : String) (anonFails certFails : Bool) : String :=
  let cls := msgClass msg
  if cls.startsWith "Named entry for '" then
    let x := (cls.drop 17).toString
    if x == "A.w" then "BB-F6 (= WB-A2): A.w fails to compile; its dependents"
    else s!"REFUSED-SIBLING (A0 refuses the block of {x}: not a one-motive recursor)"
  else if leg == "cert" then
    if cls == "decline: non-standard axiom" then "CERT-AXIOM" else defectOf unit name
  else if !anonFails && !certFails then (if leg == "lean" then "BB-F7" else "BB-F1")
  else defectOf unit name

/-- Read a dump: `(unit, switch, leg, name, message)` rows. -/
def readDump (path : String) : IO (Array (String × String × String × String × String)) := do
  let mut out := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | u :: s :: l :: n :: rest => out := out.push (u, s, l, n, "\t".intercalate rest)
    | _ => pure ()
  return out

/-- The `mayBeEmpty` control (run by `pass3` before its units): the record's
`mayBeEmpty` rows are exactly `Neighbours (on)`'s `lean` `app type mismatch`
row, which varies; on synthetic failures that row passes with none and with
one of its class (the anonymous kernels accepting it), and passes nothing
else: the same row without `mayBeEmpty` and with no failure is stale, a
failure the anonymous kernels also reject is not covered, and `mayBeEmpty`
on a non-varying row is a record error. Returns the problems (empty: the
control holds) and a summary line. -/
def mayBeEmptyControl : Array String × String := Id.run do
  let marked := table.filter (·.mayBeEmpty.isSome)
  let mut problems : Array String := #[]
  let some row := marked.head?
    | return (#["mayBeEmpty control: no row carries `mayBeEmpty`"], "")
  unless marked.length == 1 && row.unit == "Neighbours" && row.switch == "on" && row.leg == "lean" &&
      row.msg == "app type mismatch" && row.varies do
    let shown := marked.map fun e => s!"{e.unit} ({e.switch}) {e.leg} '{e.msg}' varies={e.varies}"
    problems := problems.push s!"mayBeEmpty control: the marked rows are {shown}"
  let fail : Array (String × String × String) := #[("lean", "X.a", "app type mismatch: X.a")]
  let ck (t : List Expect) (f : Array (String × String × String)) (anon : Std.HashSet (String × String)) :=
    (check t row.unit row.switch f [] 0 (some anon)).1.size
  let none0 := ck [row] #[] {}
  let one0 := ck [row] fail {}
  let strict := ck [{ row with mayBeEmpty := none }] #[] {}
  let anonRejects := ck [row] fail (({} : Std.HashSet (String × String)).insert ("lean", "X.a"))
  let notVarying := ck [{ row with varies := false, count := 0 }] #[] {}
  unless none0 == 0 do problems := problems.push s!"mayBeEmpty control: no failure gives {none0} problem(s), expected 0"
  unless one0 == 0 do problems := problems.push s!"mayBeEmpty control: one failure gives {one0} problem(s), expected 0"
  unless strict == 1 do problems := problems.push s!"mayBeEmpty control: without the flag, no failure gives {strict} problem(s), expected 1 (stale)"
  unless anonRejects == 1 do problems := problems.push s!"mayBeEmpty control: a failure the anonymous kernels reject gives {anonRejects} problem(s), expected 1 (not covered)"
  unless notVarying ≥ 1 do problems := problems.push "mayBeEmpty control: the flag on a non-varying row is not refused"
  return (problems, s!"mayBeEmpty control: {marked.length} marked row(s); problems with 0/1 failures {none0}/{one0}, \
    without the flag {strict}, anonymous-rejected {anonRejects}, on a non-varying row {notVarying}")

/-- Print the record (`Expect` rows) from a suite dump (`rows`), its
anonymous recheck (`recheck`, switches `on-anon`/`off-anon`) and further
meta rechecks of the same outputs (`more`, switches `on-meta`/`off-meta`):
one row per unit, switch, leg, cause and message class. A row whose names
are the same in every run lists them (at most six) or counts them; a row
whose names differ between runs (check-rs on collapsed aliases) lists the
union and is marked `varies`. -/
def emit (rowsPath recheckPath : String) (more : List String) : IO UInt32 := do
  let rows ← readDump rowsPath
  let re ← readDump recheckPath
  let anon : Std.HashSet String := re.foldl (fun s (u, sw, l, n, _) =>
    if sw.endsWith "-anon" then s.insert s!"{u}|{(sw.dropEnd 5).toString}|{l}|{n}" else s) {}
  let cert : Std.HashSet String := rows.foldl (fun s (u, sw, l, n, _) =>
    if l == "cert" then s.insert s!"{u}|{sw}|{n}" else s) {}
  let mut runs : Array (Array (String × String × String × String × String)) := #[rows]
  for p in more do
    let r ← readDump p
    runs := runs.push (r.filterMap fun (u, sw, l, n, m) =>
      if sw.endsWith "-meta" then some (u, (sw.dropEnd 5).toString, l, n, m) else none)
  -- per run, the names of each group
  let mut groups : Array ((String × String × String × String × String) × Array (Array String)) := #[]
  for i in [0:runs.size] do
    for (u, sw, l, n, m) in runs[i]! do
      let c := causeOf u l n m (anon.contains s!"{u}|{sw}|{l}|{n}") (cert.contains s!"{u}|{sw}|{n}")
      let key := (u, sw, l, c, msgClass m)
      let mut idx := groups.size
      match groups.findIdx? (·.1 == key) with
      | some j => idx := j
      | none => groups := groups.push (key, Array.replicate runs.size #[])
      groups := groups.modify idx fun (k, per) => (k, per.modify i (·.push n))
  for ((u, sw, l, c, cls), per) in groups do
    let sorted := per.map fun ns => ns.qsort (· < ·)
    let stable := sorted.all (· == sorted[0]!)
    let union := (sorted.foldl (· ++ ·) #[]).qsort (· < ·) |>.toList.eraseDups
    let who := if !stable then
        "varies := true"
      else if union.length ≤ 6 then
        s!"names := [{", ".intercalate (union.map (·.quote))}]"
      else s!"count := {sorted[0]!.size}"
    IO.println s!"  \{ unit := {u.quote}, switch := {sw.quote}, leg := {l.quote}, cause := {c.quote},\n    msg := {cls.quote}, {who} },"
  return 0

end Tests.Ix.Compile.Pass3Kernels
