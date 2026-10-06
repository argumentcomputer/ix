/-
  validate-lean: `ix validate-lean --local`, the Phase A validator of record
  (`Ix.Cli.ValidateLeanCmd`), on every fixture of `aux-cert`, the prototype's
  cases (`Tests/Ix/Compile/Image/C*.lean`), the twin families
  (`Tests/Ix/Compile/Twins/*`) and the library twins
  (`Tests/Ix/Compile/Oracle/Lib.lean`), with the Pass 3 switch off and on,
  against the expected verdict table below.

  Every phase passes, except:
  - phase 7 (image rules) skips when there is no changed block with `_ix`
    names (always with the switch off; phase 6 fails a changed block without
    `_ix` names under the switch, so a skip cannot hide a lost image);
  - the recorded pre-existing failures (`expected`), each by defect id; a
    recorded failure that passes is a problem too, so the table stays exact,
    and a recorded failing phase must fail with exactly its recorded counts
    (`pins`: compile failures, comparison errors, digest mismatches and
    missing constants, decompile errors, unclassified auxiliaries, violations);
  - the files Lean itself rejects (`leanRejects`), which produce no report.

  Run with: `lake test -- --ignored validate-lean` (after `lake build ix`).
  `VALIDATE_LEAN_ONLY=<stem,…>` restricts the files; `VALIDATE_LEAN_KEEP=<dir>`
  keeps the logs and reports.
-/
import Lean.Data.Json
import Tests.Ix.Compile.AuxCert

open Lean

namespace Tests.Ix.Compile.ValidateLean

/-- A recorded failure: the file stem, the switch state (`off`, `on` or `*`),
the phases that fail, and the cause by defect id. -/
structure Expected where
  stem : String
  switch : String
  phases : List String
  cause : String

/-- The expected verdict table (A3v, 2026-10-03). The causes:
- A0 refusals on the surgery path (switch off; D13 = WB-B4): the compile
  refuses a collapse call site (phase 1), so the output is partial and the
  decompile misses the refused constants (phase 5). Pass 3 compiles them
  faithfully: these pass with the switch on.
- A0 evaporation refusal ("not a one-motive recursor", both modes): phase 1;
  the partial output's siblings of the refused component fail phases 4–5
  (REFUSED-SIBLING).
- REFUSED-IPB-COLLAPSE (CORPUS-IPB, M1-j; switch off): the compile refuses
  Lean's `IndPredBelow` block of a collapse that merges alpha-equivalent
  `.below` members (phase 1); the partial output's refused names have no
  `Named.original`, so they decompile to the canonical form (phase 5). With
  the switch on, Pass 3's images refuse the same family (phases 1, 5).
- Compile totality defects by id (WB-A2, WB-A3, WB-A7, BB-F6, BB-F8).
- Decompile and auxiliary defects by id (BB-F5, WB-B6, WB-B9).
- BELOW-ORDER (removed, A6f): the kernels' single-pass canonicity gate used to
  reject an adjacent pair comparing *weakly* `Greater` (a mutual cross
  reference under the final classes) instead of falling back to the full
  refinement; fixed in both kernels, so `ValidateLeanSwap` (user blocks of
  that shape), `PropCollapse` and the twins' `Repro` pass phase 4.
- A3V-IPB (found by the oracle leg): for the nested Prop block `F8NoSplit`
  (BB-F8's passing neighbour) the Ix `IndPredBelow` family's
  `.rec`/`.casesOn` (`A.below.rec`, `A.below_1.rec`, `.casesOn`) differ by
  address from Lean's own: the family is a permuted Lean-generated block.
  Fixed under the switch (A6f: the family is treated as a changed block,
  `Ix.Compile.Pass.editPermutedBelowFamily`); recorded with the switch off. -/
def expected : List Expected := [
  -- A0 collapse refusals on the surgery path
  ⟨"SurgCollapse", "off", ["1", "5"], "A0 refusal (D13: collapse call site drops distinct arguments)"⟩,
  ⟨"F4FlatAlphaUsers", "off", ["1", "5"], "A0 refusal (collapse call site is a partial application)"⟩,
  ⟨"F4_NestedAlphaUsers", "off", ["1", "5"], "A0 refusal (collapse call site is a partial application)"⟩,
  ⟨"C5Collapse", "off", ["1", "5"], "A0 refusal (D13)"⟩,
  ⟨"C6NestedCollapse", "off", ["1", "5"], "A0 refusal (collapse call site is a partial application)"⟩,
  ⟨"C7IndPred", "off", ["1", "5"], "A0 refusal (D13, on `below` call sites)"⟩,
  ⟨"C8Collapse3", "off", ["1", "5"], "A0 refusal (D13)"⟩,
  ⟨"C9Params", "off", ["1", "5"], "A0 refusal (D13)"⟩,
  ⟨"Proto", "off", ["1", "5"], "A0 refusals (D13, partial applications) of the prototype twins"⟩,
  -- CORPUS-IPB (M1-j): the default path refuses the Lean `IndPredBelow`
  -- block of a collapse that merges alpha-equivalent `.below` members; with
  -- the switch on Pass 3's images refuse the same shapes (`image: hypothesis
  -- motive N not in its slot's class`, a Pass 3 item of M1)
  ⟨"IPBCollapse2p1", "off", ["1", "5"], "REFUSED-IPB-COLLAPSE (CORPUS-IPB)"⟩,
  ⟨"IPBCollapse2p1", "on", ["1", "5"], "Pass 3 images refusal (hypothesis motive not in its slot's class)"⟩,
  ⟨"IPBMixed", "off", ["1", "5"], "REFUSED-IPB-COLLAPSE (CORPUS-IPB)"⟩,
  ⟨"IPBMixed", "on", ["1", "5"], "Pass 3 images refusal (hypothesis motive not in its slot's class)"⟩,
  ⟨"IPBCollapseNone", "off", ["6", "8"], "A3V-IPB (its IndPredBelow .rec/.casesOn ≠ Lean's; fixed by Pass 3)"⟩,
  -- A0 evaporation refusal, both modes
  ⟨"C4Evap", "off", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"C4Evap", "on", ["1", "5"], "A0 refusal (not a one-motive recursor)"⟩,
  ⟨"F3_SplitRoseRace", "*", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"NestRoseSplit", "*", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"NestMutExt", "off", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"NestMutExt", "on", ["1", "5"], "A0 refusal (not a one-motive recursor)"⟩,
  ⟨"NestMutExtA", "*", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  -- compile totality defects
  ⟨"AliasIdx", "*", ["1", "5"], "WB-A3"⟩,
  ⟨"KernelSpec", "*", ["1", "5"], "WB-A7"⟩,
  ⟨"SurgIdx", "off", ["1", "5"], "WB-A2 (fixed by Pass 3)"⟩,
  ⟨"F6_OrderIdxBrecOn", "off", ["1", "5"], "BB-F6 (= WB-A2; fixed by Pass 3)"⟩,
  ⟨"F8_PropSplitNested", "off", ["1", "5"], "BB-F8 (fixed by Pass 3)"⟩,
  -- decompile and auxiliary defects
  ⟨"F5_SigmaNestedNested", "*", ["5"], "BB-F5 (decompile regenerates T.rec differently)"⟩,
  ⟨"RecAlias", "*", ["5", "6", "8"], "WB-B6 (Ix's PA.below family ≠ Lean's)"⟩,
  ⟨"UnsafeI", "*", ["5", "6", "8"], "WB-B9 (Ix's UNestNeg.rec ≠ Lean's)"⟩,
  ⟨"Neighbours", "off", ["6", "8"], "A3V-IPB (F8NoSplit's IndPredBelow .rec/.casesOn ≠ Lean's; fixed by Pass 3)"⟩,
  ⟨"ValidateLeanIPB", "off", ["6", "8"], "A3V-IPB (reproducer: IPB.Nested, IPB.MutNested; fixed by Pass 3)"⟩,
  -- the twin families: their RecAlias (WB-B6) and SurgCollapse (A0) members
  ⟨"Repro", "off", ["1", "5", "6", "8"], "A0 refusal of Repro.Orig.SurgCollapse (D13); WB-B6"⟩,
  ⟨"Repro", "on", ["5", "6", "8"], "WB-B6"⟩,
  -- the clique-ownership sources (added with phase 9, M4): the block rule refuses
  -- `WF8B.caller`, a caller outside the clique's unit that unfolds the transported
  -- clique's encoding (by design, M1-a: a named block failure, so phase 5 misses it)
  ⟨"Sources", "on", ["1", "5"], "block-rule caller refusal by design (WF8B.caller; M1-a)"⟩]

/-- The counts of a failing phase's detail, which the record pins: phase 6
its unclassified auxiliaries, phase 8 its violations, any other phase the
detail's first clause (`49 per-block compile failure(s)`, `7 comparison
error(s)`, `68 digest mismatch(es), 55 missing`, `3 decompile error(s)`). -/
def failSummary (key detail : String) : String :=
  match key with
  | "6" => match (detail.splitOn "unclassified ")[1]? with
    | some r => s!"unclassified {(r.splitOn ";").headD r}"
    | none => detail
  | "8" => (detail.splitOn "; ").getLastD detail
  | _ => ((((detail.splitOn " (").headD detail).splitOn ";").headD detail).trimAscii.toString

/-- The counts of each recorded failing phase (`failSummary`), per stem and
switch state (KF triage, 2026-10-05): a recorded phase that fails with more
(or fewer) failures than recorded fails the suite.

Re-record M1-d (commit "Selected closures carry whole logical units"; the
11 entries marked `M1-d re-record`): `--local` now carries the whole logical
unit of every block it reaches (design document §6.3), so the closures of
these files are larger. Every one of them already fails phase 1 (the A0
refusals and BB-F8, recorded above with unchanged counts); the phase-5
digest mismatches and missing names grow by the same number (1, 2 or 4)
except `F8_PropSplitNested` off (+4 mismatches, +3 missing: one decompiled
constant differs, and `Nat` is among the listed names; `Nat` decompiles
digest-identical in a closure without the failing blocks,
`ix validate-lean --ns Nat.succ,Nat.rec` on the same file: 173/173). -/
def pins : List (String × String × String × String) := [
  ("AliasIdx", "off", "1", "31 per-block compile failure(s)"),
  ("AliasIdx", "off", "5", "31 digest mismatch(es), 31 missing"),
  ("AliasIdx", "on", "1", "31 per-block compile failure(s)"),
  ("AliasIdx", "on", "5", "31 digest mismatch(es), 31 missing"),
  ("C4Evap", "off", "1", "49 per-block compile failure(s)"),
  ("C4Evap", "off", "4", "7 comparison error(s)"),
  ("C4Evap", "off", "5", "70 digest mismatch(es), 57 missing"), -- M1-d re-record, was 68/55
  ("C4Evap", "on", "1", "58 per-block compile failure(s)"),
  ("C4Evap", "on", "5", "79 digest mismatch(es), 73 missing"), -- M1-d re-record, was 77/71
  ("C5Collapse", "off", "1", "8 per-block compile failure(s)"),
  ("C5Collapse", "off", "5", "8 digest mismatch(es), 8 missing"),
  ("C6NestedCollapse", "off", "1", "12 per-block compile failure(s)"),
  ("C6NestedCollapse", "off", "5", "12 digest mismatch(es), 12 missing"),
  ("C7IndPred", "off", "1", "4 per-block compile failure(s)"),
  ("C7IndPred", "off", "5", "4 digest mismatch(es), 4 missing"),
  ("C8Collapse3", "off", "1", "18 per-block compile failure(s)"),
  ("C8Collapse3", "off", "5", "18 digest mismatch(es), 18 missing"),
  ("C9Params", "off", "1", "6 per-block compile failure(s)"),
  ("C9Params", "off", "5", "6 digest mismatch(es), 6 missing"),
  ("F3_SplitRoseRace", "off", "1", "41 per-block compile failure(s)"),
  ("F3_SplitRoseRace", "off", "4", "9 comparison error(s)"),
  ("F3_SplitRoseRace", "off", "5", "54 digest mismatch(es), 43 missing"), -- M1-d re-record, was 50/39
  ("F3_SplitRoseRace", "on", "1", "43 per-block compile failure(s)"),
  ("F3_SplitRoseRace", "on", "4", "2 comparison error(s)"),
  ("F3_SplitRoseRace", "on", "5", "56 digest mismatch(es), 52 missing"), -- M1-d re-record, was 52/48
  ("F4FlatAlphaUsers", "off", "1", "1 per-block compile failure(s)"),
  ("F4FlatAlphaUsers", "off", "5", "1 digest mismatch(es), 1 missing"),
  ("F4_NestedAlphaUsers", "off", "1", "1 per-block compile failure(s)"),
  ("F4_NestedAlphaUsers", "off", "5", "1 digest mismatch(es), 1 missing"),
  ("F5_SigmaNestedNested", "off", "5", "11 decompile error(s)"),
  ("F5_SigmaNestedNested", "on", "5", "11 decompile error(s)"),
  ("F6_OrderIdxBrecOn", "off", "1", "2 per-block compile failure(s)"),
  ("F6_OrderIdxBrecOn", "off", "5", "2 digest mismatch(es), 2 missing"),
  ("F8_PropSplitNested", "off", "1", "3 per-block compile failure(s)"),
  ("F8_PropSplitNested", "off", "5", "12 digest mismatch(es), 6 missing"), -- M1-d re-record, was 8/3
  ("IPBCollapse2p1", "off", "1", "9 per-block compile failure(s)"),
  ("IPBCollapse2p1", "off", "5", "7 digest mismatch(es), 0 missing"),
  ("IPBCollapse2p1", "on", "1", "6 per-block compile failure(s)"),
  ("IPBCollapse2p1", "on", "5", "6 digest mismatch(es), 6 missing"),
  ("IPBCollapseNone", "off", "6", "unclassified 6"),
  ("IPBCollapseNone", "off", "8", "6 violation(s)"),
  ("IPBMixed", "off", "1", "11 per-block compile failure(s)"),
  ("IPBMixed", "off", "5", "9 digest mismatch(es), 0 missing"),
  ("IPBMixed", "on", "1", "8 per-block compile failure(s)"),
  ("IPBMixed", "on", "5", "8 digest mismatch(es), 8 missing"),
  ("KernelSpec", "off", "1", "16 per-block compile failure(s)"),
  ("KernelSpec", "off", "5", "7 decompile error(s)"),
  ("KernelSpec", "on", "1", "16 per-block compile failure(s)"),
  ("KernelSpec", "on", "5", "7 decompile error(s)"),
  ("Neighbours", "off", "6", "unclassified 6"),
  ("Neighbours", "off", "8", "6 violation(s)"),
  ("NestMutExt", "off", "1", "84 per-block compile failure(s)"),
  ("NestMutExt", "off", "4", "14 comparison error(s)"),
  ("NestMutExt", "off", "5", "110 digest mismatch(es), 88 missing"), -- M1-d re-record, was 106/84
  ("NestMutExt", "on", "1", "88 per-block compile failure(s)"),
  ("NestMutExt", "on", "5", "114 digest mismatch(es), 106 missing"), -- M1-d re-record, was 110/102
  ("NestMutExtA", "off", "1", "43 per-block compile failure(s)"),
  ("NestMutExtA", "off", "4", "9 comparison error(s)"),
  ("NestMutExtA", "off", "5", "56 digest mismatch(es), 45 missing"), -- M1-d re-record, was 55/44
  ("NestMutExtA", "on", "1", "45 per-block compile failure(s)"),
  ("NestMutExtA", "on", "4", "2 comparison error(s)"),
  ("NestMutExtA", "on", "5", "58 digest mismatch(es), 54 missing"), -- M1-d re-record, was 57/53
  ("NestRoseSplit", "off", "1", "43 per-block compile failure(s)"),
  ("NestRoseSplit", "off", "4", "9 comparison error(s)"),
  ("NestRoseSplit", "off", "5", "56 digest mismatch(es), 45 missing"), -- M1-d re-record, was 52/41
  ("NestRoseSplit", "on", "1", "45 per-block compile failure(s)"),
  ("NestRoseSplit", "on", "4", "2 comparison error(s)"),
  ("NestRoseSplit", "on", "5", "58 digest mismatch(es), 54 missing"), -- M1-d re-record, was 54/50
  ("Proto", "off", "1", "50 per-block compile failure(s)"),
  ("Proto", "off", "5", "50 digest mismatch(es), 50 missing"),
  ("RecAlias", "off", "5", "3 decompile error(s)"),
  ("RecAlias", "off", "6", "unclassified 5"),
  ("RecAlias", "off", "8", "5 violation(s)"),
  ("RecAlias", "on", "5", "3 decompile error(s)"),
  ("RecAlias", "on", "6", "unclassified 5"),
  ("RecAlias", "on", "8", "5 violation(s)"),
  ("Repro", "off", "1", "11 per-block compile failure(s)"),
  ("Repro", "off", "5", "6 decompile error(s)"),
  ("Repro", "off", "6", "unclassified 10"),
  ("Repro", "off", "8", "10 violation(s)"),
  ("Repro", "on", "5", "6 decompile error(s)"),
  ("Repro", "on", "6", "unclassified 10"),
  ("Repro", "on", "8", "10 violation(s)"),
  ("SurgCollapse", "off", "1", "7 per-block compile failure(s)"),
  ("SurgCollapse", "off", "5", "7 digest mismatch(es), 7 missing"),
  ("SurgIdx", "off", "1", "3 per-block compile failure(s)"),
  ("SurgIdx", "off", "5", "3 digest mismatch(es), 3 missing"),
  ("UnsafeI", "off", "5", "7 decompile error(s)"),
  ("UnsafeI", "off", "6", "unclassified 2"),
  ("UnsafeI", "off", "8", "2 violation(s)"),
  ("UnsafeI", "on", "5", "7 decompile error(s)"),
  ("UnsafeI", "on", "6", "unclassified 2"),
  ("UnsafeI", "on", "8", "2 violation(s)"),
  ("ValidateLeanIPB", "off", "6", "unclassified 10"),
  ("ValidateLeanIPB", "off", "8", "10 violation(s)"),
  ("Sources", "on", "1", "1 per-block compile failure(s)"),
  ("Sources", "on", "5", "1 digest mismatch(es), 1 missing")
]

def pinOf (stem switch key : String) : Option String :=
  pins.findSome? fun (s, sw, k, p) => if s == stem && sw == switch && k == key then some p else none

/-- Phase 9 (clique values, plan M4 (b)): the exact detail of every run
whose phase 9 passes, i.e. every switch-on run that transports a definition
clique (2026-10-06, first recording; cause: the phase is new). A run that
transports none skips phase 9; a recorded run that does not pass, or passes
with other counts, fails the suite. -/
def phase9Pins : List (String × String × String) := [
  ("SurgCollapse", "on", "1 transported clique(s) (0 value-checked, 1 with no value-checkable member, each with a reason, 0 failing), 2 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 2 not value-checkable; 0 failure(s)"),
  ("SurgCollapseEq", "on", "1 transported clique(s) (0 value-checked, 1 with no value-checkable member, each with a reason, 0 failing), 2 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 2 not value-checkable; 0 failure(s)"),
  ("F4_NestedAlphaUsers", "on", "1 transported clique(s) (0 value-checked, 1 with no value-checkable member, each with a reason, 0 failing), 4 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 4 not value-checkable; 0 failure(s)"),
  ("Neighbours", "on", "4 transported clique(s) (1 value-checked, 3 with no value-checkable member, each with a reason, 0 failing), 9 member(s): 1 value-checked on 1 input tuple(s) (1 closed, 0 symbolic), 8 not value-checkable; 0 failure(s)"),
  ("DotCtor", "on", "1 transported clique(s) (0 value-checked, 1 with no value-checkable member, each with a reason, 0 failing), 2 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 2 not value-checkable; 0 failure(s)"),
  ("F6_OrderIdxBrecOn", "on", "1 transported clique(s) (0 value-checked, 1 with no value-checkable member, each with a reason, 0 failing), 2 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 2 not value-checkable; 0 failure(s)"),
  ("C5Collapse", "on", "2 transported clique(s) (0 value-checked, 2 with no value-checkable member, each with a reason, 0 failing), 4 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 4 not value-checkable; 0 failure(s)"),
  ("C6NestedCollapse", "on", "2 transported clique(s) (0 value-checked, 2 with no value-checkable member, each with a reason, 0 failing), 8 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 8 not value-checkable; 0 failure(s)"),
  ("C8Collapse3", "on", "4 transported clique(s) (1 value-checked, 3 with no value-checkable member, each with a reason, 0 failing), 11 member(s): 2 value-checked on 4 input tuple(s) (4 closed, 0 symbolic), 9 not value-checkable; 0 failure(s)"),
  ("C9Params", "on", "1 transported clique(s) (0 value-checked, 1 with no value-checkable member, each with a reason, 0 failing), 2 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 2 not value-checkable; 0 failure(s)"),
  -- re-recorded INT-fix (discovery by record): +1 `TN.P0` (na, nb; theorems, no value-checkable
  -- member), transported per the record but invisible to the `_ix`-name discovery (its canonical
  -- constants are TN.P1's by address, stored under TN.P1's `_ix` names); +1 value-checked clique of
  -- two members that the old discovery also counted on the integrated line (43) but not at M4: the
  -- clique code and the fixture are identical between `jcb/ix-cc-m4` and `jcb/ix-cc-int`, the
  -- difference is the integrated closure (`Ix/Common.lean`, `Ix/EnvScope.lean`: whole logical units)
  ("Cliques", "on", "44 transported clique(s) (30 value-checked, 14 with no value-checkable member, each with a reason, 0 failing), 105 member(s): 74 value-checked on 767 input tuple(s) (719 closed, 48 symbolic), 31 not value-checkable; 0 failure(s)"),
  ("Proto", "on", "9 transported clique(s) (1 value-checked, 8 with no value-checkable member, each with a reason, 0 failing), 25 member(s): 2 value-checked on 4 input tuple(s) (4 closed, 0 symbolic), 23 not value-checkable; 0 failure(s)"),
  ("Repro", "on", "3 transported clique(s) (0 value-checked, 3 with no value-checkable member, each with a reason, 0 failing), 8 member(s): 0 value-checked on 0 input tuple(s) (0 closed, 0 symbolic), 8 not value-checkable; 0 failure(s)"),
  ("Sources", "on", "23 transported clique(s) (23 value-checked, 0 with no value-checkable member, each with a reason, 0 failing), 46 member(s): 46 value-checked on 276 input tuple(s) (180 closed, 96 symbolic), 0 not value-checkable; 0 failure(s)")
]

def phase9PinOf (stem switch : String) : Option String :=
  phase9Pins.findSome? fun (s, sw, p) => if s == stem && sw == switch then some p else none

/-- Phase 9's controls (INT-fix, 2026-10-06): runs whose output carries O7–O12
canonical forms under `_ix` names (definition display members, recorded
`PJ-FORM-<pass>` in the non-canonical set) and transports no definition
clique. Phase 9 discovers cliques from the compiler's clique record, so it
must skip with 0 transported cliques while reporting at least one `_ix`
definition display member (the forms are there; they are not cliques). Before
the discovery by record, phase 9 counted each such form as a clique. -/
def phase9Controls : List (String × String × String) := [
  ("O9Split", "on", "O9: `A.len._ix`, `A.sum._ix`, `A.cnt._ix` and the helper `A.len._ix_retyped._f`; no clique")
]

/-- The skip detail of phase 9 when the record has no transported clique, and
the number of `_ix` definition display members it reports. -/
def phase9SkipCount? (detail : String) : Option Nat := do
  let rest ← (detail.splitOn "no transported definition clique in the compiler's clique record (")[1]?
  ((rest.splitOn " ").headD "").toNat?

/-- Fixtures Lean itself rejects (the aux-cert record): no report. -/
def leanRejects : List String := ["PropEvap", "SortU", "SortURec", "SortUOpt"]

def files : List String :=
  Tests.Ix.Compile.AuxCert.fixtures.map (fun f => s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean")
  ++ (["C1Perm", "C2Split", "C3PropSplit", "C4Evap", "C5Collapse", "C6NestedCollapse", "C7IndPred",
       "C8Collapse3", "C9Params"].map fun s => s!"Tests/Ix/Compile/Image/{s}.lean")
  ++ (["Cliques", "Proto", "Repro"].map fun s => s!"Tests/Ix/Compile/Twins/{s}.lean")
  ++ ["Tests/Ix/Compile/Oracle/Lib.lean", "Tests/Ix/Compile/ValidateLeanIPB.lean",
      "Tests/Ix/Compile/ValidateLeanSwap.lean",
      -- the clique-ownership sources: phase 9 on the compiler's own transports of
      -- user values, binders and relations of the packing type (plan M4 (b))
      "Tests/Ix/Compile/CliqueOwnership/Sources.lean",
      -- phase 9's control (`phase9Controls`): O9 canonical forms, no clique
      "Tests/Ix/Compile/Pass/O9Split.lean"]

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- A run's result: stem, switch, phase verdicts and details (none: no report), exit. -/
abbrev Row := String × String × Option (List (String × String × String)) × String

/-- One run: the phase verdicts by key (`pass`, `fail`, `skip`), or `none` when
no report was written. -/
def runOne (dir : System.FilePath) (file switch : String) :
    IO Row := do
  let stem := (System.FilePath.mk file).fileStem.getD file
  let report := dir / s!"{stem}-{switch}.json"
  let exe ← IO.FS.realPath ixExe
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #["validate-lean", "--local", "--workers", "8", "--report", report.toString, file]
    env := #[("LD_LIBRARY_PATH", none),
             ("IX_PASS3", if switch == "on" then some "images" else none)] }
  IO.FS.writeFile (dir / s!"{stem}-{switch}.log") (out.stdout ++ out.stderr)
  if !(← report.pathExists) then return (stem, switch, none, s!"exit {out.exitCode}")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile report))
  let phases ← IO.ofExcept (j.getObjValAs? (Array Json) "phases")
  let rows := phases.toList.filterMap fun p =>
    match p.getObjValAs? String "key", p.getObjValAs? String "result" with
    | .ok k, .ok r => some (k, r, (p.getObjValAs? String "detail").toOption.getD "")
    | _, _ => none
  return (stem, switch, some rows, s!"exit {out.exitCode}")

def run : IO UInt32 := do
  let only := ((← IO.getEnv "VALIDATE_LEAN_ONLY").map (·.splitOn ",")).getD []
  let keep? := (← IO.getEnv "VALIDATE_LEAN_KEEP").map System.FilePath.mk
  let dir ← match keep? with
    | some d => do IO.FS.createDirAll d; pure d
    | none => IO.FS.createTempDir
  let todo := (files.filter fun f =>
      only.isEmpty || only.contains ((System.FilePath.mk f).fileStem.getD f)).flatMap fun f =>
    [(f, "off"), (f, "on")]
  let t0 ← IO.monoMsNow
  -- a pool of four runs at a time
  let mut results : Array Row := #[]
  let mut pending : Array (Task (Except IO.Error Row)) := #[]
  for (f, s) in todo do
    if pending.size ≥ 4 then
      results := results.push (← IO.ofExcept pending[0]!.get)
      pending := pending.extract 1 pending.size
    pending := pending.push (← IO.asTask (runOne dir f s))
  for t in pending do results := results.push (← IO.ofExcept (← IO.wait t))
  let mut problems : Array String := #[]
  for (stem, switch, rows?, exit) in results do
    let exp := expected.filter fun e => e.stem == stem && (e.switch == switch || e.switch == "*")
    let failing : List String := exp.flatMap (·.phases)
    let causes := ", ".intercalate (exp.map (·.cause))
    match rows? with
    | none =>
      if leanRejects.contains stem then
        IO.println s!"[validate-lean] {stem} {switch}: Lean rejects the file (aux-cert record; {exit})"
      else problems := problems.push s!"{stem} {switch}: no report ({exit})"
    | some rows =>
      let line := " ".intercalate (rows.map fun (k, r, _) => s!"{k}={r}")
      IO.println s!"[validate-lean] {stem} {switch}: {line}{if causes.isEmpty then "" else s!"  [{causes}]"}"
      if leanRejects.contains stem then
        problems := problems.push s!"{stem} {switch}: recorded as rejected by Lean, but a report was written"
      for (k, r, d) in rows do
        let want := failing.contains k
        if r == "fail" && !want then problems := problems.push s!"{stem} {switch}: phase {k} fails (not recorded)"
        if r != "fail" && want then problems := problems.push s!"{stem} {switch}: phase {k} recorded as failing ({causes}) but {r}"
        -- phase 9 skips exactly when no definition clique is transported
        -- (always with the switch off); a switch-on run that transports one
        -- must value-check it with exactly its recorded counts
        if r == "skip" && k != "7" && k != "9" then problems := problems.push s!"{stem} {switch}: phase {k} skipped"
        if k == "9" then
          if switch == "off" && r != "skip" then
            problems := problems.push s!"{stem} {switch}: phase 9 {r} with the switch off (no clique can be transported)"
          if r == "pass" then
            IO.println s!"[validate-lean]   {stem} {switch} phase 9: {d}"
            match phase9PinOf stem switch with
            | some p => if p != d then problems := problems.push s!"{stem} {switch}: phase 9 passes with '{d}', recorded '{p}'"
            | none => problems := problems.push s!"{stem} {switch}: phase 9 passes with '{d}', no count recorded"
          else if (phase9PinOf stem switch).isSome then
            problems := problems.push s!"{stem} {switch}: phase 9 recorded as value-checking but {r}"
          if phase9Controls.any (fun (s, sw, _) => s == stem && sw == switch) then
            match r, phase9SkipCount? d with
            | "skip", some n =>
              IO.println s!"[validate-lean]   {stem} {switch} phase 9 control: 0 transported clique(s), {n} `_ix` definition display member(s)"
              if n == 0 then
                problems := problems.push s!"{stem} {switch}: phase 9 control has no `_ix` definition display member (vacuous): '{d}'"
            | _, _ => problems := problems.push s!"{stem} {switch}: phase 9 control must skip with 0 transported cliques, got {r} '{d}'"
        -- a recorded failing phase fails exactly as recorded: its counts
        if r == "fail" && want then
          let s := failSummary k d
          IO.println s!"[validate-lean]   {stem} {switch} phase {k}: {s}"
          match pinOf stem switch k with
          | some p =>
            if p != s then
              problems := problems.push s!"{stem} {switch}: phase {k} fails with '{s}', recorded '{p}'"
          | none => problems := problems.push s!"{stem} {switch}: phase {k} fails with '{s}', no count recorded"
  -- every phase-9 pin belongs to a run whose phase 9 passed
  for (stem, switch, p) in phase9Pins do
    let used := results.any fun (s, sw, rows?, _) => s == stem && sw == switch &&
      (rows?.getD []).any fun (k', r, _) => k' == "9" && r == "pass"
    if !used && (only.isEmpty || only.contains stem) then
      problems := problems.push s!"{stem} {switch}: phase 9 recorded as '{p}' (stale)"
  -- every phase-9 control ran
  for (stem, switch, _) in phase9Controls do
    let ran := results.any fun (s, sw, rows?, _) => s == stem && sw == switch &&
      (rows?.getD []).any fun (k', _, _) => k' == "9"
    if !ran && (only.isEmpty || only.contains stem) then
      problems := problems.push s!"{stem} {switch}: phase 9 control did not run"
  -- every pin belongs to a recorded failing phase of a run
  for (stem, switch, k, p) in pins do
    let used := results.any fun (s, sw, rows?, _) => s == stem && sw == switch &&
      (rows?.getD []).any fun (k', r, _) => k' == k && r == "fail"
    if !used && (only.isEmpty || only.contains stem) then
      problems := problems.push s!"{stem} {switch}: phase {k} recorded as failing with '{p}' (stale)"
  for p in problems do IO.println s!"[validate-lean] FAIL {p}"
  IO.println s!"[validate-lean] {results.size} runs ({todo.length / 2} files × 2 switch states), \
{problems.size} problem(s), {(← IO.monoMsNow) - t0} ms"
  if keep?.isNone then IO.FS.removeDirAll dir
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.ValidateLean
