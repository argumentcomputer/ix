/-
  The non-canonical record's types, and the twins' expected refusals.

  The record itself is `Tests.Ix.Compile.NonCanonicalDefault.nonCanonical`:
  every byte difference between two presentations of a twin family
  (`Tests.Ix.Compile.Twins.allFamilies`) that the compiler produces, with its
  cause. The `twins` suite reads it under the records policy:
  - the key (fixture, presentations, constant) is exact in both directions:
    a difference without an entry and an entry without a difference both fail;
  - the cause is reviewed and strict: an entry whose cause is `unreviewed`
    fails;
  - the evidence is pinned: the two addresses, the class of the difference
    and the first differing node must equal the run's.

  When bytes move (each byte-moving batch), the record is re-recorded with
  the suite's re-record mode (`IX_TWINS_RECORD=<file>`, see
  `Tests.Ix.Compile.Twins`), and the diff of the data file is reviewed: moved
  addresses, new differences (`unreviewed` until a cause is assigned) and
  removed ones.

  Causes. The compiler on this line is Pass 3's faithful rewrite (images of a
  changed block's auxiliaries; no definitional pass, no clique transport,
  today's canonical layout; the call-site surgery is gone since the flip). A
  `pending*` cause names the queue entry expected to remove the difference;
  its re-record must then show the entry gone, or give it a permanent cause. The other causes are permanent: the presentations'
  Lean terms differ in a way no canonical form removes.
-/
import Lean

namespace Tests.Ix.Compile.NonCanonical

inductive NonCanonicalCause where
  /-- Lean's tactic output depends on the presentation beyond the packing. -/
  | tacticAsym
  /-- The clique transport's grammar fails; the fallback keeps Lean's packing. -/
  | shape
  /-- GuessLex chose a different measure for a different function order. -/
  | guessLex
  /-- Structural recursion chose a different recursive argument. -/
  | recArg
  /-- A statement that follows the order (`mutual_induct`, `induct`,
      `_mutual.eq_unfold`, bare `@f._mutual`). -/
  | orderStmt
  /-- A bare or partial occurrence of a grouping-dependent auxiliary. -/
  | bare
  /-- The Lean names over a collapsed pair with different arms. -/
  | collapseArms
  /-- Lean's `IndPredBelow` family of a changed Prop block. -/
  | indPredBelow
  /-- A theorem clique whose order cannot be determined. -/
  | noSpec
  /-- A lazily realised equation lemma. -/
  | lazy
  /-- Pass 3: the Lean name of an image-kind head of a changed block (`rec`,
      `casesOn`, `recOn`, `below*`, `brecOn*`, `.go`, `.eq`) holds its image,
      Lean's own form over the canonical constants, so it follows the
      presentation (its motive and minor order, the member it eliminates
      into) by design; the canonical constant is under its `_ix` display name
      (`Ix.Compile.Pass.ixAuxName`). -/
  | image
  /-- The constant's own term is identical under the name map; it differs
      only because it references a differing constant (its class lists them). -/
  | inherited
  /-- Pending CQ5.2 (clique transport): the clique encoding's packing order
      (`PSum` summands, `PProd` factors, the packed `below` motives and
      functionals, the projection paths into them, the fixed-parameter
      telescope). -/
  | pendingTransport
  /-- A Lean auxiliary (`below`, `brecOn`, `rec_N`, …) that Lean generates
      (or not) by the member's Lean block rather than its Ix block, so one
      presentation has it and the other does not. Batch 3 (CQ3.3 A2, CQ3.4
      D6) and CQ4.2 (Pass 3) are done: the canonical constants are equal
      under their `_ix` display names, while the Lean names exist on one side
      only, which no canonical form removes; the name stays for the record's
      history. -/
  | pendingSplitAux
  /-- Pending CQ5.3 (O11b): Lean's `noConfusion` in enumeration form. -/
  | pendingNoConfusion
  /-- Pending CQ5.1 (O2–O6, the definitional passes): a caller of a changed
      block, compiled faithfully over the images. Either its Lean term follows
      its presentation (the motive order and `PProd` packing of its structural
      recursion over Lean's `below`/`brecOn`, a matcher's arms), or its terms
      are equal under the name map but Pass 3 develops a head's image at the
      occurrence in one presentation and keeps the call in the other (an
      unchanged presentation has no image, its head is the canonical
      auxiliary itself: class `UNEXPLAINED`, explained by this cause; the
      users of `casesOn`: `ctorIdx`, matchers, `noConfusionType`). The passes
      write the canonical call; CQ5.1's re-record gives a permanent cause to
      the differences they leave (the donor's record after its passes keeps
      the structural recursions of `Proto.C2`, `C4`, `C9`, `Repro.DQMut`,
      `DQSplit` and `SurgSplit`). (Until the flip these differences were the
      call-site surgery's to remove, `pendingSurgery`, deleted with it.) -/
  | pendingPasses
  /-- Pending CQ5.3 (O7–O12): the collapse passes. -/
  | pendingCollapse
  /-- Pending CQ5.3 (O11a): Lean's mutual `_sizeOf_N` over a split block. -/
  | o11aPending
  /-- Pending CQ3.3 (levels after `canonUniv`): nested occurrences whose levels
      differ in spelling only (`Fixtures.NestedLevels`). -/
  | pendingLevels
  /-- Written by the re-record mode for a new difference: the suggested cause
      (Lean syntax, e.g. `".pendingPasses"`), to be reviewed against the dumped
      terms (`IX_TWINS_DUMP`) and replaced by a cause. The gate fails while any
      entry has it. -/
  | unreviewed (suggested : String)
  deriving Repr, BEq, Inhabited

def NonCanonicalCause.tag : NonCanonicalCause → String
  | .tacticAsym => "TACTIC-ASYM" | .shape => "SHAPE" | .guessLex => "GUESSLEX"
  | .recArg => "RECARG" | .orderStmt => "ORDER-STMT" | .bare => "BARE"
  | .collapseArms => "COLLAPSE-ARMS" | .indPredBelow => "INDPRED-BELOW"
  | .noSpec => "NOSPEC" | .lazy => "LAZY" | .inherited => "INHERITED"
  | .pendingTransport => "PENDING-TRANSPORT" | .pendingSplitAux => "PENDING-SPLIT-AUX"
  | .pendingNoConfusion => "PENDING-NOCONFUSION"
  | .pendingCollapse => "PENDING-COLLAPSE" | .o11aPending => "O11A-PENDING"
  | .pendingLevels => "PENDING-LEVELS" | .image => "IMAGE"
  | .pendingPasses => "PENDING-PASSES"
  | .unreviewed s => s!"UNREVIEWED({s})"

/-- The cause as Lean syntax, for the re-recorded data file. -/
def NonCanonicalCause.syntax : NonCanonicalCause → String
  | .tacticAsym => ".tacticAsym" | .shape => ".shape" | .guessLex => ".guessLex"
  | .recArg => ".recArg" | .orderStmt => ".orderStmt" | .bare => ".bare"
  | .collapseArms => ".collapseArms" | .indPredBelow => ".indPredBelow"
  | .noSpec => ".noSpec" | .lazy => ".lazy" | .inherited => ".inherited"
  | .pendingTransport => ".pendingTransport" | .pendingSplitAux => ".pendingSplitAux"
  | .pendingNoConfusion => ".pendingNoConfusion"
  | .pendingCollapse => ".pendingCollapse" | .o11aPending => ".o11aPending"
  | .pendingLevels => ".pendingLevels" | .image => ".image"
  | .pendingPasses => ".pendingPasses"
  | .unreviewed s => s!"(.unreviewed {s.quote})"

/-- How a difference shows in the two presentations' Lean terms under the
    name map. Computed by the suite (`Tests.Ix.Compile.Twins.comparePair`);
    pinned in the record. -/
inductive DiffClass where
  /-- The terms differ: in the type, in the value or rules, and whether they
      are equal once the `PSum`/`PProd` packing is erased (`packKey`). -/
  | root (type value pack : Bool)
  /-- The terms are equal; the constant references these differing constants
      (relative to presentation A). -/
  | inherited (via : List Lean.Name)
  /-- The terms are equal and no reference differs: a canonicity defect of the
      compiler, unless the cause says otherwise. -/
  | unexplained
  /-- A constant of presentation A with no counterpart in B. -/
  | onlyA
  /-- A constant of presentation B with no counterpart in A (named by its map
      into A). -/
  | onlyB
  deriving Repr, BEq, Inhabited

def DiffClass.tag : DiffClass → String
  | .root t v k =>
    s!"ROOT[{if t then "T" else ""}{if v then "V" else ""}{if k then "|K" else ""}]"
  | .inherited _ => "INHERITED"
  | .unexplained => "UNEXPLAINED"
  | .onlyA => "ONLY-A"
  | .onlyB => "ONLY-B"

/-- A name as a Lean term (`Name`'s `Repr`: a quoted name when it is one). -/
def nameSyntax (n : Lean.Name) : String := (repr n).pretty

def DiffClass.syntax : DiffClass → String
  | .root t v k => s!"(.root {t} {v} {k})"
  | .inherited via => s!"(.inherited [{", ".intercalate (via.map nameSyntax)}])"
  | .unexplained => ".unexplained"
  | .onlyA => ".onlyA"
  | .onlyB => ".onlyB"

structure NonCanonicalEntry where
  /-- the twin family, e.g. `Tests.Ix.Compile.Twins.Cliques.SA` -/
  fixture : Lean.Name
  presA : String
  presB : String
  /-- the constant's name in presentation A, relative to A's namespace -/
  constant : Lean.Name
  /-- its role (clique member, encoding, auxiliary, user constant, …); reviewed -/
  role : String
  /-- reviewed; strict -/
  cause : NonCanonicalCause
  /-- pinned -/
  cls : DiffClass
  /-- pinned: the Lean compiler's hex address under presentation A (`-` when
      the constant is one-sided) -/
  addrA : String
  /-- pinned: the hex address under presentation B -/
  addrB : String
  /-- pinned: the path to the first differing node of the two Lean terms
      under the name map, e.g. `value.λ.body.@3` (empty when they are equal) -/
  firstDiff : String
  /-- free text, reviewed, not compared -/
  note : String := ""
  deriving Repr, Inhabited

/-- An entry, positionally (the record's data file is written in this form). -/
def e (fixture : Lean.Name) (presA presB : String) (constant : Lean.Name)
    (role : String) (cause : NonCanonicalCause) (cls : DiffClass)
    (addrA addrB firstDiff : String) (note : String := "") : NonCanonicalEntry :=
  { fixture, presA, presB, constant, role, cause, cls, addrA, addrB, firstDiff, note }

/-- The data file's text up to its first part (kept equal to
    `Tests/Ix/Compile/NonCanonicalDefault.lean`'s, so a re-record changes
    only entries). -/
def recordHeader : String :=
"/-
  The non-canonical record of the compiler: every byte difference between two
  presentations of a twin family (`Tests.Ix.Compile.Twins.allFamilies`), with
  its reviewed cause and its pinned evidence. Types and policy:
  `Tests.Ix.Compile.NonCanonical`.

  This file is data, written by the `twins` suite's re-record mode
  (`IX_TWINS_RECORD=<file> lake exe IxTests --ignored twins`) and then
  reviewed: a new difference arrives as `(.unreviewed \"<suggested cause>\")`
  and is given its cause by hand, from the dumped terms (`IX_TWINS_DUMP`);
  the gate fails until it is. Entries are ordered by family (in
  `allFamilies`' order), then by presentation pair, then by constant name.
  Change it only in a commit that states why the differences moved.
-/
import Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.NonCanonicalDefault

open Tests.Ix.Compile.NonCanonical

"

/-- The entry as one item of the data file's list (two lines; the writer
    separates items with commas). -/
def NonCanonicalEntry.syntax (x : NonCanonicalEntry) : String :=
  s!"  e {nameSyntax x.fixture} {x.presA.quote} {x.presB.quote} {nameSyntax x.constant} \
{x.role.quote} {x.cause.syntax} {x.cls.syntax}\n" ++
  s!"    {x.addrA.quote} {x.addrB.quote} {x.firstDiff.quote}" ++
  (if x.note.isEmpty then "" else s!" {x.note.quote}")

/-- Entries per list literal of the data file: a literal of a few hundred
    entries compiles within the code generator's recursion bound, the whole
    post-flip record (1883) does not, so the file holds the record in parts. -/
def recordChunk : Nat := 200

/-- The record's data file (`Tests/Ix/Compile/NonCanonicalDefault.lean`) with
    these entries, in the given order, in parts of `recordChunk`. -/
def recordFile (entries : List NonCanonicalEntry) : String := Id.run do
  let arr := entries.toArray
  let n := (arr.size + recordChunk - 1) / recordChunk
  let mut out := recordHeader
  for i in [0:n] do
    let part := (arr.extract (i * recordChunk) ((i + 1) * recordChunk)).toList
    out := out ++ s!"/-- Entries {i * recordChunk} to {i * recordChunk + part.length - 1}. -/\n\
def part{i} : List NonCanonicalEntry := [\n" ++ ",\n".intercalate (part.map (·.syntax)) ++
      "\n]\n\n"
  let parts := if n == 0 then "[]" else " ++ ".intercalate ((List.range n).map fun i => s!"part{i}")
  return out ++ s!"/-- The measured non-canonical set. -/\ndef nonCanonical : List NonCanonicalEntry :=\n  \
{parts}\n\nend Tests.Ix.Compile.NonCanonicalDefault\n"

/-- A constant of a twin presentation that the compilers refuse on purpose,
    with a fragment of the expected message (both compilers' spellings contain
    it) and the reason. The twins gate requires exactly these refusals (in
    scope), from both compilers, and leaves the refused constants (and the
    constants of the reference they map to) out of the comparison. -/
structure ExpectedRefusal where
  constant : Lean.Name
  message : String
  reason : String

/-- The constants of the twin presentations the compilers refuse on purpose.
    None since Pass 3 is wired: the call-site surgery's safety refusals
    (WB-B4, D-01, CQ1.1: "collapse call site drops distinct arguments", "… is
    a partial application") went with the surgery's plans, and the collapsed
    blocks' callers compile through images (Pass 3's faithful rewrite), so
    every twin constant is compared and checked. -/
def expectedRefusals : List ExpectedRefusal := []

end Tests.Ix.Compile.NonCanonical
