/-
  twins: the canonicity gate over twin families.

  A twin family is several presentations of the same block or clique in
  separate namespaces (`Tests/Ix/Compile/Twins/*.lean`, the library twins of
  `Tests/Ix/Compile/Oracle/Lib.lean`, `Tests/Ix/Compile/Fixtures/{LetNonDep,
  NestedLevels}.lean`): member permutations, renamings, regroupings,
  components declared separately, collapsed twins. The first presentation is
  the reference `A`; every other presentation `B` carries a name map into `A`
  (namespace replacement, then the longest matching prefix rename).

  The fixtures are not in `IxTests`' environment: the suite imports their
  root module `Tests.Ix.Compile.Twins.Fixtures` at run time (`fixturesEnv`;
  the `TwinsFixtures` library builds it). Some presentations are refused by
  the compilers on purpose (`NonCanonical.expectedRefusals`), and the
  whole-environment suites would count those as failures.

  The suite compiles the union of every presentation's closure once with the
  Lean compiler (the `ix compile-lean` pipeline,
  `ClosureHarness.compileClosure`) and once with the Rust compiler (the
  `ix compile` FFI, `ClosureHarness.rustClosure`), and requires:

  1. each compiler refuses exactly the expected refusals in scope, with their
     messages (`NonCanonical.expectedRefusals`);
  2. the two compilers give every fixture constant the same address;
  3. for every pair `(A, B)`, every constant of `B` that maps to a constant of
     `A` has `A`'s address, except the entries of the record
     (`Tests.Ix.Compile.NonCanonicalDefault.nonCanonical`), under the records
     policy (`Tests.Ix.Compile.NonCanonical`): the keys are exact in both
     directions (an unrecorded difference, a stale entry and an entry for no
     family pair all fail), every cause is reviewed (an `unreviewed` entry
     fails), and the evidence is pinned (addresses, class, first differing
     node). Constants on one side only are differences too, after
     generated-number names (`match_N`, `proof_N`, `_sizeOf_N`, …) are
     matched by address (their numbering is metadata).

  Every difference is classified mechanically (`DiffClass`): `root` (the two
  Lean terms differ under the name map; the first differing node is
  recorded), `inherited` (equal terms, and the constant references differing
  constants), `unexplained` (equal terms, no differing reference: a compiler
  canonicity defect unless its cause says otherwise), `onlyA`, `onlyB`. Causes
  are assigned by review, from the terms.

  Environment variables:
  - `IX_TWINS_ONLY=<substring>`: only the families whose fixture name
    contains it (a filter that selects none fails);
  - `IX_TWINS_DUMP=<dir>`: per non-inherited difference, both Lean constants
    pretty-printed and the first differing subterms (for review);
  - `IX_TWINS_IXE=<path>`: the Lean compiler's output, for kernel checks by
    hand (`ix check-rs`, `kernel-check-ixe`);
  - `IX_TWINS_RECORD=<path>`: re-record. Writes the record's data file with
    this run's evidence to `<path>`: an entry whose key still differs keeps
    its role, cause and note and takes the run's addresses, class and first
    differing node; a new difference is written with
    `(.unreviewed "<suggested cause>")`; a stale entry is dropped; the
    entries of families outside `IX_TWINS_ONLY` are kept as they are. Copy
    it over `Tests/Ix/Compile/NonCanonicalDefault.lean` and review the diff.
    The exit code is still the verdict against the committed record.

  Run with: `lake exe IxTests --ignored twins`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.NonCanonical
import Tests.Ix.Compile.NonCanonicalDefault
import Tests.Ix.Compile.Only
import Tests.Ix.Compile.ClosureHarness

open Lean
open Tests.Ix.Compile.NonCanonical

namespace Tests.Ix.Compile.Twins

/-! ## Families -/

inductive FamilyKind where
  | block | clique | library
  deriving Repr, BEq

structure Pres where
  id : String
  ns : Name
  /-- prefix renames from this presentation's relative names to the
      reference's relative names; the longest matching prefix applies -/
  rename : List (Name × Name) := []
  /-- relative prefixes of constants with no counterpart by construction
      (not compared) -/
  skip : List Name := []
  deriving Repr

structure Family where
  fixture : Name
  kind : FamilyKind
  /-- the reference presentation first -/
  pres : List Pres
  deriving Repr

def applyRename (rs : List (Name × Name)) (n : Name) : Name :=
  let best := rs.foldl (init := (none : Option (Name × Name))) fun acc (src, dst) =>
    if src.isPrefixOf n then
      match acc with
      | some (s, _) => if src.getNumParts > s.getNumParts then some (src, dst) else acc
      | none => some (src, dst)
    else acc
  match best with
  | some (src, dst) => n.replacePrefix src dst
  | none => n

/-- The name map of `b` into `a`, on full names; names outside `b`'s
    namespace are unchanged. -/
def mapInto (a b : Pres) (n : Name) : Name :=
  if b.ns.isPrefixOf n && n != b.ns then
    a.ns ++ applyRename b.rename (n.replacePrefix b.ns .anonymous)
  else n

private def cl (fam : String) : Name := `Tests.Ix.Compile.Twins.Cliques ++ fam.toName

private def clique (fam : String) (ps : List (String × List (Name × Name))) : Family :=
  { fixture := cl fam, kind := .clique
    pres := ps.map fun (id, rename) => { id, ns := cl fam ++ id.toName, rename } }

/-- The clique families (`Tests/Ix/Compile/Twins/Cliques.lean`). -/
def cliqueFamilies : List Family := [
  clique "SA" [("P0", []), ("P1", []), ("P2", [(`isE, `ev), (`isO, `od)]),
    ("P3", [(`ev.od, `od)])],
  clique "S3" [("P0", []), ("P1", []), ("P2", [])],
  clique "SM" [("P0", []), ("P1", [])],
  clique "SX" [("P0", []), ("P1", []), ("P2", [])],
  clique "WD" [("P0", []), ("P1", [(`wb._mutual, `wa._mutual)]),
    ("P2", [(`wa.wb, `wb), (`wa.wb._mutual, `wa._mutual)])],
  clique "W3" [("P0", []), ("P1", [(`gc._mutual, `ga._mutual)]),
    ("P2", [(`gb._mutual, `ga._mutual)])],
  clique "WG" [("P0", []), ("P1", [(`gb._mutual, `ga._mutual)])],
  clique "WT" [("P0", []), ("P1", [(`tb._mutual, `ta._mutual)])],
  clique "WB" [("P0", []), ("P1", [(`bb._mutual, `ba._mutual)])],
  clique "PF" [("P0", []), ("P1", [(`pc.mutual, `pa.mutual)]),
    ("P2", [(`pb.mutual, `pa.mutual)])],
  clique "TS" [("P0", []), ("P1", [(`odT._mutual, `evT._mutual)])],
  clique "TM" [("P0", []), ("P1", [])],
  clique "TW" [("P0", []), ("P1", [(`wb._mutual, `wa._mutual)])],
  clique "IP" [("P0", []), ("P1", [(`evM.match_1, `evM.match_2), (`odM.match_1, `odM.match_2)])],
  clique "TP" [("P0", []), ("P1", [])],
  clique "SP" [("P0", []), ("P1", [])],
  clique "WP" [("P0", []), ("P1", [(`hb._mutual, `ha._mutual)])],
  clique "PT" [("P0", []), ("P1", [])],
  clique "WA" [("P0", []), ("P1", [(`tc._mutual, `ta._mutual)])],
  clique "TN" [("P0", []), ("P1", [])],
  clique "RF" [("P0", []), ("P1", []), ("P2", [(`ra.rb, `rb)])],
  clique "NS" [("P0", []), ("P1", []), ("P2", [])],
  clique "LI" [("P0", []), ("P1", [(`lc.mutual, `la.mutual)]), ("P2", [(`lb.mutual, `la.mutual)])],
  clique "LC" [("P0", []), ("P1", [(`cb.mutual, `ca.mutual)])],
  clique "PU" [("P0", []), ("P1", [(`ub.mutual, `ua.mutual)])],
  clique "RA" [("P0", []), ("P1", [])],
  clique "WH" [("P0", []), ("P1", [(`hb._mutual, `ha._mutual)])],
  clique "TR" [("P0", []), ("P1", [])],
  clique "TQ" [("P0", []), ("P1", [(`qb._mutual, `qa._mutual)])],
  clique "WU" [("P0", []), ("P1", [(`wy._mutual, `wx._mutual)])]
]

private def rp (s : String) : Name := `Tests.Ix.Compile.Twins.Repro ++ s.toName

/-- An oracle-experiment pair: the reference is the twin (Ix's canonical
    form), the other presentation the original, mapped by `Maps/*.map`. -/
private def repro (fam : String) (orig twin : String)
    (rename : List (Name × Name) := []) (skip : List Name := []) : Family :=
  { fixture := rp fam, kind := .block
    pres := [{ id := "twin", ns := rp ("Twin." ++ twin), skip },
             { id := "orig", ns := rp ("Orig." ++ orig), rename, skip }] }

/-- The oracle experiment's pairs (`Tests/Ix/Compile/Twins/Repro.lean`). -/
def reproFamilies : List Family := [
  repro "Ctl" "Ctl" "Tw.Ctl",
  repro "DQMut" "DQMut" "Tw.DQMut" [(`A._sizeOf_2, `B._sizeOf_1)],
  repro "DQReord" "DQReord" "Tw.DQReord"
    [(`Even._sizeOf_1, `Odd._sizeOf_2), (`Even._sizeOf_2, `Odd._sizeOf_1)],
  repro "DQSplit" "DQSplit" "Tw.DQSplit" [(`A._sizeOf_2, `B._sizeOf_1)],
  repro "EvapClosure" "EvapClosure" "Tw.EvapClosure",
  repro "F1_Collapse2p1" "F1" "Tw.F1"
    [(`B, `A), (`A._sizeOf_2, `A._sizeOf_1), (`A._sizeOf_3, `A._sizeOf_2)],
  repro "F2_SplitNestedClosure" "F2" "Tw.F2",
  repro "F4_NestedAlphaUsers" "F4" "Tw.F4"
    [(`B, `A), (`sizeLA, `sizeL), (`A.rec_2, `A.rec_1)],
  repro "FieldBelow" "FieldBelow" "Tw.FieldBelow",
  repro "PropCollapse" "PropCollapse" "Tw.PropCollapse" [(`Q, `P)],
  repro "PropSplit" "PropSplit" "Tw.PropSplit",
  repro "RecAlias" "RecAlias" "Tw.RecAlias",
  repro "SurgCollapse" "SurgCollapse" "Tw.SurgCollapse"
    [(`B, `A), (`B.b, `A.a), (`B.g, `B.g), (`A._sizeOf_2, `A._sizeOf_1)],
  repro "SurgIdx" "SurgIdx" "Tw.SurgIdx" [(`A._sizeOf_2, `B._sizeOf_1)] [`B.size, `bsize],
  repro "SurgIdx2" "SurgIdx2" "Tw.SurgIdx2" [(`A._sizeOf_2, `B._sizeOf_1)],
  repro "SurgSplit" "SurgSplit" "Tw.SurgSplit" [(`A._sizeOf_2, `B._sizeOf_1)]
]

private def pr (s : String) : Name := `Tests.Ix.Compile.Twins.Proto ++ s.toName

/-- A prototype case: the reference is the hand-written canonical block
    `Can`, the other presentation the source `Src`. -/
private def proto (c : String) (rename : List (Name × Name)) (skip : List Name) : Family :=
  { fixture := pr c, kind := .block
    pres := [{ id := "can", ns := pr (c ++ ".Can"), skip },
             { id := "src", ns := pr (c ++ ".Src"), rename, skip }] }

/-- The prototype's cases (`Tests/Ix/Compile/Twins/Proto.lean`): the name map
    from `Src` into `Can` (the prototype's `#lean_view` maps; a collapsed
    member and an equal-armed function map onto the representative), and the
    `Src` constants `Can` has no counterpart for (value theorems, functions
    with different arms over a collapsed pair, raw recursor users), which are
    not compared. (On the old branch this table lived in the fixture module;
    the suite does not import the fixtures here.) -/
def protoCases : List (String × List (Name × Name) × List Name) := [
  ("C1", [], [`three]),
  ("C2", [], [`len2, `cnt1]),
  ("C2b", [], []),
  ("C3", [], []),
  ("C3b", [(`Q1, `X), (`Q2, `X), (`q1, `q), (`q2, `q)], []),
  ("C4", [], [`useRec1, `rawRec1, `useBelow1, `useBrecOn1, `size_ex, `useRec_ex]),
  ("C5", [(`A, `X), (`B, `X), (`B.b, `X.a), (`A.h, `X.h), (`B.k, `X.h),
      (`A.isNil, `X.isNil), (`B.isNil, `X.isNil)],
    [`f, `f_ab, `A.f, `B.g, `fg_ab, `fg_bab, `X.fg]),
  ("C6", [(`A, `X), (`B, `X), (`sizeLA, `sizeL), (`A.rec_2, `X.rec_1), (`A.below_2, `X.below_1),
      (`A.brecOn_2, `X.brecOn_1)],
    [`r, `rb, `r1, `t, `A.w, `B.w, `wL, `wLA, `size_ex, `w_ex]),
  ("C7", [(`P, `X), (`Q, `X), (`P.toQ, `X.self), (`Q.toP, `X.self)], [`p_cases]),
  ("C7b", [], [`EvenP.two]),
  ("C8", [(`A, `X), (`B, `X), (`A.h, `X.h), (`B.h, `X.h)],
    [`A.f, `B.f, `C.f, `f_ex, `viaRec, `viaRec_ex]),
  ("C8b", [(`A, `X), (`B, `X), (`C, `X)],
    [`A.f, `B.f, `C.f, `f_ex, `viaRec, `viaRec_ex]),
  ("C9", [], [`depth_ex]),
  ("C9b", [(`A, `X), (`B, `X), (`B.b, `X.a)], [`A.f, `B.g, `f_ex, `viaRec])
]

/-- The prototype's families. -/
def protoFamilies : List Family := protoCases.map
  fun (c, rename, skip) => proto c rename skip


private def lib (fam : String) (ns : Name) : Family :=
  { fixture := `Tests.Ix.Compile.Oracle.Lib ++ fam.toName, kind := .library
    pres := [{ id := "twin", ns := `Tests.Ix.Compile.Oracle.Lib.Twin ++ ns },
             { id := "orig", ns := `Tests.Ix.Compile.Oracle.Lib.Orig ++ ns }] }

/-- The library twins (`Tests/Ix/Compile/Oracle/Lib.lean`): Lean's own
    constructions on the library block in Lean's order and in Ix's. -/
def libraryFamilies : List Family := [
  lib "LCNF" `Lean.Compiler.LCNF,
  lib "Cutsat" `Lean.Meta.Grind.Arith.Cutsat,
  lib "Linear" `Lean.Meta.Grind.Arith.Linear
]


def allFamilies : List Family :=
  cliqueFamilies ++ reproFamilies ++ protoFamilies ++ libraryFamilies ++
    ([`Split, `Equal].map fun family =>
      let ns := `Tests.Ix.Compile.Fixtures.LetNonDep ++ family
      { fixture := ns, kind := .block,
        pres := [{ id := "A", ns := ns ++ `A }, { id := "B", ns := ns ++ `B }] }) ++
    ([`Mixed, `Neighbour].map fun family =>
      let ns := `Tests.Ix.Compile.Fixtures.NestedLevels ++ family
      { fixture := ns, kind := .block,
        pres := [{ id := "A", ns := ns ++ `A }, { id := "B", ns := ns ++ `B }] })

/-! ## Lean terms under the name map -/

/-- Strip `mdata`. -/
partial def strip : Expr → Expr
  | .mdata _ e => strip e
  | e => e

def levelEq (ia ib : Name → Option Nat) : Level → Level → Bool
  | .zero, .zero => true
  | .succ a, .succ b => levelEq ia ib a b
  | .max a b, .max c d => levelEq ia ib a c && levelEq ia ib b d
  | .imax a b, .imax c d => levelEq ia ib a c && levelEq ia ib b d
  | .param a, .param b => ia a == ib b
  | _, _ => false

structure DiffCtx where
  mapB : Name → Name
  ia : Name → Option Nat
  ib : Name → Option Nat

/-- The differing positions of `a` (presentation A) and `b` (presentation
    B, names mapped into A), at most `limit`, each with its path. -/
partial def diffs (cx : DiffCtx) (path : String) (a b : Expr) (limit : Nat)
    (acc : Array (String × Expr × Expr)) : Array (String × Expr × Expr) :=
  if acc.size ≥ limit then acc else
  let a := strip a
  let b := strip b
  let here := acc.push (path, a, b)
  match a, b with
  | .bvar i, .bvar j => if i == j then acc else here
  | .sort u, .sort v => if levelEq cx.ia cx.ib u v then acc else here
  | .lit x, .lit y => if x == y then acc else here
  | .const n us, .const m vs =>
    if n == cx.mapB m && us.length == vs.length
        && (us.zip vs).all (fun (u, v) => levelEq cx.ia cx.ib u v) then acc else here
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let xs := a.getAppArgs
    let ys := b.getAppArgs
    if xs.size != ys.size then here else
    let acc := diffs cx (path ++ ".fn") fa fb limit acc
    (List.range xs.size).foldl (init := acc) fun acc i =>
      diffs cx (path ++ s!".@{i}") xs[i]! ys[i]! limit acc
  | .lam _ t e _, .lam _ t' e' _ =>
    diffs cx (path ++ ".λ.body") e e' limit (diffs cx (path ++ ".λ.dom") t t' limit acc)
  | .forallE _ t e _, .forallE _ t' e' _ =>
    diffs cx (path ++ ".∀.body") e e' limit (diffs cx (path ++ ".∀.dom") t t' limit acc)
  | .letE _ t v e _, .letE _ t' v' e' _ =>
    let acc := diffs cx (path ++ ".let.ty") t t' limit acc
    let acc := diffs cx (path ++ ".let.val") v v' limit acc
    diffs cx (path ++ ".let.body") e e' limit acc
  | .proj s i e, .proj s' i' e' =>
    if s == cx.mapB s' && i == i' then diffs cx (path ++ s!".proj{i}") e e' limit acc
    else here
  | _, _ => here

def kindTag : ConstantInfo → String
  | .defnInfo _ => "defn" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
  | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- The terms of a constant, labelled. -/
def constTerms : ConstantInfo → List (String × Expr)
  | .defnInfo v => [("type", v.type), ("value", v.value)]
  | .thmInfo v => [("type", v.type), ("value", v.value)]
  | .opaqueInfo v => [("type", v.type), ("value", v.value)]
  | .recInfo v => ("type", v.type) :: (v.rules.mapIdx fun i r => (s!"rule{i}", r.rhs))
  | ci => [("type", ci.type)]

/-- The differing positions of two constants under the map (empty: equal). -/
def constDiffs (mapB : Name → Name) (ca cb : ConstantInfo) (limit : Nat := 6) :
    Array (String × Expr × Expr) := Id.run do
  if kindTag ca != kindTag cb || ca.levelParams.length != cb.levelParams.length then
    return #[("kind", .const ca.name [], .const cb.name [])]
  let ia := fun n => ca.levelParams.idxOf? n
  let ib := fun n => cb.levelParams.idxOf? n
  let cx : DiffCtx := { mapB, ia, ib }
  let ta := constTerms ca
  let tb := constTerms cb
  if ta.length != tb.length then
    return #[("rules", .const ca.name [], .const cb.name [])]
  let mut acc := #[]
  for ((l, a), (_, b)) in ta.zip tb do
    acc := diffs cx l a b limit acc
  return acc

/-- A pairing key for generated proofs whose statement follows the
    packing: `PSum` injections are erased to their argument and every
    `PSum` type, case tree or `PProd` tuple becomes one placeholder, so
    a decreasing obligation is recognised by its hypotheses and calls
    whatever summand position its function has. Used only to pair
    `_proof_N` constants by role, never to decide equality. -/
partial def packKey : Expr → Expr
  | .mdata _ e => packKey e
  | e@(.app ..) =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
      if (n == ``PSum.inl || n == ``PSum.inr) && args.size > 0 then packKey args.back!
      else if [``PSum, ``PSum.casesOn, ``PSum.rec, ``PProd, ``PProd.mk].contains n then
        .const `_pack []
      else mkAppN fn (args.map packKey)
    | _ => mkAppN (packKey fn) (args.map packKey)
  | .lam n t b bi => .lam n (packKey t) (packKey b) bi
  | .forallE n t b bi => .forallE n (packKey t) (packKey b) bi
  | .letE n t v b nd => .letE n (packKey t) (packKey v) (packKey b) nd
  | .proj s i e => .proj s i (packKey e)
  | e => e

/-- Whether the types, and whether the other terms (value, rules), differ
    under the map. -/
def termFlags (mapB : Name → Name) (ca cb : ConstantInfo) : Bool × Bool := Id.run do
  let cx : DiffCtx := { mapB, ia := ca.levelParams.idxOf?, ib := cb.levelParams.idxOf? }
  let ty := !(diffs cx "type" ca.type cb.type 1 #[]).isEmpty
  let rest := (constTerms ca).drop 1 |>.zip ((constTerms cb).drop 1)
  let v := rest.any fun ((l, a), (_, b)) => !(diffs cx l a b 1 #[]).isEmpty
  return (ty, v)

/-- Whether every term is equal under the map once `packKey` erased the
    `PSum`/`PProd` packing (evidence only: it also erases the case trees
    that carry measures, so a GuessLex difference is not visible to it). -/
def packEq (mapB : Name → Name) (ca cb : ConstantInfo) : Bool :=
  let cx : DiffCtx := { mapB, ia := ca.levelParams.idxOf?, ib := cb.levelParams.idxOf? }
  let ta := constTerms ca
  let tb := constTerms cb
  ta.length == tb.length && (ta.zip tb).all fun ((l, a), (_, b)) =>
    (diffs cx l (packKey a) (packKey b) 1 #[]).isEmpty

/-! ## Pretty printing for the dump -/

def ppExprIO (env : Environment) (e : Expr) (explicit : Bool := false) : IO String := do
  -- loose bound variables (subterms under binders) print as `_bN`
  let n := e.looseBVarRange
  let e := if n == 0 then e else
    e.instantiate ((List.range n).toArray.map fun i => .const (Name.mkSimple s!"_b{i}") [])
  let opts : Options := ({} : Options)
    |>.setBool `pp.proofs true |>.setBool `pp.explicit explicit
    |>.setBool `pp.funBinderTypes true |>.set `pp.maxSteps (2000000 : Nat)
    |>.setBool `pp.deepTerms true |>.setBool `pp.fieldNotation false
  let ctx : Core.Context :=
    { fileName := "<twins>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let st : Core.State := { env }
  try
    let (f, _) ← ((PrettyPrinter.ppExpr e).run' {} {}).toIO ctx st
    pure (toString f)
  catch ex => pure s!"<pp failed: {ex}> {e}"

/-! ## Pairing and comparing the presentations -/

/-- Strip trailing numeric suffixes: `match_3` ↦ `match`, `eq_1` ↦ `eq`. -/
def stem : Name → Name
  | .str p s =>
    match s.splitOn "_" |>.reverse with
    | last :: rest@(_ :: _) =>
      if last.all Char.isDigit && !last.isEmpty then .str (stem p) ("_".intercalate rest.reverse)
      else .str (stem p) s
    | _ => .str (stem p) s
  | .num p _ => stem p
  | .anonymous => .anonymous

/-- One difference of a pair. -/
structure DiffRec where
  /-- name in A, relative to A's namespace -/
  constant : Name
  cls : DiffClass
  addrA : String
  addrB : String
  firstDiff : String
  deriving Repr

structure Compiled where
  addr : Name → Option String
  /-- Whether a Lean name is an image-kind head of a changed block in this
      compile (`CompileEnv.p3Heads`): the name holds the head's image. -/
  isHead : Name → Bool := fun _ => false

def nonCanonicalFor (record : List NonCanonicalEntry) (f : Family) (a b : Pres) :
    List NonCanonicalEntry :=
  record.filter fun e =>
    e.fixture == f.fixture && e.presA == a.id && e.presB == b.id

/-- A presentation's constants, in name order (so that pairing, which takes
    the first candidate, does not depend on the environment's map order: the
    record pins what it produces). -/
def presConsts (env : Environment) (p : Pres) : Array (Name × ConstantInfo) :=
  let cs := env.constants.fold (init := #[]) fun acc n ci =>
    if p.ns.isPrefixOf n && n != p.ns
        && !p.skip.any (fun s => s.isPrefixOf (n.replacePrefix p.ns .anonymous)) then
      acc.push (n, ci)
    else acc
  cs.qsort (·.1.toString < ·.1.toString)

def lastStr : Name → String
  | .str _ s => s
  | .num p _ => lastStr p
  | .anonymous => ""

/-- The suggested cause and role of a new difference, from its name, class
    and family, for the re-record's `unreviewed` entries: an inherited
    difference, an image-kind head of a changed block (`IMAGE`), then by the
    constant's role; every suggestion is reviewed against the dumped terms
    before it becomes a cause. -/
def suggest (f : Family) (d : DiffRec) (head : Bool := false) :
    NonCanonicalCause × String := Id.run do
  let s := lastStr d.constant
  let parent := lastStr d.constant.getPrefix
  let isEq := s == "eq_def" || s == "eq_unfold" || s.startsWith "eq_"
  let isEnc := s == "_mutual" || s == "mutual" || parent == "_mutual" || parent == "mutual"
  let auxNames := ["below", "brecOn", "go", "eq", "rec", "casesOn", "recOn"]
  let isAux := auxNames.contains s || s.startsWith "rec_" || s.startsWith "below_"
    || s.startsWith "brecOn_"
  let isSizeOf := s.startsWith "_sizeOf_" || s == "sizeOf_spec"
  let oneSided := d.cls == .onlyA || d.cls == .onlyB
  if let .inherited _ := d.cls then return (.inherited, "user constant")
  if head then
    return (.image, "image-kind head of a changed block (its Lean name holds the image)")
  if Name.isPrefixOf `Tests.Ix.Compile.Fixtures.NestedLevels f.fixture then
    return (.pendingLevels, "block member or auxiliary")
  match f.kind with
  | .clique =>
    if isEq && (parent == "_mutual" || parent == "mutual") then return (.orderStmt, "encoding equation")
    if isEq then return (.lazy, "equation lemma")
    if s.startsWith "_proof_" then return (.pendingTransport, "encoding obligation")
    if isEnc then return (.pendingTransport, "clique encoding")
    if s == "_f" then return (.pendingTransport, "structural functional")
    if s.startsWith "match_" then return (.pendingTransport, "transformed matcher")
    return (.pendingTransport, "clique member")
  | _ =>
    if isSizeOf then return (.o11aPending, "sizeOf family")
    if s == "noConfusion" || s == "noConfusionType" then return (.pendingNoConfusion, "noConfusion")
    if isAux && oneSided then return (.pendingSplitAux, "block auxiliary")
    return (.pendingPasses, "caller of a changed block")

/-- Check one compiler's block failures against the expected refusals of the
    constants in `scope`: every failure must be an expected refusal with its
    message, and every expected refusal in scope must happen. Returns the
    number of violations. -/
def refusalCheck (label : String) (scope : Std.HashSet Name)
    (fails : List (String × String)) : IO Nat := do
  let mut bad := 0
  for (n, e) in fails do
    match expectedRefusals.find? (·.constant.toString == n) with
    | some r =>
      if (e.splitOn r.message).length > 1 then
        IO.println s!"[{label}] expected refusal: {n} ({r.reason})"
      else
        IO.println s!"[{label}] refusal with another message: {n}: {(e.replace "\n" " ").take 200}"
        bad := bad + 1
    | none =>
      IO.println s!"[{label}] block failure: {n}: {(e.replace "\n" " ").take 200}"
      bad := bad + 1
  for r in expectedRefusals do
    if scope.contains r.constant && !(fails.any (·.1 == r.constant.toString)) then
      IO.println s!"[{label}] expected refusal did not happen: {r.constant}"
      bad := bad + 1
  return bad

/-- The expected refusals as a set (left out of the comparison). -/
def refusedSet : Std.HashSet Name :=
  expectedRefusals.foldl (init := {}) fun s r => s.insert r.constant

/-- Compare one pair; returns the differences. -/
def comparePair (env : Environment) (lean : Compiled) (f : Family) (a b : Pres)
    (dumpDir : Option System.FilePath) (refused : Std.HashSet Name := {}) :
    IO (Array DiffRec) := do
  -- refused constants (and the constants of A they map to) are not compared
  let cb := (presConsts env b).filter (!refused.contains ·.1)
  let refusedA : Std.HashSet Name := refused.fold (init := {}) fun s r =>
    if b.ns.isPrefixOf r then s.insert (mapInto a b r) else s
  let ca := (presConsts env a).filter fun (n, _) => !refused.contains n && !refusedA.contains n
  let aSet : Std.HashMap Name ConstantInfo := ca.foldl (init := {}) fun m (n, ci) => m.insert n ci
  let mapB := mapInto a b
  -- pair B's constants into A. Numbered generated names (`_proof_N`,
  -- `match_N`) are paired by address first: their numbering follows the
  -- elaboration order, which is metadata (§5.5). Then by name; then every
  -- leftover by address (a constant whose owner name moved, e.g. a shared
  -- matcher).
  let numbered (n : Name) : Bool := match n with
    | .str _ s => (s.startsWith "_proof_" || s.startsWith "proof_" || s.startsWith "match_"
        || s.startsWith "_sizeOf_")
        && stem n != n
    | _ => false
  let mut paired : Array (Name × Name) := #[]
  let mut hit : Std.HashSet Name := {}
  let mut hitB : Std.HashSet Name := {}
  for (n, _) in cb do
    if !numbered n then continue
    let addrB := lean.addr n
    if addrB.isNone then continue
    match ca.find? (fun (m, _) => numbered m && !hit.contains m && lean.addr m == addrB) with
    | some (m, _) => paired := paired.push (m, n); hit := hit.insert m; hitB := hitB.insert n
    | none => pure ()
  -- then by role: the statement with the packing erased (`packKey`)
  for (n, cin) in cb do
    if !numbered n || hitB.contains n then continue
    let kb := packKey cin.type
    let cand := ca.find? fun (m, cim) => numbered m && !hit.contains m &&
      cim.levelParams.length == cin.levelParams.length &&
      (diffs { mapB, ia := cim.levelParams.idxOf?, ib := cin.levelParams.idxOf? }
        "type" (packKey cim.type) kb 1 #[]).isEmpty
    if let some (m, _) := cand then
      paired := paired.push (m, n); hit := hit.insert m; hitB := hitB.insert n
  -- then by value under the map: a decreasing or monotonicity proof keeps
  -- its body when only its statement follows the packing
  let valueOf (ci : ConstantInfo) : Option Expr := match ci with
    | .thmInfo v => some v.value | .defnInfo v => some v.value | _ => none
  for (n, cin) in cb do
    if !numbered n || hitB.contains n then continue
    let some vb := valueOf cin | continue
    let cand := ca.find? fun (m, cim) => numbered m && !hit.contains m &&
      match valueOf cim with
      | some va => cim.levelParams.length == cin.levelParams.length &&
          (diffs { mapB, ia := cim.levelParams.idxOf?, ib := cin.levelParams.idxOf? }
            "value" va vb 1 #[]).isEmpty
      | none => false
    if let some (m, _) := cand then
      paired := paired.push (m, n); hit := hit.insert m; hitB := hitB.insert n
  let mut onlyB : Array Name := #[]
  for (n, _) in cb do
    if hitB.contains n then continue
    let t := mapB n
    -- several constants of B may map to one of A (a collapsed twin)
    if aSet.contains t then
      paired := paired.push (t, n); hit := hit.insert t
    else onlyB := onlyB.push n
  let mut onlyA : Array Name := (ca.filter fun (n, _) => !hit.contains n).map (·.1)
  let mut stillB : Array Name := #[]
  for n in onlyB do
    let addrB := lean.addr n
    match onlyA.findIdx? (fun m => lean.addr m == addrB && addrB.isSome) with
    | some i => paired := paired.push (onlyA[i]!, n); onlyA := onlyA.eraseIdxIfInBounds i
    | none => stillB := stillB.push n
  let rel (n : Name) : Name := n.replacePrefix a.ns .anonymous
  let mut out : Array DiffRec := #[]
  let mut differing : Std.HashSet Name := {}
  for (na, nb) in paired do
    if lean.addr na != lean.addr nb then differing := differing.insert na
  for (na, nb) in paired do
    let xa := lean.addr na
    let xb := lean.addr nb
    if xa == xb then continue
    let some ciA := env.find? na | continue
    let some ciB := env.find? nb | continue
    let ds := constDiffs mapB ciA ciB
    let (cls, fd) : DiffClass × String :=
      if ds.isEmpty then
        let refs := ciA.getUsedConstantsAsSet.toList.filter differing.contains
        if refs.isEmpty then (.unexplained, "")
        else (.inherited (refs.map rel), "")
      else
        -- which terms differ: the type, the value or rules; and whether they
        -- are equal once the packing is erased
        let (tyD, valD) := termFlags mapB ciA ciB
        (.root tyD valD (packEq mapB ciA ciB), ds[0]!.1)
    let d : DiffRec :=
      { constant := rel na, cls, addrA := xa.getD "-", addrB := xb.getD "-", firstDiff := fd }
    out := out.push d
    if let some dir := dumpDir then
      unless cls matches .inherited _ do
        let mut s := s!"# {f.fixture} {a.id} vs {b.id}: {na} / {nb}\n# class {cls.tag}\n"
        s := s ++ s!"# addrA {d.addrA}\n# addrB {d.addrB}\n"
        for (p, x, y) in ds do
          s := s ++ s!"\n## differing node {p}\n-- A:\n{← ppExprIO env x true}\n-- B:\n{← ppExprIO env y true}\n"
        for (l, e) in constTerms ciA do
          s := s ++ s!"\n## A {l}\n{← ppExprIO env e}\n"
        for (l, e) in constTerms ciB do
          s := s ++ s!"\n## B {l}\n{← ppExprIO env e}\n"
        let file := dir / s!"{f.fixture.getString!}.{a.id}-{b.id}.{rel na}.txt"
        IO.FS.writeFile file s
  -- a one-sided constant the other side references is shared, not a
  -- difference: Lean reuses an equal matcher or auxiliary lemma it already
  -- added for an earlier presentation
  let usedBy (cs : Array (Name × ConstantInfo)) : Std.HashSet Name :=
    cs.foldl (init := {}) fun s (_, ci) =>
      ci.getUsedConstantsAsSet.foldl (init := s) fun s r => s.insert r
  let usedB := usedBy cb
  let usedA := usedBy ca
  -- an unreferenced numbered auxiliary is an orphan of elaboration (Lean
  -- built the matcher, then replaced its use by a transformed one, and the
  -- next presentation reused it from the cache): not part of either term
  let onlyA' := onlyA.filter fun n => !usedB.contains n && !(numbered n && !usedA.contains n)
  let stillB' := stillB.filter fun n => !usedA.contains n && !(numbered n && !usedB.contains n)
  -- a one-sided numbered auxiliary all of whose users compile to equal
  -- bytes on both sides is a naming artifact: the users reference its
  -- content by address, so the other side holds the same content under
  -- another owner name (a matcher Lean reused from an earlier declaration)
  let equalUsers (cs : Array (Name × ConstantInfo)) (n : Name) : Bool :=
    let users := cs.filter fun (_, ci) => ci.getUsedConstantsAsSet.contains n
    !users.isEmpty && users.all fun (u, _) => !differing.contains u &&
      (paired.any fun (x, y) => (x == u || y == u) && lean.addr x == lean.addr y)
  let onlyA' := onlyA'.filter fun n => !(numbered n && equalUsers ca n)
  let stillB' := stillB'.filter fun n => !(numbered n && equalUsers cb n)
  for n in onlyA' do
    out := out.push
      { constant := rel n, cls := .onlyA, addrA := (lean.addr n).getD "-",
        addrB := "-", firstDiff := "" }
  for n in stillB' do
    out := out.push
      { constant := rel (mapB n), cls := .onlyB, addrA := "-",
        addrB := (lean.addr n).getD "-", firstDiff := "" }
  return out

/-- The closure with every inductive's recursors (`rec`, `rec_N`) added and
    closed again: the certified checker's reader needs an inductive block's
    recursor in its input, and a closure reaches it only when something
    uses it. Content addressing makes the extra constants inert for the
    comparison. -/
def closeWithRecursors (env : Environment) (closure : List (Name × ConstantInfo)) :
    List (Name × ConstantInfo) := Id.run do
  let mut extra : Array Name := #[]
  for (n, ci) in closure do
    if let .inductInfo _ := ci then
      if env.contains (n ++ `rec) then extra := extra.push (n ++ `rec)
      let mut i := 1
      while env.contains ((n ++ `rec).appendIndexAfter i) do
        extra := extra.push ((n ++ `rec).appendIndexAfter i)
        i := i + 1
  if extra.isEmpty then return closure
  Ix.EnvScope.collectDeps env (closure.map (·.1) ++ extra.toList)

/-- The prerequisites of the clique rows (`Ix.Compile.Pass.Clique.rowPrereqs`:
    `Eq`, `funext`, `WellFounded.fix_eq`, …) as Lean names, those `env`
    holds. A well-founded clique is transported only when they are in the
    compile's input (`CliqueOutcome.wfOnly`, CQ5.2 (b)), so the twins'
    closures carry them; a library compile has them anyway. -/
def rowPrereqNames (env : Environment) : List Name :=
  (Ix.Compile.Pass.Clique.rowPrereqs.toList.map
    Tests.Ix.Compile.ClosureHarness.toLeanName).filter env.contains

/-- The fixture constants of the families and the union of their closures
    (with recursors, `closeWithRecursors`, and the clique rows' prerequisites,
    `rowPrereqNames`). -/
def familyClosure (env : Environment) (families : List Family) :
    Array Name × List (Name × ConstantInfo) := Id.run do
  let mut seeds : Array Name := #[]
  for f in families do
    for p in f.pres do
      seeds := seeds ++ (presConsts env p).map (·.1)
  return (seeds, closeWithRecursors env
    (Ix.EnvScope.collectDeps env (seeds.toList ++ rowPrereqNames env)))

/-! ## The fixtures' environment and the compiles -/

/-- The root module of the fixtures (`Tests/Ix/Compile/Twins/Fixtures.lean`),
    built by the `TwinsFixtures` library. -/
def fixturesModule : Name := `Tests.Ix.Compile.Twins.Fixtures

/-- The fixtures' environment: their root module and its imports, loaded from
    the built `.olean` files (as `get_env!` loads `IxTests`' own). -/
def fixturesEnv : IO Environment := getCompileEnv #[fixturesModule]

/-! ## The record -/

/-- A family's pair, as the record keys it. -/
def pairsOf (f : Family) : List (Pres × Pres) :=
  match f.pres with
  | a :: bs => bs.map (a, ·)
  | [] => []

/-- The record entries that belong to no pair of any family in
    `allFamilies` (a renamed or removed fixture, presentation or family). -/
def orphans (record : List NonCanonicalEntry) : List NonCanonicalEntry :=
  record.filter fun e => !allFamilies.any fun f =>
    f.fixture == e.fixture && (pairsOf f).any fun (a, b) => a.id == e.presA && b.id == e.presB

/-- The outcome of one pair against the record: the problems, and the pair's
    entries as a re-record writes them (in constant order). -/
structure PairOutcome where
  problems : Array String := #[]
  entries : Array NonCanonicalEntry := #[]

/-- One pair's differences against its recorded entries, under the records
    policy: exact keys, reviewed causes, pinned evidence. -/
def checkPair (f : Family) (a b : Pres) (ds : Array DiffRec)
    (es : List NonCanonicalEntry) (head : Name → Bool := fun _ => false) :
    PairOutcome := Id.run do
  let key := s!"{f.fixture} {a.id}/{b.id}"
  let mut out : PairOutcome := {}
  for d in ds do
    match es.find? (·.constant == d.constant) with
    | some e =>
      if let .unreviewed s := e.cause then
        out := { out with problems := out.problems.push s!"UNREVIEWED {key} {d.constant} (suggested {s})" }
      if e.addrA != d.addrA || e.addrB != d.addrB || e.cls != d.cls || e.firstDiff != d.firstDiff then
        out := { out with problems := out.problems.push (
          s!"MOVED {key} {d.constant} ({e.cause.tag}): recorded {e.cls.tag} {e.addrA}/{e.addrB} \
{e.firstDiff}, run {d.cls.tag} {d.addrA}/{d.addrB} {d.firstDiff}") }
      -- `IMAGE` is exactly the image-kind heads (the compile's `p3Heads`) whose
      -- terms differ: a head recorded with another cause, or `IMAGE` on a
      -- constant that is no head, is a problem; the re-record suggests again
      let wantImage := head d.constant && !(d.cls matches .inherited _)
      let mismatch := wantImage != (e.cause == .image) && !(e.cause matches .unreviewed _)
      if mismatch then
        out := { out with problems := out.problems.push (
          s!"CAUSE {key} {d.constant}: recorded {e.cause.tag}, but it is \
{if wantImage then "" else "not "}an image-kind head with differing terms") }
      let cause := if mismatch then .unreviewed (suggest f d (head d.constant)).1.syntax else e.cause
      out := { out with entries := out.entries.push (
        { e with cause, cls := d.cls, addrA := d.addrA, addrB := d.addrB, firstDiff := d.firstDiff }) }
    | none =>
      let (cause, role) := suggest f d (head d.constant)
      let entry : NonCanonicalEntry :=
        { fixture := f.fixture, presA := a.id, presB := b.id, constant := d.constant, role,
          cause := .unreviewed cause.syntax, cls := d.cls, addrA := d.addrA, addrB := d.addrB,
          firstDiff := d.firstDiff }
      out := { out with
        problems := out.problems.push s!"UNRECORDED\n{entry.syntax}"
        entries := out.entries.push entry }
  for e in es do
    unless ds.any (·.constant == e.constant) do
      out := { out with problems := out.problems.push s!"STALE {key} {e.constant} ({e.cause.tag})" }
  return out

/-- Every pair of `families` against the record. Prints a line per pair and
    every problem; returns the number of problems and the re-recorded
    entries of `families`, by family. -/
def pairsGate (env : Environment) (families : List Family) (lean : Compiled)
    (record : List NonCanonicalEntry) (refused : Std.HashSet Name)
    (dumpDir : Option System.FilePath) :
    IO (Nat × Std.HashMap Name (Array NonCanonicalEntry)) := do
  let mut totalDiffs := 0
  let mut problems : Array String := #[]
  let mut rerecorded : Std.HashMap Name (Array NonCanonicalEntry) := {}
  for f in families do
    for (a, b) in pairsOf f do
      let ds ← comparePair env lean f a b dumpDir refused
      -- one entry per constant of A (several of B may map onto it), in name order
      let ds := ds.foldl (init := #[]) fun acc d =>
        if acc.any (·.constant == d.constant) then acc else acc.push d
      let ds := ds.qsort (·.constant.toString < ·.constant.toString)
      totalDiffs := totalDiffs + ds.size
      let es := nonCanonicalFor record f a b
      -- a constant whose Lean name (in A, or its counterpart in B) holds the
      -- image of an image-kind head
      let bHeads : Std.HashSet Name := (presConsts env b).foldl (init := {}) fun s (n, _) =>
        if lean.isHead n then s.insert (mapInto a b n) else s
      let head (c : Name) : Bool := lean.isHead (a.ns ++ c) || bHeads.contains (a.ns ++ c)
      let o := checkPair f a b ds es head
      problems := problems ++ o.problems
      rerecorded := rerecorded.insert f.fixture ((rerecorded.getD f.fixture #[]) ++ o.entries)
      let nInh := (ds.filter fun d => d.cls matches .inherited _).size
      IO.println s!"[twins] {f.fixture.getString!} {a.id}/{b.id}: {ds.size} differ \
({ds.size - nInh} root or one-sided, {nInh} inherited), {es.length} recorded"
      for d in ds do
        unless d.cls matches .inherited _ do
          IO.println s!"[twins]   {d.cls.tag} {d.constant} {d.firstDiff}"
  for e in orphans record do
    problems := problems.push s!"ORPHAN {e.fixture} {e.presA}/{e.presB} {e.constant}: no such family pair"
  IO.println s!"[twins] {totalDiffs} differences; {problems.size} problems"
  for p in problems do IO.println s!"[twins] {p}"
  return (problems.size, rerecorded)

/-- The re-recorded data file: the selected families' entries from this run,
    the other families' entries as recorded, in `allFamilies`' order. -/
def rerecordFile (record : List NonCanonicalEntry) (selected : List Family)
    (rerecorded : Std.HashMap Name (Array NonCanonicalEntry)) : String :=
  let entries := allFamilies.foldl (init := #[]) fun acc f =>
    if selected.any (·.fixture == f.fixture) then acc ++ rerecorded.getD f.fixture #[]
    else acc ++ (record.filter (·.fixture == f.fixture)).toArray
  recordFile entries.toList

/-! ## The gate -/

def run : IO UInt32 := do
  let want ← Only.selectContaining "twins" "IX_TWINS_ONLY" (allFamilies.map (·.fixture.toString))
  let families := allFamilies.filter (want ·.fixture.toString)
  let dumpDir := (← IO.getEnv "IX_TWINS_DUMP").map System.FilePath.mk
  if let some d := dumpDir then IO.FS.createDirAll d
  let t0 ← IO.monoMsNow
  let env ← fixturesEnv
  let (seeds, closure) := familyClosure env families
  let t1 ← IO.monoMsNow
  IO.println s!"[twins] {families.length} of {allFamilies.length} families, {seeds.size} fixture \
constants, {closure.length} in the closure (environment and closure {t1 - t0} ms)"
  -- the Lean compiler (`ix compile-lean`)
  let leanOut ← ClosureHarness.compileClosure env closure
  let t2 ← IO.monoMsNow
  IO.println s!"[twins] Lean compile: {leanOut.bytes.size} bytes, \
{leanOut.cenv.ungrounded.size} block failures, {t2 - t1} ms"
  if let some path := (← IO.getEnv "IX_TWINS_IXE") then
    IO.FS.writeBinFile path leanOut.bytes
    IO.println s!"[twins] wrote {path}"
  -- the Rust compiler (`ix compile`), partial output allowed
  let scope : Std.HashSet Name := closure.foldl (init := {}) fun s (n, _) => s.insert n
  let mut failures ← refusalCheck "twins: Lean" scope
    (leanOut.cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e))
  let dir ← IO.FS.createTempDir
  let mut rsUngrounded : Array (String × String) := #[]
  let mut rsDeclines : Array (String × String) := #[]
  let mut rsEnv : Ixon.Env := {}
  try
    let (bytes, status) ← ClosureHarness.rustClosure env closure (dir / "twins-rs.ixe")
    rsEnv ← IO.ofExcept (Ixon.rsDeEnv bytes)
    rsUngrounded := status.ungrounded
    rsDeclines := status.nonCanonical.qsort (·.1 < ·.1)
  catch ex =>
    IO.println s!"[twins] Rust compile failed: {ex}"
    failures := failures + 1
  IO.FS.removeDirAll dir
  IO.println s!"[twins] Rust compile: {rsUngrounded.size} block failures, {(← IO.monoMsNow) - t2} ms"
  failures := failures + (← refusalCheck "twins: Rust" scope rsUngrounded.toList)
  let leanAddr (n : Name) : Option String :=
    (leanOut.env.getAddr? (_root_.Ix.Name.fromLeanName n)).map toString
  let rsAddr (n : Name) : Option String :=
    (rsEnv.getAddr? (_root_.Ix.Name.fromLeanName n)).map toString
  let declines := (leanOut.cenv.p3NonCanonical.toArray.map fun (n, cause) =>
    (n.pretty, cause)).qsort (·.1 < ·.1)
  if declines != rsDeclines then
    failures := failures + 1
    IO.println s!"[twins] Lean/Rust decline reports differ: Lean {declines.toList}, Rust {rsDeclines.toList}"
  IO.println s!"[twins] {declines.size} recorded declines"
  for (name, cause) in declines do IO.println s!"[twins] decline {name}: {cause}"
  -- 2. Lean and Rust agree on every fixture constant
  let mut lr := 0
  for n in seeds do
    if leanAddr n != rsAddr n then
      lr := lr + 1
      if lr ≤ 20 then
        IO.println s!"[twins] Lean/Rust differ: {n}: lean {leanAddr n} rust {rsAddr n}"
  IO.println s!"[twins] Lean/Rust: {seeds.size - lr}/{seeds.size} fixture constants agree"
  failures := failures + lr
  -- 3. the pairs against the record
  let record := Tests.Ix.Compile.NonCanonicalDefault.nonCanonical
  let (problems, rerecorded) ←
    pairsGate env families
      { addr := leanAddr
        isHead := fun n => leanOut.cenv.p3Heads.contains (_root_.Ix.Name.fromLeanName n) }
      record refusedSet dumpDir
  failures := failures + problems
  if let some path := (← IO.getEnv "IX_TWINS_RECORD") then
    IO.FS.writeFile path (rerecordFile record families rerecorded)
    IO.println s!"[twins] re-recorded {families.length} families to {path}: review its diff \
against Tests/Ix/Compile/NonCanonicalDefault.lean"
  IO.println s!"[twins] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.Twins
