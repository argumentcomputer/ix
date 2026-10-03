/-
  twins: the canonicity gate over twin families (Phase A §5.2; design
  document §3.6 leg 5 and §7.2).

  A twin family is several presentations of the same block or clique in
  separate namespaces (`Tests/Ix/Compile/Twins/*.lean`): member
  permutations, renamings, regroupings, components declared separately,
  collapsed twins. The first presentation is the reference `A`; every other
  presentation `B` carries a name map into `A` (namespace replacement, then
  the longest matching prefix rename).

  The suite compiles the union of every presentation's closure once with
  the Lean compiler (`Ix.CompileM.compileLeanInput`, the `ix compile-lean`
  pipeline) and once with the Rust compiler (`rsCompileEnvBytesFFI`, the
  `ix compile` path), and requires:

  1. the two compilers give every fixture constant the same address;
  2. for every pair `(A, B)`, every constant of `B` that maps to a constant
     of `A` has `A`'s address, except the entries of the non-canonical set
     (`Tests.Ix.Compile.NonCanonical.nonCanonical`), and the set is exact:
     a difference without an entry and an entry without a difference both
     fail. Constants on one side only are differences too, after
     generated-number names (`match_N`, `proof_N`, `_sizeOf_N`, `eq_N`, …)
     are matched by address (their numbering is metadata, §5.5).

  Every difference is classified mechanically as `INHERITED` (the two Lean
  terms are equal under the name map, and the constant references a
  differing constant), `UNEXPLAINED` (equal terms, no differing reference:
  a compiler canonicity defect), or `ROOT` (the Lean terms differ; the
  first differing node is reported). Causes of `ROOT` differences are
  assigned by hand in the fixture, from the terms.

  Diagnostics: `IX_TWINS_DUMP=<dir>` writes, per difference, both Lean
  constants pretty-printed and the first differing subterms;
  `IX_TWINS_IXE=<path>` writes the Lean compiler's output for the kernel
  checks of the evidence; `IX_TWINS_KERNELS=<dir>` reads the three
  kernels' verdicts on that output (`KernelVerdicts`) into the suggested
  entries; `IX_TWINS_ONLY=<substring>` restricts the
  families.

  Run with: `lake test -- --ignored twins`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.NonCanonical

import Tests.Ix.Compile.Twins.Cliques
import Tests.Ix.Compile.Twins.Repro
import Tests.Ix.Compile.Twins.Proto
import Tests.Ix.Compile.Oracle.Lib
import LSpec

open LSpec Lean
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
  clique "TN" [("P0", []), ("P1", [])]
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

/-- The prototype's cases (`Tests/Ix/Compile/Twins/Proto.lean`). -/
def protoFamilies : List Family := Tests.Ix.Compile.Twins.Proto.cases.map
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
  cliqueFamilies ++ reproFamilies ++ protoFamilies ++ libraryFamilies

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

/-! ## The gate -/

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

structure DiffRec where
  /-- name in A, relative to A's namespace -/
  constant : Name
  /-- `ROOT`, `INHERITED`, `UNEXPLAINED`, `ONLY-A`, `ONLY-B` -/
  cls : String
  addrA : String
  addrB : String
  firstDiff : String
  /-- the differing constants it references (for `INHERITED`) -/
  via : List Name := []
  deriving Repr

structure Compiled where
  addr : Name → Option String

def nonCanonicalFor (f : Family) (a b : Pres) : List NonCanonicalEntry :=
  Tests.Ix.Compile.NonCanonical.nonCanonical.filter fun e =>
    e.fixture == f.fixture && e.presA == a.id && e.presB == b.id

def presConsts (env : Environment) (p : Pres) : Array (Name × ConstantInfo) :=
  env.constants.fold (init := #[]) fun acc n ci =>
    if p.ns.isPrefixOf n && n != p.ns
        && !p.skip.any (fun s => s.isPrefixOf (n.replacePrefix p.ns .anonymous)) then
      acc.push (n, ci)
    else acc

/-- Kernel verdicts on the Lean compiler's output, read from
    `IX_TWINS_KERNELS=<dir>`: `tc.fail` (`ix check-lean --anon --fail-out`),
    `rs.fail` (`ix check-rs --anon --fail-out`) and `cert.jsonl`
    (`kernel-check-ixe`). Used only to fill the evidence of suggested
    entries: Ix.Tc and the Rust kernel accept an address they do not list;
    the certified checker accepts an address whose row says `accept`
    (a decline or a blocked row counts as not accepted). -/
structure KernelVerdicts where
  tcFail : Std.HashSet String := {}
  rsFail : Std.HashSet String := {}
  certAccept : Std.HashSet String := {}
  loaded : Bool := false

def failAddrs (text : String) : Std.HashSet String :=
  text.splitOn "\n" |>.foldl (init := {}) fun s l =>
    let l := l.trimAscii.toString
    if l.startsWith "#" && l.length == 65 && (l.drop 1).all Char.isHexDigit then
      s.insert (l.drop 1).toString
    else s

def loadKernels (dir : System.FilePath) : IO KernelVerdicts := do
  let tc ← IO.FS.readFile (dir / "tc.fail")
  let rs ← IO.FS.readFile (dir / "rs.fail")
  let cert ← IO.FS.readFile (dir / "cert.jsonl")
  let mut acc : Std.HashSet String := {}
  for l in cert.splitOn "\n" do
    if (l.splitOn "\"outcome\":\"accept\"").length > 1 then
      match l.splitOn "\"address\":\"" with
      | _ :: rest :: _ => acc := acc.insert (rest.take 64).toString
      | _ => pure ()
  return { tcFail := failAddrs tc, rsFail := failAddrs rs, certAccept := acc, loaded := true }

def KernelVerdicts.of (k : KernelVerdicts) (addr : String) : Bool × Bool × Bool :=
  if !k.loaded || addr == "-" then (true, true, true)
  else (!k.tcFail.contains addr, !k.rsFail.contains addr, k.certAccept.contains addr)

/-- The last string component. -/
def lastStr : Name → String
  | .str _ s => s
  | .num p _ => lastStr p
  | .anonymous => ""

/-- A suggested entry for an unrecorded difference: the cause and role
    are guessed from the name and class and must be reviewed against the
    dumped terms before the entry is recorded. -/
def entrySyntax (k : KernelVerdicts) (f : Family) (a b : Pres) (d : DiffRec) : String :=
  let s := lastStr d.constant
  let parent := lastStr d.constant.getPrefix
  let isEq := s == "eq_def" || s == "eq_unfold" || s.startsWith "eq_"
  let isEnc := s == "_mutual" || s == "mutual" || parent == "_mutual" || parent == "mutual"
  let auxNames := ["below", "brecOn", "go", "eq", "rec", "casesOn", "recOn"]
  let isAux := auxNames.contains s || s.startsWith "rec_" || s.startsWith "below_"
    || s.startsWith "brecOn_"
  let isSizeOf := s.startsWith "_sizeOf_" || s == "sizeOf_spec"
  let (cause, role) :=
    if d.cls == "INHERITED" then (".inherited", "user constant") else
    match f.kind with
    | .clique =>
      if isEq && (parent == "_mutual" || parent == "mutual") then (".orderStmt", "encoding equation")
      else if isEq then (".lazy", "equation lemma")
      else if s.startsWith "_proof_" then (".pendingTransport", "encoding obligation")
      else if isEnc then (".pendingTransport", "clique encoding")
      else if s == "_f" then (".pendingTransport", "structural functional")
      else if s.startsWith "match_" then (".pendingTransport", "transformed matcher")
      else (".pendingTransport", "clique member")
    | _ =>
      if isSizeOf then (".o11aPending", "sizeOf family")
      else if s == "noConfusion" || s == "noConfusionType" then (".pendingNoConfusion", "noConfusion")
      else if isAux && (d.cls == "ONLY-A" || d.cls == "ONLY-B") then
        (".pendingSplitAux", "block auxiliary")
      else (".pendingSurgery /- REVIEW -/", "user constant over the block")
  let note := match d.cls with
    | "INHERITED" => s!"via {d.via}" | c => c
  let ka := k.of d.addrA
  let kb := k.of d.addrB
  let fmt (k : Bool × Bool × Bool) : String := s!"({k.1}, {k.2.1}, {k.2.2})"
  let ks := (if ka != (true, true, true) then s!" (kernelsA := {fmt ka})" else "") ++
    (if kb != (true, true, true) then s!" (kernelsB := {fmt kb})" else "")
  s!"  e `{f.fixture} \"{a.id}\" \"{b.id}\" `{d.constant} \"{role}\" {cause}\n" ++
  s!"    \"{d.addrA}\" \"{d.addrB}\" \"{d.firstDiff}\" \"{note}\"{ks},"

/-- The expected refusals (`NonCanonical.expectedRefusals`) as a set. -/
def refusedSet : Std.HashSet Name :=
  expectedRefusals.foldl (init := {}) fun s r => s.insert r.constant

/-- Check one compiler's block failures against the expected refusals of
    the constants in `scope`: every failure must be an expected refusal with
    its message, and every expected refusal in scope must happen. Returns
    the number of violations. -/
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

/-- Compare one pair; returns the differences. -/
def comparePair (env : Environment) (lean : Compiled) (f : Family) (a b : Pres)
    (dumpDir : Option System.FilePath) : IO (Array DiffRec) := do
  -- refused constants (and the constants of A they map to) are not compared
  let cb := (presConsts env b).filter (!refusedSet.contains ·.1)
  let refusedA : Std.HashSet Name := refusedSet.fold (init := {}) fun s r =>
    if b.ns.isPrefixOf r then s.insert (mapInto a b r) else s
  let ca := (presConsts env a).filter fun (n, _) => !refusedSet.contains n && !refusedA.contains n
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
    let (cls, fd, via) :=
      if ds.isEmpty then
        let refs := ciA.getUsedConstantsAsSet.toList.filter differing.contains
        if refs.isEmpty then ("UNEXPLAINED", "", [])
        else ("INHERITED", "", refs.map rel)
      else
        -- which terms differ: T (type), V (value or rules)
        let (tyD, valD) := termFlags mapB ciA ciB
        let k := if packEq mapB ciA ciB then "|K" else ""
        (s!"ROOT[{if tyD then "T" else ""}{if valD then "V" else ""}{k}]", ds[0]!.1, [])
    let d : DiffRec :=
      { constant := rel na, cls, addrA := xa.getD "-", addrB := xb.getD "-", firstDiff := fd, via }
    out := out.push d
    if let some dir := dumpDir then
      if cls != "INHERITED" then
        let mut s := s!"# {f.fixture} {a.id} vs {b.id}: {na} / {nb}\n# class {cls}\n"
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
      { constant := rel n, cls := "ONLY-A", addrA := (lean.addr n).getD "-",
        addrB := "-", firstDiff := "" }
  for n in stillB' do
    out := out.push
      { constant := rel (mapB n), cls := "ONLY-B", addrA := "-",
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

/-- The fixture constants of the families and the union of their closures
    (with recursors, `closeWithRecursors`). -/
def familyClosure (env : Environment) (families : List Family) :
    Array Name × List (Name × ConstantInfo) := Id.run do
  let mut seeds : Array Name := #[]
  for f in families do
    for p in f.pres do
      seeds := seeds ++ (presConsts env p).map (·.1)
  return (seeds, closeWithRecursors env (Ix.EnvScope.collectDeps env seeds.toList))

/-- The Lean compiler on a closure: the `ix compile-lean` pipeline
    (`compileInputFromEnv`, then `compileLeanInput`). -/
def leanCompile (env : Environment) (closure : List (Name × ConstantInfo))
    (workers : Nat := 32) : IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := workers) with
  | .ok o => pure o
  | .error e => throw (IO.userError s!"Lean compile failed: {e}")

/-- The gate. -/
def run : IO UInt32 := do
  let env ← get_env!
  let only := (← IO.getEnv "IX_TWINS_ONLY")
  let families := allFamilies.filter fun f =>
    match only with
    | some s => (f.fixture.toString.splitOn s).length > 1
    | none => true
  let dumpDir := (← IO.getEnv "IX_TWINS_DUMP").map System.FilePath.mk
  let kernels ← match ← IO.getEnv "IX_TWINS_KERNELS" with
    | some d => loadKernels d
    | none => pure {}
  if let some d := dumpDir then IO.FS.createDirAll d
  let (seeds, closure) := familyClosure env families
  IO.println s!"[twins] {families.length} families, {seeds.size} fixture constants, \
{closure.length} in the closure"
  let t0 ← IO.monoMsNow
  let leanOut ← leanCompile env closure
  let t1 ← IO.monoMsNow
  IO.println s!"[twins] Lean compile: {leanOut.bytes.size} bytes, \
{leanOut.cenv.ungrounded.size} block failures, {t1 - t0} ms"
  if let some path := (← IO.getEnv "IX_TWINS_IXE") then
    IO.FS.writeBinFile path leanOut.bytes
    IO.println s!"[twins] wrote {path}"
  -- Rust compiler (the `ix compile` path)
  let dir ← IO.FS.createTempDir
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env closure)
  let rsPath := dir / "twins-rs.ixe"
  let mut failures ← refusalCheck "twins: Lean" ((closure.foldl (init := {}) fun s (n, _) => s.insert n))
    (leanOut.cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e))
  let mut rsUngrounded : Array (String × String) := #[]
  let mut rsEnv : Ixon.Env := {}
  try
    let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared rsPath.toString true
    rsEnv ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile rsPath))
    rsUngrounded := status.ungrounded
  catch ex =>
    IO.println s!"[twins] Rust compile failed: {ex}"
    failures := failures + 1
  IO.FS.removeDirAll dir
  IO.println s!"[twins] Rust compile: {rsUngrounded.size} ungrounded, {(← IO.monoMsNow) - t1} ms"
  let leanAddr (n : Name) : Option String :=
    (leanOut.env.getAddr? (Ix.Name.fromLeanName n)).map toString
  let rsAddr (n : Name) : Option String :=
    (rsEnv.getAddr? (Ix.Name.fromLeanName n)).map toString
  let scope : Std.HashSet Name := closure.foldl (init := {}) fun s (n, _) => s.insert n
  failures := failures + (← refusalCheck "twins: Rust" scope rsUngrounded.toList)
  -- 1. Lean and Rust agree on every fixture constant
  let mut lr := 0
  for n in seeds do
    if leanAddr n != rsAddr n then
      lr := lr + 1
      if lr ≤ 20 then
        IO.println s!"[twins] Lean/Rust differ: {n}: lean {leanAddr n} rust {rsAddr n}"
  IO.println s!"[twins] Lean/Rust: {seeds.size - lr}/{seeds.size} fixture constants agree"
  failures := failures + lr
  -- 2. pairs
  let lean : Compiled := { addr := leanAddr }
  let mut totalDiffs := 0
  let mut unexpected : Array String := #[]
  let mut stale : Array String := #[]
  for f in families do
    let some a := f.pres.head? | continue
    for b in f.pres.tail do
      let ds ← comparePair env lean f a b dumpDir
      -- one record per constant of A (several of B may map onto it)
      let ds := ds.foldl (init := #[]) fun acc d =>
        if acc.any (·.constant == d.constant) then acc else acc.push d
      totalDiffs := totalDiffs + ds.size
      let es := nonCanonicalFor f a b
      let mut nRoot := 0
      let mut nInh := 0
      for d in ds do
        if d.cls == "INHERITED" then nInh := nInh + 1 else nRoot := nRoot + 1
        unless es.any (·.constant == d.constant) do
          unexpected := unexpected.push (entrySyntax kernels f a b d)
        -- evidence drift: the entry still matches, but an address moved since
        -- the measurement (informational; the gate keys entries by constant)
        if let some e := es.find? (·.constant == d.constant) then
          if e.evidence.addrA != d.addrA || e.evidence.addrB != d.addrB then
            IO.println s!"[twins] DRIFT {f.fixture.getString!} {a.id}/{b.id} {d.constant} ({e.cause.tag}): \
{e.evidence.addrA.take 12}/{e.evidence.addrB.take 12} -> {d.addrA.take 12}/{d.addrB.take 12}"
      for e in es do
        unless ds.any (·.constant == e.constant) do
          stale := stale.push s!"{f.fixture} {a.id}/{b.id} {e.constant} ({e.cause.tag})"
      IO.println s!"[twins] {f.fixture.getString!} {a.id}/{b.id}: {ds.size} differ \
({nRoot} root or one-sided, {nInh} inherited), {es.length} recorded"
      for d in ds do
        if d.cls != "INHERITED" then
          IO.println s!"[twins]   {d.cls} {d.constant} {d.firstDiff}"
  IO.println s!"[twins] {totalDiffs} differences; {unexpected.size} unrecorded, {stale.size} stale entries"
  for s in unexpected do IO.println s
  for s in stale do IO.println s!"[twins] STALE {s}"
  failures := failures + unexpected.size + stale.size
  IO.println s!"[twins] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.Twins
