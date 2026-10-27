/-
  aux-oracle: Lean's own auxiliaries against the ones Ix regenerates.

  For every block twin family of `Tests.Ix.Compile.Twins` with a canonical
  reference presentation (the oracle experiment's pairs, the prototype's
  cases, the library twins of `Tests/Ix/Compile/Oracle/Lib.lean`) and for
  `UnivSplit`, the reference presentation `T` is the one in Ix's canonical
  form, whose auxiliaries Lean built with its own constructions (the
  `inductive` elaborator, or `Oracle.Gen` replaying it). For each auxiliary
  `t` of `T` (`rec`, `rec_N`, `casesOn`, `recOn`, `below`, `below_N`,
  `brecOn`, `brecOn_N`, `.go`, `.eq`, `noConfusionType`, `noConfusion`,
  `ctorIdx`, `ctorElim`, `_sizeOf_N`, …) and each auxiliary `o` of the other
  presentation `O` that the name map sends to `t`:

  - `lean(t)`: Lean's own form of `t` compiled by the Lean compiler, i.e.
    `Named.original` when the compiler regenerated `t`, else `t`'s address;
  - `ix(o)`: the auxiliary Ix regenerated for `O`, read at `o`. `ix(t)`
    likewise.

  The oracle requires `ix(o) = lean(t)` byte for byte. Every exception is
  classified, and the suite passes when every exception is in an accepted
  class:
  - `(a)`: the two Lean constants have different universe lists (a split
    member keeps the block's universes; `UnivSplit`);
  - `(b)`: the auxiliary exists on one side only (Lean generates it for one
    block shape and not the other);
  - `(c)`: `noConfusionType`/`noConfusion`, whose enumeration form depends
    on the block;
  - `(d)`: the `sizeOf` family (`_sizeOf_N`, `sizeOf_spec`), numbered over
    the Lean block.

  (The donor's class `(f)`, an open defect of the fixture itself, is not
  kept: its two defects are fixed, WB-B1 `FieldBelow` by A0 and the Prop
  `below` over a reducible alias, `RecAlias`, by building every Prop
  `below` from the recursor's minors, so an exception there is
  `UNEXPECTED`.)

  Two classes are recognised and fail the suite, since each is a regression
  of a canonical-form change of the layout migration:
  - `PACKAGING`: `ix(o) = ix(t)`, and `ix(t)` is a projection into a block of
    several members while Lean's form is packaged otherwise (one constant
    per auxiliary, D6);
  - `NESTED-ORDER`: `ix(o) = ix(t)`, and `T`'s own block has its nested
    auxiliaries in an order other than Lean's (a non-identity `AuxLayout`),
    so Lean's forms of its recursors and their users differ from Ix's (the
    discovery order of the canonical expansion).

  Two more classes, both bounded by records that are exact elsewhere:
  - `(nc) <cause>`: a constant Ix does not regenerate (the users of the
    images, `ctorIdx`, `ctorElim`, `.elim`, `.inj`, `noConfusion`,
    …) is Lean's own term over the presentation's images, so it differs
    where the twins gate records it: accepted only when the twins record
    (`NonCanonicalDefault.nonCanonical`, exact in both directions against
    the same compiler) has the constant for this family and pair, with a
    reviewed cause and the same two addresses.

  Anything else is `UNEXPECTED` and fails. Also checked: that `T` is in Ix's
  canonical order (in every Lean block of `T` the `iPrj` indices of the
  members increase), which the oracle presupposes; a non-canonical `T`
  fails the suite. The families of `Tests/Ix/Compile/Fixtures` (`LetNonDep`,
  `NestedLevels`) are left out: both their presentations are Lean sources
  in two member orders, so neither is a canonical reference (`twins`,
  `aux-cert` and `nested-agreement` check them).

  The fixtures are not in `IxTests`' environment: like `twins`, the suite
  loads them at run time (`Twins.fixturesEnv`) and compiles the families'
  closure once with the Lean compiler (`ClosureHarness.compileClosure`).

  Run with: `lake exe IxTests aux-oracle`.
-/
import Tests.Ix.Compile.Twins

open Lean Tests.Ix.Compile.Twins

namespace Tests.Ix.Compile.Oracle

/-- Generated-name suffixes (`Gen.familyNames`). -/
def genSuffix (s : String) : Bool :=
  ["rec", "casesOn", "recOn", "below", "brecOn", "go", "eq", "noConfusionType", "noConfusion",
    "ctorIdx", "ctorElim", "ctorElimType", "_sizeOf_inst", "inj", "injEq", "sizeOf_spec", "elim",
    ].contains s
  || s.startsWith "rec_" || s.startsWith "below_" || s.startsWith "brecOn_"
  || s.startsWith "_sizeOf_"

/-- An auxiliary of an inductive family: a name whose components after the
    longest prefix naming an inductive or a constructor are all generated. -/
def isAux (env : Environment) (n : Name) : Bool :=
  let rec go (p : Name) (sfx : List String) : Bool :=
    match p with
    | .str q s =>
      let here := match env.find? p with
        | some (.inductInfo _) | some (.ctorInfo _) => !sfx.isEmpty && sfx.all genSuffix
        | _ => false
      here || go q (s :: sfx)
    | _ => false
  match env.find? n with
  | some (.inductInfo _) | some (.ctorInfo _) => false
  | _ => go n []

def kindOf (env : Ixon.Env) (a : Address) : String :=
  match env.getConst? a with
  | some c => match c.info with
    | .defn _ => "defn" | .recr _ => "recr" | .axio _ => "axio" | .quot _ => "quot"
    | .cPrj _ => "cPrj" | .rPrj _ => "rPrj" | .iPrj _ => "iPrj" | .dPrj _ => "dPrj"
    | .muts ms => s!"muts{ms.size}"
  | none => "absent"

/-- The member count of the block a projection points into (`none` for a
    constant that is not a projection). -/
def projBlockSize (env : Ixon.Env) (a : Address) : Option Nat := do
  let c ← env.getConst? a
  let blk ← match c.info with
    | .cPrj p => some p.block | .rPrj p => some p.block | .iPrj p => some p.block
    | .dPrj p => some p.block | _ => none
  match (← env.getConst? blk).info with
  | .muts ms => some ms.size
  | _ => none

/-- The position of an inductive in its Ix block (`iPrj` index). -/
def iPrjIdx (env : Ixon.Env) (a : Address) : Option Nat := do
  match (← env.getConst? a).info with
  | .iPrj p => some p.idx.toNat
  | _ => none

/-- The class of an exception, from the auxiliary's name and the two Lean
    constants. -/
def classify (env : Environment) (t o : Option Name) (sameIx packaged : Bool) : String :=
  let last := match t.orElse fun _ => o with
    | some n => match n with | .str _ s => s | _ => ""
    | none => ""
  let lps (n? : Option Name) : Option Nat := n?.bind fun n => (env.find? n).map (·.levelParams.length)
  if t.isNone || o.isNone then "(b)"
  else if lps t != lps o then "(a)"
  else if last == "noConfusion" || last == "noConfusionType" then "(c)"
  else if last.startsWith "_sizeOf_" || last == "sizeOf_spec" then "(d)"
  else if sameIx && packaged then "PACKAGING"
  else "UNEXPECTED"

/-- The classes that fail the suite. -/
def failing (cls : String) : Bool :=
  cls == "UNEXPECTED" || cls == "PACKAGING" || cls == "NESTED-ORDER"


/-- The twins gate's record of a non-canonical constant (`NonCanonicalDefault`,
    exact in both directions against the same compiler): its reviewed cause,
    when it lists `t` (relative to `A`'s namespace) for this family and pair
    with the same addresses. `pinB` is false when several constants of `B`
    map to `t` (a collapsed twin): the gate keeps one entry per constant of
    `A`, pinned to the first of them, so only `A`'s address is pinned. -/
def recordedCause (fixture : Name) (a b : String) (t : Name) (addrA addrB : Option Address)
    (pinB : Bool := true) : Option String :=
  let hex (x : Option Address) : String := (x.map toString).getD "-"
  (Tests.Ix.Compile.NonCanonicalDefault.nonCanonical.find? fun x =>
    x.fixture == fixture && x.presA == a && x.presB == b && x.constant == t &&
      x.addrA == hex addrA && (!pinB || x.addrB == hex addrB) &&
      !(x.cause matches .unreviewed _)).map fun x => s!"(nc) {x.cause.tag}"

structure Row where
  family : Name
  aux : Name
  cls : String
  detail : String

/-- One family: the rows of every exception, and the number compared. -/
def oracleFamily (env : Environment) (ixon : Ixon.Env) (f : Family) : IO (Nat × Array Row) := do
  let some a := f.pres.head? | return (0, #[])
  let some b := f.pres[1]? | return (0, #[])
  -- the Ix auxiliary Lean calls `n`, under `n`
  let leanName (n : Name) : Option Address := ixon.getAddr? (_root_.Ix.Name.fromLeanName n)
  let addr (n : Name) : Option Address := leanName n
  let named (n : Name) := ixon.named.get? (_root_.Ix.Name.fromLeanName n)
  let lean (n : Name) : Option Address := match named n with
    | some nm => some (nm.original.map (·.1) |>.getD nm.addr)
    | none => none
  let rel (n : Name) : Name := n.replacePrefix a.ns .anonymous
  let ca := (presConsts env a).filter (isAux env ·.1)
  let cb := (presConsts env b).filter (isAux env ·.1)
  let mapB := mapInto a b
  -- `T`'s own block with its nested auxiliaries in another order than
  -- Lean's (a non-identity `AuxLayout`): Lean built `T`'s auxiliaries over
  -- its own order, so they would differ from Ix's by the nested order
  let tInds : Std.HashSet Address := (presConsts env a).foldl (init := {}) fun s (n, ci) => match ci with
    | .inductInfo _ => s.insert (_root_.Ix.Name.fromLeanName n).getHash
    | _ => s
  let nestedMoved := ixon.named.fold (init := false) fun acc _ nm =>
    acc || match nm.constMeta.info with
      | .muts all (some lay) =>
        (lay.perm.zipIdx.any fun (p, i) => p != UInt64.ofNat i) &&
          all.any (·.any tInds.contains)
      | _ => false
  let mut rows : Array Row := #[]
  let mut n := 0
  let mut hit : Std.HashSet Name := {}
  for (o, _) in cb do
    let t := mapB o
    if !(ca.any (·.1 == t)) then
      rows := rows.push
        { family := f.fixture, aux := rel t, cls := classify env none (some o) false false,
          detail := s!"only in {b.id}" }
      continue
    hit := hit.insert t
    n := n + 1
    if addr o == lean t then continue
    let sameIx := addr o == addr t
    let packaged := match addr t, lean t with
      | some x, some y => x != y && (projBlockSize ixon x).getD 0 > 1
      | _, _ => false
    let cls := classify env (some t) (some o) sameIx packaged
    -- UnivSplit: the split member keeps the block's universe list, and the
    -- users of its recursor follow (class (a))
    let cls := if cls == "UNEXPECTED" && f.fixture.getString! == "UnivSplit" then "(a)" else cls
    -- the nested order: `T`'s own block is not in Lean's nested order, so
    -- Lean's forms of its recursors and their users differ
    let cls := if sameIx && nestedMoved && (cls == "UNEXPECTED" || cls == "PACKAGING")
      then "NESTED-ORDER" else cls
    -- a constant Ix does not regenerate (on both sides): Lean's own term over
    -- the images, accepted where the twins record pins the same difference
    let cls := if cls != "UNEXPECTED" then cls
      else (recordedCause f.fixture a.id b.id (rel t) (leanName t) (leanName o)
        (pinB := (cb.filter (mapB ·.1 == t)).size == 1)).getD cls
    let k (x : Option Address) : String := (x.map (kindOf ixon)).getD "-"
    rows := rows.push
      { family := f.fixture, aux := rel t, cls,
        detail := s!"ix({b.id}) {k (addr o)} {(addr o).map toString |>.getD "-" |>.take 12}, \
lean({a.id}) {k (lean t)} {(lean t).map toString |>.getD "-" |>.take 12}, \
ix({a.id}) {k (addr t)}{if sameIx then " (= ix(" ++ b.id ++ "))" else ""}" }
  for (t, _) in ca do
    if !hit.contains t then
      rows := rows.push
        { family := f.fixture, aux := rel t, cls := classify env (some t) none false false,
          detail := s!"only in {a.id}" }
  return (n, rows)

/-- The oracle families: every twin family with a canonical reference
    presentation (no clique family, none of `Tests/Ix/Compile/Fixtures`),
    and `UnivSplit` (class (a)). -/
def oracleFamilies : List Family :=
  (allFamilies.filter fun f =>
    f.kind != .clique && !(`Tests.Ix.Compile.Fixtures).isPrefixOf f.fixture) ++
  [{ fixture := `Tests.Ix.Compile.Twins.Repro.UnivSplit, kind := .block
     pres := [{ id := "twin", ns := `Tests.Ix.Compile.Twins.Repro.Twin.Tw.UnivSplit },
              { id := "orig", ns := `Tests.Ix.Compile.Twins.Repro.Orig.UnivSplit }] }]

def run : IO UInt32 := do
  let env ← fixturesEnv
  let families := oracleFamilies
  let (seeds, closure) := familyClosure env families
  IO.println s!"[aux-oracle] {families.length} families, {seeds.size} fixture constants, \
{closure.length} in the closure"
  let out ← ClosureHarness.compileClosure env closure
  let scope : Std.HashSet Name := closure.foldl (init := {}) fun s (x, _) => s.insert x
  let mut failures ← refusalCheck "aux-oracle" scope
    (out.cenv.ungrounded.toList.map fun (x, e) => (x.pretty, e))
  let mut total := 0
  let mut byClass : Std.HashMap String Nat := {}
  for f in families do
    let (n, rows) ← oracleFamily env out.env f
    total := total + n
    let some a := f.pres.head? | continue
    -- the oracle presupposes that `T` is canonical: in every Lean block of
    -- `T`, Ix keeps the members in Lean's order (`iPrj` indices increase)
    let idx (x : Name) : Option Nat :=
      (out.env.getAddr? (_root_.Ix.Name.fromLeanName x)).bind (iPrjIdx out.env ·)
    let notCanon := (presConsts env a).filterMap fun (_, ci) => match ci with
      | .inductInfo v =>
        let is := v.all.map idx
        if v.all.head? == some ci.name && is.all Option.isSome &&
            !(is.zip is.tail).all (fun (x, y) => x.getD 0 ≤ y.getD 0)
        then some (v.all.map (·.replacePrefix a.ns .anonymous), is.map (·.getD 0)) else none
      | _ => none
    IO.println s!"[aux-oracle] {f.fixture.getString!}: {n} compared, {rows.size} exceptions\
{if notCanon.isEmpty then s!"; {a.id} canonical" else s!"; {a.id} NOT canonical: {notCanon.toList}"}"
    failures := failures + notCanon.size
    for r in rows do
      byClass := byClass.insert r.cls ((byClass.getD r.cls 0) + 1)
      IO.println s!"[aux-oracle]   {r.cls} {r.aux}: {r.detail}"
      if failing r.cls then failures := failures + 1
  IO.println s!"[aux-oracle] {total} auxiliaries compared; exceptions by class: \
{byClass.toList.map fun (c, k) => s!"{c} {k}"}"
  IO.println s!"[aux-oracle] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.Oracle
