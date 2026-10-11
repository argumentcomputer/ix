/-
  The oracle generator: Lean's own auxiliary constructions on a scratch
  declaration (ported from the oracle experiment's `exp-oracle/lib/Gen.lean`,
  ORA; design document §3.6 and Phase A §5.3).

  `twinBlock pfx comps` declares, for each component (in dependency order),
  ONE `Declaration.inductDecl` whose members are the component's
  representatives in the given order, renamed under `pfx`; every reference to
  a block member or constructor (including a collapsed non-representative) is
  redirected to the twin of its representative; the component's universe
  parameters are pruned to the ones its types and constructor types use
  (original order kept). It then runs the auxiliary constructions the
  inductive elaborator runs: `mkAuxConstructions` is private in
  `Lean.Elab.MutualInductive` and is a fixed sequence of public `MetaM`
  functions, replayed here, as is the private `addAuxRecs`; then
  `mkSizeOfInstances`, `IndPredBelow.mkBelow` and `mkInjectiveTheorems`.
  Every step is timed and every failure is logged.

  These replays track private elaborator steps: a toolchain bump that changes
  `Lean.Elab.MutualInductive` must be mirrored here (checked by the
  `aux-oracle` suite, which compares the generated block with the library's
  own on every library subject).
-/
import Lean
open Lean Meta Elab Command

namespace Tests.Ix.Compile.Oracle.Gen

structure Comp where
  /-- representatives, in canonical order -/
  members : List Name
  /-- collapsed non-representatives: (alias, representative) -/
  aliases : List (Name × Name) := []

/-- Level-parameter positions kept for each twin member, keyed by ORIGINAL member name. -/
abbrev Kept := Std.HashMap Name (Array Nat)

def renameE (m : Std.HashMap Name Name) (kept : Kept) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (m.get? n).map fun n' =>
        let ls' := match kept.get? n with
          | some ks => ks.toList.filterMap (ls[·]?)
          | none => ls
        .const n' ls'
    | _ => none

/-- Replica of the private `addAuxRecs` of `Lean.Elab.MutualInductive`: the kernel adds the
    nested auxiliary recursors `rec_N`; the elaborator must register them itself. -/
def addAuxRecs (names : List Name) : MetaM Unit := do
  for n in names do
    let mut i := 1
    while true do
      let auxRecName := n ++ `rec |>.appendIndexAfter i
      let env ← getEnv
      let some const := env.toKernelEnv.find? auxRecName | break
      let res ← env.addConstAsync auxRecName .recursor
      res.commitConst res.asyncEnv (info? := const)
      res.commitCheckEnv res.asyncEnv
      setEnv res.mainEnv
      i := i + 1

def collectLParams (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name :=
  (CollectLevelParams.main e {}).params.foldl (fun s n => s.insert n) acc

/-- Run one construction; a failure is a warning (so `--wfail` builds fail
    when a replayed elaborator step breaks), success is silent. -/
def timeIt {α} (label : String) (act : MetaM α) : MetaM (Option α) := do
  try
    return some (← act)
  catch e =>
    logWarning m!"[gen] {label}: FAILED: {e.toMessageData}"
    return none

/-- Order components so that each comes after every component it references. -/
def depSort (comps : List Comp) : MetaM (List Comp) := do
  let mut refs : Array (Std.HashSet Name) := #[]
  let mut owner : Std.HashMap Name Nat := {}
  for c in comps, i in [0:comps.length] do
    for r in c.members do owner := owner.insert r i
    for (a, _) in c.aliases do owner := owner.insert a i
  for c in comps do
    let mut s : Std.HashSet Name := {}
    for r in c.members do
      let iv ← getConstInfoInduct r
      for k in iv.ctors do
        for n in (← getConstInfoCtor k).type.getUsedConstants do s := s.insert n
    refs := refs.push s
  let mut done : Std.HashSet Nat := {}
  let mut out : List Comp := []
  for _ in comps do
    for c in comps, i in [0:comps.length] do
      if done.contains i then continue
      let deps := refs[i]!.toList.filterMap owner.get?
      if deps.all (fun j => j == i || done.contains j) then
        done := done.insert i
        out := out ++ [c]
  return out

def twinBlock (pfx : Name) (comps0 : List Comp) : MetaM Unit := do
  let comps ← depSort comps0
  -- name map over the whole block
  let mut m : Std.HashMap Name Name := {}
  for c in comps do
    for r in c.members do
      m := m.insert r (pfx ++ r)
      for k in (← getConstInfoInduct r).ctors do
        m := m.insert k (pfx ++ k)
    for (a, r) in c.aliases do
      m := m.insert a (pfx ++ r)
      let ca := (← getConstInfoInduct a).ctors
      let cr := (← getConstInfoInduct r).ctors
      for (ka, kr) in ca.zip cr do
        m := m.insert ka (pfx ++ kr)
  let mut kept : Kept := {}
  for c in comps do
    let infos ← c.members.mapM getConstInfoInduct
    let iv0 := infos[0]!
    -- universe pruning: the params the component's own types and ctor types use
    let mut used : Std.HashSet Name := {}
    for iv in infos do
      used := collectLParams iv.type used
      for k in iv.ctors do
        used := collectLParams (← getConstInfoCtor k).type used
    let ks : Array Nat := (List.range iv0.levelParams.length).toArray.filter
      fun i => used.contains iv0.levelParams[i]!
    let lps := ks.toList.map (iv0.levelParams[·]!)
    for r in c.members do kept := kept.insert r ks
    for (a, _) in c.aliases do kept := kept.insert a ks
    -- the inner occurrences of the component's OWN level params are untouched: pruning only
    -- drops params that do not occur, so `Expr.param` nodes need no rewrite.
    let mut types : List InductiveType := []
    for iv in infos do
      let mut ctors : List Constructor := []
      for k in iv.ctors do
        let kv ← getConstInfoCtor k
        ctors := ctors ++ [{ name := pfx ++ k, type := renameE m kept kv.type }]
      types := types ++ [{ name := pfx ++ iv.name, type := renameE m kept iv.type, ctors }]
    let decl := Declaration.inductDecl lps iv0.numParams types iv0.isUnsafe
    let names := c.members.map (pfx ++ ·)
    let some _ ← timeIt s!"addDecl {names}" (addDecl decl) | return
    let _ ← timeIt s!"addAuxRecs {names}" (addAuxRecs names)
    -- the elaborator compiles the inductive before the constructions (they emit code)
    let _ ← timeIt s!"compileDecls {names}" (Lean.compileDecls names.toArray)
    for n in names do
      let _ ← timeIt s!"mkRecOn {n}" (mkRecOn n)
      let _ ← timeIt s!"mkCasesOn {n}" (mkCasesOn n)
      let _ ← timeIt s!"mkCtorIdx {n}" (mkCtorIdx n)
      let _ ← timeIt s!"mkCtorElim {n}" (mkCtorElim n)
      let _ ← timeIt s!"mkNoConfusion {n}" (mkNoConfusion n)
      let _ ← timeIt s!"mkBelow {n}" (mkBelow n)
    for n in names do
      let _ ← timeIt s!"mkBRecOn {n}" (mkBRecOn n)
    let _ ← timeIt s!"mkSizeOfInstances {names[0]!}" (mkSizeOfInstances names[0]!)
    let _ ← timeIt s!"IndPredBelow.mkBelow {names[0]!}" (IndPredBelow.mkBelow names[0]!)
    for n in names do
      let _ ← timeIt s!"mkInjectiveTheorems {n}" (mkInjectiveTheorems n)

/-- Family constants of a block member, for `ix compile --consts`: everything whose name
    extends a member or a constructor name, except user code (heuristic allow-list of
    generated suffixes). -/
def familyNames (members : List Name) : MetaM (Array Name) := do
  let env ← getEnv
  let gen : List String := ["rec", "casesOn", "recOn", "below", "brecOn", "go", "eq",
    "noConfusionType", "noConfusion", "ctorIdx", "ctorElim", "ctorElimType", "_sizeOf_inst",
    "inj", "injEq", "sizeOf_spec", "elim", "below_1"]
  let isGen (s : String) : Bool :=
    gen.contains s || s.startsWith "rec_" || s.startsWith "below_" || s.startsWith "brecOn_" ||
      s.startsWith "_sizeOf_"
  let mut heads : Std.HashSet Name := {}
  for r in members do
    heads := heads.insert r
    for k in (← getConstInfoInduct r).ctors do heads := heads.insert k
  let mut out := #[]
  for (n, _) in env.constants.toList do
    if heads.contains n then out := out.push n
    else
      -- n = head ++ suffix components, all generated
      let rec go (p : Name) (sfx : List String) : Bool :=
        match p with
        | .str q s => if heads.contains q then (s :: sfx).all isGen else go q (s :: sfx)
        | _ => false
      if go n [] then out := out.push n
  return out.qsort (·.toString < ·.toString)

end Tests.Ix.Compile.Oracle.Gen
