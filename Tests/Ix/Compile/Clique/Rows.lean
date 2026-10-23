/-
  clique-rows: the equation rows of the transported well-founded cliques and
  the faithful copies of their encoding (`Ix.Compile.Pass.Clique.rowsOf`,
  `Ix/Compile/Pass/Clique/Row.lean`), admitted by Lean's kernel.

  For every clique of the library suites' fixtures (the clique twins, the
  library's own fixtures and the ownership suite's sources and lemma
  cliques, loaded at run time with the twins; `clique-rust-parity`'s
  `cliques`), with the members' equation lemmas realised, with and without
  the carried lemmas, under a name-hash and a content address, Lean's
  `planClique`; then, for each transported well-founded plan, `rowsOf` and,
  over a scratch copy of the fixtures' environment, with Lean's kernel
  (`addDecl`, `Elab.async false`, in dependency order):

  1. the canonical constants (`canonConst`, the side-car record on the
     functional);
  2. the transported members under scratch names (`f._scratch`: Lean's
     environment already has `f`);
  3. the copies `n._ix.src`;
  4. the rows `f._ix.row`, their right-hand sides renamed to the scratch
     members.

  Every copy and row must be accepted (a setup failure in 1-2, a refusal of
  `rowsOf` or a rejection fails the run). The negative control: each row
  with its right-hand side swapped to another transported member
  (`f'._scratch`, the next in Lean's order), its proof unchanged, must be
  rejected, except where the swapped statement is the row's own up to
  definitional equality. Those exceptions are listed (`expectedAccepted`,
  each with its reason) and checked both ways: an accepted swap outside the
  list, a listed clique whose swaps are all rejected, or a listed one that
  is not two members of one propositional type, fails the run. Static
  checks on every plan: no copy is unused (each is referenced by a row or by
  another copy), no `_ix.src` reference dangles (each names a copy of the
  plan), no copy or row references one of Lean's own encoding constants of
  the clique; and a transported plan of another encoding has no row
  (`rowOf` is `none` for each member, `rowsOf` empty).

  Admission here is by Lean's kernel. The rows are not emitted until the
  wiring step (`Ix.Compile.Pass` does not call the clique library yet), so
  the admission of compiler-emitted rows by IxC belongs to the wiring step's
  tests.

  Invoked as `lake test -- clique-rows`.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Pass.Clique
import Tests.Ix.Compile.Clique.Common
import Tests.Ix.Compile.Clique.RustParity

open Lean

namespace Tests.Ix.Compile.Clique.Rows

open Tests.Ix.Compile.Clique.Common
open _root_.Ix.Compile.Pass.Clique (CliquePlan CliqueOutcome Decl)

private def say (s : String) : IO Unit := IO.println s!"[clique-rows] {s}"

/-- The cliques whose swapped rows the kernel accepts, with the reason: the
swapped statement is the row's own up to definitional equality. -/
def expectedAccepted : List (Name × String) :=
  [(`Tests.Ix.Compile.Twins.Cliques.TQ.P1,
    "theorem members of one statement: the right-hand sides are proofs of one proposition, \
     definitionally equal by proof irrelevance, so the swapped row states the same equation")]

/-! ## The kernel -/

/-- A definition or theorem as a kernel declaration, its names (its own, its
references and `all`) mapped by `rename`. -/
def kernelDeclOf (rename : IxName → Option IxName) : IxConst → Option Declaration
  | .defnInfo v =>
    let ren := _root_.Ix.Compile.Pass.Clique.renameConsts rename
    let n (x : IxName) : Name := toLeanName ((rename x).getD x)
    some (.defnDecl { name := n v.cnst.name, levelParams := v.cnst.levelParams.toList.map toLeanName,
                      type := toLeanExpr (ren v.cnst.type), value := toLeanExpr (ren v.value),
                      hints := v.hints, safety := v.safety, all := v.all.toList.map n })
  | .thmInfo v =>
    let ren := _root_.Ix.Compile.Pass.Clique.renameConsts rename
    let n (x : IxName) : Name := toLeanName ((rename x).getD x)
    some (.thmDecl { name := n v.cnst.name, levelParams := v.cnst.levelParams.toList.map toLeanName,
                     type := toLeanExpr (ren v.cnst.type), value := toLeanExpr (ren v.value),
                     all := v.all.toList.map n })
  | _ => none

/-- Add one constant (renamed by `rename`) with Lean's kernel; the error, or
`none`. -/
def addOne (rename : IxName → Option IxName) (ci : IxConst) : CoreM (Option String) := do
  match kernelDeclOf rename ci with
  | some d => kernelAdd d
  | none => return some s!"{ci.getCnst.name.pretty} is not a definition or a theorem"

/-- Add a batch in dependency order (a constant after the batch's constants
it references); each constant's verdict, under its own name. -/
def addBatch (rename : IxName → Option IxName) (cis : Array IxConst) :
    CoreM (Array (IxName × Option String)) := do
  let names : Std.HashSet IxName := cis.foldl (fun s ci => s.insert ci.getCnst.name) {}
  let mut done : Std.HashSet IxName := {}
  let mut pending := cis
  let mut out := #[]
  for _ in [0:cis.size + 1] do
    if pending.isEmpty then break
    let mut rest := #[]
    for ci in pending do
      let deps := (RustParity.refsOf ci).filter fun r => names.contains r && r != ci.getCnst.name
      if deps.all done.contains then
        out := out.push (ci.getCnst.name, ← addOne rename ci)
        done := done.insert ci.getCnst.name
      else rest := rest.push ci
    pending := rest
  for ci in pending do out := out.push (ci.getCnst.name, some "a dependency cycle")
  return out

/-! ## One plan -/

structure Tally where
  /-- transported plans: well-founded (validated), of another encoding -/
  wfPlans : Nat := 0
  otherPlans : Nat := 0
  copies : Nat := 0
  copiesAccepted : Nat := 0
  rows : Nat := 0
  rowsAccepted : Nat := 0
  negatives : Nat := 0
  negativesRejected : Nat := 0
  /-- accepted swaps of a listed clique: the clique and the row -/
  exceptions : Array (Name × String) := #[]
  failures : Array String := #[]

def Tally.fail (t : Tally) (s : String) : Tally := { t with failures := t.failures.push s }

/-- `x._ix.src`. -/
def isCopyName : IxName → Bool
  | .str (.str _ "_ix" _) "src" _ => true
  | _ => false

/-- The member of a row name `f._ix.row`. -/
def rowOwner? : IxName → Option IxName
  | .str (.str f "_ix" _) "row" _ => some f
  | _ => none

/-- The scratch name of a transported member. -/
def scratchName (f : IxName) : IxName := _root_.Ix.Name.mkStr f "_scratch"

/-- The static checks of a plan's copies and rows: each copy used by a row
or another copy, no dangling `_ix.src` reference, no reference to Lean's
own encoding constants. -/
def staticChecks (plan : CliquePlan) (tag : String) (copies rows : Array IxConst) : Array String := Id.run do
  let mut out := #[]
  let copyNames : Std.HashSet IxName := copies.foldl (fun s c => s.insert c.getCnst.name) {}
  let mut used : Std.HashSet IxName := {}
  for ci in copies ++ rows do
    for r in RustParity.refsOf ci do
      if r != ci.getCnst.name then used := used.insert r
      if isCopyName r && !copyNames.contains r then
        out := out.push s!"{tag}: {ci.getCnst.name.pretty} references {r.pretty}, which is not a copy"
      else if _root_.Ix.Compile.Pass.Clique.isEncodingName plan.all r && !copyNames.contains r then
        out := out.push s!"{tag}: {ci.getCnst.name.pretty} references Lean's encoding constant {r.pretty}"
  for c in copies do
    unless used.contains c.getCnst.name do out := out.push s!"{tag}: the copy {c.getCnst.name.pretty} is unused"
  return out

/-- Validate one transported well-founded plan (see the module note). -/
def validate (const? : IxName → Option IxConst) (ns : Name) (plan : CliquePlan) (tag : String) (t0 : Tally) :
    CoreM Tally := do
  let mut t := { t0 with wfPlans := t0.wfPlans + 1 }
  let res := _root_.Ix.Compile.Pass.Clique.rowsOf const? plan
  if let .error why := res then return t.fail s!"{tag}: rowsOf refuses: {why}"
  let .ok (copies, rows) := res | return t
  t :={ t with copies := t.copies + copies.size, rows := t.rows + rows.size }
  for f in staticChecks plan tag copies rows do t := t.fail f
  let rowMembers := _root_.Ix.Compile.Pass.Clique.rowMembers plan
  if rows.size != rowMembers.size then
    t := t.fail s!"{tag}: {rows.size} rows for {rowMembers.size} transported members"
  -- 1. the canonical constants
  let canonCIs := plan.canon.map fun (d, src) =>
    _root_.Ix.Compile.Pass.Clique.canonConst const? d src
      (if plan.functionals.contains d.name then some plan.record else none)
  for (n, r) in ← addBatch (fun _ => none) canonCIs do
    if let some e := r then t := t.fail s!"{tag}: setup: canonical {n.pretty}: {e.take 300}"
  -- 2. the transported members, under scratch names
  let scratch : Std.HashMap IxName IxName := rowMembers.foldl (fun m f => m.insert f (scratchName f)) {}
  let memberCIs := rowMembers.filterMap fun f => do
    let md ← plan.members.get? f
    let ci ← const? f
    pure (_root_.Ix.Compile.Pass.Clique.withValue ci md.value)
  for (n, r) in ← addBatch scratch.get? memberCIs do
    if let some e := r then t := t.fail s!"{tag}: setup: member {n.pretty}: {e.take 300}"
  -- 3. the copies
  for (n, r) in ← addBatch (fun _ => none) copies do
    match r with
    | none => t := { t with copiesAccepted := t.copiesAccepted + 1 }
    | some e => t := t.fail s!"{tag}: the kernel rejects the copy {n.pretty}: {e.take 600}"
  -- 4. the rows, the right-hand sides on the scratch members
  for row in rows do
    match ← addOne scratch.get? row with
    | none => t := { t with rowsAccepted := t.rowsAccepted + 1 }
    | some e => t := t.fail s!"{tag}: the kernel rejects the row {row.getCnst.name.pretty}: {e.take 1000}"
  -- the negative control: each row's right-hand side swapped to the next member
  let listed := expectedAccepted.find? (·.1 == ns)
  for row in rows do
    -- the row's member, the next member, the row as a theorem
    let target : Option (IxName × IxName × _root_.Ix.TheoremVal) := do
      let f ← rowOwner? row.getCnst.name
      let i ← rowMembers.idxOf? f
      let f' ← rowMembers[(i + 1) % rowMembers.size]?
      let .thmInfo v := row | none
      pure (f, f', v)
    let some (f, f', v) := target | t := t.fail s!"{tag}: {row.getCnst.name.pretty} is not a member's row"
    if f' == f then continue
    let swapRhs (n : IxName) : Option IxName :=
      if n == f then some (scratchName f') else scratch.get? n
    let bad : IxConst := .thmInfo { v with
      cnst := { v.cnst with name := _root_.Ix.Name.mkStr v.cnst.name "swapped",
                            type := _root_.Ix.Compile.Pass.Clique.renameConsts swapRhs v.cnst.type }
      all := #[_root_.Ix.Name.mkStr v.cnst.name "swapped"] }
    t := { t with negatives := t.negatives + 1 }
    match ← addOne scratch.get? bad with
    | some _ => t := { t with negativesRejected := t.negativesRejected + 1 }
    | none =>
      let rel := s!"{(toLeanName f).replacePrefix ns .anonymous} ↦ {(toLeanName f').replacePrefix ns .anonymous}"
      -- the reason of the listed exceptions, checked: one type, a proposition
      let oneType := match const? f, const? f' with
        | some a, some b => a.getCnst.type == b.getCnst.type
        | _, _ => false
      let isProp := match v.cnst.type with
        | .app (.app (.app (.const _ #[.zero _] _) _ _) _ _) _ _ => true
        | _ => false
      match listed with
      | some _ =>
        if oneType && isProp then t := { t with exceptions := t.exceptions.push (ns, s!"{tag}: {rel}") }
        else t := t.fail s!"{tag}: listed, but the swapped row {rel} is accepted without one propositional type"
      | none => t := t.fail s!"{tag}: the kernel accepts the swapped row {rel} (one type: {oneType}, a proposition: {isProp})"
  return t

/-- A transported plan of another encoding: no row. -/
def checkNoRows (const? : IxName → Option IxConst) (plan : CliquePlan) (tag : String) (t : Tally) : Tally :=
  let t := { t with otherPlans := t.otherPlans + 1 }
  let t := plan.all.foldl (init := t) fun t m =>
    match _root_.Ix.Compile.Pass.Clique.rowOf const? plan m with
    | .ok none => t
    | .ok (some _) => t.fail s!"{tag}: a {plan.encoding.tag} plan has a row for {m.pretty}"
    | .error e => t.fail s!"{tag}: rowOf of a {plan.encoding.tag} plan fails: {e}"
  match _root_.Ix.Compile.Pass.Clique.rowsOf const? plan with
  | .ok (#[], #[]) => t
  | .ok (cs, rs) => t.fail s!"{tag}: a {plan.encoding.tag} plan has {cs.size} copies and {rs.size} rows"
  | .error e => t.fail s!"{tag}: rowsOf of a {plan.encoding.tag} plan fails: {e}"

/-! ## The suite -/

def run : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let env0 ← fixturesEnv
  let cls := RustParity.cliques env0
  let (env, realised) ← RustParity.withEqLemmas env0 cls
  let const? := constOf env
  let ixEnv := ixEnvOf env
  let oracleFor := SourceFamilyOracle.forLean env ixEnv (cls.flatten.map ixName)
  let ctx : Core.Context := { fileName := "<clique-rows>", fileMap := default, maxHeartbeats := 0 }
  let mut t : Tally := {}
  let mut planned := 0
  let mut wfCliques : Std.HashSet Name := {}
  for ms in cls do
    let some m0 := ms[0]? | continue
    let ns := m0.getPrefix
    let all := ms.map ixName
    let carried := RustParity.carriedOf const? all
    let label := toString (ms.map fun n => (RustParity.userName n).replacePrefix ns .anonymous) ++ s!" in {ns}"
    for carriedV in (if carried.isEmpty then #[#[]] else #[#[], carried]) do
      for (aname, addr?) in [("name", RustParity.nameAddr), ("content", RustParity.contentAddr const? ns)] do
        planned := planned + 1
        let .transported plan := _root_.Ix.Compile.Pass.Clique.planClique oracleFor ixEnv addr? all carriedV | continue
        let tag := s!"{label} carried={carriedV.size} addr={aname} σ={plan.sigma}"
        if plan.encoding != .wellFounded then
          t := checkNoRows const? plan tag t
          continue
        wfCliques := wfCliques.insert ns
        let (t', _) ← (validate const? ns plan tag t).toIO ctx { env }
        t := t'
  -- every listed exception is observed
  for (ns, why) in expectedAccepted do
    unless t.exceptions.any (·.1 == ns) do
      t := t.fail s!"the listed exception {ns} ({why}) is not observed: its swapped rows are rejected"
  say s!"{cls.size} cliques ({realised} equation lemmas realised), {planned} plans asked for (with and \
    without carried lemmas, two addresses); transported: {t.wfPlans} well-founded ({wfCliques.size} cliques), \
    {t.otherPlans} of another encoding (no rows: checked)"
  say s!"copies: {t.copiesAccepted}/{t.copies} accepted; rows: {t.rowsAccepted}/{t.rows} accepted"
  say s!"negative control: {t.negativesRejected}/{t.negatives} swapped rows rejected, \
    {t.exceptions.size} accepted as listed"
  for (ns, why) in expectedAccepted do
    let hits := t.exceptions.filter (·.1 == ns)
    say s!"  listed exception {ns}: {why}"
    for (_, h) in hits do say s!"    accepted: {h}"
  for f in t.failures do say s!"FAIL {f}"
  if t.wfPlans == 0 then say "FAIL no well-founded plan"
  say s!"{t.failures.size} failures ({(← IO.monoMsNow) - t0} ms)"
  return if t.failures.isEmpty && t.wfPlans > 0 then 0 else 1

end Tests.Ix.Compile.Clique.Rows
