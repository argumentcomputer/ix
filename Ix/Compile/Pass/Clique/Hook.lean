/-
  Ix.Compile.Pass.Clique.Hook: the changed-clique hook's per-block
  computation, as pure functions over data.

  Before a block compiles, the hook gives it:
  * the callers' refusal (`cliqueCallers`): a block outside a transported
    clique's unit that references a member and one of Lean's encoding
    constants of the clique fails with a named error;
  * for every member of a transported clique in the block, and every carried
    equation lemma, Lean's constant with the transported value, whose root
    carries the decompile record `_ix.inline` of Lean's value (the overlay
    entries and their sources);
  * the canonical constants the transported members reach, as input
    constants, in an order where each one's canonical references come before
    it (or are already compiled);
  * the plans computed for the block (for the plan table) and the number
    taken from the table.

  `HookEnv` is everything the hook reads of the compile state; `CliquePrep`
  is everything it gives. The rest is the wiring's: the block's compile
  environment (the overlay over the input, the `_ix.inline` sources), the
  call-site rewrite and the compile of each canonical constant in
  `CliquePrep.canon`'s order, and the merge of the fresh plans into the plan
  table (`memoMerge`).

  **The memo caveat, for the wiring.** Nothing here reads or writes Pass 3's
  rewrite state (`RwState`). The clique records (the `_ix.clique` record and
  the causes, and later the rows and `_ix.src` copies) are a pure function of
  the clique's plan, attached to the plan's own constants (its members, its
  carried lemmas, its canonical constants), never to an image expansion. The
  canonical constants' call-site rewrite must record nothing: no decline, no
  proof-justified form, no pass's canonical constant, not in place. The
  wiring (`Ix.Compile.Pass.cliqueStep`) rewrites them as a block's members
  are rewritten, with the definitional passes (`passConfig`, which record
  nothing), and refuses a rewrite that records anything
  (`rewriteCliqueCanon`), so it reads the image memo as any block does (a
  recursor's image only, `passExpansionLookup`) and writes no clique data
  into it. If a wiring ever records clique data in `RwState`,
  `readsMemoable` must be false for the expansions that recorded it;
  `CliquePlan.touches` is the test of a constant against a plan.

  **Iteration order.** The block's names and its references are passed as
  hash sets (`Ix.Set`, as the compile loop holds them); everything here that
  depends on an order reads them in pretty-name order (`sortByPretty`), so
  the result does not depend on how the sets were built. Pretty-name sorts
  use `qsort`, which is not stable: two distinct names with one pretty form (a
  string component `"1"` and a number component `1`) may come in either
  order; Lean never generates such a pair (as in `Table`).

  Total and pure: no `IO`, no `CompileM`; the closure over the canonical
  references is bounded by the number of canonical constants, the compile
  order by the donor's rounds.
-/
module
public import Ix.Compile.Pass.Memo
public import Ix.Compile.Pass.Clique.PlanClique
public import Ix.Compile.Pass.Clique.Row
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Expr ConstantInfo)

/-! ## What the hook reads -/

/-- The hook's read of the compile state. -/
structure HookEnv where
  /-- The input constants. -/
  env : Ix.Environment
  /-- The addresses compiled so far (the compiler's resolution map, then its
  auxiliary names). -/
  addr? : Name → Option Address
  /-- The clique table: every member of an input clique, and every carried
  equation lemma, ↦ (Lean's `all`, the carried lemmas) (`scheduleCliques`). -/
  table : Std.HashMap Name (Array Name × Array Name)
  /-- The encoding roots (`all₀._mutual`, `all₀.mutual`, `m._f`) ↦ the clique
  (`scheduleCliques`). -/
  roots : Std.HashMap Name (Array Name)
  /-- The plan table: a memo of `planClique`, keyed by the clique's first
  member, filled by the blocks that computed a plan. -/
  plans : Std.HashMap Name CliqueOutcome := {}
  /-- Recompute every plan the table supplies and fail on a difference
  (`planCheckPrefix`). -/
  checkPlans : Bool := false
  /-- Transport well-founded cliques only (`CliqueOutcome.wfOnly`): the
  compile's setting (decision (ii), 2026-10-21: rows have a proof recipe for
  well-founded cliques only). Off for the library's own tests, which
  exercise all three transports. -/
  wfOnly : Bool := false

/-- Names in pretty-name order (see the module note on ties). -/
def sortByPretty (xs : Array Name) : Array Name := xs.qsort fun a b => a.pretty < b.pretty

/-! ## The plan table -/

/-- A transported plan's records after the fold (`rowsOf`): the `_ix.src`
copies of its encoding set, then its members' rows. -/
abbrev Rows := Array ConstantInfo × Array ConstantInfo

/-- The outcome under decision (ii) (2026-10-21), with the rows it checked: a
transport stands only when its rows apply. A structural or
`partial_fixpoint` clique keeps Lean's form (no row recipe); so does a
well-founded clique whose rows do not apply (`rowsOf` refuses) or whose
rows' prerequisites (`rowPrereqs`) are not all in the input (`const?`), so
that every transported clique gets its rows after the fold
(`Ix.CompileM.emitRows`). The kept form's outcome is `baseline enc .shape`,
the outcome of a transport that kept Lean's form, with the reason, which is
for diagnostics, never a byte. Every other outcome is kept.

The rows are `rowsOf const? plan` for an outcome that stays transported,
`none` otherwise: computed once, when the plan is made, and kept for the
emission (`CliquePrep.rows`, `CompileEnv.p3CliqueRows`). -/
def CliqueOutcome.wfOnlyRows (const? : Name → Option ConstantInfo) :
    CliqueOutcome → CliqueOutcome × Option Rows
  | .transported plan =>
    let keep (why : String) : CliqueOutcome × Option Rows :=
      (.baseline plan.encoding .shape why, none)
    if plan.encoding != .wellFounded then
      keep s!"no row recipe for a {plan.encoding.tag} clique: rows are for well-founded cliques only"
    else if let some p := rowPrereqs.find? (const? · |>.isNone) then
      keep s!"the rows' prerequisite {p.pretty} is not in the input"
    else match rowsOf const? plan with
      | .ok rows => (.transported plan, some rows)
      | .error e => keep s!"the rows do not apply: {e}"
  | o => (o, none)

/-- The outcome under decision (ii) (`CliqueOutcome.wfOnlyRows` without the
rows). -/
def CliqueOutcome.wfOnly (const? : Name → Option ConstantInfo) (o : CliqueOutcome) :
    CliqueOutcome :=
  (o.wfOnlyRows const?).1

/-- The prefix of the plan-table check's error; a driver turns a block
failure with this prefix into a failed compile. -/
def planCheckPrefix : String := "Pass 3 plan cache check:"

/-- The plan of a clique for the current block, and whether it came from the
plan table (`HookEnv.plans`), through `memoLookup`.

**Why a table is allowed.** `planClique` is a function of the clique (`cl`),
its carried lemmas (read from the clique's own unit by `scheduleCliques`),
the input constants of its unit and its dependencies, and the addresses of
those dependencies. Every block that plans the clique (a member's block, a
carried lemma's block, a caller's block) is scheduled after all of the
members' references (`scheduleCliques`' edges), so each computes the same
plan: the table is a memo of that function (with `HookEnv.wfOnly` applied), keyed
by the clique's first member, filled by the first block that needs a plan and merged by the
driver like the other Pass 3 tables (`memoMerge`). Which block filled an
entry, or whether one did, changes no byte and no record. With `checkPlans`,
every plan the table supplies is recomputed, and a difference (by
`CliqueOutcome.same`) is `memoLookup`'s error, prefixed by `planCheckPrefix`
and the clique (`<prefix> the plan of the clique #[…]: the recomputed value
differs from the table's`). A clique without a first member (never in the
table) is planned directly.

A plan computed here (not taken from the table) comes with its rows when it
stays transported (`CliqueOutcome.wfOnlyRows`, which computes them to
decide), for the rows table (`CliquePrep.rows`); a plan from the table comes
without them (they are in the rows table, or the emission computes them). -/
def cliquePlanFor (h : HookEnv) (cl carried : Array Name) :
    Except String (CliqueOutcome × Bool × Option Rows) := do
  let compute (_ : Unit) : CliqueOutcome × Option Rows :=
    let o := planClique h.env h.addr? cl carried
    if h.wfOnly then o.wfOnlyRows h.env.get? else (o, none)
  let some key := cl[0]? | let (o, rows) := compute (); return (o, false, rows)
  unless h.plans.contains key do
    let (o, rows) := compute ()
    return (o, false, rows)
  let what := if h.checkPlans then s!"{planCheckPrefix} the plan of the clique {cl.map (·.pretty)}"
    else planCheckPrefix
  let o ← (letI : BEq CliqueOutcome := ⟨CliqueOutcome.same⟩
    memoLookup h.plans h.checkPlans what key fun _ => pure (compute ()).1)
  return (o, true, none)

/-! ## The callers -/

/-- The prefix of a caller's refusal (`cliqueCallers`): the named error the
driver records as the block's failure, by which the changed-set record tells
a refused caller from any other failed block. -/
def callerRefusalPrefix : String := "Pass 3 cliques: caller refused"

/-- The callers' side of the block rule ("callers adapt"). A block outside a
clique's unit (no member, no carried lemma, no encoding constant of the
clique) that references a member and one of Lean's encoding constants of the
clique may rely on the member unfolding to Lean's encoding. When the clique
is transported (its plan, a function of the clique, its unit and its
dependencies, all compiled before this block: `cliquePlanFor`), that
encoding is no longer what the member unfolds to: the block is refused with
a named error (`callerRefusalPrefix`), recorded as a block failure by the
driver. The clique is never changed for a caller, and the caller is never
silently compiled against Lean's form.

Returns the refusal, or `none` when the block may compile, with the plans it
computed (for the plan table) and the number it took from the table. Reads
only the block (`all`, its references `refs`) and the cliques it depends on.

Order: the references that are encoding constants of a clique
(`encodingOwner?`) are read in pretty-name order, each clique once (at its
first such reference); the member named in the refusal is the clique's
member among `refs` first in pretty-name order, and the callers are listed
in pretty-name order. -/
def cliqueCallers (h : HookEnv) (all refs : Ix.Set Name) :
    Except String (Option String × Array (Name × CliqueOutcome) × Nat) := do
  if h.roots.isEmpty then return (none, #[], 0)
  let owned := (refs.fold (init := #[]) fun acc r => match encodingOwner? h.roots r with
      | some cl => acc.push (r, cl)
      | none => acc).qsort fun a b => a.1.pretty < b.1.pretty
  let mut seen : Std.HashSet Name := {}
  let mut fresh : Array (Name × CliqueOutcome) := #[]
  let mut reused := 0
  for (r, cl) in owned do
    let some key := cl[0]? | continue
    if seen.contains key then continue
    seen := seen.insert key
    let carried := ((h.table.get? key).map (·.2)).getD #[]
    -- a block of the clique's own unit is not a caller
    if all.toList.any fun n => cl.contains n || carried.contains n || isEncodingName cl n then continue
    let some m := (sortByPretty (refs.toArray.filter cl.contains))[0]? | continue
    -- the members' blocks come before a caller's (it references a member)
    -- and plan the clique first: a plan computed here is one whose members
    -- did not compile, so there are no rows to keep
    let (outcome, hit, _) ← cliquePlanFor h cl carried
    if hit then reused := reused + 1 else fresh := fresh.push (key, outcome)
    match outcome with
    | .transported plan =>
      let callers := (sortByPretty all.toArray).toList.map (·.pretty)
      return (some s!"{callerRefusalPrefix} (block rule, callers adapt): {callers} \
        reference{if callers.length == 1 then "s" else ""} {m.pretty} and Lean's encoding constant \
        {r.pretty} of the transported clique {cl.map (·.pretty)} (sigma {plan.sigma}); a caller may \
        not unfold Lean's encoding of a transported clique", fresh, reused)
    | _ => continue
  return (none, fresh, reused)

/-! ## The block's preparation -/

/-- What the hook gives a block. Empty (`isEmpty`) when the block has nothing
to do with a changed clique. -/
structure CliquePrep where
  /-- The transported members and carried lemmas of the block, in the
  block's pretty-name order: Lean's constant (Lean's name and type) with the
  transported value under the decompile record `[(inlineKey, .ofNat i)]`,
  `i = cliqueRecordBase + k` for the `k`-th entry. -/
  overlay : Array (Name × ConstantInfo) := #[]
  /-- The decompile sources of the records: `cliqueRecordBase + k` ↦ Lean's
  value of the `k`-th overlay entry. -/
  sources : Array (Nat × Expr) := #[]
  /-- The canonical constants the block compiles (`canonConst`: the
  functionals carry the side-car record), each after the canonical constants
  it references, except those already compiled (`HookEnv.addr?`). -/
  canon : Array (Name × ConstantInfo) := #[]
  /-- The plans computed for this block, by clique key (for the plan table). -/
  fresh : Array (Name × CliqueOutcome) := #[]
  /-- The rows of the transported plans the block's members computed, by
  clique key (`CliqueOutcome.wfOnlyRows`; for the rows table). -/
  rows : Array (Name × Rows) := #[]
  /-- The number of plans taken from the plan table. -/
  reused : Nat := 0
  deriving Inhabited

def CliquePrep.isEmpty (p : CliquePrep) : Bool :=
  p.overlay.isEmpty && p.sources.isEmpty && p.canon.isEmpty && p.fresh.isEmpty && p.reused == 0

/-- `n` is a constant the plan attaches records to or replaces: a member, a
carried lemma (a transported constant besides the members), or a canonical
constant. -/
def CliquePlan.touches (p : CliquePlan) (n : Name) : Bool :=
  p.all.contains n || p.members.contains n || p.canon.any (·.1.name == n)

/-- The canonical constants reachable from `stack` through the canonical
references (`canonNames`) of their types and values, appended to `wanted`
(with its membership set), each once, in the worklist's order. Every name on
the stack is in `canonNames` and every name appended is new, so with `fuel =
canonNames.size` no name is still due at fuel `0` (every canonical name is
then already wanted): the result is the full closure. -/
def reachCanon (canon : Std.HashMap Name ConstantInfo) (canonNames : Std.HashSet Name) :
    Nat → List Name → Array Name × Std.HashSet Name → Array Name × Std.HashSet Name
  | fuel, stack, (wanted, seen) =>
    match popUnseen seen stack with
    | none => (wanted, seen)
    | some (c, rest) =>
      match fuel with
      | 0 => (wanted, seen)
      | fuel + 1 =>
        let next := match canon.get? c with
          | some cc => constOccurrences canonNames.contains cc.getCnst.type ++
              ((valueOf? cc).map (constOccurrences canonNames.contains)).getD #[]
          | none => #[]
        reachCanon canon canonNames fuel (pushStack rest next) (wanted.push c, seen.insert c)

/-- The canonical constants (other than `c`) that the canonical constant `c`
references in its type and value. -/
def canonRefs (canon : Std.HashMap Name ConstantInfo) (c : Name) (ci : ConstantInfo) : Array Name :=
  let p (r : Name) : Bool := canon.contains r && r != c
  constOccurrences p ci.getCnst.type ++ ((valueOf? ci).map (constOccurrences p)).getD #[]

/-- The error of canonical constants that never become compilable. -/
def cyclicCanonError (pending : Array Name) : String :=
  s!"Pass 3 cliques: canonical constants with cyclic references: {pending.map (·.pretty)}"

/-- The compile order of the pending canonical constants, in rounds: each
round goes through the pending constants in order and takes every one whose
canonical references are known (taken earlier, in this round or a previous
one, or already compiled: `addr?`); the others wait for the next round, in
the same order. At most `fuel` rounds (`pending.size + 1` suffices for any
acyclic set); a round that takes nothing, or pending constants after the
last round, are the cyclic error. -/
def canonRounds (addr? : Name → Option Address) (canon : Std.HashMap Name ConstantInfo) :
    Nat → Array Name → Array (Name × ConstantInfo) → Std.HashSet Name →
      Except String (Array (Name × ConstantInfo))
  | 0, pending, order, _ => if pending.isEmpty then pure order else throw (cyclicCanonError pending)
  | fuel + 1, pending, order, done =>
    if pending.isEmpty then pure order else do
    let (order, done, rest) ← pending.foldlM (init := (order, done, #[]))
      fun (order, done, rest) c => do
        let some ci := canon.get? c | throw s!"Pass 3 cliques: no canonical constant {c.pretty}"
        if (canonRefs canon c ci).any fun r => !done.contains r && (addr? r).isNone then
          pure (order, done, rest.push c)
        else pure (order.push (c, ci), done.insert c, rest)
    if rest.size == pending.size then throw (cyclicCanonError rest)
    canonRounds addr? canon fuel rest order done

/-- Before a block compiles: for every member of a changed clique in the
block, and every equation lemma carried with one, its transported value in
the overlay with Lean's value as the decompile record, and the canonical
constants it references, in compile order. A block outside a transported
clique's unit that unfolds its encoding is refused (`cliqueCallers`; `refs`
are the block's references). The empty preparation when the clique table is
empty; only the plan statistics when no constant of the block is a
transported member or lemma. A clique's plan is taken from the plan table
when an earlier block computed it (`cliquePlanFor`); the plans computed here
are returned for the table (`CliquePrep.fresh`).

The block's names in the table are read in pretty-name order. The canonical
constants a member reaches are its value's canonical references, closed
under the canonical references of their types and values (`reachCanon`);
those not yet compiled (`HookEnv.addr?`) are ordered by `canonRounds` from
pretty-name order. -/
def prepareCliques (h : HookEnv) (all refs : Ix.Set Name) : Except String CliquePrep := do
  if h.table.isEmpty then return {}
  let (refusal?, fresh0, reused0) ← cliqueCallers h all refs
  if let some refusal := refusal? then throw refusal
  let const? := h.env.get?
  let mut overlay : Array (Name × ConstantInfo) := #[]
  let mut sources : Array (Nat × Expr) := #[]
  let mut canon : Std.HashMap Name ConstantInfo := {}
  let mut wanted : Array Name × Std.HashSet Name := (#[], {})
  let mut fresh := fresh0
  let mut reused := reused0
  let mut rows : Array (Name × Rows) := #[]
  let mut plans : Std.HashMap Name CliqueOutcome := fresh0.foldl (fun m (k, o) => m.insert k o) {}
  for n in sortByPretty (all.toArray.filter h.table.contains) do
    let some (cl, carried) := h.table.get? n | continue
    let some key := cl[0]? | continue
    let mut outcome : CliqueOutcome := default
    match plans.get? key with
    | some o => outcome := o
    | none =>
      let (o, hit, rows?) ← cliquePlanFor h cl carried
      if hit then reused := reused + 1 else fresh := fresh.push (key, o)
      if let some r := rows? then rows := rows.push (key, r)
      outcome := o
    plans := plans.insert key outcome
    let .transported plan := outcome | continue
    let some md := plan.members.get? n | continue
    let some ci := const? n | continue
    let some leanValue := valueOf? ci | continue
    let idx := cliqueRecordBase + overlay.size
    overlay := overlay.push (n, withValue ci (Expr.mkMData #[(inlineKey, .ofNat idx)] md.value))
    sources := sources.push (idx, leanValue)
    -- the canonical constants, and the ones this constant reaches
    let canonNames : Std.HashSet Name := plan.canon.foldl (fun s (d, _) => s.insert d.name) {}
    for (d, src) in plan.canon do
      if !canon.contains d.name then
        let record? := if plan.functionals.contains d.name then some plan.record else none
        canon := canon.insert d.name (canonConst const? d src record?)
    wanted := reachCanon canon canonNames canonNames.size
      (pushStack [] (constOccurrences canonNames.contains md.value)) wanted
  if overlay.isEmpty then return { fresh, reused, rows }
  let pending := sortByPretty (wanted.1.filter fun c => (h.addr? c).isNone)
  let order ← canonRounds h.addr? canon (pending.size + 1) pending #[] {}
  return { overlay, sources, canon := order, fresh, reused, rows }

end Ix.Compile.Pass.Clique

end
