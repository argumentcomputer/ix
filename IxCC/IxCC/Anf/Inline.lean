import IxCC.Anf.Walk

/-! # P3: inlining

`Anf.Inline` (design note 02 §8, P3), parametric in an oracle: a **round**
lists, per caller, the callees whose `call`s and CAF `glob`s it inlines.
`call g as` becomes `tick` and `g`'s body with its parameters bound to `as`
(its `ret` continues with the caller, through a join point when the body
branches); a CAF `glob g` becomes `tick` and `g`'s body (instance
dictionaries). Every global of a round is rewritten against the program at
the start of the round, and an inlined body's own sites wait for a later
round, so a round terminates and the pass is correct for **every** oracle
(a listed callee that is not called is ignored).

**Certificate** (D17): the rounds. The default oracle (`produce`), after
Lean's (02 §7.4: instances, matchers, lazy and wrapper globals, small
bodies), inlines every call of a callee that is not recursive (not on a
cycle of the call graph) and is a CAF, a by-name variant or a wrapper, or
has at most `Budgets.size` nodes. Recursive globals are never inlined by the
default oracle (Lean's `maxRecInline` applies only to `@[inline]` recursive
definitions, which the Phase 1 fixtures do not tag). -/

namespace IxCC.Anf.Inline

/-- Per caller, the callees it inlines. -/
abbrev Round := List (GlobalId × List GlobalId)

abbrev Cert := List Round

/-- One round. -/
def round (P : Program) (r : Round) : Except String (Program × Walk.Fires) := do
  let rs ← P.globalList.mapM fun (g, gd) => do
    match r.lookup g with
    | some cs@(_ :: _) =>
      let (gd', f) ← ((Walk.global { prog := P, inline := cs } gd).run {}).mapError
        (s!"inline global {g}: " ++ ·)
      return (g, gd', f)
    | _ => return (g, gd, ({} : Walk.Fires))
  return ({ P with globals := Src.NatMap.ofList (rs.map fun (g, gd, _) => (g, gd)) },
    rs.foldl (fun acc (_, _, f) => acc.add f) {})

/-- P3 re-run on its certificate. -/
def run (cert : Cert) (P : Program) : Except String Program :=
  cert.foldlM (fun P r => (round P r).map (·.1)) P

/-! ## The default oracle (`produce`; not on the recheck path) -/

structure Budgets where
  /-- Non-recursive callees of at most this many nodes are inlined. -/
  size : Nat := 128
  /-- Inline rounds per invocation (each followed by a shrink). -/
  rounds : Nat := 8
  deriving Repr, Inhabited

/-- The globals reachable from `g` in one or more steps. -/
def reachable (edges : Src.NatMap (List GlobalId)) (size g : Nat) : List GlobalId := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := edges.getD g []
  let mut out := #[]
  for _ in [0:size * size + size + 1] do
    match todo with
    | [] => break
    | h :: rest =>
      todo := rest
      if seen.contains h then continue
      seen := seen.insert h
      out := out.push h
      todo := edges.getD h [] ++ todo
  return out.toList

/-- Globals on a cycle of the reference graph. -/
def recursive (P : Program) : Std.HashSet GlobalId := Id.run do
  let edges : Src.NatMap (List GlobalId) :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) => (g, gd.body.refs.eraseDups))
  let mut out : Std.HashSet GlobalId := {}
  for (g, _) in P.globalList do
    if (reachable edges P.size g).contains g then out := out.insert g
  return out

/-- Whether the default oracle inlines `g`. -/
def inlinable (B : Budgets) (recs : Std.HashSet GlobalId) (gd : GDef) (g : GlobalId) : Bool :=
  !recs.contains g &&
  (gd.ps.isEmpty || gd.body.nodes ≤ B.size ||
    (match gd.key with
     | .byName .. | .wrapper .. => true
     | _ => false))

/-- The default oracle's next round: for each caller, the inlinable callees
it references (none if nothing remains). -/
def produce (B : Budgets) (P : Program) : Round :=
  let recs := recursive P
  P.globalList.filterMap fun (f, gd) =>
    let sites := gd.body.sites
    let cs := gd.body.refs.eraseDups.filter fun g =>
      g != f && (match P.global? g with
        | some gd' =>
          -- a function `glob` is a closure, not a site: only calls and CAFs
          inlinable B recs gd' g && (gd'.ps.isEmpty || sites.contains g)
        | none => false)
    if cs.isEmpty then none else some (f, cs)

end IxCC.Anf.Inline
