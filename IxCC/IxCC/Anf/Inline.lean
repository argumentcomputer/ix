import IxCC.Anf.Walk

/-! # P3: inlining

`Anf.Inline` (P3), parametric in an oracle: a **round**
lists, per caller, the callees whose `call`s and CAF `glob`s it inlines.
`call g as` becomes `tick` and `g`'s body with its parameters bound to `as`
(its `ret` continues with the caller, through a join point when the body
branches); a CAF `glob g` becomes `tick` and `g`'s body (instance
dictionaries). Every global of a round is rewritten against the program at
the start of the round, and an inlined body's own sites wait for a later
round, so a round terminates and the pass is correct for **every** oracle
(a listed callee that is not called is ignored).

**Certificate** (D17): the rounds. The default oracle (`produce`), after
Lean's (instances, matchers, lazy and wrapper globals, small
bodies), inlines every call of a callee that is not recursive (not on a
cycle of the call graph) and is a CAF, a by-name variant or a wrapper, or
has at most `Budgets.size` nodes. Recursive globals are never inlined by the
default oracle (Lean's `maxRecInline` applies only to `@[inline]` recursive
definitions, which the Phase 1 fixtures do not tag). -/

namespace IxCC.Anf.Inline

/-- Per caller, the callees it inlines. -/
abbrev Round := List (GlobalId × List GlobalId)

abbrev Cert := List Round

/-- Maximum caller entries in an inline round certificate. -/
def maxCertGlobals : Nat := 100000

/-- Maximum callees per caller in an inline round certificate. -/
def maxCertCallees : Nat := 64

/-- Check that an inline round certificate is within bounds and free of self-inlining. -/
def checkCert (r : Round) : Bool :=
  r.length ≤ maxCertGlobals &&
  r.all fun (caller, callees) =>
    callees.length ≤ maxCertCallees && callees.all (· != caller)

/-- One round. Each listed caller's walk is bounded by `Walk.maxCopy` and
`Walk.maxWalkWork`, and the round stops as soon as the globals it has made pass
`maxProgramNodes` or its walks' work passes `maxStepWork`, so it never holds or
does much more than the budgets (`mapMWithin`). -/
def round (P : Program) (r : Round) : Except String (Program × Walk.Fires) := do
  let rs ← mapMWithin (fun (g, gd) => do
      match r.lookup g with
      | some cs@(_ :: _) =>
        let (gd', f) ← ((Walk.global { prog := P, inline := cs } gd).run {}).mapError
          (s!"inline global {g}: " ++ ·)
        return (g, gd', f)
      | _ => return (g, gd, ({} : Walk.Fires)))
    (fun x => (x.2.1.body.nodesUpTo maxProgramNodes, x.2.2.work)) (maxProgramNodes, maxStepWork)
    "inline: the program exceeds the node or work budget" (0, 0) P.globalList
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

mutual

/-- Whether `e` contains a local `.fn` or higher-order `.app`. -/
def hasFnOrApp : Exp → Bool
  | .bind _ b e => bindHasFnOrApp b || hasFnOrApp e
  | .join _ _ b e => hasFnOrApp b || hasFnOrApp e
  | .case _ alts d => altsHasFnOrApp alts || optHasFnOrApp d
  | .tick e => hasFnOrApp e
  | .jump .. | .ret _ | .trap => false

def bindHasFnOrApp : Bind → Bool
  | .fn .. | .app .. => true
  | _ => false

def altsHasFnOrApp : List Alt → Bool
  | [] => false
  | .mk _ _ b :: as => hasFnOrApp b || altsHasFnOrApp as

def optHasFnOrApp : Option Exp → Bool
  | none => false
  | some e => hasFnOrApp e

end

/-- Whether the default oracle inlines `g`. -/
def inlinable (B : Budgets) (recs : Std.HashSet GlobalId) (gd : GDef) (g : GlobalId) : Bool :=
  !recs.contains g &&
  (gd.ps.isEmpty || gd.body.nodes ≤ B.size || hasFnOrApp gd.body ||
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
