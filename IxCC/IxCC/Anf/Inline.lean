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

/-- The round as a map from caller to callees, the first entry for a caller
winning (as `List.lookup` would). Built once per round, so each global's
lookup costs a walk down the bits of its id, not a scan of the round. -/
def calleeMap (r : Round) : Src.NatMap (List GlobalId) := Src.NatMap.ofList r.reverse

/-- One round. Each listed caller's walk is bounded by `Walk.maxCopy` and
`Walk.maxWalkWork`, and the round stops as soon as the globals it has made pass
`maxProgramNodes` or its walks' work passes `maxStepWork`, so it never holds or
does much more than the budgets (`mapMWithin`). -/
def round (P : Program) (r : Round) : Except String (Program × Walk.Fires) := do
  let m := calleeMap r
  let rs ← mapMWithin (fun (g, gd) => do
      match m.get? g with
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

/-- Globals on a cycle of the reference graph: those with a reference to
themselves, and those in a strongly connected component of more than one
global (Tarjan's algorithm, with explicit stacks), in time linear in the
globals and their references. -/
def recursive (P : Program) : Std.HashSet GlobalId := Id.run do
  let edges : Src.NatMap (Array GlobalId) :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) => (g, gd.body.refs.toArray))
  let steps := P.globalList.foldl (fun n (_, gd) => n + 2 * gd.body.refs.length + 2) 1
  let mut index : Src.NatMap Nat := .leaf
  let mut low : Src.NatMap Nat := .leaf
  let mut onStack : Std.HashSet GlobalId := {}
  let mut stack : Array GlobalId := #[]
  let mut out : Std.HashSet GlobalId := {}
  let mut next := 0
  for (root, _) in P.globalList do
    if index.contains root then continue
    index := index.insert root next
    low := low.insert root next
    next := next + 1
    stack := stack.push root
    onStack := onStack.insert root
    -- each frame: a global and how many of its references it has followed
    let mut frames : Array (GlobalId × Nat) := #[(root, 0)]
    for _ in [0:steps] do
      match frames.back? with
      | none => break
      | some (v, i) =>
        let es := edges.getD v #[]
        if h : i < es.size then
          frames := frames.set! (frames.size - 1) (v, i + 1)
          let w := es[i]
          if w == v then out := out.insert v
          match index.get? w with
          | none =>
            index := index.insert w next
            low := low.insert w next
            next := next + 1
            stack := stack.push w
            onStack := onStack.insert w
            frames := frames.push (w, 0)
          | some iw =>
            if onStack.contains w then low := low.insert v (min (low.getD v 0) iw)
        else
          frames := frames.pop
          let lv := low.getD v 0
          if lv == index.getD v 0 then
            -- `v` roots a component: the stack down to `v`
            let mut comp : Array GlobalId := #[]
            for _ in [0:stack.size] do
              match stack.back? with
              | none => break
              | some x =>
                stack := stack.pop
                onStack := onStack.erase x
                comp := comp.push x
                if x == v then break
            if comp.size > 1 then
              for x in comp do out := out.insert x
          if let some (u, _) := frames.back? then low := low.insert u (min (low.getD u 0) lv)
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
it references, first reference first, at most `maxCertCallees` of them
(none if nothing remains). Whether a global is inlinable is decided once
per global, and each caller's sites are a set. -/
def produce (B : Budgets) (P : Program) : Round :=
  let recs := recursive P
  let inl : Src.NatMap Bool :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) => (g, inlinable B recs gd g))
  P.globalList.filterMap fun (f, gd) =>
    let sites : Std.HashSet GlobalId := gd.body.sites.foldl (·.insert ·) {}
    -- the references without repetition, in first-reference order
    let refs := (gd.body.refs.foldl (init := (({} : Std.HashSet GlobalId), ([] : List GlobalId)))
      fun (seen, acc) g => if seen.contains g then (seen, acc) else (seen.insert g, g :: acc)).2.reverse
    let cs := refs.filter fun g =>
      g != f && (match P.global? g with
        | some gd' =>
          -- a function `glob` is a closure, not a site: only calls and CAFs
          inl.getD g false && (gd'.ps.isEmpty || sites.contains g)
        | none => false)
    -- at most the callees a certificate may list per caller (`checkCert`)
    if cs.isEmpty then none else some (f, cs.take maxCertCallees)

end IxCC.Anf.Inline
