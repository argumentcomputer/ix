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
  /-- Global keys withheld from inlining (e.g. DR3 pinned native `Array`/`ByteArray` ops). -/
  noInline : List Key.GKey := []
  /-- Originating `Src.CId`s withheld from cross-origin inlining (e.g. definitions carrying
  non-default Ixon v5 `DefAsserts`). -/
  noInlineOrigins : Src.NatSet := .leaf
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

/-- Peel `.worker` wrappers to recover the base key for `noInline` matching. -/
def baseInlineKey : Key.GKey → Key.GKey
  | .worker k _ => baseInlineKey k
  | k => k

/-- Whether `k` (or its unwrapped `.worker` origin) is listed in `noInline`. -/
def isNoInlineKey (noInline : List Key.GKey) (k : Key.GKey) : Bool :=
  noInline.contains k || noInline.contains (baseInlineKey k)

/-- Originating `Src.CId` of a global key (matching `Recheck.DefAsserts.gkeyOrigin?`). -/
def keyOrigin? : Key.GKey → Option Src.CId
  | .const c _ => some c
  | .byName c _ => some c
  | .recStar r _ => some r
  | .wrapper (.ctor c) _ | .wrapper (.quotMk c) _ | .wrapper (.quotLift c) _
  | .wrapper (.recr c) _ | .wrapper (.cases c) _ => some c
  | .wrapper _ _ => none
  | .spec g _ => keyOrigin? g
  | .worker g _ => keyOrigin? g
  | .lam g _ => keyOrigin? g
  | .dispatch _ => none
  | .entry g _ => keyOrigin? g

/-- Whether `k`'s originating `Src.CId` is in `origins`. -/
def isNoInlineOrigin (origins : Src.NatSet) (k : Key.GKey) : Bool :=
  match keyOrigin? k with
  | some c => origins.contains c
  | none => false

/-- Whether `callerKey` may inline `calleeKey` under `B`: never inlines keys listed in
`B.noInline`, and never inlines a callee whose originating constant is in `B.noInlineOrigins`
into a caller from a different originating constant. -/
def inlineAllowedFor (B : Budgets) (callerKey calleeKey : Key.GKey) : Bool :=
  !isNoInlineKey B.noInline calleeKey &&
  (!isNoInlineOrigin B.noInlineOrigins calleeKey || keyOrigin? callerKey == keyOrigin? calleeKey)

/-- Expand `B.noInline` with every global key in `P` whose originating constant is in
`B.noInlineOrigins` (for post-P8 helpers taking `noInline : List Key.GKey`). -/
def expandNoInline (B : Budgets) (P : Program) : List Key.GKey :=
  if B.noInlineOrigins.toList.isEmpty then B.noInline
  else
    B.noInline ++ P.globalList.filterMap fun (_, gd) =>
      if isNoInlineOrigin B.noInlineOrigins gd.key then some gd.key else none

/-- Whether the default oracle inlines `g`. -/
def inlinable (B : Budgets) (recs : Std.HashSet GlobalId) (gd : GDef) (g : GlobalId) : Bool :=
  !isNoInlineKey B.noInline gd.key &&
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
          inl.getD g false && inlineAllowedFor B gd.key gd'.key &&
            (gd'.ps.isEmpty || sites.contains g)
        | none => false)
    -- at most the callees a certificate may list per caller (`checkCert`)
    if cs.isEmpty then none else some (f, cs.take maxCertCallees)

/-! ## Post-P8 oracle (pure `NatMap`/`NatSet`, ignores outgoing edges from dispatchers) -/

private structure TarjanSt where
  index : Src.NatMap Nat := .leaf
  low : Src.NatMap Nat := .leaf
  onStack : Src.NatSet := .leaf
  stack : List GlobalId := []
  out : Src.NatSet := .leaf
  next : Nat := 0

private def popComp (v : GlobalId) :
    List GlobalId → Src.NatSet → List GlobalId → List GlobalId × Src.NatSet × List GlobalId
  | [], onS, acc => (acc, onS, [])
  | x :: xs, onS, acc =>
    let onS' := onS.erase x
    let acc' := x :: acc
    if x == v then (acc', onS', xs) else popComp v xs onS' acc'

private def tarjanLoop (edges : Src.NatMap (List GlobalId)) :
    Nat → List (GlobalId × List GlobalId) → TarjanSt → TarjanSt
  | 0, _, st => st
  | _, [], st => st
  | fuel + 1, (v, w :: ws) :: rest, st =>
    let st := if w == v then { st with out := st.out.insert v } else st
    match st.index.get? w with
    | none =>
      let iw := st.next
      let st' : TarjanSt :=
        { st with
          index := st.index.insert w iw
          low := st.low.insert w iw
          onStack := st.onStack.insert w
          stack := w :: st.stack
          next := iw + 1 }
      tarjanLoop edges fuel ((w, edges.getD w []) :: (v, ws) :: rest) st'
    | some iw =>
      let st' :=
        if st.onStack.contains w then
          { st with low := st.low.insert v (min (st.low.getD v 0) iw) }
        else st
      tarjanLoop edges fuel ((v, ws) :: rest) st'
  | fuel + 1, (v, []) :: rest, st =>
    let lv := st.low.getD v 0
    let st' :=
      if lv == st.index.getD v 0 then
        let (comp, onS, stk) := popComp v st.stack st.onStack []
        let out' := if comp.length > 1 then comp.foldl (fun s x => s.insert x) st.out else st.out
        { st with onStack := onS, stack := stk, out := out' }
      else st
    let st'' :=
      match rest with
      | (u, _) :: _ => { st' with low := st'.low.insert u (min (st'.low.getD u 0) lv) }
      | [] => st'
    tarjanLoop edges fuel rest st''

/-- Globals on a direct cycle of the reference graph, ignoring outgoing edges
from `.dispatch _` globals (so post-P8 recursors like `Tree.rec` / `Expr.rec`
that only cycle through a mega-dispatcher are not blocked from inlining).
Pure `NatMap`/`NatSet` (zero `Quot.sound` or `Classical.choice`). -/
def directRecursive (P : Program) : Src.NatSet :=
  let edges : Src.NatMap (List GlobalId) :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) =>
      (g, if Walk.isDispatchKey gd.key then [] else gd.body.refs))
  let fuel := P.globalList.foldl (fun n (_, gd) => n + 2 * gd.body.refs.length + 2) 2
  let st := P.globalList.foldl (init := ({} : TarjanSt)) fun st (root, _) =>
    if st.index.contains root then st
    else
      let ir := st.next
      let st0 : TarjanSt :=
        { st with
          index := st.index.insert root ir
          low := st.low.insert root ir
          onStack := st.onStack.insert root
          stack := root :: st.stack
          next := ir + 1 }
      tarjanLoop edges fuel [(root, edges.getD root [])] st0
  st.out

/-- Whether the post-P8 oracle inlines `g`: never dispatchers, never directly
recursive globals; inlines CAFs, wrappers, by-name variants, and small bodies
(`≤ maxSize` nodes, including recursors and small lifted lambdas). -/
def inlinablePostP8 (maxSize : Nat) (recs : Src.NatSet) (gd : GDef) (g : GlobalId)
    (noInline : List Key.GKey := []) : Bool :=
  !isNoInlineKey noInline gd.key &&
  !Walk.isDispatchKey gd.key &&
  !recs.contains g &&
  (gd.ps.isEmpty || gd.body.nodesLe maxSize ||
    (match gd.key with
     | .byName .. | .wrapper .. => true
     | _ => false))

/-! ## The closure round (`produceClosureRound`; not on the recheck path) -/

/-- Whether a binding's value is a closure the program knows: a local function,
a function global's value, a copy of a variable holding one, or an application
of one (a partial application; a saturated application of a known function is
a `call` once shrunk). `env` says it per value variable in scope. -/
def bindIsClosure (P : Program) (env : List Bool) : Bind → Bool
  | .fn .. => true
  | .glob h => (P.arity? h).any (· > 0)
  | .atom (.var i) => env.getD i false
  | .app (.var i) _ => env.getD i false
  | _ => false

/-- Whether an operand is a variable holding a known closure (`bindIsClosure`). -/
def atomIsClosure (env : List Bool) : Atom → Bool
  | .var i => env.getD i false
  | _ => false

mutual

/-- The callees of the `call`s in `e` that pass a known closure
(`bindIsClosure`), with repetition, in order. Join and `case` parameters, and
a local function's parameters, hold no known closure. -/
def closureSites (P : Program) (env : List Bool) : Exp → List GlobalId
  | .bind _ b e => bindClosureSites P env b ++ closureSites P (bindIsClosure P env b :: env) e
  | .join n _ b e => closureSites P (List.replicate n false ++ env) b ++ closureSites P env e
  | .case _ alts d => altsClosureSites P env alts ++ optClosureSites P env d
  | .tick e => closureSites P env e
  | .jump .. | .ret _ | .trap => []
  termination_by structural e => e

def bindClosureSites (P : Program) (env : List Bool) : Bind → List GlobalId
  | .call g as => if as.any (atomIsClosure env) then [g] else []
  | .fn ps b => closureSites P (List.replicate ps.length false ++ env) b
  | _ => []
  termination_by structural b => b

def altsClosureSites (P : Program) (env : List Bool) : List Alt → List GlobalId
  | [] => []
  | .mk _ n b :: as =>
    closureSites P (List.replicate n false ++ env) b ++ altsClosureSites P env as
  termination_by structural as => as

def optClosureSites (P : Program) (env : List Bool) : Option Exp → List GlobalId
  | none => []
  | some e => closureSites P env e
  termination_by structural o => o

end

/-- The closure round: for each caller, the callees it passes a known closure
to (`closureSites`: a by-name thunk to a lazy combinator, an alternative to
a matcher, a method to a dictionary's consumer), first call first, at most
`maxCertCallees` of them; never a callee on a cycle of the reference graph
(`directRecursive`) or withheld by `noInline`. Inlining such a call puts the
closure's application into the caller, where the next shrink step reduces it
(β of a local function, the known call of a function global), so the round
removes closures at the cost of the callees' bodies only. The producer takes it
when the default oracle's round is refused (`Pipeline.produceOnce`). Pure:
`NatSet`s and structural recursion, no `HashSet`. -/
def produceClosureRound (B : Budgets) (P : Program) : Round :=
  let recs := directRecursive P
  P.globalList.filterMap fun (f, gd) =>
    let sites := closureSites P (List.replicate gd.ps.length false) gd.body
    let cs := (sites.foldl (init := ((.leaf : Src.NatSet), ([] : List GlobalId)))
      fun (seen, acc) g =>
        if seen.contains g then (seen, acc) else (Src.NatSet.insert seen g, g :: acc)).2.reverse
    let cs := cs.filter fun g =>
      g != f && !recs.contains g && (match P.global? g with
        | some gd' => inlineAllowedFor B gd.key gd'.key
        | none => false)
    if cs.isEmpty then none else some (f, cs.take maxCertCallees)

/-- Pure post-P8 inline oracle (skips `.dispatch _` globals as both callers and
callees, uses `directRecursive`, zero `HashSet`/`Quot.sound`). -/
def producePostP8 (maxSize : Nat := 128) (P : Program) (noInline : List Key.GKey := []) : Round :=
  let recs := directRecursive P
  let inl : Src.NatMap Bool :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) => (g, inlinablePostP8 maxSize recs gd g noInline))
  P.globalList.filterMap fun (f, gd) =>
    if Walk.isDispatchKey gd.key then none
    else
      let sites : Src.NatSet := gd.body.sites.foldl (fun s g => s.insert g) .leaf
      let refs := (gd.body.refs.foldl (init := ((.leaf : Src.NatSet), ([] : List GlobalId)))
        fun (seen, acc) g => if seen.contains g then (seen, acc) else (Src.NatSet.insert seen g, g :: acc)).2.reverse
      let cs := refs.filter fun g =>
        g != f && (match P.global? g with
          | some gd' => inl.getD g false && (gd'.ps.isEmpty || sites.contains g)
          | none => false)
      if cs.isEmpty then none else some (f, cs.take maxCertCallees)

end IxCC.Anf.Inline
