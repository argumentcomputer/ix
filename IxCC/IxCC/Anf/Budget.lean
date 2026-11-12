import IxCC.Anf.Syntax

/-! # Node budgets for the middle end's replay

A middle-end certificate decides which callees the walk inlines, how many
shrink rounds run and which call sites are specialised, and on the byte-level
verifiers the claimant also chooses the program. One certified step can
therefore ask for work, memory and native recursion far beyond its input's
size: a single `inline` step copied a callee into each of thousands of call
sites, and the walk's continuation-passing recursion over the copies
overflowed the checker's stack. The replay bounds every step
by fixed node budgets and refuses it, with an ordinary error, before it
exceeds them:

* `maxGlobalNodes` bounds every global and `maxProgramNodes` the whole
  program, after P1 and after every step (`Pipeline.checkGlobalNodes`), and
  during the inline and shrink steps' passes over the globals (`mapMWithin`);
* `Walk.maxCopy` bounds the nodes one walk re-walks (`Walk.fire`): inlined callees,
  β-reduced local functions, inlined join points and case-of-case
  alternatives; with `maxGlobalNodes` it bounds the walk's native depth;
* `Walk.maxWalkWork` bounds one walk's work and `maxStepWork` an inline or
  shrink step's (`Fires.work`, charged at every step of the walk with what
  it reads: the environment entries it looks up and, under shrink, the census
  of the rest of the body, which is quadratic in the global);
* `maxLamNodes` bounds every Lam global before P1 (`Pipeline.checkLamNodes`),
  whose native recursion grows with the bindings it emits;
* `Specialize.maxWork` and `Specialize.maxNodes` bound the work of a
  specialisation step's call sites and the nodes of what it builds.

Counting is itself bounded: `Exp.nodesUpTo cap e` stops once the count passes
`cap` and walks an explicit worklist, so neither its work nor its native stack
grows with `e` (`Exp.nodes` is fully recursive). `tests-corpus` replays every
committed fixture and corpus program against these budgets and fails if one
reaches them; the measured maxima and their headroom are in
`docs/compiler-design.md`, "Middle-end budgets".

On success each bounded function is the unbounded one (`mapMWithin_mapM`), so
the passes' correctness theorems are unchanged: a budget only adds refusals. -/

namespace IxCC.Anf

/-- Nodes one global may hold after P1 and after every middle-end step. The
walks recurse natively once per binding they walk, through the global and the
copies they make (`Walk.maxCopy`); on an 8 MiB stack one walk survives about
18,800 bindings (37,600 nodes) and overflows at 19,100, so this and
`Walk.maxCopy` together keep a walk to 12,288 bindings. Every later level (Fir
to x86) has been run on 37,000-node globals on an 8 MiB stack. The largest
global a committed program reaches, and so the headroom, is measured by
`tests-corpus`'s budget survey (`docs/compiler-design.md`, "Middle-end
budgets"), as for every budget of this module. -/
def maxGlobalNodes : Nat := 16384

/-- Nodes the whole program may hold after P1 and after every middle-end step
(the largest committed program: `tests-corpus`'s budget survey). -/
def maxProgramNodes : Nat := 1048576

/-- The work one inline or shrink step may do over all its walks (each walk's
work, charged step by step, is also bounded by `Walk.maxWalkWork`; the most a
committed program's step does: `tests-corpus`'s budget survey). -/
def maxStepWork : Nat := 45000000

/-- `acc` plus the nodes of the expressions in `todo`, stopping as soon as the
count passes `cap`. Each step counts at least one node, so `cap + 2` steps of
fuel always suffice; the recursion is a tail call over the worklist. -/
def Exp.countUpTo (cap : Nat) : Nat → List Exp → Nat → Nat
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, e :: todo, acc =>
    if acc > cap then acc
    else
      match e with
      | .bind _ b body =>
        match b with
        | .fn _ fb => Exp.countUpTo cap fuel (fb :: body :: todo) (acc + 2)
        | .con _ as | .prim _ as | .call _ as | .app _ as =>
          Exp.countUpTo cap fuel (body :: todo) (acc + as.length + 2)
        | .atom _ | .glob _ | .proj .. => Exp.countUpTo cap fuel (body :: todo) (acc + 2)
      | .join _ _ b body => Exp.countUpTo cap fuel (b :: body :: todo) (acc + 1)
      | .jump _ as => Exp.countUpTo cap fuel todo (acc + as.length + 1)
      | .case _ alts d => Exp.countUpTo cap fuel (alts.map Alt.body ++ d.toList ++ todo) (acc + 1)
      | .ret _ | .trap => Exp.countUpTo cap fuel todo (acc + 1)
      | .tick body => Exp.countUpTo cap fuel (body :: todo) (acc + 1)

/-- `min e.nodes (cap + 1)`, without walking more than `cap + 1` nodes of `e`. -/
def Exp.nodesUpTo (cap : Nat) (e : Exp) : Nat :=
  min (Exp.countUpTo cap (cap + 2) [e] 0) (cap + 1)

/-- `e.nodes ≤ cap`, walking at most `cap + 1` of `e`'s nodes. -/
def Exp.nodesLe (e : Exp) (cap : Nat) : Bool := e.nodesUpTo cap ≤ cap

/-- Nodes one Lam global may hold when it reaches ANF conversion (P1).
Conversion recurses natively once per binding it emits, and a Lam term's
nodes, unlike its depth, are not bounded by ingress (a `share` DAG expands), so
this bounds the conversion's native stack: on an 8 MiB stack it converts a
32,767-node Lam global and overflows on a 65,535-node one (the largest
committed Lam global: `tests-corpus`'s budget survey). -/
def maxLamNodes : Nat := 16384

/-- `acc` plus the nodes of the Lam terms in `todo`, stopping as soon as the
count passes `cap` (a tail call over the worklist, as `Exp.countUpTo`). -/
def lamCountUpTo (cap : Nat) : Nat → List Lam.Term → Nat → Nat
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, t :: todo, acc =>
    if acc > cap then acc
    else
      match t with
      | .var _ | .glob _ | .lit _ | .box | .trap => lamCountUpTo cap fuel todo (acc + 1)
      | .lam _ _ b | .tick b | .proj _ _ b => lamCountUpTo cap fuel (b :: todo) (acc + 1)
      | .app f a _ | .letE _ f a => lamCountUpTo cap fuel (f :: a :: todo) (acc + 1)
      | .con _ fs | .prim _ fs => lamCountUpTo cap fuel (fs ++ todo) (acc + 1)
      | .case s alts d =>
        lamCountUpTo cap fuel (s :: (alts.map fun | .mk _ _ b => b) ++ d.toList ++ todo) (acc + 1)

/-- `min t.nodes (cap + 1)`, without walking more than `cap + 1` of `t`'s nodes. -/
def lamNodesUpTo (cap : Nat) (t : Lam.Term) : Nat :=
  min (lamCountUpTo cap (cap + 2) [t] 0) (cap + 1)


/-! ## Nesting depth

Every recursive traversal after erasure (P1, the walks, Fir to the stacked
x86 program) recurses natively once per level of nesting, whatever the
constructor, so the stack a term needs grows with its depth. The checks below
count depth over an explicit worklist (a tail call, safe on any depth) and run
after erasure (`maxLamDepth`), after P1 and after every middle-end step and
shrink round (`maxDepth`); and a walk counts its own steps on the stack
(`Here.lvl`, `Walk.maxWalkDepth`), since a copy's frames stay below the rest of
the caller, which its continuation walks. -/

/-- The deepest level in `todo` (each expression paired with its level), at
least `acc`, stopping once it passes `cap`; `cap + 1` if the fuel runs out
first. Every nesting former counts one level: a binding (its body, and a local
function's body), a join point (its body and its scope), a `case` (each
alternative and the default) and a `tick`. -/
def Exp.depthGo (cap : Nat) : Nat → List (Exp × Nat) → Nat → Nat
  | 0, _, _ => cap + 1
  | _, [], acc => acc
  | fuel + 1, (e, d) :: todo, acc =>
    if acc > cap then acc
    else
      match e with
      | .bind _ b body =>
        match b with
        | .fn _ fb => Exp.depthGo cap fuel ((fb, d + 1) :: (body, d + 1) :: todo) (max acc d)
        | _ => Exp.depthGo cap fuel ((body, d + 1) :: todo) (max acc d)
      | .join _ _ b body => Exp.depthGo cap fuel ((b, d + 1) :: (body, d + 1) :: todo) (max acc d)
      | .case _ alts dflt =>
        Exp.depthGo cap fuel ((alts.map fun a => (a.body, d + 1)) ++ (dflt.toList.map (·, d + 1)) ++ todo)
          (max acc d)
      | .tick body => Exp.depthGo cap fuel ((body, d + 1) :: todo) (max acc d)
      | .jump .. | .ret _ | .trap => Exp.depthGo cap fuel todo (max acc d)

/-- `min (depth e) (cap + 1)`, visiting at most `nodes + 1` nodes (`cap + 1` if
`e` has more: callers pass a bound its nodes have already been checked
against). -/
def Exp.depthUpTo (cap nodes : Nat) (e : Exp) : Nat :=
  min (Exp.depthGo cap (nodes + 1) [(e, 1)] 0) (cap + 1)

/-- Nesting depth one Anf global may reach after P1, after every middle-end
step and after every shrink round. The traversals after P1 overflow an 8 MiB
stack no shallower than a walk over nested single-alternative `case`s (about
12,290 steps; Fir to x86 survive 16,383 levels), and a walk starts at most this
deep, below its own budget (`Walk.maxWalkDepth`, a quarter of that). The
deepest committed global is 752 deep, so the headroom over honest programs is
2.7×, which is what four times below the 8 MiB threshold leaves room for; see
`docs/compiler-design.md`, "Middle-end budgets". -/
def maxDepth : Nat := 2048

/-- The deepest level of the Lam terms in `todo`, as `Exp.depthGo`. -/
def lamDepthGo (cap : Nat) : Nat → List (Lam.Term × Nat) → Nat → Nat
  | 0, _, _ => cap + 1
  | _, [], acc => acc
  | fuel + 1, (t, d) :: todo, acc =>
    if acc > cap then acc
    else
      match t with
      | .var _ | .glob _ | .lit _ | .box | .trap => lamDepthGo cap fuel todo (max acc d)
      | .lam _ _ b | .tick b | .proj _ _ b => lamDepthGo cap fuel ((b, d + 1) :: todo) (max acc d)
      | .app f a _ | .letE _ f a => lamDepthGo cap fuel ((f, d + 1) :: (a, d + 1) :: todo) (max acc d)
      | .con _ fs | .prim _ fs => lamDepthGo cap fuel ((fs.map (·, d + 1)) ++ todo) (max acc d)
      | .case s alts dflt =>
        lamDepthGo cap fuel ((s, d + 1) :: (alts.map fun | .mk _ _ b => (b, d + 1)) ++
          (dflt.toList.map (·, d + 1)) ++ todo) (max acc d)

/-- `min (depth t) (cap + 1)`, visiting at most `nodes + 1` nodes. -/
def lamDepthUpTo (cap nodes : Nat) (t : Lam.Term) : Nat :=
  min (lamDepthGo cap (nodes + 1) [(t, 1)] 0) (cap + 1)

/-- Nesting depth one Lam global may reach when it leaves erasure: fifteen times
the deepest committed Lam global (134), and four times below the shallowest
depth at which P1 overflows an 8 MiB stack (a chain of applications in
argument position, 9,451; `docs/compiler-design.md`, "Middle-end budgets"). -/
def maxLamDepth : Nat := 2048

/-! ## The back end's work -/

/-- `acc` plus the squares of the alternative counts of the `case`s in `todo`,
visiting at most `fuel` nodes (a tail call over the worklist). -/
def Exp.caseWorkGo : Nat → List Exp → Nat → Nat
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, e :: todo, acc =>
    match e with
    | .bind _ b body =>
      match b with
      | .fn _ fb => Exp.caseWorkGo fuel (fb :: body :: todo) acc
      | _ => Exp.caseWorkGo fuel (body :: todo) acc
    | .join _ _ b body => Exp.caseWorkGo fuel (b :: body :: todo) acc
    | .case _ alts d =>
      Exp.caseWorkGo fuel (alts.map Alt.body ++ d.toList ++ todo) (acc + alts.length * alts.length)
    | .tick body => Exp.caseWorkGo fuel (body :: todo) acc
    | .jump .. | .ret _ | .trap => Exp.caseWorkGo fuel todo acc

/-- The back end's cost of a program: over its globals, their nodes squared,
plus their nodes and the squares of their `case`s' alternative counts times
the constructor table's length. From Fir to x86 the verifier's levels are
linear in a function's nodes except for a few that are quadratic in its blocks
or its nesting (`Cfg.lower`'s block counts, `Lir.Func.splitCriticalEdges`'
predecessor counts, `X86.Layout.tunnel`'s chains; a function has at most as
many blocks, and is at most as deep, as its global has nodes), and a
constructor's key is looked up by a search of the table
(`Fir.CtorInfo.ofKey`), once per use and, by `Rt.checkSwitches`, once per
pair of a switch's alternatives. -/
def backWork (P : Program) : Nat :=
  P.globalList.foldl (fun acc (_, gd) =>
    let n := gd.body.nodesUpTo maxGlobalNodes
    acc + n * n + (n + Exp.caseWorkGo (n + 1) [gd.body] 0) * (P.ctors.length + 1)) 0

/-- `backWork` a program may reach after P1 and after every middle-end step:
enough for one global at `maxGlobalNodes` (the most a committed program
reaches: `tests-corpus`'s budget survey). See
`docs/compiler-design.md`, "Middle-end budgets", for the back end's time at
it. -/
def maxBackWork : Nat := 1 <<< 28
/-- `xs.mapM f`, refusing with `msg` as soon as `used` plus the sizes of the
results so far passes `budget` in either of two measures (nodes made and work
done, say), so a pass stops before it does or allocates much past its budget. -/
def mapMWithin {α β : Type} (f : α → Except String β) (size : β → Nat × Nat)
    (budget : Nat × Nat) (msg : String) : Nat × Nat → List α → Except String (List β)
  | _, [] => .ok []
  | used, x :: xs =>
    match f x with
    | .error e => .error e
    | .ok y =>
      if used.1 + (size y).1 > budget.1 || used.2 + (size y).2 > budget.2 then .error msg
      else
        match mapMWithin f size budget msg (used.1 + (size y).1, used.2 + (size y).2) xs with
        | .error e => .error e
        | .ok ys => .ok (y :: ys)

/-- On success, `mapMWithin` is `mapM`. -/
theorem mapMWithin_mapM {α β : Type} {f : α → Except String β} {size : β → Nat × Nat}
    {budget : Nat × Nat} {msg : String} : ∀ (used : Nat × Nat) (xs : List α) (ys : List β),
    mapMWithin f size budget msg used xs = .ok ys → xs.mapM f = .ok ys
  | _, [], ys, h => by
    simp only [mapMWithin, Except.ok.injEq] at h
    subst h
    rfl
  | used, x :: xs, ys, h => by
    simp only [mapMWithin] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      simp only at h
      split at h
      · cases h
      · cases hr : mapMWithin f size budget msg (used.1 + (size y).1, used.2 + (size y).2) xs with
        | error e => rw [hr] at h; cases h
        | ok ys' =>
          rw [hr] at h
          simp only [Except.ok.injEq] at h
          subst h
          simp only [List.mapM_cons, hx, mapMWithin_mapM _ xs ys' hr, bind, Except.bind, pure,
            Except.pure]

end IxCC.Anf
