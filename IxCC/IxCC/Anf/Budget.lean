import IxCC.Anf.Syntax

/-! # Node budgets for the middle end's replay

A middle-end certificate decides which callees the walk inlines, how many
shrink rounds run and which call sites are specialised, and on the byte-level
verifiers the claimant also chooses the program. One certified step can
therefore ask for work, memory and native recursion far beyond its input's
size: a single `inline` step copied a callee into each of thousands of call
sites, and the walk's continuation-passing recursion over the copies
overflowed the checker's stack (REPORT item 2). The replay bounds every step
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

/-- Nodes one global may hold after P1 and after every middle-end step:
six times the largest global a committed program reaches at any stage
(2,507). The walks recurse natively once per binding they walk, through the
global and the copies they make (`Walk.maxCopy`); on an 8 MiB stack one walk
survives about 18,800 bindings (37,600 nodes) and overflows at 19,100, so this
and `Walk.maxCopy` together keep a walk to 12,288 bindings. Every later level
(Fir to x86) has been run on 37,000-node globals on an 8 MiB stack. -/
def maxGlobalNodes : Nat := 16384

/-- Nodes the whole program may hold after P1 and after every middle-end step:
two hundred times the largest committed program (4,935). -/
def maxProgramNodes : Nat := 1048576

/-- The work one inline or shrink step may do over all its walks (each walk's
work, charged step by step, is also bounded by `Walk.maxWalkWork`): seventeen
times the most a committed program's step does (2,642,755). -/
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
32,767-node Lam global and overflows on a 65,535-node one. Seven times the
largest committed Lam global (2,256). -/
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
