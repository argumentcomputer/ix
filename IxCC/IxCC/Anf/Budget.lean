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
  alternatives;
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
twenty-six times the largest global a committed program reaches at any stage
(2,507). -/
def maxGlobalNodes : Nat := 65536

/-- Nodes the whole program may hold after P1 and after every middle-end step:
two hundred times the largest committed program (4,935). -/
def maxProgramNodes : Nat := 1048576

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

/-- `xs.mapM f`, refusing with `msg` as soon as `used` plus the sizes of the
results so far passes `budget`, so a pass that grows a program stops before it
allocates much past its budget. -/
def mapMWithin {α β : Type} (f : α → Except String β) (size : β → Nat) (budget : Nat)
    (msg : String) : Nat → List α → Except String (List β)
  | _, [] => .ok []
  | used, x :: xs =>
    match f x with
    | .error e => .error e
    | .ok y =>
      if used + size y > budget then .error msg
      else
        match mapMWithin f size budget msg (used + size y) xs with
        | .error e => .error e
        | .ok ys => .ok (y :: ys)

/-- On success, `mapMWithin` is `mapM`. -/
theorem mapMWithin_mapM {α β : Type} {f : α → Except String β} {size : β → Nat} {budget : Nat}
    {msg : String} : ∀ (used : Nat) (xs : List α) (ys : List β),
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
      · cases hr : mapMWithin f size budget msg (used + size y) xs with
        | error e => rw [hr] at h; cases h
        | ok ys' =>
          rw [hr] at h
          simp only [Except.ok.injEq] at h
          subst h
          simp only [List.mapM_cons, hx, mapMWithin_mapM _ xs ys' hr, bind, Except.bind, pure,
            Except.pure]

end IxCC.Anf
