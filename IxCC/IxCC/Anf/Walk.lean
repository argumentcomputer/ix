import IxCC.Anf.Opd
import IxCC.Anf.Census
import IxCC.Anf.Budget

/-! # The rewriting walk

One traversal shared by shrink (P2), inlining (P3) and the specialiser's
body copies (P4), designed as a sequence of local rewrites applied
while copying a source term into a target term:

* The walk carries an **environment** mapping source value variables to
  target operands (levels, literals, □) or to a local function it inlines at
  its single application, and source join points to target join levels or to
  a join body it inlines at its single jump. Dropping a binder (a dead or
  copy-propagated one) or inlining a body therefore never shifts a term.
* It carries **facts** about target levels: a constructor view (from a `con`
  or a `case` alternative), `y + 1` (a `natAdd [y, 1]`), a function global's
  closure, a partial application of one.
* The **continuation** of the term is `ret`, a jump to a target join level,
  or a meta-continuation (the rest of a caller after an inlined body), used
  at most once: before any branching it becomes a join point.

**Rules** (`Cfg.shrink`), each preserving every clock charge or
replacing it by a `tick` (tick dominance):
* copy propagation of an atom binding; dead pure bindings (`con`, `proj`,
  `prim`, `fn`, function `glob`), dead join points; `call`, `app` and CAF
  `glob` bindings are kept, except that a dead known partial application
  becomes a `tick`;
* projection of a known constructor; literal folding by `Prim.sem`; `case`
  of a known constructor or `Nat` literal (or `y + 1`);
* known calls: `app` of a function global's closure, or of a partial
  application of one, becomes `call` when saturated (over-saturated: the
  call, then `app` of the rest);
* β: a local function whose occurrences are all heads of applications (one
  occurrence, or several saturated ones) is inlined at each behind a `tick`
  (over-applied: its result is applied to the rest; under-applied: it
  becomes the function of its remaining parameters, behind a `tick` for the
  application's charge);
* a join point jumped to once, or of at most `Cfg.smallJoin` nodes, is
  inlined at its jumps behind a `tick`;
* case-of-case: a jump with a known constructor to a join point whose body
  scrutinises its parameter takes the selected alternative, behind a `tick`
  (bounded by the alternative's size, `Cfg.caseOfCaseBound`);
* case identity (`case x {cᵢ ⇒ ret cᵢ}` is `ret x`, never on the pinned
  `Nat` keys, whose literals are not constructors; leading ticks kept) and a
  `case` whose field-free arms are all equal.

**Inlining** (`Cfg.inline`, P3): a `call g as` or a CAF `glob g` of a listed
callee becomes `tick` and `g`'s body with its parameters bound to the
arguments; its `ret` continues with the caller (a join point when the body
branches). **Redirection** (`Cfg.redirect`, P4): a call of the specialised
global whose masked arguments are its own parameters (`fixedAt`) and exactly
the specialisation's fixed values calls the specialisation.

Everything recurses on explicit fuel over lists and `NatMap`s
(kernel-evaluable, D17). The census counts (`Exp.occ`, `Exp.jocc`) are
computed on the source term; a binding is dropped only when its variable has
no occurrence at all.

**Budgets.** Every walk step is charged its work (`charge`, `maxWalkWork`)
and refused past `maxWalkDepth` steps on the native stack (`descend`), so a
walk's work and stack are bounded whatever its input and certificate. The copy
count bounds what the walk visits in terms of its source:

* A walk visits each node of its source at most once, except where a rule
  walks a body again at another place: an inlined callee (`inline`,
  `inlineCaf`), an inlined join point (`joinOnce`, `joinSmall`), a
  case-of-case alternative, and a β-reduced local function's body *after its
  first expansion*. Each such firing charges the body's nodes (`copyCost`) to
  `Fires.copied`, and `fire` refuses the walk once its firings exceed
  `maxFires` or its copies exceed `maxCopy`, before it walks the body.
* A local function the walk inlines at its applications (`Ent.fn`) is
  *moved*, not copied, by its first expansion: the binding skips its body, so
  the body's nodes, which the walk of the term holding the binding paid for,
  are walked there once. The entry carries a number (`fresh`, `Fires.ents`)
  and the walk records the entries it has expanded (`Fires.expanded`); a
  second or later expansion of the same entry (a function applied at
  several saturated sites, or at a site that a join point inlined at several
  jumps or a case-of-case copy walks again) is charged in full (`betaFires`).
  A join point inlined at its single jump (`JEnt.mk none`) is numbered and
  moved the same way (`onceFires`).
* Under shrink, a join point walked as *pending* (`JEnt.pend`: case-of-case
  as a move) has its body, a `case` on its parameter, never walked where it
  stands: each jump to it walks the alternative its known constructor
  selects, the first selection of each alternative uncharged (that
  alternative's nodes are walked there once) and a later one charged
  (`pendFires`); a jump no known constructor resolves walks the whole body,
  charged (`Fires.pendInline`, none expected). The choice (`pendOk`, a
  pre-check of the join point and its scope, seeded with the constructors the
  walk knows there) is a function of the source and of the walk's state, so
  the re-run makes it alike. Its scan visits each node of the join point's
  scope at most once, which the walk's step at the join point already charges
  (`stepCost` counts the join point's nodes under shrink); its alternative
  lookups and its seed are charged as work (`chargeWork`).
* So, counting as an *instance* the global's body and each body a charged
  firing walks: every step of the walk is on a node of one instance (a moved
  body's nodes are those of the instance whose walk reached its binding), no
  node of an instance is walked twice (the continuations a walk builds, the
  rest of a caller after an inlined body, are each invoked at most once:
  `branch` turns one into a join point before any branching), and the
  instances other than the global's body total `Fires.copied` nodes. A walk,
  successful or refused, therefore takes at most its source's nodes plus
  `maxCopy` steps (`Fires.steps`; `tests-corpus` checks
  `steps ≤ nodes + copied` on every walk of every committed program).

That bound is argued here and checked, not proved: no Lean statement
mentions `Fires.steps` or `Fires.copied` (the walk's theorems are about the
program a successful walk returns), and what bounds the verifier whatever the
argument are the budgets the walk enforces. Nor is it proved that the pending
entry never makes a round worse than the walk without it: `tests-corpus`'s
budget survey checks, on every shrink round of every committed program, that
the walk with the pending choice is never refused where the walk without it
fires a rule and never copies more.

Before 2026-11-11 every β-reduction was charged, a once-used function's too,
so nested once-used functions (the else-branches of an `if` chain, as `Unit`
thunks) were charged the square of their nesting while the walk visited each
node once. (Under shrink, the census counts read at a binding, `Exp.occ` and
`Exp.headOcc`, walk the rest of the body, so a round on a global of `n` nodes
still costs up to order `n²` work, which `maxWalkWork` bounds.) -/

namespace IxCC.Anf.Walk

open IxCC.Ixon

/-- What a source value variable is in the target. -/
inductive Ent where
  | opd (o : Opd)
  /-- A local function inlined at its applications: its source environment,
  arity and body, and its number (`fresh`), by which the walk tells its first
  expansion, a move, from later ones, copies (`betaFires`). -/
  | fn (σ : List Ent) (arity : Nat) (body : Exp) (id : Nat)

instance : Inhabited Ent := ⟨.opd .box⟩

/-- What a source join point is in the target: emitted at a target join
level (`some l`) or inlined at its single jump (`none`, with its number `id`,
by which the walk tells its first expansion, a move, from later ones), with its source
environments, arity, recursion flag and body. -/
inductive JEnt where
  | mk (lvl : Option Nat) (σ : List Ent) (jσ : List JEnt) (arity : Nat) (rec : Bool) (body : Exp)
      (id : Nat)
  /-- A non-recursive join point of one parameter whose body is a `case` on
  it, every jump to which passes a constructor that `case` selects
  (`pendOk`): emitted dead at target join level `lvl` (body `trap`), each
  jump taking the alternative its constructor selects. -/
  | pend (lvl : Nat) (σ : List Ent) (jσ : List JEnt) (body : Exp)

instance : Inhabited JEnt := ⟨.mk none [] [] 0 false .trap 0⟩

/-- Facts about a target level. -/
inductive Fact where
  /-- `asCtor x = (c, fs)`: a `con` binding, or a `case` alternative. -/
  | ctor (c : Key.CtorKey) (fs : List Opd)
  /-- `x = y + 1`, from a successful `natAdd [y, 1]`. -/
  | succ (y : Opd)
  /-- `primResult p os = .ok x`, from a successful `prim p os`. -/
  | prim (p : Lam.Prim) (os : List Opd)
  /-- The closure of function global `g`. -/
  | glob (g : GlobalId)
  /-- An under-saturated application of function global `g`. -/
  | pap (g : GlobalId) (as : List Opd)

/-- The target depths and the facts at a point, and how many walk steps are on
the native stack below it (`lvl`, counted by `walk`; a continuation is called
with the `Here` of the point that calls it, so this counts the copies whose
frames stay below the rest of a caller too). -/
structure Here where
  d : Nat
  dj : Nat
  facts : Src.NatMap Fact
  lvl : Nat := 0

/-- Rule firing counts (the census of a round; zero at a fixpoint). -/
structure Fires where
  copy : Nat := 0
  dead : Nat := 0
  projKnown : Nat := 0
  fold : Nat := 0
  knownCall : Nat := 0
  deadPap : Nat := 0
  beta : Nat := 0
  joinOnce : Nat := 0
  joinSmall : Nat := 0
  deadJoin : Nat := 0
  caseKnown : Nat := 0
  caseOfCase : Nat := 0
  caseId : Nat := 0
  sameArms : Nat := 0
  inline : Nat := 0
  inlineCaf : Nat := 0
  redirect : Nat := 0
  /-- Nodes of the bodies the firings walked again (`copyCost`): not a rule
  firing, so `total` leaves it out. -/
  copied : Nat := 0
  /-- The most walk steps on the native stack at once (`Here.lvl`): not a rule
  firing either. -/
  depth : Nat := 0
  /-- The work the walk's steps charged (`stepCost`): not a rule firing
  either. -/
  work : Nat := 0
  /-- The walk's steps (calls of `walk`, counted by `charge`): at most the
  source's nodes plus `copied` (see the module note). -/
  steps : Nat := 0
  /-- Local function entries numbered so far (`fresh`). -/
  ents : Nat := 0
  /-- The local function entries already expanded once: a later expansion is
  a copy (`betaFires`). The walk's own state, not a census: `add` drops it. -/
  expanded : Src.NatMap Unit := .leaf
  /-- Jumps to a pending join point (`JEnt.pend`) that no known constructor
  resolved, so its body was inlined there: none is expected under `pendOk`
  (`tests-corpus`'s survey asserts zero). -/
  pendInline : Nat := 0
  /-- Per target join level of a pending join point, the alternatives (by
  position, the default last) selected at its jumps so far: the first
  selection of each moves it, a later one copies it. The walk's own state, not
  a census: `add` drops it. -/
  pending : Src.NatMap (Src.NatMap Unit) := .leaf
  deriving Repr, Inhabited

namespace Fires

def total (f : Fires) : Nat :=
  f.copy + f.dead + f.projKnown + f.fold + f.knownCall + f.deadPap + f.beta + f.joinOnce +
  f.joinSmall + f.deadJoin + f.caseKnown + f.caseOfCase + f.caseId + f.sameArms + f.inline +
  f.inlineCaf + f.redirect + f.pendInline

def add (f g : Fires) : Fires :=
  { copy := f.copy + g.copy, dead := f.dead + g.dead, projKnown := f.projKnown + g.projKnown
    fold := f.fold + g.fold, knownCall := f.knownCall + g.knownCall
    deadPap := f.deadPap + g.deadPap, beta := f.beta + g.beta, joinOnce := f.joinOnce + g.joinOnce
    joinSmall := f.joinSmall + g.joinSmall
    deadJoin := f.deadJoin + g.deadJoin, caseKnown := f.caseKnown + g.caseKnown
    caseOfCase := f.caseOfCase + g.caseOfCase, caseId := f.caseId + g.caseId
    sameArms := f.sameArms + g.sameArms, inline := f.inline + g.inline
    inlineCaf := f.inlineCaf + g.inlineCaf, redirect := f.redirect + g.redirect
    pendInline := f.pendInline + g.pendInline, copied := f.copied + g.copied, depth := max f.depth g.depth,
    work := f.work + g.work, steps := f.steps + g.steps, ents := f.ents + g.ents }

def render (f : Fires) : String :=
  let xs := [("copy", f.copy), ("dead", f.dead), ("projKnown", f.projKnown), ("fold", f.fold),
    ("knownCall", f.knownCall), ("deadPap", f.deadPap), ("beta", f.beta),
    ("joinOnce", f.joinOnce), ("joinSmall", f.joinSmall), ("deadJoin", f.deadJoin),
    ("caseKnown", f.caseKnown), ("caseOfCase", f.caseOfCase), ("caseId", f.caseId),
    ("sameArms", f.sameArms), ("inline", f.inline), ("inlineCaf", f.inlineCaf),
    ("redirect", f.redirect), ("pendInline", f.pendInline)]
  " ".intercalate ((xs.filter (·.2 > 0)).map fun (n, k) => s!"{n} {k}")

end Fires

/-- An argument of a redirected call: parameter `i`'s argument, or a fixed
operand of the specialisation's body. -/
inductive Hole where
  | param (i : Nat)
  | fixed (o : Opd)
  deriving Inhabited

/-- P4: calls of `g` whose masked arguments are the operands `fixedArgs`
become calls of `spec` on `holes`. -/
structure Redirect where
  g : GlobalId
  /-- Per parameter of `g`: the operand a masked parameter is fixed to. -/
  fixedArgs : List (Option Opd)
  spec : GlobalId
  holes : List Hole

structure Cfg where
  prog : Program
  shrink : Bool := false
  /-- P3: callees whose calls and CAF values are inlined. -/
  inline : List GlobalId := []
  /-- Case-of-case copies alternatives of at most this many nodes. -/
  caseOfCaseBound : Nat := 512
  /-- Non-recursive join points of at most this many nodes are inlined at
  their jumps. -/
  smallJoin : Nat := 24
  redirect : Option Redirect := none
  /-- Tests only: force the choice of the pending mode for every join point that
  may take it (`none`, the default: `pendOk` decides). The producer's shrink
  rounds take it from `Shrink.Budgets.pendForce` (`none` unless a test sets
  it); the re-run's walks (`Shrink.cfg`, the inline step's) never set it, and no
  certificate carries it. -/
  pendForce : Option Bool := none

abbrev M := StateT Fires (Except String)

structure Env where
  σ : List Ent := []
  jσ : List JEnt := []

/-- The continuation of the term being walked. -/
inductive Kont where
  | ret
  /-- Jump to the join point at this target join level. -/
  | jump (l : Nat)
  /-- The rest of a caller: used at most once. -/
  | cont (k : Here → Opd → M Exp)

instance : Inhabited Kont := ⟨.ret⟩

/-- Rule firings allowed in one walk of one global (the most a walk of a
committed program fires: `tests-corpus`'s budget survey, `docs/compiler-design.md`,
"Middle-end budgets"). -/
def maxFires : Nat := 8192

/-- Nodes one walk may walk again (`Fires.copied`): inlined callees, inlined
join points, case-of-case alternatives (but the first selection of each
alternative of a pending join point) and the second and later expansions of
a local function, together (a local function's first expansion is a move,
see the module note). With the source's nodes it bounds the walk's steps. The
committed programs' largest copies, in an inline walk and in a shrink round,
are `tests-corpus`'s survey's, recorded in `docs/compiler-design.md`
("Middle-end budgets"). -/
def maxCopy : Nat := 8192

/-- The charge for walking `b` again: its nodes, counted up to `maxCopy + 1`
(`Exp.nodesUpTo` stops there). -/
def copyCost (b : Exp) : Nat := b.nodesUpTo maxCopy

/-- Count a rule firing, refusing the walk once its firings exceed `maxFires`
or its copies exceed `maxCopy`. -/
def fire (f : Fires → Fires) : M Unit := fun s =>
  if (f s).total > maxFires then .error "walk: rule firing budget exhausted"
  else if (f s).copied > maxCopy then .error "walk: copy budget exhausted"
  else .ok ((), f s)

/-- A β-reduction of local function entry `id`, of body `fb`: the entry's
first expansion moves its body (the walk that reached its binding skipped it)
and is not charged; every later one walks it again and is charged its nodes.
The entry is recorded as expanded. -/
def betaFires (id : Nat) (fb : Exp) (f : Fires) : Fires :=
  { f with beta := f.beta + 1
           copied := if f.expanded.contains id then f.copied + copyCost fb else f.copied
           expanded := f.expanded.insert id () }

/-- A join point inlined at its single jump (entry `id`, body `b`): as for a
local function (`betaFires`), the entry's first expansion moves the body (the
walk that reached the join point skipped it) and is not charged; a later one
(the jump walked again, in a copy) is charged its nodes. -/
def onceFires (id : Nat) (b : Exp) (f : Fires) : Fires :=
  { f with joinOnce := f.joinOnce + 1
           copied := if f.expanded.contains id then f.copied + copyCost b else f.copied
           expanded := f.expanded.insert id () }

/-- A new local function entry's number. -/
def fresh : M Nat := fun s => .ok (s.ents, { s with ents := s.ents + 1 })

/-- Work one walk may do (`Fires.work`, charged by `stepCost` at every step, and by
`chargeWork` for the pending pre-check; the most one walk of a committed program
does: `tests-corpus`'s budget survey). -/
def maxWalkWork : Nat := 10000000

/-- What resolving `as` reads: variable `i` is the `i`-th entry of the
environment's list. -/
def atomsCost : List Atom → Nat
  | [] => 0
  | .var i :: as => i + 1 + atomsCost as
  | _ :: as => 1 + atomsCost as

/-- The atoms a binding resolves. -/
def bindAtoms : Bind → List Atom
  | .atom a | .proj _ _ a => [a]
  | .con _ as | .prim _ as | .call _ as => as
  | .app f as => f :: as
  | .glob _ | .fn .. => []

/-- An upper bound of the work one walk step on `e` does beyond a constant,
counted up to `cap + 1`: resolving the atoms it reads (the environment is a
list), looking a join point up by index (a jump, or a binding whose body is
one, `after`), and, under shrink, the census counts, arm comparisons and
case-identity tests that read subterms of `e` (`Exp.occ`, `Exp.headOcc`,
`Exp.jocc`, `sameArms`, `identityTail`), the target join point's body at a
jump, and the known-primitive search over the levels (`knownPrim`); a call
being redirected reads the redirection's holes. Charged by `walk` before the
step runs (`charge`), so a walk's work is at most `maxWalkWork` whatever its
input and certificate. (A local function entry's number and the expanded
entries' map, `fresh` and `betaFires`, cost a constant: a number below the
walk's steps, at most `maxWalkWork`, has at most 24 bits.) -/
def stepCost (C : Cfg) (env : Env) (here : Here) (e : Exp) (cap : Nat) : Nat :=
  let lookups := match e with
    | .bind _ b body => atomsCost (bindAtoms b) + (match body with
        | .jump j _ => j
        | _ => 0)
    | .jump j as => atomsCost as + j
    | .case x _ _ => atomsCost [x]
    | .ret a => atomsCost [a]
    | _ => 0
  let census := if C.shrink then
      e.nodesUpTo cap + here.d + (match e with
        | .jump j _ => match env.jσ[j]? with
          | some (.mk _ _ _ _ _ b _) | some (.pend _ _ _ b) => b.nodesUpTo cap
          | none => 0
        | _ => 0)
    else 0
  let redirect := match e, C.redirect with
    | .bind _ (.call _ _) _, some r => r.holes.length
    | _, _ => 0
  1 + lookups + census + redirect

/-- Charge one step's work (`cost` of the budget left) and count the step,
refusing the walk once its work passes `maxWalkWork`. -/
def charge (cost : Nat → Nat) : M Unit := fun s =>
  if s.work + cost (maxWalkWork - s.work) > maxWalkWork then .error "walk: work budget exhausted"
  else .ok ((), { s with work := s.work + cost (maxWalkWork - s.work), steps := s.steps + 1 })

/-- Charge work that is not a walk step (reading the output of a scope walked
first, `walkJoin`): `cost` of the budget left, refusing past `maxWalkWork`. -/
def chargeWork (cost : Nat → Nat) : M Unit := fun s =>
  if s.work + cost (maxWalkWork - s.work) > maxWalkWork then .error "walk: work budget exhausted"
  else .ok ((), { s with work := s.work + cost (maxWalkWork - s.work) })

/-- Walk steps one walk may have on the native stack at once: four times below
the fewest at which a walk overflows an 8 MiB stack (nested single-alternative
`case`s, about 12,290; see `docs/compiler-design.md`, "Middle-end budgets"),
and 2.4 times the most a committed program's walk reaches (1,252).
A walk recurses natively through its global and, below the rest of a caller,
through every copy it splices in, so the depth checks on its input do not bound
this alone. -/
def maxWalkDepth : Nat := 3072

/-- Refuse a step `lvl` walk steps deep once that passes `maxWalkDepth`, and
record the deepest. -/
def descend (lvl : Nat) : M Unit := fun s =>
  if lvl > maxWalkDepth then .error "walk: depth budget exhausted"
  else .ok ((), { s with depth := max s.depth lvl })

def resolve (env : Env) : Atom → M Opd
  | .var i =>
    match env.σ[i]? with
    | some (.opd o) => pure o
    | some (.fn ..) => throw s!"walk: inlined local function #{i} used as a value"
    | none => throw s!"walk: variable #{i} out of scope"
  | .lit l => pure (.lit l)
  | .box => pure .box

def resolveList (env : Env) : List Atom → M (List Opd)
  | [] => pure []
  | a :: as => return (← resolve env a) :: (← resolveList env as)

def atoms (d : Nat) (os : List Opd) : List Atom := os.map (·.atom d)

/-- The constructor view of an operand, when known. -/
def known (K : Lam.Known) (here : Here) : Opd → Option (Key.CtorKey × List Opd)
  | .lit (.nat 0) => K.natZero.map (·, [])
  | .lit (.nat (n + 1)) => K.natSucc.map (·, [.lit (.nat n)])
  | .lvl l =>
    match here.facts.get? l with
    | some (.ctor c fs) => some (c, fs)
    | some (.succ y) => K.natSucc.map (·, [y])
    | _ => none
  | _ => none

/-- A known function global and the arguments it already has. -/
def knownHead (here : Here) : Opd → Option (GlobalId × List Opd)
  | .lvl l =>
    match here.facts.get? l with
    | some (.glob g) => some (g, [])
    | some (.pap g as) => some (g, as)
    | _ => none
  | _ => none

/-- Literal folding. -/
def fold (p : Lam.Prim) (os : List Opd) : Option Src.PrimResult :=
  let rec lits : List Opd → Option (List Nat)
    | [] => some []
    | .lit (.nat n) :: os => (lits os).map (n :: ·)
    | _ => none
  (lits os).bind p.sem

/-- A target level that already holds `prim p os`. -/
def knownPrim (facts : Src.NatMap Fact) (p : Lam.Prim) (os : List Opd) : Nat → Option Opd
  | 0 => none
  | l + 1 =>
    match facts.get? l with
    | some (.prim p' os') =>
      if decide (p' = p ∧ os' = os) then some (.lvl l) else knownPrim facts p os l
    | some (.succ y) =>
      if decide (p = .natAdd ∧ os = [y, .lit (.nat 1)]) then some (.lvl l) else knownPrim facts p os l
    | _ => knownPrim facts p os l

/-- `natBle [x, m]` where `x = y + 1` is known (`Fact.succ`): the operands `[y, m]` of the
`natBlt` with the same result (`y + 1 ≤ m ↔ y < m`). Lean's `x < y` on `Nat` (`Nat.decLt`, and
through it every fixed-width word's `decLt`) is `Nat.ble (x + 1) y`; `natBlt` does not build
`x + 1`, which natively fails with `natOverflow` at `x = 2^63 − 1`. `natBle m x` has no such
form and is kept. -/
def succBle (facts : Src.NatMap Fact) : Lam.Prim → List Opd → Option (List Opd)
  | .natBle, [.lvl l, m] =>
    match facts.get? l with
    | some (.succ y) => some [y, m]
    | _ => none
  | _, _ => none

/-- The fact a successful `prim p os` records at its level. -/
def primFact (p : Lam.Prim) (os : List Opd) : Fact :=
  match p, os with
  | .natAdd, [y, .lit (.nat 1)] => .succ y
  | p, os => .prim p os

/-- The alternative a known constructor selects: `(true, body)` for an
alternative (fields bound), `(false, body)` for the default. -/
def select (alts : List Alt) (dflt : Option Exp) (c : Key.CtorKey) (n : Nat) :
    Option (Bool × Exp) :=
  match alts.find? fun a => decide (a.key = c) && a.arity == n with
  | some a => some (true, a.body)
  | none => dflt.map (false, ·)

/-- `tick^n e`. -/
def ticks : Nat → Exp → Exp
  | 0, e => e
  | n + 1, e => .tick (ticks n e)

/-- Leading ticks and the rest. -/
def stripTicks : Exp → Nat × Exp
  | .tick e => let (n, r) := stripTicks e; (n + 1, r)
  | e => (0, e)

/-- The position of the alternative a known constructor selects (`select`),
the default's being `alts.length`. -/
def selectIdx (alts : List Alt) (c : Key.CtorKey) (n : Nat) : Nat :=
  (alts.findIdx? fun a => decide (a.key = c) && a.arity == n).getD alts.length

/-- A case-of-case selection of alternative `i`, of body `alt`, at a jump to
the pending join point at target level `l` (`JEnt.pend`): its body is never
walked, so the first selection of each alternative moves it and is not
charged; a later one walks it again and is charged its nodes. -/
def pendFires (l i : Nat) (alt : Exp) (f : Fires) : Fires :=
  let f := { f with caseOfCase := f.caseOfCase + 1 }
  let sel := f.pending.getD l .leaf
  if sel.contains i then { f with copied := f.copied + copyCost alt }
  else { f with pending := f.pending.insert l (sel.insert i ()) }

/-- The common tail of a case identity: every alternative is field-free and
returns (or jumps with) its own constructor. -/
def identityTail (K : Lam.Known) (alts : List Alt) : Option (Nat × Option Nat) :=
  let tail : Alt → Option (Nat × Option Nat)
    | .mk key 0 b =>
      let ok := fun (key' : Key.CtorKey) => decide (key' = key) && !(K.natZero == some key)
      match stripTicks b with
      | (m, .bind _ (.con key' []) (.ret (.var 0))) => if ok key' then some (m, none) else none
      | (m, .bind _ (.con key' []) (.jump j [.var 0])) => if ok key' then some (m, some j) else none
      | _ => none
    | _ => none
  match alts with
  | [] => none
  | a :: rest =>
    match tail a with
    | some t => if rest.all (fun b => tail b == some t) then some t else none
    | none => none

/-- All arms field-free and equal (at least two branches). -/
def sameArms (alts : List Alt) (dflt : Option Exp) : Option Exp :=
  match alts with
  | [] => none
  | .mk _ 0 b :: rest =>
    if rest.all (fun a => a.arity == 0 && a.body.beq b) &&
       (match dflt with | some e => e.beq b | none => true) &&
       rest.length + (if dflt.isSome then 1 else 0) ≥ 1
    then some b else none
  | _ => none

mutual
/-- The constructors (key and field count) the jumps to join point `jd` pass
in a scope, if every such jump passes a variable of known constructor, none is
in a nested join point's body (walked once, where it is), and no `case` there
whose scrutinee's constructor is unknown is a case identity (which turns into
a jump with its scrutinee); `none` otherwise. `cons` maps the source levels
below `d` of known constructor to it: on entry those the walk's facts give for
the variables in scope at the join point, then each `con` binding of the scope
and, in an alternative, the scrutinee. A `case` on a variable of known
constructor contributes only the alternative it selects, as the walk takes only
that one (`caseKnown`). A `fn`'s body is not scanned: its jumps cannot reach
the scope's join points. -/
def pendScan (K : Lam.Known) (cons : Src.NatMap (Key.CtorKey × Nat)) (d jd : Nat) :
    Exp → Option (List (Key.CtorKey × Nat))
  | .bind _ b e =>
    let cons := match b with
      | .con c as => cons.insert d (c, as.length)
      | _ => cons
    pendScan K cons (d + 1) jd e
  | .join _ r b e =>
    if b.jocc (if r then jd + 1 else jd) == 0 then pendScan K cons d (jd + 1) e else none
  | .case x alts dflt =>
    let lx := match x with
      | .var i => if i < d then some (d - 1 - i) else none
      | _ => none
    -- a scrutinee of known constructor: the walk takes the alternative it
    -- selects and nothing else (`caseKnown`, before the other `case` rules)
    let kx := lx.bind cons.get?
    let sel := match kx with
      | some (c, n) => if alts.any (fun a => decide (a.key = c) && a.arity == n) then some (c, n) else none
      | none => none
    match sel with
    | some (c, n) => pendScanSel K cons c n d jd alts
    | none =>
    if kx.isSome && dflt.isSome then pendScanOpt K cons d jd dflt
    else if (dflt.isNone && (identityTail K alts).isSome) || (sameArms alts dflt).isSome then none
    else do
      -- in an alternative, a scrutinee variable is that alternative's
      -- constructor (`walkAlts` records it)
      let xs ← pendScanAlts K cons lx d jd alts
      let ys ← pendScanOpt K cons d jd dflt
      pure (xs ++ ys)
  | .tick e => pendScan K cons d jd e
  | .jump j as =>
    if j != jd then some []
    else match as with
      | [.var i] => if i < d then (cons.get? (d - 1 - i)).map ([·]) else none
      | _ => none
  | .ret _ | .trap => some []
def pendScanAlts (K : Lam.Known) (cons : Src.NatMap (Key.CtorKey × Nat)) (lx : Option Nat)
    (d jd : Nat) : List Alt → Option (List (Key.CtorKey × Nat))
  | [] => some []
  | .mk c n b :: as => do
    let cons' := match lx with
      | some l => cons.insert l (c, n)
      | none => cons
    let xs ← pendScan K cons' (d + n) jd b
    let ys ← pendScanAlts K cons lx d jd as
    pure (xs ++ ys)
/-- The alternative of constructor `c` with `n` fields, the first that matches (as
`select`), scanned with its fields bound. -/
def pendScanSel (K : Lam.Known) (cons : Src.NatMap (Key.CtorKey × Nat)) (c : Key.CtorKey) (n d jd : Nat) :
    List Alt → Option (List (Key.CtorKey × Nat))
  | [] => some []
  | .mk c' n' b :: as =>
    if decide (c' = c) && n' == n then pendScan K cons (d + n') jd b
    else pendScanSel K cons c n d jd as
def pendScanOpt (K : Lam.Known) (cons : Src.NatMap (Key.CtorKey × Nat)) (d jd : Nat) :
    Option Exp → Option (List (Key.CtorKey × Nat))
  | some e => pendScan K cons d jd e
  | none => some []
end

/-- Whether a non-recursive join point of one parameter, of body `b` and
scope `body` at source depth `d`, is walked as pending (`JEnt.pend`): its body is a `case` on its
parameter, every jump to it passes a known constructor that `case` selects
(`pendScan`), and an alternative over `caseOfCaseBound` nodes is selected by
at most one jump. `seed`: the constructors the walk knows for the variables in
scope (`pendScan`). A deterministic function of the source join point and the
walk's state there, so the producer and the re-run choose alike. Under it every jump resolves by
case-of-case (the walk's facts hold each `con` it emitted), so the body is
never walked; the walk counts a jump that does not (`Fires.pendInline`, none
expected). -/
def pendOk (C : Cfg) (d : Nat) (seed : Src.NatMap (Key.CtorKey × Nat)) (b body : Exp) : Bool :=
  match (stripTicks b).2 with
  | .case (.var 0) alts dflt =>
    match pendScan C.prog.known seed d 0 body with
    | none => false
    | some keys =>
      let sel : List (Option Exp × Nat) := keys.map fun (c, n) =>
        ((select alts dflt c n).map (fun (p : Bool × Exp) => p.2), selectIdx alts c n)
      let counts : Src.NatMap Nat := sel.foldl (fun m (_, i) => m.insert i (m.getD i 0 + 1)) .leaf
      sel.all fun ((alt : Option Exp), (i : Nat)) => match alt with
        | some a => a.nodesLe C.caseOfCaseBound || decide (counts.getD i 0 ≤ 1)
        | none => false
  | _ => false

/-- The most jumps a pending join point may have (`pendOk` looks each one's
alternative up, so its work is at most this many times the join point's body,
which `walkJoin` charges). -/
def maxPendJumps : Nat := 8

/-- Continue with an operand. -/
def pass (here : Here) (o : Opd) : Kont → M Exp
  | .ret => pure (.ret (o.atom here.d))
  | .jump l => pure (.jump (here.dj - 1 - l) [o.atom here.d])
  | .cont k => k here o

/-- Before branching, turn a meta-continuation into a join point. -/
def branch (here : Here) (k : Kont) (body : Here → Kont → M Exp) : M Exp :=
  match k with
  | .cont f => do
    let jb ← f { here with d := here.d + 1 } (.lvl here.d)
    let e ← body { here with dj := here.dj + 1 } (.jump here.dj)
    pure (.join 1 false jb e)
  | k => body here k

/-- The arguments of a redirected call, if every masked argument is its
fixed operand. -/
def redirectArgs (r : Redirect) (os : List Opd) : Option (List Opd) :=
  if os.length == r.fixedArgs.length &&
     (os.zip r.fixedArgs).all (fun (o, f) => match f with
        | some f => o == f
        | none => true)
  then r.holes.mapM fun
    | .param i => os[i]?
    | .fixed o => some o
  else none

/-- Every masked argument of a call is the redirected global's parameter
itself (`d`: the source depth, one per variable in scope), as P4's
fixed-parameter checker requires of every call it redirects. -/
def fixedAt (r : Redirect) (d : Nat) (as : List Atom) : Bool :=
  as.length == r.fixedArgs.length &&
    (as.zipIdx.zip r.fixedArgs).all fun ((a, i), f) =>
      f.isNone || a == .var (d - 1 - i) || (f == some .box && a == .box)

/-- Field levels `d … d + n - 1`, in order. -/
def fieldOpds (d n : Nat) : List Opd := (List.range n).map fun i => .lvl (d + i)

def entsOf (os : List Opd) : List Ent := os.map .opd

mutual

def walk (C : Cfg) : Nat → Env → Here → Exp → Kont → M Exp
  | 0, _, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, here, e, k => do
    charge (stepCost C env here e)
    descend (here.lvl + 1)
    let here := { here with lvl := here.lvl + 1 }
    match e with
    | .bind c b body => walkBind C fuel env here c b body k
    | .join n r b body => walkJoin C fuel env here n r b body k
    | .jump j as => walkJump C fuel env here j as k
    | .case x alts d => walkCase C fuel env here x alts d k
    | .ret a => do pass here (← resolve env a) k
    | .tick body => return .tick (← walk C fuel env here body k)
    | .trap => pure .trap

/-- Walk `body` (the rest after an inlined term whose value is the result)
as the continuation of an inlined body, or reuse `k` for a tail call. -/
def after (C : Cfg) : Nat → Env → Exp → Kont → M Kont
  | 0, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, body, k =>
    match body with
    | .ret (.var 0) => pure k
    | .jump j [.var 0] =>
      match env.jσ[j]? with
      | some (.mk (some l) ..) => pure (.jump l)
      | _ => pure (.cont fun here o => walk C fuel { env with σ := .opd o :: env.σ } here body k)
    | _ => pure (.cont fun here o => walk C fuel { env with σ := .opd o :: env.σ } here body k)

def walkBind (C : Cfg) : Nat → Env → Here → V3.LetContract → Bind → Exp → Kont → M Exp
  | 0, _, _, _, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, here, c, b, body, k =>
    let P := C.prog
    let K := P.known
    let emit := fun (b' : Bind) (fact : Option Fact) => do
      let facts := match fact with
        | some f => here.facts.insert here.d f
        | none => here.facts
      let e ← walk C fuel { env with σ := .opd (.lvl here.d) :: env.σ }
        { here with d := here.d + 1, facts } body k
      pure (Exp.bind c b' e)
    let skip := fun (ent : Ent) => walk C fuel { env with σ := ent :: env.σ } here body k
    let dead := C.shrink && body.occ 0 == 0
    match b with
    | .atom a => do
      let o ← resolve env a
      if C.shrink then do fire fun f => { f with copy := f.copy + 1 }; skip (.opd o)
      else emit (.atom (o.atom here.d)) none
    | .con cc as => do
      let os ← resolveList env as
      if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
      else emit (.con cc (atoms here.d os)) (some (.ctor cc os))
    | .proj cc i x => do
      let xo ← resolve env x
      let hit := if C.shrink then
          match known K here xo with
          | some (c', fs) => if decide (c' = cc) then fs[i]? else none
          | none => none
        else none
      match hit with
      | some o => do fire fun f => { f with projKnown := f.projKnown + 1 }; skip (.opd o)
      | none =>
        if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
        else emit (.proj cc i (xo.atom here.d)) none
    | .prim p as => do
      let os ← resolveList env as
      let fact := some (primFact p os)
      match (if C.shrink then fold p os else none) with
      | some (.nat n) => do fire fun f => { f with fold := f.fold + 1 }; skip (.opd (.lit (.nat n)))
      | some (.bool v) =>
        match (if v then K.boolTrue else K.boolFalse) with
        | some key => do
          fire fun f => { f with fold := f.fold + 1 }
          if dead then skip (.opd .box) else emit (.con key []) (some (.ctor key []))
        | none => emit (.prim p (atoms here.d os)) fact
      | none =>
        match (if C.shrink then knownPrim here.facts p os here.d else none) with
        | some o => do fire fun f => { f with fold := f.fold + 1 }; skip (.opd o)
        | none =>
          if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
          else
            match (if C.shrink then succBle here.facts p os else none) with
            | some os' => do
              fire fun f => { f with fold := f.fold + 1 }
              emit (.prim .natBlt (atoms here.d os')) fact
            | none => emit (.prim p (atoms here.d os)) fact
    | .glob g =>
      match P.global? g with
      | some gd =>
        match gd.ps with
        | [] =>
          if C.inline.contains g then do
            fire fun f => { f with inlineCaf := f.inlineCaf + 1, copied := f.copied + copyCost gd.body }
            let k' ← after C fuel env body k
            return .tick (← walk { C with inline := [], redirect := none } fuel {} here gd.body k')
          else emit (.glob g) none
        | _ :: _ =>
          if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
          else emit (.glob g) (some (.glob g))
      | none => throw s!"walk: global {g} out of range"
    | .call g as => do
      let os ← resolveList env as
      let redirected := C.redirect.bind fun r =>
        if r.g == g && fixedAt r env.σ.length as then (redirectArgs r os).map (r.spec, ·) else none
      match redirected with
      | some (s, os') => do
        fire fun f => { f with redirect := f.redirect + 1 }
        emit (.call s (atoms here.d os')) none
      | none =>
        match P.global? g with
        | some gd =>
          if C.inline.contains g && os.length == gd.ps.length then do
            fire fun f => { f with inline := f.inline + 1, copied := f.copied + copyCost gd.body }
            let k' ← after C fuel env body k
            return .tick (← walk { C with inline := [], redirect := none } fuel
              { σ := entsOf os.reverse } here gd.body k')
          else emit (.call g (atoms here.d os)) none
        | none => throw s!"walk: global {g} out of range"
    | .app f as => do
      let os ← resolveList env as
      let local? := match f with
        | .var i =>
          match env.σ[i]? with
          | some (.fn σf n fb id) => some (σf, n, fb, id)
          | _ => none
        | _ => none
      match local? with
      | some (σf, n, fb, id) =>
        if os.length ≥ n then do
          fire (betaFires id fb)
          let rest := os.drop n
          let k' ← if rest.isEmpty then after C fuel env body k
            else pure (.cont fun here' o => do
              -- over-application: apply the result to the remaining arguments
              let e ← walk C fuel { env with σ := .opd (.lvl here'.d) :: env.σ }
                { here' with d := here'.d + 1 } body k
              pure (.bind c (.app (o.atom here'.d) (atoms here'.d rest)) e))
          return .tick (← walk C fuel { σ := entsOf (os.take n).reverse ++ σf } here fb k')
        else do
          -- under-application: the rest of the function, its first
          -- parameters bound (the application's charge becomes a tick)
          fire (betaFires id fb)
          let m := n - os.length
          let fb' ← walk C fuel { σ := entsOf (os ++ fieldOpds here.d m).reverse ++ σf }
            { here with d := here.d + m, dj := 0 } fb .ret
          let e ← walk C fuel { env with σ := .opd (.lvl here.d) :: env.σ }
            { here with d := here.d + 1 } body k
          return .tick (.bind c (.fn (List.replicate m {}) fb') e)
      | none => do
        let fo ← resolve env f
        match (if C.shrink then knownHead here fo else none) with
        | some (g, as0) =>
          let n := (P.arity? g).getD 0
          let all := as0 ++ os
          if all.length == n then do
            fire fun f => { f with knownCall := f.knownCall + 1 }
            emit (.call g (atoms here.d all)) none
          else if all.length > n then do
            fire fun f => { f with knownCall := f.knownCall + 1 }
            let e ← walk C fuel { env with σ := .opd (.lvl (here.d + 1)) :: env.σ }
              { here with d := here.d + 2 } body k
            pure (.bind freshLet (.call g (atoms here.d (all.take n)))
              (.bind c (.app (.var 0) (atoms (here.d + 1) (all.drop n))) e))
          else if dead then do
            fire fun f => { f with deadPap := f.deadPap + 1 }
            return .tick (← skip (.opd .box))
          else emit (.app (fo.atom here.d) (atoms here.d os)) (some (.pap g all))
        | none => emit (.app (fo.atom here.d) (atoms here.d os)) none
    | .fn ps fb =>
      let n := ps.length
      if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
      else if C.shrink && body.occ 0 == body.headOcc 0 1 &&
          (body.occ 0 == 1 || body.occ 0 == body.headOcc 0 n) then do
        let id ← fresh
        skip (.fn env.σ n fb id)
      else do
        let fb' ← walk C fuel { σ := entsOf (paramOpds here.d n) ++ env.σ }
          { here with d := here.d + n, dj := 0 } fb .ret
        emit (.fn ps fb') none

def walkJoin (C : Cfg) : Nat → Env → Here → Nat → Bool → Exp → Exp → Kont → M Exp
  | 0, _, _, _, _, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, here, n, r, b, body, k =>
    if C.shrink && !r && body.jocc 0 == 0 then do
      fire fun f => { f with deadJoin := f.deadJoin + 1 }
      walk C fuel { env with jσ := default :: env.jσ } here body k
    else if C.shrink && !r && body.jocc 0 == 1 then do
      let id ← fresh
      walk C fuel { env with jσ := .mk none env.σ env.jσ n false b id :: env.jσ } here body k
    else branch here k fun here k => do
      let pend ← if C.shrink && !r && n == 1 && body.jocc 0 ≤ maxPendJumps then do
          chargeWork fun cap => maxPendJumps * b.nodesUpTo cap + env.σ.length
          -- the constructors the walk knows for the variables in scope (its
          -- facts): the scope's `case`s on them are resolved (`caseKnown`)
          -- and the jumps passing them take their alternatives
          let d := env.σ.length
          let seed : Src.NatMap (Key.CtorKey × Nat) := env.σ.zipIdx.foldl (fun m (ent, i) =>
            match ent with
            | .opd o =>
              match known C.prog.known here o with
              | some (c, fs) => m.insert (d - 1 - i) (c, fs.length)
              | none => m
            | .fn .. => m) .leaf
          pure (C.pendForce.getD (pendOk C d seed b body))
        else pure false
      if pend then
        -- case-of-case as a move: every jump takes its alternative, the first
        -- selection of each a move; the body is never walked, and the join
        -- point is emitted dead (the next round removes it)
        let l := here.dj
        modify fun f => { f with pending := f.pending.insert l .leaf }
        let e' ← walk C fuel { env with jσ := .pend l env.σ env.jσ b :: env.jσ }
          { here with dj := l + 1 } body k
        modify fun f => { f with pending := f.pending.erase l }
        return .join n r .trap e'
      let self := JEnt.mk (some here.dj) env.σ env.jσ n r b 0
      let b' ← walk C fuel
        { σ := entsOf (paramOpds here.d n) ++ env.σ, jσ := if r then self :: env.jσ else env.jσ }
        { here with d := here.d + n, dj := if r then here.dj + 1 else here.dj } b k
      let e' ← walk C fuel { env with jσ := self :: env.jσ } { here with dj := here.dj + 1 } body k
      pure (.join n r b' e')

def walkJump (C : Cfg) : Nat → Env → Here → Nat → List Atom → Kont → M Exp
  | 0, _, _, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, here, j, as, k => do
    let os ← resolveList env as
    match env.jσ[j]? with
    | some (.mk none σj jσj n _ b id) =>
      if os.length == n then do
        fire (onceFires id b)
        return .tick (← walk C fuel { σ := entsOf os.reverse ++ σj, jσ := jσj } here b k)
      else throw s!"walk: jump to join point #{j} with {os.length} arguments"
    | some (.mk (some l) σj jσj n r b _) =>
      let (m, inner) := stripTicks b
      if C.shrink && !r && os.length == n &&
          (b.nodesLe C.smallJoin || (n == 1 && b.headOcc 0 1 > 0)) then do
        fire fun f => { f with joinSmall := f.joinSmall + 1, copied := f.copied + copyCost b }
        return .tick (← walk C fuel { σ := entsOf os.reverse ++ σj, jσ := jσj } here b k)
      let hit := if C.shrink && !r && n == 1 then
          match inner, os with
          | .case (.var 0) alts dflt, [o] =>
            match known C.prog.known here o with
            | some (c, fs) =>
              match select alts dflt c fs.length with
              | some (isAlt, alt) =>
                if alt.nodesLe C.caseOfCaseBound then
                  some ((if isAlt then entsOf fs.reverse else []) ++ .opd o :: σj, alt)
                else none
              | none => none
            | none => none
          | _, _ => none
        else none
      match hit with
      | some (σ', alt) => do
        fire fun f => { f with caseOfCase := f.caseOfCase + 1, copied := f.copied + copyCost alt }
        return ticks (m + 1) (← walk C fuel { σ := σ', jσ := jσj } here alt k)
      | none => pure (.jump (here.dj - 1 - l) (atoms here.d os))
    | some (.pend l σj jσj b) =>
      if os.length == 1 then
        let (m, inner) := stripTicks b
        let hit := match inner, os with
          | .case (.var 0) alts dflt, [o] =>
            match known C.prog.known here o with
            | some (c, fs) => (select alts dflt c fs.length).map fun (isAlt, alt) =>
                ((if isAlt then entsOf fs.reverse else []) ++ .opd o :: σj, alt,
                  selectIdx alts c fs.length)
            | none => none
          | _, _ => none
        match hit with
        | some (σ', alt, i) => do
          fire (pendFires l i alt)
          return ticks (m + 1) (← walk C fuel { σ := σ', jσ := jσj } here alt k)
        | none => do
          -- not expected under `pendOk`: the body, inlined at this jump
          fire fun f => { f with pendInline := f.pendInline + 1, copied := f.copied + copyCost b }
          return .tick (← walk C fuel { σ := entsOf os.reverse ++ σj, jσ := jσj } here b k)
      else throw s!"walk: jump to join point #{j} with {os.length} arguments"
    | none => throw s!"walk: join point #{j} out of scope"

def walkCase (C : Cfg) : Nat → Env → Here → Atom → List Alt → Option Exp → Kont → M Exp
  | 0, _, _, _, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, here, x, alts, dflt, k => do
    let xo ← resolve env x
    let K := C.prog.known
    let sel := if C.shrink then
        match known K here xo with
        | some (c, fs) => (select alts dflt c fs.length).map fun (isAlt, e) =>
            ((if isAlt then entsOf fs.reverse else []), e)
        | none => none
      else none
    match sel with
    | some (fields, e) => do
      fire fun f => { f with caseKnown := f.caseKnown + 1 }
      walk C fuel { env with σ := fields ++ env.σ } here e k
    | none =>
      match (if C.shrink && dflt.isNone then identityTail K alts else none) with
      | some (m, tail) => do
        fire fun f => { f with caseId := f.caseId + 1 }
        match tail with
        | none => return ticks m (← pass here xo k)
        | some j => return ticks m (← walk C fuel env here (.jump j [x]) k)
      | none =>
        match (if C.shrink then sameArms alts dflt else none) with
        | some e => do
          fire fun f => { f with sameArms := f.sameArms + 1 }
          walk C fuel env here e k
        | none =>
          let go := fun (here : Here) (k : Kont) => do
            let alts' ← walkAlts C fuel env here xo alts k
            let dflt' ← match dflt with
              | some e => some <$> walk C fuel env here e k
              | none => pure none
            pure (Exp.case (xo.atom here.d) alts' dflt')
          if alts.length + (if dflt.isSome then 1 else 0) ≥ 2 then branch here k go else go here k

def walkAlts (C : Cfg) : Nat → Env → Here → Opd → List Alt → Kont → M (List Alt)
  | 0, _, _, _, _, _ => throw "walk: fuel"
  | _, _, _, _, [], _ => pure []
  | fuel + 1, env, here, xo, .mk key n b :: rest, k => do
    let facts := match xo with
      | .lvl l => here.facts.insert l (.ctor key (fieldOpds here.d n))
      | _ => here.facts
    let b' ← walk C fuel { env with σ := entsOf (paramOpds here.d n) ++ env.σ }
      { here with d := here.d + n, facts } b k
    return .mk key n b' :: (← walkAlts C fuel env here xo rest k)

end

/-- Fuel of one walk: a bound on its recursion through subterms and inlined
bodies, far above any Phase 1 body. A continuation walks with its caller's
fuel, so the fuel does not bound the native stack; `maxWalkDepth` does. -/
def fuel : Nat := 1 <<< 24

/-- Walk a global's body over its parameters. -/
def global (C : Cfg) (gd : GDef) : M GDef := do
  let n := gd.ps.length
  let body ← walk C fuel { σ := entsOf (paramOpds 0 n) } { d := n, dj := 0, facts := .leaf }
    gd.body .ret
  return { gd with body }

end IxCC.Anf.Walk
