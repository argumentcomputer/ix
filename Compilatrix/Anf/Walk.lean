import Compilatrix.Anf.Opd
import Compilatrix.Anf.Census

/-! # The rewriting walk

One traversal shared by shrink (P2), inlining (P3) and the specialiser's
body copies (P4), designed as a sequence of local rewrites (02 §7.3) applied
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

**Rules** (`Cfg.shrink`, 02 §8), each preserving every clock charge or
replacing it by a `tick` (tick dominance):
* copy propagation of an atom binding; dead pure bindings (`con`, `proj`,
  `prim`, `fn`, function `glob`), dead join points; `call`, `app` and CAF
  `glob` bindings are kept, except that a dead known partial application
  becomes a `tick`;
* projection of a known constructor; literal folding by `Prim.sem`; `case`
  of a known constructor or `Nat` literal (or `y + 1`);
* known calls: `app` of a function global's closure, or of a partial
  application of one, becomes `call` when saturated;
* β: a local function used once, as the head of an application of its
  arity, is inlined there behind a `tick`; a join point jumped to once is
  inlined at the jump behind a `tick`;
* case-of-case: a jump with a known constructor to a join point whose body
  scrutinises its parameter takes the selected alternative, behind a `tick`
  (bounded by the alternative's size);
* case identity (`case x {cᵢ ⇒ ret cᵢ}` is `ret x`, never on the pinned
  `Nat` keys, whose literals are not constructors) and a `case` whose
  field-free arms are all equal.

**Inlining** (`Cfg.inline`, P3): a `call g as` or a CAF `glob g` of a listed
callee becomes `tick` and `g`'s body with its parameters bound to the
arguments; its `ret` continues with the caller (a join point when the body
branches). **Redirection** (`Cfg.redirect`, P4): a call of the specialised
global whose masked arguments are exactly the specialisation's fixed values
calls the specialisation.

Everything recurses on explicit fuel over lists and `NatMap`s
(kernel-evaluable, D17). The census counts (`Exp.occ`, `Exp.jocc`) are
computed on the source term; a binding is dropped only when its variable has
no occurrence at all. -/

namespace Compilatrix.Anf.Walk

open Compilatrix.Ixon

/-- What a source value variable is in the target. -/
inductive Ent where
  | opd (o : Opd)
  /-- A local function inlined at its single application: its source
  environment, arity and body. -/
  | fn (σ : List Ent) (arity : Nat) (body : Exp)

instance : Inhabited Ent := ⟨.opd .box⟩

/-- What a source join point is in the target: emitted at a target join
level (`some l`) or inlined at its single jump (`none`), with its source
environments, arity, recursion flag and body. -/
inductive JEnt where
  | mk (lvl : Option Nat) (σ : List Ent) (jσ : List JEnt) (arity : Nat) (rec : Bool) (body : Exp)

instance : Inhabited JEnt := ⟨.mk none [] [] 0 false .trap⟩

/-- Facts about a target level. -/
inductive Fact where
  /-- `asCtor x = (c, fs)`: a `con` binding, or a `case` alternative. -/
  | ctor (c : Key.CtorKey) (fs : List Opd)
  /-- `x = y + 1`, from a successful `natAdd [y, 1]`. -/
  | succ (y : Opd)
  /-- The closure of function global `g`. -/
  | glob (g : GlobalId)
  /-- An under-saturated application of function global `g`. -/
  | pap (g : GlobalId) (as : List Opd)

/-- The target depths and the facts at a point. -/
structure Here where
  d : Nat
  dj : Nat
  facts : Src.NatMap Fact

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
  deriving Repr, Inhabited

namespace Fires

def total (f : Fires) : Nat :=
  f.copy + f.dead + f.projKnown + f.fold + f.knownCall + f.deadPap + f.beta + f.joinOnce +
  f.joinSmall + f.deadJoin + f.caseKnown + f.caseOfCase + f.caseId + f.sameArms + f.inline +
  f.inlineCaf + f.redirect

def add (f g : Fires) : Fires :=
  { copy := f.copy + g.copy, dead := f.dead + g.dead, projKnown := f.projKnown + g.projKnown
    fold := f.fold + g.fold, knownCall := f.knownCall + g.knownCall
    deadPap := f.deadPap + g.deadPap, beta := f.beta + g.beta, joinOnce := f.joinOnce + g.joinOnce
    joinSmall := f.joinSmall + g.joinSmall
    deadJoin := f.deadJoin + g.deadJoin, caseKnown := f.caseKnown + g.caseKnown
    caseOfCase := f.caseOfCase + g.caseOfCase, caseId := f.caseId + g.caseId
    sameArms := f.sameArms + g.sameArms, inline := f.inline + g.inline
    inlineCaf := f.inlineCaf + g.inlineCaf, redirect := f.redirect + g.redirect }

def render (f : Fires) : String :=
  let xs := [("copy", f.copy), ("dead", f.dead), ("projKnown", f.projKnown), ("fold", f.fold),
    ("knownCall", f.knownCall), ("deadPap", f.deadPap), ("beta", f.beta),
    ("joinOnce", f.joinOnce), ("joinSmall", f.joinSmall), ("deadJoin", f.deadJoin),
    ("caseKnown", f.caseKnown), ("caseOfCase", f.caseOfCase), ("caseId", f.caseId),
    ("sameArms", f.sameArms), ("inline", f.inline), ("inlineCaf", f.inlineCaf),
    ("redirect", f.redirect)]
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
  caseOfCaseBound : Nat := 64
  /-- Non-recursive join points of at most this many nodes are inlined at
  their jumps. -/
  smallJoin : Nat := 24
  redirect : Option Redirect := none

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

def fire (f : Fires → Fires) : M Unit := modify f

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

/-- Field levels `d … d + n - 1`, in order. -/
def fieldOpds (d n : Nat) : List Opd := (List.range n).map fun i => .lvl (d + i)

def entsOf (os : List Opd) : List Ent := os.map .opd

mutual

def walk (C : Cfg) : Nat → Env → Here → Exp → Kont → M Exp
  | 0, _, _, _, _ => throw "walk: fuel"
  | fuel + 1, env, here, e, k =>
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
      let succ := match p, os with
        | .natAdd, [y, .lit (.nat 1)] => some (Fact.succ y)
        | _, _ => none
      match (if C.shrink then fold p os else none) with
      | some (.nat n) => do fire fun f => { f with fold := f.fold + 1 }; skip (.opd (.lit (.nat n)))
      | some (.bool v) =>
        match (if v then K.boolTrue else K.boolFalse) with
        | some key => do
          fire fun f => { f with fold := f.fold + 1 }
          if dead then skip (.opd .box) else emit (.con key []) (some (.ctor key []))
        | none => emit (.prim p (atoms here.d os)) succ
      | none =>
        if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
        else emit (.prim p (atoms here.d os)) succ
    | .glob g =>
      match P.global? g with
      | some gd =>
        match gd.ps with
        | [] =>
          if C.inline.contains g then do
            fire fun f => { f with inlineCaf := f.inlineCaf + 1 }
            let k' ← after C fuel env body k
            return .tick (← walk { C with inline := [], redirect := none } fuel {} here gd.body k')
          else emit (.glob g) none
        | _ :: _ =>
          if dead then do fire fun f => { f with dead := f.dead + 1 }; skip (.opd .box)
          else emit (.glob g) (some (.glob g))
      | none => throw s!"walk: global {g} out of range"
    | .call g as => do
      let os ← resolveList env as
      match C.redirect.bind fun r => if r.g == g then (redirectArgs r os).map (r.spec, ·) else none with
      | some (s, os') => do
        fire fun f => { f with redirect := f.redirect + 1 }
        emit (.call s (atoms here.d os')) none
      | none =>
        match P.global? g with
        | some gd =>
          if C.inline.contains g && os.length == gd.ps.length then do
            fire fun f => { f with inline := f.inline + 1 }
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
          | some (.fn σf n fb) => some (σf, n, fb)
          | _ => none
        | _ => none
      match local? with
      | some (σf, n, fb) =>
        if os.length ≥ n then do
          fire fun f => { f with beta := f.beta + 1 }
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
          fire fun f => { f with beta := f.beta + 1 }
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
      else if C.shrink && body.occ 0 == 1 && body.headOcc 0 1 == 1 then skip (.fn env.σ n fb)
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
    else if C.shrink && !r && body.jocc 0 == 1 then
      walk C fuel { env with jσ := .mk none env.σ env.jσ n false b :: env.jσ } here body k
    else branch here k fun here k => do
      let self := JEnt.mk (some here.dj) env.σ env.jσ n r b
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
    | some (.mk none σj jσj n _ b) =>
      if os.length == n then do
        fire fun f => { f with joinOnce := f.joinOnce + 1 }
        return .tick (← walk C fuel { σ := entsOf os.reverse ++ σj, jσ := jσj } here b k)
      else throw s!"walk: jump to join point #{j} with {os.length} arguments"
    | some (.mk (some l) σj jσj n r b) =>
      let (m, inner) := stripTicks b
      if C.shrink && !r && os.length == n && b.nodes ≤ C.smallJoin then do
        fire fun f => { f with joinSmall := f.joinSmall + 1 }
        return .tick (← walk C fuel { σ := entsOf os.reverse ++ σj, jσ := jσj } here b k)
      let hit := if C.shrink && !r && n == 1 then
          match inner, os with
          | .case (.var 0) alts dflt, [o] =>
            match known C.prog.known here o with
            | some (c, fs) =>
              match select alts dflt c fs.length with
              | some (isAlt, alt) =>
                if alt.nodes ≤ C.caseOfCaseBound then
                  some ((if isAlt then entsOf fs.reverse else []) ++ .opd o :: σj, alt)
                else none
              | none => none
            | none => none
          | _, _ => none
        else none
      match hit with
      | some (σ', alt) => do
        fire fun f => { f with caseOfCase := f.caseOfCase + 1 }
        return ticks (m + 1) (← walk C fuel { σ := σ', jσ := jσj } here alt k)
      | none => pure (.jump (here.dj - 1 - l) (atoms here.d os))
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

/-- Fuel of one walk: a bound on its recursion depth (subterms, inlined
bodies and continuations), far above any Phase 1 body. -/
def fuel : Nat := 1 <<< 24

/-- Walk a global's body over its parameters. -/
def global (C : Cfg) (gd : GDef) : M GDef := do
  let n := gd.ps.length
  let body ← walk C fuel { σ := entsOf (paramOpds 0 n) } { d := n, dj := 0, facts := .leaf } gd.body .ret
  return { gd with body }

end Compilatrix.Anf.Walk
