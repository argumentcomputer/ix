/-
  Ix.AuxGen.IxcScope: AuxGen's level questions answered by IxC Source mode
  over the Source service (AuxGen on IxC, M2a; AUXGEN-IXC §3.3; the plan is
  `auxgen-m2.md` §1.3). It builds the closures of `Ix.AuxGen.Oracle`.

  ## The scope

  A `Scope` is a local context over a Source environment (`SourceEnv`: the
  verified fold, its evidence, and the class map σ):
  * **Terms in.** A Lean term over the context goes through the Source
    ingress's own conversion, with nothing copied: its free variables are
    abstracted into loose bound variables (`batchAbstractWith`, the local at
    level `i` of `n` becomes `bvar (n - 1 - i)`); the term goes through σ and
    the shared `ingressExprs` (`SourceEnv.ingress`), which refuses any other
    free variable, metavariable or unknown level parameter; the loose bound
    variables are then instantiated with the locals, IxC's
    `.fvar i (annotated type)`. Level parameters are numbered by position in
    the context's `lps`.
  * **Locals** are annotated once, when pushed, at their own depth (IxC
    checks binder data).
  * **`getLevel`** is the `inferAppType` fast path where it applies (below),
    else `annotate`, `infer`, `ensureSort` in IxC's cached checker
    (`coreKnotI .verified`, fuel `checkFuel`; running out is a refusal). The
    level goes out as `Ix.Tc` would have built it (`Egress.egressLevel`), and
    a ∀'s level is `levelNormalize`d, as `Ix.Tc`'s `getLevel` does.

  ## The fast path

  `Ix.Tc`'s `getLevel` first tries `inferAppType`'s shortcut: a constant
  applied to as many arguments as its type has leading ∀s, whose body is a
  sort, has that sort's level with the arguments' levels substituted
  (`tryInferAppSortLevel`). The spelling of Lean's own auxiliaries depends on
  it. Here it reads the head's **Lean type** (the input's, through the
  service's lookups), rebuilt as `Ix.Tc`'s ingress rebuilds a level
  (`Egress.normalize`), and substitutes with `Ix.Tc`'s rules
  (`kunivToLevelWithConstLevels`). It never reads IxC's environment, so the
  level spelling the Source environment holds cannot change it.

  ## The oracle

  `oracleOf` builds one block's `AuxOracle` over a service snapshot, given
  lazily (the drivers' snapshot is a task that the first question waits
  for). `withFlat` installs the block's own canonical flat block
  (`Service.installFlat`) when the block's layout is not Lean's.

  Nothing here is trusted: every answer comes from IxC's verified checker over
  declarations the verified fold accepted, and an answer it cannot give is a
  refusal.
-/
module
public import Ix.AuxGen.Oracle
public import Ix.AuxGen.SourceService
public import Ix.AuxGen.LevelEgress
public import Ix.AuxGen.Levels
public import Ix.AuxGen.FastPaths
public section

namespace Ix.AuxGen.Ixc

open Ix.AuxGen.Source (SourceEnv Service renderCheck)

/-- The fuel of one scope chain: operations on a scope and the scopes it
returns. -/
def scopeFuel : Nat := 1000000

/-- The fuel of one oracle chain: flat-block installs. -/
def oracleFuel : Nat := 8

/-! ## Named `whnf` (AuxGen M4)

The recursor generator's `whnf` results reach generated binder names
(`AUXGEN-IXC.md` §1.3, F1–F3), so its answers are spelled as `Ix.Tc`'s
`whnf?` spells them, not decision-grade:
* **nothing reduces** (IxC's result is its input): the input, as `Ix.Tc`'s
  same-content restoration returns it (the source's names and infos, mdata
  dropped, levels as `Ix.Tc`'s ingress builds them: `tcSpelling`);
* **a reduction**: the **named replay** (`replay`), the same head
  reduction redone on the Lean term (delta with the head constant's Lean
  definition, β, `let`), so the definition's own binder names survive;
  accepted only when it ingresses to IxC's result, else refused.
A syntactically stuck head (`stuckHead`), also one after syntactic β-steps
(`betaHead`, AuxGen M5c), answers without the service. -/

/-- A term as `Ix.Tc`'s `whnf` spells it back: mdata dropped, each level
rebuilt as `Ix.Tc`'s ingress builds it (`Egress.normalize`). -/
def tcSpelling : Expr → Expr
  | .mdata _ e _ => tcSpelling e
  | .sort u _ => Expr.mkSort (Egress.normalize u)
  | .const n us _ => Expr.mkConst n (us.map Egress.normalize)
  | .app f a _ => Expr.mkApp (tcSpelling f) (tcSpelling a)
  | .lam n t b bi _ => Expr.mkLam n (tcSpelling t) (tcSpelling b) bi
  | .forallE n t b bi _ => Expr.mkForallE n (tcSpelling t) (tcSpelling b) bi
  | .letE n t v b nd _ => Expr.mkLetE n (tcSpelling t) (tcSpelling v) (tcSpelling b) nd
  | .proj n i e _ => Expr.mkProj n i (tcSpelling e)
  | e => e

/-- The fuel of one named replay (head steps). -/
def replayFuel : Nat := 256

/-- **The named replay**: head steps until none applies, at most `fuel`:
β; `let` (ζ); delta with the head constant's Lean definition, its levels
substituted; a projection of a structure value that replays to a
constructor application (the field). Anything else (a recursor, a literal
operation, a theorem) stops it: `whnfNamedExpr` then finds IxC's result
different and refuses. `none` when the fuel runs out. -/
def replay (get? : Name → Option ConstantInfo) : Nat → Expr → Option Expr
  | 0, _ => none
  | n + 1, e =>
    let (head, args) := decomposeApps (stripMData e)
    match stripMData head with
    | .lam _ _ body _ _ =>
      match args[0]? with
      | some a => replay get? n (mkAppN (instantiate1 body a) (args.extract 1 args.size))
      | none => some e
    | .letE _ _ v b _ _ => replay get? n (mkAppN (instantiate1 b v) args)
    | .const c us _ =>
      match get? c with
      | some (.defnInfo d) => replay get? n (mkAppN (substLevels d.value d.cnst.levelParams us) args)
      | _ => some e
    | .proj _ i x _ =>
      match replay get? n x with
      | some x' =>
        match replayField get? (stripMData x') i with
        | some fld => replay get? n (mkAppN fld args)
        | none => some e
      | none => none
    | _ => some e
where
  /-- Field `i` of a constructor application. -/
  replayField (get? : Name → Option ConstantInfo) (x : Expr) (i : Nat) : Option Expr :=
    let (h, xs) := decomposeApps x
    match stripMData h with
    | .const c _ _ =>
      match get? c with
      | some (.ctorInfo cv) => xs[cv.numParams + i]?
      | _ => none
    | _ => none

/-! ## The scope -/

/-- **A local context over a Source environment.** Locals are numbered by
level, outermost `0`, as IxC's `fvar`s are; `locals[i]` is `.fvar i ty` with
the local's annotated type. -/
structure Scope where
  env : SourceEnv
  lps : Array Name
  fvarLevels : Std.HashMap Name Nat := {}
  locals : Array (Ix.Kernel.Expr .source) := #[]
  /-- each local's name, by level (the egress's free variables) -/
  names : Array Name := #[]
  cs : Ix.Kernel.Cached.CState .source := {}

namespace Scope

def depth (s : Scope) : Nat := s.locals.size

/-- One action of IxC's cached checker over the scope's environment, with the
scope's memo state. -/
def run (s : Scope)
    (act : Ix.Kernel.Cached.CoreFnsI .source → Ix.Kernel.Cached.CheckCM .source α) :
    Except String (α × Scope) :=
  match (act (Ix.Kernel.Cached.coreKnotI .verified s.env.fold.fe Ix.Kernel.checkFuel)).run s.cs with
  | .ok (a, cs) => .ok (a, { s with cs })
  | .error e => .error (renderCheck e)

/-- **A Lean term over the context as an IxC term**: free variables
abstracted, the Source ingress through σ, the loose bound variables
instantiated with the locals. -/
def term (s : Scope) (e : Expr) : Except String (Ix.Kernel.Expr .source) := do
  let n := s.depth
  let closed := batchAbstractWith s.fvarLevels.get? e n 0
  match s.env.ingress s.lps [closed] with
  | .ok [k] => pure (k.instantiateList s.locals.reverse.toList)
  | .ok _ => throw "ingress: arity"
  | .error err => throw s!"ingress: {err}"

/-- Push one local: its domain over the context, annotated at its depth. A
name already in the context is refused. -/
def push1 (s : Scope) (loc : Name × Expr) : Except String Scope := do
  let (name, domain) := loc
  if s.fvarLevels.contains name then throw s!"duplicate free variable {name.pretty}"
  let i := s.depth
  let ty ← s.term domain
  let (ty', s) ← s.run fun r => r.annotate i ty
  pure { s with fvarLevels := s.fvarLevels.insert name i, locals := s.locals.push (.fvar i ty'),
                names := s.names.push name }

/-- Push a telescope, outermost first. -/
def push (s : Scope) (locals : Array (Name × Expr)) : Except String Scope :=
  locals.foldlM push1 s

/-- Pop the most recently pushed `k` locals. -/
def pop (s : Scope) (k : Nat) : Except String Scope := do
  if k > s.depth then throw s!"pop of {k} locals from a context of {s.depth}"
  let keep := s.depth - k
  let fvarLevels := s.fvarLevels.fold (init := {}) fun m name i =>
    if i < keep then m.insert name i else m
  pure { s with fvarLevels, locals := s.locals.extract 0 keep, names := s.names.extract 0 keep }

/-- A context over `lps` with no locals; duplicate level parameters are
refused. -/
def new (env : SourceEnv) (lps : Array Name) : Except String Scope := do
  let mut seen : Std.HashSet Name := {}
  for n in lps do
    if seen.contains n then throw s!"duplicate universe parameter {n.pretty}"
    seen := seen.insert n
  pure { env, lps }

/-- The level of a type by IxC's checker: `annotate`, `infer`, `ensureSort`;
the level as `Ix.Tc` builds it, `levelNormalize`d for a ∀. -/
def slowLevel (s : Scope) (ty : Expr) : Except String (Level × Scope) := do
  let d := s.depth
  let e ← s.term ty
  let (u, s) ← s.run fun r => do
    let e' ← r.annotate d e
    let t ← r.infer d e'
    Ix.Kernel.Cached.ensureSortI r d t
  let l ← (Egress.egressLevel s.lps u).mapError toString
  if ty matches .forallE .. then return (levelNormalize l, s)
  return (l, s)

/-- **The sort level of a type**: the fast path on the head's Lean type, else
IxC's checker. -/
def getLevel (get? : Name → Option ConstantInfo) (s : Scope) (ty : Expr) :
    Except String (Level × Bool × Scope) := do
  if let some l ← fastLevel get? ty then return (l, true, s)
  let (l, s) ← s.slowLevel ty
  return (l, false, s)

/-! ### Terms out, decision-grade (AuxGen M3)

`.brecOn.eq`'s unit-like test reads `inferType?` and `whnf?` results to
decide between `Eq` and `HEq`, and never emits them (the `AuxKernel`
contract's clause 6). So an IxC result goes out as a term that denotes the
same value over the context, and nothing more:
- a free variable is its local's name;
- a constant is its Source key's Lean name (`.id n` as `n`, `.role r` as
  `r`'s Lean name), a fresh name (`Flat.fresh n`: a flat block's member, an
  admitted `.below`) as the `n` it is fresh for, which `term` sends back
  through σ; so the generator's lookups (`lookupConst?` on the head) see the
  names `Ix.Tc` gives; a derived key (`.aux`) is refused;
- levels are spelled as `Ix.Tc` builds them (`Egress.egressLevel`);
- binder names are anonymous, binder information default.
The result re-enters through `term`, as the generator passes `inferType?`'s
answer back to `whnf?` and `isDefEq?`. -/

/-- An IxC name as an `Ix.Name`: `ingressName`'s inverse, with a fresh name's
reserved root dropped (`Flat.fresh`'s inverse; no input name has the root). -/
def egressName : Ix.Kernel.Name → Name
  | .anonymous => Name.mkAnon
  | .str .anonymous s => if s == Flat.freshRoot then Name.mkAnon else Name.mkStr Name.mkAnon s
  | .str p s => Name.mkStr (egressName p) s
  | .num p n => Name.mkNat (egressName p) n

/-- A Source key's Lean name. -/
def egressKey : Ix.Kernel.Key .source → Except String Name
  | .id n => pure (egressName n)
  | .role r => pure (egressName r.leanName)
  | .aux _ _ => throw "egress: a derived key has no Lean name"

/-- **An IxC term over the context as a Lean term**, decision-grade. -/
def egress (s : Scope) : Ix.Kernel.Expr .source → Except String Expr
  | .bvar i => pure (Expr.mkBVar i)
  | .fvar i _ =>
    match s.names[i]? with
    | some n => pure (Expr.mkFVar n)
    | none => throw s!"egress: free variable {i} beyond the context's {s.names.size}"
  | .sort u => return Expr.mkSort (← (Egress.egressLevel s.lps u).mapError toString)
  | .const k us => do
    let us ← us.toArray.mapM fun u => (Egress.egressLevel s.lps u).mapError toString
    return Expr.mkConst (← egressKey k) us
  | .app f a => return Expr.mkApp (← s.egress f) (← s.egress a)
  | .lam t b _ => return Expr.mkLam Name.mkAnon (← s.egress t) (← s.egress b) .default
  | .forallE t b _ => return Expr.mkForallE Name.mkAnon (← s.egress t) (← s.egress b) .default
  | .letE t v b _ =>
    return Expr.mkLetE Name.mkAnon (← s.egress t) (← s.egress v) (← s.egress b) false
  | .lit (.natVal n) => pure (Expr.mkLit (.natVal n))
  | .lit (.strVal str) => pure (Expr.mkLit (.strVal str))
  | .proj k i e => return Expr.mkProj (← egressKey k) i (← s.egress e)

/-- The type of a term, decision-grade: `annotate`, `infer`, out. -/
def inferExpr (s : Scope) (e : Expr) : Except String (Expr × Scope) := do
  let d := s.depth
  let k ← s.term e
  let (t, s) ← s.run fun r => do
    let k' ← r.annotate d k
    r.infer d k'
  return (← s.egress t, s)

/-- The weak head normal form of a term, decision-grade: `annotate`, `whnf`,
out. -/
def whnfExpr (s : Scope) (e : Expr) : Except String (Expr × Scope) := do
  let d := s.depth
  let k ← s.term e
  let (w, s) ← s.run fun r => do
    let k' ← r.annotate d k
    r.whnf d k'
  return (← s.egress w, s)

/-- Definitional equality of two terms: both annotated, then IxC's `defeq`. -/
def defEq (s : Scope) (a b : Expr) : Except String (Bool × Scope) := do
  let d := s.depth
  let ka ← s.term a
  let kb ← s.term b
  s.run fun r => do
    let a' ← r.annotate d ka
    let b' ← r.annotate d kb
    r.defeq d a' b'

/-- **The weak head normal form with names** (AuxGen M4, `OracleScope.whnfNamed`):
the input when IxC does not reduce it, else the named replay when it
ingresses to IxC's result; both spelled as `Ix.Tc` spells its answer. -/
def whnfNamedExpr (get? : Name → Option ConstantInfo) (s : Scope) (e : Expr) :
    Except String (Expr × WhnfHow × Scope) := do
  let d := s.depth
  let k ← s.term e
  let ((k', w), s) ← s.run fun r => do
    let k' ← r.annotate d k
    let w ← r.whnf d k'
    pure (k', w)
  let some rep := replay get? replayFuel e | throw "replay: out of fuel"
  -- No head step applies: IxC must have left the head as it was. (Annotation
  -- ζ-reduces `let`s, so the head's own `let` is a replay step, not this.)
  let unreduced := Ix.Compile.ExactKey.exprEq rep e
  if unreduced && k' == w then return (tcSpelling e, .same, s)
  let (kr', s) ← if unreduced then pure (k', s) else do
    let kr ← s.term rep
    s.run fun r => r.annotate d kr
  if !unreduced && kr' == w then return (tcSpelling rep, .replayed, s)
  let label (x : Expr) : String :=
    match (decomposeApps (stripMData x)).1 with
    | .const n _ _ => n.pretty
    | .fvar n _ => s!"fvar {n.pretty}"
    | .forallE .. => "forall"
    | .lam .. => "lambda"
    | .sort .. => "sort"
    | .proj n i _ _ => s!"proj {n.pretty}.{i}"
    | .letE .. => "let"
    | .lit .. => "literal"
    | _ => "other"
  let ixcHead := match s.egress w with
    | .ok x => label x
    | .error err => s!"(egress: {err})"
  let sameModMeta := match s.egress w, s.egress kr' with
    | .ok a, .ok b => Ix.Compile.ExactKey.exprEq a b
    | _, _ => false
  throw s!"replay: the replayed term is not IxC's whnf (input head {label e}, replay head \
    {label rep}, IxC head {ixcHead}, equal after egress {sameModMeta})"

end Scope

/-- **The scope as an `OracleScope`**, with `fuel` operations left. -/
def ofScope (get? : Name → Option ConstantInfo) : Nat → Scope → OracleScope
  | 0, _ =>
    let out {α} : Except String α := .error "scope fuel exhausted"
    .mk (fun _ => out) (fun _ => out) (fun _ => out) (fun _ => out) (fun _ => out) (fun _ _ => out)
      (fun _ => out)
  | n + 1, s =>
    .mk
      (fun ty => (s.getLevel get? ty).map fun (l, fast, s') => (l, fast, ofScope get? n s'))
      (fun locals => (s.push locals).map (ofScope get? n))
      (fun k => (s.pop k).map (ofScope get? n))
      (fun e => (s.inferExpr e).map fun (t, s') => (t, ofScope get? n s'))
      (fun e => (s.whnfExpr e).map fun (w, s') => (w, ofScope get? n s'))
      (fun a b => (s.defEq a b).map fun (q, s') => (q, ofScope get? n s'))
      (fun e => (s.whnfNamedExpr get? e).map fun (w, how, s') => (w, how, ofScope get? n s'))

/-- The level of a local's type read off its declared domain: `some u` when
`ty` is a local whose domain is syntactically `Sort u` (spelled as `Ix.Tc`
spells it), as `Ix.Tc` infers it. -/
def localLevel (locals : Array (Name × Expr)) (ty : Expr) : Option Level :=
  match stripMData ty with
  | .fvar x _ =>
    match locals.findRev? (Ix.Compile.ExactKey.nameEq ·.1 x) with
    | some (_, d) =>
      match stripMData d with
      | .sort u _ => some (Egress.normalize u)
      | _ => none
    | none => none
  | _ => none

/-- A lookup that reads `overlay` before `get?` (AuxGen M5c: the recursor
generator's overlay before the input, as the generator's own `envGet`). -/
def overlaid (overlay get? : Name → Option ConstantInfo) (n : Name) : Option ConstantInfo :=
  (overlay n).orElse fun _ => get? n

/-- **A lazy scope** (AuxGen M4): the scope a thunk gives, built only when a
question escapes the fast paths, which need only the input's declarations
(`get?`; on the recursor route the generator's overlay first, `overlaid`):
the `inferAppType` level (`fastLevel`) and a syntactically stuck `whnf`
(`stuckHead`), also after syntactic β-steps at the head (`betaHead`, AuxGen
M5c: a β-redex whose reduct has a stuck head is answered by that reduct,
spelled as the named replay spells it, `WhnfHow.beta`). A local whose domain
is syntactically a sort has that sort's level (`localLevel`; `ls`: the locals
pushed so far, outermost first). Pushes and pops compose the thunk. A refusal
(the service's, or a local's annotation) surfaces at the question that forces
it. -/
def ofLazy (get? : Name → Option ConstantInfo) :
    Nat → Array (Name × Expr) → Thunk (Except String Scope) → OracleScope
  | 0, _, _ =>
    let out {α} : Except String α := .error "scope fuel exhausted"
    .mk (fun _ => out) (fun _ => out) (fun _ => out) (fun _ => out) (fun _ => out) (fun _ _ => out)
      (fun _ => out)
  | n + 1, ls, t =>
    .mk
      (fun ty => match fastLevel get? ty with
        | .ok (some l) => .ok (l, true, ofLazy get? n ls t)
        | _ =>
          match localLevel ls ty with
          | some l => .ok (l, true, ofLazy get? n ls t)
          | none => do
            let (l, fast, s') ← (← t.get).getLevel get? ty
            pure (l, fast, ofScope get? n s'))
      (fun locals => .ok (ofLazy get? n (ls ++ locals) (Thunk.mk fun _ => do (← t.get).push locals)))
      (fun k => .ok (ofLazy get? n (ls.extract 0 (ls.size - k)) (Thunk.mk fun _ => do (← t.get).pop k)))
      (fun e => do
        let (ty, s') ← (← t.get).inferExpr e
        pure (ty, ofScope get? n s'))
      (fun e =>
        if stuckHead get? e then .ok (e, ofLazy get? n ls t)
        else
          let r := betaHead betaFuel e
          if stuckHead get? r then .ok (r, ofLazy get? n ls t)
          else do
            let (w, s') ← (← t.get).whnfExpr e
            pure (w, ofScope get? n s'))
      (fun a b => do
        let (q, s') ← (← t.get).defEq a b
        pure (q, ofScope get? n s'))
      (fun e =>
        if stuckHead get? e then .ok (tcSpelling e, .stuck, ofLazy get? n ls t)
        else
          -- the named replay's first steps (`replay`): β, then a stuck head
          -- stops it, so its answer is the reduct's spelling
          let r := betaHead betaFuel e
          if stuckHead get? r then .ok (tcSpelling r, .beta, ofLazy get? n ls t)
          else do
            let (w, how, s') ← (← t.get).whnfNamedExpr get? e
            pure (w, how, ofScope get? n s'))

/-! ## The oracle -/

/-- The block's own canonical flat block, installed when its layout is not
Lean's: the service after it, or `none`. The flat block is built as the
fixture test builds it (`Flat.build` over the input's lookups and the σ of
the blocks installed before), and lowered and installed by the service
(`Service.installFlat`); a refusal is an error naming its reason. -/
def installOwnFlat (svc : Service) (classes : Array (Array Name)) (originalAll : Array Name)
    (canonicalRecs : Array (Name × RecursorVal)) : Except String (Option Service) := do
  let nClasses := classes.size
  let auxNames := (canonicalRecs.extract nClasses canonicalRecs.size).map (·.1)
  let leanNested := match originalAll[0]?.bind svc.input.get? with
    | some (.inductInfo v) => v.numNested
    | _ => 0
  unless Flat.needed classes originalAll auxNames leanNested do return none
  let fb ← (Flat.build svc.input.get? classes canonicalRecs svc.sigma).mapError (·.render)
  let svc := svc.installFlat fb
  match svc.flatStatus? (fb.firstName.getD default) with
  | some .accepted => return some svc
  | some (.refused why) => throw s!"flat block refused: {why}"
  | _ => throw "flat block not recorded"

/-- The block's generated Type-level `.below` definitions made visible
(AuxGen M3, the `AuxKernel` contract's clause 9), on the block's copy of
the service: each admitted through σ under its fresh name
(`Service.admitDefinition`), as `Ix.Tc`'s kenv takes the generated
definition at its name. The service after them, and how many were admitted
and refused. -/
def admitBelowIn (svc : Service) (defs : Array BelowDef) : Service × Nat × Nat := Id.run do
  let mut svc := svc
  let mut ok := 0
  let mut bad := 0
  for d in defs do
    let (svc', st) := svc.admitDefinition d.name d.levelParams d.typ d.value (thm := false)
    svc := svc'
    if st.isAccepted then ok := ok + 1 else bad := bad + 1
  return (svc, ok, bad)

/-- **The block's facts the oracle carries besides its service** (AuxGen
M4): whether the recursor generator asks IxC (`recursors`), whether the
run-ahead asked for the block (`asked`), and the input's declarations
(`lookup`), which the lazy scopes' fast paths read without the service. -/
structure OracleFacts where
  recursors : Bool := false
  asked : Bool := true
  lookup : Name → Option ConstantInfo := fun _ => none
  /-- the block's members: a lazy scope over a block the service did not
  accept says why -/
  members : Array Name := #[]

instance : Inhabited OracleFacts := ⟨{}⟩

/-- A generated family of inductives (with constructors and generated
recursors) installed as a block under fresh names through σ (AuxGen M5: a
regenerated Prop-level `.below` family): built as a canonical flat block is
(`Flat.build`, over the family's own declarations and the input's), so
IxC's install checks it, recursors included. The service after it, or the
reason it was refused. -/
def installFamily (svc : Service) (types : Array (InductiveVal × Array ConstructorVal))
    (recs : Array (Name × RecursorVal)) : Except String Service := do
  let own (n : Name) : Option ConstantInfo :=
    match types.find? (fun (v, _) => Ix.Compile.ExactKey.nameEq v.cnst.name n) with
    | some (v, _) => some (.inductInfo v)
    | none => (types.findSome? fun (_, cs) =>
        cs.find? fun c => Ix.Compile.ExactKey.nameEq c.cnst.name n).map .ctorInfo
  let lookup (n : Name) : Option ConstantInfo := (own n).orElse fun _ => svc.input.get? n
  let classes := types.map fun (v, _) => #[v.cnst.name]
  let fb ← (Flat.build lookup classes recs svc.sigma).mapError (·.render)
  let svc := svc.installFlat fb
  match svc.flatStatus? (fb.firstName.getD default) with
  | some .accepted => return svc
  | some (.refused why) => throw s!"family refused: {why}"
  | _ => throw "family not recorded"

/-- **Generated declarations accepted by Source mode**, in order, each later one
seeing the earlier ones through σ (AuxGen M5): a definition or theorem
through `Service.admitDefinition` under its fresh name, a family through
`installFamily`. The service after them, and each declaration's verdict
(`none` accepted, `some` the reason). -/
def admitGeneratedIn (svc : Service) (decls : Array GeneratedDecl) :
    Service × Array (Name × Option String) := Id.run do
  let mut svc := svc
  let mut out : Array (Name × Option String) := #[]
  for d in decls do
    match d with
    | .defn name lps ty v thm =>
      let (svc', st) := svc.admitDefinition name lps ty v thm
      svc := svc'
      let why : Option String := match st with
        | .accepted => none
        | .refused r => some r
        | .blocked _ => some "blocked"
        | .pending => some "pending"
      out := out.push (name, why)
    | .family types recs =>
      match installFamily svc types recs with
      | .ok svc' =>
        svc := svc'
        for (v, _) in types do out := out.push (v.cnst.name, none)
      | .error why =>
        for (v, _) in types do out := out.push (v.cnst.name, some why)
  return (svc, out)

/-- **Why a block's own groups are not accepted in Source mode**, if they are
not (AuxGen M5b, `AuxOracle.blockStatus`): `Source.Run.blockReason?`, with a
blocking group's own reason, so the reason names the root cause (e.g.
`blocked behind BEq (ingress: declined: inductive block without a recursor in
the input)`). -/
def blockStatus? (svc : Service) (members : Array Name) : Option String :=
  members.findSome? fun n => match svc.statusOf? n with
    | some (.refused why) => some s!"refused ({why})"
    | some (.blocked root) =>
      let entry := svc.entries[root]?
      let rootName := (entry.map (·.name)).getD (.id .anonymous)
      let rootWhy := match entry.map (·.status) with
        | some (.refused why) => s!" ({why})"
        | _ => ""
      some s!"blocked behind {rootName}{rootWhy}"
    | some .pending => some "not folded"
    | _ => none

/-- **One block's oracle** over a service, given lazily (`svc ()` is asked at
the first question; the drivers' snapshot is a task), in `mode` (tracing the
tail's counts under `trace`), with `fuel` installs left (the flat block, the
generated `.below`). `retry` is the block's oracle in `fallback` (AuxGen M5c,
`AuxOracle.retry`): `none` on the oracles an install returns. -/
def oracleOf (mode : IxcMode) (trace : Bool) (facts : OracleFacts)
    (retry : Option AuxOracle) : Nat → (Unit → Except String Service) → AuxOracle
  | 0, _ =>
    .mk mode trace (fun _ _ => .error "oracle fuel exhausted")
      (fun _ _ _ => .error "oracle fuel exhausted") (fun _ => .error "oracle fuel exhausted")
      facts.recursors facts.asked
      (fun overlay _ locals =>
        ofLazy (overlaid overlay facts.lookup) scopeFuel locals (Thunk.pure (.error "oracle fuel exhausted")))
      (fun _ => .error "oracle fuel exhausted")
      (fun _ => some "oracle fuel exhausted") retry
  | n + 1, svc =>
    .mk mode trace
      (fun lps locals => do
        let svc ← svc ()
        let s ← Scope.new svc.env lps
        let s ← s.push locals
        pure (ofScope svc.input.get? scopeFuel s))
      (fun classes originalAll canonicalRecs => do
        let svc ← svc ()
        match ← installOwnFlat svc classes originalAll canonicalRecs with
        | none => pure none
        | some svc' => pure (some (oracleOf mode trace facts none n fun _ => .ok svc')))
      (fun defs => do
        let svc ← svc ()
        let (svc', ok, bad) := admitBelowIn svc defs
        pure (oracleOf mode trace facts none n fun _ => .ok svc', ok, bad))
      facts.recursors facts.asked
      (fun overlay lps locals =>
        ofLazy (overlaid overlay facts.lookup) scopeFuel locals (Thunk.mk fun _ => do
          let svc ← svc ()
          if let some why := Source.Run.blockReason? svc facts.members then
            throw s!"the block is not accepted in Source mode: {why}"
          let s ← Scope.new svc.env lps
          s.push locals))
      (fun decls => do
        let (s', verdicts) := admitGeneratedIn (← svc ()) decls
        pure (oracleOf mode trace facts none n fun _ => .ok s', verdicts))
      (fun _ => match svc () with
        | .ok s => blockStatus? s facts.members
        | .error e => some s!"no service: {e}")
      retry

/-- **One block's oracle over the snapshot `run`** (a run of the drivers'
service), with the block's `members` folded first (`Service.ensureNames`): a
no-op when the run asked for the block, and otherwise its groups and what they
depend on, folded on this block's copy of the snapshot, so a block the asks
did not select is still answered. The service is taken once, at the first
question, and shared by the block's scopes. `trace`: the tail traces its
counts; `facts`: AuxGen M4's (production: recursors on `Ix.Tc`). Its `retry`
(AuxGen M5c) is the same block's oracle in `fallback` over the same service
value (built as closures; nothing is asked unless the tail re-runs), so a
re-run costs no second fold. -/
def oracleOfRun (mode : IxcMode) (trace : Bool) (run : Unit → Source.Run) (members : Array Name)
    (facts : OracleFacts := {}) : AuxOracle :=
  let svc : Thunk (Except String Service) :=
    Thunk.mk fun _ => (run ()).service.map (·.ensureNames members)
  let facts := { facts with members }
  let retry := oracleOf .fallback trace facts none oracleFuel fun _ => svc.get
  oracleOf mode trace facts (some retry) oracleFuel fun _ => svc.get

end Ix.AuxGen.Ixc

end
