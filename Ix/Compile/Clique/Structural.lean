/-
  Ix.Compile.Clique.Structural: transport of a structural clique (design
  document §5.3), the steps (R) and (A); structural recursion has no (S) and
  no (G).

  Lean's encoding (`Elab/PreDefinition/Structural`, Lean 4.34.1), as the
  transport sees it:

  * the functions are grouped by the type former of their recursive argument
    (`Positions.groupAndSort`); the groups follow the inductive's `all` order
    (nested auxiliaries included), and **within a group the functions are in
    clique order** — the only place the clique order enters;
  * per type former, the packed motive `λ is x. R₀ ×' (R₁ ×' …)` (`PProd`, or
    `And` for propositions; the motive itself for a singleton group) is passed
    to `T.brecOn`/`T.below` (`PProdN.packLambdas`);
  * each function's functional `f._f : ∀ fixed is x (f : T.below … x) …`,
    whose body reaches a recursive call through a path into the `below`
    dictionary (`searchPProd`): a prefix that walks the inductive's `below`
    structure, then the position inside the packed motive;
  * the members `f := λ ys. (T.brecOn ps motives is x F₁ … F_K).2.1 rest`,
    `F_k = λ is x f. ⟨g₀._f fixed is x f, …⟩` the packed functionals;
  * for an inductive predicate (IndPred route), `let funType_i := …` in clique
    order around the body, and "below" matchers taking the `funType` binders
    in clique order;
  * the fixed parameters in the first function's order (in every `_f`).

  `Φ_σ` re-associates, per group `k` (with `σ_k`, the restriction of `σ`):
  the packed motives at the motive positions of every `below`/`brecOn`
  application of the block, the packed functionals at `brecOn`'s functional
  positions, the members' projections out of `brecOn`, and the motive-part of
  every path into a `below` dictionary — found, as Lean finds it, by reducing
  the dictionary's type with canaries in place of the packed motives
  (`Whnf.lean`); a path through a reflexive field `f : A → T` applies the
  field's entry to the argument in the middle of the path, and the walk
  instantiates the entry's `∀` there, as `toBelowAux` does. The `let funType`
  telescope and the "below" matchers' binders
  are reordered, the `_f` telescopes too (O13a, O13b). Nothing else moves: the
  prefix of a path, the bodies, the matchers' alternatives, `recArgPos` (D22).

  Unsupported shapes are outside the grammar and leave the clique in Lean's
  form (§5.3: the fallback is the baseline): a dictionary passed whole to a
  helper other than a matcher, a path the walk cannot follow, a projection
  of a `brecOn` result that is not a full path.
-/
module
public import Ix.Compile.Clique.Packing
public import Ix.Compile.Clique.Telescope
public import Ix.Compile.Clique.Whnf
public import Ix.Compile.Clique.WF
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata instantiateRev)

/-- A `below` or `brecOn` constant of the block. -/
structure BlockAux where
  /-- the motive position (type former, nested auxiliaries after `all`) -/
  pos : Nat
  isBrecOn : Bool
  deriving Inhabited

/-- The functions recursing on one type former. -/
structure Group where
  /-- Lean member indices, in Lean's group order -/
  members : Array Nat := #[]
  /-- the motive's binders (indices and major) -/
  arity : Nat := 0
  /-- Lean's packed motive (when `N ≥ 2`), its leaves under `arity` binders -/
  spine : Spine := default
  /-- Lean group position ↦ canonical group position -/
  perm : Array Nat := #[]
  deriving Inhabited

def Group.size (g : Group) : Nat := g.members.size

/-- The canonical packed-motive spine (for the projections' structure names). -/
def Group.canonSpine (g : Group) : Spine := g.spine.permute g.perm

structure StructLayout where
  n : Nat
  sigma : Array Nat
  const? : Name → Option ConstantInfo
  numParams : Nat
  numMotives : Nat
  aux : Std.HashMap Name BlockAux
  groups : Array Group
  fNames : Std.HashSet Name
  numFixed : Nat
  fixedPerm : Array Nat
  matchers : Std.HashSet Name := {}
  /-- IndPred: the number of `funType` lets (`n`), else `0` -/
  numFunTypes : Nat := 0
  deriving Inhabited

/-- new position `p` ↦ Lean position, for the `funType` telescope. -/
def StructLayout.funPerm (L : StructLayout) : Array Nat := invPerm L.sigma

/-! ## Paths -/

/-- The projection chain around `e`: steps innermost first, and the base. -/
def projChain : Expr → Array (Name × Nat) × Expr
  | .proj s i x _ => let (st, b) := projChain x; (st.push (s, i), b)
  | .mdata _ x _ => projChain x
  | e => (#[], e)

/-- A path to a component of an `n`-component product at the start of
`steps`: the component and the number of steps it takes (`PProdN.proj`). -/
def pathPrefix (n : Nat) (steps : Array (Name × Nat)) : Option (Nat × Nat) :=
  if n < 2 then some (0, 0) else
  let k := (steps.takeWhile (·.2 == 1)).size
  if k + 1 < n then
    if h : k < steps.size then (if steps[k].2 == 0 then some (k, k + 1) else none) else none
  else some (n - 1, n - 1)

/-- The structure names of `steps` must be those of the spine's nodes. -/
def stepsFit (s : Spine) (idx : Nat) (steps : Array (Name × Nat)) : Bool :=
  (s.projSteps idx).map (·.1) == steps.map (·.1)

/-- Re-associate the start of `steps` (a path into group `g`'s packed
motive) and keep the rest. -/
def transportPath (g : Group) (steps : Array (Name × Nat)) : Except String (Array (Name × Nat)) := do
  if g.size < 2 then return steps
  let some (idx, len) := pathPrefix g.size steps | throw "grammar: a projection of a packed value that is not a path"
  let part := steps.extract 0 len
  unless stepsFit g.spine idx part do throw "grammar: a path whose projections are not the packing's"
  return g.canonSpine.projSteps g.perm[idx]! ++ steps.extract len steps.size

/-- One step of a path into a `below` dictionary: a projection, or (through
a reflexive field `f : A → T`, whose dictionary entry is a function) an
application to an argument. -/
inductive PStep where
  | proj (s : Name) (i : Nat)
  | app (a : Expr)
  deriving Inhabited

/-- The chain of projections and applications around `e`: steps innermost
first, and the base. -/
def pathChain : Expr → Array PStep × Expr
  | .proj s i x _ => let (st, b) := pathChain x; (st.push (.proj s i), b)
  | .app f a _ => let (st, b) := pathChain f; (st.push (.app a), b)
  | .mdata _ x _ => pathChain x
  | e => (#[], e)

def applySteps (steps : Array PStep) (e : Expr) : Expr :=
  steps.foldl (init := e) fun acc st => match st with
    | .proj s i => Expr.mkProj s i acc
    | .app a => Expr.mkApp acc a

/-- The maximal prefix of projections, and the rest. -/
def projPrefix (steps : Array PStep) : Array (Name × Nat) × Array PStep := Id.run do
  let mut acc := #[]
  for i in [0:steps.size] do
    match steps[i]! with
    | .proj s j => acc := acc.push (s, j)
    | .app _ => return (acc, steps.extract i steps.size)
  return (acc, #[])

/-- The motive-part of a path into a `below` dictionary of type `ty`:
replay Lean's `searchPProd` and `toBelowAux` (`Structural/BRecOn.lean`) with
canaries for the packed motives. The walk follows the `PProd`/`And` nodes of
the dictionary's weak head normal form, and passes through a reflexive
field's entry (a `∀`) by instantiating it at the path's argument, until it
reaches an entry `C_j t`; the projections that follow select the function
inside group `j`'s packed motive and are re-associated. `none` when the
steps end inside the dictionary before any entry (a part of the dictionary,
independent of the clique). A step the walk cannot follow (a weak head normal
form that is neither a node nor a `∀`, or another structure than the node's)
is a grammar failure: such a path might reach into the packed motives in a
way the walk does not see, so it is never left alone. -/
def belowPath (L : StructLayout) (ty : Expr) (steps : Array PStep) :
    TM (Option (Array PStep)) := do
  let some (c, us, args) := constApp? ty | return none
  let some a := L.aux.get? c | return none
  if a.isBrecOn || args.size < L.numParams + L.numMotives then return none
  -- the canaries
  let mut cans : Array Name := #[]
  let mut args' := args
  for j in [0:L.numMotives] do
    let f ← freshFVar
    cans := cans.push f
    args' := args'.set! (L.numParams + j) (Expr.mkFVar f)
  let mut cur := mkAppN (Expr.mkConst c us) args'
  for t in [0:steps.size] do
    let w := whnf L.const? whnfFuel cur
    match steps[t]! with
    | .proj s i =>
      match decodeNode .pprod w with
      | some (_, _, a, b) =>
        let isAnd := match constApp? w with
          | some (h, _, _) => h == nAnd
          | none => false
        unless (s == nAnd) == isAnd do
          throw "grammar: a projection into a below dictionary whose structure is not the node's"
        cur := if i == 0 then a else b
      | none => throw "grammar: a projection into a below dictionary that the walk cannot follow"
    | .app x =>
      match stripMdata w with
      | .forallE _ _ b _ _ => cur := instantiateRev b #[x]
      | _ => throw "grammar: an application inside a below dictionary that the walk cannot follow"
    -- an entry of the dictionary: a canary applied
    match getAppFnArgs (stripMdata cur) with
    | (.fvar f _, _) =>
      match cans.idxOf? f with
      | some j =>
        let g := L.groups[j]!
        let (projs, tail) := projPrefix (steps.extract (t + 1) steps.size)
        let projs' ← liftE (transportPath g projs)
        return some (steps.extract 0 (t + 1) ++ projs'.map (fun (s, i) => PStep.proj s i) ++ tail)
      | none => throw "grammar: a path into a below dictionary that reaches a foreign variable"
    | _ => pure ()
  return none

/-! ## `Φ_σ` -/

/-- One step of `Φ_σ` on a structural clique's term, in a context of binder
types (Lean's, outermost first); `go ctx` is `Φ_σ` on subterms. -/
def phiSStep (L : StructLayout) (go : Array Expr → Expr → TM Expr) (ctx : Array Expr)
    (e : Expr) : TM Expr := do
  let underBinders (n : Nat) (lam : Bool) (x : Expr) (k : Array Expr → Expr → TM Expr) :
      TM Expr := do
    -- transform `n` leading binders of `x` and the body with `k`
    let (bs, body) := if lam then peelLams n x #[] else
      let (bs, b) := Ix.Compile.Canon.peelForalls n x #[]; (bs, b)
    let mut ctx' := ctx
    let mut bs' := #[]
    for (nm, t, bi) in bs do
      bs' := bs'.push (nm, ← go ctx' t, bi)
      ctx' := ctx'.push t
    let body' ← k ctx' body
    return if lam then mkLams bs' body' else Ix.Compile.Canon.mkForalls bs' body'
  -- the packed motive at motive position `j`
  let motive (j : Nat) (arg : Expr) : TM Expr := do
    let g := L.groups[j]!
    if g.size < 2 then return ← go ctx arg
    underBinders g.arity true arg fun ctx' body => do
      let some s := decodeSpine .pprod g.size body
        | throw "grammar: a packed motive that is not Lean's"
      let leaves ← s.leaves.mapM (go ctx')
      return ({ s with leaves }.permute g.perm).type
  -- the packed functional at functional position `j`
  let functional (j : Nat) (arg : Expr) : TM Expr := do
    let g := L.groups[j]!
    if g.size < 2 then return ← go ctx arg
    underBinders (g.arity + 1) true arg fun ctx' body => do
      let some (s, cs) := decodeTuple g.size body
        | throw "grammar: a packed functional that is not Lean's"
      let leaves ← s.leaves.mapM (go ctx')
      let cs ← cs.mapM (go ctx')
      return mkTuple ({ s with leaves }.permute g.perm) (permute g.perm cs)
  match e with
  | .proj .. =>
    -- a path of projections and applications from a variable: a path into a
    -- `below` dictionary when the variable is one (the applications are a
    -- reflexive field's arguments, transported as terms)
    let (gsteps, gbase) := pathChain e
    if let .bvar i _ := stripMdata gbase then
      if h : i < ctx.size then
        let ty := liftLoose ctx[ctx.size - 1 - i] (i + 1)
        match ← belowPath L ty gsteps with
        | some steps' =>
          let steps'' ← steps'.mapM fun st => do match st with
            | .app a => return PStep.app (← go ctx a)
            | s => return s
          return applySteps steps'' gbase
        | none => pure ()
    let (steps, base) := projChain e
    match stripMdata base with
    | .bvar _ _ => return applyProjs steps base
    | base' =>
      let isBrecOn : Bool := match constApp? base' with
        | some (c, _, _) => match L.aux.get? c with | some a => a.isBrecOn | none => false
        | none => false
      let b ← go ctx base'
      if isBrecOn then
        let some (c, _, _) := constApp? base' | return applyProjs steps b
        let some a := L.aux.get? c | return applyProjs steps b
        let steps' ← liftE (transportPath L.groups[a.pos]! steps)
        return applyProjs steps' b
      return applyProjs steps b
  | .app .. =>
    let (h, args) := getAppFnArgs e
    match h with
    | .const c _ _ =>
      if let some a := L.aux.get? c then
        let P := L.numParams
        let K := L.numMotives
        let g := L.groups[a.pos]!
        let fStart := P + K + g.arity
        let mut args' := #[]
        for i in [0:args.size] do
          let x := args[i]!
          if P ≤ i && i < P + K then args' := args'.push (← motive (i - P) x)
          else if a.isBrecOn && fStart ≤ i && i < fStart + K then
            args' := args'.push (← functional (i - fStart) x)
          else args' := args'.push (← go ctx x)
        return mkAppN h args'
      if L.fNames.contains c then
        if args.size < L.numFixed then throw "grammar: a partial application of a functional"
        let args' ← args.mapM (go ctx)
        return mkAppN h (L.fixedPerm.map (args'[·]!) ++ args'.extract L.numFixed args'.size)
      if L.matchers.contains c then
        let m := L.numFunTypes
        if args.size < m then throw "grammar: a partial application of a below matcher"
        let args' ← args.mapM (go ctx)
        return mkAppN h (L.funPerm.map (args'[·]!) ++ args'.extract m args'.size)
      return mkAppN h (← args.mapM (go ctx))
    | _ => return mkAppN (← go ctx h) (← args.mapM (go ctx))
  | .const c _ _ =>
    if L.fNames.contains c && L.numFixed > 0 then throw "grammar: a bare functional"
    if L.matchers.contains c && L.numFunTypes > 0 then throw "grammar: a bare below matcher"
    return e
  | .lam nm t b bi _ => return Expr.mkLam nm (← go ctx t) (← go (ctx.push t) b) bi
  | .forallE nm t b bi _ => return Expr.mkForallE nm (← go ctx t) (← go (ctx.push t) b) bi
  | .letE nm t v b nd _ =>
    return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push t) b) nd
  | .mdata d x _ => return Expr.mkMData d (← go ctx x)
  | _ => return e

/-- `Φ_σ` with a context, memoised by the term and the context's hash. -/
def phiSFix (L : StructLayout) : Nat → Array Expr → UInt64 → Expr → TM Expr
  | 0, _, _, _ => throw "Φ: recursion bound exhausted"
  | fuel + 1, ctx, hctx, e => do
    let key := mixHash (hash e) hctx
    if let some (e', ctx', r) := (← get).cacheCtx.get? key then
      if e' == e && ctx' == ctx then return r
    let go (ctx' : Array Expr) (x : Expr) : TM Expr :=
      phiSFix L fuel ctx' (ctx'.foldl (fun h t => mixHash h (hash t)) 7) x
    let r ← phiSStep L go ctx e
    modify fun st => { st with cacheCtx := st.cacheCtx.insert key (e, ctx, r) }
    return r

def phiS (L : StructLayout) (ctx : Array Expr) (e : Expr) : TM Expr :=
  phiSFix L defaultFuel ctx (ctx.foldl (fun h t => mixHash h (hash t)) 7) e

/-! ## The layout -/

/-- The block of a `brecOn` constant: its `below`/`brecOn` constants by
motive position, the number of parameters and motives, each position's
motive arity. -/
def blockOf (const? : Name → Option ConstantInfo) (brecOn : Name) :
    Except String (Std.HashMap Name BlockAux × Nat × Nat × Array Nat) := do
  let ind := match brecOn with
    | .str p _ _ => p
    | n => n
  let some (.inductInfo iv) := const? ind | throw s!"{brecOn}: not the brecOn of an inductive"
  let all := iv.all
  let K := all.size + iv.numNested
  let mut aux : Std.HashMap Name BlockAux := {}
  let mut arities := #[]
  for j in [0:K] do
    let (below, brec, recN) :=
      if j < all.size then
        (Ix.Name.mkStr all[j]! "below", Ix.Name.mkStr all[j]! "brecOn", Ix.Name.mkStr all[j]! "rec")
      else
        let k := j - all.size + 1
        (Ix.Name.mkStr all[0]! s!"below_{k}", Ix.Name.mkStr all[0]! s!"brecOn_{k}",
          Ix.Name.mkStr all[0]! s!"rec_{k}")
    aux := aux.insert below { pos := j, isBrecOn := false }
    aux := aux.insert brec { pos := j, isBrecOn := true }
    let some (.recInfo r) := const? recN | throw s!"{recN}: no recursor"
    arities := arities.push (r.numIndices + 1)
  return (aux, iv.numParams, K, arities)

/-- Peel leading `let`s. -/
def peelLets : Nat → Expr → Array (Name × Expr × Expr) → Array (Name × Expr × Expr) × Expr
  | 0, e, acc => (acc, e)
  | n + 1, e, acc =>
    match stripMdata e with
    | .letE nm t v b _ _ => peelLets n b (acc.push (nm, t, v))
    | e' => (acc, e')

def letArity : Expr → Nat
  | .letE _ _ _ b _ _ => letArity b + 1
  | .mdata _ e _ => letArity e
  | _ => 0

/-- A member's shape: `λ ys. let … ; (projs (brecOn …)) rest`. -/
structure MemberShape where
  lams : Nat
  lets : Nat
  brecOnName : Name
  /-- the `brecOn` application's arguments -/
  brecArgs : Array Expr
  steps : Array (Name × Nat)
  deriving Inhabited

def memberShape (d : Decl) : Except String MemberShape := do
  let (ps, b1) := peelLams (lamArity d.value) d.value #[]
  let (ls, b2) := peelLets (letArity b1) b1 #[]
  let (h, _) := getAppFnArgs (stripMdata b2)
  -- `(projs (brecOn …)) rest`, or the `brecOn` application itself
  let (steps, base) := match stripMdata h with
    | .proj .. => projChain h
    | _ => (#[], stripMdata b2)
  let some (c, _, args) := constApp? base | throw s!"member {d.name}: not a brecOn application"
  return { lams := ps.size, lets := ls.size, brecOnName := c, brecArgs := args, steps }

/-- Remap the loose variables `bvar k`, `k < n`, of `e` to `bvar (f k)`. -/
def remapLoose (n : Nat) (f : Nat → Nat) (e : Expr) : Expr := go e 0
where
  go : Expr → Nat → Expr
    | .bvar i _, d => if d ≤ i && i < d + n then Expr.mkBVar (d + f (i - d)) else Expr.mkBVar i
    | .app g a _, d => Expr.mkApp (go g d) (go a d)
    | .lam nm t b bi _, d => Expr.mkLam nm (go t d) (go b (d + 1)) bi
    | .forallE nm t b bi _, d => Expr.mkForallE nm (go t d) (go b (d + 1)) bi
    | .letE nm t v b nd _, d => Expr.mkLetE nm (go t d) (go v d) (go b (d + 1)) nd
    | .proj s i x _, d => Expr.mkProj s i (go x d)
    | .mdata m x _, d => Expr.mkMData m (go x d)
    | e, _ => e

/-- Reorder a telescope of independent `let`s (`perm[p]` = old let at new
position `p`) and re-index the body; the values must not mention earlier
lets (Lean's `funType_i`, `IndPred.lean`'s `withFunTypes`). -/
def reorderLets (perm : Array Nat) (ls : Array (Name × Expr × Expr)) (body : Expr) :
    Except String (Array (Name × Expr × Expr) × Expr) := do
  let n := ls.size
  let mut closed := #[]
  for i in [0:n] do
    let (nm, t, v) := ls[i]!
    let some t' := lower? t i | throw "a let type mentions an earlier let"
    let some v' := lower? v i | throw "a let value mentions an earlier let"
    closed := closed.push (nm, t', v')
  let inv := invPerm perm
  let ls' := (List.range n).toArray.map fun p =>
    let (nm, t, v) := closed[perm[p]!]!
    (nm, liftLoose t p, liftLoose v p)
  -- old let `i` is `bvar (n-1-i)`; it becomes `bvar (n-1-inv[i])`
  let body' := remapLoose n (fun k => n - 1 - inv[n - 1 - k]!) body
  return (ls', body')

def mkLets (ls : Array (Name × Expr × Expr)) (body : Expr) : Expr :=
  ls.foldr (init := body) fun (nm, t, v) acc => Expr.mkLetE nm t v acc false

/-- The structural layout of a clique from its members (Lean's order). -/
def structLayout (members : Array Decl) (aux : Array Decl) (σ : Array Nat)
    (const? : Name → Option ConstantInfo) : Except String StructLayout := do
  let n := members.size
  unless n ≥ 2 && σ.size == n && isPerm σ do throw "structLayout: bad permutation"
  let shapes ← members.mapM memberShape
  let (blockAux, P, K, arities) ← blockOf const? shapes[0]!.brecOnName
  let poss ← shapes.mapM fun s => match blockAux.get? s.brecOnName with
    | some a => if a.isBrecOn then pure a.pos else throw "structLayout: not a brecOn"
    | none => throw "structLayout: members over different blocks"
  let matchers : Std.HashSet Name := aux.foldl (init := {}) fun s d =>
    match d.name with
    | .str _ str _ => if str.startsWith "match_" then s.insert d.name else s
    | _ => s
  -- groups
  let mut groups : Array Group := (List.range K).toArray.map fun j =>
    { members := (List.range n).toArray.filter (poss[·]! == j), arity := arities[j]! }
  for j in [0:K] do
    let g := groups[j]!
    if g.size ≥ 2 then
      let some motive := shapes[0]!.brecArgs[P + j]? | throw "structLayout: missing motive"
      let (_, body) := peelLams g.arity motive #[]
      let some s := decodeSpine .pprod g.size body | throw "structLayout: a packed motive that is not Lean's"
      let ranks := g.members.map fun i => σ[i]!
      let perm := (List.range g.size).toArray.map fun a =>
        (ranks.filter (· < ranks[a]!)).size
      groups := groups.set! j { g with spine := s, perm }
    else groups := groups.set! j { g with perm := idPerm g.size }
  -- each member projects its own position
  for i in [0:n] do
    let g := groups[poss[i]!]!
    let a := (g.members.idxOf? i).getD 0
    if g.size ≥ 2 then
      match pathPrefix g.size shapes[i]!.steps with
      | some (idx, len) =>
        unless idx == a && len == shapes[i]!.steps.size && stepsFit g.spine idx shapes[i]!.steps do
          throw s!"structLayout: member {i} does not project its clique position"
      | none => throw s!"structLayout: member {i} does not project its clique position"
  -- the functionals and the fixed parameters
  let mut fNames : Std.HashSet Name := {}
  let mut qss : Array (Array Nat) := #[]
  for i in [0:n] do
    let sh := shapes[i]!
    let fStart := P + K + arities[poss[i]!]!
    let mut q? : Option (Array Nat) := none
    for j in [0:K] do
      let g := groups[j]!
      if g.size == 0 then continue
      let some f := sh.brecArgs[fStart + j]? | throw "structLayout: missing functional"
      let depth := min (lamArity f) (g.arity + 1)
      let (_, body) := peelLams depth f #[]
      let comps ← if g.size ≥ 2 then
          match decodeTuple g.size body with
          | some (_, cs) => pure cs
          | none => throw "structLayout: a packed functional that is not Lean's"
        else pure #[body]
      for c in comps do
        let some (h, _, args) := constApp? c | throw "structLayout: a functional that is not a constant"
        if matchers.contains h then continue
        fNames := fNames.insert h
        unless args.size ≥ depth do throw "structLayout: a functional applied to too few arguments"
        let m := args.size - depth
        let mut q := #[]
        for x in args.extract 0 m do
          match stripMdata x with
          | .bvar b _ =>
            unless b ≥ depth + sh.lets && b - depth - sh.lets < sh.lams do
              throw "structLayout: a fixed argument is not a member parameter"
            q := q.push (sh.lams - 1 - (b - depth - sh.lets))
          | _ => throw "structLayout: a fixed argument is not a member parameter"
        match q? with
        | none => q? := some q
        | some q' => unless q == q' do throw "structLayout: inconsistent fixed arguments"
    qss := qss.push (q?.getD #[])
  let m := qss[0]!.size
  unless qss.all (·.size == m) do throw "structLayout: inconsistent fixed parameters"
  unless qss[0]! == qss[0]!.qsort (· < ·) do
    throw "structLayout: the fixed parameters are not in the first member's order"
  let qg := qss[(invPerm σ)[0]!]!
  let fixedPerm := (idPerm m).qsort fun a b => qg[a]! < qg[b]!
  let numFunTypes := shapes[0]!.lets
  unless shapes.all (·.lets == numFunTypes) do throw "structLayout: inconsistent funType lets"
  unless numFunTypes == 0 || numFunTypes == n do throw "structLayout: unexpected lets"
  return { n, sigma := σ, const?, numParams := P, numMotives := K, aux := blockAux, groups,
           fNames, numFixed := m, fixedPerm, matchers, numFunTypes }

/-- Transport a structural clique: the functionals (`_f`), the "below"
matchers, the members. Fails (and the caller keeps the baseline) on anything
outside the grammar. -/
def transportStructural (members : Array Decl) (aux : Array Decl) (σ : Array Nat)
    (const? : Name → Option ConstantInfo) : TM (Array Transported) := do
  let L ← liftE (structLayout members aux σ const?)
  let phi (e : Expr) : TM Expr := phiS L #[] e
  let mut out : Array Transported := #[]
  for d in aux do
    if L.fNames.contains d.name then
      let m := L.numFixed
      let type ← withReorderedBinders false m L.fixedPerm d.type phi
      let value ← withReorderedBinders true m L.fixedPerm d.value phi
      out := out.push { decl := { d with type, value } }
    else if L.matchers.contains d.name then
      let m := L.numFunTypes
      let type ← withReorderedBinders false m L.funPerm d.type phi
      let value ← withReorderedBinders true m L.funPerm d.value phi
      out := out.push { decl := { d with type, value } }
    else
      out := out.push { decl := { d with type := ← phi d.type, value := ← phi d.value } }
  for d in members do
    let (ps, b1) := peelLams (lamArity d.value) d.value #[]
    let mut ctx := #[]
    let mut ps' := #[]
    for (nm, t, bi) in ps do
      ps' := ps'.push (nm, ← phiS L ctx t, bi)
      ctx := ctx.push t
    let (ls, b2) := peelLets L.numFunTypes b1 #[]
    let (ls, b2) ← liftE (reorderLets L.funPerm ls b2)
    let mut ls' := #[]
    for (nm, t, v) in ls do
      ls' := ls'.push (nm, ← phiS L ctx t, ← phiS L ctx v)
      ctx := ctx.push t
    let body ← phiS L ctx b2
    out := out.push { decl := { d with type := ← phi d.type, value := mkLams ps' (mkLets ls' body) } }
  return out

end Ix.Compile.Clique

end
