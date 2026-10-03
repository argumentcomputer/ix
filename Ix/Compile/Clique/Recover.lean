/-
  Ix.Compile.Clique.Recover: Q6's second source, the recovered specification
  of a theorem clique (design document §5.4; decision Q6 of 2026-10-03).

  A theorem clique has no `EqnInfo`, so Pass 1 has no specification to order
  it by. Q6 orders it by its statements first (`Canon.statementOrder`); when
  statements tie, by the **recovered specification**: the inverse of Lean's
  encoding applied to Lean's own bodies, i.e. each member's body with its
  recursion made explicit again.

  **Recovery `R`.**
  * Structural route (`brecOn`, theorems over data): the member's functional
    `f._f` (`λ fixed is x (below : T.below … x) rest. body`). Every path into
    a `below` dictionary that reaches an entry (`Structural.belowWalk`, the
    replay of Lean's `searchPProd`/`toBelowAux` with canaries) and then
    selects function `m` inside the group's packed motive becomes the call
    `f_m is x` (the entry's arguments), applied to whatever the path was
    applied to. The packed motives at the motive positions of `below`/`brecOn`
    applications are erased (a placeholder): they are the encoding's.
  * Well-founded route: the leaf of `processSumCasesOn`'s tree for member
    `i` in the packed function (`λ v a. body`). Every application of the
    recursion variable `a (inj_j v) h` becomes `f_j v` (the decreasing proof
    `h` is dropped: it is the encoding's obligation); the recursion
    variable's type and every relation application are erased.
  * The inductive-predicate route (no `_f`; "below" matchers) is not
    recovered: `NOSPEC`.

  **The check: re-encoding.** `R` records what it erased and which
  dictionary or recursion variable each call used (`Hole`). `E` rebuilds the
  encoding from the specification: each structural call by Lean's own search
  for the dictionary entry (`leanSearch`: `searchPProd` and `toBelowAux` of
  `Structural/BRecOn.lean`, first match in Lean's order, then the path to the
  function inside the packed motive), each well-founded call by `ArgsPacker`'s
  injection (`mkInj`); the erased annotations are restored verbatim. The
  recovery is accepted only if `E (R t)` is Lean's term (up to binder names
  and `mdata`); otherwise the clique keeps its baseline (`NOSPEC`).

  **The order.** Pass 1's classes over the members with the statement as the
  type and the recovered body as the value (`Canon.cliqueClasses`): the
  statements are compared first, and recursive calls compare by class, as in
  every definition clique (M.3). Members that are still in one class have
  bisimilar recovered specifications; their order is Pass 1's seed order
  within the class (Q2, as for definition cliques), and collapse (O17, A6)
  would merge them.

  The placeholders are reserved names (`_ix_spec_*`) with fixed addresses.
  Total and pure, like the transport.
-/
module
public import Ix.Compile.Clique.Transport
public import Ix.Compile.Canon.Clique
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose stripMdata peelForalls instantiateRev
  CliqueMember Clique cliqueClasses Rules)

/-! ## Placeholders -/

def phMotive : Name := Ix.Name.mkStr Ix.Name.mkAnon "_ix_spec_motive"
def phRel : Name := Ix.Name.mkStr Ix.Name.mkAnon "_ix_spec_rel"
def phRecVar : Name := Ix.Name.mkStr Ix.Name.mkAnon "_ix_spec_recvar"

/-- A fixed address per placeholder (no hashing needed). -/
def placeholderAddr? (n : Name) : Option Address :=
  let mk (k : UInt8) : Address := ⟨⟨(Array.replicate 31 (0 : UInt8)).push k⟩⟩
  if n == phMotive then some (mk 1)
  else if n == phRel then some (mk 2)
  else if n == phRecVar then some (mk 3)
  else none

/-- What `R` erased or dropped, in traversal order. -/
inductive Hole where
  /-- an erased annotation, restored verbatim -/
  | expr (e : Expr)
  /-- a structural call through the dictionary variable `bvar i` -/
  | sCall (i : Nat)
  /-- a well-founded call through the recursion variable `bvar i`, into the
  packing `s`, with the decreasing proof `h` -/
  | wCall (i : Nat) (s : Spine) (h : Expr)
  deriving Inhabited

/-- `R` and `E` run in the transport's monad with the holes as extra state:
`R` appends, `E` consumes from the cursor. -/
abbrev RM := StateT (Array Hole × Nat) TM

def pushHole (h : Hole) : RM Unit := modify fun (hs, i) => (hs.push h, i)

def popHole : RM Hole := do
  let (hs, i) ← get
  let some h := hs[i]? | throw "recovery: the holes ran out during re-encoding"
  set (hs, i + 1)
  return h

def popExpr : RM Expr := do
  match ← popHole with
  | .expr e => return e
  | _ => throw "recovery: an erased annotation was expected"

/-! ## The structural route -/

/-- The walk of `belowPath`, returning where the path reaches an entry:
the step index, the group, and the entry `C_j args`. -/
def belowWalk (L : StructLayout) (ty : Expr) (steps : Array PStep) :
    TM (Option (Nat × Nat × Expr)) := do
  let some (c, us, args) := constApp? ty | return none
  let some a := L.aux.get? c | return none
  if a.isBrecOn || args.size < L.numParams + L.numMotives then return none
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
        unless (s == nAnd) == isAnd do throw "recovery: a projection that is not the node's"
        cur := if i == 0 then a else b
      | none => throw "recovery: a projection the walk cannot follow"
    | .app x =>
      match stripMdata w with
      | .forallE _ _ b _ _ => cur := instantiateRev b #[x]
      | _ => throw "recovery: an application the walk cannot follow"
    match getAppFnArgs (stripMdata cur) with
    | (.fvar f _, _) =>
      match cans.idxOf? f with
      | some j => return some (t, j, stripMdata cur)
      | none => throw "recovery: a path that reaches a foreign variable"
    | _ => pure ()
  return none

def isConstNamed (e : Expr) (n : Name) : Bool :=
  match stripMdata e with
  | .const c _ _ => c == n
  | _ => false

/-- `R` on a structural functional, in a context of Lean's binder types. -/
def recS (L : StructLayout) (names : Array Name) (lvls : Array Level) :
    Nat → Array Expr → Expr → RM Expr
  | 0, _, _ => throw "recovery: recursion bound exhausted"
  | fuel + 1, ctx, e => do
    let go := recS L names lvls fuel
    -- a path into a dictionary
    match e with
    | .proj .. | .app .. =>
      let (steps, base) := pathChain e
      if let .bvar i _ := stripMdata base then
        if h : i < ctx.size then
          let ty := liftLoose ctx[ctx.size - 1 - i] (i + 1)
          match ← (belowWalk L ty steps : TM _) with
          | some (t, j, entry) =>
            let g := L.groups[j]!
            let (projs, tail) := projPrefix (steps.extract (t + 1) steps.size)
            let some (idx, len) := pathPrefix g.size projs
              | throw "recovery: a path that does not select a function"
            unless stepsFit g.spine idx (projs.extract 0 len) || g.size < 2 do
              throw "recovery: a path whose projections are not the packing's"
            let some m := g.members[idx]? | throw "recovery: no such member"
            let (_, eargs) := getAppFnArgs entry
            pushHole (.sCall i)
            let mut acc := mkAppN (Expr.mkConst names[m]! lvls) eargs
            let rest := (projs.extract len projs.size).map (fun (s, k) => PStep.proj s k) ++ tail
            for st in rest do
              match st with
              | .proj s k => acc := Expr.mkProj s k acc
              | .app x => acc := Expr.mkApp acc (← go ctx x)
            return acc
          | none => pure ()
    | _ => pure ()
    match e with
    | .app .. =>
      let (h, args) := getAppFnArgs e
      match h with
      | .const c _ _ =>
        if (L.aux.get? c).isSome then
          let P := L.numParams
          let K := L.numMotives
          let mut args' := #[]
          for k in [0:args.size] do
            if P ≤ k && k < P + K then
              pushHole (.expr args[k]!)
              args' := args'.push (Expr.mkConst phMotive #[])
            else args' := args'.push (← go ctx args[k]!)
          return mkAppN h args'
        return mkAppN h (← args.mapM (go ctx))
      | _ => return mkAppN (← go ctx h) (← args.mapM (go ctx))
    | .lam nm t b bi _ => return Expr.mkLam nm (← go ctx t) (← go (ctx.push t) b) bi
    | .forallE nm t b bi _ => return Expr.mkForallE nm (← go ctx t) (← go (ctx.push t) b) bi
    | .letE nm t v b nd _ =>
      return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push t) b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go ctx x)
    | .mdata d x _ => return Expr.mkMData d (← go ctx x)
    | _ => return e

/-- Lean's search for the dictionary entry of a recursive call
(`searchPProd` and `toBelowAux`, `Structural/BRecOn.lean`): depth-first over
the `PProd`/`And` nodes, first component first; at the first other node,
instantiate its `∀`s (a reflexive field's entry) at the last arguments of
the recursive argument, search again, and accept the canary of group `j`
applied to the recursive argument. Returns the steps. -/
def leanSearch (L : StructLayout) (ty : Expr) (j : Nat) (major : Expr) :
    TM (Option (Array PStep)) := do
  let some (c, us, args) := constApp? ty | return none
  if args.size < L.numParams + L.numMotives then return none
  let mut cans : Array Name := #[]
  let mut args' := args
  for k in [0:L.numMotives] do
    let f ← freshFVar
    cans := cans.push f
    args' := args'.set! (L.numParams + k) (Expr.mkFVar f)
  let some can := cans[j]? | return none
  let start := mkAppN (Expr.mkConst c us) args'
  let majorArgs := (getAppFnArgs (stripMdata major)).2
  let isTerminal (w : Expr) : Bool := match constApp? w with
    | some (h, _, _) => h == leanName ``PUnit || h == leanName ``True
    | none => false
  let nodeStruct (w : Expr) : Name := match constApp? w with
    | some (h, _, _) => if h == nAnd then nAnd else nPProd
    | none => nPProd
  -- step 2: search the instantiated entry for the canary
  let rec search2 : Nat → Expr → Array PStep → Option (Array PStep)
    | 0, _, _ => none
    | fuel + 1, cur, acc =>
      let w := whnf L.const? whnfFuel cur
      match decodeNode .pprod w with
      | some (_, _, d1, d2) =>
        let s := nodeStruct w
        (search2 fuel d1 (acc.push (.proj s 0))).orElse
          fun _ => search2 fuel d2 (acc.push (.proj s 1))
      | none =>
        if isTerminal w then none else
        match getAppFnArgs w with
        | (.fvar f _, fargs) =>
          if f == can && (match fargs.back? with
              | some a => alphaEq (stripAllMdata a) (stripAllMdata major)
              | none => false) then some acc else none
        | _ => none
  -- the `∀`s of a reflexive entry, instantiated at the recursive argument's tail
  let instEntry (w : Expr) : Option (Expr × Array PStep) := Id.run do
    let mut k := 0
    let mut cur := w
    for _ in [0:majorArgs.size + 1] do
      match stripMdata (whnf L.const? whnfFuel cur) with
      | .forallE _ _ b _ _ => k := k + 1; cur := b
      | _ => break
    if majorArgs.size < k then return none
    let tailArgs := majorArgs.extract (majorArgs.size - k) majorArgs.size
    let mut ent := w
    for x in tailArgs do
      match stripMdata (whnf L.const? whnfFuel ent) with
      | .forallE _ _ b _ _ => ent := instantiateRev b #[x]
      | _ => return none
    return some (ent, tailArgs.map PStep.app)
  -- step 1: the dictionary's nodes
  let rec search1 : Nat → Expr → Array PStep → Option (Array PStep)
    | 0, _, _ => none
    | fuel + 1, cur, acc =>
      let w := whnf L.const? whnfFuel cur
      match decodeNode .pprod w with
      | some (_, _, d1, d2) =>
        let s := nodeStruct w
        (search1 fuel d1 (acc.push (.proj s 0))).orElse
          fun _ => search1 fuel d2 (acc.push (.proj s 1))
      | none =>
        if isTerminal w then none else
        match instEntry w with
        | some (e', apps) => search2 fuel e' (acc ++ apps)
        | none => none
  return search1 64 start #[]

/-- `E` on a structural functional: rebuild every call by Lean's search,
restore the erased motives. -/
def encS (L : StructLayout) (names : Array Name) (memberGroup : Array (Nat × Nat)) :
    Nat → Array Expr → Expr → RM Expr
  | 0, _, _ => throw "recovery: recursion bound exhausted"
  | fuel + 1, ctx, e => do
    let go := encS L names memberGroup fuel
    match e with
    | .app .. | .const .. | .proj .. =>
      let (h, args) := getAppFnArgs e
      if let .const c _ _ := h then
        if let some m := names.idxOf? c then
          -- a recovered call
          let (j, idx) := memberGroup[m]!
          let g := L.groups[j]!
          if args.size < g.arity then throw "recovery: a call with too few arguments"
          let eargs := args.extract 0 g.arity
          let some major := eargs.back? | throw "recovery: a call without its argument"
          let .sCall i ← popHole | throw "recovery: a structural call was expected"
          unless i < ctx.size do throw "recovery: the dictionary is out of scope"
          let ty := liftLoose ctx[ctx.size - 1 - i]! (i + 1)
          let some steps ← (leanSearch L ty j major : TM _)
            | throw "recovery: Lean's search does not find the call"
          let groupSteps := if g.size < 2 then #[] else
            (g.spine.projSteps idx).map fun (s, k) => PStep.proj s k
          let mut acc := applySteps (steps ++ groupSteps) (Expr.mkBVar i)
          for x in args.extract g.arity args.size do acc := Expr.mkApp acc (← go ctx x)
          return acc
        if let some _ := L.aux.get? c then
          let P := L.numParams
          let K := L.numMotives
          let mut args' := #[]
          for k in [0:args.size] do
            if P ≤ k && k < P + K then
              unless isConstNamed args[k]! phMotive do throw "recovery: a motive placeholder was expected"
              args' := args'.push (← popExpr)
            else args' := args'.push (← go ctx args[k]!)
          return mkAppN h args'
      match e with
      | .app .. => return mkAppN (← go ctx h) (← args.mapM (go ctx))
      | .proj s i x _ => return Expr.mkProj s i (← go ctx x)
      | _ => return e
    | .lam nm t b bi _ => return Expr.mkLam nm (← go ctx t) (← go (ctx.push t) b) bi
    | .forallE nm t b bi _ => return Expr.mkForallE nm (← go ctx t) (← go (ctx.push t) b) bi
    | .letE nm t v b nd _ =>
      return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push t) b) nd
    | .mdata d x _ => return Expr.mkMData d (← go ctx x)
    | _ => return e

/-- The recovered specifications of a structural theorem clique (one body
per member, in Lean's order), each checked by re-encoding. -/
def recoverStructural (members aux : Array Decl) (const? : Name → Option ConstantInfo) :
    TM (Array Expr) := do
  let n := members.size
  let L ← liftE (structLayout members aux (idPerm n) const?)
  if L.numFunTypes > 0 then throw "recovery: the inductive-predicate route is not recovered"
  let names := members.map (·.name)
  let lvls := (members[0]!).levelParams.map Level.mkParam
  -- each member's group and position in it
  let mut memberGroup : Array (Nat × Nat) := Array.replicate n (0, 0)
  for j in [0:L.groups.size] do
    let g := L.groups[j]!
    for k in [0:g.size] do memberGroup := memberGroup.set! g.members[k]! (j, k)
  let mut out := #[]
  for d in members do
    let fName := Ix.Name.mkStr d.name "_f"
    let some f := aux.find? (·.name == fName) | throw s!"recovery: no functional for {fName}"
    let (spec, (holes, _)) ← (recS L names lvls defaultFuel #[] f.value).run (#[], 0)
    let (back, (_, used)) ← (encS L names memberGroup defaultFuel #[] spec).run (holes, 0)
    unless used == holes.size && alphaEq back f.value do
      throw s!"recovery: re-encoding {fName} does not give Lean's term back"
    out := out.push spec
  return out

/-! ## The well-founded route -/

/-- `R` on a leaf of the packed function's case tree, in the user region,
under binders of which `ctx` marks the recursion variables. -/
def recW (L : WFLayout) (names : Array Name) (lvls : Array Level) :
    Nat → Array Bool → Expr → RM Expr
  | 0, _, _ => throw "recovery: recursion bound exhausted"
  | fuel + 1, ctx, e => do
    let go := recW L names lvls fuel
    if L.isRelApp e then
      pushHole (.expr e)
      return Expr.mkConst phRel #[]
    let binderTy (t : Expr) : RM Expr := do
      if L.isRecVarType t then
        pushHole (.expr t)
        return Expr.mkConst phRecVar #[]
      go ctx t
    match e with
    | .app .. =>
      let (h, args) := getAppFnArgs e
      match h with
      | .bvar i _ =>
        if i < ctx.size && ctx[ctx.size - 1 - i]! then
          let some y := args[0]? | throw "recovery: a bare recursion variable"
          let some pf := args[1]? | throw "recovery: a recursive call without its proof"
          let some (s, j, v) := decodeInj L.n y | throw "recovery: a recursive call whose argument is not an injection"
          unless L.isClique s do throw "recovery: a recursive call into another packing"
          pushHole (.wCall i s pf)
          let mut acc := Expr.mkApp (Expr.mkConst names[j]! lvls) (← go ctx v)
          for x in args.extract 2 args.size do acc := Expr.mkApp acc (← go ctx x)
          return acc
        return mkAppN h (← args.mapM (go ctx))
      | _ => return mkAppN (← go ctx h) (← args.mapM (go ctx))
    | .lam nm t b bi _ =>
      return Expr.mkLam nm (← binderTy t) (← go (ctx.push (L.isRecVarType t)) b) bi
    | .forallE nm t b bi _ =>
      return Expr.mkForallE nm (← binderTy t) (← go (ctx.push (L.isRecVarType t)) b) bi
    | .letE nm t v b nd _ =>
      return Expr.mkLetE nm (← binderTy t) (← go ctx v) (← go (ctx.push (L.isRecVarType t)) b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go ctx x)
    | .mdata d x _ => return Expr.mkMData d (← go ctx x)
    | _ => return e

/-- `E` on a recovered leaf: every call rebuilt by `ArgsPacker`'s injection,
the erased annotations restored. -/
def encW (names : Array Name) : Nat → Expr → RM Expr
  | 0, _ => throw "recovery: recursion bound exhausted"
  | fuel + 1, e => do
    let go := encW names fuel
    if isConstNamed e phRel || isConstNamed e phRecVar then return ← popExpr
    match e with
    | .app .. =>
      let (h, args) := getAppFnArgs e
      if let .const c _ _ := h then
        if let some j := names.idxOf? c then
          let some v := args[0]? | throw "recovery: a call without its argument"
          -- `R` recorded the call before transforming its argument
          let .wCall i s pf ← popHole | throw "recovery: a well-founded call was expected"
          let v' ← go v
          let mut acc := mkAppN (Expr.mkBVar i) #[mkInj s j v', pf]
          for x in args.extract 1 args.size do acc := Expr.mkApp acc (← go x)
          return acc
      return mkAppN (← go h) (← args.mapM go)
    | .lam nm t b bi _ => return Expr.mkLam nm (← go t) (← go b) bi
    | .forallE nm t b bi _ => return Expr.mkForallE nm (← go t) (← go b) bi
    | .letE nm t v b nd _ => return Expr.mkLetE nm (← go t) (← go v) (← go b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go x)
    | .mdata d x _ => return Expr.mkMData d (← go x)
    | _ => return e

/-- The recovered specifications of a well-founded theorem clique, each
checked by re-encoding. -/
def recoverWF (members : Array Decl) (mutDecl : Decl) : TM (Array Expr) := do
  let n := members.size
  let L ← liftE (wfLayout members mutDecl (idPerm n) mutDecl.name)
  let names := members.map (·.name)
  let lvls := (members[0]!).levelParams.map Level.mkParam
  let (_, fixApp) := peelLams L.numFixed mutDecl.value #[]
  let (_, fargs) := getAppFnArgs (stripMdata fixApp)
  let some F := fargs.back? | throw "recovery: no functional in the packed function"
  let (bs, body) := peelLams 2 F #[]
  unless bs.size == 2 do throw "recovery: the functional is not `λ x a. …`"
  let some t := decodeTree n body | throw "recovery: the functional is not Lean's case tree"
  unless L.isClique t.spine do throw "recovery: a case tree over another packing"
  let mut out := #[]
  for leaf in t.leaves do
    let (spec, (holes, _)) ← (recW L names lvls defaultFuel #[] leaf).run (#[], 0)
    let (back, (_, used)) ← (encW names defaultFuel spec).run (holes, 0)
    unless used == holes.size && alphaEq back leaf do
      throw "recovery: re-encoding a leaf does not give Lean's term back"
    out := out.push spec
  return out

/-! ## The order -/

/-- The recovered specifications of a theorem clique (`inp.members` in
Lean's order; `inp.sigma` is ignored). -/
def recoverSpecs (inp : Input) : Except String (Array Expr) :=
  let r : TM (Array Expr) := match inp.encoding with
    | .structural => recoverStructural inp.members inp.aux inp.const?
    | .wellFounded => do
      let some packed := findPacked? inp.members inp.aux
        | throw "recovery: no packed function"
      recoverWF inp.members packed
    | .partialFixpoint => throw "recovery: a theorem clique has no partial_fixpoint route"
  r.run'

/-- Q6: the canonical order of a theorem clique by its statements and, among
tied statements, its recovered specifications (Pass 1's classes over
statement and recovered body). `σ[i]` is the canonical position of Lean's
member `i`; the classes are returned for the report (a class of two or more
members is ordered by Pass 1's seed order). An error means the recovery
failed: the clique keeps its baseline (`NOSPEC`). -/
def recoveredOrder (rules : Rules) (addr? : Name → Option Address) (inp : Input) :
    Except String (Array Nat × Array (Array Name)) := do
  let specs ← recoverSpecs inp
  let members : Array CliqueMember := (inp.members.zip specs).map fun (d, v) =>
    { name := d.name, levelParams := d.levelParams, type := d.type, value := v }
  let addr' (n : Name) : Option Address := (placeholderAddr? n).orElse fun _ => addr? n
  let (cls, _) ← cliqueClasses rules addr' { kind := .noSpec, members }
  let order := cls.foldl (· ++ ·) #[]
  let σ := members.map fun m => (order.idxOf? m.name).getD 0
  unless isPerm σ do throw "recovery: the classes do not order every member"
  return (σ, cls)

end Ix.Compile.Clique

end
