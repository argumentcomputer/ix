/-
  Ix.Compile.Pass.Clique.Recover: the recovered specification of a clique,
  and the canonical order it gives.

  A theorem clique has no `EqnInfo`, so Pass 1 has no specification to order
  it by. It is ordered by its **recovered specification**: the inverse of
  Lean's encoding applied to Lean's own bodies, i.e. each member's body with
  its recursion made explicit again; when that cannot be recovered, by its
  statements alone (`statementOrder`). The same recovery orders a definition
  clique.

  **Recovery `R`.**
  * Structural route (`brecOn`, theorems over data): the member's functional
    `f._f` (`λ fixed is x (below : T.below … x) rest. body`), one of the
    functionals the members' `brecOn` applications pass (`StructLayout.fNames`).
    Every path into a `below` dictionary that reaches an entry (`belowWalk`,
    the replay of Lean's `searchPProd`/`toBelowAux` with canaries) and then
    selects function `m` inside the group's packed motive becomes the call
    `f_m is x` (the entry's arguments), applied to whatever the path was
    applied to. The packed motives at the motive positions of `below`/`brecOn`
    applications are erased (a placeholder): they are the encoding's.
  * Well-founded route: the leaf of `processSumCasesOn`'s tree for member
    `i` in the packed function (`λ v a. body`). Every application of the
    recursion variable `a (inj_j v) h` becomes `f_j v` (the decreasing proof
    `h` is dropped: it is the encoding's obligation); the recursion
    variable's type is erased only at the root-validated leaf entry and
    explicitly threaded `PSigma` eliminator positions. User relations and
    same-typed user binders remain intact.
  * `partial_fixpoint` route: a component `F_i` of the fixpoint's functional,
    each full projection path into the packed variable to component `j`
    becoming the member `f_j`.
  * The inductive-predicate route (no `_f`; below matchers) is not
    recovered.

  **The check: re-encoding.** `R` records what it erased and which
  dictionary or recursion variable each call used (`Hole`). `E` rebuilds the
  encoding from the specification: each structural call by Lean's own search
  for the dictionary entry (`leanSearch`: `searchPProd` and `toBelowAux` of
  `Structural/BRecOn.lean`, first match in Lean's order, then the path to the
  function inside the packed motive), each well-founded call by `ArgsPacker`'s
  injection (`mkInj`), each `partial_fixpoint` call by Lean's projection path;
  the erased annotations are restored verbatim. The recovery is accepted only
  if `E (R t)` is Lean's term (up to binder names and `mdata`); otherwise the
  clique is ordered by its statements, or keeps its baseline (`NOSPEC`).

  **The order** (`cliqueOrder`). Pass 1's classes over the members with the
  statement as the type and the normalised specification as the value
  (`Ix.Compile.Canon.cliqueClasses`, under the compiler's rules
  `Ix.Compile.Canon.Rules.compiler`, the default `Rules`: the name-hash seed;
  the Rust twin uses the same): the statements are compared first, and
  recursive calls compare by class, as in every definition clique. Members
  that are still in one class have bisimilar specifications; their order is
  Pass 1's seed order within the class, and the hook may alias them.

  The placeholders are reserved names (`_ix_spec_*`) with fixed addresses.
  Total and pure, like the transport.
-/
module
public import Ix.Compile.Pass.Clique.Transport
public import Ix.Compile.Pass.Clique.WFConjugation
public import Ix.Compile.Pass.Clique.Order
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata peelForalls mkForalls CliqueMember
  cliqueClasses Rules)

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

/-- The type of `bvar i` in the context `ctx` (Lean's binder types,
outermost first), lifted to the current depth; `none` out of scope. -/
def bvarType? (ctx : Array Expr) (i : Nat) : Option Expr :=
  if h : i < ctx.size then some (liftLoose ctx[ctx.size - 1 - i] (i + 1)) else none

/-- `bvar i` is marked in `ctx` (outermost first); `false` out of scope. -/
def bvarMarked (ctx : Array Bool) (i : Nat) : Bool :=
  if h : i < ctx.size then ctx[ctx.size - 1 - i] else false

/-! ## The structural route -/

/-- The walk of `belowPath`, returning where the path reaches an entry:
the step index, the group, and the entry `C_j args`. A step the walk cannot
follow, or an exhausted reducer, is a refusal. -/
def belowWalk (L : StructLayout) (ty : Expr) (steps : Array PStep) :
    TM (Option (Nat × Nat × Expr)) := do
  let some (c, us, args) := constApp? ty | return none
  let some a := L.aux.get? c | return none
  let P := L.numParams
  let K := L.numMotives
  if a.isBrecOn || args.size < P + K then return none
  -- the canaries
  let mut cans : Array Name := #[]
  for _ in [0:K] do
    cans := cans.push (← freshFVar)
  let args' := args.extract 0 P ++ cans.map Expr.mkFVar ++ args.extract (P + K) args.size
  let mut cur := mkAppN (Expr.mkConst c us) args'
  for (step, t) in steps.zipIdx do
    let w ← liftE (whnf L.const? whnfFuel cur)
    match step with
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

/-- The arguments of a `below`/`brecOn` application with the motives (the
positions `P ≤ k < P + K`) erased to the placeholder, each erased motive
recorded as a hole, and the others transformed by `go`, in argument order. -/
def eraseMotives (L : StructLayout) (go : Expr → RM Expr) (args : Array Expr) :
    RM (Array Expr) := do
  let P := L.numParams
  let K := L.numMotives
  let mut args' := #[]
  for (x, k) in args.zipIdx do
    if P ≤ k && k < P + K then
      pushHole (.expr x)
      args' := args'.push (Expr.mkConst phMotive #[])
    else args' := args'.push (← go x)
  return args'

/-- `R` on a structural functional, in a context of Lean's binder types.
The motives of the block's `brecOn` applications (a member's root) and of the
`below` applications in the binder types of owned dictionaries (a λ binder of
a `below` type: after the ownership check every such binder is the
recursion's own; and the binders a matcher motive gets for an owned
dictionary, `MatcherApp.addArg`) are erased to a placeholder, since they are
the packing's; a `below` application anywhere else is the user's and keeps
its motive (two members that differ only there keep different
specifications). -/
def recS (L : StructLayout) (names : Array Name) (lvls : Array Level) :
    Nat → Array Expr → Expr → RM Expr
  | 0, _, _ => throw "recovery: recursion bound exhausted"
  | fuel + 1, ctx, e => do
    let go := recS L names lvls fuel
    -- an owned dictionary's binder type: its motives erased
    let dictTy (ctx : Array Expr) (t : Expr) : RM Expr := do
      let (h, args) := getAppFnArgs t
      match h with
      | .const c _ _ =>
        if let some a := L.aux.get? c then
          if !a.isBrecOn then
            return mkAppN h (← eraseMotives L (go ctx) args)
        go ctx t
      | _ => go ctx t
    let ownedVar (x : Expr) : Bool := match stripMdata x with
      | .bvar i _ => match bvarType? ctx i with
        | some ty => L.isBelowTy ty
        | none => false
      | _ => false
    -- a path into a dictionary
    match e with
    | .proj .. | .app .. =>
      let (steps, base) := pathChain e
      if let .bvar i _ := stripMdata base then
        if let some ty := bvarType? ctx i then
          match ← (belowWalk L ty steps : TM _) with
          | some (t, j, entry) =>
            let some g := L.groups[j]? | throw "recovery: a dictionary entry of no group"
            let (projs, tail) := projPrefix (steps.extract (t + 1) steps.size)
            let some (idx, len) := pathPrefix g.size projs
              | throw "recovery: a path that does not select a function"
            unless stepsFit g.spine idx (projs.extract 0 len) || g.size < 2 do
              throw "recovery: a path whose projections are not the packing's"
            let some m := g.members[idx]? | throw "recovery: no such member"
            let some name := names[m]? | throw "recovery: no such member"
            let (_, eargs) := getAppFnArgs entry
            pushHole (.sCall i)
            let mut acc := mkAppN (Expr.mkConst name lvls) eargs
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
        if let some a := L.aux.get? c then
          -- a `brecOn` application (a member's root): its motives erased; a
          -- `below` application outside a dictionary's binder type: the user's
          if !a.isBrecOn then return mkAppN h (← args.mapM (go ctx))
          return mkAppN h (← eraseMotives L (go ctx) args)
        -- an eliminator that receives an owned dictionary past its arity:
        -- its motive's binders for the extras are dictionary types
        if let some sh := L.elimShape? c then
          if sh.arity < args.size && (args.extract sh.arity args.size).any ownedVar then
            let extras := (args.extract sh.arity args.size).map ownedVar
            let mut args' := #[]
            for (x, k) in args.zipIdx do
              match sh.motives.find? (·.1 == k) with
              | some (_, ma) =>
                let (bs, body) := peelLams ma x #[]
                let mut c' := ctx
                let mut bs' := #[]
                for (nm, t, bi) in bs do
                  bs' := bs'.push (nm, ← go c' t, bi)
                  c' := c'.push t
                let (fs, rest) := peelForalls extras.size body #[]
                let mut fs' := #[]
                -- `fs` has at most `extras.size` binders
                for ((nm, t, bi), isDict) in fs.zip extras do
                  fs' := fs'.push (nm, ← (if isDict then dictTy c' t else go c' t), bi)
                  c' := c'.push t
                args' := args'.push (mkLams bs' (mkForalls fs' (← go c' rest)))
              | none => args' := args'.push (← go ctx x)
            return mkAppN h args'
        return mkAppN h (← args.mapM (go ctx))
      | _ => return mkAppN (← go ctx h) (← args.mapM (go ctx))
    | .lam nm t b bi _ =>
      let t' ← if L.isBelowTy t then dictTy ctx t else go ctx t
      return Expr.mkLam nm t' (← go (ctx.push t) b) bi
    | .forallE nm t b bi _ => return Expr.mkForallE nm (← go ctx t) (← go (ctx.push t) b) bi
    | .letE nm t v b nd _ =>
      return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push t) b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go ctx x)
    | .mdata d x _ => return Expr.mkMData d (← go ctx x)
    | _ => return e

/-- A dictionary's terminal node (`PUnit`, `True`): no entry below it. -/
def searchTerminal (w : Expr) : Bool := match constApp? w with
  | some (h, _, _) => h == leanName ``PUnit || h == leanName ``True
  | none => false

/-- The structure of a dictionary node (`And` or `PProd`). -/
def searchNodeStruct (w : Expr) : Name := match constApp? w with
  | some (h, _, _) => if h == nAnd then nAnd else nPProd
  | none => nPProd

/-- Step 2 of `leanSearch`: search the instantiated entry for the canary
`can` applied to the recursive argument `major`, depth-first, first
component first. The bound ends the search without a result. -/
def searchEntry (const? : Name → Option ConstantInfo) (can : Name) (major : Expr) :
    Nat → Expr → Array PStep → Except String (Option (Array PStep))
  | 0, _, _ => pure none
  | fuel + 1, cur, acc => do
    let w ← whnf const? whnfFuel cur
    match decodeNode .pprod w with
    | some (_, _, d1, d2) =>
      let s := searchNodeStruct w
      match ← searchEntry const? can major fuel d1 (acc.push (.proj s 0)) with
      | some r => pure (some r)
      | none => searchEntry const? can major fuel d2 (acc.push (.proj s 1))
    | none =>
      if searchTerminal w then pure none else
      match getAppFnArgs w with
      | (.fvar f _, fargs) =>
        let applied := match fargs.back? with
          | some a => alphaEqSkipMdata (stripAllMdata a) (stripAllMdata major)
          | none => false
        pure (if f == can && applied then some acc else none)
      | _ => pure none

/-- The `∀`s of a reflexive entry `w`, instantiated at the last arguments of
the recursive argument (`majorArgs`): the instantiated entry and the
application steps; `none` when the recursive argument has too few
arguments. -/
def searchInstEntry (const? : Name → Option ConstantInfo) (majorArgs : Array Expr) (w : Expr) :
    Except String (Option (Expr × Array PStep)) := do
  let mut k := 0
  let mut cur := w
  for _ in [0:majorArgs.size + 1] do
    match stripMdata (← whnf const? whnfFuel cur) with
    | .forallE _ _ b _ _ => k := k + 1; cur := b
    | _ => break
  if majorArgs.size < k then return none
  let tailArgs := majorArgs.extract (majorArgs.size - k) majorArgs.size
  let mut ent := w
  for x in tailArgs do
    match stripMdata (← whnf const? whnfFuel ent) with
    | .forallE _ _ b _ _ => ent := instantiateRev b #[x]
    | _ => return none
  return some (ent, tailArgs.map PStep.app)

/-- Step 1 of `leanSearch`: the dictionary's nodes, depth-first, first
component first; at the first other node, step 2 on the instantiated entry
with the remaining bound. -/
def searchDict (const? : Name → Option ConstantInfo) (can : Name) (major : Expr)
    (majorArgs : Array Expr) : Nat → Expr → Array PStep → Except String (Option (Array PStep))
  | 0, _, _ => pure none
  | fuel + 1, cur, acc => do
    let w ← whnf const? whnfFuel cur
    match decodeNode .pprod w with
    | some (_, _, d1, d2) =>
      let s := searchNodeStruct w
      match ← searchDict const? can major majorArgs fuel d1 (acc.push (.proj s 0)) with
      | some r => pure (some r)
      | none => searchDict const? can major majorArgs fuel d2 (acc.push (.proj s 1))
    | none =>
      if searchTerminal w then pure none else
      match ← searchInstEntry const? majorArgs w with
      | some (e', apps) => searchEntry const? can major fuel e' (acc ++ apps)
      | none => pure none

/-- Lean's search for the dictionary entry of a recursive call
(`searchPProd` and `toBelowAux`, `Structural/BRecOn.lean`): depth-first over
the `PProd`/`And` nodes, first component first; at the first other node,
instantiate its `∀`s (a reflexive field's entry) at the last arguments of
the recursive argument, search again, and accept the canary of group `j`
applied to the recursive argument. Returns the steps; `none` when the search
(bounded by `searchDepth`) finds no entry. An exhausted reducer is a
refusal. -/
def leanSearch (L : StructLayout) (ty : Expr) (j : Nat) (major : Expr) :
    TM (Option (Array PStep)) := do
  let some (c, us, args) := constApp? ty | return none
  let P := L.numParams
  let K := L.numMotives
  if args.size < P + K then return none
  let mut cans : Array Name := #[]
  for _ in [0:K] do
    cans := cans.push (← freshFVar)
  let args' := args.extract 0 P ++ cans.map Expr.mkFVar ++ args.extract (P + K) args.size
  let some can := cans[j]? | return none
  let start := mkAppN (Expr.mkConst c us) args'
  let majorArgs := (getAppFnArgs (stripMdata major)).2
  liftE (searchDict L.const? can major majorArgs searchDepth start #[])

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
          let some (j, idx) := memberGroup[m]? | throw "recovery: a member of no group"
          let some g := L.groups[j]? | throw "recovery: a member of no group"
          if args.size < g.arity then throw "recovery: a call with too few arguments"
          let eargs := args.extract 0 g.arity
          let some major := eargs.back? | throw "recovery: a call without its argument"
          let .sCall i ← popHole | throw "recovery: a structural call was expected"
          let some ty := bvarType? ctx i | throw "recovery: the dictionary is out of scope"
          let some steps ← (leanSearch L ty j major : TM _)
            | throw "recovery: Lean's search does not find the call"
          let groupSteps ← if g.size < 2 then pure #[] else
            match g.spine.projSteps idx with
            | some st => pure (st.map fun (s, k) => PStep.proj s k)
            | none => throw "recovery: a call past its group's packed motive"
          let mut acc := applySteps (steps ++ groupSteps) (Expr.mkBVar i)
          for x in args.extract g.arity args.size do acc := Expr.mkApp acc (← go ctx x)
          return acc
        if let some _ := L.aux.get? c then
          let P := L.numParams
          let K := L.numMotives
          let mut args' := #[]
          for (x, k) in args.zipIdx do
            -- a placeholder where `recS` erased the motive; a user's `below`
            -- application keeps its own
            if P ≤ k && k < P + K && isConstNamed x phMotive then
              args' := args'.push (← popExpr)
            else args' := args'.push (← go ctx x)
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

/-- The recovered specifications of a structural clique (one functional body
per member, in Lean's order), each checked by re-encoding. `family` is the
block's authenticated `below`/`brecOn` family (`familyCandidates`). A
member's functional `f._f` must be one of the functionals the members'
`brecOn` applications pass (`StructLayout.fNames`). -/
def recoverStructural (members aux : Array Decl) (const? : Name → Option ConstantInfo)
    (family : Std.HashSet Name) : TM (Array Expr) := do
  let n := members.size
  let L ← liftE (structLayout members aux (idPerm n) const? family)
  if L.numFunTypes > 0 then throw "recovery: the inductive-predicate route is not recovered"
  -- Every dictionary path `R` reads as a recursive call must be the
  -- recursion's own ("Ownership" in `Structural.lean`): a path out of a user's
  -- `below` value would be read as an invented call, and two members that
  -- differ only there would get one specification (and be aliased).
  -- The identity transport with ownership enforced is that check.
  let _ ← transportStructural members aux (idPerm n) const? family (forceOwnership := true)
  let names := members.map (·.name)
  let some m0 := members[0]? | throw "recovery: a clique without members"
  let lvls := m0.levelParams.map Level.mkParam
  -- each member's group and position in it (the layout puts every member in
  -- exactly one group)
  let some memberGroup := (List.range n).toArray.mapM fun m =>
      L.groups.zipIdx.findSome? fun (g, j) => (g.members.idxOf? m).map fun k => (j, k)
    | throw "recovery: a member of no group"
  let mut out := #[]
  for d in members do
    let fName := Ix.Name.mkStr d.name "_f"
    unless L.fNames.contains fName do
      throw s!"recovery: {fName} is not a functional of the members' brecOn applications"
    let some f := aux.find? (·.name == fName) | throw s!"recovery: no functional for {fName}"
    let (spec, (holes, _)) ← (recS L names lvls transportFuel #[] f.value).run (#[], 0)
    let (back, (_, used)) ← (encS L names memberGroup transportFuel #[] spec).run (holes, 0)
    unless used == holes.size && alphaEqSkipMdata back f.value do
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
    match e with
    | .app .. =>
      let (h, args) := getAppFnArgs e
      if let .const name levels _ := h then
        if name == leanName ``PSigma.casesOn then
          if let #[alpha0, beta0, motive0, major0, minor0, last] := args then
            if let .bvar identity _ := stripMdata last then
              if bvarMarked ctx identity then
                -- The eliminator passes this exact recursion argument to its
                -- minor's third binder. Value flow, not a matching type,
                -- establishes the copied binder's role.
                let .lam mn mt (.forallE rn rt result rbi _) mbi _ := stripMdata motive0
                  | throw "recovery: threaded PSigma motive has no recursion binder"
                let .lam an aty (.lam bn bty (.lam cn cty body cbi _) bbi _) abi _ := stripMdata minor0
                  | throw "recovery: threaded PSigma minor has no recursion binder"
                let alpha ← go ctx alpha0
                let beta ← go ctx beta0
                let mt ← go ctx mt
                pushHole (.expr rt)
                let result ← go ((ctx.push false).push false) result
                let motive := Expr.mkLam mn mt (Expr.mkForallE rn (Expr.mkConst phRecVar #[]) result rbi) mbi
                let major ← go ctx major0
                let aty ← go ctx aty
                let bty ← go (ctx.push false) bty
                pushHole (.expr cty)
                let body ← go (((ctx.push false).push false).push true) body
                let minor := Expr.mkLam an aty
                  (Expr.mkLam bn bty (Expr.mkLam cn (Expr.mkConst phRecVar #[]) body cbi) bbi) abi
                pushHole (.expr last)
                return mkAppN (Expr.mkConst name levels)
                  #[alpha, beta, motive, major, minor, Expr.mkConst phRecVar #[]]
      match h with
      | .bvar i _ =>
        if bvarMarked ctx i then
          let some y := args[0]? | throw "recovery: a bare recursion variable"
          let some pf := args[1]? | throw "recovery: a recursive call without its proof"
          let some (s, j, v) := decodeInj L.n y | throw "recovery: a recursive call whose argument is not an injection"
          unless L.isClique s do throw "recovery: a recursive call into another packing"
          pushHole (.wCall i s pf)
          let some name := names[j]? | throw "recovery: no such member"
          let mut acc := Expr.mkApp (Expr.mkConst name lvls) (← go ctx v)
          for x in args.extract 2 args.size do acc := Expr.mkApp acc (← go ctx x)
          return acc
        return mkAppN h (← args.mapM (go ctx))
      | _ => return mkAppN (← go ctx h) (← args.mapM (go ctx))
    | .lam nm t b bi _ =>
      return Expr.mkLam nm (← go ctx t) (← go (ctx.push false) b) bi
    | .forallE nm t b bi _ =>
      return Expr.mkForallE nm (← go ctx t) (← go (ctx.push false) b) bi
    | .letE nm t v b nd _ =>
      return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push false) b) nd
    | .bvar i _ =>
      if bvarMarked ctx i then
        throw "recovery: exact recursive binder escapes the decoded call region"
      return e
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
          let some inj := mkInj s j v' | throw "recovery: a call past its packing"
          let mut acc := mkAppN (Expr.mkBVar i) #[inj, pf]
          for x in args.extract 1 args.size do acc := Expr.mkApp acc (← go x)
          return acc
      return mkAppN (← go h) (← args.mapM go)
    | .lam nm t b bi _ => return Expr.mkLam nm (← go t) (← go b) bi
    | .forallE nm t b bi _ => return Expr.mkForallE nm (← go t) (← go b) bi
    | .letE nm t v b nd _ => return Expr.mkLetE nm (← go t) (← go v) (← go b) nd
    | .proj s i x _ => return Expr.mkProj s i (← go x)
    | .mdata d x _ => return Expr.mkMData d (← go x)
    | _ => return e

/-- The recovered specifications of a well-founded clique (one leaf per
member, in Lean's order), each checked by re-encoding. -/
def recoverWF (members : Array Decl) (mutDecl : Decl)
    (const? : Name → Option ConstantInfo := fun _ => none) : TM (Array Expr) := do
  let n := members.size
  let L ← liftE (wfLayout members mutDecl (idPerm n) mutDecl.name)
  let names := members.map (·.name)
  let some m0 := members[0]? | throw "recovery: a clique without members"
  let lvls := m0.levelParams.map Level.mkParam
  let (_, fixApp) := peelLams L.numFixed mutDecl.value #[]
  -- Validate the actual root, relationship, tree and entry identities before
  -- assigning a recursion role to any leaf binder. This identity permutation
  -- is a decoder check; recovery still reads the original source syntax.
  let _ ← conjugateWFRoot L fixApp const?
  let (_, fargs) := getAppFnArgs (stripMdata fixApp)
  let some F := fargs.back? | throw "recovery: no functional in the packed function"
  let (bs, body) := peelLams 2 F #[]
  unless bs.size == 2 do throw "recovery: the functional is not `λ x a. …`"
  let some t := decodeTree n body | throw "recovery: the functional is not Lean's case tree"
  unless L.isClique t.spine do throw "recovery: a case tree over another packing"
  let mut out := #[]
  for leaf in t.leaves do
    let .lam payloadName payloadType (.lam recursiveName recursiveType body rbi _) pbi _ := stripMdata leaf
      | throw "recovery: missing decoded leaf entry binders"
    let recover : RM Expr := do
      pushHole (.expr recursiveType)
      let body ← recW L names lvls transportFuel #[false, true] body
      return Expr.mkLam payloadName payloadType
        (Expr.mkLam recursiveName (Expr.mkConst phRecVar #[]) body rbi) pbi
    let (spec, (holes, _)) ← recover.run (#[], 0)
    let (back, (_, used)) ← (encW names transportFuel spec).run (holes, 0)
    unless used == holes.size && alphaEqSkipMdata back leaf do
      throw "recovery: re-encoding a leaf does not give Lean's term back"
    out := out.push spec
  return out

/-! ## The `partial_fixpoint` route

The packed fixpoint is `λ fixed. fix … (λ x. ⟨F₀, …, F_{n-1}⟩) h` (or a
lattice fixpoint of the same shape); a recursive call in `F_i` is a full
projection path `x.2.1` into the packed variable (`PProdN.proj`). `R` turns
a path to component `j` into the member `f_j`; any other occurrence of the
packed variable fails. `E` rebuilds each call as Lean's path
(`Spine.projSteps`) and the recovery is accepted only if it gives Lean's
component back. -/

/-- `R` on a functional component; `d` is the packed variable's de Bruijn
index at the current depth. -/
def recP (s : Spine) (names : Array Name) (lvls : Array Level) :
    Nat → Nat → Expr → Except String Expr
  | 0, _, _ => throw "recovery: recursion bound exhausted"
  | fuel + 1, d, e =>
    let go := recP s names lvls fuel
    match e with
    | .proj sn i x _ =>
      let (steps, base) := projChain e
      match stripMdata base with
      | .bvar b _ =>
        if b == d then do
          let some (j, len) := pathPrefix s.size steps
            | throw "recovery: a projection of the packed variable that is not a path"
          unless stepsFit s j (steps.extract 0 len) do
            throw "recovery: a path whose projections are not the packing's"
          let some m := names[j]? | throw "recovery: no such member"
          return applyProjs (steps.extract len steps.size) (Expr.mkConst m lvls)
        else return e
      | _ => return Expr.mkProj sn i (← go d x)
    | .bvar b _ =>
      if b == d then throw "recovery: the packed variable outside a projection path" else return e
    | .app f a _ => return Expr.mkApp (← go d f) (← go d a)
    | .lam nm t b bi _ => return Expr.mkLam nm (← go d t) (← go (d + 1) b) bi
    | .forallE nm t b bi _ => return Expr.mkForallE nm (← go d t) (← go (d + 1) b) bi
    | .letE nm t v b nd _ => return Expr.mkLetE nm (← go d t) (← go d v) (← go (d + 1) b) nd
    | .mdata md x _ => return Expr.mkMData md (← go d x)
    | e => return e

/-- `E` on a recovered component: every member constant becomes Lean's path
(a member past the packing is a refusal). -/
def encP (s : Spine) (names : Array Name) : Nat → Expr → Except String Expr
  | d, e@(.const c _ _) =>
    match names.idxOf? c with
    | some j => match s.projSteps j with
      | some st => pure (applyProjs st (Expr.mkBVar d))
      | none => throw "recovery: a member past the fixpoint's packing"
    | none => pure e
  | d, .proj sn i x _ => return Expr.mkProj sn i (← encP s names d x)
  | d, .app f a _ => return Expr.mkApp (← encP s names d f) (← encP s names d a)
  | d, .lam nm t b bi _ => return Expr.mkLam nm (← encP s names d t) (← encP s names (d + 1) b) bi
  | d, .forallE nm t b bi _ =>
    return Expr.mkForallE nm (← encP s names d t) (← encP s names (d + 1) b) bi
  | d, .letE nm t v b nd _ =>
    return Expr.mkLetE nm (← encP s names d t) (← encP s names d v) (← encP s names (d + 1) b) nd
  | d, .mdata md x _ => return Expr.mkMData md (← encP s names d x)
  | _, e => pure e

/-- The recovered functional components of a `partial_fixpoint` clique (in
the context of the fixed parameters and the packed variable, `bvar 0`), each
checked by re-encoding, and the layout. -/
def recoverPF (members : Array Decl) (packed : Decl) : Except String (Array Expr × PFLayout) := do
  let n := members.size
  let L ← pfLayout members packed (idPerm n) packed.name
  let names := members.map (·.name)
  let some m0 := members[0]? | throw "recovery: a clique without members"
  let lvls := m0.levelParams.map Level.mkParam
  let (_, body) := peelLams L.numFixed packed.value #[]
  let some (head, _, args) := constApp? (stripMdata body)
    | throw "recovery: the packed value is not a fixpoint application"
  unless head == nOrderFix || head == leanName ``Lean.Order.lfp_monotone do
    throw "recovery: unsupported partial-fixpoint root"
  let #[rootDomain, _, rootFunctional, _] := args | throw "recovery: unsupported partial-fixpoint root"
  let .lam _ domain functional _ _ := stripMdata rootFunctional
    | throw "recovery: the fixpoint functional has no recursive binder"
  let some input := decodeSpine .pprod n domain
    | throw "recovery: the recursive binder is not a packed product"
  let some (output, cs) := decodeTuple n (stripMdata functional)
    | throw "recovery: the functional has no encoded output tuple"
  let outputFits := match output.type? with
    | some outputType => alphaEqSkipMdata (normOrderAlias outputType) (normOrderAlias (liftLoose domain 1))
    | none => false
  unless L.isClique input && alphaEqSkipMdata (normOrderAlias domain) (normOrderAlias rootDomain) &&
      outputFits do
    throw "recovery: the decoded functional disagrees with the fixpoint packing"
  let mut out := #[]
  for c in cs do
    let spec ← recP L.spine names lvls transportFuel 0 c
    unless alphaEqSkipMdata (← encP L.spine names 0 spec) c do
      throw "recovery: re-encoding a functional component does not give Lean's term back"
    out := out.push spec
  return (out, L)

/-! ## Specifications in each member's own parameters

The recovery reads each member's body back out of the encoding, but in the
encoding's context: the fixed parameters follow Lean's *first* function's
order, so the recovered bodies of two presentations differ by a permutation
of those binders. A member's specification is stated in the member's own
parameters instead: the recovered body is instantiated at the member's own
arguments of the fixed positions (read off its call of the encoding,
`memberFixed`) and abstracted over the member's own parameters. The result
is a function of the member's specification alone, so two presentations give
the same specifications, whatever Lean's first function was. The encoding's
own variables that `R` left (none, when the encoding is Lean's) become the
recursion-variable placeholder. -/

/-- The placeholder for an encoding variable in a specification. -/
def phEnc : Expr := Expr.mkConst phRecVar #[]

/-- The member's own arguments of the fixed positions, under its own
parameters (`ps` binders). -/
def fixedArgsOf (numParams : Nat) (q : Array Nat) : Array Expr :=
  q.map fun p => Expr.mkBVar (numParams - 1 - p)

/-- Per member (Lean's order), its recovered body and its fixed positions
(`memberFixed`); a member without either is a refusal (neither happens: the
recovery gives one body per member, the layout one entry per member). -/
def withMemberFixed (members : Array Decl) (bodies : Array Expr) (memberFixed : Array (Array Nat)) :
    Except String (Array (Decl × Expr × Array Nat)) :=
  members.zipIdx.mapM fun (d, i) => do
    let some body := bodies[i]? | throw s!"recovery: no recovered body for {d.name}"
    let some q := memberFixed[i]? | throw s!"recovery: no fixed positions for {d.name}"
    return (d, body, q)

/-- The normalised specifications of a clique (`inp.members` in Lean's
order; `inp.sigma` is ignored): one closed term per member, a function of
the member's specification alone. An error means the recovery failed. -/
def normalisedSpecs (inp : Input) : Except String (Array Expr) := do
  let n := inp.members.size
  let paramsOf (d : Decl) := (peelLams (lamArity d.value) d.value #[]).1
  match inp.encoding with
  | .wellFounded =>
    let some packed := findPacked? inp.members inp.aux | throw "recovery: no packed function"
    let L ← wfLayout inp.members packed (idPerm n) packed.name
    let leaves ← TM.run' (recoverWF inp.members packed inp.const?)
    -- a leaf lives under the fixed parameters, then `F`'s `x` and `a`
    let items ← withMemberFixed inp.members leaves L.memberFixed
    return items.map fun (d, leaf, q) =>
      let ps := paramsOf d
      let fixed := (fixedArgsOf ps.size q).reverse
      mkLams ps (instantiateRev leaf (#[phEnc, phEnc] ++ fixed))
  | .structural =>
    let L ← structLayout inp.members inp.aux (idPerm n) inp.const? inp.family
    let fs ← TM.run' (recoverStructural inp.members inp.aux inp.const? inp.family)
    -- a functional `f._f` is closed: applied to the member's fixed arguments
    let items ← withMemberFixed inp.members fs L.memberFixed
    return items.map fun (d, f, q) =>
      let ps := paramsOf d
      mkLams ps (mkAppN f (fixedArgsOf ps.size q))
  | .partialFixpoint =>
    let some packed := findPacked? inp.members inp.aux | throw "recovery: no packed fixpoint"
    let (cs, L) ← recoverPF inp.members packed
    -- a component lives under the fixed parameters, then the packed variable
    let items ← withMemberFixed inp.members cs L.memberFixed
    return items.map fun (d, c, q) =>
      let ps := paramsOf d
      let fixed := (fixedArgsOf ps.size q).reverse
      mkLams ps (instantiateRev c (#[phEnc] ++ fixed))

/-- The canonical order of a clique: Pass 1's classes over each member's
type and normalised specification, statements compared first, under the
compiler's rules (`Rules.compiler`, the default `Rules`: the name-hash seed);
members still in one class follow Pass 1's seed order. When the
specification cannot be recovered, the statements alone (`statementOrder`,
same rules); when they tie too, an error (`NOSPEC`: the clique keeps its
baseline). `σ[i]` is the canonical position of Lean's member `i`; the
classes are returned for the plan (a class of two or more members is ordered
by the seed order). `addr?` gives the external constants' addresses; the
placeholders have their own (`placeholderAddr?`). -/
def cliqueOrder (addr? : Name → Option Address) (inp : Input) :
    Except String (Array Nat × Array (Array Name) × OrderSource) := do
  let rules : Rules := Rules.compiler
  let addr' (n : Name) : Option Address := (placeholderAddr? n).orElse fun _ => addr? n
  match normalisedSpecs inp with
  | .ok specs =>
    let members : Array CliqueMember := (inp.members.zip specs).map fun (d, v) =>
      { name := d.name, levelParams := d.levelParams, type := d.type, value := v }
    let (cls, _) ← cliqueClasses rules addr' { kind := .noSpec, members }
    let order := cls.foldl (· ++ ·) #[]
    let some σ := members.mapM fun m => order.idxOf? m.name
      | throw "order: the classes do not order every member"
    unless isPerm σ do throw "order: the classes do not order every member"
    return (σ, cls, .specification)
  | .error why =>
    let members : Array CliqueMember := inp.members.map fun d =>
      { name := d.name, levelParams := d.levelParams, type := d.type, value := d.value }
    match ← statementOrder rules addr' members with
    | some σ =>
      let some cls := invPerm σ >>= (·.mapM fun i => members[i]?.map fun m => #[m.name])
        | throw "order: the statements' order is not a permutation of the members"
      return (σ, cls, .statements why)
    | none => throw s!"NOSPEC: {why}; the statements tie"

end Ix.Compile.Pass.Clique

end
