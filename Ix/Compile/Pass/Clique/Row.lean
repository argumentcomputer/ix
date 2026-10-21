/-
  Ix.Compile.Pass.Clique.Row: the equation rows of a transported
  well-founded clique and the faithful copies of its encoding, as pure
  functions over `Ix.Expr`.

  A transported member `f` keeps Lean's name and type, and its value becomes
  the transported one over the canonical constants (`g._ix._mutual`, its
  `_proof_k`). Lean's own encoding constants are given faithful copies under
  reserved names, and each member a row relating Lean's value to `f`:

  * **the encoding set** (`encodingSet`) of a well-founded plan: exactly
    what the rows need, the clique's Lean encoding constants
    (`isEncodingName`) that the rows' left-hand sides (the transported
    members' Lean values) reference, closed under the references of the set
    itself. On every fixture it is `f₀._mutual` and its abstracted proofs:
    a member's value reaches `f₀._mutual` only, and that its proofs only. A
    packed equation lemma the carried lemmas reach (`f₀._mutual.eq_def`, a
    source of the plan's canonical constants) is reached by no row and gets
    no copy. A referenced encoding constant missing from the input is an
    error. The rename to the copies (`srcRename`) is over this set only, and
    a row whose statement or proof would reference an encoding constant
    outside it is refused (never a dangling `_ix.src` name);
  * **the copy** `n._ix.src` of each `n` of the set (`srcCopy`): exactly
    `n`'s record (kind, type, value, level parameters, hints, safety, `all`)
    with its name replaced and the references to the set (constants and
    `all`, constructor and recursor names) renamed to their copies; every
    other reference unchanged. One pure function, so that
    `srcCopy n = translate (source n)` can be stated;
  * **the row** `f._ix.row : @Eq.{u} T lhs (f us)` (`rowOf`), a theorem with
    `f`'s level parameters, `T` its type, `us` its parameters as levels and
    `lhs` Lean's value of `f` with the set renamed to its copies
    (`rowLhs`). `u` is `T`'s sort (`sortOf?`).

  Names go through `Ix.Compile.Pass.Names` (`n._ix.src`, `f._ix.row` by
  `appendComps`); their reserved-ness is the name test only, they are never
  marked generated. A copy byte-identical to another published constant may
  share its record: nothing here assumes one record per copy.

  **The sort** (`sortOf?`): light and fail-closed, over declared types. A
  `Sort v` has sort `succ v`; a `∀` the `mkLevelIMax'` (Lean's simplifying
  `imax`, `inferType`'s) of its domain's and body's sorts, the body under a
  free variable `_clq_sort.k`; an application of a constant or a free
  variable (no argument is an application too) its head's declared type
  (the constant's at its levels, through `substLevels`), the arguments
  peeled one `∀` each (reduced by `Clique.whnf` when not one), reduced to a
  `Sort v`: `v`. Anything else, or an exhausted bound (`sortDepth`, or
  `whnfFuel` per reduction), is `none`, and then no row. The level is not
  `Level.normalize`d: the kernel compares levels up to normalisation, and
  `mkLevelIMax'`/`mkLevelMax'` only simplify to equivalent levels.

  **The proof** (`rowProof`), a fixed term recipe (the donor's `proveWF`),
  every implicit argument and level explicit. Over the member's parameters
  `ps` (opened as free variables), with `A = P fixed` (Lean's packed
  function at the member's fixed arguments, `P` the head of Lean's body),
  `B = P' fixed'` (the canonical one, from the transported body), their
  roots `fix α C r hwf F` / `Nat.fix α C h F` (`P`'s value at the fixed
  arguments, `WellFounded.fix.{u,v}`/`WellFounded.Nat.fix.{u,v}` giving `α`,
  `C` and the levels `u`, `v`), `R` the relation read off `F`'s recursion
  binder (`F = λ x a. …`, `a : ∀ y, R y x → C y`), `inj_j` Lean's injections
  and `inj'_k` the canonical ones (the spines decoded from `α` and `α'`, σ
  the plan's):

  ```
  M x    := casesOn.{1} x (λ w. @Eq.{v} (C (inj_j w)) (A (inj_j w)) (B (inj'_{σ j} w)))_j
  Φ y    := casesOn.{v} y (λ w. B (inj'_{σ j} w))_j                       -- motive C
  IH x   := ∀ (y : α) (hy : R y x), M y
  step   := λ x (ih : IH x). casesOn.{0} x (λ w. λ (ih : IH (inj_j w)). chain_j) ih
  chain_j : A xL = B xI  (xL = inj_j w, xI = inj'_{σ j} w, every Eq at C xL):
    Eq.trans (fix_eq … xL)                                  -- A xL = F xL gA
     (Eq.trans (congrArg (F xL) K)                          -- F xL gA = F xL gΦ
       (Eq.trans (Eq.refl (F xL gΦ))                        -- F xL gΦ = F' xI gB (conversion)
         (Eq.symm (fix_eq' … xI))))                         -- F' xI gB = B xI
    gA = λ y hy. A y,  gΦ = λ y hy. Φ y,  gB = λ (y : α') (hy : R' y xI). B y
    K  = funext (λ y. funext (λ hy. casesOn.{0} y (λ w (m : M (inj_k w)). m)_k (ih y hy)))
  ind    := @WellFounded.induction.{u} α (λ y x. R y x) hwf (λ x. M x) xL step
  proof  := funext (λ p₀. … funext (λ p_{n-1}. ind))         -- lhs = f us
  ```

  `hwf` is the root's for `WellFounded.fix`; for `Nat.fix`
  `@InvImage.wf.{u,1} α Nat (@WellFoundedRelation.rel.{1} Nat Nat.lt_wfRel) h
  (@WellFoundedRelation.wf.{1} Nat Nat.lt_wfRel)`. The case trees are the
  library's `Tree.build` (Lean's `Mutual.casesOn` form) over Lean's spine.
  No expected-type hint is needed: every argument the kernel checks is
  explicit. The proof is built over Lean's constants and the set renamed to
  its copies at the end (with `lhs`), so it is a proof about the copies.

  **Refusals** (errors; the wiring keeps Lean's form): an alias member (its
  value is its representative's, another summand); a value or root outside
  the recipe's shapes; a definition clique (motive level not `0`) whose
  functional uses the recursion binder other than as calls through `PSigma`
  layers (`leafReduces`, the packed equation lemma's own test: threaded into
  a `match`, the transport passes an adapter and the conjugated step is not
  one unfolding; the planner leaves such cliques in Lean's form anyway,
  `NOSPEC`); no sort; an encoding constant missing from the input or not a
  definition or theorem; a row mentioning an encoding constant outside the
  set. Non-well-founded plans get no row (`rowOf` is `none`, `rowsOf`
  empty).

  Total and pure: the walks are structural or on the named bounds, no
  panicking access.
-/
module
public import Ix.Compile.Pass.Clique.PlanClique
public import Ix.Compile.Pass.Clique.WFSchema
public import Ix.Compile.Pass.Clique.Whnf
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata substLevels)
open Ix.Compile.Image (Local)
open Ix.Compile.LibraryNames (nEq nEqRefl)

/-! ## Names -/

/-- `n._ix.src`: the faithful copy of the encoding constant `n`. -/
def srcName (n : Name) : Name := appendComps n [.s ixComponent, .s "src"]

/-- `f._ix.row`: the equation row of the member `f`. -/
def rowName (f : Name) : Name := appendComps f [.s ixComponent, .s "row"]

def nEqSymm : Name := leanName ``Eq.symm
def nEqTrans : Name := leanName ``Eq.trans
def nCongrArg : Name := leanName ``congrArg
def nFunext : Name := leanName ``funext
def nWFInduction : Name := leanName ``WellFounded.induction
def nWFFix : Name := leanName ``WellFounded.fix
def nWFFixEq : Name := leanName ``WellFounded.fix_eq
def nNatFix : Name := leanName ``WellFounded.Nat.fix
def nNatFixEq : Name := leanName ``WellFounded.Nat.fix_eq
def nInvImageWf : Name := leanName ``InvImage.wf
def nWFRelRel : Name := leanName ``WellFoundedRelation.rel
def nWFRelWf : Name := leanName ``WellFoundedRelation.wf
def nNat : Name := leanName ``Nat
def nNatLtWfRel : Name := leanName ``Nat.lt_wfRel

/-- The library constants a row proof references (for the scheduler): the
row's statement `Eq`, the proof's equality steps, the induction and the
fixpoint equations, the sum packing's type, injections and case split, and
the `Nat.fix` well-foundedness witness. -/
def rowPrereqs : Array Name :=
  #[nEq, nEqRefl, nEqSymm, nEqTrans, nCongrArg, nFunext, nWFInduction, nWFFixEq, nNatFixEq, nPSum,
    nPSumCasesOn, nPSumInl, nPSumInr, nInvImageWf, nWFRelRel, nWFRelWf, nNat, nNatLtWfRel]

/-! ## The copies and the row's left-hand side -/

/-- The renaming of the encoding set `enc` to its copies. -/
def srcRename (enc : Std.HashSet Name) (c : Name) : Option Name :=
  if enc.contains c then some (srcName c) else none

/-- The copy `n._ix.src` of `n`'s record `ci`: the name replaced, and the
references to `enc` (in the type, the value, `all`, and the names of a
constructor's inductive or a recursor's rules) renamed to their copies. -/
def srcCopy (enc : Std.HashSet Name) (ci : ConstantInfo) : ConstantInfo :=
  let e (x : Expr) : Expr := renameConsts (srcRename enc) x
  let n (c : Name) : Name := (srcRename enc c).getD c
  let cv (v : Ix.ConstantVal) : Ix.ConstantVal := { v with name := srcName v.name, type := e v.type }
  match ci with
  | .axiomInfo v => .axiomInfo { v with cnst := cv v.cnst }
  | .defnInfo v => .defnInfo { v with cnst := cv v.cnst, value := e v.value, all := v.all.map n }
  | .thmInfo v => .thmInfo { v with cnst := cv v.cnst, value := e v.value, all := v.all.map n }
  | .opaqueInfo v => .opaqueInfo { v with cnst := cv v.cnst, value := e v.value, all := v.all.map n }
  | .quotInfo v => .quotInfo { v with cnst := cv v.cnst }
  | .inductInfo v => .inductInfo { v with cnst := cv v.cnst, all := v.all.map n, ctors := v.ctors.map n }
  | .ctorInfo v => .ctorInfo { v with cnst := cv v.cnst, induct := n v.induct }
  | .recInfo v =>
    let rules := v.rules.map fun r => ({ r with ctor := n r.ctor, rhs := e r.rhs } : Ix.RecursorRule)
    .recInfo { v with cnst := cv v.cnst, all := v.all.map n, rules := rules }

/-- The row's left-hand side: Lean's value of the member with the encoding
set renamed to its copies. -/
def rowLhs (enc : Std.HashSet Name) (leanValue : Expr) : Expr :=
  renameConsts (srcRename enc) leanValue

/-! ## The encoding set -/

/-- The names reached from `stack` through the references satisfying
`isEnc` of their types and values, added to `seen`. At most `fuel` names
are visited; an exhausted bound, or a name that is not in the input, is an
error. -/
def encodingClosure (const? : Name → Option ConstantInfo) (isEnc : Name → Bool) :
    Nat → List Name → Std.HashSet Name → Except String (Std.HashSet Name)
  | fuel, stack, seen =>
    match popUnseen seen stack with
    | none => pure seen
    | some (c, rest) =>
      match fuel with
      | 0 => throw "row: the encoding set exceeds its bound"
      | fuel + 1 =>
        match const? c with
        | none => throw s!"row: the encoding constant {c.pretty} is not in the input"
        | some ci =>
          let refs := constOccurrences isEnc ci.getCnst.type ++
            ((valueOf? ci).map (constOccurrences isEnc)).getD #[]
          encodingClosure const? isEnc fuel (pushStack rest refs) (seen.insert c)

/-- The members of a plan that get rows: its transported members, in Lean's
order. -/
def rowMembers (plan : CliquePlan) : Array Name := plan.all.filter plan.members.contains

/-- The encoding set of a plan: the clique's Lean encoding constants that
the rows' left-hand sides (the Lean values of `rowMembers`) reference,
closed under those references (see the module note). At most
`eqLemmaBound` names are visited (as many as `encodingProofs` visits). -/
def encodingSet (const? : Name → Option ConstantInfo) (plan : CliquePlan) :
    Except String (Std.HashSet Name) := do
  let isEnc := isEncodingName plan.all
  let mut seeds := #[]
  for m in rowMembers plan do
    if let some v := (const? m).bind valueOf? then seeds := seeds ++ constOccurrences isEnc v
  encodingClosure const? isEnc eqLemmaBound (pushStack [] seeds) {}

/-! ## The row's level -/

/-- Lean's `Level.isNeverZero`. -/
def levelNeverZero : Level → Bool
  | .succ .. => true
  | .max a b _ => levelNeverZero a || levelNeverZero b
  | .imax _ b _ => levelNeverZero b
  | _ => false

/-- Lean's `mkLevelIMax'` (`src/lean/Lean/Level.lean`, `mkLevelIMaxCore`):
the simplifying `imax` of `inferType`'s `∀` rule. -/
def mkLevelIMax' (u v : Level) : Level :=
  if levelNeverZero v then mkLevelMax' u v
  else if Level.isZero v then v
  else if Level.isZero u then v
  else if u == v then u
  else Level.mkIMax u v

/-- The root of the free variables `sortOf?` opens binders with. -/
def sortVarRoot : Name := Name.mkStr Name.mkAnon "_clq_sort"

/-- The declared type of an application head: a constant at its levels (as
many as its parameters), or a free variable of `ctx`. -/
def headType? (const? : Name → Option ConstantInfo) (ctx : Array Local) : Expr → Option Expr
  | .const c us _ => do
    let cv := (← const? c).getCnst
    if cv.levelParams.size != us.size then none
    some (substLevels cv.levelParams us cv.type)
  | .fvar x _ => (ctx.find? (·.fvar == x)).map (·.type)
  | _ => none

/-- `ty` at the arguments `args`: each one instantiates a `∀`, `ty` reduced
to weak head normal form first when it is not one. -/
def instForallArgs (const? : Name → Option ConstantInfo) (ty : Expr) (args : Array Expr) : Option Expr :=
  args.foldlM (init := ty) fun ty a => do
    let ty ← match stripMdata ty with
      | t@(.forallE ..) => some t
      | t => match whnf const? whnfFuel t with
        | .ok r => some (stripMdata r)
        | .error _ => none
    match ty with
    | .forallE _ _ b _ _ => some (instantiateRev b #[a])
    | _ => none

/-- `sortOf?` on an explicit bound. -/
def sortOfAux (const? : Name → Option ConstantInfo) : Nat → Array Local → Expr → Option Level
  | 0, _, _ => none
  | fuel + 1, ctx, ty =>
    match stripMdata ty with
    | .sort u _ => some (Level.mkSucc u)
    | .forallE nm dom body bi _ => do
      let u ← sortOfAux const? fuel ctx dom
      let x : Local := { fvar := Name.mkNat sortVarRoot ctx.size, userName := nm, type := dom, bi := bi }
      let v ← sortOfAux const? fuel (ctx.push x) (instantiateRev body #[x.expr])
      some (mkLevelIMax' u v)
    | e => do
      let (h, args) := getAppFnArgs e
      let t ← instForallArgs const? (← headType? const? ctx (stripMdata h)) args
      match whnf const? whnfFuel t with
      | .ok r => match stripMdata r with
        | .sort u _ => some u
        | _ => none
      | .error _ => none

/-- The sort `u` of the type `ty` (`ty : Sort u`), over declared types, with
`ctx` the free variables' types (see the module note); `none` outside the
computation's shapes or past `sortDepth`. -/
def sortOf? (const? : Name → Option ConstantInfo) (ctx : Array Local) (ty : Expr) : Option Level :=
  sortOfAux const? sortDepth ctx ty

/-! ## The well-founded row proof -/

/-- A packed function's root at its fixed arguments. -/
structure RowFix where
  /-- `WellFounded.Nat.fix` (else `WellFounded.fix`) -/
  nat : Bool
  /-- the root's levels `[u, v]`: the domain's and the motive's -/
  levels : Array Level
  /-- the root's arguments (without the point) -/
  args : Array Expr
  domain : Expr
  motive : Expr
  functional : Expr
  domainLevel : Level
  motiveLevel : Level

/-- `WellFounded.fix.{u,v} α C r hwf F` or `WellFounded.Nat.fix.{u,v} α C h F`. -/
def readRowFix (root : Expr) : Except String RowFix := do
  let notFix := "row: the packed function's value is not a `WellFounded.fix` or `WellFounded.Nat.fix` root"
  let some (h, levels, args) := constApp? root | throw notFix
  let #[u, v] := levels | throw notFix
  if h == nWFFix then
    let #[α, C, _, _, F] := args | throw notFix
    return { nat := false, levels, args, domain := α, motive := C, functional := F, domainLevel := u,
             motiveLevel := v }
  else if h == nNatFix then
    let #[α, C, _, F] := args | throw notFix
    return { nat := true, levels, args, domain := α, motive := C, functional := F, domainLevel := u,
             motiveLevel := v }
  else throw notFix

/-- The fixpoint equation of a root (`fix_eq` / `Nat.fix_eq`, the root's
arguments then the point). -/
def RowFix.eqAt (fx : RowFix) (point : Expr) : Expr :=
  mkAppN (Expr.mkConst (if fx.nat then nNatFixEq else nWFFixEq) fx.levels) (fx.args.push point)

/-- One side of a row: a packed function at a member's fixed arguments. -/
structure RowSide where
  /-- `P.{us} fixed` -/
  head : Expr
  fix : RowFix
  /-- the domain's sum packing -/
  spine : Spine
  /-- the recursion relation `R y x`, over the free variables `relY`, `relX` -/
  relY : Name
  relX : Name
  rel : Expr

/-- `R y x` at the given terms. -/
def RowSide.relAt (s : RowSide) (y x : Expr) : Expr :=
  instLocals (abstractFVars #[s.relY, s.relX] s.rel) #[y, x]

/-- The side of the body `P.{us} fixed point` (a member's value under its
parameters), with `decl?` the packed function's declaration: its root at
the fixed arguments, the domain's packing of `n` summands and the relation
of the functional's recursion binder; and the point. -/
def rowSide (decl? : Name → Option Decl) (n : Nat) (body : Expr) (what : String) :
    TM (RowSide × Expr) := do
  let notPacked := s!"row: {what} is not an application of the packed function"
  let some (p, us, args) := constApp? body | throw notPacked
  let some point := args.back? | throw notPacked
  let fixed := args.pop
  let some d := decl? p | throw s!"row: {what}: {p.pretty} is not the clique's packed function"
  unless d.levelParams.size == us.size do throw s!"row: {what}: the packed function's universe arguments"
  let fx ← liftE (readRowFix (betaApp (substLevels d.levelParams us d.value) fixed))
  let some spine := decodeSpine .psum n fx.domain
    | throw s!"row: {what}: the fixpoint's domain is not the clique's sum packing"
  let (xs, rest) ← openBinders true 1 fx.functional
  let some x := xs[0]? | throw s!"row: {what}: the functional has no argument"
  let .lam _ recType _ _ _ := stripMdata rest | throw s!"row: {what}: the functional has no recursion binder"
  let (ys, recBody) ← openBinders false 1 recType
  let some y := ys[0]? | throw s!"row: {what}: the recursion binder is not a function"
  let .forallE _ rel _ _ _ := stripMdata recBody
    | throw s!"row: {what}: the recursion binder has no decreasing hypothesis"
  return ({ head := mkAppN (Expr.mkConst p us) fixed, fix := fx, spine, relY := y.fvar, relX := x.fvar, rel },
    point)

/-- A local named `name` (default binder). -/
def rowLocal (name : String) (type : Expr) : TM Local := do
  let fvar ← freshFVar
  return { fvar, userName := Name.mkStr Name.mkAnon name, type, bi := .default }

/-- An optional result, or the named refusal. -/
def rowSome {α} (what : String) : Option α → TM α
  | some a => pure a
  | none => throw s!"row: {what}"

/-- The domains of `type`'s leading `∀`s at the terms `xs`, each with the
rest of the type after it (instantiated through it). -/
def rowTelescope (type : Expr) (xs : Array Expr) : TM (Array (Expr × Expr)) := do
  let mut cur := type
  let mut out := #[]
  for x in xs do
    match stripMdata cur with
    | .forallE _ dom body _ _ =>
      let rest := instantiateRev body #[x]
      out := out.push (dom, rest)
      cur := rest
    | _ => throw "row: the member's type binds fewer parameters than its value"
  return out

/-- The proof of `leanValue = rhs` for the member at Lean index `index` of a
clique of `n` members under `sigma`: `type` is the member's type,
`ixValue` its transported value, `leanDecl?`/`ixDecl?` the declarations of
Lean's and the canonical packed function (see the module note for the
term). Over Lean's constants: the caller renames the encoding set. -/
def rowProof (const? : Name → Option ConstantInfo) (leanDecl? ixDecl? : Name → Option Decl) (n : Nat)
    (sigma : Array Nat) (index : Nat) (type leanValue ixValue rhs : Expr) : TM Expr := do
  -- the member's parameters, and both bodies under them
  let arity := lamArity leanValue
  let (ps, bodyL) ← openBinders true arity leanValue
  let pes := ps.map (·.expr)
  let (ixBinders, ixBody) := peelLams arity ixValue #[]
  unless ixBinders.size == arity do throw "row: the transported value does not bind the member's parameters"
  let bodyI := instLocals ixBody pes
  let tele ← rowTelescope type pes
  let (sL, xL) ← rowSide leanDecl? n bodyL "Lean's value"
  let (sI, xI) ← rowSide ixDecl? n bodyI "the transported value"
  let some (_, jL, _) := decodeInj n xL | throw "row: Lean's packed argument is not an injection"
  let some (_, jI, _) := decodeInj n xI | throw "row: the transported packed argument is not an injection"
  unless jL == index && sigma[index]? == some jI do throw "row: the members' injections do not follow σ"
  let αL := sL.fix.domain
  let uL := sL.fix.domainLevel
  let vL := sL.fix.motiveLevel
  -- the conjugated step is one unfolding of either side only when Lean's
  -- bodies use the recursion binder as calls (through `PSigma` layers, as
  -- `leafReduces` decides for the packed equation lemma): threaded into a
  -- `match`, the transport passes an adapter instead. Proofs (motive level
  -- `0`) are equal regardless.
  unless Level.isZero vL do
    let (_, functionalBody) := peelLams 2 sL.fix.functional #[]
    let some tree := decodeTree n functionalBody | throw "row: Lean's functional is not a refinement case tree"
    unless tree.leaves.all (leafReduces wfDepth) do
      throw "row: a body threads the recursion binder (argument pushing): one unfolding does not give the \
        transported body"
  let atC (x : Expr) : Expr := applyWFCase sL.fix.motive x
  let eqAt (x a b : Expr) : Expr := mkAppN (Expr.mkConst nEq #[vL]) #[atC x, a, b]
  let injL (j : Nat) (w : Expr) : TM Expr := rowSome "Lean's injection" (mkInj sL.spine j w)
  let injI (j : Nat) (w : Expr) : TM Expr := do
    let k ← TM.idx sigma j "row: σ"
    rowSome "the canonical injection" (mkInj sI.spine k w)
  -- a case split of `major : α` at the motive's level `w` (`Tree.build`)
  let cases (w : Level) (motive : Expr → TM Expr) (major : Expr) (leaf : Nat → Local → TM Expr) :
      TM Expr := do
    let x ← rowLocal "x" αL
    let motiveBody := abstractFVars #[x.fvar] (← motive x.expr)
    let mut leaves := #[]
    for j in [0:n] do
      let w ← rowLocal "w" (← TM.idx sL.spine.leaves j "row: summand")
      leaves := leaves.push (mkLambda #[w] (← leaf j w))
    let tree : Tree := { spine := sL.spine, w, motiveBody, motiveName := x.userName, major, leaves,
                         extras := #[], altNames := #[] }
    rowSome "the case tree" tree.build
  -- `M x`: the members' equations at their summands
  let motM (major : Expr) : TM Expr :=
    cases lvlOne (fun _ => pure (Expr.mkSort Level.mkZero)) major fun j w => do
      let xl ← injL j w.expr
      return eqAt xl (Expr.mkApp sL.head xl) (Expr.mkApp sI.head (← injI j w.expr))
  -- `Φ y`: the canonical fixpoint at the canonical summand of `y`'s
  let phi (major : Expr) : TM Expr :=
    cases vL (fun x => pure (atC x)) major fun j w => do
      return Expr.mkApp sI.head (← injI j w.expr)
  let ihType (x : Expr) : TM Expr := do
    let y ← rowLocal "y" αL
    let hy ← rowLocal "hy" (sL.relAt y.expr x)
    return mkForall #[y, hy] (← motM y.expr)
  let guarded (α : Expr) (rel : Expr → Expr) (g : Expr → TM Expr) : TM Expr := do
    let y ← rowLocal "y" α
    let hy ← rowLocal "hy" (rel y.expr)
    return mkLambda #[y, hy] (← g y.expr)
  -- the induction step at summand `j`
  let branch (j : Nat) (w : Local) : TM Expr := do
    let xl ← injL j w.expr
    let xi ← injI j w.expr
    let ih ← rowLocal "ih" (← ihType xl)
    let gA ← guarded αL (sL.relAt · xl) fun y => pure (Expr.mkApp sL.head y)
    let gB ← guarded sI.fix.domain (sI.relAt · xi) fun y => pure (Expr.mkApp sI.head y)
    let gPhi ← guarded αL (sL.relAt · xl) phi
    let ty := atC xl
    let fL := Expr.mkApp sL.fix.functional xl
    let fI := Expr.mkApp sI.fix.functional xi
    let lhs := Expr.mkApp sL.head xl
    let rhs := Expr.mkApp sI.head xi
    -- K : gA = gΦ, from the induction hypothesis
    let y ← rowLocal "y" αL
    let hy ← rowLocal "hy" (sL.relAt y.expr xl)
    let splitMotive (t : Expr) : TM Expr := do
      let m ← rowLocal "m" (← motM t)
      return mkForall #[m] (eqAt t (Expr.mkApp sL.head t) (← phi t))
    let split ← cases Level.mkZero splitMotive y.expr fun k w' => do
      let m ← rowLocal "m" (← motM (← injL k w'.expr))
      return mkLambda #[m] m.expr
    let atY := Expr.mkApp split (mkAppN ih.expr #[y.expr, hy.expr])
    let recLevel := mkLevelIMax' Level.mkZero vL
    let inner := mkAppN (Expr.mkConst nFunext #[Level.mkZero, vL])
      #[hy.type, mkLambda #[hy] (atC y.expr), Expr.mkApp gA y.expr, Expr.mkApp gPhi y.expr,
        mkLambda #[hy] atY]
    let kProof := mkAppN (Expr.mkConst nFunext #[uL, recLevel])
      #[αL, mkLambda #[y] (mkForall #[hy] (atC y.expr)), gA, gPhi, mkLambda #[y] inner]
    let congr := mkAppN (Expr.mkConst nCongrArg #[mkLevelIMax' uL recLevel, vL])
      #[mkForall #[y, hy] (atC y.expr), ty, gA, gPhi, fL, kProof]
    let refl := mkAppN (Expr.mkConst nEqRefl #[vL]) #[ty, Expr.mkApp fL gPhi]
    let symm := mkAppN (Expr.mkConst nEqSymm #[vL]) #[ty, rhs, Expr.mkApp fI gB, sI.fix.eqAt xi]
    let trans (a b p q : Expr) : Expr := mkAppN (Expr.mkConst nEqTrans #[vL]) #[ty, a, b, rhs, p, q]
    let chain := trans lhs (Expr.mkApp fL gA) (sL.fix.eqAt xl)
      (trans (Expr.mkApp fL gA) (Expr.mkApp fL gPhi) congr
        (trans (Expr.mkApp fL gPhi) (Expr.mkApp fI gB) refl symm))
    return mkLambda #[ih] chain
  let x ← rowLocal "x" αL
  let ih ← rowLocal "ih" (← ihType x.expr)
  let stepMotive (t : Expr) : TM Expr := do
    let h ← rowLocal "ih" (← ihType t)
    return mkForall #[h] (← motM t)
  let stepTree ← cases Level.mkZero stepMotive x.expr branch
  let step := mkLambda #[x, ih] (Expr.mkApp stepTree ih.expr)
  let xm ← rowLocal "x" αL
  let motive := mkLambda #[xm] (← motM xm.expr)
  let relation := mkLambda
    #[{ fvar := sL.relY, userName := Name.mkStr Name.mkAnon "y", type := αL, bi := .default },
      { fvar := sL.relX, userName := Name.mkStr Name.mkAnon "x", type := αL, bi := .default }] sL.rel
  let wf ← if sL.fix.nat then do
      let measure ← TM.idx sL.fix.args 2 "row: the measure of `Nat.fix`"
      let nat := Expr.mkConst nNat #[]
      let ltRel := Expr.mkConst nNatLtWfRel #[]
      pure (mkAppN (Expr.mkConst nInvImageWf #[uL, lvlOne])
        #[αL, nat, mkAppN (Expr.mkConst nWFRelRel #[lvlOne]) #[nat, ltRel], measure,
          mkAppN (Expr.mkConst nWFRelWf #[lvlOne]) #[nat, ltRel]])
    else TM.idx sL.fix.args 3 "row: the well-foundedness proof of `WellFounded.fix`"
  -- `M xL`, which is `A xL = B xI`: Lean's body is the transported one
  let mut proof := mkAppN (Expr.mkConst nWFInduction #[uL]) #[αL, relation, wf, motive, xL, step]
  -- funext over the parameters, innermost first
  for j in (List.range arity).reverse do
    let p ← TM.idx ps j "row: parameter"
    let (dom, rest) ← TM.idx tele j "row: parameter type"
    let u ← rowSome "no sort for a parameter's type" (sortOf? const? ps dom)
    let v ← rowSome "no sort for a parameter's codomain" (sortOf? const? ps rest)
    proof := mkAppN (Expr.mkConst nFunext #[u, v])
      #[dom, mkLambda #[p] rest, mkLambda (ps.extract j arity) bodyL, mkAppN rhs (pes.extract 0 j),
        mkLambda #[p] proof]
  return proof

/-! ## Rows -/

/-- The row of the member `f` of a well-founded `plan`, with the encoding
set `enc` (`encodingSet`). -/
def rowOfWith (const? : Name → Option ConstantInfo) (plan : CliquePlan) (enc : Std.HashSet Name)
    (f : Name) : Except String ConstantInfo := do
  let some index := plan.all.idxOf? f | throw s!"row: {f.pretty} is not a member of the clique"
  if plan.aliases.any (·.1 == f) then
    throw s!"row: {f.pretty} is an alias (its value is its representative's, at another summand)"
  let some md := plan.members.get? f | throw s!"row: {f.pretty} is not a transported member"
  let some ci := const? f | throw s!"row: {f.pretty} is not in the input"
  let some leanValue := valueOf? ci | throw s!"row: {f.pretty} has no value"
  let cv := ci.getCnst
  let rhs := Expr.mkConst f (cv.levelParams.map Level.mkParam)
  let some u := sortOf? const? #[] cv.type | throw s!"row: no sort for the type of {f.pretty}"
  let leanDecl? (p : Name) : Option Decl := if enc.contains p then (const? p).bind Decl.ofConstantInfo? else none
  let ixDecl? (p : Name) : Option Decl := (plan.canon.find? (·.1.name == p)).map (·.1)
  let proof ← (rowProof const? leanDecl? ixDecl? plan.all.size plan.sigma index cv.type leanValue md.value
    rhs).run'
  -- every Lean encoding constant the row mentions has a copy
  let outside (c : Name) : Bool := isEncodingName plan.all c && !enc.contains c
  if let some c := (constOccurrences outside leanValue ++ constOccurrences outside proof)[0]? then
    throw s!"row: the row of {f.pretty} references the encoding constant {c.pretty}, which has no copy"
  let name := rowName f
  let type := mkAppN (Expr.mkConst nEq #[u]) #[cv.type, rowLhs enc leanValue, rhs]
  return .thmInfo { cnst := { name, levelParams := cv.levelParams, type },
                    value := renameConsts (srcRename enc) proof, all := #[name] }

/-- The row `f._ix.row` of the member `f` (see the module note): `none` for
a plan that is not well-founded, an error where the recipe does not apply
(the wiring keeps Lean's form then). -/
def rowOf (const? : Name → Option ConstantInfo) (plan : CliquePlan) (f : Name) :
    Except String (Option ConstantInfo) := do
  unless plan.encoding == .wellFounded do return none
  let enc ← encodingSet const? plan
  return some (← rowOfWith const? plan enc f)

/-- Every record a well-founded plan adds: the copies of its encoding set,
then the rows of its transported members, each in pretty-name order of the
names they get (see `Hook`'s note on ties); both empty for another
encoding. An encoding constant that is not a definition or a theorem is an
error, and so is any member's refusal. -/
def rowsOf (const? : Name → Option ConstantInfo) (plan : CliquePlan) :
    Except String (Array ConstantInfo × Array ConstantInfo) := do
  unless plan.encoding == .wellFounded do return (#[], #[])
  let enc ← encodingSet const? plan
  let names := enc.toArray.qsort fun a b => (srcName a).pretty < (srcName b).pretty
  let copies ← names.mapM fun c => match const? c with
    | some ci@(.defnInfo _) | some ci@(.thmInfo _) => pure (srcCopy enc ci)
    | some _ => throw s!"row: the encoding constant {c.pretty} is not a definition or a theorem"
    | none => throw s!"row: the encoding constant {c.pretty} is not in the input"
  let members := (rowMembers plan).qsort fun a b => (rowName a).pretty < (rowName b).pretty
  let rows ← members.mapM (rowOfWith const? plan enc)
  return (copies, rows)

end Ix.Compile.Pass.Clique

end
