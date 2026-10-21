/-
  Ix.Compile.Pass.Clique.Structural: the transport of a structural clique.
  Structural recursion has no packed function to rename and no measure: the
  transport re-associates the packings and reorders telescopes.

  Lean's encoding (`Elab/PreDefinition/Structural`, Lean 4.34.1), as the
  transport sees it:

  * the functions are grouped by the type former of their recursive argument
    (`Positions.groupAndSort`); the groups follow the inductive's `all` order
    (nested auxiliaries included), and **within a group the functions are in
    clique order**, the only place the clique order enters;
  * per type former, the packed motive `λ is x. R₀ ×' (R₁ ×' …)` (`PProd`, or
    `And` for propositions; the motive itself for a singleton group) is passed
    to `T.brecOn`/`T.below` (`PProdN.packLambdas`);
  * each function's functional `f._f : ∀ fixed is x (f : T.below … x) …`,
    whose body reaches a recursive call through a path into the `below`
    dictionary (`searchPProd`): a prefix that walks the inductive's `below`
    structure, then the position inside the packed motive;
  * the members `f := λ ys. (T.brecOn ps motives is x F₁ … F_K).2.1 rest`,
    `F_k = λ is x f. ⟨g₀._f fixed is x f, …⟩` the packed functionals;
  * for an inductive predicate (`IndPred`), `let funType_i := …` in clique
    order around the body, the functionals inline, and "below" matchers
    (`IndPredBelow.mkBelowMatcher`) closing over the `funType` lets in clique
    order (their first parameters when they close over nothing else);
  * the fixed parameters in the first function's order (in every `_f`).

  `Φ_σ` re-associates, per group `k` (with `σ_k`, the restriction of `σ`):
  the packed motives at the motive positions of every `below`/`brecOn`
  application of the block, the packed functionals at `brecOn`'s functional
  positions, the members' projections out of `brecOn`, and the motive-part of
  every path into a `below` dictionary, found, as Lean finds it, by reducing
  the dictionary's type with canaries in place of the packed motives
  (`Whnf.lean`); a path through a reflexive field `f : A → T` applies the
  field's entry to the argument in the middle of the path, and the walk
  instantiates the entry's `∀` there, as `toBelowAux` does. The `let funType`
  telescope is reordered, and with it the first `n` parameters of every below
  matcher, in its declaration and at its applications alike; the `_f`
  telescopes too. Nothing else moves: the prefix of a path, the bodies, the
  matchers' alternatives, the recursive argument's position.

  **The `below`/`brecOn` family is authenticated, never found by name.** The
  block is the inductive of the members' `brecOn` head; it must be recursive
  (`isRec`: Lean generates the family only then). `familyCandidates` lists
  every name the transport may treat as the block's family: per motive
  position its `below` and `brecOn` (`T.below`, `T.brecOn` for `T` in `all`,
  then `all₀.below_k`, `all₀.brecOn_k` for the nested auxiliaries), and the
  `.go`/`.eq` the input has under the `brecOn` names. The caller keeps the
  ones `Ix.AuxGen.SourceFamily.filterHeads env all candidates` authenticates
  (each equal to what Lean's generators build from the block's source
  recursors) and passes that set to `structLayout` (`family`); this module
  does not import the authentication (it needs the compiler's environment).
  `blockOf` refuses a block one of whose `below`/`brecOn` names is not in the
  set, and an encoding constant of the family (`isEncodingConst`) is a name
  with a prefix in the set (`T.brecOn.go`, the constructors and `casesOn` of
  an inductive predicate's `T.below`).

  **A matcher is recognised by its declaration, not by its name.** A
  `match_*` name is only a pre-filter: an auxiliary is a below matcher
  (`StructLayout.matchers`) only when its declaration has the shape the
  transport relies on (`matcherShape?`). Any other auxiliary, whatever its
  name, is an ordinary constant (in particular, the ownership rules below
  apply to it as to any constant).

  Unsupported shapes are outside the grammar and leave the clique in Lean's
  form (the fallback is the baseline): a dictionary passed whole to a helper
  other than an eliminator, a path the walk cannot follow, a projection of a
  `brecOn` result that is not a full path, an unauthenticated family, or a
  carried equation lemma of a repacked group that cannot be regenerated.
  `StructuralEq` builds an unfolding proof from the unchanged statement and
  the actual `casesOn`; it does not transport Lean's old packed proof.
-/
module
public import Ix.Compile.Pass.Clique.Packing
public import Ix.Compile.Pass.Clique.Telescope
public import Ix.Compile.Pass.Clique.Whnf
public import Ix.Compile.Pass.Clique.WF
public import Ix.Compile.Pass.Clique.StructuralEq
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata peelForalls mkForalls)
open Ix.Compile.Image (forallArity)

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

/-- The canonical packed-motive spine (for the projections' structure
names); `none` when `perm` is not a permutation of the leaves. -/
def Group.canonSpine (g : Group) : Option Spine := g.spine.permute g.perm

/-! ## Eliminators and matchers -/

/-- The shape of an eliminator (a matcher or a `casesOn`) that receives an
owned dictionary past its declared arity (`MatcherApp.addArg`), read off its
declaration: the declared arity, for each declared parameter its number of
fields when it is an alternative (a parameter whose type concludes in an
earlier parameter), and the motives (the parameters the alternatives conclude
in) with their own arities. `none` when the constant is not in the input. -/
structure ElimShape where
  arity : Nat
  alts : Array (Option Nat)
  motives : Array (Nat × Nat)

def elimShapeOf? (const? : Name → Option ConstantInfo) (c : Name) : Option ElimShape := do
  let ci ← const? c
  let ty := ci.getCnst.type
  let ar := forallArity ty
  let (ps, _) := peelForalls ar ty #[]
  let mut alts : Array (Option Nat) := #[]
  let mut motives : Array (Nat × Nat) := #[]
  for ((_, pt, _), k) in ps.zipIdx do
    let fc := forallArity pt
    let (_, concl) := peelForalls fc pt #[]
    match (getAppFnArgs (stripMdata concl)).1 with
    | .bvar i _ =>
      if i ≥ fc && i - fc < k then
        alts := alts.push (some fc)
        let mk := k - 1 - (i - fc)
        unless motives.any (·.1 == mk) do
          let (_, mt, _) ← ps[mk]?
          motives := motives.push (mk, forallArity mt)
      else alts := alts.push none
    | _ => alts := alts.push none
  return { arity := ar, alts, motives }

/-- The shape of a below matcher, read off its declared type (see
`matcherShape?`), in argument positions (a `let` of the telescope is not an
argument): the declared arity, the motive's position, the number of
discriminants, and each argument's declared domain. -/
structure MatcherShape where
  arity : Nat
  motive : Nat
  discrs : Nat
  domains : Array Expr
  deriving Inhabited, BEq

/-- `c` is `T.casesOn` for an inductive `T` of the input. -/
def isCasesOn (const? : Name → Option ConstantInfo) : Name → Bool
  | .str p "casesOn" _ => match const? p with
    | some (.inductInfo _) => true
    | _ => false
  | _ => false

/-- `c` is a definition of the input whose value, after its leading `λ`s,
applies a recursor of the input: Lean's sparse `casesOn`
(`mkSparseCasesOn`), which its match compiler names after the declaration
that needed it, not after the inductive. -/
def isRecursorDef (const? : Name → Option ConstantInfo) (c : Name) : Bool :=
  if let some (.defnInfo v) := const? c then
    if let some (r, _, _) := constApp? (peelLams (lamArity v.value) v.value #[]).2 then
      const? r matches some (.recInfo _)
    else false
  else false

/-- The pre-filter of the matchers: the last component starts with
`match_`. It decides nothing alone (`matcherShape?`). -/
def isMatcherName : Name → Bool
  | .str _ s _ => s.startsWith "match_"
  | _ => false

/-- The binders of a declaration's type (`∀`, `lam := false`) or value (`λ`,
`lam := true`), through `let`s and `mdata`: each binder's domain, with its
value for a `let`; and the body. -/
def bindersThroughLets (lam : Bool) :
    Expr → Array (Expr × Option Expr) → Array (Expr × Option Expr) × Expr
  | e@(.forallE _ t b _ _), acc => if lam then (acc, e) else bindersThroughLets lam b (acc.push (t, none))
  | e@(.lam _ t b _ _), acc => if lam then bindersThroughLets lam b (acc.push (t, none)) else (acc, e)
  | .letE _ t v b _ _, acc => bindersThroughLets lam b (acc.push (t, some v))
  | .mdata _ e _, acc => bindersThroughLets lam e acc
  | e, acc => (acc, e)

/-- The auxiliary `d` is a below matcher whose first `numPermuted` arguments
the transport may permute, recognised by its declaration (the one in the
input, `const? d.name`, which `d` must be), never by its name. It checks
exactly:

* the declaration is a definition, `d` is it (same type and value), and its
  value does not mention its own name (not recursive);
* its type is a telescope `(p₁ … p_m) (motive) (d₁ … d_k) (h₁ … h_r)` ending
  in `motive d₁ … d_k`, where the parameters `p` may be interleaved with
  `let`s and every later binder is a `∀`: the conclusion is a binder (the
  motive) applied to exactly the `k` binders that follow it, in order (the
  discriminants); the motive's own type is a telescope of `k` binders ending
  in a sort; every binder after the discriminants is an alternative, whose
  type concludes in the motive;
* the arguments the transport permutes are parameters before the motive:
  `1 ≤ numPermuted ≤ m` (`m` counts the `∀` parameters, not the `let`s);
* its value is the same telescope (a `λ` with the same domain for each `∀`,
  the same `let`s), whose body (up to `mdata`) is an eliminator application:
  `T.casesOn` of an inductive `T` of the input, a recursor-based definition of
  the input (`isRecursorDef`), or a matcher already accepted (`accepted`),
  whose declaration `elimShapeOf?` reads, applied to at least its declared
  arity.

Lean's below matchers (`IndPredBelow.mkBelowMatcher`, through
`Match.mkMatcher`) have this shape: the closure first (the fixed parameters
the match mentions, then the `funType` lets, as `∀` parameters or kept as
`let`s), then motive, discriminants (the predicate's indices and proof, and
its `below` proof) and alternatives, the body a `casesOn` (usually
`T.below.casesOn` on the `below` discriminant, with `Eq.refl`/`HEq.refl`
extra arguments). Every below matcher of Lean's library and of the clique
fixtures passes, with the shape Lean's `MatcherInfo` records. The transport
permutes the first `numPermuted` arguments, which are the `funType`
parameters exactly when the matcher closes over nothing else. -/
def matcherShape? (const? : Name → Option ConstantInfo) (accepted : Name → Bool)
    (numPermuted : Nat) (d : Decl) : Option MatcherShape := do
  let some (.defnInfo v) := const? d.name | none
  unless !d.isThm && v.cnst.type == d.type && v.value == d.value do none
  if mentions d.name v.value then none
  let (ps, concl) := bindersThroughLets false v.cnst.type #[]
  let n := ps.size
  let (hd, ds) := getAppFnArgs (stripMdata concl)
  let .bvar mv _ := stripMdata hd | none
  unless mv < n do none
  -- the motive is binder `mt`, discriminant `j` binder `mt + 1 + j`
  let mt := n - 1 - mv
  let k := ds.size
  unless mt + k < n && (ps.extract mt n).all (·.2.isNone) do none
  unless ds.zipIdx.all (fun (x, j) => match stripMdata x with
      | .bvar b _ => b == n - 2 - mt - j
      | _ => false) do none
  let (mty, _) ← ps[mt]?
  let (mbs, mres) := peelForalls k mty #[]
  unless mbs.size == k && (stripMdata mres matches .sort ..) do none
  -- every later binder `q` concludes in the motive (`bvar (q - 1 - mt)` in
  -- its context, under its own `fc` binders)
  unless (ps.zipIdx.extract (mt + k + 1) n).all (fun ((pt, _), q) =>
      let fc := forallArity pt
      let (_, c) := peelForalls fc pt #[]
      match (getAppFnArgs (stripMdata c)).1 with
      | .bvar i _ => i == q - 1 - mt + fc
      | _ => false) do none
  let motive := mt - (ps.filter (·.2.isSome)).size
  unless 1 ≤ numPermuted && numPermuted ≤ motive do none
  let (vs, body) := bindersThroughLets true v.value #[]
  unless vs == ps do none
  let some (h, _, bargs) := constApp? body | none
  unless accepted h || isCasesOn const? h || isRecursorDef const? h do none
  let sh ← elimShapeOf? const? h
  unless sh.arity ≤ bargs.size do none
  return { arity := n - (ps.filter (·.2.isSome)).size, motive, discrs := k,
           domains := ps.filterMap fun (t, x) => if x.isNone then some t else none }

/-! ## The layout -/

structure StructLayout where
  n : Nat
  sigma : Array Nat
  const? : Name → Option ConstantInfo
  numParams : Nat
  numMotives : Nat
  aux : Std.HashMap Name BlockAux
  /-- the block's authenticated `below`/`brecOn` family (`familyCandidates`) -/
  family : Std.HashSet Name
  groups : Array Group
  fNames : Std.HashSet Name
  numFixed : Nat
  fixedPerm : Array Nat
  /-- the below matchers, with their shapes (`matcherShape?`) -/
  matchers : Std.HashMap Name MatcherShape := {}
  /-- IndPred: the number of `funType` lets (`n`), else `0` -/
  numFunTypes : Nat := 0
  /-- new position `p` ↦ Lean position (`invPerm sigma`), for the `funType`
  telescope and the matchers' `funType` binders -/
  funPerm : Array Nat := #[]
  /-- per member (Lean's order): the member's parameter (outermost `0`) at
  each fixed position of its functionals' applications -/
  memberFixed : Array (Array Nat) := #[]
  /-- per functional `f._f`: the number of its binders after the fixed
  parameters (indices, major, then the `below` dictionary when the number is
  the arity plus one) and its group's arity -/
  fDepth : Std.HashMap Name (Nat × Nat) := {}
  /-- enforce the ownership of the `below` dictionaries (see "Ownership");
  off for a theorem clique, whose terms are proofs -/
  checkOwnership : Bool := true
  deriving Inhabited

/-- Some type former's group packs two or more functions in an order the
transport changes (`perm` is not the identity): only then does the clique
have packed motives, tuples and paths to re-associate. -/
def StructLayout.repacks (L : StructLayout) : Bool :=
  L.groups.any fun g => g.size ≥ 2 && g.perm != idPerm g.size

def StructLayout.elimShape? (L : StructLayout) (c : Name) : Option ElimShape :=
  elimShapeOf? L.const? c

/-- `n` or one of its prefixes is in `family`. -/
def underFamily (family : Std.HashSet Name) : Name → Bool
  | n@(.anonymous _) => family.contains n
  | n@(.str p _ _) => family.contains n || underFamily family p
  | n@(.num p _ _) => family.contains n || underFamily family p

/-- `c` is a constant of the recursion's encoding: a functional `f._f`, a
below matcher, or a name with a prefix in the authenticated family (a
`below`/`brecOn` constant of the block or a constant under one:
`T.brecOn.go`, `T.brecOn.eq`, the constructors of an inductive `T.below`). -/
def StructLayout.isEncodingConst (L : StructLayout) (c : Name) : Bool :=
  L.fNames.contains c || L.matchers.contains c || underFamily L.family c

/-- `e` mentions a constant satisfying `p`. -/
def mentionsWhere (p : Name → Bool) (e : Expr) : Bool :=
  foldConsts (fun _ n => if p n then .done true else .yield false) false e

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
  match s.projSteps idx with
  | some st => st.map (·.1) == steps.map (·.1)
  | none => false

/-- Re-associate the start of `steps` (a path into group `g`'s packed
motive) and keep the rest. -/
def transportPath (g : Group) (steps : Array (Name × Nat)) : Except String (Array (Name × Nat)) := do
  if g.size < 2 then return steps
  let some (idx, len) := pathPrefix g.size steps | throw "grammar: a projection of a packed value that is not a path"
  let part := steps.extract 0 len
  unless stepsFit g.spine idx part do throw "grammar: a path whose projections are not the packing's"
  let some p := g.perm[idx]? | throw "grammar: a path into a packed motive past its group"
  let some canon := g.canonSpine | throw "grammar: a packed motive whose group order is not a permutation"
  let some st := canon.projSteps p | throw "grammar: a path into a packed motive past its group"
  return st ++ steps.extract len steps.size

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
def projPrefix (steps : Array PStep) : Array (Name × Nat) × Array PStep :=
  let k := (steps.findIdx? fun st => st matches .app _).getD steps.size
  ((steps.extract 0 k).filterMap fun st => match st with
      | .proj s j => some (s, j)
      | .app _ => none,
    steps.extract k steps.size)

/-- The motive-part of a path into a `below` dictionary of type `ty`:
replay Lean's `searchPProd` and `toBelowAux` (`Structural/BRecOn.lean`) with
canaries for the packed motives. The walk follows the `PProd`/`And` nodes of
the dictionary's weak head normal form, and passes through a reflexive
field's entry (a `∀`) by instantiating it at the path's argument, until it
reaches an entry `C_j t`; the projections that follow select the function
inside group `j`'s packed motive and are re-associated. `none` when the
steps end inside the dictionary before any entry (a part of the dictionary,
independent of the clique). A step the walk cannot follow (a weak head normal
form that is neither a node nor a `∀`, or another structure than the node's,
or an exhausted reducer) is a grammar failure: such a path might reach into
the packed motives in a way the walk does not see, so it is never left
alone. -/
def belowPath (L : StructLayout) (ty : Expr) (steps : Array PStep) :
    TM (Option (Array PStep)) := do
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
        let g ← TM.idx L.groups j "structural: the group of a dictionary entry"
        let (projs, tail) := projPrefix (steps.extract (t + 1) steps.size)
        let projs' ← liftE (transportPath g projs)
        return some (steps.extract 0 (t + 1) ++ projs'.map (fun (s, i) => PStep.proj s i) ++ tail)
      | none => throw "grammar: a path into a below dictionary that reaches a foreign variable"
    | _ => pure ()
  return none

/-! ## Ownership of the `below` dictionaries

A path into a `below` dictionary is re-associated only when the dictionary is
the recursion's own, decided by where the variable is bound and never by its
type:

* the dictionary binder of a functional `f._f` (the binder after the indices
  and the major, `fDepth`), and the dictionary binder of each packed
  functional handed to the members' `brecOn`;
* the binders that receive an owned dictionary through a matcher or a
  `casesOn` (`MatcherApp.addArg`): the arguments past the eliminator's
  declared arity are passed to the trailing binders of every alternative (a
  parameter whose type concludes in an earlier parameter, the motive), after
  that alternative's own fields.

An owned dictionary passed to a below matcher (`StructLayout.matchers`) must
sit at one of its discriminants whose declared type is a `below` of the block
(the dictionary the below matcher eliminates) or past its declared arity (an
extra argument, which the alternatives' trailing binders receive and the
binder rules check); anywhere else (a `funType` parameter, the motive, an
alternative) is a refusal.

A user's binder whose type is a `below` of the block, a path into a `below`
value that is not owned, an owned dictionary passed whole anywhere else, and a
`brecOn` application of the block outside a member's root are outside the
grammar: the clique stays in Lean's form. Lean's own encoding never produces
them; user code can (a user `Nat.brecOn` whose motive has the packing's
shape, a user `below` binder read through primitive projections). A theorem
clique is exempt: its terms are proofs, so a wrong path can make the kernel
reject but cannot change a value. -/

/-- `ty` is a `below` of the block (by its head constant). -/
def StructLayout.isBelowTy (L : StructLayout) (ty : Expr) : Bool :=
  match constApp? (stripMdata ty) with
  | some (c, _, _) => match L.aux.get? c with
    | some a => !a.isBrecOn
    | none => false
  | none => false

/-- `c` is a `brecOn` constant of the block. -/
def StructLayout.isBrecOnConst (L : StructLayout) (c : Name) : Bool :=
  match L.aux.get? c with
  | some a => a.isBrecOn
  | none => false

/-- The number of occurrences of the block's `brecOn` constants in `e`,
counted in the unshared tree (an occurrence in a shared subterm counts once
per occurrence of the subterm), memoised by the subterm. -/
def StructLayout.brecOnCount (L : StructLayout) (e : Expr) : Nat := (go e).run' {}
where
  go : Expr → StateM (Std.HashMap Expr Nat) Nat
    | .const c _ _ => pure (if L.isBrecOnConst c then 1 else 0)
    | e@(.app f a _) => cached e do pure ((← go f) + (← go a))
    | e@(.lam _ t b _ _) | e@(.forallE _ t b _ _) => cached e do pure ((← go t) + (← go b))
    | e@(.letE _ t v b _ _) => cached e do pure ((← go t) + (← go v) + (← go b))
    | e@(.proj _ _ x _) | e@(.mdata _ x _) => cached e (go x)
    | _ => pure 0
  cached (e : Expr) (k : StateM (Std.HashMap Expr Nat) Nat) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some r := (← get).get? e then return r
    let r ← k
    modify (·.insert e r)
    return r

/-- With ownership enforced, the owned arguments (`owned`, by position) of
an application of the below matcher `c` of shape `sh`: each must be one of
its discriminants whose declared type is a `below` of the block, or past its
declared arity (see "Ownership"). -/
def StructLayout.checkMatcherOwnership (L : StructLayout) (c : Name) (sh : MatcherShape)
    (owned : Array Bool) : Except String Unit := do
  for (o, i) in owned.zipIdx do
    if !o || i ≥ sh.arity then continue
    let declaredBelow := match sh.domains[i]? with
      | some t => L.isBelowTy t
      | none => false
    let isBelowDiscr := sh.motive < i && i ≤ sh.motive + sh.discrs && declaredBelow
    unless isBelowDiscr do
      throw s!"grammar: a below dictionary passed to the matcher {c} outside its below discriminants"

/-! ## `Φ_σ` -/

/-- The binder context of the structural `Φ`: Lean's binder types,
outermost first, each with its ownership (the recursion's own `below`
dictionary), and the running hash of the entries, the context's part of the
memo key (`phiSFix`), so that a push costs O(1). -/
structure SCtx where
  entries : Array (Expr × Bool) := #[]
  hash : UInt64 := 7
  deriving Inhabited

def SCtx.push (c : SCtx) (t : Expr) (owned : Bool) : SCtx :=
  { entries := c.entries.push (t, owned)
    hash := mixHash (mixHash c.hash (Hashable.hash t)) (if owned then 11 else 13) }

def SCtx.ofArray (xs : Array (Expr × Bool)) : SCtx :=
  xs.foldl (fun c (t, o) => c.push t o) {}

/-- The binder `bvar i` refers to: its type (in its own context) and its
ownership; `none` for a variable bound outside the context. -/
def SCtx.get? (c : SCtx) (i : Nat) : Option (Expr × Bool) :=
  if i < c.entries.size then c.entries[c.entries.size - 1 - i]? else none

/-- The packed motive at motive position `j` of a `below`/`brecOn`
application of the block, in canonical order (its leaves transported by
`go`). -/
def phiSMotive (L : StructLayout) (go : SCtx → Expr → TM Expr)
    (ctx : SCtx) (j : Nat) (arg : Expr) : TM Expr := do
  let g ← TM.idx L.groups j "structural: the group of a motive position"
  if g.size < 2 then return ← go ctx arg
  let (bs, body) := peelLams g.arity arg #[]
  let mut ctx' := ctx
  let mut bs' := #[]
  for (nm, t, bi) in bs do
    bs' := bs'.push (nm, ← go ctx' t, bi)
    ctx' := ctx'.push t false
  let some s := decodeSpine .pprod g.size body
    | throw "grammar: a packed motive that is not Lean's"
  let leaves ← s.leaves.mapM (go ctx')
  let some s' := ({ s with leaves } : Spine).permute g.perm
    | throw "grammar: a packed motive whose group order is not a permutation"
  return mkLams bs' (← s'.typeM "grammar: a packed motive")

/-- The type of an owned dictionary binder (or of a matcher motive's binder
built from one, `MatcherApp.addArg`): a `below` application of the block has
its motives permuted. These are the only places where Lean's encoding writes
a `below` application in a definition clique, so with ownership enforced no
other `below` application is touched (a user's `below` application keeps its
motive). Anything else is `go`. -/
def phiSDictType (L : StructLayout) (go : SCtx → Expr → TM Expr)
    (ctx : SCtx) (t : Expr) : TM Expr := do
  let (h, args) := getAppFnArgs t
  match h with
  | .const c _ _ =>
    match L.aux.get? c with
    | some a =>
      if a.isBrecOn then return ← go ctx t
      let P := L.numParams
      let K := L.numMotives
      let args' ← args.zipIdx.mapM fun (x, i) =>
        if P ≤ i && i < P + K then phiSMotive L go ctx (i - P) x else go ctx x
      return mkAppN h args'
    | none => go ctx t
  | _ => go ctx t

/-- One step of `Φ_σ` on a structural clique's term, in a context of binder
types (Lean's, outermost first) each with its ownership (the recursion's own
`below` dictionary); `go ctx` is `Φ_σ` on subterms. -/
def phiSStep (L : StructLayout) (go : SCtx → Expr → TM Expr)
    (ctx : SCtx) (e : Expr) : TM Expr := do
  let underBinders (n : Nat) (lam : Bool) (x : Expr) (owned : Nat → Bool)
      (k : SCtx → Expr → TM Expr) : TM Expr := do
    -- transform `n` leading binders of `x` and the body with `k`
    let (bs, body) := if lam then peelLams n x #[] else peelForalls n x #[]
    let mut ctx' := ctx
    let mut bs' := #[]
    for ((nm, t, bi), i) in bs.zipIdx do
      bs' := bs'.push (nm, ← (if owned i then phiSDictType L go ctx' t else go ctx' t), bi)
      ctx' := ctx'.push t (owned i)
    let body' ← k ctx' body
    return if lam then mkLams bs' body' else mkForalls bs' body'
  let ownedArg (x : Expr) : Bool := match stripMdata x with
    | .bvar i _ => match ctx.get? i with
      | some (_, o) => o
      | none => false
    | _ => false
  -- the packed functional at functional position `j`; its last binder is
  -- the dictionary `brecOn` builds
  let functional (j : Nat) (arg : Expr) : TM Expr := do
    let g ← TM.idx L.groups j "structural: the group of a functional position"
    let dict (i : Nat) : Bool := i == g.arity
    if g.size < 2 then return ← underBinders (g.arity + 1) true arg dict fun ctx' body => go ctx' body
    underBinders (g.arity + 1) true arg dict fun ctx' body => do
      let some (s, cs) := decodeTuple g.size body
        | throw "grammar: a packed functional that is not Lean's"
      let leaves ← s.leaves.mapM (go ctx')
      let cs ← cs.mapM (go ctx')
      let some s' := ({ s with leaves } : Spine).permute g.perm
        | throw "grammar: a packed functional whose group order is not a permutation"
      let some cs' := permute g.perm cs
        | throw "grammar: a packed functional whose group order is not a permutation"
      let some tuple := mkTuple s' cs'
        | throw "grammar: a packed functional with fewer components than its packing"
      return tuple
  match e with
  | .proj .. =>
    -- a path of projections and applications from a variable: a path into a
    -- `below` dictionary when the variable is one (the applications are a
    -- reflexive field's arguments, transported as terms)
    let (gsteps, gbase) := pathChain e
    if let .bvar i _ := stripMdata gbase then
      if let some (t, owned) := ctx.get? i then
        let ty := liftLoose t (i + 1)
        match ← belowPath L ty gsteps with
        | some steps' =>
          if L.checkOwnership && !owned then
            throw "grammar: a path into a below dictionary that is not the recursion's own"
          let steps'' ← steps'.mapM fun st => do match st with
            | .app a => return PStep.app (← go ctx a)
            | s => return s
          return applySteps steps'' gbase
        | none => pure ()
    let (steps, base) := projChain e
    match stripMdata base with
    | .bvar _ _ => return applyProjs steps base
    | base' =>
      let brecOn? : Option BlockAux := match constApp? base' with
        | some (c, _, _) => match L.aux.get? c with
          | some a => if a.isBrecOn then some a else none
          | none => none
        | none => none
      let b ← go ctx base'
      match brecOn? with
      | some a =>
        let g ← TM.idx L.groups a.pos "structural: the group of a brecOn application"
        let steps' ← liftE (transportPath g steps)
        return applyProjs steps' b
      | none => return applyProjs steps b
  | .app .. =>
    let (h, args) := getAppFnArgs e
    match h with
    | .const c _ _ =>
      if let some a := L.aux.get? c then
        -- with ownership enforced, a `below` application here is not in an
        -- owned dictionary's binder type (those go through `phiSDictType`):
        -- it is the user's, and keeps its motive
        if !a.isBrecOn && L.checkOwnership then return mkAppN h (← args.mapM (go ctx))
        let P := L.numParams
        let K := L.numMotives
        let g ← TM.idx L.groups a.pos "structural: the group of a below/brecOn application"
        let fStart := P + K + g.arity
        let args' ← args.zipIdx.mapM fun (x, i) =>
          if P ≤ i && i < P + K then phiSMotive L go ctx (i - P) x
          else if a.isBrecOn && fStart ≤ i && i < fStart + K then functional (i - fStart) x
          else go ctx x
        return mkAppN h args'
      if L.fNames.contains c then
        if args.size < L.numFixed then throw "grammar: a partial application of a functional"
        let args' ← args.mapM fun x => if ownedArg x then pure x else go ctx x
        let some fixed := reorder L.fixedPerm args'
          | throw "grammar: a functional's fixed arguments do not fit its telescope"
        return mkAppN h (fixed ++ args'.extract L.numFixed args'.size)
      if let some msh := L.matchers.get? c then
        let m := L.numFunTypes
        if args.size < m then throw "grammar: a partial application of a below matcher"
        if L.checkOwnership then liftE (L.checkMatcherOwnership c msh (args.map ownedArg))
        let args' ← args.mapM fun x => if ownedArg x then pure x else go ctx x
        let some funTypes := reorder L.funPerm args'
          | throw "grammar: a below matcher's funType arguments do not fit the clique"
        return mkAppN h (funTypes ++ args'.extract m args'.size)
      if L.checkOwnership && args.any ownedArg then
        -- an owned dictionary passed to an eliminator past its declared
        -- arity: it reaches the trailing binders of the alternatives
        let some ci := L.const? c
          | throw s!"grammar: a below dictionary passed to {c}, which is not in the input"
        let ty := ci.getCnst.type
        let ar := forallArity ty
        unless ar ≤ args.size do throw s!"grammar: a below dictionary passed to a partial application of {c}"
        if (args.extract 0 ar).any ownedArg then throw s!"grammar: a below dictionary passed whole to {c}"
        let extras := (args.extract ar args.size).map ownedArg
        let (ps, _) := peelForalls ar ty #[]
        let some shape := L.elimShape? c
          | throw s!"grammar: a below dictionary passed to {c}, whose declaration cannot be read"
        let args' ← args.zipIdx.mapM fun (x, k) => do
          if let some (_, ma) := shape.motives.find? (·.1 == k) then
            -- the motive: its leading binders after its own are the
            -- extras' types, an owned dictionary's a `below` of the block
            unless lamArity x ≥ ma do throw s!"grammar: a motive of {c} that is not a function of its discriminants"
            underBinders ma true x (fun _ => false) fun ctx' body => do
              let (fs, rest) := peelForalls extras.size body #[]
              unless fs.size == extras.size do
                throw s!"grammar: a motive of {c} that does not bind the dictionary"
              let mut c' := ctx'
              let mut fs' := #[]
              for ((nm, t, bi), isOwned) in fs.zip extras do
                fs' := fs'.push (nm, ← (if isOwned then phiSDictType L go c' t else go c' t), bi)
                c' := c'.push t false
              return mkForalls fs' (← go c' rest)
          else if h : k < ps.size then
            let (_, pt, _) := ps[k]
            let fc := forallArity pt
            let (_, concl) := peelForalls fc pt #[]
            let isAlt := match (getAppFnArgs (stripMdata concl)).1 with
              | .bvar i _ => i ≥ fc && i - fc < k
              | _ => false
            if isAlt then
              unless lamArity x ≥ fc + extras.size do
                throw s!"grammar: an alternative of {c} that does not bind the dictionary"
              underBinders (fc + extras.size) true x
                (fun i => i ≥ fc && extras[i - fc]? == some true) fun ctx' body => go ctx' body
            else go ctx x
          else if ownedArg x then pure x else go ctx x
        return mkAppN h args'
      return mkAppN h (← args.mapM (go ctx))
    | _ =>
      if L.checkOwnership && args.any ownedArg then
        throw "grammar: a below dictionary passed to a term that is not an eliminator"
      return mkAppN (← go ctx h) (← args.mapM (go ctx))
  | .const c _ _ =>
    if L.fNames.contains c && L.numFixed > 0 then throw "grammar: a bare functional"
    if L.matchers.contains c && L.numFunTypes > 0 then throw "grammar: a bare below matcher"
    return e
  | .lam nm t b bi _ =>
    if L.checkOwnership && L.isBelowTy t then
      throw s!"grammar: a binder {nm.pretty} of a below type that is not the recursion's dictionary"
    return Expr.mkLam nm (← go ctx t) (← go (ctx.push t false) b) bi
  | .forallE nm t b bi _ => return Expr.mkForallE nm (← go ctx t) (← go (ctx.push t false) b) bi
  | .letE nm t v b nd _ =>
    if L.checkOwnership && L.isBelowTy t then
      throw s!"grammar: a let {nm.pretty} of a below type that is not the recursion's dictionary"
    return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push t false) b) nd
  | .bvar _ _ =>
    if L.checkOwnership && ownedArg e then
      throw "grammar: a below dictionary used whole outside an eliminator"
    return e
  | .mdata d x _ => return Expr.mkMData d (← go ctx x)
  | _ => return e

/-- `Φ_σ` with a context, memoised by the term, the context and the
ownership mode (`L.checkOwnership`). Within one transport the layout differs
only in that mode (the members and functionals of a definition clique with
ownership enforced, the carried lemmas without), and `phiSStep`'s result
depends on it (a `below` application outside an owned binder keeps its
motive with ownership enforced and is re-associated without), so a result is
shared only within one mode. The key mixes the term's hash, the context's
running hash and the mode; a hit is confirmed on all three. -/
def phiSFix (L : StructLayout) : Nat → SCtx → Expr → TM Expr
  | 0, _, _ => throw "Φ: recursion bound exhausted"
  | fuel + 1, ctx, e => do
    let own := L.checkOwnership
    let key := mixHash (mixHash (hash e) ctx.hash) (if own then 17 else 19)
    if let some (e', ctx', own', r) := (← get).cacheOwn.get? key then
      if e' == e && ctx' == ctx.entries && own' == own then return r
    let r ← phiSStep L (phiSFix L fuel) ctx e
    modify fun st => { st with cacheOwn := st.cacheOwn.insert key (e, ctx.entries, own, r) }
    return r

/-- `Φ_σ` in the context `ctx`, with the transport's bound. -/
def phiSC (L : StructLayout) (ctx : SCtx) (e : Expr) : TM Expr :=
  phiSFix L transportFuel ctx e

def phiS (L : StructLayout) (ctx : Array (Expr × Bool)) (e : Expr) : TM Expr :=
  phiSC L (SCtx.ofArray ctx) e

/-! ## The block and its family -/

/-- The inductive of a `brecOn` constant: `T` for `T.brecOn`, `all₀` for
`all₀.brecOn_k`. -/
def brecOnOwner : Name → Name
  | .str p _ _ => p
  | n => n

/-- Per motive position of the block of `iv` (the type formers of `all`,
then the nested auxiliaries): its `below`, `brecOn` and recursor names;
`none` for a block with nested auxiliaries and no type former. -/
def blockNames (iv : Ix.InductiveVal) : Option (Array (Name × Name × Name)) :=
  let all := iv.all
  (List.range (all.size + iv.numNested)).toArray.mapM fun j =>
    if h : j < all.size then
      let t := all[j]
      some (Name.mkStr t "below", Name.mkStr t "brecOn", Name.mkStr t "rec")
    else do
      let t ← all[0]?
      let k := j - all.size + 1
      some (Name.mkStr t s!"below_{k}", Name.mkStr t s!"brecOn_{k}", Name.mkStr t s!"rec_{k}")

/-- The names the transport may treat as the `below`/`brecOn` family of the
block of the `brecOn` constant `brecOn`, for the caller to authenticate: the
block's `all`, and per motive position its `below` and `brecOn`, then the
`.go`/`.eq` the input has under the `brecOn` names. The caller passes the
names `Ix.AuxGen.SourceFamily.filterHeads env all candidates` keeps as
`structLayout`'s `family`. `none` when `brecOn` is not under a recursive
inductive of the input (`blockOf` refuses those). -/
def familyCandidates (const? : Name → Option ConstantInfo) (brecOn : Name) :
    Option (Array Name × Array Name) := do
  let some (.inductInfo iv) := const? (brecOnOwner brecOn) | none
  if !iv.isRec then none
  let names ← blockNames iv
  let heads := names.flatMap fun (below, brec, _) => #[below, brec]
  let helpers := (names.flatMap fun (_, brec, _) => #[Name.mkStr brec "go", Name.mkStr brec "eq"]).filter
    fun x => (const? x).isSome
  return (iv.all, heads ++ helpers)

/-- The block of a `brecOn` constant: its `below`/`brecOn` constants by
motive position, the number of parameters and motives, each position's
motive arity. The inductive must be recursive, and every `below`/`brecOn`
name the layout relies on must be in the authenticated `family`. -/
def blockOf (const? : Name → Option ConstantInfo) (family : Std.HashSet Name) (brecOn : Name) :
    Except String (Std.HashMap Name BlockAux × Nat × Nat × Array Nat) := do
  let some (.inductInfo iv) := const? (brecOnOwner brecOn)
    | throw s!"{brecOn}: not the brecOn of an inductive"
  unless iv.isRec do
    throw s!"{brecOn}: the inductive is not recursive (Lean generates no below/brecOn family)"
  let some names := blockNames iv
    | throw s!"{brecOn}: a block with nested auxiliaries and no type former"
  let mut aux : Std.HashMap Name BlockAux := {}
  let mut arities := #[]
  for ((below, brec, recN), j) in names.zipIdx do
    for x in [below, brec] do
      unless family.contains x do throw s!"{x}: not in the block's authenticated below/brecOn family"
    aux := aux.insert below { pos := j, isBrecOn := false }
    aux := aux.insert brec { pos := j, isBrecOn := true }
    let some (.recInfo r) := const? recN | throw s!"{recN}: no recursor"
    arities := arities.push (r.numIndices + 1)
  return (aux, iv.numParams, names.size, arities)

/-! ## The members -/

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

/-- Map the loose variables `bvar k`, `k < map.size`, of `e` to
`bvar (map[k])` (over distinct subterms, `Dag.lean`). -/
def remapLoose (map : Array Nat) (e : Expr) : Expr :=
  if map.isEmpty then e else (go e 0).run' {}
where
  go : Expr → Nat → DagM Expr
    | .bvar i _, d =>
      pure (if h : d ≤ i ∧ i - d < map.size then Expr.mkBVar (d + map[i - d]) else Expr.mkBVar i)
    | e@(.app f a _), d => memoAt e d d fun _ => do
      let f' ← go f d
      let a' ← go a d
      pure (Expr.mkApp f' a')
    | e@(.lam nm t b bi _), d => memoAt e d d fun _ => do
      let t' ← go t d
      let b' ← go b (d + 1)
      pure (Expr.mkLam nm t' b' bi)
    | e@(.forallE nm t b bi _), d => memoAt e d d fun _ => do
      let t' ← go t d
      let b' ← go b (d + 1)
      pure (Expr.mkForallE nm t' b' bi)
    | e@(.letE nm t v b nd _), d => memoAt e d d fun _ => do
      let t' ← go t d
      let v' ← go v d
      let b' ← go b (d + 1)
      pure (Expr.mkLetE nm t' v' b' nd)
    | e@(.proj s i x _), d => memoAt e d d fun _ => do
      let x' ← go x d
      pure (Expr.mkProj s i x')
    | e@(.mdata m x _), d => memoAt e d d fun _ => do
      let x' ← go x d
      pure (Expr.mkMData m x')
    | e, _ => pure e

/-- Reorder a telescope of independent `let`s (`perm[p]` = old let at new
position `p`) and re-index the body; the values must not mention earlier
lets (Lean's `funType_i`, `IndPred.lean`'s `withFunTypes`). -/
def reorderLets (perm : Array Nat) (ls : Array (Name × Expr × Expr)) (body : Expr) :
    Except String (Array (Name × Expr × Expr) × Expr) := do
  let n := ls.size
  let mut closed := #[]
  for ((nm, t, v), i) in ls.zipIdx do
    let some t' := lower? t i | throw "a let type mentions an earlier let"
    let some v' := lower? v i | throw "a let value mentions an earlier let"
    closed := closed.push (nm, t', v')
  let some inv := invPerm perm | throw "reorderLets: the order is not a permutation"
  let some ls' := (List.range n).toArray.mapM fun p => do
      let (nm, t, v) ← closed[← perm[p]?]?
      pure (nm, liftLoose t p, liftLoose v p)
    | throw "reorderLets: the order does not index the lets"
  -- old let `i` is `bvar (n-1-i)`; it becomes `bvar (n-1-inv[i])`
  let some map := (List.range n).toArray.mapM fun k => do
      let j ← inv[n - 1 - k]?
      pure (n - 1 - j)
    | throw "reorderLets: the order does not index the lets"
  return (ls', remapLoose map body)

def mkLets (ls : Array (Name × Expr × Expr)) (body : Expr) : Expr :=
  ls.foldr (init := body) fun (nm, t, v) acc => Expr.mkLetE nm t v acc false

/-- The structural layout of a clique from its members (Lean's order), the
other constants of its encoding (`aux`: the functionals, the below
matchers), `σ`, the input, and the authenticated `below`/`brecOn` family of
its block (`familyCandidates`). -/
def structLayout (members : Array Decl) (aux : Array Decl) (σ : Array Nat)
    (const? : Name → Option ConstantInfo) (family : Std.HashSet Name) :
    Except String StructLayout := do
  let n := members.size
  unless n ≥ 2 && σ.size == n && isPerm σ do throw "structLayout: bad permutation"
  let shapes ← members.mapM memberShape
  let some sh0 := shapes[0]? | throw "structLayout: bad permutation"
  let (blockAux, P, K, arities) ← blockOf const? family sh0.brecOnName
  let poss ← shapes.mapM fun s => match blockAux.get? s.brecOnName with
    | some a => if a.isBrecOn then pure a.pos else throw "structLayout: not a brecOn"
    | none => throw "structLayout: members over different blocks"
  -- the below matchers: the name is a pre-filter, the declaration decides
  let numFunTypes := sh0.lets
  let matchers := aux.foldl (init := ({} : Std.HashMap Name MatcherShape)) fun acc d =>
    if !isMatcherName d.name then acc else
    match matcherShape? const? acc.contains numFunTypes d with
    | some s => acc.insert d.name s
    | none => acc
  -- groups
  let groups ← (List.range K).toArray.mapM fun j => do
    let some arity := arities[j]? | throw "structLayout: missing motive"
    let g : Group := { members := (List.range n).toArray.filter (poss[·]? == some j), arity }
    if g.size ≥ 2 then
      let some motive := sh0.brecArgs[P + j]? | throw "structLayout: missing motive"
      let (_, body) := peelLams g.arity motive #[]
      let some s := decodeSpine .pprod g.size body | throw "structLayout: a packed motive that is not Lean's"
      let some ranks := g.members.mapM (σ[·]?) | throw "structLayout: bad permutation"
      let perm := ranks.map fun r => (ranks.filter (· < r)).size
      pure { g with spine := s, perm }
    else pure { g with perm := idPerm g.size }
  -- each member projects its own position
  for (sh, i) in shapes.zipIdx do
    let some g := poss[i]? >>= (groups[·]?)
      | throw s!"structLayout: member {i} does not project its clique position"
    if g.size ≥ 2 then
      let some a := g.members.idxOf? i
        | throw s!"structLayout: member {i} does not project its clique position"
      match pathPrefix g.size sh.steps with
      | some (idx, len) =>
        unless idx == a && len == sh.steps.size && stepsFit g.spine idx sh.steps do
          throw s!"structLayout: member {i} does not project its clique position"
      | none => throw s!"structLayout: member {i} does not project its clique position"
  -- the functionals and the fixed parameters
  let mut fNames : Std.HashSet Name := {}
  let mut fDepth : Std.HashMap Name (Nat × Nat) := {}
  let mut qss : Array (Array Nat) := #[]
  for (sh, i) in shapes.zipIdx do
    let some arity := poss[i]? >>= (arities[·]?) | throw "structLayout: missing functional"
    let fStart := P + K + arity
    let mut q? : Option (Array Nat) := none
    for (g, j) in groups.zipIdx do
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
        fDepth := fDepth.insert h (depth, g.arity)
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
        -- A fixed slot is identified by its source binder, not by its type.
        -- Repeated arguments do not establish an invertible telescope map.
        unless q.toList.eraseDups.length == q.size do
          throw "structLayout: distinct fixed parameters alias the same binder"
        match q? with
        | none => q? := some q
        | some q' => unless q == q' do throw "structLayout: inconsistent fixed arguments"
    -- a member none of whose functionals is a constant (the inductive-
    -- predicate route, whose functionals are inline) has no fixed parameter
    qss := qss.push (match q? with
      | some q => q
      | none => #[])
  let some q0 := qss[0]? | throw "structLayout: inconsistent fixed parameters"
  let m := q0.size
  unless qss.all (·.size == m) do throw "structLayout: inconsistent fixed parameters"
  unless q0 == q0.qsort (· < ·) do
    throw "structLayout: the fixed parameters are not in the first member's order"
  let some funPerm := invPerm σ | throw "structLayout: bad permutation"
  let some qg := funPerm[0]? >>= (qss[·]?) | throw "structLayout: inconsistent fixed parameters"
  let fixedPerm := sortIdxByKey qg
  unless shapes.all (·.lets == numFunTypes) do throw "structLayout: inconsistent funType lets"
  unless numFunTypes == 0 || numFunTypes == n do throw "structLayout: unexpected lets"
  return { n, sigma := σ, const?, numParams := P, numMotives := K, aux := blockAux, family,
           groups, fNames, numFixed := m, fixedPerm, matchers, numFunTypes, funPerm,
           memberFixed := qss, fDepth }

/-! ## The transport -/

/-- Transport a structural clique: the functionals (`_f`), the below
matchers, the members, and the carried equation lemmas (`lemmas`, each with
its output name). `family` is the block's authenticated `below`/`brecOn`
family (`familyCandidates`). Fails (and the caller keeps the baseline) on
anything outside the grammar, including a `below` dictionary or `brecOn`
application the recursion does not own (see "Ownership"). -/
def transportStructural (members : Array Decl) (aux : Array Decl) (σ : Array Nat)
    (const? : Name → Option ConstantInfo) (family : Std.HashSet Name)
    (lemmas : Array (Decl × Name) := #[]) (forceOwnership : Bool := false) :
    TM (Array Transported) := do
  let L ← liftE (structLayout members aux σ const? family)
  let L := { L with checkOwnership := forceOwnership || !members.all (·.isThm) }
  -- `brecOn` of the block: at the members' roots only
  if L.checkOwnership then
    let mentionsBrecOn := mentionsWhere L.isBrecOnConst
    for d in aux do
      if mentionsBrecOn d.type || mentionsBrecOn d.value then
        throw s!"grammar: a brecOn application of the block outside a member's root (in {d.name})"
    for d in members do
      unless !mentionsBrecOn d.type && L.brecOnCount d.value == 1 do
        throw s!"grammar: a brecOn application of the block outside a member's root (in {d.name})"
  let phi (e : Expr) : TM Expr := phiSC L {} e
  -- a functional's body after its fixed parameters: the indices, the major
  -- and (at depth arity + 1) the recursion's own dictionary
  let phiF (depth arity : Nat) (e : Expr) : TM Expr := do
    let (bs, body) := peelLams depth e #[]
    let mut ctx : SCtx := {}
    let mut bs' := #[]
    for ((nm, t, bi), i) in bs.zipIdx do
      let dict := depth == arity + 1 && i == arity
      bs' := bs'.push (nm, ← (if dict then phiSDictType L (phiSC L) ctx t else phiSC L ctx t), bi)
      ctx := ctx.push t dict
    return mkLams bs' (← phiSC L ctx body)
  -- the same telescope in the functional's type
  let phiFTy (depth arity : Nat) (e : Expr) : TM Expr := do
    let (bs, body) := peelForalls depth e #[]
    let mut ctx : SCtx := {}
    let mut bs' := #[]
    for ((nm, t, bi), i) in bs.zipIdx do
      let dict := depth == arity + 1 && i == arity
      bs' := bs'.push (nm, ← (if dict then phiSDictType L (phiSC L) ctx t else phiSC L ctx t), bi)
      ctx := ctx.push t false
    return mkForalls bs' (← phiSC L ctx body)
  let mut out : Array Transported := #[]
  for d in aux do
    if L.fNames.contains d.name then
      let m := L.numFixed
      -- the dictionary is the binder after the group's indices and major, in
      -- the functional's own telescope (a member may pass it eta-reduced)
      let some (_, arity) := L.fDepth.get? d.name
        | throw s!"structLayout: the functional {d.name} has no recorded telescope"
      let depth := arity + 1
      let type ← withReorderedBinders2 false m L.fixedPerm d.type phi (phiFTy depth arity)
      let value ← withReorderedBinders2 true m L.fixedPerm d.value phi (phiF depth arity)
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
    let mut ctx : SCtx := {}
    let mut ps' := #[]
    for (nm, t, bi) in ps do
      if L.checkOwnership && L.isBelowTy t then
        throw "grammar: a member parameter of a below type"
      ps' := ps'.push (nm, ← phiSC L ctx t, bi)
      ctx := ctx.push t false
    let (ls, b2) := peelLets L.numFunTypes b1 #[]
    let (ls, b2) ← liftE (reorderLets L.funPerm ls b2)
    let mut ls' := #[]
    for (nm, t, v) in ls do
      ls' := ls'.push (nm, ← phiSC L ctx t, ← phiSC L ctx v)
      ctx := ctx.push t false
    let body ← phiSC L ctx b2
    out := out.push { decl := { d with type := ← phi d.type, value := mkLams ps' (mkLets ls' body) } }
  if lemmas.isEmpty then return out
  -- Regeneration sees exactly the transported members/functionals, before
  -- the encoding constants get canonical names. Source declarations retain
  -- all metadata; the override changes only the produced type/value.
  let targets := out.map (·.decl)
  let targetConst? (n : Name) : Option ConstantInfo := do
    let ci ← const? n
    match targets.find? (fun d => eqDefNameEq d.name n), ci with
    | some d, .defnInfo v => return .defnInfo { v with cnst := { v.cnst with type := d.type }, value := d.value }
    | some d, .thmInfo v => return .thmInfo { v with cnst := { v.cnst with type := d.type }, value := d.value }
    | _, _ => return ci
  let Lp := { L with checkOwnership := false }
  for (d, nn) in lemmas do
    if L.repacks && (mentionsWhere L.isEncodingConst d.type || mentionsWhere L.isEncodingConst d.value) then
      -- Keep the original refusal, including its text, unless every branch
      -- of the replacement proof was constructed and checked by conversion.
      let regenerated ← try
        let some member := members.find? (fun m => eqDefNameEq d.name (Name.mkStr m.name "eq_def"))
          | throw "structural eq_def: not a member unfolding theorem"
        let sh ← liftE (memberShape member)
        let some a := L.aux.get? sh.brecOnName | throw "structural eq_def: no block layout"
        let g ← TM.idx L.groups a.pos "structural eq_def: the member's group"
        let some major := sh.brecArgs[L.numParams + L.numMotives + g.arity - 1]?
          | throw "structural eq_def: no recursive argument"
        let .bvar i _ := stripMdata major | throw "structural eq_def: recursive argument is not a binder"
        unless sh.lets ≤ i && i - sh.lets < sh.lams do
          throw "structural eq_def: recursive binder lies outside the member telescope"
        regenerateStructuralEq targetConst? member d nn (sh.lams - 1 - (i - sh.lets))
      catch _ =>
        throw s!"grammar: the carried equation lemma {d.name} unfolds a member through the encoding \
          of a repacked group (brecOn.go/brecOn.eq and packed values the transport does not re-associate)"
      out := out.push { decl := regenerated }
    else
      out := out.push { decl := { d with name := nn, type := ← phiSC Lp {} d.type,
                                             value := ← phiSC Lp {} d.value } }
  return out

end Ix.Compile.Pass.Clique

end
