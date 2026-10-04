/-
  Ix.Compile.Clique.WF: transport of a well-founded clique (design document
  §5.1), the steps (R), (A) and (S).

  Lean's encoding (`Elab/PreDefinition/WF`, Lean 4.34.1), as the transport
  sees it:

  * `f₀._mutual : ∀ fixed, (x : α) → C x` with `α = PSum D₀ (… D_{n-1})` in
    Lean's clique order and `C` a `mkCodomain` case tree; the fixed
    parameters in the first function's order;
  * its value `λ fixed. WellFounded.fix α (λ x. C x) rel wf F` or
    `λ fixed. WellFounded.Nat.fix α (λ x. C x) measure F`, where `rel`
    (`(invImage m inst).1`) and `measure` carry the per-function measures in a
    case tree over `α`, and `F = λ x a. tree` is `processSumCasesOn`'s
    refinement tree whose leaves are the functions' bodies, recursive calls
    `a (inj_j ⟨args⟩) h`;
  * the decreasing proofs `f₀._mutual._proof_k : ∀ ctx, rel (inj_j y) (inj_i x)`
    (definitions; for theorems they stay inline), whose bodies mention the
    packing in copies of their goal (`id`, motives);
  * the members `f_i := λ ps. f₀._mutual fixed (inj_i ⟨varying⟩)`.

  `Φ_σ` is the homomorphism on terms that, at every occurrence of the
  clique's packing in a position Lean's construction generates (§ Positions
  below; recognised by its summands: the decoded `PSum` leaves must be
  `α`'s, up to variables), rebuilds the construct in canonical order with
  Lean's own construction (`Packing.lean`): packing types, injections, case
  trees (motives regenerated, leaves moved: `inj_i ↦ inj'_{σ i}`, leaf `i` at
  position `σ i`). Applications of `f₀._mutual` and of the proofs get their
  fixed-parameter arguments permuted; their telescopes are reordered
  (`Telescope.lean`). Everything else — user bodies, measures (D22), the
  `PSigma` packing of each function's arguments, external constants — is
  untouched. A proof's statement is transported with the rest (S); the
  proofs are renumbered in the canonical traversal (their numbering is
  metadata, §5.5).

  In the encoding region, an occurrence of a proper suffix of the packing
  outside a recognised construct (a partial injection, a fragment of the
  case tree) is outside the grammar: `Φ` fails, and the caller falls back.
  In the user region, packing-shaped terms are the user's and stay.
-/
module
public import Ix.Compile.Clique.Packing
public import Ix.Compile.Clique.PackingMatch
public import Ix.Compile.Clique.Telescope
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata peelForalls)
open Ix.Compile.Image (Local forallArity instLocals abstractFVars)

/-- What `Φ_σ` needs to know about a well-founded clique. -/
structure WFLayout where
  n : Nat
  /-- Lean index ↦ canonical position -/
  sigma : Array Nat
  mutualName : Name
  newMutualName : Name
  numFixed : Nat
  /-- new fixed position `p` ↦ Lean's fixed position -/
  fixedPerm : Array Nat
  /-- Lean's summands `D_i`, from `f₀._mutual`'s type (the fixed parameters as
  loose variables) -/
  leaves : Array Expr
  /-- abstracted proof ↦ the permutation of its leading fixed-parameter
  binders (empty when it uses none) -/
  proofPerm : Std.HashMap Name (Array Nat) := {}
  /-- the packed function's equation lemmas carried with the clique: in the
  user region, an application of one re-enters the encoding region at its
  packed argument, as an application of the packed function does -/
  packedLemmas : Std.HashSet Name := {}
  /-- per member (Lean's order): the member's parameter (outermost `0`) at
  each fixed position of its call of the packed function -/
  memberFixed : Array (Array Nat) := #[]
  deriving Inhabited

def WFLayout.isClique (L : WFLayout) (s : Spine) : Bool :=
  s.size == L.n && (matchPackingLeaves s.leaves L.leaves).isSome

/-- A packing type that is a proper suffix of the clique's (`m` summands,
`2 ≤ m < n`): it may occur only inside a recognised construct. -/
def WFLayout.isFragment (L : WFLayout) (ty : Expr) : Bool :=
  (List.range L.n).any fun m =>
    m ≥ 2 && m < L.n &&
      match decodeSpine .psum m ty with
      | some s => (matchPackingLeaves s.leaves (L.leaves.extract (L.n - m) L.n)).isSome
      | none => false

/-- The packing type named by the type arguments of an injection or a case
tree. -/
def psumOfArgs (us : Array Level) (a b : Expr) : Expr :=
  mkAppN (Expr.mkConst nPSum us) #[a, b]

/-- The recognised constructs. -/
inductive WFConstruct where
  | spine (s : Spine)
  | inj (s : Spine) (i : Nat) (v : Expr)
  | tree (t : Tree)
  /-- a construct over the clique's packing (or a fragment of it) that is
  not one of Lean's: outside the grammar -/
  | stray (what : String)
  | none

def WFLayout.recognise (L : WFLayout) (e : Expr) : WFConstruct :=
  match constApp? e with
  | some (c, us, args) =>
    if c == nPSum && args.size == 2 then
      match decodeSpine .psum L.n e with
      | some s => if L.isClique s then .spine s
          else if L.isFragment e then .stray "a fragment of the packing type" else .none
      | none => if L.isFragment e then .stray "a fragment of the packing type" else .none
    else if (c == nPSumInl || c == nPSumInr) && us.size == 2 && args.size ≥ 2 then
      let ty := psumOfArgs us args[0]! args[1]!
      let full := match decodeSpine .psum L.n ty with
        | some s => L.isClique s
        | none => false
      if full then
        match decodeInj L.n e with
        | some (s, i, v) => .inj s i v
        | none => .stray "an injection that is not Lean's"
      else if L.isFragment ty then .stray "an injection into a fragment of the packing"
      else .none
    else if c == nPSumCasesOn && us.size == 3 && args.size ≥ 2 then
      let ty := psumOfArgs #[us[1]!, us[2]!] args[0]! args[1]!
      let full := match decodeSpine .psum L.n ty with
        | some s => L.isClique s
        | none => false
      if full then
        match decodeTree L.n e with
        | some t => .tree t
        | none => .stray "a case tree that is not Lean's"
      else if L.isFragment ty then .stray "a case split on a fragment of the packing"
      else .none
    else .none
  | none => .none

/-! ## Positions

The packing type `α` can also be the type of a user's own value (`PSum Nat
Nat` in a clique of two functions on `Nat`, family `WU`): such a value is
not the encoding's and must not move. So the definitions of the encoding are
transported by position. Lean's construction generates the packing in these
places only, and they are the *encoding region*:

* the packed function's type after its fixed parameters, `(x : α) → C x`,
  and its value after them, the fixpoint `WellFounded.fix α C rel wf F` or
  `WellFounded.Nat.fix α C m F` with everything inside it, except
* the *user region* inside the encoding: the summands `D_i` of every packing
  type, the payloads of injections, and the leaves of every case tree (the
  functions' bodies, codomains and measures, D22);
* in the user region, Lean's construction re-enters the encoding at four
  kinds of position, transported as encoding again: an application of the
  packed function (its packed argument), an application of the recursion
  variable `a : (y : α) → rel y x → C y` (its argument and the decreasing
  proof: the recursive call), the type of a binder that is a copy of the
  recursion variable (threaded through matchers by `MatcherApp.addArg`),
  and an application of the relation (`InvImage r m y x`,
  `(invImage m inst).1 y x`, `WellFoundedRelation.rel R y x`).

The members are user region (their bodies apply the packed function). The
decreasing proofs are transported as encoding throughout: they are proofs
of the transported obligation, whatever user value they mention (proof
irrelevance), and their copies of the obligation occur wherever a tactic put
them, at no syntactic position. -/

def nInvImage : Name := leanName ``InvImage
def nWFRelRel : Name := leanName ``WellFoundedRelation.rel
def nWFRelation : Name := leanName ``WellFoundedRelation

def WFLayout.isSpine (L : WFLayout) (e : Expr) : Bool :=
  match decodeSpine .psum L.n (stripMdata e) with
  | some s => L.isClique s
  | none => false

/-- An application of the relation over the clique's packing. -/
def WFLayout.isRelApp (L : WFLayout) (e : Expr) : Bool :=
  let (h, args) := getAppFnArgs (stripMdata e)
  match stripMdata h with
  | .const c _ _ =>
    (c == nInvImage || c == nWFRelRel) && args.size ≥ 2 &&
      match args[0]? with
      | some a => L.isSpine a
      | none => false
  | .proj structureName field r _ =>
    -- A user record can have the same first type argument and a binary
    -- function field. Re-entering the encoding there would permute its user
    -- inputs, possibly changing a Nat result while preserving its type.
    -- Only the actual relation field is a candidate for this encoding form.
    structureName == nWFRelation && field == 0 && args.size ≥ 2 &&
      match constApp? r with
      | some (_, _, rargs) => match rargs[0]? with
        | some a => L.isSpine a
        | none => false
      | none => false
  | _ => false

/-- The type of the recursion variable or of one of its copies:
`(y : α) → rel y x → C y`. -/
def WFLayout.isRecVarType (L : WFLayout) (t : Expr) : Bool :=
  match stripMdata t with
  | .forallE _ dom b _ _ =>
    L.isSpine dom && match stripMdata b with
      | .forallE _ r _ _ _ => L.isRelApp r
      | _ => false
  | _ => false

/-- One step of `Φ_σ` on a well-founded clique's term, in the encoding
region (`enc`) or the user region, under binders of which `ctx` marks the
recursion variables; `go enc ctx` is `Φ_σ` on subterms. -/
def phiWFStep (L : WFLayout) (go : Bool → Array Bool → Expr → TM Expr) (enc : Bool)
    (ctx : Array Bool) (e : Expr) : TM Expr := do
  let goE := go true ctx
  let goU := go false ctx
  let goM := go enc ctx
  if enc then
    match L.recognise e with
    | .spine s =>
      let leaves ← s.leaves.mapM goU
      return ({ s with leaves }.permute L.sigma).type
    | .inj s i v =>
      let leaves ← s.leaves.mapM goU
      return mkInj ({ s with leaves }.permute L.sigma) L.sigma[i]! (← goU v)
    | .tree t =>
      let spineLeaves ← t.spine.leaves.mapM goU
      let t' : Tree := { t with
        spine := { t.spine with leaves := spineLeaves }
        motiveBody := ← go true (ctx.push false) t.motiveBody
        major := ← goE t.major
        leaves := ← t.leaves.mapM goU
        extras := ← t.extras.mapM goE }
      match (t'.permute L.sigma).build with
      | some r => return r
      | none => throw "Φ: rebuilding a case tree failed"
    | .stray what => throw s!"grammar: {what}"
    | .none => pure ()
  else if L.isRelApp e then
    -- the relation: encoding again
    return ← goE e
  let binderTy (t : Expr) : TM Expr :=
    if !enc && L.isRecVarType t then goE t else goM t
  match e with
  | .app .. =>
    let (h, args) := getAppFnArgs e
    match h with
    | .const c us _ =>
      if c == L.mutualName then
        if args.size < L.numFixed + 1 then
          throw "grammar: a partial application of the packed function"
        let mut args' := #[]
        for j in [0:args.size] do
          args' := args'.push (← if j == L.numFixed then goE args[j]! else goM args[j]!)
        let fixed := L.fixedPerm.map fun j => args'[j]!
        return mkAppN (Expr.mkConst L.newMutualName us) (fixed ++ args'.extract L.numFixed args'.size)
      if let some ρ := L.proofPerm.get? c then
        if args.size < ρ.size then
          throw "grammar: a partial application of a decreasing proof"
        let reenter := !enc && L.packedLemmas.contains c
        let mut args' := #[]
        for j in [0:args.size] do
          args' := args'.push (← if reenter && j == L.numFixed then goE args[j]! else goM args[j]!)
        return mkAppN h (ρ.map (args'[·]!) ++ args'.extract ρ.size args'.size)
      return mkAppN h (← args.mapM goM)
    | .bvar i _ =>
      let isRec := !enc && i < ctx.size && ctx[ctx.size - 1 - i]!
      if isRec then
        -- a recursive call: the packed argument and the decreasing proof
        let mut args' := #[]
        for j in [0:args.size] do
          args' := args'.push (← if j < 2 then goE args[j]! else goU args[j]!)
        return mkAppN h args'
      return mkAppN h (← args.mapM goM)
    | _ => return mkAppN (← goM h) (← args.mapM goM)
  | .const c us _ =>
    if c == L.mutualName then
      if L.numFixed == 0 then return Expr.mkConst L.newMutualName us
      throw "grammar: a bare occurrence of the packed function"
    if let some ρ := L.proofPerm.get? c then
      unless ρ.isEmpty do throw "grammar: a bare occurrence of a decreasing proof"
    return e
  | .lam nm t b bi _ =>
    return Expr.mkLam nm (← binderTy t) (← go enc (ctx.push (L.isRecVarType t)) b) bi
  | .forallE nm t b bi _ =>
    return Expr.mkForallE nm (← binderTy t) (← go enc (ctx.push (L.isRecVarType t)) b) bi
  | .letE nm t v b nd _ =>
    return Expr.mkLetE nm (← binderTy t) (← goM v) (← go enc (ctx.push (L.isRecVarType t)) b) nd
  | .proj s i x _ => return Expr.mkProj s i (← goM x)
  | .mdata d x _ => return Expr.mkMData d (← goM x)
  | _ => return e

/-- `Φ_σ` memoised by the term, the region and the recursion variables in
scope, under a recursion bound. -/
def phiWFFix (L : WFLayout) : Nat → Bool → Array Bool → Expr → TM Expr
  | 0, _, _, _ => throw "Φ: recursion bound exhausted"
  | fuel + 1, enc, ctx, e => do
    let key := mixHash (mixHash (hash e) (hash enc)) (hash ctx)
    if let some (e', enc', ctx', r) := (← get).cacheMode.get? key then
      if e' == e && enc' == enc && ctx' == ctx then return r
    let r ← phiWFStep L (phiWFFix L fuel) enc ctx e
    modify fun st => { st with cacheMode := st.cacheMode.insert key (e, enc, ctx, r) }
    return r

/-- `Φ_σ` on a term of a well-founded clique, in the encoding region
(`enc := true`) or the user region. -/
def phiWF (L : WFLayout) (enc : Bool) : Expr → TM Expr := phiWFFix L defaultFuel enc #[]

/-- Memoise a step function by the term's hash, under a recursion bound. -/
def memoFix (step : (Expr → TM Expr) → Expr → TM Expr) : Nat → Expr → TM Expr
  | 0, _ => throw "Φ: recursion bound exhausted"
  | fuel + 1, e => do
    if let some r := (← get).cache.get? e then return r
    let r ← step (memoFix step fuel) e
    modify fun st => { st with cache := st.cache.insert e r }
    return r

/-! ## The layout -/

/-- The fixed-parameter positions of a member's call of `f₀._mutual`: for
each fixed argument, the member's parameter it is (outermost `0`). -/
def memberFixedArgs (mutualName : Name) (m : Nat) (member : Decl) :
    Except String (Array Nat × Expr) := do
  let (ps, body) := peelLams (lamArity member.value) member.value #[]
  let some (h, _, args) := constApp? body
    | throw s!"member {member.name}: not an application of the packed function"
  unless h == mutualName && args.size == m + 1 do
    throw s!"member {member.name}: not an application of the packed function"
  let mut qs := #[]
  for j in [0:m] do
    match stripMdata args[j]! with
    | .bvar b _ =>
      if b < ps.size then qs := qs.push (ps.size - 1 - b)
      else throw s!"member {member.name}: fixed argument out of scope"
    | _ => throw s!"member {member.name}: a fixed argument is not a parameter"
  return (qs, args[m]!)

def wfLayout (members : Array Decl) (mutDecl : Decl) (σ : Array Nat) (newMutualName : Name) :
    Except String WFLayout := do
  let n := members.size
  unless n ≥ 2 && σ.size == n && isPerm σ do throw "wfLayout: bad permutation"
  let ar := forallArity mutDecl.type
  unless ar ≥ 1 do throw "wfLayout: the packed function has no argument"
  let m := ar - 1
  let (bs, _) := peelForalls ar mutDecl.type #[]
  let some (_, α, _) := bs[m]? | throw "wfLayout: no packed argument"
  let some s := decodeSpine .psum n α | throw "wfLayout: the packed domain is not Lean's PSum packing"
  let mut qss : Array (Array Nat) := #[]
  for i in [0:n] do
    let (qs, arg) ← memberFixedArgs mutDecl.name m members[i]!
    match decodeInj n arg with
    | some (_, j, _) =>
      unless j == i do throw s!"wfLayout: member {i} injects at summand {j} (not Lean's order)"
    | none => throw s!"wfLayout: member {i}'s argument is not an injection"
    qss := qss.push qs
  -- Lean's fixed order is its first member's order
  unless qss[0]! == (qss[0]!.qsort (· < ·)) do
    throw "wfLayout: the fixed parameters are not in the first member's order"
  -- the canonical first member's order
  let g := (invPerm σ)[0]!
  let qg := qss[g]!
  let fixedPerm := (idPerm m).qsort fun a b => qg[a]! < qg[b]!
  return { n, sigma := σ, mutualName := mutDecl.name, newMutualName, numFixed := m,
           fixedPerm, leaves := s.leaves, memberFixed := qss }

/-- For every application of an abstracted proof in the (opened) value of
`f₀._mutual`: the fixed parameters (by Lean position) among its leading
arguments. An application node is visited before its function part, so the
full argument list is the one recorded. -/
def scanProofs (proofs : Std.HashSet Name) (fixed : Array Name) :
    Expr → Std.HashMap Name (Array Nat) → Std.HashMap Name (Array Nat)
  | e@(.app f a _), acc =>
    let (h, args) := getAppFnArgs e
    let fixedIdx (x : Expr) : Option Nat := match stripMdata x with
      | .fvar y _ => fixed.idxOf? y
      | _ => none
    let acc := match h with
      | .const c _ _ =>
        if proofs.contains c && !acc.contains c then
          acc.insert c (args.toList.map fixedIdx |>.takeWhile Option.isSome
            |>.filterMap id).toArray
        else acc
      | _ => acc
    scanProofs proofs fixed a (scanProofs proofs fixed f acc)
  | .lam _ t b _ _, acc | .forallE _ t b _ _, acc =>
    scanProofs proofs fixed b (scanProofs proofs fixed t acc)
  | .letE _ t v b _ _, acc =>
    scanProofs proofs fixed b (scanProofs proofs fixed v (scanProofs proofs fixed t acc))
  | .proj _ _ x _, acc | .mdata _ x _, acc => scanProofs proofs fixed x acc
  | _, acc => acc

/-! ## The transport -/

/-- One constant's outcome. -/
structure Transported where
  decl : Decl
  /-- `none`: transported; `some why`: Lean's term kept (the faithful
  fallback), with the reason -/
  fallback : Option String := none
  deriving Inhabited

structure WFOutput where
  decls : Array Transported
  /-- Lean's constant ↦ its canonical name (the packed function, the
  renumbered proofs) -/
  renames : Array (Name × Name)

/-! ## The packed function's equation lemma (A5 proper)

Lean proves `f₀._mutual.eq_def : ∀ fixed x, f₀._mutual fixed x = T x` (the
case tree `T` of the bodies, recursive calls through `f₀._mutual`) by
`WellFounded.fix_eq` (or `Nat.fix_eq`) followed by a `simp` chain that
pushes the recursion argument through the case tree
(`PSum.casesOn._arg_pusher`, `congrArg PSum.rec`, …). That chain's shape
follows the packing node by node and is not transported. The canonical lemma
keeps the transported statement (S), keeps Lean's `fix_eq` step (Φ), and
replaces the chain by the step it computes, made explicit: a case split on
the packed argument (`PSum.casesOn` over the canonical packing, then
`PSigma.casesOn` over each summand's arguments), each leaf the `fix_eq` step
at the constructor. At a constructor, `f₀._mutual' fixed' (inj'_i ⟨a⃗⟩)` is
`fix … (inj'_i ⟨a⃗⟩)` by δ, and the functional applied to it reduces to the
statement's leaf by β and ι (§5.1's conversion steps), so each leaf proves
its case by conversion. This is regeneration (G) of a proof whose shape
depends on the packing, by a fixed term recipe; no tactic runs. Equation
lemmas are outside the canonicity claim (`LAZY`); the lemma exists so that
the members' own equation lemmas, transported with them, still prove
Lean's statements. -/

/-- `@id T p ↦ p`. -/
def stripId (e : Expr) : Expr :=
  match constApp? e with
  | some (h, _, args) => if h == leanName ``id && args.size == 2 then args[1]! else e
  | none => e

/-- The `fix_eq` step of Lean's packed equation lemma (the first argument of
its `Eq.trans`), opened at `xs` (the fixed parameters in Lean's order, then
the packed argument). -/
def eqDefFixStep (eqDef : Decl) (m : Nat) (xs : Array Expr) : Except String Expr := do
  let (bs, body) := peelLams (m + 1) eqDef.value #[]
  unless bs.size == m + 1 do throw "eq_def: the proof does not bind the fixed parameters and the argument"
  let body := instLocals body xs
  match constApp? (stripId body) with
  | some (h, _, args) =>
    if h == leanName ``Eq.trans && args.size == 6 then return args[4]!
    else throw "eq_def: the proof is not `Eq.trans (fix_eq …) …`"
  | none => throw "eq_def: the proof is not `Eq.trans (fix_eq …) …`"

/-- Split `major : ty` into its `PSigma` components and prove the motive at
`mk ⟨a⃗⟩` by `leaf`: `PSigma.casesOn` with motive `λ t. motive (mk t)` at each
`PSigma` level, `leaf (mk ⟨a⃗⟩)` at the atoms. -/
def splitPSigma (motive : Expr → Expr) (leaf : Expr → Expr) :
    Nat → Expr → (Expr → Expr) → Expr → TM Expr
  | 0, _, _, _ => throw "eq_def: PSigma nesting bound exhausted"
  | fuel + 1, ty, mk, major => do
    match constApp? ty with
    | some (h, us, #[α, β]) =>
      if h == nPSigma && us.size == 2 then
        let a ← freshFVar
        let b ← freshFVar
        let la : Local := { fvar := a, userName := Ix.Name.mkStr Ix.Name.mkAnon "a", type := α, bi := .default }
        let bty := (match stripMdata β with
          | .lam _ _ body _ _ => Ix.Compile.Canon.instantiateRev body #[Expr.mkFVar a]
          | _ => Expr.mkApp β (Expr.mkFVar a))
        let lb : Local := { fvar := b, userName := Ix.Name.mkStr Ix.Name.mkAnon "b", type := bty, bi := .default }
        let pair (t : Expr) : Expr :=
          mkAppN (Expr.mkConst (leanName ``PSigma.mk) us) #[α, β, Expr.mkFVar a, t]
        let inner ← splitPSigma motive leaf fuel bty (fun t => mk (pair t)) (Expr.mkFVar b)
        let t ← freshFVar
        let lt : Local := { fvar := t, userName := Ix.Name.mkStr Ix.Name.mkAnon "t", type := ty, bi := .default }
        let mot := Ix.Compile.Image.mkLambda #[lt] (motive (mk (Expr.mkFVar t)))
        return mkAppN (Expr.mkConst (leanName ``PSigma.casesOn) #[Level.mkZero, us[0]!, us[1]!])
          #[α, β, mot, major, Ix.Compile.Image.mkLambda #[la, lb] inner]
      else return leaf (mk major)
    | _ => return leaf (mk major)

/-- `bvar d` occurs in `e` only as the head of an application (a recursive
call `a y h`), never passed on whole. -/
def onlyCalls : Nat → Nat → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, d, e@(.app ..) =>
    let (h, args) := getAppFnArgs e
    let headOk := match h with
      | .bvar _ _ => true
      | h => onlyCalls fuel d h
    headOk && args.all fun x => (match stripMdata x with
      | .bvar i _ => i != d
      | _ => true) && onlyCalls fuel d x
  | _, d, .bvar i _ => i != d
  | fuel + 1, d, .lam _ t b _ _ | fuel + 1, d, .forallE _ t b _ _ =>
    onlyCalls fuel d t && onlyCalls fuel (d + 1) b
  | fuel + 1, d, .letE _ t v b _ _ =>
    onlyCalls fuel d t && onlyCalls fuel d v && onlyCalls fuel (d + 1) b
  | fuel + 1, d, .proj _ _ x _ | fuel + 1, d, .mdata _ x _ => onlyCalls fuel d x
  | _, _, _ => true

/-- A leaf of the packed function's case tree (`λ v a. E`) whose recursion
variable reaches the bodies only through `PSigma.casesOn` layers (which the
regenerated proof splits) and is used there only as recursive calls: the
functional applied at a constructor then reduces to the statement's leaf by
β and ι. A body that threads the recursion variable through a `match`
(`MatcherApp.addArg`) needs Lean's argument pushing, which is not
regenerated. -/
def leafReduces : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    let (bs, body) := peelLams (lamArity e) e #[]
    if bs.isEmpty then false else
    match constApp? body with
    | some (h, _, args) =>
      if h == leanName ``PSigma.casesOn && args.size == 6 &&
          (match stripMdata args[5]! with
            | .bvar 0 _ => true
            | _ => false) then leafReduces fuel args[4]!
      else onlyCalls defaultFuel 0 body
    | none => onlyCalls defaultFuel 0 body

/-- The canonical packed equation lemma (see above): the transported
statement, and the case split whose leaves are the transported `fix_eq`
step at each constructor. -/
def transportEqDef (L : WFLayout) (phi : Expr → TM Expr) (eqDef : Decl) (newName : Name) : TM Decl := do
  let m := L.numFixed
  let type ← withReorderedBinders false m L.fixedPerm eqDef.type phi
  -- open the canonical statement: the fixed parameters (canonical order), `x`
  let (xs, stmt) ← openBinders false (m + 1) type
  let some x := xs[m]? | throw "eq_def: no packed argument"
  let some s' := decodeSpine .psum L.n x.type | throw "eq_def: the argument is not the canonical packing"
  -- Lean's `fix_eq` step, at the same variables (Lean's fixed order), transported
  let inv := invPerm L.fixedPerm
  let leanXs := ((List.range m).toArray.map fun j => xs[inv[j]!]!.expr).push x.expr
  let step ← phi (← liftE (eqDefFixStep eqDef m leanXs))
  let atX (t : Expr) (e : Expr) : Expr := instLocals (abstractFVars #[x.fvar] e) #[t]
  -- the leaves: `λ v. split v`, each atom `step[x := inj'_i ⟨a⃗⟩]`
  let mut leaves : Array Expr := #[]
  for i in [0:L.n] do
    let some d := s'.leaves[i]? | throw "eq_def: no summand"
    let v ← freshFVar
    let lv : Local := { fvar := v, userName := Ix.Name.mkStr Ix.Name.mkAnon "v", type := d, bi := .default }
    let inj (t : Expr) : Expr := mkInj s' i t
    let body ← splitPSigma (fun t => atX (inj t) stmt) (fun t => atX (inj t) step) 64 d id (Expr.mkFVar v)
    leaves := leaves.push (Ix.Compile.Image.mkLambda #[lv] body)
  -- the case tree over the packed argument, motive `λ x. stmt`
  let t : Tree := { spine := s', w := Level.mkZero, motiveBody := abstractFVars #[x.fvar] stmt,
                    motiveName := x.userName, major := x.expr, leaves, extras := #[],
                    altNames := #[] }
  let some cases := t.build | throw "eq_def: building the case split failed"
  let value ← liftE (closeBinders true xs cases)
  return { eqDef with name := newName, type, value }

/-- Transport a well-founded clique. `members` in Lean's clique order,
`proofs` the abstracted `f₀._mutual._proof_k` (none for theorems). Fails
(and the caller keeps the baseline) when the packed function, a statement or
a member is outside the grammar; a proof body outside the grammar is kept
verbatim under its transported statement. -/
def transportWF (members : Array Decl) (mutDecl : Decl) (proofs : Array Decl) (σ : Array Nat)
    (newMutualName : Name) (lemmas : Array (Decl × Name) := #[]) : TM WFOutput := do
  let L ← liftE (wfLayout members mutDecl σ newMutualName)
  let m := L.numFixed
  -- the proofs' fixed-parameter prefixes, from their uses in the packed function
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun s p => s.insert p.name
  let (xs, body) ← openBinders true m mutDecl.value
  let uses := scanProofs proofNames (xs.map (·.fvar)) body {}
  let inv := invPerm L.fixedPerm
  let proofPerm : Std.HashMap Name (Array Nat) := uses.fold (init := {}) fun acc c js =>
    acc.insert c ((idPerm js.size).qsort fun a b => inv[js[a]!]! < inv[js[b]!]!)
  -- the packed function's equation lemmas carried with the clique: their
  -- fixed-parameter arguments follow the canonical order
  let isPackedLemma (d : Decl) : Bool := match d.name with
    | .str p _ _ => p == mutDecl.name
    | _ => false
  let proofPerm := lemmas.foldl (init := proofPerm) fun acc (d, _) =>
    if isPackedLemma d then acc.insert d.name L.fixedPerm else acc
  let packedLemmas : Std.HashSet Name := lemmas.foldl (init := {}) fun acc (d, _) =>
    if isPackedLemma d then acc.insert d.name else acc
  let L := { L with proofPerm, packedLemmas }
  -- the encoding region (the decreasing proofs) and the user region (§ Positions)
  let phi := phiWF L true
  let phiU := phiWF L false
  -- the packed function: its fixed parameters are user region, the rest encoding
  let value ← withReorderedBinders2 true m L.fixedPerm mutDecl.value phiU phi
  let type ← withReorderedBinders2 false m L.fixedPerm mutDecl.type phiU phi
  let mutDecl' : Decl := { mutDecl with name := newMutualName, type, value }
  -- the proofs: statement re-stated (S); body transported, else verbatim
  let mut proofs' : Array Transported := #[]
  for p in proofs do
    let ρ := (proofPerm.get? p.name).getD #[]
    let type ← withReorderedBinders false ρ.size ρ p.type phi
    let st ← get
    match (withReorderedBinders true ρ.size ρ p.value phi).run st with
    | .ok (value, st') =>
      set st'
      proofs' := proofs'.push { decl := { p with type, value } }
    | .error err =>
      let value ← withReorderedBinders true ρ.size ρ p.value pure
      proofs' := proofs'.push { decl := { p with type, value }, fallback := some err }
  -- the carried equation lemmas: the packed one regenerated, the others
  -- transported (a failure leaves the clique in Lean's form)
  let mut lemmas' : Array Transported := #[]
  for (d, nn) in lemmas do
    if d.name == Ix.Name.mkStr mutDecl.name "eq_def" then
      -- the regenerated proof holds only when each leaf reduces at a constructor
      let (_, fixApp) := peelLams m mutDecl.value #[]
      let (_, fargs) := getAppFnArgs (stripMdata fixApp)
      let some F := fargs.back? | throw "eq_def: no functional in the packed function"
      let (_, tree) := peelLams 2 F #[]
      let some t := decodeTree L.n tree | throw "eq_def: the functional is not Lean's case tree"
      unless t.leaves.all (leafReduces 64) do
        throw "eq_def: a body threads the recursion through a match (Lean's argument pushing is not regenerated)"
      lemmas' := lemmas'.push { decl := ← transportEqDef L phi d nn }
    else
      if isPackedLemma d then
        let type ← withReorderedBinders false m L.fixedPerm d.type phi
        let value ← withReorderedBinders true m L.fixedPerm d.value phi
        lemmas' := lemmas'.push { decl := { d with name := nn, type, value } }
      else
      -- a member's own lemma: its statement is about the members (user
      -- region); its proof reaches the encoding through the packed lemmas
      let type ← phiU d.type
      let value ← phiU d.value
      lemmas' := lemmas'.push { decl := { d with name := nn, type, value } }
  -- the members
  let mut members' : Array Transported := #[]
  for mem in members do
    members' := members'.push { decl := { mem with type := ← phiU mem.type,
                                                     value := ← phiU mem.value } }
  -- renumber the proofs in the canonical traversal
  let order := constOccurrences proofNames.contains value
  let rest := (proofs.map (·.name)).filter fun p => !order.contains p
  let numbered := (order ++ rest).zipIdx.map fun (p, i) =>
    (p, Ix.Name.mkStr newMutualName s!"_proof_{i + 1}")
  let lemmaRenames := lemmas.filterMap fun (d, nn) => if d.name != nn then some (d.name, nn) else none
  let rn : Std.HashMap Name Name := (numbered ++ lemmaRenames).foldl (init := {}) fun m (a, b) => m.insert a b
  let ren (t : Transported) : Transported :=
    { t with decl := { t.decl with name := (rn.get? t.decl.name).getD t.decl.name
                                   type := renameConsts rn.get? t.decl.type
                                   value := renameConsts rn.get? t.decl.value } }
  let all := (((#[({ decl := mutDecl' } : Transported)] ++ proofs') ++ lemmas') ++ members').map ren
  return { decls := all, renames := #[(mutDecl.name, newMutualName)] ++ numbered ++ lemmaRenames }

end Ix.Compile.Clique

end
