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
public import Ix.Compile.Clique.Telescope
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata peelForalls)
open Ix.Compile.Image (Local forallArity)

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
  deriving Inhabited

def WFLayout.isClique (L : WFLayout) (s : Spine) : Bool :=
  s.size == L.n && (s.leaves.zip L.leaves).all fun (a, b) => eqModVars a b

/-- A packing type that is a proper suffix of the clique's (`m` summands,
`2 ≤ m < n`): it may occur only inside a recognised construct. -/
def WFLayout.isFragment (L : WFLayout) (ty : Expr) : Bool :=
  (List.range L.n).any fun m =>
    m ≥ 2 && m < L.n &&
      match decodeSpine .psum m ty with
      | some s => (s.leaves.zip (L.leaves.extract (L.n - m) L.n)).all fun (a, b) => eqModVars a b
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
  | .proj _ _ r _ =>
    args.size ≥ 2 &&
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
        let args' ← args.mapM goM
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
           fixedPerm, leaves := s.leaves }

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

/-- Transport a well-founded clique. `members` in Lean's clique order,
`proofs` the abstracted `f₀._mutual._proof_k` (none for theorems). Fails
(and the caller keeps the baseline) when the packed function, a statement or
a member is outside the grammar; a proof body outside the grammar is kept
verbatim under its transported statement. -/
def transportWF (members : Array Decl) (mutDecl : Decl) (proofs : Array Decl) (σ : Array Nat)
    (newMutualName : Name) : TM WFOutput := do
  let L ← liftE (wfLayout members mutDecl σ newMutualName)
  let m := L.numFixed
  -- the proofs' fixed-parameter prefixes, from their uses in the packed function
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun s p => s.insert p.name
  let (xs, body) ← openBinders true m mutDecl.value
  let uses := scanProofs proofNames (xs.map (·.fvar)) body {}
  let inv := invPerm L.fixedPerm
  let proofPerm : Std.HashMap Name (Array Nat) := uses.fold (init := {}) fun acc c js =>
    acc.insert c ((idPerm js.size).qsort fun a b => inv[js[a]!]! < inv[js[b]!]!)
  let L := { L with proofPerm }
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
  let rn : Std.HashMap Name Name := numbered.foldl (init := {}) fun m (a, b) => m.insert a b
  let ren (t : Transported) : Transported :=
    { t with decl := { t.decl with name := (rn.get? t.decl.name).getD t.decl.name
                                   type := renameConsts rn.get? t.decl.type
                                   value := renameConsts rn.get? t.decl.value } }
  let all := ((#[({ decl := mutDecl' } : Transported)] ++ proofs') ++ members').map ren
  return { decls := all, renames := #[(mutDecl.name, newMutualName)] ++ numbered }

end Ix.Compile.Clique

end
