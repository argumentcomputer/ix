import IxCC.Src.Relevance.Syntax
import IxCC.Ixon.V3.Tc.Driver

/-! # The relevance annotator (untrusted)

Produces an `Ann` for the runtime-reachable part of a program with the ported checker's context:
each runtime term is walked in step with its kernel reading (`KExpr`, from the same v3 expression,
so the shapes agree node for node), opening binders as free variables. Relevance is
level-exact (D18): a binder, argument or let whose type's sort is zero under
a condition on the constant's universe parameters (`kZeroCond` of the
inferred sort, exact without normalisation) is `proof` under that condition;
otherwise one whose type whnf's to a Π-telescope ending in a sort is `type`;
anything else is `rel`. Each λ gets `propWhen` from the zero condition of
the sort of its body's type. Field classes and constant classes use the same
test. A λ binder, let, constant parameter or argument written `0` (erased)
is irrelevant at every instance whatever its type (`honourErased`),
so a run-time use of it fails the checker's C1 instead of its C0.

The annotator is an oracle of the pipeline: nothing it produces is trusted.
`Src.Relevance.check` decides the result, and a wrong annotation only makes
SrcEval stuck. It starts from the roots and follows references in positions
relevant at some instance, so theorems and types reached only through
always-irrelevant positions are never walked. -/

namespace IxCC.Src.Relevance.Annotate

open IxCC.Ixon IxCC.Ixon.V3.Tc

abbrev M := TcM .anon

def fail (msg : String) : M α := throw (.other msg)

def resetFuel : M Unit := modify fun s => { s with recFuel := s.fuelBudget }

def inferType (e : KExpr .anon) : M (KExpr .anon) := do
  resetFuel
  TcM.withInferOnly (TcM.infer e)

/-- Run `x` and drop the free variables it opened. -/
def withScope (x : M α) : M α := do
  let saved := (← get).lctx.size
  try x finally modify fun s => { s with lctx := s.lctx.truncate saved }

/-- Whether `ty` whnf's to a Π-telescope ending in a sort. -/
def endsInSort : Nat → KExpr .anon → M Bool
  | 0, _ => pure false
  | fuel + 1, ty => do
    resetFuel
    match ← TcM.whnf ty with
    | .sort .. => pure true
    | .all _ _ dom body _ => withScope do
      let (b, _) ← TcM.openBinderAnon dom body
      endsInSort fuel b
    | _ => pure false

/-- Zero condition of a level: `none` when never zero, `some ps` when zero
exactly when every parameter in `ps` is. Exact for every form, so no
normalisation is needed (`Src.zeroCond` on `Univ` is the same recursion). -/
def kZeroCond : KUniv .anon → Option (List Nat)
  | .zero _ => some []
  | .succ .. => none
  | .param i _ _ => some [i.toNat]
  | .max a b _ =>
    match kZeroCond a, kZeroCond b with
    | some xs, some ys => some (xs ++ ys)
    | _, _ => none
  | .imax _ b _ => kZeroCond b

/-- The zero condition of a level as a `PropWhen` (duplicates removed). -/
def condOfLevel (u : KUniv .anon) : PropWhen :=
  match kZeroCond u with
  | none => .never
  | some ps => .allZero ps.eraseDups

/-- When a term of type `ty` is a proof: the zero condition of `ty`'s sort
(D18). Only `ty`'s type is inferred and reduced to a sort, never `ty`
itself; inner errors and sorts that do not reduce count as `never`, as
`isPropType` counts them as not a proof. -/
def sortCond (ty : KExpr .anon) : M PropWhen := do
  resetFuel
  let some s ← (try some <$> inferType ty catch _ => pure none) | return .never
  resetFuel
  let w : Option (KExpr .anon) ← (try some <$> TcM.whnf s catch _ => pure none)
  match w with
  | some (.sort u _) => return condOfLevel u
  | _ => return .never

/-- The proof test comes first: it only infers the type's sort, while the
sort-telescope test reduces the type itself, which for a proposition (a
well-founded decreasing goal, say) can unfold arbitrarily much. A type whose
sort is zero under a condition on the universe parameters is a `proof`
under that condition; a type-former's sort is never zero. -/
def classifyType (ty : KExpr .anon) : M Rel := do
  let w ← sortCond ty
  if w != .never then return .proof w
  if ← endsInSort 256 ty then return .type
  return .rel

def classifyTerm (e : KExpr .anon) : M Rel := do
  classifyType (← inferType e)

/-- `propWhen` of a λ from its opened body: the λ's type is a proof exactly
when the sort of the body's type is zero. -/
def propWhenOf (bodyOpen : KExpr .anon) : M PropWhen := do
  let bty ← inferType bodyOpen
  let s ← inferType bty
  resetFuel
  let u ← TcM.ensureSort s
  return condOfLevel u

structure Acc where
  tags : Array Tag := #[]
  refs : Array CId := #[]
  projs : Array CId := #[]
  nodes : Nat := 0

def nodeBudget : Nat := 1 <<< 20
def depthBudget : Nat := 1 <<< 14

/-- How `propWhen` is computed: from the sort of the opened body's type
(the default), or from the sort of the whole λ's Π type (an independent
re-inference used by the census test). -/
inductive PropWhenVia where
  | body
  | lambda
  deriving BEq, Inhabited

/-- `propWhen` from the λ's own type: its Π type's sort is `imax` of the
domain's and the body's, zero exactly when the body's is. -/
def propWhenOfLam (lamE : KExpr .anon) : M PropWhen := do
  let ty ← inferType lamE
  let s ← inferType ty
  resetFuel
  let u ← TcM.ensureSort s
  return condOfLevel u

/-- A binder written `0` (erased) is irrelevant at every instance:
the class its type gives is kept when that is already irrelevant at every
instance, and is a proof at every instance otherwise. The checker decides
the consequences: a run-time use of the binder fails C1, and a call whose
argument class disagrees with the parameter's fails C2. -/
def honourErased (c : Ixon.V3.BinderContract) (r : Rel) : Rel :=
  if c.uses == .erased && !r.alwaysIrr then Rel.prf else r

/-- Whether the `i`-th argument of a spine headed by `head` meets a binder
written erased: a parameter of a constant's Π telescope, or a binder of a
β-redex's λ telescope. -/
def erasedAt (p : Program) (head : Term) (i : Nat) : Bool :=
  let binders : List (Binder × Term) := match head with
    | .const c _ => ((p.decl? c).map fun (d : Decl) => d.type.pis.1).getD []
    | .lam .. => head.lams.1
    | _ => []
  match binders[i]? with
  | some (b, _) => b.contract.uses == .erased
  | none => false

/-- Walk the positions of a Src term that are relevant at some instance,
with its kernel reading. -/
def walk (p : Program) (via : PropWhenVia) : Nat → Term → KExpr .anon → Acc → M Acc
  | 0, _, _, _ => fail "relevance annotator: depth budget exhausted"
  | fuel + 1, t, e, acc => do
    let acc := { acc with nodes := acc.nodes + 1 }
    if acc.nodes > nodeBudget then fail "relevance annotator: node budget exhausted"
    match t, e with
    | .lam b _ body, .lam _ _ kty kbody _ => do
      let r := honourErased b.contract (← classifyType kty)
      let pwLam ← if via == .lambda then some <$> propWhenOfLam e else pure none
      withScope do
        let (kb, _) ← TcM.openBinderAnon kty kbody
        let pw ← match pwLam with
          | some pw => pure pw
          | none => propWhenOf kb
        walk p via fuel body kb { acc with tags := acc.tags.push (.lam r pw) }
    | .app f a _ _, .app kf ka _ => do
      let acc ← walk p via fuel f kf acc
      let r ← classifyTerm ka
      let (head, args) := Term.spine t
      let r := if erasedAt p head (args.length - 1) then honourErased .erased r else r
      let acc := { acc with tags := acc.tags.push (.arg r) }
      if r.alwaysIrr then pure acc else walk p via fuel a ka acc
    | .letE c _ _ v body, .letE _ kty kv kbody _ _ => do
      let r := honourErased c.binder (← classifyType kty)
      let acc := { acc with tags := acc.tags.push (.letE r) }
      let acc ← if r.alwaysIrr then pure acc else walk p via fuel v kv acc
      withScope do
        let (kb, _) ← TcM.openLet RecM.anonN kty kv kbody
        walk p via fuel body kb acc
    | .proj s _ e', .prj _ _ kv _ => walk p via fuel e' kv { acc with projs := acc.projs.push s }
    | .const c _, .const .. => pure { acc with refs := acc.refs.push c }
    | .var _, .fvar .. | .var _, .var .. => pure acc
    | .natLit _, .nat .. | .strLit _, .str .. | .sort _, .sort .. | .pi .., .all .. => pure acc
    | _, _ => fail "relevance annotator: Src and kernel terms differ in shape"

def kConst (p : Program) (c : CId) : M (KConst .anon) :=
  TcM.getConst ⟨p.addr c, ()⟩

/-- `λ xs. rhs` from `Π xs. Eq B lhs rhs`, as `Table.checkEqn` builds it. -/
def kEqnBody : Nat → KExpr .anon → M (KExpr .anon)
  | 0, _ => fail "relevance annotator: equation telescope too deep"
  | fuel + 1, .all _ _ dom body _ => do
    let b ← kEqnBody fuel body
    TcM.intern (.mkLam RecM.anonN RecM.anonBi dom b)
  | _, e =>
    match e.collectSpine with
    | (_, args) =>
      match args[2]? with
      | some rhs => if args.size == 3 then pure rhs else fail "relevance annotator: not an equation"
      | none => fail "relevance annotator: not an equation"

def kTermOf (p : Program) : TermKey → M (KExpr .anon)
  | .value c => do
    match ← kConst p c with
    | .defn (val := v) .. => pure v
    | _ => fail "relevance annotator: not a definition"
  | .rule r j => do
    match ← kConst p r with
    | .recr (rules := rules) .. =>
      match rules[j]? with
      | some rule => pure rule.rhs
      | none => fail "relevance annotator: missing rule"
    | _ => fail "relevance annotator: not a recursor"
  | .eqn c => do
    match p.table.resolveOf c with
    | some (.eqn thm _) => kEqnBody 4096 (← kConst p thm).ty
    | _ => fail "relevance annotator: no equation entry"

/-- Peel one Π, syntactically or after whnf, opening its binder. -/
def openPi (ty : KExpr .anon) : M (Option (KExpr .anon × KExpr .anon)) := do
  let ty ← match ty with
    | .all .. => pure ty
    | _ => do resetFuel; TcM.whnf ty
  match ty with
  | .all _ _ dom body _ =>
    let (b, _) ← TcM.openBinderAnon dom body
    return some (dom, b)
  | _ => return none

/-- A constant's class and its parameters' classes; a parameter written
erased in the constant's Src type is irrelevant (`honourErased`). -/
def constRel (p : Program) (c : CId) : M ConstRel := do
  let ty := (← kConst p c).ty
  let result ← classifyType ty
  let written := ((p.decl? c).map fun d => d.type.pis.1.map (·.1.contract)).getD []
  withScope do
    let mut cur := ty
    let mut params := #[]
    for _ in [0:4096] do
      match cur with
      | .all _ _ dom body _ =>
        let r ← classifyType dom
        params := params.push (match written[params.size]? with
          | some contract => honourErased contract r
          | none => r)
        let (b, _) ← TcM.openBinderAnon dom body
        cur := b
      | _ => break
    return { result, params := params.toList }

def ctorRel (p : Program) (c : CId) : M CtorRel := do
  let .ctor (params := np) (fields := nf) (ty := ty) .. ← kConst p c
    | fail "relevance annotator: not a constructor"
  withScope do
    let mut cur := ty
    for _ in [0:np.toNat] do
      let some (_, b) ← openPi cur | fail "relevance annotator: constructor parameters"
      cur := b
    let mut fields := #[]
    for _ in [0:nf.toNat] do
      let some (dom, b) ← openPi cur | fail "relevance annotator: constructor fields"
      fields := fields.push (FieldClass.ofRel (← classifyType dom))
      cur := b
    return { fields := fields.toList }

/-- Constructors of an inductive (for recursors and projections). -/
def ctorsOf (p : Program) (ind : CId) : Array CId :=
  match p.decl? ind with
  | some (.induct _ _ _ _ _ ctors) => ctors.toArray
  | _ => #[]

def run (p : Program) (via : PropWhenVia := .body) : M Ann := do
  let n := p.size
  let mut reached : Array Bool := .replicate n false
  let mut consts : Array (Option ConstRel) := .replicate n none
  let mut ctors : Array (Option CtorRel) := .replicate n none
  let mut nodes : Array (TermKey × Array Tag) := #[]
  let mut queue : Array CId := p.roots.toArray.map (·.2)
  let mut ctorQueue : Array CId := #[]
  let mut qi := 0
  while qi < queue.size do
    let c := queue[qi]!
    qi := qi + 1
    if reached[c]?.getD true then continue
    reached := reached.set! c true
    consts := consts.set! c (some (← constRel p c))
    match p.decl? c with
    | some (.ctor ..) => ctorQueue := ctorQueue.push c
    | some (.recr _ _ _ _ _ _ _ ind _ _) => ctorQueue := ctorQueue ++ ctorsOf p ind
    | _ => pure ()
    for key in p.runtimeKeys c do
      let some t := p.termOf key | fail "relevance annotator: missing runtime term"
      let e ← kTermOf p key
      let acc ← walk p via depthBudget t e {}
      nodes := nodes.push (key, acc.tags)
      queue := queue ++ acc.refs
      for s in acc.projs do ctorQueue := ctorQueue ++ ctorsOf p s
    queue := queue ++ (p.runtimeRefs c).toArray.map (·.1)
  for c in ctorQueue do
    if (ctors[c]?).join.isNone then ctors := ctors.set! c (some (← ctorRel p c))
  return { consts := NatMap.ofOptions consts.toList, ctors := NatMap.ofOptions ctors.toList
           nodes := nodes.toList.map fun (key, tags) => (key, tags.toList) }

end IxCC.Src.Relevance.Annotate

namespace IxCC.Src.Relevance

/-- The annotator with a chosen `propWhen` method. -/
def annotateVia (via : Annotate.PropWhenVia) (env : Ixon.V3.Env) (p : Program) :
    Except String Ann :=
  match (Annotate.run p via).run (Ixon.V3.Tc.initialState env) with
  | .ok ann _ => .ok ann
  | .error e _ => .error s!"relevance annotator: {e}"

/-- The relevance oracle: annotate the runtime-reachable part of `p`, read
from the typed environment `env` that `p` was ingressed from. -/
def annotate (env : Ixon.V3.Env) (p : Program) : Except String Ann :=
  annotateVia .body env p

/-- Field classes of the given constructors (for the census). -/
def ctorRels (env : Ixon.V3.Env) (p : Program) (cs : Array CId) :
    Except String (Array (CId × CtorRel)) :=
  match (cs.mapM fun c => do return (c, ← Annotate.ctorRel p c)).run
      (Ixon.V3.Tc.initialState env) with
  | .ok out _ => .ok out
  | .error e _ => .error s!"relevance annotator: {e}"

end IxCC.Src.Relevance
