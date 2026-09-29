import Compilatrix.Src.Relevance.Syntax
import Compilatrix.Ixon.V3.Tc.Driver

/-! # The relevance annotator (untrusted)

Produces an `Ann` for the runtime-reachable part of a program (design note
02 §3.2) with the ported checker's context: each runtime term is walked in
step with its kernel reading (`KExpr`, from the same v3 expression, so the
shapes agree node for node), opening binders as free variables. A binder,
argument or let whose type whnf's to a Π-telescope ending in a sort is
`type`; one whose type satisfies `isPropType` is `proof`; anything else is
`rel`. Each λ gets `propWhen` from the zero condition of the sort of its
body's type. Field classes and constant classes use the same test.

The annotator is an oracle of the pipeline: nothing it produces is trusted.
`Src.Relevance.check` decides the result, and a wrong annotation only makes
SrcEval stuck. It starts from the roots and follows relevant references, so
theorems and types reached only through irrelevant positions are never
walked. -/

namespace Compilatrix.Src.Relevance.Annotate

open Compilatrix.Ixon Compilatrix.Ixon.V3.Tc

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

/-- The proof test comes first: it only infers the type's sort, while the
sort-telescope test reduces the type itself, which for a proposition (a
well-founded decreasing goal, say) can unfold arbitrarily much. -/
def classifyType (ty : KExpr .anon) : M Rel := do
  resetFuel
  if ← TcM.runRec (RecM.isPropType ty) then return .proof
  if ← endsInSort 256 ty then return .type
  return .rel

def classifyTerm (e : KExpr .anon) : M Rel := do
  classifyType (← inferType e)

/-- Zero condition of a level: `none` when never zero, `some ps` when zero
exactly when every parameter in `ps` is. -/
def zeroCond : KUniv .anon → Option (List Nat)
  | .zero _ => some []
  | .succ .. => none
  | .param i _ _ => some [i.toNat]
  | .max a b _ =>
    match zeroCond a, zeroCond b with
    | some xs, some ys => some (xs ++ ys)
    | _, _ => none
  | .imax _ b _ => zeroCond b

/-- `propWhen` of a λ from its opened body: the λ's type is a proof exactly
when the sort of the body's type is zero. -/
def propWhenOf (bodyOpen : KExpr .anon) : M PropWhen := do
  let bty ← inferType bodyOpen
  let s ← inferType bty
  resetFuel
  let u ← TcM.ensureSort s
  return match zeroCond u with
    | none => .never
    | some ps => .allZero ps.eraseDups

def fieldClass : Rel → FieldClass
  | .rel => .keep
  | .proof => .proof
  | .type => .type

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
  return match zeroCond u with
    | none => .never
    | some ps => .allZero ps.eraseDups

/-- Walk the relevant positions of a Src term and its kernel reading. -/
def walk (via : PropWhenVia) : Nat → Term → KExpr .anon → Acc → M Acc
  | 0, _, _, _ => fail "relevance annotator: depth budget exhausted"
  | fuel + 1, t, e, acc => do
    let acc := { acc with nodes := acc.nodes + 1 }
    if acc.nodes > nodeBudget then fail "relevance annotator: node budget exhausted"
    match t, e with
    | .lam _ _ body, .lam _ _ kty kbody _ => do
      let r ← classifyType kty
      let pwLam ← if via == .lambda then some <$> propWhenOfLam e else pure none
      withScope do
        let (kb, _) ← TcM.openBinderAnon kty kbody
        let pw ← match pwLam with
          | some pw => pure pw
          | none => propWhenOf kb
        walk via fuel body kb { acc with tags := acc.tags.push (.lam r pw) }
    | .app f a _, .app kf ka _ => do
      let acc ← walk via fuel f kf acc
      let r ← classifyTerm ka
      let acc := { acc with tags := acc.tags.push (.arg r) }
      if r == .rel then walk via fuel a ka acc else pure acc
    | .letE _ _ _ v body, .letE _ kty kv kbody _ _ => do
      let r ← classifyType kty
      let acc := { acc with tags := acc.tags.push (.letE r) }
      let acc ← if r == .rel then walk via fuel v kv acc else pure acc
      withScope do
        let (kb, _) ← TcM.openLet RecM.anonN kty kv kbody
        walk via fuel body kb acc
    | .proj s _ e', .prj _ _ kv _ => walk via fuel e' kv { acc with projs := acc.projs.push s }
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

def constRel (p : Program) (c : CId) : M ConstRel := do
  let ty := (← kConst p c).ty
  let result ← classifyType ty
  withScope do
    let mut cur := ty
    let mut params := #[]
    for _ in [0:4096] do
      match cur with
      | .all _ _ dom body _ =>
        params := params.push (← classifyType dom)
        let (b, _) ← TcM.openBinderAnon dom body
        cur := b
      | _ => break
    return { result, params }

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
      fields := fields.push (fieldClass (← classifyType dom))
      cur := b
    return { fields }

/-- Constructors of an inductive (for recursors and projections). -/
def ctorsOf (p : Program) (ind : CId) : Array CId :=
  match p.decl? ind with
  | some (.induct _ _ _ _ _ ctors) => ctors
  | _ => #[]

def run (p : Program) (via : PropWhenVia := .body) : M Ann := do
  let n := p.size
  let mut reached : Array Bool := .replicate n false
  let mut consts : Array (Option ConstRel) := .replicate n none
  let mut ctors : Array (Option CtorRel) := .replicate n none
  let mut nodes : Array (TermKey × Array Tag) := #[]
  let mut queue : Array CId := p.roots.map (·.2)
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
      let acc ← walk via depthBudget t e {}
      nodes := nodes.push (key, acc.tags)
      queue := queue ++ acc.refs
      for s in acc.projs do ctorQueue := ctorQueue ++ ctorsOf p s
    queue := queue ++ p.runtimeRefs c
  for c in ctorQueue do
    if (ctors[c]?).join.isNone then ctors := ctors.set! c (some (← ctorRel p c))
  return { consts, ctors, nodes }

end Compilatrix.Src.Relevance.Annotate

namespace Compilatrix.Src.Relevance

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

end Compilatrix.Src.Relevance
