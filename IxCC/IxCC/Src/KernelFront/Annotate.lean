import IxCC.Src.KernelFront.Reading
import IxCC.Src.Relevance.Syntax
import IxCK.Kernel.Cached.CoreC

/-! # The relevance annotation from the certified kernel's inference

The kernel front end's annotator: the same annotation as IxCC's earlier
annotator (`Src.Relevance.annotate`, which asked IxCC's own erased type
checker), computed from the certified kernel's type inference, weak head
normalisation and annotation pass over the environment the kernel accepted
(`Accepted.env`), each question asked of the kernel's own reading of the term
at the position IxCC's term occupies.

For each runtime term (a definition's value, a recursor rule's right-hand
side, or an equation's body) of each constant the roots reach, the annotator

1. checks that IxCC's term corresponds to the kernel's reading of it
   (`Reading.corr`; an equation's body, which IxCC's table check builds, is
   translated instead, `toKernel`);
2. walks the two together, opening each λ binder as a kernel free variable
   whose type is the binder's annotated domain and reducing each `let` as the
   kernel's annotation pass does (substituting its value into its body), and
   classifies every binder, argument and let:
   * a **proof** under a zero condition when the sort of its type is zero
     exactly under that condition on the constant's universe parameters (D18):
     the kernel infers the position's type, infers that type's type and reduces
     it to `Sort u`, and the condition is `u`'s (`zeroCond`);
   * a **type** when its type reduces to a Π-telescope ending in a sort;
   * **relevant** otherwise;

   and gives each λ the zero condition of the sort of its body's type;
3. records the constants the term reaches in relevant positions, which joins
   them to the queue.

Every constant reached also gets its own class and its Π-telescope's binder
classes (`constRel`), and every constructor its fields' classes (`ctorRel`).
A binder written erased is irrelevant at every instance whatever its type
(`honourErased`), as before. The output is the annotation's format
(`Src.Relevance.Ann`); the recheck path decides it as before
(`Relevance.check`, `checkCanonical`), and the byte-level verifiers require it
to be this function's output (`Front.checkCanonicalRelevance`).

**Positions.** The kernel's binder datum (`BinderMeta.pw`) is the zero
condition of a binder's *codomain*; IxCC's position classes are about the
*domain* (a binder's type, an argument's type), so the annotator asks the
kernel's inference about domains and arguments rather than reading `pw`.

**Universes.** The kernel's reader renames a large eliminator's universe
parameters (`Reading.backOf`); every condition is read back to IxCC's
numbering before it is recorded.

The kernel calls are the executed cached core (`Ix.Kernel.Cached.coreKnotI
.verified`), threaded through one memo state; each call is bounded by the
kernel's own fuel (`Ix.Kernel.checkFuel`). Every walk is bounded by a depth
and a node budget. -/

namespace IxCC.Src.KernelFront

open IxCC.Src IxCC.Src.Relevance

/-- The annotator's monad: the kernel core's memo state, over IxCC's
failures. -/
abbrev AM := StateT (Ix.Kernel.Cached.CState .anon) (Except String)

/-- The cached core over an accepted environment's index, at the verified
mode and the kernel's fuel. -/
def coreOf (fe : Ix.Kernel.FEnv .anon) : Ix.Kernel.Cached.CoreFnsI .anon :=
  Ix.Kernel.Cached.coreKnotI .verified fe Ix.Kernel.checkFuel

/-- Run a kernel call; a kernel failure is the annotator's. -/
def kcall (what : String) (x : Ix.Kernel.Cached.CheckCM .anon α) : AM α := fun s =>
  match x s with
  | .ok (a, s') => .ok (a, s')
  | .error e => .error s!"{what}: {e}"

/-- The zero condition of a level, over its parameters: `none` when never
zero, `some ps` when zero exactly when every parameter in `ps` is. Exact for
every form, so no normalisation is needed; the list is in the order the
earlier annotator gave it (`Src.zeroCond` on `Univ` is the same recursion). -/
def zeroCond : KLevel → Option (List Nat)
  | .zero => some []
  | .succ _ => none
  | .param i => some [i]
  | .max a b =>
    match zeroCond a, zeroCond b with
    | some xs, some ys => some (xs ++ ys)
    | _, _ => none
  | .imax _ b => zeroCond b

/-- The zero condition of a level as a `PropWhen`, its kernel parameters read
back to IxCC's numbering (`back`), duplicates removed. -/
def condOfLevel (back : Nat → Nat) (u : KLevel) : PropWhen :=
  match zeroCond u with
  | none => .never
  | some ps => .allZero (ps.map back).eraseDups

/-- What a classification needs: the core, and the reading-back of the
universe parameters of the constant whose term is walked. -/
structure Ctx where
  core : Ix.Kernel.Cached.CoreFnsI .anon
  back : Nat → Nat

/-- The kernel's annotation pass on a term at depth `d` (free variables below
`d`): what inference and reduction take. -/
def Ctx.annotate (k : Ctx) (d : Nat) (e : KTerm) : AM KTerm :=
  kcall "annotation" (k.core.annotate d e)

/-- When a term whose (annotated) type is `ty` is a proof: the zero condition
of `ty`'s sort. Only `ty`'s type is inferred and reduced to a sort; a failure
counts as `never`, as before. -/
def Ctx.sortCond (k : Ctx) (d : Nat) (ty : KTerm) : AM PropWhen := fun s =>
  match k.core.infer d ty s with
  | .error _ => .ok (.never, s)
  | .ok (t, s₁) =>
    match k.core.whnf d t s₁ with
    | .ok (.sort u, s₂) => .ok (condOfLevel k.back u, s₂)
    | .ok (_, s₂) => .ok (.never, s₂)
    | .error _ => .ok (.never, s₁)

/-- Whether an (annotated) type reduces to a Π-telescope ending in a sort. -/
def Ctx.endsInSort (k : Ctx) : Nat → Nat → KTerm → AM Bool
  | 0, _, _ => pure false
  | fuel + 1, d, ty => do
    match ← kcall "reduction" (k.core.whnf d ty) with
    | .sort .. => pure true
    | .forallE dom body _ => k.endsInSort fuel (d + 1) (body.instantiate1 (.fvar d dom))
    | _ => pure false

/-- The class of a position whose annotated type is `ty`: the proof test
first (it only infers the type's sort), then the type-former test. -/
def Ctx.classifyAnnotated (k : Ctx) (d : Nat) (ty : KTerm) : AM Rel := fun s =>
  match k.sortCond d ty s with
  | .error e => .error e
  | .ok (w, s₁) =>
    if w = .never then
      match k.endsInSort 256 d ty s₁ with
      | .ok (true, s₂) => .ok (.type, s₂)
      | .ok (false, s₂) => .ok (.rel, s₂)
      | .error e => .error e
    else .ok (.proof w, s₁)

/-- The class of a position whose type is the (read) term `ty`. -/
def Ctx.classifyType (k : Ctx) (d : Nat) (ty : KTerm) : AM Rel := fun s =>
  match k.core.annotate d ty s with
  | .error e => .error s!"annotation: {e}"
  | .ok (ty', s₁) => k.classifyAnnotated d ty' s₁

/-- The class of the (read) term `e` as a position: its inferred type's. -/
def Ctx.classifyTerm (k : Ctx) (d : Nat) (e : KTerm) : AM Rel := fun s =>
  match k.core.annotate d e s with
  | .error err => .error s!"annotation: {err}"
  | .ok (e', s₁) =>
    match k.core.infer d e' s₁ with
    | .error err => .error s!"inference: {err}"
    | .ok (t, s₂) => k.classifyAnnotated d t s₂

/-- A λ's `propWhen` from its opened body (a read term at depth `d`): the λ's
type is a proof exactly when the sort of the body's type is zero. -/
def Ctx.propWhenOf (k : Ctx) (d : Nat) (body : KTerm) : AM PropWhen := do
  let b' ← k.annotate d body
  let bty ← kcall "inference" (k.core.infer d b')
  let s ← kcall "inference" (k.core.infer d bty)
  match ← kcall "reduction" (k.core.whnf d s) with
  | .sort u => return condOfLevel k.back u
  | _ => throw "relevance annotator: a λ body's type is not a type"

/-- A binder written `0` (erased) is irrelevant at every instance: the class
its type gives is kept when that is already irrelevant at every instance, and
is a proof at every instance otherwise. -/
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

structure Acc where
  tags : Array Tag := #[]
  refs : Array CId := #[]
  projs : Array CId := #[]
  nodes : Nat := 0

/-- Walk the positions of a Src term that are relevant at some instance, with
the kernel's reading of the term at depth `d` (outer λ binders opened as free
variables, outer lets substituted). -/
def walk (p : Program) (k : Ctx) : Nat → Nat → Term → KTerm → Acc → AM Acc
  | 0, _, _, _, _ => throw "relevance annotator: depth budget exhausted"
  | fuel + 1, d, t, e, acc => do
    let acc := { acc with nodes := acc.nodes + 1 }
    if acc.nodes > nodeBudget then throw "relevance annotator: node budget exhausted"
    match t, e with
    | .lam b _ body, .lam kty kbody _ => do
      let r := honourErased b.contract (← k.classifyType d kty)
      let kty' ← k.annotate d kty
      let kb := kbody.instantiate1 (.fvar d kty')
      let pw ← k.propWhenOf (d + 1) kb
      walk p k fuel (d + 1) body kb { acc with tags := acc.tags.push (.lam r pw) }
    | .app f a _ _, .app kf ka => do
      let acc ← walk p k fuel d f kf acc
      let r ← k.classifyTerm d ka
      let (head, args) := Term.spine t
      let r := if erasedAt p head (args.length - 1) then honourErased .erased r else r
      let acc := { acc with tags := acc.tags.push (.arg r) }
      if r.alwaysIrr then pure acc else walk p k fuel d a ka acc
    | .letE c _ _ v body, .letE kty kv kbody _ => do
      let r := honourErased c.binder (← k.classifyType d kty)
      let acc := { acc with tags := acc.tags.push (.letE r) }
      let acc ← if r.alwaysIrr then pure acc else walk p k fuel d v kv acc
      -- the kernel's annotation pass reduces a `let` by substituting its value
      walk p k fuel d body (kbody.instantiate1 kv) acc
    | .proj s _ e', .proj _ _ kv => walk p k fuel d e' kv { acc with projs := acc.projs.push s }
    | .const c _, .const .. => pure { acc with refs := acc.refs.push c }
    -- a λ-bound variable is a free variable; a let-bound one is the let's value
    | .var _, _ => pure acc
    | .natLit _, .lit .. | .strLit _, .lit .. | .sort _, .sort .. | .pi .., .forallE .. => pure acc
    | _, _ => throw s!"relevance annotator: a Src {srcHead t} node meets a kernel {kHead e} node"

/-- `λ xs. rhs` from the kernel's reading of an equation theorem's type
`Π xs. Eq B lhs rhs`. -/
def eqnBodyOf : Nat → KTerm → Except String KTerm
  | 0, _ => throw "relevance annotator: equation telescope too deep"
  | fuel + 1, .forallE dom body mb => do
    let b ← eqnBodyOf fuel body
    pure (.lam dom b (Ix.Kernel.BinderMeta.ofContracts mb.contract .shared))
  | _, e =>
    match e.getAppArgs with
    | [_, _, rhs] => pure rhs
    | _ => throw "relevance annotator: not an equation"

/-- The kernel term of a runtime term, with the kernel parameters of the
constant it belongs to: a value's or a rule's reading, after checking that
IxCC's term corresponds to it; an equation's body translated
(`toKernel`), IxCC's table check having built it. -/
def kernelTermOf (p : Program) (rd : Reading) (key : TermKey) (t : Term) :
    Except String (KTerm × List Nat) := do
  match key with
  | .value c =>
    let some (.defn cv v _) := rd.info? c
      | throw s!"constant {c}: the kernel's reading has no definition there"
    let _ ← (corr rd.keys cv.levelParams depthBudget t v nodeBudget).mapError
      fun e => s!"constant {c} ({p.addr c}), its value: {e}"
    pure (v, cv.levelParams)
  | .rule r j =>
    let some (.recr cv _ _ rules) := rd.info? r
      | throw s!"constant {r}: the kernel's reading has no recursor there"
    let some rule := rules[j]? | throw s!"recursor {r}: no rule {j} in the kernel's reading"
    let _ ← (corr rd.keys cv.levelParams depthBudget t rule.rhs nodeBudget).mapError
      fun e => s!"recursor {r} ({p.addr r}), rule {j}: {e}"
    pure (rule.rhs, cv.levelParams)
  | .eqn c =>
    let lps := rd.lps c
    let (e, _) ← (toKernel rd.keys lps depthBudget t).run nodeBudget
    pure (e, lps)

/-- Peel one Π, syntactically or after reduction, opening its binder at
depth `d`: the binder's annotated domain and the opened body. -/
def Ctx.openPi (k : Ctx) (d : Nat) (ty : KTerm) : AM (Option (KTerm × KTerm)) := do
  let ty ← match ty with
    | .forallE .. => pure ty
    | _ => do kcall "reduction" (k.core.whnf d (← k.annotate d ty))
  match ty with
  | .forallE dom body _ =>
    let dom' ← k.annotate d dom
    return some (dom, body.instantiate1 (.fvar d dom'))
  | _ => return none

/-- A constant's class and its Π telescope's binder classes, from its kernel
type; a parameter written erased in its Src type is irrelevant. -/
def constRel (p : Program) (k : Ctx) (c : CId) (ty : KTerm) : AM ConstRel := do
  let result ← k.classifyType 0 ty
  let written := ((p.decl? c).map fun d => d.type.pis.1.map (·.1.contract)).getD []
  let mut cur := ty
  let mut d := 0
  let mut params := #[]
  for _ in [0:4096] do
    match cur with
    | .forallE dom body _ =>
      let r ← k.classifyType d dom
      params := params.push (match written[params.size]? with
        | some contract => honourErased contract r
        | none => r)
      let dom' ← k.annotate d dom
      cur := body.instantiate1 (.fvar d dom')
      d := d + 1
    | _ => break
  return { result, params := params.toList }

/-- A constructor's field classes, from its kernel type. -/
def ctorRel (k : Ctx) (np nf : Nat) (ty : KTerm) : AM CtorRel := do
  let mut cur := ty
  let mut d := 0
  for _ in [0:np] do
    let some (_, b) ← k.openPi d cur | throw "relevance annotator: constructor parameters"
    cur := b
    d := d + 1
  let mut fields := #[]
  for _ in [0:nf] do
    let some (dom, b) ← k.openPi d cur | throw "relevance annotator: constructor fields"
    fields := fields.push (FieldClass.ofRel (← k.classifyType d dom))
    cur := b
    d := d + 1
  return { fields := fields.toList }

/-- Constructors of an inductive (for recursors and projections). -/
def ctorsOf (p : Program) (ind : CId) : Array CId :=
  match p.decl? ind with
  | some (.induct _ _ _ _ _ ctors) => ctors.toArray
  | _ => #[]

/-- The annotation of the runtime-reachable part of `p`, from the roots, with
the kernel core `core` over the accepted environment. -/
def annotateRun (p : Program) (rd : Reading) (core : Ix.Kernel.Cached.CoreFnsI .anon) : AM Ann := do
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
    let some info := rd.info? c | throw s!"relevance annotator: constant {c} has no kernel declaration"
    let lps := info.cv.levelParams
    let kc : Ctx := { core, back := backOf lps }
    consts := consts.set! c (some (← constRel p kc c info.cv.type))
    match p.decl? c with
    | some (.ctor ..) => ctorQueue := ctorQueue.push c
    | some (.recr _ _ _ _ _ _ _ ind _ _) => ctorQueue := ctorQueue ++ ctorsOf p ind
    | _ => pure ()
    for key in p.runtimeKeys c do
      let some t := p.termOf key | throw "relevance annotator: missing runtime term"
      let (e, lps) ← (kernelTermOf p rd key t : Except String _)
      let acc ← walk p { core, back := backOf lps } depthBudget 0 t e {}
      nodes := nodes.push (key, acc.tags)
      queue := queue ++ acc.refs
      for s in acc.projs do ctorQueue := ctorQueue ++ ctorsOf p s
    queue := queue ++ (p.runtimeRefs c).toArray.map (·.1)
  for c in ctorQueue do
    if (ctors[c]?).join.isNone then
      let some (.ctor cv np nf) := rd.info? c
        | throw s!"relevance annotator: constant {c} is not a constructor in the kernel's reading"
      ctors := ctors.set! c (some (← ctorRel { core, back := backOf cv.levelParams } np nf cv.type))
  return { consts := NatMap.ofOptions consts.toList, ctors := NatMap.ofOptions ctors.toList
           nodes := nodes.toList.map fun (key, tags) => (key, tags.toList) }

/-- **The relevance oracle over the certified kernel**: annotate the
runtime-reachable part of `p` (IxCC's reading of the accepted environment,
keyed to the kernel's by `rd`), asking the kernel core over the accepted
environment's index `fe`. -/
def annotate (fe : Ix.Kernel.FEnv .anon) (rd : Reading) (p : Program) : Except String Ann :=
  match (annotateRun p rd (coreOf fe)).run {} with
  | .ok (ann, _) => .ok ann
  | .error e => .error s!"relevance annotator (kernel): {e}"

/-- The constants an annotation reaches: every constant with a class and
every constructor with field classes. -/
def annReached (a : Ann) (size : Nat) : List CId :=
  (List.range size).filter fun c => (a.constRel? c).isSome || (a.ctorRel? c).isSome

/-- **The types the program reads correspond to the kernel's**: the type of
every constant an annotation reaches, and of every theorem the unfolding table
names, is the kernel's reading of it (`Reading.typeCheck`). -/
def checkReachedTypes (rd : Reading) (p : Program) (a : Ann) : Except String Unit := do
  let tableThms : List CId := (List.range p.size).flatMap fun c =>
    match p.table.resolveOf c with
    | some (.eqn thm _) => [thm]
    | some (.csimp g _ thm) => [g, thm]
    | some (.case r) => [r]
    | _ => []
  for c in (annReached a p.size ++ tableThms).eraseDups do
    rd.typeCheck p c

end IxCC.Src.KernelFront
