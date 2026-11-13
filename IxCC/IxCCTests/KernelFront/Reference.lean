import IxCC.Src.KernelFront.Annotate

/-! # The kernel annotator before the λ-run change (test-only reference)

`Src.KernelFront.annotate` asks the kernel for a λ's condition once per maximal run of λs, of the
run's innermost body, and `Ctx.sortCond` continues with the empty memo when the kernel fails it
(2026-11-13). Below is the definition it replaced, verbatim but for names: the kernel asked at
every λ (`walk`'s `propWhenOf (d + 1) kb`), and `sortCond` kept the state from before its call
for its failure branches. The two are tested equal (`LamRuns`), not proved equal; this copy is
the reference for that test and is not in the production library. The helpers the two share
(`Ctx.annotate`, `endsInSort`, `propWhenOf`, `openPi`, `kernelTermOf`, …) are production's. -/

namespace IxCCTests.KernelFront.Reference

open IxCC IxCC.Src IxCC.Src.Relevance IxCC.Src.KernelFront

def sortCond (k : Ctx) (d : Nat) (ty : KTerm) : AM PropWhen := fun s =>
  match k.core.infer d ty s with
  | .error _ => .ok (.never, s)
  | .ok (t, s₁) =>
    match k.core.whnf d t s₁ with
    | .ok (.sort u, s₂) => .ok (condOfLevel k.back u, s₂)
    | .ok (_, s₂) => .ok (.never, s₂)
    | .error _ => .ok (.never, s₁)

def classifyAnnotated (k : Ctx) (d : Nat) (ty : KTerm) : AM Rel := fun s =>
  match sortCond k d ty s with
  | .error e => .error e
  | .ok (w, s₁) =>
    if w = .never then
      match k.endsInSort 256 d ty s₁ with
      | .ok (true, s₂) => .ok (.type, s₂)
      | .ok (false, s₂) => .ok (.rel, s₂)
      | .error e => .error e
    else .ok (.proof w, s₁)

def classifyType (k : Ctx) (d : Nat) (ty : KTerm) : AM Rel := fun s =>
  match k.core.annotate d ty s with
  | .error e => .error s!"annotation: {e}"
  | .ok (ty', s₁) => classifyAnnotated k d ty' s₁

def classifyTerm (k : Ctx) (d : Nat) (e : KTerm) : AM Rel := fun s =>
  match k.core.annotate d e s with
  | .error err => .error s!"annotation: {err}"
  | .ok (e', s₁) =>
    match k.core.infer d e' s₁ with
    | .error err => .error s!"inference: {err}"
    | .ok (t, s₂) => classifyAnnotated k d t s₂

def walk (p : Program) (k : Ctx) : Nat → Nat → Term → KTerm → Acc → AM Acc
  | 0, _, _, _, _ => throw "relevance annotator: depth budget exhausted"
  | fuel + 1, d, t, e, acc => do
    let acc := { acc with nodes := acc.nodes + 1 }
    if acc.nodes > nodeBudget then throw "relevance annotator: node budget exhausted"
    match t, e with
    | .lam b _ body, .lam kty kbody _ => do
      let r := honourErased b.contract (← classifyType k d kty)
      let kty' ← k.annotate d kty
      let kb := kbody.instantiate1 (.fvar d kty')
      let pw ← k.propWhenOf (d + 1) kb
      walk p k fuel (d + 1) body kb { acc with tags := acc.tags.push (.lam r pw) }
    | .app f a _ _, .app kf ka => do
      let acc ← walk p k fuel d f kf acc
      let r ← classifyTerm k d ka
      let (head, args) := Term.spine t
      let r := if erasedAt p head (args.length - 1) then honourErased .erased r else r
      let acc := { acc with tags := acc.tags.push (.arg r) }
      if r.alwaysIrr then pure acc else walk p k fuel d a ka acc
    | .letE c _ _ v body, .letE kty kv kbody _ => do
      let r := honourErased c.binder (← classifyType k d kty)
      let acc := { acc with tags := acc.tags.push (.letE r) }
      let acc ← if r.alwaysIrr then pure acc else walk p k fuel d v kv acc
      walk p k fuel d body (kbody.instantiate1 kv) acc
    | .proj s _ e', .proj _ _ kv => walk p k fuel d e' kv { acc with projs := acc.projs.push s }
    | .const c _, .const .. => pure { acc with refs := acc.refs.push c }
    | .var _, _ => pure acc
    | .natLit _, .lit .. | .strLit _, .lit .. | .sort _, .sort .. | .pi .., .forallE .. => pure acc
    | _, _ => throw s!"relevance annotator: a Src {srcHead t} node meets a kernel {kHead e} node"

def constRel (p : Program) (k : Ctx) (c : CId) (ty : KTerm) : AM ConstRel := do
  let result ← classifyType k 0 ty
  let written := ((p.decl? c).map fun d => d.type.pis.1.map (·.1.contract)).getD []
  let mut cur := ty
  let mut d := 0
  let mut params := #[]
  for _ in [0:4096] do
    match cur with
    | .forallE dom body _ =>
      let r ← classifyType k d dom
      params := params.push (match written[params.size]? with
        | some contract => honourErased contract r
        | none => r)
      let dom' ← k.annotate d dom
      cur := body.instantiate1 (.fvar d dom')
      d := d + 1
    | _ => break
  return { result, params := params.toList }

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
    fields := fields.push (FieldClass.ofRel (← classifyType k d dom))
    cur := b
    d := d + 1
  return { fields := fields.toList }

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

/-- The annotator before 2026-11-13 (`Src.KernelFront.annotate`'s former definition). -/
def annotate (fe : Ix.Kernel.FEnv .anon) (rd : Reading) (p : Program) : Except String Ann :=
  match (annotateRun p rd (coreOf fe)).run {} with
  | .ok (ann, _) => .ok ann
  | .error e => .error s!"relevance annotator (kernel): {e}"

end IxCCTests.KernelFront.Reference
