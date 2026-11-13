import IxCC.Recheck
import IxCC.Src.KernelFront.Annotate

/-! H11's Stage A probe (test-only; removed before the landing). `stagea CLOSURE EQS ROOT CERT`
times production's `annotate` and `checkReachedTypes` on a saved zero-RC certificate, then runs
copies of the annotator, one change each, and compares each copy's annotation with production's:

* `copy`: the text of `annotateRun` verbatim (timing sanity);
* `noretain`: `sortCond` does not keep the pre-call state for its failure branches (a failure
  continues with the empty memo), so the kernel's memo is updated in place;
* `reset`: every constant reached starts from the empty memo (the kernel's per-declaration rule);
* `nopw`: no `propWhenOf` (every λ gets `.never`; wrong output, measures that part's share);
* `instr`: `copy` with counters: per site, the `sortCond` calls and those that grew the memo,
  with the first types that did. -/

namespace IxCCTests.KernelFront.ProbeH11

open IxCC IxCC.Src IxCC.Src.Relevance IxCC.Src.KernelFront

structure V where
  noRetain : Bool := false
  reset : Bool := false
  noPw : Bool := false
  instr : Bool := false

abbrev CS := Ix.Kernel.Cached.CState .anon

def memoSize (s : CS) : Nat :=
  s.inferC.size + s.whnfC.size + s.whnfCoreC.size + s.annotC.size + s.defeqC.size +
    s.constTyAt.size + s.constValAt.size + s.instC.size

/-- `sortCond`, with the memo growth of the call (0 unless `instr`). -/
def sortCondV (v : V) (k : Ctx) (d : Nat) (ty : KTerm) : AM (PropWhen × Nat) := fun s =>
  let n0 := if v.instr then memoSize s else 0
  if v.noRetain then
    match k.core.infer d ty s with
    | .error _ => .ok ((.never, 0), {})
    | .ok (t, s₁) =>
      match k.core.whnf d t s₁ with
      | .ok (.sort u, s₂) => .ok ((condOfLevel k.back u, if v.instr then memoSize s₂ - n0 else 0), s₂)
      | .ok (_, s₂) => .ok ((.never, if v.instr then memoSize s₂ - n0 else 0), s₂)
      | .error _ => .ok ((.never, 0), {})
  else
    match k.core.infer d ty s with
    | .error _ => .ok ((.never, 0), s)
    | .ok (t, s₁) =>
      match k.core.whnf d t s₁ with
      | .ok (.sort u, s₂) => .ok ((condOfLevel k.back u, if v.instr then memoSize s₂ - n0 else 0), s₂)
      | .ok (_, s₂) => .ok ((.never, if v.instr then memoSize s₂ - n0 else 0), s₂)
      | .error _ => .ok ((.never, 0), s₁)

def classifyAnnotatedV (v : V) (k : Ctx) (d : Nat) (ty : KTerm) : AM (Rel × Nat) := fun s =>
  match sortCondV v k d ty s with
  | .error e => .error e
  | .ok ((w, g), s₁) =>
    if w = .never then
      match k.endsInSort 256 d ty s₁ with
      | .ok (true, s₂) => .ok ((.type, g), s₂)
      | .ok (false, s₂) => .ok ((.rel, g), s₂)
      | .error e => .error e
    else .ok ((.proof w, g), s₁)

def classifyTypeV (v : V) (k : Ctx) (d : Nat) (ty : KTerm) : AM (Rel × Nat) := fun s =>
  match k.core.annotate d ty s with
  | .error e => .error s!"annotation: {e}"
  | .ok (ty', s₁) => classifyAnnotatedV v k d ty' s₁

def classifyTermV (v : V) (k : Ctx) (d : Nat) (e : KTerm) : AM (Rel × Nat × KTerm) := fun s =>
  match k.core.annotate d e s with
  | .error err => .error s!"annotation: {err}"
  | .ok (e', s₁) =>
    match k.core.infer d e' s₁ with
    | .error err => .error s!"inference: {err}"
    | .ok (t, s₂) =>
      match classifyAnnotatedV v k d t s₂ with
      | .error err => .error err
      | .ok ((r, g), s₃) => .ok ((r, g, t), s₃)

/-- Counters: per site (0 λ, 1 argument, 2 let, 3 constRel, 4 ctorRel), calls and growing calls. -/
structure Cnt where
  calls : Array Nat := .replicate 5 0
  grew : Array Nat := .replicate 5 0
  examples : Array (List String) := .replicate 5 []

def Cnt.note (c : Cnt) (v : V) (site : Nat) (g : Nat) (ty : Unit → KTerm) : Cnt :=
  if !v.instr then c else
  let c := { c with calls := c.calls.modify site (· + 1) }
  if g == 0 then c else
  let c := { c with grew := c.grew.modify site (· + 1) }
  if (c.examples[site]!).length < 3 then
    { c with examples := c.examples.modify site (· ++ [s!"(+{g}) " ++ ((toString (repr (ty ()))).take 300)]) }
  else c

structure AccV where
  tags : Array Tag := #[]
  refs : Array CId := #[]
  projs : Array CId := #[]
  nodes : Nat := 0

def walkV (v : V) (p : Program) (k : Ctx) : Nat → Nat → Term → KTerm → AccV × Cnt → AM (AccV × Cnt)
  | 0, _, _, _, _ => throw "relevance annotator: depth budget exhausted"
  | fuel + 1, d, t, e, (acc, cnt) => do
    let acc := { acc with nodes := acc.nodes + 1 }
    if acc.nodes > nodeBudget then throw "relevance annotator: node budget exhausted"
    match t, e with
    | .lam b _ body, .lam kty kbody _ => do
      let (r0, g) ← classifyTypeV v k d kty
      let cnt := cnt.note v 0 g fun _ => kty
      let r := honourErased b.contract r0
      let kty' ← k.annotate d kty
      let kb := kbody.instantiate1 (.fvar d kty')
      let pw ← if v.noPw then pure .never else k.propWhenOf (d + 1) kb
      walkV v p k fuel (d + 1) body kb ({ acc with tags := acc.tags.push (.lam r pw) }, cnt)
    | .app f a _ _, .app kf ka => do
      let (acc, cnt) ← walkV v p k fuel d f kf (acc, cnt)
      let (r, g, kt) ← classifyTermV v k d ka
      let cnt := cnt.note v 1 g fun _ => kt
      let (head, args) := Term.spine t
      let r := if erasedAt p head (args.length - 1) then honourErased .erased r else r
      let acc := { acc with tags := acc.tags.push (.arg r) }
      if r.alwaysIrr then pure (acc, cnt) else walkV v p k fuel d a ka (acc, cnt)
    | .letE c _ _ val body, .letE kty kv kbody _ => do
      let (r0, g) ← classifyTypeV v k d kty
      let cnt := cnt.note v 2 g fun _ => kty
      let r := honourErased c.binder r0
      let acc := { acc with tags := acc.tags.push (.letE r) }
      let (acc, cnt) ← if r.alwaysIrr then pure (acc, cnt) else walkV v p k fuel d val kv (acc, cnt)
      walkV v p k fuel d body (kbody.instantiate1 kv) (acc, cnt)
    | .proj s _ e', .proj _ _ kv => walkV v p k fuel d e' kv ({ acc with projs := acc.projs.push s }, cnt)
    | .const c _, .const .. => pure ({ acc with refs := acc.refs.push c }, cnt)
    | .var _, _ => pure (acc, cnt)
    | .natLit _, .lit .. | .strLit _, .lit .. | .sort _, .sort .. | .pi .., .forallE .. => pure (acc, cnt)
    | _, _ => throw s!"relevance annotator: a Src {srcHead t} node meets a kernel {kHead e} node"

def constRelV (v : V) (p : Program) (k : Ctx) (c : CId) (ty : KTerm) (cnt : Cnt) : AM (ConstRel × Cnt) := do
  let (result, g) ← classifyTypeV v k 0 ty
  let mut cnt := cnt.note v 3 g fun _ => ty
  let written := ((p.decl? c).map fun d => d.type.pis.1.map (·.1.contract)).getD []
  let mut cur := ty
  let mut d := 0
  let mut params := #[]
  for _ in [0:4096] do
    match cur with
    | .forallE dom body _ =>
      let (r, g) ← classifyTypeV v k d dom
      cnt := cnt.note v 3 g fun _ => dom
      params := params.push (match written[params.size]? with
        | some contract => honourErased contract r
        | none => r)
      let dom' ← k.annotate d dom
      cur := body.instantiate1 (.fvar d dom')
      d := d + 1
    | _ => break
  return ({ result, params := params.toList }, cnt)

def ctorRelV (v : V) (k : Ctx) (np nf : Nat) (ty : KTerm) (cnt : Cnt) : AM (CtorRel × Cnt) := do
  let mut cur := ty
  let mut d := 0
  let mut cnt := cnt
  for _ in [0:np] do
    let some (_, b) ← k.openPi d cur | throw "relevance annotator: constructor parameters"
    cur := b
    d := d + 1
  let mut fields := #[]
  for _ in [0:nf] do
    let some (dom, b) ← k.openPi d cur | throw "relevance annotator: constructor fields"
    let (r, g) ← classifyTypeV v k d dom
    cnt := cnt.note v 4 g fun _ => dom
    fields := fields.push (FieldClass.ofRel r)
    cur := b
    d := d + 1
  return ({ fields := fields.toList }, cnt)

def annotateRunV (v : V) (p : Program) (rd : Reading) (core : Ix.Kernel.Cached.CoreFnsI .anon) :
    AM (Ann × Cnt) := do
  let n := p.size
  let mut cnt : Cnt := {}
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
    if v.reset then set ({} : CS)
    let some info := rd.info? c | throw s!"relevance annotator: constant {c} has no kernel declaration"
    let lps := info.cv.levelParams
    let kc : Ctx := { core, back := backOf lps }
    let (cr, cnt') ← constRelV v p kc c info.cv.type cnt
    cnt := cnt'
    consts := consts.set! c (some cr)
    match p.decl? c with
    | some (.ctor ..) => ctorQueue := ctorQueue.push c
    | some (.recr _ _ _ _ _ _ _ ind _ _) => ctorQueue := ctorQueue ++ ctorsOf p ind
    | _ => pure ()
    for key in p.runtimeKeys c do
      let some t := p.termOf key | throw "relevance annotator: missing runtime term"
      let (e, lps) ← (kernelTermOf p rd key t : Except String _)
      let (acc, cnt') ← walkV v p { core, back := backOf lps } depthBudget 0 t e ({}, cnt)
      cnt := cnt'
      nodes := nodes.push (key, acc.tags)
      queue := queue ++ acc.refs
      for s in acc.projs do ctorQueue := ctorQueue ++ ctorsOf p s
    queue := queue ++ (p.runtimeRefs c).toArray.map (·.1)
  for c in ctorQueue do
    if (ctors[c]?).join.isNone then
      if v.reset then set ({} : CS)
      let some (.ctor cv np nf) := rd.info? c
        | throw s!"relevance annotator: constant {c} is not a constructor in the kernel's reading"
      let (cr, cnt') ← ctorRelV v { core, back := backOf cv.levelParams } np nf cv.type cnt
      cnt := cnt'
      ctors := ctors.set! c (some cr)
  return ({ consts := NatMap.ofOptions consts.toList, ctors := NatMap.ofOptions ctors.toList
            nodes := nodes.toList.map fun (key, tags) => (key, tags.toList) }, cnt)

def annotateV (v : V) (fe : Ix.Kernel.FEnv .anon) (rd : Reading) (p : Program) :
    Except String (Ann × Cnt × Nat) :=
  match (annotateRunV v p rd (coreOf fe)).run {} with
  | .ok ((ann, cnt), s) => .ok (ann, cnt, memoSize s)
  | .error e => .error s!"relevance annotator (kernel): {e}"

def timeMs {α : Type} (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0).toFloat / 1e6)

def fmt (x : Float) : String := toString (Float.round (x * 10) / 10)

def stagea (clo eqs : System.FilePath) (root : String) (cert : System.FilePath)
    (variants : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile clo
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let (inp, ti) ← timeMs fun _ => Recheck.ingress bytes json [root]
  let inp ← match inp with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"ingress: {(e.render).take 300}")
  IO.println s!"ingress {fmt ti} ms"
  let text ← IO.FS.readFile cert
  let (zc, tc) ← timeMs fun _ => Recheck.Cert.ofText text
  let zc ← match zc with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"Cert.ofText: {(e.render).take 300}")
  IO.println s!"Cert.ofText {fmt tc} ms"
  let cfg := Recheck.Config.forInput {} inp
  let (tab, tt) ← timeMs fun _ => Src.Table.ofCert cfg.table inp.program zc.table
  let table ← match tab with
    | .ok t => pure t
    | .error _ => throw (IO.userError "Table.ofCert refused")
  IO.println s!"Table.ofCert {fmt tt} ms"
  let p := { inp.program with table }
  let k := inp.kernel
  let (a0, ta) ← timeMs fun _ => annotate k.fe k.rd p
  let a0 ← IO.ofExcept a0
  IO.println s!"production annotate {fmt ta} ms; equals the certificate's: {a0.eqb zc.relevance}"
  let (r, tr) ← timeMs fun _ => checkReachedTypes k.rd p a0
  IO.println s!"production checkReachedTypes {fmt tr} ms ({(r.toBool)})"
  let (tot, tw) ← timeMs fun _ => Recheck.checkCanonicalRelevance cfg inp zc.table zc.relevance
  IO.println s!"production checkCanonicalRelevance {fmt tw} ms ({tot})"
  for name in variants do
    let v : V := match name with
      | "noretain" => { noRetain := true }
      | "reset" => { reset := true }
      | "nopw" => { noPw := true }
      | "instr" => { instr := true }
      | "noretain-instr" => { noRetain := true, instr := true }
      | "noretain-nopw" => { noRetain := true, noPw := true }
      | _ => {}
    let (res, t) ← timeMs fun _ => annotateV v k.fe k.rd p
    match res with
    | .error e => IO.println s!"{name}: REFUSED {fmt t} ms: {e.take 300}"
    | .ok (a, cnt, ms) =>
      IO.println s!"{name}: {fmt t} ms; equals production's: {a.eqb a0}; final memo entries {ms}"
      if v.instr then
        for i in [0:5] do
          IO.println s!"  site {i}: sortCond calls {cnt.calls[i]!}, grew the memo {cnt.grew[i]!}"
          for x in cnt.examples[i]! do IO.println s!"    {x}"
  return 0

end IxCCTests.KernelFront.ProbeH11

def main (args : List String) : IO UInt32 :=
  match args with
  | "stagea" :: clo :: eqs :: root :: cert :: variants =>
    IxCCTests.KernelFront.ProbeH11.stagea clo eqs root cert variants
  | _ => do
    IO.eprintln "usage: probe-h11 stagea CLOSURE EQS ROOT CERT [copy|noretain|reset|nopw|instr|noretain-instr]..."
    return 2
