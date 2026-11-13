module

public import IxC.Resource.Oracle

/-!
# The mode checker (uncertified)

`check lim env s` decides, for the run program of a subject, whether every
seed's run can reach none of `runR`'s four violations: it **accepts**,
**refuses** with a witness (the constant and the event it could not exclude), or
**declines** when a limit (its steps, its depth, the class oracle's kernel fuel)
runs out. Nothing about it is proved: its soundness, `CheckSound` (accept gives
`ModeSafe`), is left to prove.

* **Fast path.** A closure whose every record carries only default modes, with
  no run table, is accepted without reading it (`DefaultOk`).
* **Otherwise** it reads, with the kernel as class oracle (`oracleClassifier`),
  every constant of a record with a non-default mode and every constant that
  references one, with the interfaces they call, and runs an abstract
  interpretation of `runR` on each run body: per binding whether it is live and
  unique, shared or consumed, the regions a value may be confined to, the
  bindings a value may alias, whether a once binding has been called, whether a
  closure may only be called once; alternatives joined; skeletons compared at
  every flow (`Skel.admits`). Any event it cannot exclude is a refusal.

The checker is first order: explicit fuel and step counts, arrays and lists,
modes and classes read positionally from the run program, the kernel asked
mode-free questions only through the class oracle.
-/

@[expose] public section

namespace IxC.Resource

open Ixon

/-! ## Abstract values and state -/

inductive Own where
  | uniq
  | shared
  deriving BEq, DecidableEq, Repr, Inhabited

/-- What the checker knows of a value: its class; whether it is unique while
the bindings it aliases (`deps`) are live; the regions it may be confined to;
its mode skeleton; whether it is a closure that may be called only once; the
binding it was read from. -/
structure AVal where
  cls : Cls := .val
  own : Own := .shared
  deps : List Nat := []
  regs : List Nat := []
  skel : Skel := .unknown
  onceOnly : Bool := false
  src : Option Nat := none
  deriving Inhabited

/-- A binding's state: live and unique, possibly shared, or consumed. -/
inductive BSt where
  | live
  | shared
  | dead
  deriving BEq, DecidableEq, Inhabited

structure ABnd where
  id : Nat
  mode : BinderMode
  val : AVal
  deriving Inhabited

/-- The checker's state: per binding id its state, whether it is a once binding
and whether that has been called; the open regions (region 1 is the caller's,
always open); the steps left. -/
structure CSt where
  st : Array BSt := #[]
  once : Array Bool := #[]
  spent : Array Bool := #[]
  regions : List Nat := [1]
  nextRegion : Nat := 2
  steps : Nat := 0

inductive Halt where
  | refuse (w : String)
  | decline (w : String)

abbrev CM := StateT CSt (Except Halt)

def refuseM {α : Type} (w : String) : CM α := throw (.refuse w)
def declineM {α : Type} (w : String) : CM α := throw (.decline w)

def tick : CM Unit := do
  let s ← get
  if s.steps == 0 then throw (.decline "the checker's step limit")
  set { s with steps := s.steps - 1 }

def stOf (id : Nat) : CM BSt := do pure ((← get).st[id]?.getD .dead)
def setSt (id : Nat) (b : BSt) : CM Unit := modify fun s => { s with st := s.st.set! id b }
def isOnceBnd (id : Nat) : CM Bool := do pure ((← get).once[id]?.getD false)
def isSpent (id : Nat) : CM Bool := do pure ((← get).spent[id]?.getD false)
def markSpent (id : Nat) : CM Unit := modify fun s => { s with spent := s.spent.set! id true }

def newBnd (v : AVal) (once : Bool) : CM Nat := do
  let s ← get
  set { s with st := s.st.push (if v.own == Own.uniq then BSt.live else BSt.shared),
               once := s.once.push once, spent := s.spent.push false }
  pure s.st.size

def openReg : CM Nat := do
  let s ← get
  set { s with nextRegion := s.nextRegion + 1, regions := s.nextRegion :: s.regions }
  pure s.nextRegion

def closeReg (r : Nat) : CM Unit := modify fun s => { s with regions := s.regions.filter (· != r) }

def innermost : CM Nat := do pure ((← get).regions.headD 1)

/-! ## Flows -/

/-- A value is usable while no binding it aliases has been consumed. -/
def valid (v : AVal) (w : String) : CM Unit := do
  for d in v.deps do
    if (← stOf d) == BSt.dead then refuseM s!"revokedUse: {w}, after a unique transfer"

def readVar (env : List ABnd) (i : Nat) : CM AVal := do
  let some b := env[i]? | refuseM "a variable out of scope"
  if b.mode == .erased then refuseM "erasedRead: an erased binding is read"
  let v : AVal := { b.val with deps := b.id :: b.val.deps.filter (· != b.id), src := some b.id }
  valid v "a binding is read"
  pure v

/-- Whether a value may be transferred: nothing to transfer for an immediate, a
leaf or an irrelevant value; otherwise unique, with every binding it aliases live. -/
def isUniq (v : AVal) : CM Bool := do
  if v.cls != .val then return true
  if v.own != Own.uniq then return false
  for d in v.deps do
    unless (← stOf d) == BSt.live do return false
  return true

/-- Where a value goes. -/
inductive Dest where
  /-- it may be retained: what it aliases becomes shared -/
  | share
  /-- lent, not retained -/
  | lend
  /-- transferred uniquely (into a borrowed binder or not) -/
  | uniq (borrowed : Bool)
  /-- bound at a once binder -/
  | once

/-- Not a value read from a once binding (`Rules.repaired`'s `NotOnceSrc`). -/
def notOnceSrc (v : AVal) (w : String) : CM Unit := do
  if let some x := v.src then
    if ← isOnceBnd x then refuseM s!"onceReentry: a once binding where it may be called again: {w}"

/-- A once-only value read from a binding moves out of it: the binding is
consumed (`Rules.repaired`'s `killSrc`). -/
def killSrc (v : AVal) : CM Unit := do
  if v.onceOnly then
    if let some x := v.src then setSt x BSt.dead

/-- **A flow** of `v` to a position of skeleton `exp`. A once binding passed on
counts as called. A once-only value, or a value read from a once binding, goes
only to a `once` position: lent or retained, it may be called again (findings
10 and 11); a once-only value read from a binding is moved out of it. -/
def flowTo (d : Dest) (exp : Skel) (v : AVal) (w : String) : CM Unit := do
  valid v w
  unless exp.admits v.skel do refuseM s!"mode skeletons differ: {w}"
  match d with
  | .once => do
    -- a once binding already called or passed on is not passed on again (repair T): each once
    -- position wraps its own once view around the same target
    for x in v.deps do
      if (← isOnceBnd x) && (← isSpent x) then
        refuseM s!"onceReentry: a once binding passed on after it was called or passed on: {w}"
  | _ => do
    if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
    notOnceSrc v w
  for x in v.deps do
    if ← isOnceBnd x then markSpent x
  match d with
  | .lend => pure ()
  | .share => do
    if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
    if v.cls == .val then
      for x in v.deps do
        if (← stOf x) == BSt.live then setSt x BSt.shared
  | .once => do
    if v.cls == .val then
      for x in v.deps do
        if (← stOf x) == BSt.live then setSt x BSt.shared
  | .uniq b => do
    if v.onceOnly then refuseM s!"onceReentry: a once-only closure given away: {w}"
    if v.cls == .val then
      unless ← isUniq v do refuseM s!"revokedUse: a value that may be shared, at a unique position: {w}"
      if !b && !v.regs.isEmpty then refuseM s!"borrowEscape: a borrowed value given away: {w}"
      for x in v.deps do setSt x BSt.dead
  killSrc v

/-- A callee's interface. -/
structure Iface where
  params : Array Param
  res : ResultMode
  resCls : Cls
  resSkel : Skel

def ifaceOf? : RunDef → Option Iface
  | .body ps r rc rs _ => some ⟨ps, r, rc, rs⟩
  | .extern ps r rc rs => some ⟨ps, r, rc, rs⟩
  | .stuck ps r rc rs => some ⟨ps, r, rc, rs⟩
  | _ => none

/-- Where an argument at parameter `p` goes: a plain parameter lends when the
result is no cell (it cannot retain the argument). -/
def destOf (p : Param) (lendPlain : Bool) : Dest :=
  if p.mode == .erased then .lend
  else if p.mode.isUnique then .uniq p.mode.isBorrowed
  else if p.mode.usage == .once then .once
  else if p.mode.isBorrowed then .lend
  else if lendPlain then .lend else .share

/-- **A call's result**, the arguments bound at the parameters in order. A
`shared` result of class `leaf` may be any argument's leaf, or a leaf a closure
or a cell among the arguments holds with the confinement it was stored with, so
it carries every argument's regions. (As landed, an argument at a parameter
whose type no leaf inhabits, `Param.noLeaf`, gave it none: unsound for `Nat`
itself, for function types and under an absurd hypothesis, findings 1 to 3.) -/
def callResult (ifc : Iface) (avs : Array (Option AVal)) (w : String) : CM AVal := do
  let lendPlain := ifc.resCls != .val
  let mut deps : List Nat := []
  let mut sdeps : List Nat := []
  let mut regs : List Nat := []
  for (p, i) in ifc.params.zipIdx do
    match avs[i]? with
    | some (some a) =>
      let d := destOf p lendPlain
      flowTo d p.skel a w
      if a.cls == .val then deps := natUnion deps a.deps
      regs := natUnion regs a.regs
      match d with
      | .share => sdeps := natUnion sdeps a.deps
      | _ => pure ()
    | _ => pure ()
  let base : AVal := { cls := ifc.resCls, skel := ifc.resSkel }
  if ifc.resCls == .irr || ifc.resCls == .imm then return base
  let inner ← innermost
  match ifc.res with
  | .unique => pure { base with own := .uniq }
  | .uniqueBorrowed => pure { base with own := .uniq, deps, regs := natUnion regs [inner] }
  | .borrowed => pure { base with deps, regs := natUnion regs [inner] }
  | .shared =>
    if ifc.resCls == .leaf then pure { base with regs }
    else pure { base with deps := sdeps, regs }

/-- A partial application: its arguments at unique parameters transferred now
(`captureTransfers`), which makes it callable once; the others retained. -/
def papVal (ifc : Iface) (avs : Array (Option AVal)) (w : String) : CM AVal := do
  let mut deps : List Nat := []
  let mut regs : List Nat := []
  let mut once := false
  for (p, i) in ifc.params.zipIdx do
    match avs[i]? with
    | some (some a) =>
      if captureTransfers p.mode then
        flowTo (.uniq p.mode.isBorrowed) p.skel a w
        once := true
      else
        flowTo .share p.skel a w
        deps := natUnion deps a.deps
      regs := natUnion regs a.regs
    | _ => pure ()
  pure { cls := .val, deps, regs, onceOnly := once,
         skel := ifaceSkel (ifc.params.toList.drop avs.size) ifc.res ifc.resSkel }

/-- Applying a function value to one argument: by its skeleton's arrow (an
unknown skeleton is a mode-free arrow, since only mode-free values flow there).
A once binding called twice is refused; a once-only closure is consumed. The
result may hold what the function value holds (a closure's captures, a partial
application's arguments) with the confinement they were stored with, so it
carries the function value's regions; at class `val` it may alias what the
function value aliases, and the argument whatever its destination (a partial
application retains even a lent argument). As landed the result was built
from the argument alone (finding 9). -/
def applyValue (f a : AVal) (c : Cls) (w : String) : CM AVal := do
  valid f w
  for x in f.deps do
    if ← isOnceBnd x then
      if ← isSpent x then refuseM s!"onceReentry: a once binding called a second time: {w}"
      markSpent x
  if f.onceOnly then
    if let some x := f.src then setSt x BSt.dead
  let (m, dom, res, cod) := match f.skel with
    | .arrow m d r cd => (m, d, r, cd)
    | _ => (BinderMode.many, Skel.unknown, ResultMode.shared, Skel.unknown)
  let p : Param := { mode := m, cls := a.cls, skel := dom }
  let ifc : Iface := { params := #[p], res := res, resCls := c, resSkel := cod }
  let r ← callResult ifc #[some a] w
  let regs := if c == .val || c == .leaf then natUnion r.regs f.regs else r.regs
  let deps := if c == .val then natUnion (natUnion r.deps f.deps) a.deps else r.deps
  pure { r with cls := c, regs, deps }

/-- A call of something the program does not define: arguments retained. -/
def unknownCall (avs : Array (Option AVal)) (c : Cls) : CM AVal := do
  let mut deps : List Nat := []
  let mut regs : List Nat := []
  for a in avs do
    if let some a := a then
      flowTo .share .unknown a "an argument of an unknown function"
      deps := natUnion deps a.deps
      regs := natUnion regs a.regs
  pure { cls := c, deps := (if c == .val then deps else []),
         regs := (if c == .irr || c == .imm then [] else regs), skel := .unknown }

/-- Binding a value at an inner binder (a `let`, a case field's binder) in
region `s`, as `bindAt` does, before the once rules of `bindInner`. A plain
binder aliases. -/
def bindInnerBase (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) : CM AVal := do
  match m with
  | .erased => pure { cls := .irr }
  | .unique | .uniqueBorrowed => do
    flowTo (.uniq m.isBorrowed) v.skel v w
    pure { cls, own := .uniq, regs := (if m.isBorrowed then natUnion v.regs [s] else []),
           skel := v.skel }
  | .borrowed => do valid v w; pure { v with cls, regs := natUnion v.regs [s], src := none }
  | .once => do flowTo .once v.skel v w; pure { v with cls, src := none }
  | .onceBorrowed => do
    flowTo .once v.skel v w
    pure { v with cls, regs := natUnion v.regs [s], src := none }
  | .many => do valid v w; pure { v with cls, src := none }

/-- Binding a value at an inner binder (`bindInnerBase`), with the once rules: a
value read from a once binding is bound only at a `once` binder (finding 11),
and a once-only value read from a binding moves out of it (finding 10: as
landed, `let h := g` left both `g` and `h` callable). `Rules.repaired`'s
`repairedBind`. -/
def bindInner (m : BinderMode) (cls : Cls) (v : AVal) (s : Nat) (w : String) : CM AVal := do
  if m.usage != .once then notOnceSrc v w
  let r ← bindInnerBase m cls v s w
  killSrc v
  pure r

/-- A parameter as its body sees it, in the call's region `s` (region 1 stands
for the caller's regions, which a lent argument may also be confined to). -/
def paramVal (p : Param) (s : Nat) : AVal :=
  match p.mode with
  | .erased => { cls := .irr }
  | .unique => { cls := p.cls, own := .uniq, skel := p.skel }
  | .uniqueBorrowed => { cls := p.cls, own := .uniq, regs := [s, 1], skel := p.skel }
  | .borrowed | .onceBorrowed => { cls := p.cls, regs := [s, 1], skel := p.skel }
  | .many | .once => { cls := p.cls, skel := p.skel }

/-- **The return rule** from region `s` at result mode `res`, as `ret`. -/
def retCheck (exp : Skel) (res : ResultMode) (s : Nat) (r : AVal) (w : String) : CM Unit := do
  valid r w
  unless exp.admits r.skel do refuseM s!"mode skeletons differ: {w}"
  if r.onceOnly then refuseM s!"onceReentry: a once-only closure returned: {w}"
  -- a once binding returned may be called again by whoever receives it (repair S)
  notOnceSrc r w
  if r.cls == .val || r.cls == .leaf then
    match res with
    | .shared => if r.regs.contains s then refuseM s!"borrowEscape: a borrowed value returned: {w}"
    | .unique => do
      if r.regs.contains s then refuseM s!"borrowEscape: a borrowed value returned: {w}"
      if r.cls == .val then
        unless ← isUniq r do refuseM s!"revokedUse: a value that may be shared, returned unique: {w}"
        unless r.regs.isEmpty do refuseM s!"borrowEscape: a borrowed value returned unique: {w}"
    | .borrowed => pure ()
    | .uniqueBorrowed => do
      if r.cls == .val then
        unless ← isUniq r do refuseM s!"revokedUse: a value that may be shared, returned unique: {w}"

/-- A saturated constructor application, as `construct`. -/
def anCtor (nP : Nat) (fields : Array Field) (avs : Array (Option AVal)) (c : Cls) : CM AVal := do
  if avs.size < nP + fields.size then
    let mut deps : List Nat := []
    let mut regs : List Nat := []
    for a in avs do
      if let some a := a then
        flowTo .share .unknown a "a constructor's partial application"
        deps := natUnion deps a.deps
        regs := natUnion regs a.regs
    return { cls := .val, deps, regs, skel := .unknown }
  let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
  if kept.isEmpty then return { cls := .imm }
  if (c == .imm || c == .leaf) && kept.size == 1 then
    match avs[nP + kept[0]!]? with
    | some (some v) => do
      valid v "a wrapper's field"
      return { v with cls := c, src := none }
    | _ => return { cls := c }
  let mut own := Own.uniq
  let mut deps : List Nat := []
  let mut regs : List Nat := []
  for i in kept do
    match avs[nP + i]?, fields[i]? with
    | some (some v), some f =>
      valid v "a constructor field"
      if v.onceOnly then refuseM "onceReentry: a once-only closure stored in a cell"
      unless Skel.unknown.admits v.skel do refuseM "mode skeletons differ: a moded closure stored in a cell"
      regs := natUnion regs v.regs
      if f.fmode == .shared then
        unless v.regs.isEmpty do refuseM "borrowEscape: a borrowed value stored in a @shared field"
        flowTo .share v.skel v "a shared field"
      else if v.cls == .val then
        -- a once binding stored in a cell can be read out and called again (repair Q)
        notOnceSrc v "a constructor field"
        unless ← isUniq v do own := .shared
        -- two inherited fields aliasing one binding: the cell holds a value twice, so it is no
        -- tree and its transfer reaches that value twice (finding 8)
        if v.deps.any deps.contains then own := .shared
        deps := natUnion deps v.deps
    | _, _ => pure ()
  pure { cls := c, own, deps, regs, skel := .unknown }

/-- A projection, as `runR`'s: an erased field is refused; a trivial wrapper is
its field; a `@shared` field or a leaf is a counted value of its own; any other
field aliases its container and shares its confinement. -/
def anProj (P : Prog) (s : Ref) (i : Nat) (v : AVal) (c : Cls) : CM AVal := do
  let fields : Array Field := match (P.ctorsOf s)[0]? with
    | some ctor => match P.ctorOf? ctor with
      | some (_, _, _, fs) => fs
      | none => #[]
    | none => #[]
  let some f := fields[i]? | return { cls := c }
  if f.mode == .erased then refuseM "erasedRead: an erased field is projected"
  if f.cls == .irr || c == .irr then return { cls := .irr }
  if c == .imm then return { cls := .imm }
  if v.cls != .val then return { v with cls := c, src := none }
  if f.fmode == .shared then return { cls := c, skel := .unknown }
  -- a leaf: read out of a cell it is unconfined, but the container may be a
  -- trivial wrapper represented by it
  if c == .leaf then return { cls := c, regs := v.regs, skel := .unknown }
  pure { cls := c, deps := v.deps, regs := v.regs, skel := .unknown }

/-- The value of field `i` of a case's constructor, whether it is erased, and
whether it was read out of a cell (so a leaf or an immediate bound from it is
not confined by the cell, as `readOut`). -/
def caseField (P : Prog) (k : CaseInfo) (fields : Array Field) (mv : AVal) (consuming : Bool)
    (i : Nat) : AVal × Bool × Bool :=
  if some k.ind == P.nat then ({ cls := natClass }, false, false)
  else match fields[i]? with
    | none => ({ cls := .irr }, false, false)
    | some f =>
      if f.mode == .erased then ({ cls := .irr }, true, false)
      else if f.cls == .irr then ({ cls := .irr }, false, false)
      else if mv.cls != .val && P.wrapperField? k.ind == some i then ({ mv with src := none }, false, false)
      else if f.cls != .val then ({ cls := f.cls }, false, false)
      else if f.fmode == .shared then ({ cls := .val }, false, false)
      else
        -- read out of a cell, unless the inductive may be a trivial wrapper
        let fromCell := (P.ctorsOf k.ind).size != 1
        if consuming then ({ cls := .val, own := .uniq, regs := mv.regs }, false, fromCell)
        else ({ cls := .val, deps := mv.deps, regs := mv.regs }, false, fromCell)

/-! ## The abstract run -/

mutual

def anTerm (P : Prog) : Nat → List ABnd → Term → CM AVal
  | 0, _, _ => declineM "the checker's depth limit"
  | n + 1, env, t => do
    tick
    match t with
    | .irr => pure { cls := .irr }
    | .var i c => do
      let v ← readVar env i
      pure { v with cls := c }
    | .natLit _ => pure { cls := natClass }
    | .strLit _ => pure { cls := .val, skel := .data }
    | .const r c => anCall P n env r #[] c
    | .app _ _ c => do
      let (h, args) := termSpine t
      match h with
      | .const r _ => anCall P n env r args c
      | _ => do
        -- every argument, then the applications, as `runR`'s `spine` and `applyAll` (finding
        -- 13: as landed each argument was judged after the applications before it)
        let mut f ← anTerm P n env h
        let mut avs : Array AVal := #[]
        for a in args do
          avs := avs.push (← anTerm P n env a)
        for (av, i) in avs.zipIdx do
          f ← applyValue f av (if i + 1 == avs.size then c else .val) "an application"
        pure f
    | .lam p res rc fvs body => anLam P n env p res rc fvs body
    | .letE m d v b => do
      match m with
      | .value .erased => do
        let id ← newBnd { cls := .irr } false
        anTerm P n ({ id, mode := .erased, val := { cls := .irr } } :: env) b
      | _ => do
        let x ← anTerm P n env v
        let s ← openReg
        let bm := m.binderMode
        let bv ← bindInner bm d x s "a let"
        let id ← newBnd bv (bm.usage == .once)
        let r ← anTerm P n ({ id, mode := bm, val := bv } :: env) b
        valid r "a let's value"
        if r.regs.contains s then refuseM "borrowEscape: a value borrowed by a let outlives it"
        closeReg s
        pure r
    | .proj s i e c => do
      let v ← anTerm P n env e
      valid v "a projection"
      anProj P s i v c
    | .case k mj alts ex c => anCase P n env k mj alts ex c

def anCall (P : Prog) : Nat → List ABnd → Ref → Array Term → Cls → CM AVal
  | 0, _, _, _, _ => declineM "the checker's depth limit"
  | n + 1, env, r, args, c => do
    let d? := P.find? r
    let mut avs : Array (Option AVal) := #[]
    for (a, i) in args.zipIdx do
      let skip := match d? with
        | some d => erasedAt d i
        | none => false
      avs := avs.push (← if skip then pure none else some <$> anTerm P n env a)
    match d? with
    | some (.ind _) => pure { cls := .irr }
    | some (.ctor _ _ nP fields) => anCtor nP fields avs c
    | some (.prim p) => do
      for a in avs do
        if let some a := a then valid a "a primitive's argument"
      -- a partial application holds its arguments as they were (`makePap`), so it carries
      -- their regions and aliases (finding 12: as landed it had none)
      if avs.size < p.arity then
        let regs := avs.foldl (fun r a => match a with | some a => natUnion r a.regs | none => r) []
        let deps := avs.foldl (fun r a => match a with | some a => natUnion r a.deps | none => r) []
        pure { cls := .val, skel := .unknown, regs, deps }
      else pure { cls := c }
    | some d =>
      match ifaceOf? d with
      | some ifc =>
        let k := ifc.params.size
        if avs.size < k then papVal ifc avs "a partial application"
        else do
          let r0 ← if k == 0 then pure ({ cls := ifc.resCls, skel := ifc.resSkel } : AVal)
            else callResult ifc (avs.extract 0 k) "a call"
          let mut f := r0
          for (a, i) in (avs.extract k avs.size).zipIdx do
            match a with
            | some av => f ← applyValue f av (if k + i + 1 == avs.size then c else .val) "an application"
            | none => pure ()
          pure { f with cls := c }
      | none => unknownCall avs c
    | none => unknownCall avs c

/-- A closure: its captures read, the unique ones transferred into it; its body
checked as a call of its own, from a copy of the state; once-only if the body
consumes a capture. -/
def anLam (P : Prog) : Nat → List ABnd → Param → ResultMode → Cls → Array Nat → Term → CM AVal
  | 0, _, _, _, _, _, _ => declineM "the checker's depth limit"
  | n + 1, env, p, res, rc, fvs, body => do
    let mut deps : List Nat := []
    let mut regs : List Nat := []
    let mut owned : List Nat := []
    for i in fvs.toList do
      let some b := env[i]? | refuseM "a capture out of scope"
      let v ← readVar env i
      if captureTransfers b.mode then
        flowTo (.uniq b.mode.isBorrowed) v.skel v "a capture"
        owned := b.id :: owned
      else
        flowTo .share v.skel v "a capture"
        deps := natUnion deps v.deps
      regs := natUnion regs v.regs
    let saved ← get
    for x in owned do setSt x BSt.live
    let s ← openReg
    let pv := paramVal p s
    let pid ← newBnd pv (p.mode.usage == .once)
    let r ← anTerm P n ({ id := pid, mode := p.mode, val := pv } :: env) body
    retCheck r.skel res s { r with cls := rc } "a closure's result"
    let mut consumed := false
    for x in owned do
      if (← stOf x) == BSt.dead then consumed := true
    let after ← get
    set { saved with steps := after.steps, nextRegion := after.nextRegion }
    pure { cls := .val, deps, regs, onceOnly := consumed, skel := .arrow p.mode p.skel res r.skel }

/-- A case: a consuming match on a unique binding; each alternative from the
same state, the states joined; the alternatives' results joined. -/
def anCase (P : Prog) :
    Nat → List ABnd → CaseInfo → Term → Array Term → Array Term → Cls → CM AVal
  | 0, _, _, _, _, _, _ => declineM "the checker's depth limit"
  | n + 1, env, k, mj, alts, ex, c => do
    let (mv, consuming) ← match mj with
      | .var j mc => do
        let some b := env[j]? | refuseM "a variable out of scope"
        let v ← readVar env j
        if b.mode.isUnique && mc == .val then
          flowTo (.uniq b.mode.isBorrowed) v.skel v "a consuming match"
          pure ({ v with own := .uniq, deps := [], cls := mc, src := none }, true)
        else pure ({ v with cls := mc }, false)
      | t => do pure ((← anTerm P n env t), false)
    let pre ← get
    let ctors := P.ctorsOf k.ind
    let mut posts : Array CSt := #[]
    let mut results : Array AVal := #[]
    let mut steps := pre.steps
    let mut nextRegion := pre.nextRegion
    for (ca, j) in k.alts.zipIdx do
      set { pre with steps, nextRegion }
      let fields : Array Field := match ctors[j]? with
        | some ctor => match P.ctorOf? ctor with
          | some (_, _, _, fs) => fs
          | none => #[]
        | none => #[]
      let args := ca.args.toList.map fun fa => match fa with
        | .field i => caseField P k fields mv consuming i
        | .irr => (({ cls := .irr } : AVal), false, false)
        | .unit => (({ cls := .imm } : AVal), false, false)
      let some alt := alts[j]? | continue
      let r ← anAlt P n env alt args
      -- the join drops the binding a result was read from, so a once binding cannot leave an
      -- alternative (repair R; judged here, where a once binding made inside it is still known)
      notOnceSrc r "a case alternative's result"
      results := results.push { r with deps := r.deps.filter (· < pre.st.size) }
      let post ← get
      posts := posts.push post
      steps := post.steps
      nextRegion := post.nextRegion
    let mut st := pre.st
    let mut spent := pre.spent
    for post in posts do
      for i in [0:pre.st.size] do
        let a := st[i]!
        let b := post.st[i]!
        st := st.set! i (if a == BSt.dead || b == BSt.dead then BSt.dead
          else if a == BSt.shared || b == BSt.shared then BSt.shared else BSt.live)
        if post.spent[i]! then spent := spent.set! i true
    set { pre with st, spent, steps, nextRegion }
    let some r0 := results[0]? | return { cls := c }
    let mut r := r0
    for x in results do
      unless x.skel.admits r.skel do refuseM "mode skeletons differ between a case's alternatives"
      r := { r with own := (if r.own == Own.uniq && x.own == Own.uniq then Own.uniq else Own.shared),
                    deps := natUnion r.deps x.deps, regs := natUnion r.regs x.regs,
                    onceOnly := r.onceOnly || x.onceOnly }
    r := { r with cls := c, src := none }
    -- the extra arguments, then the applications, all but the last at class `val`, as
    -- `runR`'s `applyAll` (finding 16: as landed each was judged in turn, at the case's class)
    let mut avs : Array AVal := #[]
    for e in ex do
      avs := avs.push (← anTerm P n env e)
    for (av, i) in avs.zipIdx do
      r ← applyValue r av (if i + 1 == avs.size then c else .val) "an application"
    pure r

/-- An alternative applied to its fields, as `applyAlt`: a λ telescope binds
them in place; an erased field reaching anything else is an erased read. -/
def anAlt (P : Prog) : Nat → List ABnd → Term → List (AVal × Bool × Bool) → CM AVal
  | 0, _, _, _ => declineM "the checker's depth limit"
  | n + 1, env, t, [] => anTerm P n env t
  | n + 1, env, t, (a0, er, fromCell) :: rest => do
    match t with
    | .lam p res rc _ body => do
      let a := if fromCell && p.cls != .val then { a0 with deps := [], regs := [] } else a0
      let s ← openReg
      let (mode, bv) ← if er then pure (BinderMode.erased, ({ cls := .irr } : AVal)) else do
        unless p.skel.admits a.skel do refuseM "mode skeletons differ: a case field's binder"
        pure (p.mode, ← bindInner p.mode p.cls a s "a case field's binder")
      let id ← newBnd bv (mode.usage == .once)
      let r ← anAlt P n ({ id, mode, val := bv } :: env) body rest
      retCheck r.skel res s r "a case alternative"
      closeReg s
      pure { r with cls := rc }
    | _ => do
      if ((a0, er, fromCell) :: rest).any (·.2.1) then
        refuseM "erasedRead: an erased field passed to an alternative that is not a λ for it"
      let mut f ← anTerm P n env t
      for (av, _, _) in (a0, er, fromCell) :: rest do
        f ← applyValue f av .val "an alternative"
      pure f

end

/-- **One run body**, from its parameters as `InputsOk` gives them. -/
def anDef (P : Prog) (fuel : Nat) (params : Array Param) (res : ResultMode) (rc : Cls) (rs : Skel)
    (body : Term) : CM Unit := do
  let s ← openReg
  let mut env : List ABnd := []
  for p in params do
    let v := paramVal p s
    let id ← newBnd v (p.mode.usage == .once)
    env := { id, mode := p.mode, val := v } :: env
  let r ← anTerm P fuel env body
  retCheck rs res s { r with cls := rc } "the result"

/-! ## The entry -/

/-- The checker's limits. -/
structure Limits where
  steps : Nat := 1 <<< 22
  depth : Nat := 1 <<< 12
  oracle : OracleLimits := {}
  deriving Inhabited

/-- **The verdict**: accepted (how many run bodies were checked, and whether by
the fast path), refused at a constant with a witness, or declined at a limit. -/
inductive Verdict where
  | accept (checked : Nat) (fastPath : Bool)
  | refuse (at_ : String) (witness : String)
  | decline (reason : String)
  deriving Inhabited

def Verdict.isAccept : Verdict → Bool
  | .accept .. => true
  | _ => false

/-- The constants a run term names. -/
def termRefs : Nat → Term → List Ref
  | 0, _ => []
  | n + 1, t =>
    match t with
    | .const r _ => [r]
    | .app f a _ => termRefs n f ++ termRefs n a
    | .lam _ _ _ _ b => termRefs n b
    | .letE _ _ v b => termRefs n v ++ termRefs n b
    | .proj s _ e _ => s :: termRefs n e
    | .case k mj alts ex _ =>
      k.ind :: (termRefs n mj ++ alts.toList.flatMap (termRefs n) ++ ex.toList.flatMap (termRefs n))
    | _ => []

/-- A reading failure as a verdict: the oracle's declines decline, anything
else (malformed modes, a telescope mismatch, a bad run table) refuses. -/
def readFailure (where_ e : String) : Verdict :=
  if e.startsWith "decline:" then .decline s!"{where_}: {e}" else .refuse where_ s!"the reading fails: {e}"

def refName (r : Ref) : String := (repr r).pretty

/-- Check run bodies, in order: the first refusal or decline stops. -/
def checkBodies (lim : Limits) (P : Prog) (rs : List Ref) : Verdict := Id.run do
  let mut n := 0
  for r in rs do
    let some (.body params res rc rsk body) := P.find? r | continue
    match (anDef P lim.depth params res rc rsk body).run' { steps := lim.steps } with
    | .ok () => n := n + 1
    | .error (.refuse w) => return .refuse (refName r) w
    | .error (.decline w) => return .decline s!"{refName r}: {w}"
  return .accept n false

/-- **The fast path's test**: every record of the subject's closure carries only
default modes, and there is no run table (an error: a record's modes are
malformed). -/
def allDefault (s : Subject) : Except String Bool := do
  for a in closureOf s.store (s.seeds ++ s.runTable.toList ++ s.externs) do
    let some c := s.store a | continue
    unless (← recordDefault c) do return false
  return s.runTable.isNone

/-- **The mode checker** (uncertified): the subject's closure, its records' modes,
the kernel environment `env` its typing installed (for the class oracle). -/
def check (lim : Limits) (env : Ix.Kernel.Env .anon) (s : Subject) : Verdict := Id.run do
  let rd := Reading.make s
  if let .error e := rd.complete then return .refuse "the closure" e
  -- the fast path: every record's modes default, and no run table
  let mut nonDefault : Array Address := #[]
  for a in rd.closure do
    let some c := s.store a | continue
    match recordDefault c with
    | .ok true => pure ()
    | .ok false => nonDefault := nonDefault.push a
    | .error e => return .refuse s!"record {a}" s!"malformed modes: {e}"
  if nonDefault.isEmpty && s.runTable.isNone then return .accept 0 true
  let cl := oracleClassifier env (ctorShapes rd) lim.oracle
  let rt ← match rd.runTable cl with
    | .ok rt => pure rt
    | .error e => return readFailure "the run table" e
  -- a reference touches a non-default record directly or through its block
  let touches (p : Address) : Bool :=
    nonDefault.contains p || match s.store p with
      | some pc => match pc.info with
        | .dPrj x => nonDefault.contains x.block
        | .iPrj x => nonDefault.contains x.block
        | .cPrj x => nonDefault.contains x.block
        | .rPrj x => nonDefault.contains x.block
        | _ => false
      | none => false
  let mut toCheck : Array Ref := #[]
  for a in rd.closure do
    let some c := s.store a | continue
    if touches a || c.refs.any touches || rt.any (fun (f, _) => f.block == a) then
      for r in refsOf a c do toCheck := toCheck.push r
  -- their run definitions, then the interfaces they reach
  let mut defs : Array (Ref × RunDef) := #[]
  for r in toCheck do
    match rd.readDef cl rt true r with
    | .ok d => defs := defs.push (r, d)
    | .error e => return readFailure (refName r) e
  let mut todo : List Ref := []
  for (_, d) in defs do
    match d with
    | .body _ _ _ _ t => todo := todo ++ termRefs (1 <<< 20) t
    | .ind cs => todo := todo ++ cs.toList
    | .caseDef k => todo := todo ++ [k.ind]
    | _ => pure ()
  for _ in [0:1 <<< 20] do
    match todo with
    | [] => break
    | r :: rest =>
      todo := rest
      if defs.any (·.1 == r) then continue
      match rd.readDef cl rt false r with
      | .ok d =>
        defs := defs.push (r, d)
        match d with
        | .ind cs => todo := todo ++ cs.toList
        | .caseDef k => todo := todo ++ [k.ind]
        | .ctor ind .. => todo := todo ++ [ind]
        | _ => pure ()
      | .error e => return readFailure (refName r) e
  let P : Prog := { defs, nat := roleRef? s .nat }
  checkBodies lim P toCheck.toList

/-- **The checker's soundness**, to prove: whatever it accepts is mode-safe
(over the environment the subject's typing installs). The fast path rests on
`DefaultOk`, and on a closure whose modes are all default reading as a run
program (`Reads`) whenever the kernel reads it. -/
def CheckSound : Prop :=
  ∀ lim env s n fp, check lim env s = .accept n fp → ModeSafe env s

end IxC.Resource

end
