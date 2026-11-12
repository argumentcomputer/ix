module

public import IxC.Resource.Syntax

/-!
# `runR`: the reference evaluator, with its four monitors

Call by value, left to right, with explicit fuel. Values are immediates or
references to heap cells; a reference carries the capability it was issued
(`cap`) and the regions it is confined to (`taint`).

* **Uniqueness by revocation.** A unique transfer gives every cell of the
  value's ownership closure (`ownedSlots`) a fresh capability: every other
  reference to those cells dies. Using a dead reference is `revokedUse`.
* **Borrows as regions.** Entering a call, a closure, a `let` or a case
  alternative opens a region; a value bound at a borrowed binder is confined to
  it, and a value read out of a confined container is confined with it (a leaf
  or a `@shared` field excepted). A value confined to a region that is closing,
  returned or let-bound past it, is `borrowEscape`, and so is the unique transfer
  of a value confined to an open region, except into a borrowed binder.
* **Erasure.** Evaluating a binding of mode `erased`, or projecting an erased
  field, is `erasedRead`.
* **Once.** A value bound at a `once` binder is wrapped in a once view; calling
  it a second time is `onceReentry`.

Classes are checked where they are used (`conform`): a node of class `imm`
yields an immediate, of class `leaf` a number cell; a mismatch, a constructor
of the wrong type under a case, a wrong arity or a constant with no run body is
`stuck`, which is not a violation and is not covered.
-/

@[expose] public section

namespace IxC.Resource

open Ixon

/-! ## Values and the heap -/

/-- An immediate: a field-less constructor, a bounded number, or `irr`. -/
inductive Imm where
  | con (r : Ref)
  | bits (n : Nat)
  | irr
  deriving BEq, Repr, Inhabited

/-- A value: an immediate, or a reference with its capability and the regions it
is confined to. -/
inductive Val where
  | imm (i : Imm)
  | ref (loc cap : Nat) (taint : List Nat)
  deriving BEq, Repr, Inhabited

def Val.taint : Val → List Nat
  | .ref _ _ t => t
  | .imm _ => []

/-- A binding: its value and the mode it was bound at. -/
structure Bnd where
  val : Val
  mode : BinderMode
  deriving Inhabited

/-- A heap cell. -/
inductive Cell where
  /-- A constructor with its fields (every field, an irrelevant or erased one as `irr`). -/
  | ctor (r : Ref) (fields : Array Val)
  /-- A number: a `Nat`, or a trivial wrapper of one. -/
  | num (n : Nat)
  | str (s : String)
  /-- A closure: its environment (captures transferred), parameter, result mode and
  class, captures, body. -/
  | clo (env : List Bnd) (p : Param) (res : ResultMode) (resCls : Cls) (fvs : Array Nat) (body : Term)
  /-- A partial application of a constant. -/
  | pap (r : Ref) (args : Array Val)
  /-- A once view of a function value, and whether it has been called. -/
  | once (target : Val) (spent : Bool)
  deriving Inhabited

structure Obj where
  cell : Cell
  cap : Nat
  deriving Inhabited

structure Heap where
  objs : Array Obj := #[]
  nextCap : Nat := 0
  deriving Inhabited

/-- The four violations. -/
inductive Violation where
  | erasedRead
  | revokedUse
  | borrowEscape
  | onceReentry
  deriving BEq, DecidableEq, Repr, Inhabited

/-- How a run ends. `stuck` and `outOfFuel` are not violations, and nothing is
claimed about runs that end so. -/
inductive Outcome where
  | value (v : Val) (h : Heap)
  | violation (k : Violation)
  | stuck
  | outOfFuel
  deriving Inhabited

inductive Stop where
  | violation (k : Violation)
  | stuck
  | outOfFuel

/-- An extern's behaviour: from its constant, its arguments as bound at its
parameters and the heap, a new heap and its result (`none`: stuck). -/
abbrev ExternOracle := Ref → List Val → Heap → Option (Heap × Val)

/-- The run's state: the heap, the open regions (innermost first; region `0`
is the root and never opens or closes), the statics. -/
structure St where
  heap : Heap
  nextRegion : Nat := 1
  regions : List Nat := []
  statics : Array (Ref × Val) := #[]
  strs : Array (String × Val) := #[]

abbrev M := StateT St (Except Stop)

def violate {α : Type} (k : Violation) : M α := throw (.violation k)
def stuckM {α : Type} : M α := throw .stuck

def obj (loc : Nat) : M Obj := do
  match (← get).heap.objs[loc]? with
  | some o => pure o
  | none => stuckM

def setObj (loc : Nat) (o : Obj) : M Unit :=
  modify fun s => { s with heap := { s.heap with objs := s.heap.objs.set! loc o } }

def freshCap : M Nat := do
  let s ← get
  set { s with heap := { s.heap with nextCap := s.heap.nextCap + 1 } }
  pure s.heap.nextCap

def alloc (c : Cell) (taint : List Nat) : M Val := do
  let cap ← freshCap
  let s ← get
  let loc := s.heap.objs.size
  set { s with heap := { s.heap with objs := s.heap.objs.push ⟨c, cap⟩ } }
  pure (.ref loc cap taint)

/-- A reference is live while its cell has not been transferred since it was
issued. -/
def live (v : Val) : M Unit := do
  match v with
  | .ref loc cap _ => do
    let o ← obj loc
    unless o.cap == cap do violate .revokedUse
  | .imm _ => pure ()

def addTaint (s : Nat) : Val → Val
  | .ref l c t => .ref l c (if t.contains s then t else s :: t)
  | v => v

def taints (vs : List Val) : List Nat := vs.foldl (fun t v => natUnion t v.taint) []

/-- Open a region: the new region and the innermost region open before it (`0`
for the root). -/
def openRegion : M (Nat × Nat) := do
  let s ← get
  let r := s.nextRegion
  set { s with nextRegion := r + 1, regions := r :: s.regions }
  pure (r, s.regions.headD 0)

def closeRegion (r : Nat) : M Unit :=
  modify fun s => { s with regions := s.regions.filter (· != r) }

def confinedTo (s : Nat) (v : Val) : Bool := v.taint.contains s

/-- A borrowed result: confinement to the closing region `s` becomes confinement
to `cur`, the region innermost at the call (none at the root). -/
def renameTaint (s cur : Nat) : Val → Val
  | .ref l c t =>
    if t.contains s then
      let t' := t.filter (· != s)
      .ref l c (if cur == 0 || t'.contains cur then t' else cur :: t')
    else .ref l c t
  | v => v

/-- Whether the value is confined to an open region. -/
def confinedOpen (v : Val) : M Bool := do
  let rs := (← get).regions
  pure (v.taint.any fun s => rs.contains s)

/-! ## Numbers and classes -/

/-- The number a value holds: an immediate number, or a number cell. -/
def numOf? (v : Val) : M (Option Nat) := do
  match v with
  | .imm (.bits n) => pure (some n)
  | .ref loc cap _ => do
    let o ← obj loc
    unless o.cap == cap do violate .revokedUse
    match o.cell with
    | .num n => pure (some n)
    | _ => pure none
  | .imm _ => pure none

/-- A fresh number of class `c`: an immediate, or a fresh, unconfined number cell. -/
def mkNum (c : Cls) (n : Nat) : M Val :=
  match c with
  | .imm => pure (.imm (.bits n))
  | _ => alloc (.num n) []

/-- A `Nat`, by the class of `Nat` (`natClass`). -/
def natValue (n : Nat) : M Val := mkNum natClass n

/-- Whether `v` is a leaf: a number cell, while numbers are leaves. -/
def isLeaf (v : Val) : M Bool := do
  if natClass != .leaf then return false
  match v with
  | .ref loc _ _ => do
    match (← obj loc).cell with
    | .num _ => pure true
    | _ => pure false
  | .imm _ => pure false

/-- **The class check** at a node or binder of class `c`, with the number
representation's conversions: an `imm` node yields an immediate (a number cell
read as its number), a `leaf` node a number cell (an immediate number given a
fresh cell); anything else is `stuck`. -/
def conform (c : Cls) (v : Val) : M Val := do
  match c with
  | .irr => pure (.imm .irr)
  | .val => pure v
  | .imm =>
    match v with
    | .imm i => pure (.imm i)
    | .ref .. => do
      match ← numOf? v with
      | some n => pure (.imm (.bits n))
      | none => stuckM
  | .leaf =>
    match v with
    | .imm (.bits n) => alloc (.num n) []
    | .ref .. => do
      match ← numOf? v with
      | some _ => pure v
      | none => stuckM
    | .imm _ => stuckM

/-! ## Unique transfer -/

def Cell.slot? : Cell → Nat → Option Val
  | .ctor _ fs, i => fs[i]?
  | .clo env _ _ _ _ _, i => env[i]?.map (·.val)
  | .pap _ as, i => as[i]?
  | .once t _, 0 => some t
  | _, _ => none

def setBnd : List Bnd → Nat → Val → List Bnd
  | [], _, _ => []
  | b :: bs, 0, v => { b with val := v } :: bs
  | b :: bs, n + 1, v => b :: setBnd bs n v

def Cell.setSlot : Cell → Nat → Val → Cell
  | .ctor r fs, i, v => .ctor r (fs.set! i v)
  | .clo env p res rc fvs b, i, v => .clo (setBnd env i v) p res rc fvs b
  | .pap r as, i, v => .pap r (as.set! i v)
  | .once _ s, 0, v => .once v s
  | c, _, _ => c

/-- **The ownership closure**: the slots of a cell that a unique transfer of the
cell transfers with it. Deep: a constructor's `inherited` fields, a closure's
captures, a partial application's arguments, a once view's target. It stops at
`@shared` fields, immediates and leaves (`renew`). One definition, so a
different closure (a spine rule, say) is a change here. -/
def ownedSlots (P : Prog) : Cell → List Nat
  | .ctor r fields =>
    match P.ctorOf? r with
    | some (_, _, _, fs) =>
      (List.range fields.size).filter fun i => (fs[i]?.map (·.fmode == .inherited)).getD true
    | none => List.range fields.size
  | .clo _ _ _ _ fvs _ => fvs.toList
  | .pap _ args => List.range args.size
  | .once _ _ => [0]
  | .num _ | .str _ => []

/-- Renew `v`'s ownership closure: fresh capabilities, so every other reference
dies. A cell reached twice is `revokedUse` (a unique value is a tree); a leaf is
left as it is. -/
def renew (P : Prog) : Nat → Val → M Val
  | 0, _ => throw .outOfFuel
  | _ + 1, .imm i => pure (.imm i)
  | n + 1, .ref loc cap t => do
    let o ← obj loc
    unless o.cap == cap do violate .revokedUse
    if ← isLeaf (.ref loc cap t) then return .ref loc cap t
    let cap' ← freshCap
    setObj loc { o with cap := cap' }
    let mut cell := o.cell
    for i in ownedSlots P o.cell do
      match cell.slot? i with
      | some sv => cell := cell.setSlot i (← renew P n sv)
      | none => pure ()
    setObj loc ⟨cell, cap'⟩
    pure (.ref loc cap' t)

/-- **A unique transfer**: nothing for a leaf or an immediate; a value confined
to an open region may only go to a borrowed binder or result. -/
def transfer (P : Prog) (fuel : Nat) (toBorrowed : Bool) (v : Val) : M Val := do
  if ← isLeaf v then return v
  if !toBorrowed && (← confinedOpen v) then violate .borrowEscape
  renew P fuel v

/-- **Binding a value at a binder** of mode `m` and class `c`, in region `s`. -/
def bindAt (P : Prog) (fuel s : Nat) (m : BinderMode) (c : Cls) (v : Val) : M Bnd := do
  if m == .erased then return ⟨.imm .irr, .erased⟩
  let v ← conform c v
  let v ← if m.isUnique then transfer P fuel m.isBorrowed v else pure v
  let v := if m.isBorrowed then addTaint s v else v
  let v ← if m.usage == .once then alloc (.once v false) v.taint else pure v
  return ⟨v, m⟩

/-- **Returning** from region `s` (opened inside `cur`) at result mode `r`. -/
def ret (P : Prog) (fuel s cur : Nat) (r : ResultMode) (c : Cls) (v : Val) : M Val := do
  let v ← conform c v
  match r with
  | .shared => if confinedTo s v then violate .borrowEscape else pure v
  | .unique => if confinedTo s v then violate .borrowEscape else transfer P fuel false v
  | .borrowed => pure (renameTaint s cur v)
  | .uniqueBorrowed => do
    let v ← transfer P fuel true v
    pure (renameTaint s cur v)

/-- A value read out of a container confined to `t`: confined with it, unless
the field is `@shared` (`inherit = false`). A leaf read out of a container is a
counted reference of its own, confined to nothing. -/
def readOut (inherit : Bool) (t : List Nat) (v : Val) : M Val := do
  if ← isLeaf v then
    match v with
    | .ref l c _ => return .ref l c []
    | .imm _ => return v
  if !inherit then return v
  pure (t.foldl (fun v s => addTaint s v) v)

/-- **Where capture transfers**: forming a closure transfers each captured
binding of a unique mode (and a partial application its arguments at unique
parameters, `makePap`). One definition, so a different rule is a change here. -/
def captureTransfers (m : BinderMode) : Bool := m.isUnique

/-- A partial application of `r`: its arguments at unique parameters transferred
when it is formed. -/
def makePap (P : Prog) (fuel : Nat) (r : Ref) (params : Array Param) (vs : List Val) : M Val := do
  let mut out : Array Val := #[]
  for (v, i) in vs.zipIdx do
    let m := (params[i]?.map (·.mode)).getD .many
    out := out.push (← if captureTransfers m then transfer P fuel m.isBorrowed v else pure v)
  alloc (.pap r out) (taints out.toList)

/-- Whether argument `i` of a call of `d` is not evaluated (an erased parameter
or field). -/
def erasedAt (d : RunDef) (i : Nat) : Bool :=
  match d with
  | .body ps .. | .extern ps .. | .stuck ps .. => (ps[i]?.map (·.mode == .erased)).getD false
  | .ctor _ _ nP fs => if i < nP then false else (fs[i - nP]?.map (·.mode == .erased)).getD false
  | _ => false

/-- A constructor application: a field-less constructor is an immediate; a
trivial wrapper at class `imm` or `leaf` is its field; anything else a fresh
cell confined with what it holds. -/
def construct (r : Ref) (fields : Array Field) (vs : List Val) (c : Cls) : M Val := do
  let mut out : Array Val := #[]
  for (f, v) in fields.toList.zip vs do
    out := out.push (← if f.kept then conform f.cls v else pure (.imm .irr))
  let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
  if kept.isEmpty then return .imm (.con r)
  if (c == .imm || c == .leaf) && kept.size == 1 then
    let some i := kept[0]? | stuckM
    let some v := out[i]? | stuckM
    return ← conform c v
  alloc (.ctor r out) (taints out.toList)

/-- A primitive applied to numbers. -/
def prim (p : Prim) (vs : List Val) : M Val := do
  let mut ns : List Nat := []
  for v in vs do
    match ← numOf? v with
    | some k => ns := ns ++ [k]
    | none => stuckM
  match p, ns with
  | .zero, [] => natValue 0
  | .succ, [a] => natValue (a + 1)
  | .pred, [a] => natValue (a - 1)
  | .add, [a, b] => natValue (a + b)
  | .sub, [a, b] => natValue (a - b)
  | .mul, [a, b] => natValue (a * b)
  | .div, [a, b] => natValue (a / b)
  | .mod, [a, b] => natValue (a % b)
  | .pow, [a, b] => natValue (a ^ b)
  | .gcd, [a, b] => natValue (Nat.gcd a b)
  | .land, [a, b] => natValue (a &&& b)
  | .lor, [a, b] => natValue (a ||| b)
  | .xor, [a, b] => natValue (a ^^^ b)
  | .shiftLeft, [a, b] => natValue (a <<< b)
  | .shiftRight, [a, b] => natValue (a >>> b)
  | .beq t f, [a, b] => pure (.imm (.con (if a == b then t else f)))
  | .ble t f, [a, b] => pure (.imm (.con (if a ≤ b then t else f)))
  | _, _ => stuckM

/-- A string literal: one static cell per content. -/
def strValue (s : String) : M Val := do
  match (← get).strs.find? (·.1 == s) with
  | some (_, v) => do live v; pure v
  | none => do
    let v ← alloc (.str s) []
    modify fun st => { st with strs := st.strs.push (s, v) }
    pure v

/-- Forming a closure: each capture is read (so `erasedRead` and `revokedUse`
apply) and transferred where `captureTransfers` says. -/
def formClosure (P : Prog) (fuel : Nat) (env : List Bnd) (p : Param) (res : ResultMode)
    (rc : Cls) (fvs : Array Nat) (body : Term) : M Val := do
  let mut env' := env
  let mut taint : List Nat := []
  for i in fvs.toList do
    let some b := env[i]? | stuckM
    if b.mode == .erased then violate .erasedRead
    live b.val
    let v ← if captureTransfers b.mode then transfer P fuel b.mode.isBorrowed b.val else pure b.val
    env' := setBnd env' i v
    taint := natUnion taint v.taint
  alloc (.clo env' p res rc fvs body) taint

/-- An extern call: its arguments bound at its parameters in a fresh region, its
result from the oracle, returned at its result mode. -/
def callExtern (P : Prog) (ext : ExternOracle) (fuel : Nat) (r : Ref) (params : Array Param)
    (res : ResultMode) (rc : Cls) (vs : List Val) : M Val := do
  let (s, cur) ← openRegion
  let mut bs : List Val := []
  for (p, v) in params.toList.zip vs do
    bs := bs ++ [(← bindAt P fuel s p.mode p.cls v).val]
  let st ← get
  match ext r bs st.heap with
  | none => stuckM
  | some (h', v) =>
    set { st with heap := h' }
    let v ← ret P fuel s cur res rc v
    closeRegion s
    pure v

/-- The case a value selects: the constructor's index and its fields, each with
whether it is erased. A number at `Nat`; a field-less constructor; `irr` at a
one-constructor inductive (a proof's eliminator, a cast); a trivial wrapper's
immediate or number cell, as its one field; a constructor cell, its fields
read out of it. -/
def select (P : Prog) (k : CaseInfo) (mv : Val) : M (Nat × Array (Val × Bool)) := do
  let cs := P.ctorsOf k.ind
  let fieldsOf (ci : Nat) : Array Field :=
    match cs[ci]? with
    | some c => match P.ctorOf? c with
      | some (_, _, _, fs) => fs
      | none => #[]
    | none => #[]
  let irrFields (ci : Nat) : Array (Val × Bool) :=
    (fieldsOf ci).map fun f => (Val.imm .irr, f.mode == .erased)
  let wrapperCase : M (Nat × Array (Val × Bool)) :=
    match P.wrapperField? k.ind with
    | some wi => pure (0, (irrFields 0).set! wi (mv, false))
    | none => stuckM
  if P.nat == some k.ind then
    match ← numOf? mv with
    | some 0 => return (0, #[])
    | some (m + 1) => return (1, #[(← natValue m, false)])
    | none => stuckM
  match mv with
  | .imm (.con r) =>
    match P.ctorOf? r with
    | some (ind, cidx, _, _) => if ind == k.ind then pure (cidx, irrFields cidx) else wrapperCase
    | none => stuckM
  | .imm .irr => if cs.size == 1 then pure (0, irrFields 0) else stuckM
  | .imm (.bits _) => wrapperCase
  | .ref loc cap t => do
    let o ← obj loc
    unless o.cap == cap do violate .revokedUse
    match o.cell with
    | .ctor r fs =>
      match P.ctorOf? r with
      | some (ind, cidx, _, fdefs) =>
        unless ind == k.ind do stuckM
        let mut out : Array (Val × Bool) := #[]
        for (f, i) in fdefs.zipIdx do
          let v := fs[i]?.getD (.imm .irr)
          out := out.push ((← readOut (f.fmode == .inherited) t v), f.mode == .erased)
        pure (cidx, out)
      | none => stuckM
    | .num _ => wrapperCase
    | _ => stuckM

/-- The head and arguments of an application spine. -/
def collect : Nat → Term → List Term → Term × List Term
  | 0, t, acc => (t, acc)
  | n + 1, .app f a _, acc => collect n f (a :: acc)
  | _, t, acc => (t, acc)

/-! ## The evaluator -/

mutual

/-- Evaluate a term. -/
def eval (P : Prog) (ext : ExternOracle) : Nat → List Bnd → Term → M Val
  | 0, _, _ => throw .outOfFuel
  | n + 1, env, t =>
    match t with
    | .irr => pure (.imm .irr)
    | .var i c => do
      let some b := env[i]? | stuckM
      if b.mode == .erased then violate .erasedRead
      live b.val
      conform c b.val
    | .natLit k => natValue k
    | .strLit s => strValue s
    | .const r c => spine P ext n env (.const r c) [] c
    | .app f a c => do
      let (h, as) := collect n (.app f a c) []
      spine P ext n env h as c
    | .lam p res rc fvs body => formClosure P n env p res rc fvs body
    | .letE m d v b => do
      match m with
      | .value .erased => eval P ext n (⟨.imm .irr, .erased⟩ :: env) b
      | _ => do
        let x ← eval P ext n env v
        let (s, _) ← openRegion
        let bnd ← bindAt P n s m.binderMode d x
        let r ← eval P ext n (bnd :: env) b
        if confinedTo s r then violate .borrowEscape
        closeRegion s
        pure r
    | .proj s i e c => do
      let v ← eval P ext n env e
      live v
      let cs := P.ctorsOf s
      let some ctor := cs[0]? | stuckM
      let some (_, _, _, fields) := P.ctorOf? ctor | stuckM
      let some f := fields[i]? | stuckM
      if f.mode == .erased then violate .erasedRead
      if f.cls == .irr then return .imm .irr
      let asWrapper : M Val :=
        if P.wrapperField? s == some i then conform c v else stuckM
      match v with
      | .ref loc _ tv => do
        match (← obj loc).cell with
        | .ctor r' fs =>
          unless r' == ctor do stuckM
          let some fv := fs[i]? | stuckM
          conform c (← readOut (f.fmode == .inherited) tv fv)
        | .num _ => asWrapper
        | _ => stuckM
      | .imm _ => asWrapper
    | .case k major alts extra c => do
      let mv ← match major with
        | .var j mc => do
          let some b := env[j]? | stuckM
          if b.mode == .erased then violate .erasedRead
          live b.val
          let v ← conform mc b.val
          -- a match on a unique binding consumes it
          if b.mode.isUnique then transfer P n b.mode.isBorrowed v else pure v
        | t => eval P ext n env t
      let (j, fields) ← select P k mv
      let some alt := k.alts[j]? | stuckM
      let some altT := alts[j]? | stuckM
      let args := alt.args.toList.map fun fa => match fa with
        | .field i => fields[i]?.getD (.imm .irr, false)
        | .irr => (.imm .irr, false)
        | .unit => (.imm .irr, false)
      let r ← applyAlt P ext n env altT args
      let mut ex : List Val := []
      for e in extra.toList do
        ex := ex ++ [← eval P ext n env e]
      applyAll P ext n r ex c

/-- Evaluate an application spine: at a constant head, the arguments at erased
positions are not evaluated. -/
def spine (P : Prog) (ext : ExternOracle) : Nat → List Bnd → Term → List Term → Cls → M Val
  | 0, _, _, _, _ => throw .outOfFuel
  | n + 1, env, head, args, c =>
    match head with
    | .const r _ => do
      let d := P.find? r
      let mut vs : List Val := []
      for (a, i) in args.zipIdx do
        let skip := match d with
          | some d => erasedAt d i
          | none => false
        vs := vs ++ [← if skip then pure (.imm .irr) else eval P ext n env a]
      callWith P ext n r vs c
    | _ => do
      let f ← eval P ext n env head
      let mut vs : List Val := []
      for a in args do
        vs := vs ++ [← eval P ext n env a]
      applyAll P ext n f vs c

/-- Call a constant with evaluated arguments. -/
def callWith (P : Prog) (ext : ExternOracle) : Nat → Ref → List Val → Cls → M Val
  | 0, _, _, _ => throw .outOfFuel
  | n + 1, r, vs, c =>
    match P.find? r with
    | some (.body params res rc _ body) =>
      if vs.length < params.size then makePap P n r params vs
      else do
        let f ← if params.size == 0 then static P ext n r body rc
          else enter P ext n params res rc body (vs.take params.size)
        applyAll P ext n f (vs.drop params.size) c
    | some (.ctor _ _ nP fields) =>
      if vs.length < nP + fields.size then makePap P n r #[] vs
      else if vs.length > nP + fields.size then stuckM
      else construct r fields (vs.drop nP) c
    | some (.prim p) =>
      if vs.length < p.arity then makePap P n r #[] vs
      else if vs.length > p.arity then stuckM
      else do conform c (← prim p vs)
    | some (.extern params res rc _) =>
      if vs.length < params.size then makePap P n r params vs
      else do
        let f ← callExtern P ext n r params res rc (vs.take params.size)
        applyAll P ext n f (vs.drop params.size) c
    | some (.ind _) => pure (.imm .irr)
    | _ => stuckM

/-- Enter a run body with its arguments: a region for the call, the parameters
bound by their modes, the result returned at the result mode. -/
def enter (P : Prog) (ext : ExternOracle) :
    Nat → Array Param → ResultMode → Cls → Term → List Val → M Val
  | 0, _, _, _, _, _ => throw .outOfFuel
  | n + 1, params, res, rc, body, vs => do
    let (s, cur) ← openRegion
    let mut env : List Bnd := []
    for (p, v) in params.toList.zip vs do
      env := (← bindAt P n s p.mode p.cls v) :: env
    let r ← eval P ext n env body
    let r ← ret P n s cur res rc r
    closeRegion s
    pure r

/-- A static: a nullary constant's body runs once, and its value is shared. -/
def static (P : Prog) (ext : ExternOracle) : Nat → Ref → Term → Cls → M Val
  | 0, _, _, _ => throw .outOfFuel
  | n + 1, r, body, rc => do
    match (← get).statics.find? (·.1 == r) with
    | some (_, v) => do live v; pure v
    | none => do
      let v ← conform rc (← eval P ext n [] body)
      modify fun s => { s with statics := s.statics.push (r, v) }
      pure v

/-- Apply a value to arguments, one at a time. -/
def applyAll (P : Prog) (ext : ExternOracle) : Nat → Val → List Val → Cls → M Val
  | 0, _, _, _ => throw .outOfFuel
  | _ + 1, f, [], c => conform c f
  | n + 1, f, a :: rest, c => do
    let g ← applyOne P ext n f a (if rest.isEmpty then c else .val)
    applyAll P ext n g rest c

/-- Apply a function value to one argument: a closure is a call of arity one,
returning at its own result mode; a partial application gathers its arguments
until its constant is entered; a once view may be called once. -/
def applyOne (P : Prog) (ext : ExternOracle) : Nat → Val → Val → Cls → M Val
  | 0, _, _, _ => throw .outOfFuel
  | n + 1, f, a, c => do
    match f with
    | .imm .irr => pure (.imm .irr)
    | .imm _ => stuckM
    | .ref loc cap _ => do
      let o ← obj loc
      unless o.cap == cap do violate .revokedUse
      match o.cell with
      | .clo env p res rc _ body => do
        let (s, cur) ← openRegion
        let b ← bindAt P n s p.mode p.cls a
        let r ← eval P ext n (b :: env) body
        let r ← ret P n s cur res rc r
        closeRegion s
        conform c r
      | .pap r args => callWith P ext n r (args.toList ++ [a]) c
      | .once t spent => do
        if spent then violate .onceReentry
        setObj loc { o with cell := .once t true }
        applyOne P ext n t a c
      | _ => stuckM

/-- A case alternative applied to its constructor's fields, by need: a λ
telescope binds them in place (a call of arity one per binder, with no closure
formed); anything else is evaluated and applied. -/
def applyAlt (P : Prog) (ext : ExternOracle) : Nat → List Bnd → Term → List (Val × Bool) → M Val
  | 0, _, _, _ => throw .outOfFuel
  | n + 1, env, t, [] => eval P ext n env t
  | n + 1, env, t, (a, er) :: rest =>
    match t with
    | .lam p res rc _ body => do
      let (s, cur) ← openRegion
      let b ← if er then pure ⟨.imm .irr, .erased⟩ else bindAt P n s p.mode p.cls a
      let r ← applyAlt P ext n (b :: env) body rest
      let r ← ret P n s cur res rc r
      closeRegion s
      pure r
    | _ => do
      let f ← eval P ext n env t
      applyAll P ext n f (((a, er) :: rest).map (·.1)) .val

end

/-- **`runR`**: run the run body of `f` on `args` in the heap `h`, from the
root, with `fuel`. -/
def runR (P : Prog) (ext : ExternOracle) (fuel : Nat) (f : Ref) (h : Heap) (args : List Val) :
    Outcome :=
  match P.find? f with
  | some (.body params res rc _ body) =>
    if args.length != params.size then .stuck else
    match (enter P ext fuel params res rc body args).run { heap := h } with
    | .ok (v, st) => .value v st.heap
    | .error (.violation k) => .violation k
    | .error .stuck => .stuck
    | .error .outOfFuel => .outOfFuel
  | _ => .stuck

end IxC.Resource

end
