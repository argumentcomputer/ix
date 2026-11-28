import IxCK.Resource
import DiffTest.Hyp

/-! # The generator (MT): a typed universe, its run program, programs and inputs

Classes, skeletons and `noLeaf` of a type are computed in one place (`Ty.cls`,
`Ty.skel`, `Ty.noLeaf`), by the canonical classes and by the reader's own rules
(`noLeafType`: a function type, a sort, an inductive with other than one
constructor; `readSkel`: an inductive applied to arguments is `dataApp`). The
self-test in `Main` compares the interfaces built here with the reader's
functions on Ixon records of the same types. -/

namespace MT.DiffTest

open IxCK.Resource Ixon

/-! ## Randomness -/

abbrev R := StateM Rng

def rand (n : Nat) : R Nat := do
  let (x, g) := (← get).next
  set g
  pure (if n == 0 then 0 else x.toNat % n)

def chance (pct : Nat) : R Bool := do pure ((← rand 100) < pct)

def weighted {α : Type} [Inhabited α] (xs : List (Nat × α)) : R α := do
  let total := xs.foldl (fun s (w, _) => s + w) 0
  let mut k ← rand total
  for (w, x) in xs do
    if k < w then return x
    k := k - w
  pure default

def pickL {α : Type} [Inhabited α] (xs : List α) : R α := do
  pure (xs[← rand xs.length]?.getD default)

/-! ## Types -/

inductive Ty where
  | nat | bool | list | box | sbox | ekey | pairN | pairL | wrap
  | eq (a b : Ty)
  | arr (m : BinderMode) (r : ResultMode) (a b : Ty)
  deriving BEq, Inhabited, Repr

namespace Ty

/-- The canonical class of the type's values. -/
def cls : Ty → Cls
  | .nat | .wrap => .leaf
  | .bool => .imm
  | .eq .. => .irr
  | _ => .val

/-- `readSkel`'s skeleton: an inductive `data`, `List Nat` an application, an arrow its modes. -/
def skel : Ty → Skel
  | .list => .dataApp .data .data
  | .eq .. => .dataApp (.dataApp (.dataApp .data .data) .unknown) .unknown
  | .arr m r a b => .arrow m a.skel r b.skel
  | _ => .data

/-- `noLeafType`'s rule: a function type, or an inductive with other than one constructor. -/
def noLeaf : Ty → Bool
  | .nat | .bool | .list | .arr .. => true
  | _ => false

def param (t : Ty) (m : BinderMode) : Param := { mode := m, cls := t.cls, skel := t.skel, noLeaf := t.noLeaf }

/-- Whether a type is data or an arrow chain with default modes only. -/
def isDefaultArrow : Ty → Bool
  | .arr m r _ b => m == .many && r == .shared && b.isDefaultArrow
  | _ => true

def defaultArrows : Ty → Ty
  | .arr _ _ a b => .arr .many .shared a b.defaultArrows
  | t => t

/-- An input function's interface for an arrow type: its parameters up to the
  last moded arrow (at least one), that arrow's result mode, the rest. -/
def split : Ty → List (Ty × BinderMode) × ResultMode × Ty
  | .arr m r a b =>
    if b.isDefaultArrow then ([(a, m)], r, b)
    else let (ps, r', c) := split b; ((a, m) :: ps, r', c)
  | t => ([], .shared, t)

def dropArrows : Nat → Ty → Option Ty
  | 0, t => some t
  | k + 1, .arr _ _ _ b => dropArrows k b
  | _, _ => none

def arity : Ty → Nat
  | .arr _ _ _ b => b.arity + 1
  | _ => 0

def domains : Nat → Ty → List Ty
  | 0, _ => []
  | k + 1, .arr _ _ a b => a :: domains k b
  | _, _ => []

/-- The first `k` binder modes. -/
def domainModes : Nat → Ty → List BinderMode
  | 0, _ => []
  | k + 1, .arr m _ _ b => m :: domainModes k b
  | _, _ => []

def name : Ty → String
  | .nat => "Nat" | .bool => "Bool" | .list => "List Nat" | .box => "Box" | .sbox => "SBox"
  | .ekey => "EKey" | .pairN => "PairN" | .pairL => "PairL" | .wrap => "WrapN"
  | .eq a b => s!"({a.name} = {b.name})"
  | .arr m r a b => s!"({repr m} {a.name} →{repr r} {b.name})"

end Ty

/-- The interface type of `params` (`ifaceSkel`'s shape: only the last arrow
carries the result mode). -/
def ifaceTy : List (Ty × BinderMode) → ResultMode → Ty → Ty
  | [], _, ρ => ρ
  | [(a, m)], r, ρ => .arr m r a ρ
  | (a, m) :: ps, r, ρ => .arr m .shared a (ifaceTy ps r ρ)

/-! ## The fixed library -/

def addrOf (k : Nat) : Address := ⟨⟨#[(k % 256).toUInt8, (k / 256).toUInt8, 0x6d]⟩⟩
def memR (k : Nat) : Ref := .member (addrOf k) 0
def ctrR (k j : Nat) : Ref := .ctor (addrOf k) 0 j

def natI := memR 1
def boolI := memR 2
def trueR := ctrR 2 0
def falseR := ctrR 2 1
def listI := memR 3
def nilR := ctrR 3 0
def consR := ctrR 3 1
def boxI := memR 4
def boxC := ctrR 4 0
def sboxI := memR 5
def sboxC := ctrR 5 0
def ekeyI := memR 6
def ekeyC := ctrR 6 0
def pairNI := memR 7
def pairNC := ctrR 7 0
def pairLI := memR 8
def pairLC := ctrR 8 0
def wrapI := memR 9
def wrapC := ctrR 9 0
def eqI := memR 10
def reflC := ctrR 10 0

def addP := memR 20
def consumeR := memR 21
def lenR := memR 22
def callTwiceR := memR 23
def idR := memR 24
def constR := memR 25
def mkKR := memR 26
def ekeyRecR := memR 27
def boxCasesR := memR 28
def exFresh := memR 30
def exId := memR 31
def exBox := memR 32
def exStale := memR 33
def exClo := memR 34
def exCloU := memR 35

/-- User definitions are `memR (100 + j)`, input functions `memR (200 + j)`. -/
def userR (j : Nat) : Ref := memR (100 + j)
def inFnR (j : Nat) : Ref := memR (200 + j)

def fieldOf (c : Cls) (fm : FieldMode := .inherited) (m : BinderMode := .many) : Field :=
  { mode := m, fmode := fm, cls := c }

/-- The inductives: their type, run definitions, case shape and constructor field types. -/
structure IndK where
  ty : Ty
  ind : Ref
  ctors : List Ref
  /-- per constructor: the number of type arguments, the field types, which field is erased -/
  shape : List (Nat × List Ty × List Bool)
  info : CaseInfo
  deriving Inhabited

def caseOf (ind : Ref) (fields : List Nat) : CaseInfo :=
  { ind, arity := fields.length + 1, major := 0,
    alts := (fields.zipIdx.map fun (n, j) =>
      ({ alt := j + 1, args := (List.range n).toArray.map FieldArg.field } : CaseAlt)).toArray }

def inds : List IndK := [
  { ty := .nat, ind := natI, ctors := [], shape := [(0, [], []), (0, [.nat], [false])],
    info := caseOf natI [0, 1] },
  { ty := .bool, ind := boolI, ctors := [trueR, falseR], shape := [(0, [], []), (0, [], [])],
    info := caseOf boolI [0, 0] },
  { ty := .list, ind := listI, ctors := [nilR, consR],
    shape := [(1, [], []), (1, [.nat, .list], [false, false])], info := caseOf listI [0, 2] },
  { ty := .box, ind := boxI, ctors := [boxC], shape := [(0, [.list], [false])], info := caseOf boxI [1] },
  { ty := .sbox, ind := sboxI, ctors := [sboxC], shape := [(0, [.list], [false])], info := caseOf sboxI [1] },
  { ty := .ekey, ind := ekeyI, ctors := [ekeyC], shape := [(0, [.list, .list], [true, false])],
    info := caseOf ekeyI [2] },
  { ty := .pairN, ind := pairNI, ctors := [pairNC], shape := [(0, [.nat, .nat], [false, false])],
    info := caseOf pairNI [2] },
  { ty := .pairL, ind := pairLI, ctors := [pairLC], shape := [(0, [.list, .list], [false, false])],
    info := caseOf pairLI [2] },
  { ty := .wrap, ind := wrapI, ctors := [wrapC], shape := [(0, [.nat], [false])], info := caseOf wrapI [1] }]

def indOf? (t : Ty) : Option IndK := inds.find? (·.ty == t)

def caseEq : CaseInfo := { ind := eqI, arity := 4, major := 2, alts := #[{ alt := 3, args := #[] }] }

/-! ## Typed terms -/

inductive G where
  | var (i : Nat) (t : Ty)
  | lit (n : Nat)
  /-- a constant (body, helper, primitive, extern, constructor) applied to `args`, of type `t` -/
  | call (f : Ref) (args : List G) (t : Ty)
  /-- a non-constant head applied to `args` -/
  | appv (f : G) (args : List G) (t : Ty)
  | lam (m : BinderMode) (r : ResultMode) (a b : Ty) (body : G)
  | letE (lm : LetMode) (s : Ty) (v body : G)
  | proj (s : Ref) (i : Nat) (e : G) (t : Ty)
  /-- a case on inductive `k` (by its type) -/
  | case (k : Ty) (major : G) (alts : List G) (ex : List G) (t : Ty)
  | cast (e : G) (t : Ty)
  | irr
  deriving Inhabited

partial def G.ty : G → Ty
  | .var _ t | .call _ _ t | .appv _ _ t | .proj _ _ _ t | .case _ _ _ _ t | .cast _ t => t
  | .lit _ => .nat
  | .lam m r a b _ => .arr m r a b
  | .letE _ _ _ b => b.ty
  | .irr => .eq .nat .nat

/-- Fold arguments into applications, the last at class `c` (their `app` helper). -/
def foldApp (h : Term) (args : List Term) (c : Cls) : Term :=
  args.zipIdx.foldl (fun g (a, i) => Term.app g a (if i + 1 == args.length then c else .val)) h

/-- **Compile** to a run term, every class by `Ty.cls`. -/
partial def G.compile : G → Term
  | .var i t => if t.cls == .irr then .irr else .var i t.cls
  | .lit n => .natLit n
  | .call f [] t => .const f t.cls
  | .call f args t => foldApp (.const f .val) (args.map G.compile) t.cls
  | .appv f args t => foldApp f.compile (args.map G.compile) t.cls
  | .lam m r a b body =>
    let bt := body.compile
    .lam (a.param m) r b.cls ((freeVars 4096 1 bt).toOption.getD []).toArray bt
  | .letE lm s v b => .letE lm s.cls v.compile b.compile
  | .proj s i e t => .proj s i e.compile t.cls
  | .case k mj alts ex t =>
    match indOf? k with
    | some ik => .case ik.info mj.compile (alts.map G.compile).toArray (ex.map G.compile).toArray t.cls
    | none => .irr
  | .cast e t => .case caseEq .irr #[e.compile] #[] t.cls
  | .irr => .irr

/-- The closed leaf of a type. -/
partial def leafOf : Ty → G
  | .nat => .lit 1
  | .bool => .call trueR [] .bool
  | .list => .call nilR [.irr] .list
  | .box => .call boxC [leafOf .list] .box
  | .sbox => .call sboxC [leafOf .list] .sbox
  | .ekey => .call ekeyC [leafOf .list, leafOf .list] .ekey
  | .pairN => .call pairNC [.lit 1, .lit 2] .pairN
  | .pairL => .call pairLC [leafOf .list, leafOf .list] .pairL
  | .wrap => .call wrapC [.lit 1] .wrap
  | .eq .. => .irr
  | .arr m r a b => .lam m r a b (leafOf b)

/-! ## Programs -/

/-- A user definition (or an input function): its parameters, result, body. -/
structure UDef where
  ref : Ref
  params : List (Ty × BinderMode)
  res : ResultMode
  rty : Ty
  body : G
  deriving Inhabited

def UDef.fullTy (d : UDef) : Ty := ifaceTy d.params d.res d.rty

def UDef.runDef (d : UDef) : RunDef :=
  .body (d.params.map fun (t, m) => t.param m).toArray d.res d.rty.cls d.rty.skel d.body.compile

structure GProg where
  defs : List UDef
  inFns : List UDef
  externs : Bool
  deriving Inhabited

def anyTy := Ty.eq .nat .nat  -- placeholder for a type parameter's class `irr`

def ctorDefs : List (Ref × RunDef) := [
  (natI, .ind #[]),
  (boolI, .ind #[trueR, falseR]), (trueR, .ctor boolI 0 0 #[]), (falseR, .ctor boolI 1 0 #[]),
  (listI, .ind #[nilR, consR]), (nilR, .ctor listI 0 1 #[]), (consR, .ctor listI 1 1 #[fieldOf .val, fieldOf .val]),
  (boxI, .ind #[boxC]), (boxC, .ctor boxI 0 0 #[fieldOf .val]),
  (sboxI, .ind #[sboxC]), (sboxC, .ctor sboxI 0 0 #[fieldOf .val .shared]),
  (ekeyI, .ind #[ekeyC]), (ekeyC, .ctor ekeyI 0 0 #[fieldOf .val .inherited .erased, fieldOf .val]),
  (pairNI, .ind #[pairNC]), (pairNC, .ctor pairNI 0 0 #[fieldOf .leaf, fieldOf .leaf]),
  (pairLI, .ind #[pairLC]), (pairLC, .ctor pairLI 0 0 #[fieldOf .val, fieldOf .val]),
  (wrapI, .ind #[wrapC]), (wrapC, .ctor wrapI 0 0 #[fieldOf .leaf]),
  (eqI, .ind #[reflC]), (reflC, .ctor eqI 0 2 #[])]

def natArr : Ty := .arr .many .shared .nat .nat

/-- A type parameter `(α : Type)`: class irr, skeleton data (a sort), `noLeaf` (a sort). -/
def tyParam : Param := { mode := .many, cls := .irr, skel := .data, noLeaf := true }
/-- A value at a type parameter: class val, skeleton unknown (a variable). -/
def polyParam : Param := { mode := .many, cls := .val, skel := .unknown, noLeaf := false }

def ekeyMinorTy : Ty := .arr .many .shared .list (.arr .many .shared .list .list)
def ekeyRecTy : Ty := .arr .many .shared ekeyMinorTy (.arr .many .shared .ekey .list)
def boxCasesTy : Ty := .arr .many .shared .box (.arr .many .shared (.arr .many .shared .list .nat) .nat)

def helperDefs : List (Ref × RunDef) := [
  (addP, .prim .add),
  -- consume (@unique xs : List Nat) : Nat := 0
  (consumeR, .body #[Ty.list.param .unique] .shared .leaf .data (.natLit 0)),
  -- len (xs : List Nat) : Nat := match xs with | [] => 0 | _ :: t => len t + 1
  (lenR, .body #[Ty.list.param .many] .shared .leaf .data
    (.case (caseOf listI [0, 2]) (.var 0 .val)
      #[.natLit 0, .lam (Ty.nat.param .many) .shared .leaf #[]
        (.lam (Ty.list.param .many) .shared .leaf #[] (foldApp (.const addP .val)
          [foldApp (.const lenR .val) [.var 0 .val] .leaf, .natLit 1] .leaf))] #[] .leaf)),
  -- callTwice (f : Nat → Nat) : Nat := f 0 + f 1
  (callTwiceR, .body #[natArr.param .many] .shared .leaf .data
    (foldApp (.const addP .val) [foldApp (.var 0 .val) [.natLit 0] .leaf, foldApp (.var 0 .val) [.natLit 1] .leaf] .leaf)),
  -- id {α} (a : α) : α := a
  (idR, .body #[tyParam, polyParam] .shared .val .unknown (.var 0 .val)),
  -- const {α β} (a : α) (b : β) : α := a
  (constR, .body #[tyParam, tyParam, polyParam, polyParam] .shared .val .unknown (.var 1 .val)),
  -- mkK {α β} (a : α) (b : β) : Nat → α := fun _ => a
  (mkKR, .body #[tyParam, tyParam, polyParam, polyParam] .shared .val (.arrow .many .data .shared .unknown)
    (.lam (Ty.nat.param .many) .shared .val #[1] (.var 2 .val))),
  -- raw recursor stub (`stuck` in `runR`, checked via `ifaceOf?` in `anCall` at class `val`)
  (ekeyRecR, .stuck #[ekeyMinorTy.param .many, Ty.ekey.param .many] .shared .val Ty.list.skel),
  -- case definition callable directly (under-applied or non-case call refused by V3 in `anCall`)
  (boxCasesR, .caseDef (caseOf boxI [1]))]

def externDefs : List (Ref × RunDef) := [
  (exFresh, .extern #[Ty.nat.param .many] .shared .leaf .data),
  (exId, .extern #[Ty.list.param .many] .shared .val Ty.list.skel),
  (exBox, .extern #[Ty.list.param .many] .shared .val .data),
  (exStale, .extern #[Ty.nat.param .many] .shared .val Ty.list.skel),
  -- closure-environment externs (hardening: exercises `Cell.vals` on `.clo` captures & Gap A)
  (exClo, .extern #[natArr.param .many] .shared .val Ty.list.skel),
  (exCloU, .extern #[natArr.param .many] .unique .val Ty.list.skel)]

def GProg.prog (gp : GProg) : Prog :=
  { defs := (ctorDefs ++ helperDefs ++ (if gp.externs then externDefs else []) ++
      (gp.defs ++ gp.inFns).map (fun d => (d.ref, d.runDef))).toArray,
    nat := some natI }

/-- The bodies to check: the helpers and every user and input definition. -/
def GProg.bodies (gp : GProg) : List Ref :=
  [consumeR, lenR, callTwiceR, idR, constR, mkKR] ++ (gp.defs ++ gp.inFns).map (·.ref)

/-- The same program with `noLeaf := false` everywhere ("drop the refinement"). -/
partial def dropNoLeafT : Term → Term
  | .lam p r rc fvs b => .lam { p with noLeaf := false } r rc fvs (dropNoLeafT b)
  | .app f a c => .app (dropNoLeafT f) (dropNoLeafT a) c
  | .letE m d v b => .letE m d (dropNoLeafT v) (dropNoLeafT b)
  | .proj s i e c => .proj s i (dropNoLeafT e) c
  | .case k mj alts ex c => .case k (dropNoLeafT mj) (alts.map dropNoLeafT) (ex.map dropNoLeafT) c
  | t => t

def dropNoLeaf (P : Prog) : Prog :=
  { P with defs := P.defs.map fun (r, d) => (r, match d with
      | .body ps res rc rs t => .body (ps.map fun p => { p with noLeaf := false }) res rc rs (dropNoLeafT t)
      | .extern ps res rc rs => .extern (ps.map fun p => { p with noLeaf := false }) res rc rs
      | .stuck ps res rc rs => .stuck (ps.map fun p => { p with noLeaf := false }) res rc rs
      | d => d) }

/-- `noLeaf := false` at the parameters `q` selects (knockouts for the recognisers). -/
partial def dropNoLeafWhereT (q : Param → Bool) : Term → Term
  | .lam p r rc fvs b => .lam (if q p then { p with noLeaf := false } else p) r rc fvs (dropNoLeafWhereT q b)
  | .app f a c => .app (dropNoLeafWhereT q f) (dropNoLeafWhereT q a) c
  | .letE m d v b => .letE m d (dropNoLeafWhereT q v) (dropNoLeafWhereT q b)
  | .proj s i e c => .proj s i (dropNoLeafWhereT q e) c
  | .case k mj alts ex c => .case k (dropNoLeafWhereT q mj) (alts.map (dropNoLeafWhereT q)) (ex.map (dropNoLeafWhereT q)) c
  | t => t

def dropNoLeafWhere (q : Param → Bool) (P : Prog) : Prog :=
  let f (p : Param) : Param := if q p then { p with noLeaf := false } else p
  { P with defs := P.defs.map fun (r, d) => (r, match d with
      | .body ps res rc rs t => .body (ps.map f) res rc rs (dropNoLeafWhereT q t)
      | .extern ps res rc rs => .extern (ps.map f) res rc rs
      | .stuck ps res rc rs => .stuck (ps.map f) res rc rs
      | d => d) }

/-! ## Externs: the oracle family -/

def allocH (h : Heap) (c : Cell) (cap : Nat) : Heap × Nat :=
  ({ h with objs := h.objs.push ⟨c, cap⟩, nextCap := max h.nextCap cap + 1 }, h.objs.size)

/-- Search cells reachable from `a` (through `Cell.vals`, i.e., `fvs` for closures) for a
`List Nat` (`consR`) value held inside a closure/pap/container, preserving its taint. -/
def capturedListOf? (h : Heap) (a : Val) : Option Val := Id.run do
  for l in reachSet h 64 a do
    let some o := objAt h l | continue
    for v in o.cell.vals do
      match v with
      | .ref loc _ _ =>
        match objAt h loc with
        | some ⟨.ctor r _, _⟩ => if r == consR then return some v
        | _ => pure ()
      | _ => pure ()
  return none

/-- Find an uncaptured reference binding in a closure's environment (outside `fvs` and not
a data field of `a`), to verify Gap A (`externCallOkB` must reject returning it). -/
def uncapturedEnvRef? (h : Heap) (a : Val) : Option Val := Id.run do
  match a with
  | .ref loc _ _ =>
    match objAt h loc with
    | some ⟨.clo env _ _ _ fvs _, _⟩ =>
      for (b, idx) in env.zipIdx do
        if fvs.contains idx then continue
        match b.val with
        | .ref l _ _ =>
          if l < h.objs.size && !dataFieldOf h a b.val then return some b.val
        | _ => pure ()
      return none
    | _ => return none
  | _ => return none

/-- The family; `fixStale` gives `exStale`'s result its cell's capability, `cleanBox`
stores `exBox`'s argument unconfined (knockouts for the recognisers). `exClo` returns
`nil` (closures are opaque under `DataFieldOf`, and `checkedOracleWith` asserts that both
uncaptured and captured closure-env refs are rejected by `externCallOkB`); `exCloU` returns
a fresh unique `List Nat`. -/
def oracleFamilyWith (fixStale cleanBox : Bool) : ExternOracle := fun r args h =>
  if r == exFresh then
    let (h', l) := allocH h (.num 42) h.nextCap
    some (h', .ref l h.nextCap [])
  else if r == exId then
    match args with
    | [a] => some (h, a)
    | _ => none
  else if r == exBox then
    match args with
    | [a] =>
      let a := if cleanBox then (match a with | .ref l c _ => .ref l c [] | v => v) else a
      let (h', l) := allocH h (.ctor sboxC #[a]) h.nextCap; some (h', .ref l h.nextCap [])
    | _ => none
  else if r == exStale then
    match args with
    | [a] => let (h', l) := allocH h (.ctor consR #[a, .imm (.con nilR)]) h.nextCap
             some (h', .ref l (if fixStale then h.nextCap else h.nextCap + 7) [])
    | _ => none
  else if r == exClo then
    match args with
    | [_] => some (h, .imm (.con nilR))
    | _ => none
  else if r == exCloU then
    match args with
    | [_] =>
      let cap0 := h.nextCap
      let (h1, lNum) := allocH h (.num 7) cap0
      let cap1 := h1.nextCap
      let (h2, lCons) := allocH h1 (.ctor consR #[.ref lNum cap0 [], .imm (.con nilR)]) cap1
      some (h2, .ref lCons cap1 [])
    | _ => none
  else none

-- MU: under repair I's statement (stmtV2) the stale member is outside `ExternOk`; it returns its cell's
-- capability instead, so its programs stay covered
def oracleFamily : ExternOracle := oracleFamilyWith stmtV2 false

/-- The family with every call decided by `externCallOkB`; a failing call is stuck
(`notCovered` re-runs with the plain family to tell it from a stuck run). Also checks
Gap A and closure opaqueness on `exClo`: both uncaptured and captured references in the
closure's env must fail `externCallOkB`. -/
def checkedOracleWith (fixStale cleanBox : Bool) (P : Prog) : ExternOracle := fun r args h =>
  match oracleFamilyWith fixStale cleanBox r args h, P.find? r with
  | some (h', v), some (.extern ps res rc rs) =>
    let cloOpaqueOk := if r == exClo then
      match args with
      | [a] =>
        let uncapOk := match uncapturedEnvRef? h a with
          | some u => !externCallOkB P ps res rc rs args h h u
          | none => true
        let capOk := match capturedListOf? h a with
          | some c => !externCallOkB P ps res rc rs args h h c
          | none => true
        uncapOk && capOk
      | _ => true
    else true
    if cloOpaqueOk && externCallOkB P ps res rc rs args h h' v then some (h', v) else none
  | _, _ => none

def checkedOracle (P : Prog) : ExternOracle := checkedOracleWith stmtV2 false P

/-! ## The generator -/

structure Cx where
  /-- the constants a body may call, with their full types -/
  callables : List (Ref × Ty)
  externs : Bool

def binderDist : List (Nat × BinderMode) :=
  [(40, .many), (12, .borrowed), (12, .unique), (6, .uniqueBorrowed), (8, .once), (4, .onceBorrowed), (8, .erased)]
def resultDist : List (Nat × ResultMode) := [(55, .shared), (15, .borrowed), (15, .unique), (15, .uniqueBorrowed)]
def letDist : List (Nat × LetMode) :=
  [(40, .value .many), (10, .value .borrowed), (12, .value .unique), (5, .value .uniqueBorrowed), (8, .value .once),
   (3, .value .onceBorrowed), (6, .value .erased), (12, .borrow)]

partial def genArrow (depth : Nat) : R Ty := do
  let a ← weighted [(50, Ty.nat), (50, .list)]
  let b ← if depth == 0 then weighted [(70, Ty.nat), (30, .list)]
    else weighted [(55, Ty.nat), (25, .list), (20, .eq .nat .nat)]
  let b ← if b == .eq .nat .nat then genArrow (depth - 1) else pure b
  let m ← weighted [(60, BinderMode.many), (12, .borrowed), (12, .unique), (4, .erased), (4, .uniqueBorrowed)]
  let r ← weighted [(70, ResultMode.shared), (10, .borrowed), (10, .unique), (10, .uniqueBorrowed)]
  -- the reader admits only default ∀s beyond a definition's λs, so a moded codomain
  -- arrow needs a shared result here (an input function then takes both parameters)
  let r := if b.isDefaultArrow then r else .shared
  pure (.arr m r a b)

def genTy : R Ty := do
  let k ← weighted [(22, 0), (22, 1), (6, 2), (5, 3), (5, 4), (4, 5), (5, 6), (5, 7), (4, 8), (20, 9), (2, 10)]
  match k with
  | 0 => pure .nat | 1 => pure .list | 2 => pure .bool | 3 => pure .box | 4 => pure .sbox
  | 5 => pure .ekey | 6 => pure .pairN | 7 => pure .pairL | 8 => pure .wrap
  | 9 => genArrow 1
  | _ => do pure (.eq (← pickL [Ty.nat, .list]) (← pickL [Ty.nat, .list]))

/-- Structures and the field a projection reads. -/
def projs : List (Ty × Ref × Nat × Ty) :=
  [(.box, boxI, 0, .list), (.sbox, sboxI, 0, .list), (.ekey, ekeyI, 1, .list), (.ekey, ekeyI, 0, .list),
   (.pairL, pairLI, 0, .list), (.pairL, pairLI, 1, .list), (.pairN, pairNI, 0, .nat), (.pairN, pairNI, 1, .nat),
   (.wrap, wrapI, 0, .nat)]

abbrev Env := List (Ty × BinderMode)

def arrowsTo (fs : List Ty) (t : Ty) : Ty := fs.foldr (fun a acc => .arr .many .shared a acc) t

mutual

/-- A term of type `t` under `env`, at depth budget `d`. -/
partial def gen (cx : Cx) (env : Env) (t : Ty) (d : Nat) : R G := do
  if t.cls == .irr then return .irr
  let vars := env.zipIdx.filter fun ((ty, m), _) => ty == t && (m != .erased || true)
  let heads := env.zipIdx.filterMap fun ((ty, _), i) =>
    let ks := (List.range (ty.arity + 1)).filter fun k => k ≥ 1 && ty.dropArrows k == some t
    if ks.isEmpty then none else some (i, ty, ks)
  let calls := cx.callables.filterMap fun (r, ty) =>
    let ks := (List.range (ty.arity + 1)).filter fun k => ty.dropArrows k == some t
    if ks.isEmpty then none else some (r, ty, ks)
  let casts := env.zipIdx.filter fun ((ty, _), _) => match ty with
    | .eq _ b => b == t
    | _ => false
  let leafy := d == 0
  let choice ← weighted ([
      (if vars.isEmpty then 0 else 30, 0),
      (if t == .nat then 8 else 0, 1),
      (if (indOf? t).isSome && t != .nat then 8 else 0, 2),
      (if calls.isEmpty || leafy then 0 else 25, 3),
      (if heads.isEmpty || leafy then 0 else 20, 4),
      (match t with | .arr .. => 25 | _ => 0, 5),
      (if leafy then 0 else 10, 6),
      (if leafy || !(projs.any (·.2.2.2 == t)) then 0 else 8, 7),
      (if leafy then 0 else 12, 8),
      (if casts.isEmpty || leafy then 0 else 6, 9),
      (if leafy then 0 else 6, 10),
      (if leafy then 2 else 0, 11)] : List (Nat × Nat))
  match choice with
  | 0 => do
    let ((ty, m), i) ← pickL vars
    -- an erased binding is read only rarely
    if m == .erased && !(← chance 20) then return leafOf t
    pure (.var i ty)
  | 1 => pure (.lit (← rand 4))
  | 2 => genCtor cx env t (d - 1)
  | 3 => do
    let (r, ty, ks) ← pickL calls
    let k ← pickL ks
    let args ← ((ty.domains k).zip (ty.domainModes k)).mapM fun (a, m) => genArg cx env a m (d - 1)
    pure (.call r args t)
  | 4 => do
    let (i, ty, ks) ← pickL heads
    let k ← pickL ks
    let args ← (ty.domains k).mapM fun a => gen cx env a (d - 1)
    pure (.appv (.var i ty) args t)
  | 5 => match t with
    | .arr m r a b => do pure (.lam m r a b (← gen cx ((a, m) :: env) b (if d == 0 then 0 else d - 1)))
    | _ => pure (leafOf t)
  | 6 => do
    let s ← genTy
    let lm ← weighted letDist
    let lm := if lm.binderMode.usage == .once && !(match s with | .arr .. => true | _ => false) then LetMode.value .many else lm
    let v ← gen cx env s (d - 1)
    let b ← gen cx ((s, lm.binderMode) :: env) t (d - 1)
    pure (.letE lm s v b)
  | 7 => do
    let ps := projs.filter (·.2.2.2 == t)
    let (sty, s, i, _) ← pickL ps
    -- the erased field of `EKey` is projected only rarely
    if sty == .ekey && i == 0 && !(← chance 15) then return leafOf t
    pure (.proj s i (← gen cx env sty (d - 1)) t)
  | 8 => genCase cx env t d
  | 9 => do
    let (_, i) ← pickL casts
    let a := match env[i]? with
      | some (.eq a _, _) => a
      | _ => t
    pure (.cast (← gen cx env a (d - 1)) t)
  | 10 => do
    -- polymorphic helpers: `id`, `const`, `mkK`
    match t with
    | .arr .many .shared .nat σ => do
      if ← chance 50 then
        return .call mkKR [.irr, .irr, ← gen cx env σ (d - 1), ← gen cx env (← genTy) (d - 1)] t
      pure (.call idR [.irr, ← gen cx env t (d - 1)] t)
    | _ => do
      if ← chance 50 then pure (.call idR [.irr, ← gen cx env t (d - 1)] t)
      else pure (.call constR [.irr, .irr, ← gen cx env t (d - 1), ← gen cx env (← genTy) (d - 1)] t)
  | _ => pure (leafOf t)

/-- An argument at a parameter of mode `m`: at an erased position, an erased variable of
its type when one is in scope (what source passes there), most of the time. -/
partial def genArg (cx : Cx) (env : Env) (a : Ty) (m : BinderMode) (d : Nat) : R G := do
  if m == .erased then
    let ev := env.zipIdx.filter fun ((ty, bm), _) => ty == a && bm == .erased
    if !ev.isEmpty && (← chance 70) then
      let (_, i) ← pickL ev
      return .var i a
  gen cx env a d

partial def genCtor (cx : Cx) (env : Env) (t : Ty) (d : Nat) : R G := do
  let some ik := indOf? t | return leafOf t
  let j ← rand ik.ctors.length
  let some c := ik.ctors[j]? | return leafOf t
  let some (nT, fs, _) := ik.shape[j]? | return leafOf t
  let args ← fs.mapM fun f => if d == 0 then pure (leafOf f) else gen cx env f (d - 1)
  pure (.call c ((List.replicate nT G.irr) ++ args) t)

partial def genCase (cx : Cx) (env : Env) (t : Ty) (d : Nat) : R G := do
  let ik ← pickL inds
  let major ← gen cx env ik.ty (d - 1)
  -- sometimes the alternatives return a function the case applies to extra arguments
  let nEx ← weighted [(75, 0), (15, 1), (10, 2)]
  let mut exTys : List Ty := []
  for _ in [0:nEx] do exTys := exTys ++ [← pickL [Ty.nat, .list]]
  let altTy := arrowsTo exTys t
  let alts ← ik.shape.mapM fun (_, fs, _) => do
    if fs.isEmpty then gen cx env altTy (d - 1)
    else if ← chance 75 then lamTele cx env fs altTy (d - 1)
    else gen cx env (arrowsTo fs altTy) (d - 1)
  let ex ← exTys.mapM fun a => gen cx env a (d - 1)
  pure (.case ik.ty major alts ex t)

/-- A λ telescope binding the fields `fs` (mostly plain binders), its body of type `t`. -/
partial def lamTele (cx : Cx) (env : Env) (fs : List Ty) (t : Ty) (d : Nat) : R G := do
  match fs with
  | [] => gen cx env t d
  | f :: rest => do
    let m ← weighted [(80, BinderMode.many), (10, .borrowed), (10, .unique)]
    let body ← lamTele cx ((f, m) :: env) rest t d
    pure (.lam m .shared f (arrowsTo rest t) body)

end

def paramCountDist : List (Nat × Nat) := [(12, 0), (23, 1), (23, 2), (17, 3), (9, 4), (8, 5), (8, 6)]

/-- Input functions: one per arrow type a seed's parameter has, one parameter,
reading it (a generated body of depth 2). -/
partial def arrowTys : Ty → List Ty
  | .arr m r a b => .arr m r a b :: arrowTys b
  | _ => []

def genProg (externs : Bool) (nDefs : Nat) (depth : Nat) : R GProg := do
  let externs := externs && (← chance 35)
  let useRecs ← chance 15
  let base : List (Ref × Ty) :=
    [(consumeR, Ty.arr .unique .shared .list .nat), (lenR, .arr .many .shared .list .nat),
     (callTwiceR, .arr .many .shared natArr .nat),
     (addP, .arr .many .shared .nat (.arr .many .shared .nat .nat))] ++
    (if useRecs then [(ekeyRecR, ekeyRecTy), (boxCasesR, boxCasesTy)] else []) ++
    (if externs then [(exFresh, Ty.arr .many .shared .nat .nat), (exId, .arr .many .shared .list .list),
      (exBox, .arr .many .shared .list .sbox), (exStale, .arr .many .shared .nat .list),
      (exClo, .arr .many .shared natArr .list), (exCloU, .arr .many .unique natArr .list)] else [])
  let mut defs : List UDef := []
  let mut callables := base
  for j in [0:nDefs] do
    let n ← weighted paramCountDist
    let mut params : List (Ty × BinderMode) := []
    for _ in [0:n] do
      let pt ← genTy
      let pm ← weighted binderDist
      -- a once mode only at a function type (a once view of data is stuck when read)
      let pm := if pm.usage == .once && !(match pt with | .arr .. => true | _ => false) then .many else pm
      params := params ++ [(pt, pm)]
    let rty ← genTy
    let rty := if rty.cls == .irr then Ty.nat else rty.defaultArrows
    let res ← weighted resultDist
    -- Hardening (V6): allow 0-parameter statics to carry non-shared result modes ~35% of the time
    -- so `anDef`'s V6 static guard is exercised directly; `selfTest` skips those (not representable in records).
    let res := if n == 0 && !(← chance 35) then ResultMode.shared else res
    let env : Env := params.reverse
    let body ← gen { callables, externs } env rty depth
    let d : UDef := { ref := userR j, params, res, rty, body }
    defs := defs ++ [d]
    callables := callables ++ [(d.ref, d.fullTy)]
  -- input functions for the arrow types at the seeds' parameters
  let mut inFns : List UDef := []
  let mut seen : List Ty := []
  for d in defs do
    for (t, _) in d.params do
      for a in arrowTys t do
        unless seen.contains a do
          seen := seen ++ [a]
          match a with
          | .arr .. => do
            let (ps, r, cod) := a.split
            let body ← gen { callables := base, externs } ps.reverse cod 2
            inFns := inFns ++ [{ ref := inFnR inFns.length, params := ps, res := r, rty := cod, body }]
          | _ => pure ()
  pure { defs, inFns, externs }

/-! ## Inputs -/

structure HB where
  objs : Array Obj := #[]

def HB.alloc (b : HB) (c : Cell) : HB × Val :=
  ({ objs := b.objs.push ⟨c, b.objs.size⟩ }, .ref b.objs.size b.objs.size [])

def HB.heap (b : HB) : Heap := { objs := b.objs, nextCap := b.objs.size }

/-- An input value of type `t` (well typed, or with fields outside their class when `ill`). -/
def genNum (b : HB) : R (HB × Val) := do pure (b.alloc (.num (← rand 5)))

partial def genList (ill : Bool) (b : HB) (n : Nat) : R (HB × Val) := do
  if n == 0 then return (b, .imm (.con nilR))
  let (b, tl) ← genList ill b (n - 1)
  let (b, hd) ← if ill && (← chance 30) then genList ill b 1 else genNum b
  pure (b.alloc (.ctor consR #[hd, tl]))

partial def genVal (gp : GProg) (ill : Bool) (b : HB) (t : Ty) : R (HB × Val) := do
  let num := genNum
  let list := genList ill
  let field (b : HB) (ft : Ty) : R (HB × Val) := do
    if ill && (← chance 30) then
      match ft with
      | .nat => list b 1
      | _ => num b
    else genVal gp ill b ft
  match t with
  | .nat | .wrap => num b
  | .bool => pure (b, .imm (.con (if ← chance 50 then trueR else falseR)))
  | .list => list b (← rand 4)
  | .box => do let (b, x) ← field b .list; pure (b.alloc (.ctor boxC #[x]))
  | .sbox => do let (b, x) ← field b .list; pure (b.alloc (.ctor sboxC #[x]))
  | .ekey => do let (b, x) ← field b .list; pure (b.alloc (.ctor ekeyC #[.imm .irr, x]))
  | .pairN => do
    let (b, x) ← field b .nat
    let (b, y) ← field b .nat
    pure (b.alloc (.ctor pairNC #[x, y]))
  | .pairL => do
    let (b, x) ← field b .list
    let (b, y) ← field b .list
    pure (b.alloc (.ctor pairLC #[x, y]))
  | .eq .. => pure (b, .imm .irr)
  | .arr .. =>
    match gp.inFns.find? (·.fullTy == t) with
    | some f => pure (b.alloc (.pap f.ref #[]))
    | none => pure (b, .imm .irr)

/-- Inputs for a seed's parameters: erased and irrelevant positions `irr`; plain
list arguments sometimes share a value with an earlier plain one. -/
def genInputs (gp : GProg) (ill : Bool) (params : List (Ty × BinderMode)) : R (Heap × List Val) := do
  let mut b : HB := {}
  let mut out : List Val := []
  let mut plainLists : List (Ty × Val) := []
  for (t, m) in params do
    if m == .erased || t.cls == .irr then
      out := out ++ [.imm .irr]
      continue
    if !m.isUnique && !plainLists.isEmpty && (← chance 20) then
      match plainLists.find? (·.1 == t) with
      | some (_, v) => out := out ++ [v]; continue
      | none => pure ()
    let (b', v) ← genVal gp ill b t
    b := b'
    out := out ++ [v]
    if !m.isUnique then plainLists := plainLists ++ [(t, v)]
  pure (b.heap, out)

/-! ## Record-level differential testing (Ixon v5 records, raw recursors, case shapes, run tables)

Covers the documented generator blind spots outside `Prog`:
- real Ixon v5 records with binder-data sections (`withSection`), sharing tables, `allDefault`,
  `readProg`, `RespectsErasure`, and `check` + `runR`;
- raw recursors with randomized constructor/minor erasure, field permutations/duplications,
  subsingleton flag, partial/saturated calls, and transitive mutual rule calls (V1 & V3);
- `casesOn` matchers with and without sharing in minor/outer spines, erased positions, and
  under-applied calls (V3 & V8);
- definitions with parameterless statics, telescopes through sharing (V2), `Subject.runTable`
  (`f.eq_def` and `And` conjunctions), V4 malformed-record guards, and V7 recursive `L`. -/

structure RecEnv where
  table : Ix.Kernel.RoleTable
  store : Ix.Kernel.Reader.Store
  blob : Address → Option ByteArray
  natA : Address
  eqA : Address
  andA : Address

def dtAddr (k : Nat) : Address := ⟨⟨#[k.toUInt8, 0x72, 0x63]⟩⟩

def dtWithSection (c : Ixon.Constant) (mode : Bool → Nat → Nat → AllMode := fun _ _ _ => {}) :
    Ixon.Constant := Id.run do
  let full := Ixon.binderfulEntries c.sharing
  let undecided := c.info.uncheckedSafety
  let nodesOf (sh : Bool) (idx : Nat) (shape : Array (Option Nat)) : Array BinderNode :=
    shape.zipIdx.map fun (k, o) => match k with
      | none => if undecided then .undecided (mode sh idx o) else .never (mode sh idx o)
      | some _ => .share 0
  let mut roots : Array BinderBlock := #[]
  let mut todo : List Nat := []
  for (e, r) in c.info.binderRoots.zipIdx do
    let shape := e.numberedNodes full #[]
    if shape.isEmpty then continue
    roots := roots.push { shared := false, index := r.toUInt64, variant := 0, nodes := nodesOf false r shape }
    todo := todo ++ shape.toList.filterMap id
  let mut seen : Array Bool := Array.replicate c.sharing.size false
  let mut entries : Array BinderBlock := #[]
  for _ in [0:c.sharing.size + 1] do
    let mut next : List Nat := []
    for n in todo do
      if seen[n]?.getD true then continue
      seen := seen.set! n true
      let shape := (c.sharing[n]?.getD (.sort 0)).numberedNodes full #[]
      entries := entries.push { shared := true, index := n.toUInt64, variant := 0, nodes := nodesOf true n shape }
      next := next ++ shape.toList.filterMap id
    todo := next
  return { c with binders := roots ++ entries.qsort (·.index < ·.index) }

def dtApp (f : Ixon.Expr) (as : List Ixon.Expr) : Ixon.Expr := as.foldl .app f
def dtRef (i : Nat) (us : Array UInt64 := #[]) : Ixon.Expr := .ref i.toUInt64 us
def dtVar (i : Nat) : Ixon.Expr := .var i.toUInt64
def dtAlls (doms : List Ixon.Expr) (body : Ixon.Expr) : Ixon.Expr := doms.foldr .all body
def dtLams (doms : List Ixon.Expr) (body : Ixon.Expr) : Ixon.Expr := doms.foldr .lam body
def dtProjI (b : Address) (i : Nat) : Ixon.Constant :=
  { info := .iPrj { idx := i.toUInt64, block := b }, sharing := #[], refs := #[], univs := #[] }
def dtProjC (b : Address) (i ci : Nat) : Ixon.Constant :=
  { info := .cPrj { idx := i.toUInt64, cidx := ci.toUInt64, block := b }, sharing := #[], refs := #[], univs := #[] }
def dtSafeDef (typ value : Ixon.Expr) (lvls : Nat := 0) : Ixon.Definition :=
  { kind := Ix.DefKind.defn, safety := Ix.DefinitionSafety.safe, lvls := lvls.toUInt64, typ, value }
def dtModeAt (marks : List (Nat × Nat × AllMode)) : Bool → Nat → Nat → AllMode := fun sh idx o =>
  if sh then {} else ((marks.find? fun (r, n, _) => r == idx && n == o).map (·.2.2)).getD {}
def dtErasedM : AllMode := { input := .erased }

/-- `RespectsErasure`, decided over a read program's constants. -/
def dtRespectsErasure (s : Subject) (P : Prog) : Bool :=
  P.defs.all fun (r, d) =>
    match d.suppliedReads with
    | none => true
    | some reads =>
      match ifaceErased s r with
      | .ok es => es.all fun i => !reads i
      | .error _ => false

def dtSubj (re : RecEnv) (extra : List (Address × Ixon.Constant)) (seeds : List Address)
    (rt : List Address := []) : Subject :=
  { table := re.table,
    store := fun a => (extra.find? (·.1 == a)).map (·.2) <|> re.store a,
    blob := re.blob, seeds, runTable := rt }

/-- Result of one randomized record-level check: `(accepted, optional failure diagnostic)`. -/
structure RecOutcome where
  accepted : Bool
  err : Option String := none

/-- Check `allDefault`/`readProg`/`RespectsErasure`/`check` consistency + `runR` safety on a
record subject with a static (0-arg) or typed-input entry. -/
def checkRecordSubject (s : Subject) (entry : Address) (runInputs : List (Heap × List Val)) : RecOutcome :=
  let ad := allDefault s
  let cl := oracleClassifier Ix.Kernel.Env.empty (ctorShapes (Reading.make s)) {}
  let rp := readProg s cl
  let v := check {} Ix.Kernel.Env.empty s
  match ad, v with
  | .ok true, .accept 0 true =>
    match rp with
    | .error e => { accepted := true, err := some s!"allDefault=true + fast-path accept, but readProg fails: {e}" }
    | .ok P =>
      if !dtRespectsErasure s P then { accepted := true, err := some "RespectsErasure false on fast-path accept" }
      else { accepted := true }
  | .ok true, _ =>
    { accepted := v.isAccept, err := some s!"allDefault=ok true but check did not fast-path accept" }
  | _, _ =>
    match v with
    | .accept .. =>
      match rp with
      | .error e => { accepted := true, err := some s!"check accepted but readProg failed: {e}" }
      | .ok P =>
        if !dtRespectsErasure s P then { accepted := true, err := some "RespectsErasure false on accepted subject" }
        else Id.run do
          let some er := Ix.Kernel.Reader.resolve s.store entry
            | return { accepted := true, err := some "entry does not resolve" }
          for (h, args) in runInputs do
            match P.find? er with
            | some (.body ps ..) =>
              if inputsOkB P h ps args then
                for f in [0, 10, 50, 1000] do
                  match runR P (fun _ _ _ => none) f er h args with
                  | .violation k =>
                    return { accepted := true, err := some s!"RECORD COUNTEREXAMPLE: violation {repr k} at fuel {f}" }
                  | _ => pure ()
            | _ => pure ()
          return { accepted := true }
    | .refuse .. =>
      match rp with
      | .ok P =>
        if !dtRespectsErasure s P then { accepted := false, err := some "RespectsErasure false on read program" }
        else { accepted := false }
      | .error _ => { accepted := false }
    | .decline r => { accepted := false, err := some s!"unexpected decline on finite record subject: {r}" }

/-- Family A: randomized raw recursor records over `K | mk (a b c : Nat)` (V1 & V3). -/
def genRecFamilyA (re : RecEnv) : R RecOutcome := do
  let e0 ← chance 40; let e1 ← chance 50; let e2 ← chance 40
  let m0 ← if e0 then chance 65 else chance 15
  let m1 ← if e1 then chance 65 else chance 15
  let m2 ← if e2 then chance 65 else chance 15
  let perm ← pickL [#[2, 1, 0], #[2, 1, 0], #[2, 0, 1], #[2, 1, 1], #[1, 2, 0]]
  let isK ← chance 30
  let nargs ← weighted [(15, 0), (15, 2), (70, 3)]
  let nat := dtRef 0
  let ctorMarks : List (Nat × Nat × AllMode) :=
    (if e0 then [(1, 0, dtErasedM)] else []) ++
    (if e1 then [(1, 1, dtErasedM)] else []) ++
    (if e2 then [(1, 2, dtErasedM)] else [])
  let ind : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0,
      typ := if isK then .sort 0 else .sort 1,
      ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 3,
                   typ := dtAlls [nat, nat, nat] (.recur 0 #[]) }] }
  let block := dtWithSection
    { info := .muts #[.indc ind], sharing := #[], refs := #[re.natA], univs := #[.zero, .succ .zero] }
    (dtModeAt ctorMarks)
  -- K.rec: refs natA, K, K.mk
  let motive := Ixon.Expr.all (dtRef 1) (.sort 0)
  let minor := dtAlls [nat, nat, nat] (.app (dtVar 3) (dtApp (dtRef 2) [dtVar 2, dtVar 1, dtVar 0]))
  let typ := dtAlls [motive, minor, dtRef 1] (.app (dtVar 2) (dtVar 0))
  let rhs := dtLams [motive, minor, nat, nat, nat]
    (dtApp (dtVar 3) [dtVar perm[0]!, dtVar perm[1]!, dtVar perm[2]!])
  let rr : Ixon.Recursor :=
    { k := isK, isUnsafe := false, lvls := 1, params := 0, indices := 0, motives := 1, minors := 1,
      typ, rules := #[{ fields := 3, rhs }] }
  let minorMarks : List (Nat × Nat × AllMode) :=
    (if m0 then [(0, 3, dtErasedM)] else []) ++
    (if m1 then [(0, 4, dtErasedM)] else []) ++
    (if m2 then [(0, 5, dtErasedM)] else [])
  let kRec := dtWithSection
    { info := .recr rr, sharing := #[], refs := #[re.natA, dtAddr 2, dtAddr 3], univs := #[.var 0] }
    (dtModeAt minorMarks)
  -- Caller `useK`: nargs = 3 (saturated), 2 (partial), or 0 (unapplied argument)
  let useK :=
    if nargs == 3 then
      let bodyMarks := (if m0 then [(1, 2, dtErasedM)] else []) ++
        (if m1 then [(1, 3, dtErasedM)] else []) ++ (if m2 then [(1, 4, dtErasedM)] else [])
      dtWithSection
        { info := .defn (dtSafeDef (.all (dtRef 1) nat)
            (.lam (dtRef 1) (dtApp (dtRef 2 #[0]) [.lam (dtRef 1) nat, dtLams [nat, nat, nat] (dtVar 2), dtVar 0]))),
          sharing := #[], refs := #[re.natA, dtAddr 2, dtAddr 4], univs := #[.succ .zero] }
        (dtModeAt bodyMarks)
    else if nargs == 2 then
      let bodyMarks := (if m0 then [(1, 2, dtErasedM)] else []) ++
        (if m1 then [(1, 3, dtErasedM)] else []) ++ (if m2 then [(1, 4, dtErasedM)] else [])
      dtWithSection
        { info := .defn (dtSafeDef (.all nat (.all (dtRef 1) nat))
            (.lam nat (dtApp (dtRef 2 #[0]) [.lam (dtRef 1) nat, dtLams [nat, nat, nat] (dtVar 3)]))),
          sharing := #[], refs := #[re.natA, dtAddr 2, dtAddr 4], univs := #[.succ .zero] }
        (dtModeAt bodyMarks)
    else
      let gDom := Ixon.Expr.all typ nat
      let gMarks := (if m0 then [(0, 5, dtErasedM), (1, 5, dtErasedM)] else []) ++
        (if m1 then [(0, 6, dtErasedM), (1, 6, dtErasedM)] else []) ++
        (if m2 then [(0, 7, dtErasedM), (1, 7, dtErasedM)] else [])
      dtWithSection
        { info := .defn (dtSafeDef (.all gDom nat) (.lam gDom (.app (dtVar 0) (dtRef 3 #[0])))),
          sharing := #[], refs := #[re.natA, dtAddr 2, dtAddr 3, dtAddr 4], univs := #[.succ .zero] }
        (dtModeAt gMarks)
  let extra := [(dtAddr 1, block), (dtAddr 2, dtProjI (dtAddr 1) 0), (dtAddr 3, dtProjC (dtAddr 1) 0 0),
                (dtAddr 4, kRec), (dtAddr 5, useK)]
  let s := dtSubj re extra [dtAddr 5]
  -- Ground-truth V1 + V3 oracle
  let eFlags := #[e0, e1, e2]
  let mFlags := #[m0, m1, m2]
  let anyErased := e0 || e1 || e2
  let v1Ok := (List.range 3).all fun q =>
    !eFlags[q]! || (mFlags[q]! && perm[q]! == 2 - q &&
      (List.range 3).all fun p => p == q || perm[p]! != 2 - q)
  let v3Ok := !anyErased || nargs == 3
  -- Also note: in `useK` for nargs ∈ {2,3}, minor body returns `var 2` (field 0 `a`) or `var 3` (outer param)
  let bodyReadsErased := nargs == 3 && m0
  let expectReadOk := v1Ok && v3Ok
  let expectAccept := expectReadOk && !bodyReadsErased
  let rp := readProg s noClasses
  let v := check {} Ix.Kernel.Env.empty s
  let readOk := match rp with | .ok _ => true | .error _ => false
  if readOk != expectReadOk then
    return { accepted := v.isAccept, err := some s!"Family A V1/V3 read mismatch: e={eFlags} m={mFlags} perm={perm} nargs={nargs} expected readOk={expectReadOk} got {readOk}" }
  if v.isAccept != expectAccept then
    return { accepted := v.isAccept, err := some s!"Family A V1/V3 check mismatch: e={eFlags} m={mFlags} perm={perm} nargs={nargs} expected accept={expectAccept} got {v.isAccept}" }
  if let .ok P := rp then
    if !dtRespectsErasure s P then
      return { accepted := v.isAccept, err := some "Family A RespectsErasure failed" }
  return { accepted := v.isAccept }

/-- Family B: randomized `casesOn` matchers with/without sharing, erased positions, under-application (V3 & V8). -/
def genRecFamilyB (re : RecEnv) : R RecOutcome := do
  let kind ← weighted [(40, 0), (15, 1), (15, 2), (15, 3), (15, 4)]
  -- 0: identity (2,1,0); 1: perm (0,1,2); 2: dup (2,2,0); 3: outer var (4,1,0); 4: non-var (ref 0)
  let (a0, a1, a2) : Ixon.Expr × Ixon.Expr × Ixon.Expr := match kind with
    | 0 => (dtVar 2, dtVar 1, dtVar 0)
    | 1 => (dtVar 0, dtVar 1, dtVar 2)
    | 2 => (dtVar 2, dtVar 2, dtVar 0)
    | 3 => (dtVar 4, dtVar 1, dtVar 0)
    | _ => (dtVar 2, dtVar 1, dtRef 0)
  let erasePos ← weighted [(55, (none : Option Nat)), (15, some 0), (15, some 1), (15, some 2)]
  let underApp ← chance 30
  let outerShared ← chance 50
  let modedCaller ← chance 50
  let nat := dtRef 0
  let ind : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
      ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 3,
                   typ := dtAlls [nat, nat, nat] (.recur 0 #[]) }] }
  let block := dtWithSection
    { info := .muts #[.indc ind], sharing := #[], refs := #[re.natA], univs := #[.succ .zero] }
  let motive := Ixon.Expr.all (dtRef 1) (.sort 0)
  let minorTy := dtAlls [nat, nat, nat] (.app (dtVar 3) (dtApp (dtRef 2) [dtVar 2, dtVar 1, dtVar 0]))
  let recTyp := dtAlls [motive, minorTy, dtRef 1] (.app (dtVar 2) (dtVar 0))
  let recRhs := dtLams [motive, minorTy, nat, nat, nat] (dtApp (dtVar 3) [dtVar 2, dtVar 1, dtVar 0])
  let kRec := dtWithSection
    { info := .recr { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0,
                      motives := 1, minors := 1, typ := recTyp, rules := #[{ fields := 3, rhs := recRhs }] },
      sharing := #[], refs := #[re.natA, dtAddr 12, dtAddr 13], univs := #[.var 0] }
  -- K.casesOn (motive) (t : K) (m : Nat → Nat → Nat → motive t): nodes 0=motive(inner 1), 2=t, 3=m
  let cM := dtAlls [nat, nat, nat] (.app (dtVar 4) (dtApp (dtRef 2) [dtVar 2, dtVar 1, dtVar 0]))
  let cDoms := [motive, dtRef 1, cM]
  let cMarks : List (Nat × Nat × AllMode) := match erasePos with
    | some 0 => [(0, 0, dtErasedM), (1, 0, dtErasedM)]
    | some 1 => [(0, 2, dtErasedM), (1, 2, dtErasedM)]
    | some 2 => [(0, 3, dtErasedM), (1, 3, dtErasedM)]
    | _ => []
  let mkCases (shared : Bool) : Ixon.Constant :=
    let mPre := dtApp (dtVar 3) [a0, a1]
    let mBody := if shared then .app (.share 0) a2 else .app mPre a2
    let minor := dtLams [nat, nat, nat] mBody
    let oPre := dtApp (dtRef 3 #[0]) [dtVar 2]
    let oBody := if shared && outerShared then dtApp (.share 1) [minor, dtVar 1]
                 else dtApp oPre [minor, dtVar 1]
    let sh := (if shared then #[mPre] else #[]) ++ (if shared && outerShared then #[oPre] else #[])
    dtWithSection
      { info := .defn (dtSafeDef (dtAlls cDoms (.app (dtVar 2) (dtVar 1))) (dtLams cDoms oBody) 1),
        sharing := sh, refs := #[re.natA, dtAddr 12, dtAddr 13, dtAddr 14], univs := #[.var 0] }
      (dtModeAt cMarks)
  let callerMarks : List (Nat × Nat × AllMode) :=
    if modedCaller then [(0, 0, { input := .borrowed }), (1, 0, { input := .borrowed })] else []
  let mkUse (casesA : Address) : Ixon.Constant :=
    if underApp then
      dtWithSection
        { info := .defn (dtSafeDef (.all (dtRef 1) (.all (dtAlls [nat, nat, nat] nat) nat))
            (.lam (dtRef 1) (dtApp (dtRef 2 #[0]) [.lam (dtRef 1) nat, dtVar 0]))),
          sharing := #[], refs := #[re.natA, dtAddr 12, casesA], univs := #[.succ .zero] }
        (dtModeAt callerMarks)
    else
      dtWithSection
        { info := .defn (dtSafeDef (.all (dtRef 1) nat)
            (.lam (dtRef 1) (dtApp (dtRef 2 #[0]) [.lam (dtRef 1) nat, dtVar 0, dtLams [nat, nat, nat] (dtVar 2)]))),
          sharing := #[], refs := #[re.natA, dtAddr 12, casesA], univs := #[.succ .zero] }
        (dtModeAt callerMarks)
  let common := [(dtAddr 11, block), (dtAddr 12, dtProjI (dtAddr 11) 0),
                 (dtAddr 13, dtProjC (dtAddr 11) 0 0), (dtAddr 14, kRec)]
  let sU := dtSubj re (common ++ [(dtAddr 15, mkCases false), (dtAddr 16, mkUse (dtAddr 15))]) [dtAddr 16]
  let sS := dtSubj re (common ++ [(dtAddr 17, mkCases true), (dtAddr 18, mkUse (dtAddr 17))]) [dtAddr 18]
  let shU := caseShape sU #[] 16 (.member (dtAddr 15) 0)
  let shS := caseShape sS #[] 16 (.member (dtAddr 17) 0)
  if shU != shS then
    return { accepted := false, err := some s!"Family B V8 sharing divergence: kind={kind} unshared={repr shU} shared={repr shS}" }
  let expectShape := kind == 0 || kind == 1
  if shU.isSome != expectShape then
    return { accepted := false, err := some s!"Family B caseShape mismatch: kind={kind} expected {expectShape} got {repr shU}" }
  let vU := check {} Ix.Kernel.Env.empty sU
  let vS := check {} Ix.Kernel.Env.empty sS
  if vU.isAccept != vS.isAccept then
    return { accepted := false, err := some s!"Family B V8 verdict divergence: kind={kind} erase={erasePos} under={underApp}" }
  if expectShape && (erasePos == some 1 || erasePos == some 2) && vS.isAccept then
    return { accepted := true, err := some s!"Family B accepted erased major/alt on caseDef" }
  -- When non-default modes are present (`allDefault == false`), slow-path `anCall` must refuse
  -- under-applied `caseDef` (V3). When all modes are default (`erasePos == none && !modedCaller`),
  -- `check` validly takes the all-default fast path.
  if expectShape && (erasePos == some 0 || (erasePos == none && modedCaller)) && underApp && vS.isAccept then
    return { accepted := true, err := some s!"Family B accepted under-applied caseDef (V3, erase={erasePos}, modedCaller={modedCaller})" }
  return { accepted := vS.isAccept }

/-- Family C: randomized v5 definitions (0..2 params, modes, telescope sharing V2, `runTable`
`f.eq_def` & `And`, V4 malformed records) checked end-to-end with `check` and `runR`. -/
def genRecFamilyC (re : RecEnv) : R RecOutcome := do
  -- `E | c0 | c1` (21..24) and `B | mk (x : E)` / `L | nil | cons (h : E) (t : L)` (25..28)
  let eInd : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
      ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := .recur 0 #[] },
                 { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 0, typ := .recur 0 #[] }] }
  let lInd : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
      ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := .recur 0 #[] },
                 { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 2,
                   typ := dtAlls [dtRef 0, .recur 0 #[]] (.recur 0 #[]) }] }
  let eBlk := dtWithSection { info := .muts #[.indc eInd], sharing := #[], refs := #[], univs := #[.succ .zero] }
  let lBlk := dtWithSection { info := .muts #[.indc lInd], sharing := #[], refs := #[dtAddr 22], univs := #[.succ .zero] }
  let baseRecs := [(dtAddr 21, eBlk), (dtAddr 22, dtProjI (dtAddr 21) 0),
                   (dtAddr 23, dtProjC (dtAddr 21) 0 0), (dtAddr 24, dtProjC (dtAddr 21) 0 1),
                   (dtAddr 25, lBlk), (dtAddr 26, dtProjI (dtAddr 25) 0),
                   (dtAddr 27, dtProjC (dtAddr 25) 0 0), (dtAddr 28, dtProjC (dtAddr 25) 0 1)]
  -- 15% V4 malformed record test (incomplete binder section or theorem with DefAsserts)
  if ← chance 15 then
    let bad :=
      if ← chance 50 then
        ({ info := .axio ⟨false, 0, .all (.sort 0) (.sort 0)⟩, sharing := #[], refs := #[], univs := #[.zero] } : Ixon.Constant)
      else
        { info := .defn { kind := Ix.DefKind.thm, safety := Ix.DefinitionSafety.safe,
                          asserts := { boundedStack := true }, lvls := 0, typ := .sort 0, value := .sort 0 },
          sharing := #[], refs := #[], univs := #[.zero] }
    let s := dtSubj re [(dtAddr 30, bad)] [dtAddr 30]
    let ad := allDefault s
    let v := check {} Ix.Kernel.Env.empty s
    let adErr := match ad with | .error _ => true | .ok _ => false
    if !adErr || v.isAccept then
      return { accepted := v.isAccept, err := some s!"Family C V4 malformed record not rejected" }
    return { accepted := false }
  -- Normal definition `f` with n ∈ {0, 1, 2} params over `L`, random modes, optional telescope sharing, optional runTable
  let n ← weighted [(25, 0), (45, 1), (30, 2)]
  let m0 ← pickL [BinderMode.many, .borrowed, .unique, .erased]
  let m1 ← pickL [BinderMode.many, .borrowed, .unique, .erased]
  let rMode ← if n == 0 then pure ResultMode.shared else pickL [ResultMode.shared, .borrowed, .unique]
  let shareTele ← chance 40
  let bodyKind ← rand 4  -- 0: L.nil, 1: var 0, 2: L.cons E.c0 (var 0), 3: var 1 (when n=2)
  let useRT ← chance 45
  let shareEq ← chance 40
  let dupFlag ← chance 15
  let dupRT := useRT && dupFlag
  -- refs for f: 0=L, 1=L.nil, 2=L.cons, 3=E.c0
  let bodyExpr : Ixon.Expr :=
    if n == 0 then dtApp (dtRef 2) [dtRef 3, dtRef 1]
    else match bodyKind with
      | 0 => dtRef 1
      | 1 => dtVar 0
      | 2 => dtApp (dtRef 2) [dtRef 3, dtVar 0]
      | _ => if n == 2 then dtVar 1 else dtVar 0
  let fRec : Ixon.Constant :=
    if n == 0 then
      dtWithSection { info := .defn (dtSafeDef (dtRef 0) bodyExpr),
                      sharing := #[], refs := #[dtAddr 26, dtAddr 27, dtAddr 28, dtAddr 23], univs := #[] }
    else if n == 1 then
      let md : AllMode := { input := m0, result := rMode }
      dtWithSection { info := .defn (dtSafeDef (.all (dtRef 0) (dtRef 0)) (.lam (dtRef 0) bodyExpr)),
                      sharing := #[], refs := #[dtAddr 26, dtAddr 27, dtAddr 28, dtAddr 23], univs := #[] }
        (dtModeAt [(0, 0, md), (1, 0, md)])
    else
      let md0 : AllMode := { input := m0, result := .shared }
      let md1 : AllMode := { input := m1, result := rMode }
      if shareTele then
        dtWithSection
          { info := .defn (dtSafeDef (.all (dtRef 0) (.share 0)) (.lam (dtRef 0) (.share 1))),
            sharing := #[.all (dtRef 0) (dtRef 0), .lam (dtRef 0) bodyExpr],
            refs := #[dtAddr 26, dtAddr 27, dtAddr 28, dtAddr 23], univs := #[] }
          (fun sh _ o => if !sh && o == 0 then md0 else if sh && o == 0 then md1 else {})
      else
        dtWithSection
          { info := .defn (dtSafeDef (.all (dtRef 0) (.all (dtRef 0) (dtRef 0))) (.lam (dtRef 0) (.lam (dtRef 0) bodyExpr))),
            sharing := #[], refs := #[dtAddr 26, dtAddr 27, dtAddr 28, dtAddr 23], univs := #[] }
          (dtModeAt [(0, 0, md0), (0, 1, md1), (1, 0, md0), (1, 1, md1)])
  -- Optional f.eq_def theorem record (refs: 0=L, 1=L.nil, 2=L.cons, 3=E.c0, 4=Eq, 5=f)
  let eqRhsKind ← rand 3
  let eqRhs : Ixon.Expr :=
    if n == 0 then dtApp (dtRef 2) [dtRef 3, dtRef 1]
    else match eqRhsKind with
      | 0 => dtRef 1
      | 1 => dtVar 0
      | _ => dtApp (dtRef 2) [dtRef 3, dtVar 0]
  let lhs := dtApp (dtRef 5) ((List.range n).map fun i => dtVar (n - 1 - i))
  let eqPre := dtApp (dtRef 4 #[0]) [dtRef 0, lhs]
  let eqBody := if shareEq then .app (.share 0) eqRhs else .app eqPre eqRhs
  let eqTyp := dtAlls (List.replicate n (dtRef 0)) eqBody
  let eqRec := dtWithSection
    { info := .defn { kind := Ix.DefKind.thm, safety := Ix.DefinitionSafety.safe, lvls := 0,
                      typ := eqTyp, value := .sort 0 },
      sharing := if shareEq then #[eqPre] else #[],
      refs := #[dtAddr 26, dtAddr 27, dtAddr 28, dtAddr 23, re.eqA, dtAddr 31],
      univs := #[.succ .zero] }
  let eqRec2 := eqRec
  let rtList := if !useRT then [] else if dupRT then [dtAddr 32, dtAddr 33] else [dtAddr 32]
  let recs := baseRecs ++ [(dtAddr 31, fRec)] ++ (if useRT then [(dtAddr 32, eqRec), (dtAddr 33, eqRec2)] else [])
  let s := dtSubj re recs [dtAddr 31] rtList
  if dupRT then
    let v := check {} Ix.Kernel.Env.empty s
    if v.isAccept then return { accepted := true, err := some "Family C accepted duplicate runTable binding" }
    return { accepted := false }
  -- Build an admissible input heap for `f` (fresh L.cons E.c0 L.nil per non-erased param)
  let mkIn : Heap × List Val := Id.run do
    let mut b : HB := {}
    let mut args : List Val := []
    let ms := if n == 0 then [] else if n == 1 then [m0] else [m0, m1]
    for m in ms do
      if m == .erased then args := args ++ [.imm .irr]
      else
        let (b', v) := b.alloc (.ctor (.ctor (dtAddr 25) 0 1) #[.imm (.con (.ctor (dtAddr 21) 0 0)), .imm (.con (.ctor (dtAddr 25) 0 0))])
        b := b'; args := args ++ [v]
    return (b.heap, args)
  return checkRecordSubject s (dtAddr 31) [mkIn]

/-- Family D: randomized recursive `L` + `L.casesOn` (V7 oracle path + V8 sharing). -/
def genRecFamilyD (re : RecEnv) : R RecOutcome := do
  let shared ← chance 50
  let m ← pickL [BinderMode.many, .borrowed, .unique, .erased]
  let eInd : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
      ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := .recur 0 #[] },
                 { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 0, typ := .recur 0 #[] }] }
  let lInd : Ixon.Inductive :=
    { isUnsafe := false, lvls := 0, params := 0, indices := 0, typ := .sort 0,
      ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0, typ := .recur 0 #[] },
                 { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 2,
                   typ := dtAlls [dtRef 0, .recur 0 #[]] (.recur 0 #[]) }] }
  let eBlk := dtWithSection { info := .muts #[.indc eInd], sharing := #[], refs := #[], univs := #[.succ .zero] }
  let lBlk := dtWithSection { info := .muts #[.indc lInd], sharing := #[], refs := #[dtAddr 42], univs := #[.succ .zero] }
  let motive := Ixon.Expr.all (dtRef 0) (.sort 0)
  let mnil := Ixon.Expr.app (dtVar 0) (dtRef 1)
  let mcons := dtAlls [dtRef 3, dtRef 0, .app (dtVar 3) (dtVar 0)] (.app (dtVar 4) (dtApp (dtRef 2) [dtVar 2, dtVar 1]))
  let pre := [motive, mnil, mcons]
  let lRecR : Ixon.Recursor :=
    { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0, motives := 1, minors := 2,
      typ := dtAlls (pre ++ [dtRef 0]) (.app (dtVar 3) (dtVar 0)),
      rules := #[{ fields := 0, rhs := dtLams pre (dtVar 1) },
                 { fields := 2, rhs := dtLams (pre ++ [dtRef 3, dtRef 0])
                     (dtApp (dtVar 2) [dtVar 1, dtVar 0, dtApp (.recur 0 #[0]) [dtVar 4, dtVar 3, dtVar 2, dtVar 0]]) }] }
  let lRec := dtWithSection
    { info := .recr lRecR, sharing := #[], refs := #[dtAddr 46, dtAddr 47, dtAddr 48, dtAddr 42], univs := #[.var 0] }
  let cMnil := Ixon.Expr.app (dtVar 1) (dtRef 1)
  let cMcons := dtAlls [dtRef 3, dtRef 0] (.app (dtVar 4) (dtApp (dtRef 2) [dtVar 1, dtVar 0]))
  let cDoms := [motive, dtRef 0, cMnil, cMcons]
  let mPre := Ixon.Expr.app (dtVar 3) (dtVar 2)
  let mBody := if shared then .app (.share 0) (dtVar 1) else .app mPre (dtVar 1)
  let minorCons := dtLams [dtRef 3, dtRef 0, .app (dtVar 5) (dtVar 0)] mBody
  let lCases := dtWithSection
    { info := .defn (dtSafeDef (dtAlls cDoms (.app (dtVar 3) (dtVar 2)))
        (dtLams cDoms (dtApp (dtRef 4 #[0]) [dtVar 3, dtVar 1, minorCons, dtVar 2])) 1),
      sharing := if shared then #[mPre] else #[],
      refs := #[dtAddr 46, dtAddr 47, dtAddr 48, dtAddr 42, dtAddr 49], univs := #[.var 0] }
  let lMode : AllMode := { input := m }
  let headOr := dtWithSection
    { info := .defn (dtSafeDef (dtAlls [dtRef 0, dtRef 1] (dtRef 0))
        (dtLams [dtRef 0, dtRef 1] (dtApp (dtRef 2 #[0]) [.lam (dtRef 1) (dtRef 0), dtVar 0, dtVar 1,
          dtLams [dtRef 0, dtRef 1] (dtVar 1)]))),
      sharing := #[], refs := #[dtAddr 42, dtAddr 46, dtAddr 50], univs := #[.succ .zero] }
    (dtModeAt [(0, 1, lMode), (1, 1, lMode)])
  let mainL := dtWithSection
    { info := .defn (dtSafeDef (dtRef 5) (dtApp (dtRef 0) [dtRef 1, dtApp (dtRef 2) [dtRef 3, dtRef 4]])),
      sharing := #[], refs := #[dtAddr 51, dtAddr 43, dtAddr 48, dtAddr 44, dtAddr 47, dtAddr 42], univs := #[] }
  let recs := [(dtAddr 41, eBlk), (dtAddr 42, dtProjI (dtAddr 41) 0),
               (dtAddr 43, dtProjC (dtAddr 41) 0 0), (dtAddr 44, dtProjC (dtAddr 41) 0 1),
               (dtAddr 45, lBlk), (dtAddr 46, dtProjI (dtAddr 45) 0),
               (dtAddr 47, dtProjC (dtAddr 45) 0 0), (dtAddr 48, dtProjC (dtAddr 45) 0 1),
               (dtAddr 49, lRec), (dtAddr 50, lCases), (dtAddr 51, headOr), (dtAddr 52, mainL)]
  let s := dtSubj re recs [dtAddr 52]
  let v := check {} Ix.Kernel.Env.empty s
  if m == .erased then
    if v.isAccept then return { accepted := true, err := some "Family D accepted erased major in headOr" }
    return { accepted := false }
  if !v.isAccept then
    return { accepted := false, err := some s!"Family D V7/V8 failed to accept recursive L (m={repr m}, shared={shared})" }
  let cl := oracleClassifier Ix.Kernel.Env.empty (ctorShapes (Reading.make s)) {}
  match readProg s cl with
  | .error e => return { accepted := true, err := some s!"Family D readProg failed: {e}" }
  | .ok P =>
    match runR P (fun _ _ _ => none) 100000 (.member (dtAddr 52) 0) {} [] with
    | .value (.imm (.con r)) _ =>
      if r == .ctor (dtAddr 41) 0 1 then return { accepted := true }
      else return { accepted := true, err := some s!"Family D wrong value {repr r}" }
    | _ => return { accepted := true, err := some s!"Family D did not evaluate to E.c1 (got non-value)" }

def genRecordCase (re : RecEnv) : R RecOutcome := do
  match ← rand 4 with
  | 0 => genRecFamilyA re
  | 1 => genRecFamilyB re
  | 2 => genRecFamilyC re
  | _ => genRecFamilyD re

end MT.DiffTest
