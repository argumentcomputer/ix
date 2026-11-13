import IxC.Resource
import DiffTest.Hyp

/-! # The generator (MT): a typed universe, its run program, programs and inputs

Classes, skeletons and `noLeaf` of a type are computed in one place (`Ty.cls`,
`Ty.skel`, `Ty.noLeaf`), by the canonical classes and by the reader's own rules
(`noLeafType`: a function type, a sort, an inductive with other than one
constructor; `readSkel`: an inductive applied to arguments is `dataApp`). The
self-test in `Main` compares the interfaces built here with the reader's
functions on Ixon records of the same types. -/

namespace MT.DiffTest

open IxC.Resource Ixon

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
def exFresh := memR 30
def exId := memR 31
def exBox := memR 32
def exStale := memR 33

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
    (.lam (Ty.nat.param .many) .shared .val #[1] (.var 2 .val)))]

def externDefs : List (Ref × RunDef) := [
  (exFresh, .extern #[Ty.nat.param .many] .shared .leaf .data),
  (exId, .extern #[Ty.list.param .many] .shared .val Ty.list.skel),
  (exBox, .extern #[Ty.list.param .many] .shared .val .data),
  (exStale, .extern #[Ty.nat.param .many] .shared .val Ty.list.skel)]

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

/-- The family; `fixStale` gives `exStale`'s result its cell's capability, `cleanBox`
stores `exBox`'s argument unconfined (knockouts for the recognisers). -/
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
  else none

-- MU: under repair I's statement (stmtV2) the stale member is outside `ExternOk`; it returns its cell's
-- capability instead, so its programs stay covered
def oracleFamily : ExternOracle := oracleFamilyWith stmtV2 false

/-- The family with every call decided by `externCallOkB`; a failing call is stuck
(`notCovered` re-runs with the plain family to tell it from a stuck run). -/
def checkedOracleWith (fixStale cleanBox : Bool) (P : Prog) : ExternOracle := fun r args h =>
  match oracleFamilyWith fixStale cleanBox r args h, P.find? r with
  | some (h', v), some (.extern ps res rc _) =>
    if externCallOkB P ps res rc args h h' v then some (h', v) else none
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

def paramCountDist : List (Nat × Nat) := [(5, 0), (25, 1), (25, 2), (18, 3), (10, 4), (8, 5), (9, 6)]

/-- Input functions: one per arrow type a seed's parameter has, one parameter,
reading it (a generated body of depth 2). -/
partial def arrowTys : Ty → List Ty
  | .arr m r a b => .arr m r a b :: arrowTys b
  | _ => []

def genProg (externs : Bool) (nDefs : Nat) (depth : Nat) : R GProg := do
  let externs := externs && (← chance 30)
  let base : List (Ref × Ty) :=
    [(consumeR, Ty.arr .unique .shared .list .nat), (lenR, .arr .many .shared .list .nat),
     (callTwiceR, .arr .many .shared natArr .nat),
     (addP, .arr .many .shared .nat (.arr .many .shared .nat .nat))] ++
    (if externs then [(exFresh, Ty.arr .many .shared .nat .nat), (exId, .arr .many .shared .list .list),
      (exBox, .arr .many .shared .list .sbox), (exStale, .arr .many .shared .nat .list)] else [])
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
    -- a definition without parameters has no binder to carry a result mode
    let res := if n == 0 then ResultMode.shared else res
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

end MT.DiffTest
