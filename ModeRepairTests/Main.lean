/- Engineer MR's driver for the mode-lane repairs (branch `jcb/ixcc-mode-repair`, made from
`jcb/ixvmc-mo` at 6db9089a7, rebased by engineer MV onto `origin/jcb/certified-ixvm` at f2b985847,
whose records hold binder modes in a binder-data section: see `withSection`). Kernel package
only: run from the repository root as
`lake -d IxC env lean --run ModeRepairTests/Main.lean` after `lake -d IxC build IxC.Resource
IxC.Kernel.Ixon.Prelude`. Every expectation is asserted; the process exits 1 if any fails.

* Part 1: the 41 cases of `Tests/Ix/ResourceModes.lean` that need no record fixture (that file
  imports the root package, so it cannot run here), with their expectations; a case whose
  expectation a repair changes says so beside it, and the suite file says the same.
* Part 2: the sixteen findings (REPLY-2-TO-IXVM.md §4) with their controls, from engineer MT's
  `Findings.lean` (branch `jcb/ixcc-mode-findings` at 3c673bc38), each with the checker's expected
  verdict and `runR`'s expected outcome at every fuel tried.

Every case also asserts what soundness gives on its inputs: if the checker accepts and the
inputs meet `InputsOk` (decided by `inputsOkB`), no fuel tried ends in a violation. A finding
not yet repaired is marked `open`, and its unsoundness is then expected rather than a failure. -/
import IxC.Resource
import IxC.Kernel.Ixon.Prelude

namespace ModeRepair

open IxC.Resource Ixon

/-! ## COPIED verbatim from Tests/Ix/ResourceModes.lean:37-152 at 6db9089a7 -/

def addr (k : Nat) : Address := ⟨⟨#[k.toUInt8, 0x5a]⟩⟩
def mem (k : Nat) : Ref := .member (addr k) 0
def ctr (k j : Nat) : Ref := .ctor (addr k) 0 j

/-- A list, `Nat`, a box with an inherited field, a box with a `@shared` field,
a key with an erased field. -/
def L := mem 1
def nilR := ctr 1 0
def consR := ctr 1 1
def natR := mem 2
def B := mem 3
def boxR := ctr 3 0
def S := mem 4
def sboxR := ctr 4 0
def K := mem 5
def keyR := ctr 5 0

def addR := mem 10
def consumeR := mem 11
def lenR := mem 12
def consumeNR := mem 13
def consume2R := mem 14
def consumeBR := mem 15
def consumeSR := mem 16
def incR := mem 17
def useR := mem 18
def tblR := mem 19

def fld (c : Cls := .val) (fm : FieldMode := .inherited) (m : BinderMode := .many) : Field :=
  { mode := m, fmode := fm, cls := c }

def par (m : BinderMode := .many) (c : Cls := .val) (s : Skel := .data) (noLeaf : Bool := false) :
    Param :=
  { mode := m, cls := c, skel := s, noLeaf }

/-- A list parameter: no leaf inhabits its type. -/
def parL (m : BinderMode := .many) : Param := par m .val .data true

/-- A closure, its captures computed. -/
def lam (p : Param) (body : Term) (res : ResultMode := .shared) (rc : Cls := .val) : Term :=
  .lam p res rc ((freeVars 4096 1 body).toOption.getD []).toArray body

def app (f : Term) (args : List Term) (c : Cls := .val) : Term :=
  (args.zipIdx.foldl (fun g (a, i) => Term.app g a (if i + 1 == args.length then c else .val)) f)

def add (a b : Term) : Term := app (.const addR .val) [a, b] .leaf
def lenOf (t : Term) : Term := app (.const lenR .val) [t] .leaf
def v (i : Nat) (c : Cls := .val) : Term := .var i c

/-- A case on a list: `nil => n | cons h t => c` (`c` under `h` and `t`). -/
def caseL : CaseInfo :=
  { ind := L, arity := 3, major := 0,
    alts := #[{ alt := 1, args := #[] }, { alt := 2, args := #[.field 0, .field 1] }] }

def onList (major : Term) (n : Term) (c : Term) (hc : Cls := .val) (rc : Cls := .val) : Term :=
  .case caseL major #[n, lam (par .many hc) (lam (par .many .val) c .shared rc) .shared rc] #[] rc

def body (ps : List Param) (t : Term) (res : ResultMode := .shared) (rc : Cls := .val)
    (rs : Skel := .data) : RunDef :=
  .body ps.toArray res rc rs t

/-- An arrow skeleton `Nat → Nat` or `List → Nat`, default modes. -/
def arrowSk (m : BinderMode := .many) : Skel := .arrow m .data .shared .data

def lib : Array (Ref × RunDef) := #[
  (L, .ind #[nilR, consR]),
  (nilR, .ctor L 0 1 #[]),
  (consR, .ctor L 1 1 #[fld, fld]),
  (natR, .ind #[]),
  (B, .ind #[boxR]), (boxR, .ctor B 0 0 #[fld]),
  (S, .ind #[sboxR]), (sboxR, .ctor S 0 0 #[fld .val .shared]),
  (K, .ind #[keyR]), (keyR, .ctor K 0 0 #[fld .val .inherited .erased, fld .leaf]),
  (addR, .prim .add),
  (consumeR, body [par .unique] (.natLit 0) .shared .leaf),
  (consumeNR, body [par .unique .leaf] (v 0 .leaf) .shared .leaf),
  (consume2R, body [par .unique, par .many .leaf] (.natLit 0) .shared .leaf),
  (consumeBR, body [par .unique] (.natLit 0) .shared .leaf),
  (consumeSR, body [par .unique] (.natLit 0) .shared .leaf),
  (incR, body [par .many .leaf] (add (v 0 .leaf) (.natLit 1)) .shared .leaf),
  (lenR, body [parL] (onList (v 0) (.natLit 0) (add (lenOf (v 0)) (.natLit 1)) .val .leaf)
    .shared .leaf),
  -- `use (k : List → Nat) (xs : List) : Nat := k xs + len xs`
  (useR, body [par .many .val (arrowSk), par .many] (add (app (v 1) [v 0] .leaf) (lenOf (v 0)))
    .shared .leaf),
  -- a static: `tbl : List := [1]`
  (tblR, body [] (app (.const consR .val) [.irr, .natLit 1, app (.const nilR .val) [.irr] .imm]) .shared .val)
]

def prog (defs : List (Ref × RunDef)) : Prog := { defs := lib ++ defs.toArray, nat := some natR }

/-! ## Input heaps -/

structure HB where
  objs : Array Obj := #[]

def HB.alloc (b : HB) (c : Cell) : HB × Val :=
  ({ objs := b.objs.push ⟨c, b.objs.size⟩ }, .ref b.objs.size b.objs.size [])

def HB.heap (b : HB) : Heap := { objs := b.objs, nextCap := b.objs.size }

def HB.list (b : HB) (ns : List Nat) : HB × Val :=
  ns.foldr (fun n (b, tl) =>
    let (b, h) := b.alloc (.num n)
    b.alloc (.ctor consR #[h, tl])) (b, .imm (.con nilR))

/-- Inputs: the heap and the arguments. -/
def oneList : Heap × List Val := let (b, xs) := ({} : HB).list [1, 2]; (b.heap, [xs])
def oneNat : Heap × List Val := let (b, n) := ({} : HB).alloc (.num 7); (b.heap, [n])
def irrArg : Heap × List Val := (({} : HB).heap, [.imm .irr])
def irrAndList : Heap × List Val := let (b, xs) := ({} : HB).list [1]; (b.heap, [.imm .irr, xs])
def oneKey : Heap × List Val :=
  let (b, n) := ({} : HB).alloc (.num 5)
  let (b, k) := b.alloc (.ctor keyR #[.imm .irr, n])
  (b.heap, [k])
def oneFun : Heap × List Val := let (b, f) := ({} : HB).alloc (.pap incR #[]); (b.heap, [f])
def noArgs : Heap × List Val := (({} : HB).heap, [])

/-! ## COPIED verbatim from Tests/Ix/ResourceModes.lean:156-167 at 6db9089a7 -/

def noExtern : ExternOracle := fun _ _ _ => none

def outcomeName : Outcome → String
  | .value .. => "a value"
  | .violation k => s!"violation {repr k}"
  | .stuck => "stuck"
  | .outOfFuel => "out of fuel"

def verdictName : Verdict → String
  | .accept .. => "accept"
  | .refuse at_ w => s!"refuse at {at_}: {w}"
  | .decline r => s!"decline: {r}"

/-! ## COPIED from engineer MT's `DiffTest/Hyp.lean` (lines 14-144, unpushed, read 2026-11-13):
`InputsOk` decided. Kept in step with `Statement.lean`'s `InputsOk` by hand. -/

def walkFuel : Nat := 4096

def objAt (h : Heap) (l : Nat) : Option Obj := h.objs[l]?

def reachSet (h : Heap) : Nat → Val → List Nat
  | 0, _ => []
  | _ + 1, .imm _ => []
  | n + 1, .ref loc _ _ =>
    loc :: match objAt h loc with
      | some o => o.cell.vals.flatMap (reachSet h n)
      | none => []

def reaches (h : Heap) (v : Val) (l : Nat) : Bool := (reachSet h walkFuel v).contains l

def notLeafCell (o : Obj) : Bool := o.cell.isNum == false || natClass != .leaf

def ownSet (P : Prog) (h : Heap) : Nat → Val → List Nat
  | 0, _ => []
  | _ + 1, .imm _ => []
  | n + 1, .ref loc _ _ =>
    match objAt h loc with
    | none => []
    | some o =>
      let here := if notLeafCell o then [loc] else []
      here ++ (ownedSlots P o.cell).flatMap fun i =>
        match o.cell.slot? i with
        | some sv => ownSet P h n sv
        | none => []

def valOk (h : Heap) : Val → Bool
  | .imm _ => true
  | .ref loc cap t => t.isEmpty && match objAt h loc with
    | some o => o.cap == cap
    | none => false

def inputCell (P : Prog) : Cell → Bool
  | .ctor .. | .num _ | .str _ => true
  | .pap r args => (papSkel P r args.size).isSome
  | .clo .. | .once .. => false

def heapOk (P : Prog) (h : Heap) : Bool :=
  (List.range h.objs.size).all fun loc =>
    match objAt h loc with
    | none => true
    | some o => inputCell P o.cell && decide (o.cap < h.nextCap) &&
        o.cell.vals.all fun v => valOk h v && !reaches h v loc

def papArgOk (h : Heap) : Val → Bool
  | .imm _ => true
  | .ref loc _ t => t.isEmpty && match objAt h loc with
    | some o => o.cell.isNum
    | none => false

def closureAt (P : Prog) (h : Heap) (s : Skel) : Val → Bool
  | .ref loc _ t => t.isEmpty && match objAt h loc with
    | some o => match o.cell with
      | .pap r args => args.all (papArgOk h) && match papSkel P r args.size with
        | some sk => s.admits sk
        | none => false
      | _ => false
    | none => false
  | .imm _ => false

def defaultPaps (P : Prog) (h : Heap) (v : Val) : Bool :=
  (reachSet h walkFuel v).all fun l =>
    match objAt h l with
    | some o => match o.cell with
      | .pap r args => args.all (papArgOk h) && match papSkel P r args.size with
        | some sk => sk.isDefault
        | none => false
      | _ => true
    | none => true

def isIrr (v : Val) : Bool := v == .imm .irr

def isImm : Val → Bool
  | .imm _ => true
  | _ => false

def isFreshNum (h : Heap) : Val → Bool
  | .ref loc _ t => t.isEmpty && match objAt h loc with
    | some o => o.cell.isNum
    | none => false
  | .imm _ => false

def argOk (P : Prog) (h : Heap) (p : Param) (a : Val) : Bool :=
  valOk h a &&
  (p.mode != .erased || isIrr a) &&
  (p.cls != .irr || isIrr a) &&
  (p.cls != .imm || isImm a) &&
  (p.cls != .leaf || isFreshNum h a) &&
  (match p.skel with
    | .arrow .. => closureAt P h p.skel a
    | _ => defaultPaps P h a)

def ownTree (P : Prog) (h : Heap) (v : Val) : Bool := Id.run do
  let mut seen : List (Nat × Nat × Nat) := []
  for p in (ownSet P h walkFuel v).eraseDups do
    let some o := objAt h p | continue
    for i in ownedSlots P o.cell do
      match o.cell.slot? i with
      | some (.ref l _ _) =>
        let leafTarget := match objAt h l with
          | some ol => !notLeafCell ol
          | none => false
        if leafTarget then continue
        if seen.any fun (l', p', i') => l' == l && (p' != p || i' != i) then return false
        seen := (l, p, i) :: seen
      | _ => pure ()
  return true

def inputsOkB (P : Prog) (h : Heap) (params : Array Param) (args : List Val) : Bool :=
  args.length == params.size && heapOk P h &&
  (List.range args.length).all fun i =>
    match params[i]?, args[i]? with
    | some p, some a =>
      argOk P h p a &&
      (!p.mode.isUnique || (ownTree P h a &&
        (List.range args.length).all fun j =>
          j == i || match args[j]? with
            | some b => (ownSet P h walkFuel a).all fun l => !reaches h b l
            | none => true))
    | _, _ => false

/-! ## END OF COPIED LINES. Everything below is MR's (the finding programs are MT's encodings). -/

/-! ## The harness -/

/-- An expected outcome of `runR`. -/
inductive OExp where
  | value
  | vio (k : Violation)
  | stuck
  | oof
  /-- not a violation (a value, stuck or out of fuel) -/
  | noVio
  /-- a value or out of fuel -/
  | valOrOof
  /-- the violation or out of fuel -/
  | vioOrOof (k : Violation)
  deriving Inhabited

def OExp.ok : OExp → Outcome → Bool
  | .value, .value .. => true
  | .vio k, .violation k' => k == k'
  | .stuck, .stuck => true
  | .oof, .outOfFuel => true
  | .noVio, .violation _ => false
  | .noVio, _ => true
  | .valOrOof, .value .. => true
  | .valOrOof, .outOfFuel => true
  | .vioOrOof k, .violation k' => k == k'
  | .vioOrOof _, .outOfFuel => true
  | _, _ => false

def OExp.name : OExp → String
  | .value => "a value"
  | .vio k => s!"violation {repr k}"
  | .stuck => "stuck"
  | .oof => "out of fuel"
  | .noVio => "no violation"
  | .valOrOof => "a value or out of fuel"
  | .vioOrOof k => s!"violation {repr k} or out of fuel"

/-- Expected outcomes by fuel: entry `(n, e)` holds from fuel `n` until the next entry. -/
abbrev Table := List (Nat × OExp)

def Table.at (t : Table) (f : Nat) : OExp :=
  ((t.filter (·.1 ≤ f)).getLast?.map (·.2)).getD .noVio

/-- An expected verdict: accept, refuse (with a fragment of its witness), decline. -/
inductive VExp where
  | accept
  | refuse (frag : String := "")
  | decline
  deriving Inhabited

def VExp.ok : VExp → Verdict → Bool
  | .accept, .accept .. => true
  | .refuse frag, .refuse _ w => frag.isEmpty || (w.splitOn frag).length > 1
  | .decline, .decline _ => true
  | _, _ => false

def VExp.name : VExp → String
  | .accept => "accept"
  | .refuse frag => if frag.isEmpty then "refuse" else s!"refuse ({frag})"
  | .decline => "decline"

def stdFuels : List Nat := [10, 20, 50, 100, 1000, 100000]
def fuels0to12 : List Nat := (List.range 13) ++ [100000]

def outcomeLong : Outcome → String
  | .value v _ => s!"a value {repr v}"
  | o => outcomeName o

/-- One case: a program, a seed and its inputs, the bodies to check, what the checker and the
run must do. `inputs`: whether the inputs meet `InputsOk` (decided), when asserted. `open_`: the
finding is not repaired yet, so the checker's accepting a violating run is expected. -/
structure Case where
  label : String
  P : Prog
  ext : ExternOracle := noExtern
  seed : Ref
  inp : Heap × List Val
  toCheck : List Ref
  verdict : VExp
  fuels : List Nat := stdFuels
  run : Table
  inputs : Option Bool := some true
  open_ : Bool := false
  lim : Limits := {}

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  failed : Array String := #[]

def note (t : IO.Ref Tally) (label : String) (ok : Bool) : IO Unit := do
  if ok then t.modify fun s => { s with pass := s.pass + 1 }
  else t.modify fun s => { s with fail := s.fail + 1, failed := s.failed.push label }

def runCase (t : IO.Ref Tally) (c : Case) : IO Unit := do
  let verdict := checkBodies c.lim c.P c.toCheck
  let vOk := c.verdict.ok verdict
  let inOk := match c.P.find? c.seed with
    | some (.body ps ..) => inputsOkB c.P c.inp.1 ps c.inp.2
    | _ => false
  let iOk := match c.inputs with
    | some b => b == inOk
    | none => true
  let mut lines : Array String := #[]
  let mut rOk := true
  let mut violates := false
  let mut os : List Outcome := []
  for f in c.fuels do
    let o := runR c.P c.ext f c.seed c.inp.1 c.inp.2
    os := os ++ [o]
    let e := Table.at c.run f
    let ok := e.ok o
    if !ok then rOk := false
    if let .violation _ := o then violates := true
    lines := lines.push s!"    fuel {f}: {outcomeLong o}{if ok then "" else s!"   EXPECTED {e.name}"}"
  -- fuel monotonicity (since repair B): over increasing fuel, out of fuel and then one outcome
  let rest := os.dropWhile fun o => match o with | .outOfFuel => true | _ => false
  let mono := match rest with
    | [] => true
    | o :: more => more.all fun o' => outcomeName o' == outcomeName o
  -- what soundness gives on these inputs
  let unsound := verdict.isAccept && inOk && violates
  let sOk := !unsound || c.open_
  let ok := vOk && iOk && rOk && sOk && mono
  IO.println s!"{if ok then "ok  " else "FAIL"} [{c.label}] checker: {verdictName verdict}{if vOk then "" else s!"   EXPECTED {c.verdict.name}"}; InputsOk {inOk}{if iOk then "" else "   NOT AS EXPECTED"}{if unsound then (if c.open_ then "; accepted and violates (open finding)" else "; ACCEPTED AND VIOLATES") else ""}{if mono then "" else "; NOT FUEL-MONOTONE"}"
  for l in lines do IO.println l
  note t c.label ok

def check1 (t : IO.Ref Tally) (label : String) (ok : Bool) (detail : String) : IO Unit := do
  IO.println s!"{if ok then "ok  " else "FAIL"} [{label}] {detail}"
  note t label ok

/-! ## Records built by hand at the Ixon v5 layout (since the rebase onto f2b985847)

A binder's mode is no longer inline in the expression: it is in the record's binder-data section
(`Ixon.Constant.binders`), one block per root expression with a binder and one per variant of a
sharing entry with a binder, one node per `lam`, `all` and binderful `share`, in pre-order
(`Ixon.Expr.numberedNodes`). `check` and `readProg` refuse a record whose section is not complete
(`Reading.complete`, `Constant.bindersComplete`). `withSection c mode` gives `c` its complete
section: every share node at variant 0, each binder node with the datum `never` (`undecided` in an
unsafe or partial record) and the mode `mode shared index ordinal` (the block's key and the
node's ordinal in it; a share node's ordinal counts too). -/

def withSection (c : Ixon.Constant) (mode : Bool → Nat → Nat → AllMode := fun _ _ _ => {}) :
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

/-! ## Part 1: the suite's 41 cases without a record fixture

COPIED from Tests/Ix/ResourceModes.lean:191-410 at 6db9089a7, with their `runCase` replaced by
`suiteCase` (same arguments, run at fuel 100000 as theirs). Expectations changed by a repair are
marked `-- REPAIR <letter>:` with the reason. -/

def suiteCase (label : String) (defs : List (Ref × RunDef)) (entry : Ref) (input : Heap × List Val)
    (run : Option Violation) (accept : Bool) (toCheck : List Ref := [entry]) (lim : Limits := {}) : Case :=
  { label := s!"suite: {label}", P := prog defs, seed := entry, inp := input, toCheck,
    verdict := if accept then .accept else .refuse, fuels := [100000],
    run := [(0, match run with | some k => .vio k | none => .value)], inputs := none, lim }

-- `useErased (@erased n : Nat) : Nat := n + 1`
def useErased := mem 100
-- `keep (@erased n : Nat) (b : List) : List := b`
def keepE := mem 101
-- `leak (k : Key) : Nat := k.ghost`; `idOf (k : Key) : Nat := k.id`
def leak := mem 102
def idOf := mem 103
-- `let (@erased x) := xs; len x`
def eraseLet := mem 104

def erasedCases : List Case := [
  suiteCase "erased: reading an erased parameter" [(useErased, body [par .erased .leaf]
    (add (v 0 .leaf) (.natLit 1)) .shared .leaf)] useErased irrArg (some .erasedRead) false,
  suiteCase "erased: an erased parameter never read" [(keepE, body [par .erased .leaf, par]
    (v 0))] keepE irrAndList none true,
  suiteCase "erased: projecting an erased field" [(leak, body [par] (.proj K 0 (v 0) .leaf) .shared .leaf)]
    leak oneKey (some .erasedRead) false,
  suiteCase "erased: projecting a kept field" [(idOf, body [par] (.proj K 1 (v 0) .leaf) .shared .leaf)]
    idOf oneKey none true,
  suiteCase "erased: reading an erased let" [(eraseLet, body [par]
    (.letE (.value .erased) .val (v 0) (lenOf (v 0))) .shared .leaf)] eraseLet oneList
    (some .erasedRead) false
]

def twice := mem 110
def once1 := mem 111
def share1 := mem 112
def caller := mem 113
def headU := mem 114
def headBad := mem 115
def deep := mem 116
def boxS := mem 117
def boxI := mem 118
def twiceN := mem 119

def uniqueCases : List Case := [
  -- `twice (@unique xs) := consume xs + consume xs`
  suiteCase "unique: a binding transferred twice" [(twice, body [par .unique]
    (add (app (.const consumeR .val) [v 0] .leaf) (app (.const consumeR .val) [v 0] .leaf)) .shared .leaf)]
    twice oneList (some .revokedUse) false,
  suiteCase "unique: a binding transferred once" [(once1, body [par .unique]
    (app (.const consumeR .val) [v 0] .leaf) .shared .leaf)] once1 oneList none true,
  -- `share1 (xs : List) := consume xs`; `caller (xs) := share1 xs + len xs`
  suiteCase "unique: a shared parameter given away, then read by its caller"
    [(share1, body [par] (app (.const consumeR .val) [v 0] .leaf) .shared .leaf),
     (caller, body [par] (add (app (.const share1 .val) [v 0] .leaf) (lenOf (v 0))) .shared .leaf)]
    caller oneList (some .revokedUse) false [share1, caller],
  -- `headU (@unique xs) := match xs with | [] => 0 | _ :: t => len t`
  suiteCase "unique: a consuming match, the fields used" [(headU, body [par .unique]
    (onList (v 0) (.natLit 0) (lenOf (v 0)) .val .leaf) .shared .leaf)] headU oneList none true,
  -- `headBad (@unique xs) := match xs with | [] => 0 | _ :: _ => len xs`
  suiteCase "unique: a consumed major read in an alternative" [(headBad, body [par .unique]
    (onList (v 0) (.natLit 0) (lenOf (v 2)) .val .leaf) .shared .leaf)] headBad oneList
    (some .revokedUse) false,
  -- `deep (@unique xs) := match xs with | [] => 0 | h :: t => consume (h :: t) + len t`
  suiteCase "unique: deep transfer revokes the fields" [(deep, body [par .unique]
    (onList (v 0) (.natLit 0)
      (add (app (.const consumeR .val) [app (.const consR .val) [.irr, v 1, v 0]] .leaf) (lenOf (v 0))) .val .leaf)
    .shared .leaf)] deep oneList (some .revokedUse) false,
  -- `boxS (x : List) := let s := ⟨x⟩ : S; consumeS s + len x` (a `@shared` field)
  suiteCase "unique: a @shared field stops deep uniqueness" [(boxS, body [par]
    (.letE (.value .many) .val (app (.const sboxR .val) [v 0])
      (add (app (.const consumeSR .val) [v 0] .leaf) (lenOf (v 1)))) .shared .leaf)] boxS oneList none true,
  -- `boxI (x : List) := let s := ⟨x⟩ : B; consumeB s + len x` (an inherited field)
  suiteCase "unique: an inherited field is transferred with its box" [(boxI, body [par]
    (.letE (.value .many) .val (app (.const boxR .val) [v 0])
      (add (app (.const consumeBR .val) [v 0] .leaf) (lenOf (v 1)))) .shared .leaf)] boxI oneList
    (some .revokedUse) false,
  -- `twiceN (@unique n : Nat) := consumeN n + consumeN n` (a leaf is never unique)
  suiteCase "unique: a leaf transferred twice" [(twiceN, body [par .unique .leaf]
    (add (app (.const consumeNR .val) [v 0 .leaf] .leaf) (app (.const consumeNR .val) [v 0 .leaf] .leaf))
    .shared .leaf)] twiceN oneNat none true
]

def esc := mem 120
def peek := mem 121
def same := mem 122
def stash := mem 123
def give := mem 124
def letEsc := mem 125
def letOk := mem 126
def escN := mem 127
def addN := mem 128
def headN := mem 129
def storeN := mem 132
def shf := mem 133

def borrowCases : List Case := [
  suiteCase "borrow: a borrowed parameter returned" [(esc, body [par .borrowed] (v 0))] esc oneList
    (some .borrowEscape) false,
  -- REPAIR A: accepted as landed; refused now. `len`'s result is a `shared` leaf, which now
  -- carries its argument's regions (its parameter's `noLeaf` is no longer read), and it is
  -- returned at `shared`. The run returns a fresh number: the checker is incomplete here.
  suiteCase "borrow: a borrowed parameter read" [(peek, body [par .borrowed] (lenOf (v 0)) .shared .leaf)]
    peek oneList none false,
  suiteCase "borrow: a borrowed parameter returned borrowed" [(same, body [par .borrowed] (v 0) .borrowed)]
    same oneList none true,
  -- `stash (@borrowed b : List) : List := [b]`
  suiteCase "borrow: a borrowed parameter stored in a cell" [(stash, body [par .borrowed]
    (app (.const consR .val) [.irr, v 0, app (.const nilR .val) [.irr] .imm]))] stash oneList
    (some .borrowEscape) false,
  suiteCase "borrow: a borrowed parameter given away" [(give, body [par .borrowed]
    (app (.const consumeR .val) [v 0] .leaf) .shared .leaf)] give oneList (some .borrowEscape) false,
  suiteCase "borrow: a let's loan returned" [(letEsc, body [par] (.letE .borrow .val (v 0) (v 0)))]
    letEsc oneList (some .borrowEscape) false,
  -- REPAIR A: accepted as landed; refused now, for the same reason: `len x` carries the let's
  -- region, so the let's value outlives the loan to the checker.
  suiteCase "borrow: a let's loan read" [(letOk, body [par] (.letE .borrow .val (v 0) (lenOf (v 0)))
    .shared .leaf)] letOk oneList none false,
  suiteCase "borrow: a borrowed leaf returned" [(escN, body [par .borrowed .leaf] (v 0 .leaf) .shared .leaf)]
    escN oneNat (some .borrowEscape) false,
  suiteCase "borrow: arithmetic on a borrowed leaf" [(addN, body [par .borrowed .leaf]
    (add (v 0 .leaf) (.natLit 1)) .shared .leaf)] addN oneNat none true,
  -- `headN (@borrowed xs : List Nat) : Nat := match xs with | [] => 0 | h :: _ => h`
  suiteCase "borrow: a leaf read out of a borrowed container is not confined" [(headN, body [par .borrowed]
    (onList (v 0) (.natLit 0) (v 1 .leaf) .leaf .leaf) .shared .leaf)] headN oneList none true,
  -- `storeN (@borrowed n : Nat) : Nat := match [n] with | [] => 0 | h :: _ => h`
  suiteCase "borrow: a borrowed leaf stored in a cell and read back is a counted value" [(storeN,
    body [par .borrowed .leaf]
      (onList (app (.const consR .val) [.irr, v 0 .leaf, app (.const nilR .val) [.irr] .imm])
        (.natLit 0) (v 1 .leaf) .leaf .leaf) .shared .leaf)] storeN oneNat none true,
  -- `shf (@borrowed b : List) : List := (⟨b⟩ : S).1` (a borrowed value in a `@shared` field)
  suiteCase "borrow: a borrowed value stored in a @shared field and returned" [(shf,
    body [par .borrowed] (.proj S 0 (app (.const sboxR .val) [v 0]) .val))] shf oneList
    (some .borrowEscape) false
]

def twiceCall := mem 130
def onceCall := mem 131

def onceCases : List Case := [
  suiteCase "once: a once parameter called twice" [(twiceCall, body [par .once .val arrowSk]
    (add (app (v 0) [.natLit 1] .leaf) (app (v 0) [.natLit 2] .leaf)) .shared .leaf)] twiceCall oneFun
    (some .onceReentry) false,
  suiteCase "once: a once parameter called once" [(onceCall, body [par .once .val arrowSk]
    (app (v 0) [.natLit 1] .leaf) .shared .leaf)] onceCall oneFun none true
]

def capOnce := mem 140
def capOuter := mem 141
def capPlain := mem 142
def papT := mem 143

def captureCases : List Case := [
  -- `capOnce (@unique xs) := let g := fun u => consume xs; g 0 + g 1`
  suiteCase "capture: a closure consuming its capture called twice" [(capOnce, body [par .unique]
    (.letE (.value .many) .val (lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf)
      (add (app (v 0) [.natLit 0] .leaf) (app (v 0) [.natLit 1] .leaf))) .shared .leaf)] capOnce oneList
    (some .revokedUse) false,
  -- `capOuter (@unique xs) := let g := fun u => len xs; len xs`
  suiteCase "capture: a unique binding captured, then read outside" [(capOuter, body [par .unique]
    (.letE (.value .many) .val (lam (par .many .leaf) (lenOf (v 1)) .shared .leaf) (lenOf (v 1)))
    .shared .leaf)] capOuter oneList (some .revokedUse) false,
  -- `capPlain (xs : List) := let g := fun u => len xs; g 0 + len xs`
  suiteCase "capture: a shared binding captured and read" [(capPlain, body [par]
    (.letE (.value .many) .val (lam (par .many .leaf) (lenOf (v 1)) .shared .leaf)
      (add (app (v 0) [.natLit 0] .leaf) (lenOf (v 1)))) .shared .leaf)] capPlain oneList none true,
  -- `papT (@unique xs) := let g := consume2 xs; len xs`
  suiteCase "capture: a partial application transfers its unique argument" [(papT, body [par .unique]
    (.letE (.value .many) .val (app (.const consume2R .val) [v 0]) (lenOf (v 1))) .shared .leaf)] papT oneList
    (some .revokedUse) false
]

def callUse := mem 150
def callUseOk := mem 151
def badStatic := mem 152
def okStatic := mem 153

def skeletonCases : List Case := [
  -- `callUse (xs) := use (fun (@unique y) => consume y) xs`
  suiteCase "skeleton: a closure with a unique binder at a plain arrow" [(callUse, body [par]
    (app (.const useR .val) [lam (par .unique) (app (.const consumeR .val) [v 0] .leaf) .shared .leaf, v 0] .leaf)
    .shared .leaf)] callUse oneList (some .revokedUse) false,
  suiteCase "skeleton: a closure with a plain binder at a plain arrow" [(callUseOk, body [par]
    (app (.const useR .val) [lam (par .many) (lenOf (v 0)) .shared .leaf, v 0] .leaf) .shared .leaf)]
    callUseOk oneList none true,
  -- `badStatic := consume tbl + len tbl`
  suiteCase "static: a static given away, then read" [(badStatic, body []
    (add (app (.const consumeR .val) [.const tblR .val] .leaf) (lenOf (.const tblR .val))) .shared .leaf)] badStatic
    noArgs (some .revokedUse) false,
  suiteCase "static: a static read twice" [(okStatic, body []
    (add (lenOf (.const tblR .val)) (lenOf (.const tblR .val))) .shared .leaf)] okStatic noArgs none true
]

/-- A case on `Key`: `key g n => alt g n`. -/
def caseK : CaseInfo :=
  { ind := K, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0, .field 1] }] }

def firstOf := mem 160
def altConst := mem 161
def secondOf := mem 162
def altLam := mem 163

def alternativeCases : List Case := [
  -- `firstOf (a : List) (b : Nat) : List := a`; `altConst (k : Key) := Key.casesOn k firstOf`
  suiteCase "must-reject: an erased field passed to an alternative that is not a λ" [
    (firstOf, body [par, par .many .leaf] (v 1)),
    (altConst, body [par] (.case caseK (v 0) #[.const firstOf .val] #[] .val))]
    altConst oneKey (some .erasedRead) false,
  -- `secondOf (b : Nat) : Nat := b`; `altLam (k : Key) := Key.casesOn k (fun (@erased g) => secondOf)`
  suiteCase "erased: a λ alternative binds the erased field, the rest passed on" [
    (secondOf, body [par .many .leaf] (v 0 .leaf) .shared .leaf),
    (altLam, body [par] (.case caseK (v 0) #[lam (par .erased) (.const secondOf .val) .shared .leaf] #[]
      .leaf) .shared .leaf)]
    altLam oneKey none true
]

/-- A step limit declines (their `limitCase`). -/
def limitCase (t : IO.Ref Tally) : IO Unit := do
  let verdict := checkBodies { steps := 3 } (prog []) [lenR]
  let ok := match verdict with
    | .decline _ => true
    | _ => false
  check1 t "suite: limits: the step limit declines" ok (verdictName verdict)

/-- Their `fastPathCase`: a closure of default records is accepted without reading; an annotated
axiom is read and refused outside the extern set, accepted inside it. -/
def fastPathCase (t : IO.Ref Tally) : IO Unit := do
  let plain : Ixon.Constant :=
    { info := .axio ⟨false, 0, .sort 0⟩, sharing := #[], refs := #[], univs := #[.zero] }
  let moded : Ixon.Constant :=
    { info := .axio ⟨false, 0, .all (.sort 0) (.sort 0)⟩,
      sharing := #[], refs := #[], univs := #[.zero],
      binders := #[{ shared := false, index := 0, variant := 0,
                     nodes := #[.never { input := .unique }] }] }
  let table : Ix.Kernel.RoleTable := { version := 0, bound := #[], evidence := #[] }
  let mk (c : Ixon.Constant) (externs : List Address := []) : Subject :=
    { table, store := fun a => if a == addr 200 then some c else none, seeds := [addr 200], externs }
  let v1 := check {} Ix.Kernel.Env.empty (mk plain)
  let v2 := check {} Ix.Kernel.Env.empty (mk moded)
  let v3 := check {} Ix.Kernel.Env.empty (mk moded [addr 200])
  let ok := (match v1 with | .accept 0 true => true | _ => false) &&
    (match v2 with | .refuse _ w => (w.splitOn "not in the extern set").length > 1 | _ => false) &&
    (match v3 with | .accept _ false => true | _ => false)
  check1 t "suite: fast path and externs: default records unread; an annotated axiom only as an extern" ok
    s!"{verdictName v1}; {verdictName v2}; {verdictName v3}"

def suiteCases : List Case :=
  erasedCases ++ uniqueCases ++ borrowCases ++ onceCases ++ captureCases ++ skeletonCases ++ alternativeCases

/-! ## Part 1b: the finding cases added to Tests/Ix/ResourceModes.lean, COPIED verbatim from
its section "Findings of the mode study" (so that text elaborates and runs here), with `runCase`
the driver's `suiteCase`. Part 2 runs the same programs at every fuel. -/

namespace SuiteFindings

def runCase (label : String) (defs : List (Ref × RunDef)) (entry : Ref) (input : Heap × List Val)
    (run : Option Violation) (accept : Bool) (toCheck : List Ref := [entry]) (lim : Limits := {}) : Case :=
  suiteCase label defs entry input run accept toCheck lim

/-- The suite's `fuelCase` (not copied: it is harness): out of fuel, then a value, at the given
ascending fuels (with `runCase`'s fuel monotonicity, as the suite's version asserts). -/
def fuelCase (label : String) (defs : List (Ref × RunDef)) (entry : Ref) (input : Heap × List Val)
    (fuels : List Nat) (accept : Bool) (toCheck : List Ref := [entry]) : Case :=
  { label := s!"suite: {label}", P := prog defs, seed := entry, inp := input, toCheck,
    verdict := if accept then .accept else .refuse, fuels,
    run := [(0, .valOrOof), (fuels.getLastD 0, .value)], inputs := none }

-- BEGIN COPY of Tests/Ix/ResourceModes.lean, "Findings of the mode study"

-- Finding 1: `idN (n : Nat) : Nat := n`; `g4 (@borrowed n : Nat) : Nat := idN n`
def idN := mem 300
def g4 := mem 301
def g4b := mem 341
-- Finding 2: `app1 (f : Unit → Nat) : Nat := f ()`; `g3 (@borrowed n : Nat) : Nat := app1 (fun _ => n)`
def app1 := mem 302
def g3 := mem 303
def g3p := mem 342
-- Finding 3: `bad (h : List Nat = Nat) (xs : List Nat) : Nat := cast h (id xs)`;
-- `g2 (h : Nat = List Nat) (h' : List Nat = Nat) (@borrowed n : Nat) : Nat := bad h' (cast h n)`
def EqI := mem 6
def reflR := ctr 6 0
def caseEq : CaseInfo := { ind := EqI, arity := 4, major := 2, alts := #[{ alt := 3, args := #[] }] }
def idR := mem 308
def bad3 := mem 309
def g2 := mem 310

def idNDef (noLeaf : Bool) : Ref × RunDef := (idN, body [par .many .leaf .data noLeaf] (v 0 .leaf) .shared .leaf)
def app1Def (noLeaf : Bool) : Ref × RunDef :=
  (app1, body [par .many .val arrowSk noLeaf] (app (v 0) [.natLit 0] .leaf) .shared .leaf)
def eqDefs : List (Ref × RunDef) := [(EqI, .ind #[reflR]), (reflR, .ctor EqI 0 2 #[]),
  (idR, body [par .many .irr, par] (v 0)),
  (bad3, body [par .many .irr, parL] (.case caseEq .irr #[app (.const idR .val) [.irr, v 0]] #[] .leaf) .shared .leaf)]
def in3 : Heap × List Val := let (b, n) := ({} : HB).alloc (.num 7); (b.heap, [.imm .irr, .imm .irr, n])
-- Finding 7: `f (a b : Nat) (@erased x : List Nat) (c d e : Nat) : Nat := a`, `g` the same
-- parameters, `g a b x c d e := f a b x c d e`; the control has the erased parameter first
def fV := mem 335
def gV := mem 336
def fXV := mem 343
def gXV := mem 344
def sixV : List Param :=
  [par .many .leaf, par .many .leaf, par .erased .val (.dataApp .data .data) true, par .many .leaf, par .many .leaf,
   par .many .leaf]
def sixXV : List Param :=
  [par .erased .val (.dataApp .data .data) true, par .many .leaf, par .many .leaf, par .many .leaf, par .many .leaf,
   par .many .leaf]
def p7Defs : List (Ref × RunDef) := [(fV, body sixV (v 5 .leaf) .shared .leaf),
  (gV, body sixV (app (.const fV .val) [v 5 .leaf, v 4 .leaf, v 3, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf) .shared .leaf)]
def p7xDefs : List (Ref × RunDef) := [(fXV, body sixXV (v 4 .leaf) .shared .leaf),
  (gXV, body sixXV (app (.const fXV .val) [v 5, v 4 .leaf, v 3 .leaf, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf)
    .shared .leaf)]
def fiveNats : HB × List Val :=
  let (b, n1) := ({} : HB).alloc (.num 1)
  let (b, n2) := b.alloc (.num 2)
  let (b, n3) := b.alloc (.num 3)
  let (b, n4) := b.alloc (.num 4)
  let (b, n5) := b.alloc (.num 5)
  (b, [n1, n2, n3, n4, n5])
def in7 : Heap × List Val :=
  let (b, ns) := fiveNats; (b.heap, ns.take 2 ++ [.imm .irr] ++ ns.drop 2)
def in7x : Heap × List Val :=
  let (b, ns) := fiveNats; (b.heap, .imm .irr :: ns)
def fuels0to12 : List Nat := List.range 13 ++ [100000]
-- Finding 8: `dup (@unique x : List Nat) : Nat := consume (x :: x)`; `dup2 … := consume [x, x]`;
-- the control `pairOk (@unique x y : List Nat) : Nat := consume (x :: y)`
def dup := mem 315
def dup2 := mem 345
def pairOk := mem 346
def twoLists : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, ys) := b.list [3]
  (b.heap, [xs, ys])
-- Finding 9: `g5 (@borrowed xs : List Nat) : List Nat := let f := fun _ => xs; f 0`; the control `g5p`
-- with `xs` plain
def g5 := mem 317
def g5p := mem 353
-- Found with repair D: a partial application of a function value holding a value moved into it is
-- once-only. `kc17 (@unique a : List Nat) (n : Nat) : Nat := n`; `kc3 (@unique a) (b c : Nat) : Nat := b`;
-- `d1 (k : (@unique a : List Nat) → Nat → Nat) (@unique x) : Nat := let h := k x; h 1 + h 2`, `d1h … := k x 1`;
-- `d2 (@unique x) : Nat := let h := kc3 x; let h2 := h 1; h2 2 + h2 3`, `d2h … := let h := kc3 x; h 1 2`
def kc17 := mem 347
def d1 := mem 348
def d1h := mem 349
def kc3 := mem 350
def d2 := mem 351
def d2h := mem 352
def skU : Skel := .arrow .unique .data .shared (.arrow .many .data .shared .data)
def kcDefs : List (Ref × RunDef) := [(kc17, body [par .unique, par .many .leaf] (v 0 .leaf) .shared .leaf),
  (kc3, body [par .unique, par .many .leaf, par .many .leaf] (v 1 .leaf) .shared .leaf)]
def inD1 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, k) := b.alloc (.pap kc17 #[])
  (b.heap, [k, xs])
-- Finding 13: `use13 (k : (@borrowed a : List Nat) → Nat → Nat) (@unique y : List Nat) : Nat :=
-- k y (consume y)`, with `kk (@borrowed a : List Nat) (n : Nat) : Nat := match a with | [] => 0 | _ => 1`
-- given as `k`
def sk13 : Skel := .arrow .borrowed .data .shared (.arrow .many .data .shared .data)
def kk := mem 327
def use13 := mem 328
def p13Defs : List (Ref × RunDef) := [
  (kk, body [par .borrowed, par .many .leaf] (onList (v 1) (.natLit 0) (.natLit 1) .val .leaf) .shared .leaf),
  (use13, body [par .many .val sk13, par .unique]
    (app (v 1) [v 0, app (.const consumeR .val) [v 0] .leaf] .leaf) .shared .leaf)]
def in13 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, f) := b.alloc (.pap kk #[])
  (b.heap, [f, xs])
-- Found with repair N: a spine longer than the checker's depth left at it. `S6` is a structure of
-- five `Nat` fields and a `@shared` `List Nat` field; `g6 (@borrowed xs : List Nat) : List Nat :=
-- (S6.mk 1 2 3 4 5 xs).sh`, checked at depth 6 (its spine of six arguments is cut at 4 as landed)
-- and at the default depth; the control `g6p` has `xs` plain
def S6 := mem 354
def s6mk := ctr 354 0
def g6 := mem 355
def g6p := mem 356
def s6Defs : List (Ref × RunDef) := [(S6, .ind #[s6mk]),
  (s6mk, .ctor S6 0 0 #[fld .leaf, fld .leaf, fld .leaf, fld .leaf, fld .leaf, fld .val .shared]),
  (g6, body [par .borrowed] (.proj S6 5 (app (.const s6mk .val)
    [.natLit 1, .natLit 2, .natLit 3, .natLit 4, .natLit 5, v 0]) .val)),
  (g6p, body [par] (.proj S6 5 (app (.const s6mk .val)
    [.natLit 1, .natLit 2, .natLit 3, .natLit 4, .natLit 5, v 0]) .val))]
-- Findings 10 and 11: `callTwice (f : Nat → Nat) : Nat := f 0 + f 1`; `callOnce (@once f : Nat → Nat) : Nat := f 0`;
-- `bad10 (@unique xs) := callTwice (fun _ => consume xs)`; `alias10 (@unique xs) := let g := fun _ => consume xs;
-- let h := g; h 0 + g 0`; `h11 (@once f) := callTwice f`; the controls `ok10`, `ok11` call `callOnce` instead
def callTwice := mem 319
def bad10 := mem 320
def alias10 := mem 321
def h11 := mem 323
def callOnce := mem 357
def ok10 := mem 358
def ok11 := mem 359
def onceDefs : List (Ref × RunDef) := [
  (callTwice, body [par .many .val arrowSk] (add (app (v 0) [.natLit 0] .leaf) (app (v 0) [.natLit 1] .leaf))
    .shared .leaf),
  (callOnce, body [par .once .val arrowSk] (app (v 0) [.natLit 0] .leaf) .shared .leaf)]
def consumeClo : Term := lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf
-- Finding 12: `addB (@borrowed n : Nat) : Nat → Nat := Nat.add n`; the control `addP` with `n` plain
def addB := mem 325
def addP := mem 362
-- Finding 16: `use16 (k : List Nat → Nat → Nat) (@unique y : List Nat) (b : E) : Nat :=
-- (match b with | e0 => k | e1 => k) y (consume y)`, the case of class leaf, with
-- `kk16 (a : List Nat) (n : Nat) : Nat := len a` given as `k`; the control `use16p` has `y` plain
-- and applies the case to `y` and `1`
def E2 := mem 9
def e0R := ctr 9 0
def e1R := ctr 9 1
def caseE : CaseInfo :=
  { ind := E2, arity := 3, major := 0, alts := #[{ alt := 1, args := #[] }, { alt := 2, args := #[] }] }
def kk16 := mem 337
def use16 := mem 338
def use16p := mem 364
def sk16 : Skel := .arrow .many .data .shared (.arrow .many .data .shared .data)
def p16Defs : List (Ref × RunDef) := [
  (E2, .ind #[e0R, e1R]), (e0R, .ctor E2 0 0 #[]), (e1R, .ctor E2 1 0 #[]),
  (kk16, body [par, par .many .leaf] (lenOf (v 1)) .shared .leaf)]
def in16 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, k) := b.alloc (.pap kk16 #[])
  (b.heap, [k, xs, .imm (.con e0R)])
-- Found after repair E (repair Q): `useBox (b : Box (Nat → Nat)) : Nat := b.1 0 + b.1 1`;
-- `bad11b (@once f : Nat → Nat) : Nat := useBox ⟨f⟩`; the control `ok11b` has `f` plain
def useBox := mem 360
def bad11b := mem 361
def ok11b := mem 380
def useBoxDef : Ref × RunDef :=
  (useBox, body [par] (add (app (.proj B 0 (v 0) .val) [.natLit 0] .leaf) (app (.proj B 0 (v 0) .val) [.natLit 1] .leaf))
    .shared .leaf)

-- (the suite's `fuelCase` definition stands here; the driver's is above)

def findingCases : List Case := [
  runCase "finding 1: a borrowed number through a call of `Nat → Nat` (its parameter read as no-leaf)"
    [idNDef true, (g4, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .shared .leaf)]
    g4 oneNat (some .borrowEscape) false,
  runCase "finding 1, control: the parameter not read as no-leaf"
    [idNDef false, (g4, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .shared .leaf)]
    g4 oneNat (some .borrowEscape) false,
  runCase "finding 1, control: the result returned borrowed"
    [idNDef true, (g4b, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .borrowed .leaf)]
    g4b oneNat none true,
  runCase "finding 2: a borrowed number captured by a closure passed at a function type"
    [app1Def true, (g3, body [par .borrowed .leaf]
      (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf) .shared .leaf)]
    g3 oneNat (some .borrowEscape) false [g3, app1],
  runCase "finding 2, control: the parameter not read as no-leaf"
    [app1Def false, (g3, body [par .borrowed .leaf]
      (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf) .shared .leaf)]
    g3 oneNat (some .borrowEscape) false [g3, app1],
  runCase "finding 2, control: the captured number not borrowed"
    [app1Def true, (g3p, body [par .many .leaf]
      (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf) .shared .leaf)]
    g3p oneNat none true [g3p, app1],
  runCase "finding 3: a borrowed number cast to a list under an absurd hypothesis"
    (eqDefs ++ [(g2, body [par .many .irr, par .many .irr, par .borrowed .leaf]
      (app (.const bad3 .val) [.irr, .case caseEq .irr #[v 0 .leaf] #[] .val] .leaf) .shared .leaf)])
    g2 in3 (some .borrowEscape) false [g2, bad3],
  fuelCase "finding 7: a call of six arguments, the third erased, at every fuel from 0 to 12"
    p7Defs gV in7 fuels0to12 true [gV, fV],
  fuelCase "finding 7, control: the erased parameter first" p7xDefs gXV in7x fuels0to12 true [gXV, fXV],
  runCase "finding 8: a unique list stored twice in one cell, the cell given away"
    [(dup, body [par .unique] (app (.const consumeR .val) [app (.const consR .val) [.irr, v 0, v 0]] .leaf)
      .shared .leaf)] dup oneList (some .revokedUse) false,
  runCase "finding 8: a unique list stored in a cell and in a cell inside it, the cell given away"
    [(dup2, body [par .unique] (app (.const consumeR .val) [app (.const consR .val)
      [.irr, v 0, app (.const consR .val) [.irr, v 0, app (.const nilR .val) [.irr] .imm]]] .leaf) .shared .leaf)]
    dup2 oneList (some .revokedUse) false,
  runCase "finding 8, control: two unique lists in one cell, the cell given away"
    [(pairOk, body [par .unique, par .unique]
      (app (.const consumeR .val) [app (.const consR .val) [.irr, v 1, v 0]] .leaf) .shared .leaf)]
    pairOk twoLists none true,
  runCase "finding 9: a closure capturing a borrowed list, applied, its result returned"
    [(g5, body [par .borrowed] (.letE (.value .many) .val (lam (par .many .leaf) (v 1) .shared .val)
      (app (v 0) [.natLit 0])))] g5 oneList (some .borrowEscape) false,
  runCase "finding 9, control: the list not borrowed"
    [(g5p, body [par] (.letE (.value .many) .val (lam (par .many .leaf) (v 1) .shared .val)
      (app (v 0) [.natLit 0])))] g5p oneList none true,
  runCase "finding 13: a function value applied to a borrowed list, then to its consumption"
    p13Defs use13 in13 (some .revokedUse) false [use13, kk],
  runCase "a partial application of a function value at a unique binder, called twice"
    (kcDefs ++ [(d1, body [par .many .val skU, par .unique] (.letE (.value .many) .val (app (v 1) [v 0] .val)
      (add (app (v 0) [.natLit 1] .leaf) (app (v 0) [.natLit 2] .leaf))) .shared .leaf)])
    d1 inD1 (some .revokedUse) false,
  runCase "a partial application of a once-only partial application, called twice"
    (kcDefs ++ [(d2, body [par .unique] (.letE (.value .many) .val (app (.const kc3 .val) [v 0] .val)
      (.letE (.value .many) .val (app (v 0) [.natLit 1] .val)
        (add (app (v 0) [.natLit 2] .leaf) (app (v 0) [.natLit 3] .leaf)))) .shared .leaf)])
    d2 oneList (some .revokedUse) false,
  -- refused since repair D though the runs are clean: the result's aliases include the moved
  -- argument (d1h) or the consumed once-only binding (d2h)
  runCase "a function value at a unique binder applied to all its arguments (refused, runs clean)"
    (kcDefs ++ [(d1h, body [par .many .val skU, par .unique] (app (v 1) [v 0, .natLit 1] .leaf) .shared .leaf)])
    d1h inD1 none false,
  runCase "a once-only partial application applied to all its remaining arguments (refused, runs clean)"
    (kcDefs ++ [(d2h, body [par .unique] (.letE (.value .many) .val (app (.const kc3 .val) [v 0] .val)
      (app (v 0) [.natLit 1, .natLit 2] .leaf)) .shared .leaf)])
    d2h oneList none false,
  runCase "a spine longer than the checker's depth left at it: a borrowed list stored in a @shared field"
    s6Defs g6 oneList (some .borrowEscape) false [g6] { depth := 6 },
  runCase "the same at the default depth" s6Defs g6 oneList (some .borrowEscape) false,
  runCase "the same, the list not borrowed, at depth 6" s6Defs g6p oneList none true [g6p] { depth := 6 },
  runCase "finding 10: a closure consuming its capture, lent to a body that calls it twice"
    (onceDefs ++ [(bad10, body [par .unique] (app (.const callTwice .val) [consumeClo] .leaf) .shared .leaf)])
    bad10 oneList (some .revokedUse) false [bad10, callTwice],
  runCase "finding 10: a closure consuming its capture, aliased by a let, both called"
    [(alias10, body [par .unique] (.letE (.value .many) .val consumeClo
      (.letE (.value .many) .val (v 0) (add (app (v 0) [.natLit 0] .leaf) (app (v 1) [.natLit 0] .leaf))))
      .shared .leaf)] alias10 oneList (some .revokedUse) false,
  runCase "finding 10, control: the closure passed to a once parameter"
    (onceDefs ++ [(ok10, body [par .unique] (app (.const callOnce .val) [consumeClo] .leaf) .shared .leaf)])
    ok10 oneList none true [ok10, callOnce],
  runCase "finding 11: a once parameter passed to a body that calls it twice"
    (onceDefs ++ [(h11, body [par .once .val arrowSk] (app (.const callTwice .val) [v 0] .leaf) .shared .leaf)])
    h11 oneFun (some .onceReentry) false [h11, callTwice],
  runCase "finding 11, control: a once parameter passed to a once parameter"
    (onceDefs ++ [(ok11, body [par .once .val arrowSk] (app (.const callOnce .val) [v 0] .leaf) .shared .leaf)])
    ok11 oneFun none true [ok11, callOnce],
  runCase "finding 12: a primitive's partial application holding a borrowed number, returned"
    [(addB, body [par .borrowed .leaf] (app (.const addR .val) [v 0 .leaf] .val) .shared .val arrowSk)]
    addB oneNat (some .borrowEscape) false,
  runCase "finding 12, control: the number not borrowed"
    [(addP, body [par .many .leaf] (app (.const addR .val) [v 0 .leaf] .val) .shared .val arrowSk)]
    addP oneNat none true,
  runCase "finding 16: a case's two extra arguments, the second consuming the first"
    (p16Defs ++ [(use16, body [par .many .val sk16, par .unique, par .many .imm]
      (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, app (.const consumeR .val) [v 1] .leaf] .leaf) .shared .leaf)])
    use16 in16 (some .revokedUse) false [use16, kk16],
  runCase "finding 16, control: the extra arguments a plain list and a number"
    (p16Defs ++ [(use16p, body [par .many .val sk16, par .many, par .many .imm]
      (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, .natLit 1] .leaf) .shared .leaf)])
    use16p in16 none true [use16p, kk16],
  runCase "a once parameter stored in a cell, the cell lent to a body that calls the field twice"
    [useBoxDef, (bad11b, body [par .once .val arrowSk] (app (.const useBox .val) [app (.const boxR .val) [v 0]] .leaf)
      .shared .leaf)] bad11b oneFun (some .onceReentry) false [bad11b, useBox],
  runCase "the same, the parameter plain"
    [useBoxDef, (ok11b, body [par .many .val arrowSk] (app (.const useBox .val) [app (.const boxR .val) [v 0]] .leaf)
      .shared .leaf)] ok11b oneFun none true [ok11b, useBox]
]

-- END COPY

end SuiteFindings

/-! ## Part 2: the findings (MT's encodings, `Findings.lean` at 3c673bc38) -/

/-! ### Finding 1: `noLeaf` true for `Nat` -/

def idN := mem 300
def g4 := mem 301
def g4b := mem 341

def p1 (noLeafIdN : Bool) : Prog := prog [
  (idN, body [par .many .leaf .data noLeafIdN] (v 0 .leaf) .shared .leaf),
  (g4, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .shared .leaf),
  -- `g4b (@borrowed n : Nat) : @borrowed Nat := idN n`
  (g4b, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .borrowed .leaf)]

def f1Cases : List Case := [
  -- REPAIR A: accepted as landed
  { label := "F1 g4, idN's parameter noLeaf := true", P := p1 true, seed := g4, inp := oneNat, toCheck := [g4],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F1 control: noLeaf := false", P := p1 false, seed := g4, inp := oneNat, toCheck := [g4],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F1 control: the result returned borrowed", P := p1 true, seed := g4b, inp := oneNat, toCheck := [g4b],
    verdict := .accept, run := [(0, .value)] }]

def must {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- Finding 1 on the real records: the prelude's and evidence records, the default role table,
one hand-built record `idN : Nat → Nat := fun n => n`. `expectNoLeaf`: what the reading claims
of `Nat` (true as landed). -/
def finding1b (t : IO.Ref Tally) (expectNoLeaf : Bool) : IO Unit := do
  let tbl ← must "defaultTable" Ix.Kernel.Reader.defaultTable
  let recs ← must "preludeRecords" Ix.Kernel.Reader.preludeRecords
  let evid ← must "evidenceRecords" Ix.Kernel.Reader.evidenceRecords
  let blobs ← must "evidenceBlobs" Ix.Kernel.Reader.evidenceBlobs
  let some natA := tbl.addressOf? .nat | throw (IO.userError "no nat role")
  let idNA := addr 250
  let idNDef : Ixon.Definition :=
    { kind := Ix.DefKind.defn, safety := Ix.DefinitionSafety.safe, lvls := 0,
      typ := Ixon.Expr.leanAll (.ref 0 #[]) (.ref 0 #[]), value := Ixon.Expr.leanLam (.ref 0 #[]) (.var 0) }
  let idNRec : Ixon.Constant :=
    withSection { info := Ixon.ConstantInfo.defn idNDef, sharing := #[], refs := #[natA], univs := #[] }
  let base : Ix.Kernel.Reader.Store := fun a =>
    ((recs.find? (·.1 == a)).map (·.2)) <|> ((evid.find? (·.1 == a)).map (·.2))
  let store : Ix.Kernel.Reader.Store := fun a => if a == idNA then some idNRec else base a
  let blob : Address → Option ByteArray := fun a => blobs.lookup a
  let s : Subject := { table := tbl, store, blob, seeds := [idNA] }
  let rd := Reading.make s
  let x ← must "rcx idN" (rd.rcx noClasses (.member idNA 0))
  let nl := x.noLeafType (.ref 0 #[])
  check1 t "F1b noLeafType at the record's `Nat`" (nl == expectNoLeaf) s!"{nl} (expected {expectNoLeaf})"
  match rd.readDef noClasses #[] true (.member idNA 0) with
  | .ok (.body ps ..) =>
    let got := ps.toList.map (·.noLeaf)
    check1 t "F1b readDef idN: its parameter's noLeaf" (got == [expectNoLeaf]) s!"{got}"
  | .ok _ => check1 t "F1b readDef idN" false "not a body"
  | .error e => check1 t "F1b readDef idN" false s!"fails: {e}"
  match tbl.addressOf? .natRec with
  | none => check1 t "F1b Nat.rec" false "no natRec role"
  | some recA =>
    let rd2 := Reading.make { s with seeds := [recA] }
    match Ix.Kernel.Reader.resolve store recA with
    | none => check1 t "F1b Nat.rec" false "does not resolve"
    | some rr =>
      match rd2.readDef noClasses #[] false rr with
      | .ok (.stuck ps _ _ _) =>
        let got := ps.toList.map (·.noLeaf)
        let want := if expectNoLeaf then [true, false, true, true] else [false, false, false, false]
        check1 t "F1b Nat.rec's interface: noLeaf per parameter" (got == want) s!"{got}"
      | .ok _ => check1 t "F1b Nat.rec" false "not stuck"
      | .error e => check1 t "F1b Nat.rec" false s!"readDef fails: {e}"

/-! ### Finding 2: `noLeaf` on a function type -/

def app1 := mem 302
def g3 := mem 303
def g3p := mem 342

def p2 (noLeafApp1 : Bool) : Prog := prog [
  (app1, body [par .many .val arrowSk noLeafApp1] (app (v 0) [.natLit 0] .leaf) .shared .leaf),
  (g3, body [par .borrowed .leaf] (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf)
    .shared .leaf),
  -- `g3p (n : Nat) : Nat := app1 (fun _ => n)`
  (g3p, body [par .many .leaf] (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf)
    .shared .leaf)]

def f2Cases : List Case := [
  -- REPAIR A: accepted as landed
  { label := "F2 g3, app1's parameter noLeaf := true", P := p2 true, seed := g3, inp := oneNat,
    toCheck := [g3, app1], verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F2 control: noLeaf := false", P := p2 false, seed := g3, inp := oneNat, toCheck := [g3, app1],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F2 control: the captured number not borrowed", P := p2 true, seed := g3p, inp := oneNat,
    toCheck := [g3p, app1], verdict := .accept, run := [(0, .value)] }]

/-! ### Finding 3: an absurd hypothesis -/

def EqI := mem 6
def reflR := ctr 6 0
def caseEq : CaseInfo := { ind := EqI, arity := 4, major := 2, alts := #[{ alt := 3, args := #[] }] }
def idR := mem 308
def bad3 := mem 309
def g2 := mem 310

def p3 : Prog := prog [
  (EqI, .ind #[reflR]), (reflR, .ctor EqI 0 2 #[]),
  (idR, body [par .many .irr, par] (v 0)),
  (bad3, body [par .many .irr, parL] (.case caseEq .irr #[app (.const idR .val) [.irr, v 0]] #[] .leaf) .shared .leaf),
  (g2, body [par .many .irr, par .many .irr, par .borrowed .leaf]
    (app (.const bad3 .val) [.irr, .case caseEq .irr #[v 0 .leaf] #[] .val] .leaf) .shared .leaf)]

def in3 : Heap × List Val := let (b, n) := ({} : HB).alloc (.num 7); (b.heap, [.imm .irr, .imm .irr, n])

def f3Cases : List Case := [
  -- REPAIR A: accepted as landed
  { label := "F3 g2 (a cast under an absurd hypothesis)", P := p3, seed := g2, inp := in3, toCheck := [g2, bad3],
    verdict := .refuse "borrowEscape", run := [(0, .oof), (20, .vio .borrowEscape)] },
  { label := "F3 control: bad on a real list", P := p3, seed := bad3, inp := irrAndList, toCheck := [bad3],
    verdict := .accept, run := [(0, .stuck)] }]

/-! ### Finding 4: the oracle's program (Po) against the canonical one (Pc), at the program level -/

def Wi := mem 7
def wR := ctr 7 0
def caseW : CaseInfo := { ind := Wi, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0, .field 1] }] }
def leak4 := mem 311

def po4 : Prog := prog [
  (Wi, .ind #[wR]), (wR, .ctor Wi 0 0 #[fld .leaf, fld .val]),
  (leak4, body [par .borrowed .leaf, par] (.case caseW (app (.const wR .val) [v 1 .leaf, v 0])
    #[lam (par .many .leaf) (lam par (v 1 .leaf) .shared .leaf) .shared .leaf] #[] .leaf) .shared .leaf)]

def pc4 : Prog := prog [
  (Wi, .ind #[wR]), (wR, .ctor Wi 0 0 #[fld .leaf, fld .irr]),
  (leak4, body [par .borrowed .leaf, par .many .irr] (.case caseW (app (.const wR .val) [v 1 .leaf, .irr] .leaf)
    #[lam (par .many .leaf) (lam (par .many .irr) (v 1 .leaf) .shared .leaf) .shared .leaf] #[] .leaf) .shared .leaf)]

def in4 : Heap × List Val := let (b, n) := ({} : HB).alloc (.num 7); (b.heap, [n, .imm .irr])

def f4Cases : List Case := [
  -- the checker's program: its run is clean (the class gap is between two programs, finding 4's point)
  { label := "F4 Po (the oracle's program at depth 1)", P := po4, seed := leak4, inp := in4, toCheck := [leak4],
    verdict := .accept, run := [(0, .value)] },
  { label := "F4 Pc (the canonical program)", P := pc4, seed := leak4, inp := in4, toCheck := [leak4],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] }]

def former (k : Nat) : Ix.Kernel.Expr .anon :=
  (List.range k).foldl (fun acc _ => .forallE (.sort (.succ .zero)) acc default) (.sort (.succ .zero))

/-- The oracle's depth (information only until repair L). -/
def finding4oracle : IO Unit := do
  let sh : Ix.Kernel.Key .anon → Option (List CtorShape) := fun _ => none
  for (k, d) in [(1, 1), (1, 2), (16, 16), (17, 17)] do
    let c := oTypeClass Ix.Kernel.Env.empty sh {} d 0 (former k)
    let cs := match c with | .ok x => s!"ok {repr x}" | .error e => s!"error {e}"
    IO.println s!"info [F4 oracle] oTypeClass, empty env, depth {d}, a {k}-ary former: {cs}"

/-! ### Finding 5: an extern stores a confined argument in a `@shared` field -/

def mkS := mem 312
def leak5 := mem 313
def leak5c := mem 314

def p5 : Prog := prog [
  (mkS, .extern #[par] .shared .val .data),
  (leak5, body [par .borrowed] (.proj S 0 (app (.const mkS .val) [v 0]) .val)),
  (leak5c, body [par .borrowed] (.proj S 0 (app (.const sboxR .val) [v 0]) .val))]

def extS : ExternOracle := fun r args h =>
  if r == mkS then
    match args with
    | [a] => some ({ h with objs := h.objs.push ⟨.ctor sboxR #[a], h.nextCap⟩, nextCap := h.nextCap + 1 },
        .ref h.objs.size h.nextCap [])
    | _ => none
  else none

def f5Cases : List Case := [
  { label := "F5 leak5 (extern mkS)", P := p5, ext := extS, seed := leak5, inp := oneList, toCheck := [leak5],
    verdict := .accept, run := [(0, .vio .borrowEscape)], open_ := true },
  { label := "F5 control: SBox.mk itself", P := p5, ext := extS, seed := leak5c, inp := oneList,
    toCheck := [leak5c], verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] }]

/-! ### Finding 6: `check` accepts a store that does not read -/

def readName : Except String Prog → String
  | .ok P => s!"reads ({P.defs.size} constants)"
  | .error e => s!"does not read: {e}"

def verdictLong : Verdict → String
  | .accept n fp => s!"accept (checked {n}, fastPath {fp})"
  | v => verdictName v

/-- `brokenAccepted`: whether `check` (as landed) accepts the stores that do not read. -/
def finding6 (t : IO.Ref Tally) (brokenAccepted : Bool) : IO Unit := do
  let table : Ix.Kernel.RoleTable := { version := 0, bound := #[], evidence := #[] }
  let mkAx (ty : Ixon.Expr) : Ixon.Constant :=
    { info := .axio ⟨false, 0, ty⟩, sharing := #[], refs := #[], univs := #[.zero] }
  let plain := mkAx (.sort 0)
  let broken := mkAx (.ref 0 #[])
  let mk (c : Ixon.Constant) : Subject :=
    { table, store := fun a => if a == addr 200 then some c else none, seeds := [addr 200] }
  let vp := check {} Ix.Kernel.Env.empty (mk plain)
  check1 t "F6 control: `plain` (type Sort 0) on the fast path" (match vp with | .accept 0 true => true | _ => false)
    s!"{verdictLong vp}; readProg: {readName (readProg (mk plain) noClasses)}"
  let vb := check {} Ix.Kernel.Env.empty (mk broken)
  let rb := readProg (mk broken) noClasses
  check1 t "F6 fast path: a type with a reference out of range"
    (vb.isAccept == brokenAccepted && match rb with | .error _ => true | .ok _ => false)
    s!"{verdictLong vb}; readProg: {readName rb}"
  let aDef : Ixon.Definition :=
    { kind := Ix.DefKind.defn, safety := Ix.DefinitionSafety.safe, lvls := 0,
      typ := Ixon.Expr.all (.sort 0) (.sort 0), value := Ixon.Expr.lam (.sort 0) (.var 0) }
  -- v5: the erased binder's mode is in the section (type root 0, value root 1, node 0 each)
  let aRec : Ixon.Constant :=
    withSection { info := Ixon.ConstantInfo.defn aDef, sharing := #[], refs := #[], univs := #[.zero] }
      (fun _ _ _ => { input := .erased })
  let s2 : Subject :=
    { table, store := fun a => if a == addr 201 then some aRec else if a == addr 200 then some broken else none,
      seeds := [addr 201, addr 200] }
  let v2 := check {} Ix.Kernel.Env.empty s2
  check1 t "F6 slow path: a moded seed beside the broken axiom" (v2.isAccept == brokenAccepted)
    s!"{verdictLong v2}; readProg: {readName (readProg s2 noClasses)}"
  let s3 : Subject := { s2 with seeds := [addr 201] }
  let v3 := check {} Ix.Kernel.Env.empty s3
  check1 t "F6 slow path control: the moded seed alone" (match v3 with | .accept 1 false => true | _ => false)
    s!"{verdictLong v3}; readProg: {readName (readProg s3 noClasses)}"

/-! ### Finding 7: `collect` cut by fuel -/

def fR := mem 304
def gR := mem 305
def fX := mem 306
def gX := mem 307

def six : List Param :=
  [par .many .leaf, par .many .leaf, par .erased .leaf, par .many .leaf, par .many .leaf, par .many .leaf]
def sixX : List Param :=
  [par .erased .leaf, par .many .leaf, par .many .leaf, par .many .leaf, par .many .leaf, par .many .leaf]

def p7 : Prog := prog [
  (fR, body six (v 5 .leaf) .shared .leaf),
  (gR, body six (app (.const fR .val) [v 5 .leaf, v 4 .leaf, v 3 .leaf, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf)
    .shared .leaf)]

def p7x : Prog := prog [
  (fX, body sixX (v 4 .leaf) .shared .leaf),
  (gX, body sixX (app (.const fX .val) [v 5 .leaf, v 4 .leaf, v 3 .leaf, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf)
    .shared .leaf)]

def in7 : Heap × List Val :=
  let (b, n1) := ({} : HB).alloc (.num 1)
  let (b, n2) := b.alloc (.num 2)
  let (b, n3) := b.alloc (.num 3)
  let (b, n4) := b.alloc (.num 4)
  let (b, n5) := b.alloc (.num 5)
  (b.heap, [n1, n2, .imm .irr, n3, n4, n5])

def in7x : Heap × List Val :=
  let (b, n1) := ({} : HB).alloc (.num 1)
  let (b, n2) := b.alloc (.num 2)
  let (b, n3) := b.alloc (.num 3)
  let (b, n4) := b.alloc (.num 4)
  let (b, n5) := b.alloc (.num 5)
  (b.heap, [.imm .irr, n1, n2, n3, n4, n5])

def fV := mem 335
def gV := mem 336

/-- The corrected program: the erased parameter at `List Nat` (class `val`). -/
def sixV : List Param :=
  [par .many .leaf, par .many .leaf, par .erased .val (.dataApp .data .data) true, par .many .leaf, par .many .leaf,
   par .many .leaf]

def p7v : Prog := prog [
  (fV, body sixV (v 5 .leaf) .shared .leaf),
  (gV, body sixV (app (.const fV .val) [v 5 .leaf, v 4 .leaf, v 3, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf) .shared .leaf)]

def fXV := mem 343
def gXV := mem 344

/-- The control of the corrected program: the erased `List Nat` parameter first. -/
def sixXV : List Param :=
  [par .erased .val (.dataApp .data .data) true, par .many .leaf, par .many .leaf, par .many .leaf, par .many .leaf,
   par .many .leaf]

def p7xv : Prog := prog [
  (fXV, body sixXV (v 4 .leaf) .shared .leaf),
  (gXV, body sixXV (app (.const fXV .val) [v 5, v 4 .leaf, v 3 .leaf, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf)
    .shared .leaf)]

-- REPAIR B: as landed, every program below was out of fuel at 0 to 5 and the first two ended
-- in `erasedRead` at fuels 6 and 7 (a value from 8; the controls out of fuel to 7, a value from 8)
def f7Cases : List Case := [
  { label := "F7v x : List Nat erased at position 2", P := p7v, seed := gV, inp := in7, toCheck := [gV, fV],
    verdict := .accept, fuels := fuels0to12, run := [(0, .oof), (6, .value)] },
  { label := "F7v control: the erased parameter first", P := p7xv, seed := gXV, inp := in7x, toCheck := [gXV, fXV],
    verdict := .accept, fuels := fuels0to12, run := [(0, .oof), (6, .value)] },
  -- the first encoding: no input meets `InputsOk` (an erased parameter of class leaf)
  { label := "F7 x : Nat erased at position 2 (no admissible input)", P := p7, seed := gR, inp := in7,
    toCheck := [gR, fR], verdict := .accept, fuels := fuels0to12,
    run := [(0, .oof), (6, .value)], inputs := some false },
  { label := "F7 control: the erased parameter first", P := p7x, seed := gX, inp := in7x, toCheck := [gX, fX],
    verdict := .accept, fuels := fuels0to12, run := [(0, .oof), (6, .value)], inputs := some false }]

/-! ### Finding 8: a unique value stored twice in one cell -/

def dup := mem 315
def deep8 := mem 316
def dup2 := mem 345
def pairOk := mem 346

def p8 : Prog := prog [
  (dup, body [par .unique] (app (.const consumeR .val) [app (.const consR .val) [.irr, v 0, v 0]] .leaf) .shared .leaf),
  (deep8, body [par .unique] (onList (v 0) (.natLit 0)
      (add (app (.const consumeR .val) [app (.const consR .val) [.irr, v 1, v 0]] .leaf) (lenOf (v 0))) .val .leaf)
    .shared .leaf),
  -- `dup2 (@unique x : List Nat) : Nat := consume [x, x]`, the second through a cell of its own
  (dup2, body [par .unique] (app (.const consumeR .val) [app (.const consR .val)
    [.irr, v 0, app (.const consR .val) [.irr, v 0, app (.const nilR .val) [.irr] .imm]]] .leaf) .shared .leaf),
  -- `pairOk (@unique x y : List Nat) : Nat := consume (x :: y)`
  (pairOk, body [par .unique, par .unique] (app (.const consumeR .val) [app (.const consR .val) [.irr, v 1, v 0]] .leaf)
    .shared .leaf)]

def twoLists : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, ys) := b.list [3]
  (b.heap, [xs, ys])

def f8Cases : List Case := [
  -- REPAIR C: accepted as landed
  { label := "F8 dup: consume (x :: x)", P := p8, seed := dup, inp := oneList, toCheck := [dup],
    verdict := .refuse "revokedUse: a value that may be shared, at a unique position", run := [(0, .vio .revokedUse)] },
  -- REPAIR C: accepted as landed
  { label := "F8 dup2: consume [x, x]", P := p8, seed := dup2, inp := oneList, toCheck := [dup2],
    verdict := .refuse "revokedUse: a value that may be shared, at a unique position", run := [(0, .vio .revokedUse)] },
  { label := "F8 control: their `deep`", P := p8, seed := deep8, inp := oneList, toCheck := [deep8],
    verdict := .refuse "revokedUse", run := [(0, .oof), (20, .vio .revokedUse)] },
  { label := "F8 control: consume (x :: y), two unique lists", P := p8, seed := pairOk, inp := twoLists,
    toCheck := [pairOk], verdict := .accept, run := [(0, .valOrOof), (20, .value)] }]

/-! ### Finding 9: `applyValue` drops the function's regions -/

def g5 := mem 317
def g5c := mem 318
def g5p := mem 353

def p9 : Prog := prog [
  (g5, body [par .borrowed] (.letE (.value .many) .val (lam (par .many .leaf) (v 1) .shared .val) (app (v 0) [.natLit 0]))),
  (g5c, body [par .borrowed] (lam (par .many .leaf) (v 1) .shared .val) .shared .val arrowSk),
  -- `g5p (xs : List Nat) : List Nat := let f := fun _ => xs; f 0`
  (g5p, body [par] (.letE (.value .many) .val (lam (par .many .leaf) (v 1) .shared .val) (app (v 0) [.natLit 0])))]

def f9Cases : List Case := [
  -- REPAIR D: accepted as landed
  { label := "F9 g5: let f := fun _ => xs; f 0", P := p9, seed := g5, inp := oneList, toCheck := [g5],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F9 control: the closure returned", P := p9, seed := g5c, inp := oneList, toCheck := [g5c],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F9 control: xs not borrowed", P := p9, seed := g5p, inp := oneList, toCheck := [g5p],
    verdict := .accept, run := [(0, .valOrOof), (20, .value)] }]

/-! ### Two more, found while writing repair D (by reading; run): a partial application of a
function value holding a value moved into it is once-only, and the checker reused it

`kc17 (@unique a : List Nat) (n : Nat) : Nat := n`; `kc3 (@unique a : List Nat) (b c : Nat) : Nat := b`.
* D1 `d1 (k : (@unique a : List Nat) → Nat → Nat) (@unique x : List Nat) : Nat := let h := k x; h 1 + h 2`:
  `k x` is a partial application holding `x` (transferred into it); its first call transfers `x`
  again, so its second call is `revokedUse`.
* D2 `d2 (@unique x : List Nat) : Nat := let h := kc3 x; let h2 := h 1; h2 2 + h2 3`: `h` is
  once-only (`papVal`), but `h2 := h 1` is a partial application holding the same moved value and
  was not once-only.
Repair D (r2) refuses both, because the result's aliases include the moved argument (D1) or the
consumed once-only binding (D2), which are dead. The same dead alias refuses the honest single
uses D1' `k x 1` and D2' `let h := kc3 x; h 1 2`, which run to a value: a cost of r2 as written. -/

def kc17 := mem 347
def d1 := mem 348
def d1h := mem 349
def kc3 := mem 350
def d2 := mem 351
def d2h := mem 352

def skU : Skel := .arrow .unique .data .shared (.arrow .many .data .shared .data)

def pD : Prog := prog [
  (kc17, body [par .unique, par .many .leaf] (v 0 .leaf) .shared .leaf),
  (kc3, body [par .unique, par .many .leaf, par .many .leaf] (v 1 .leaf) .shared .leaf),
  (d1, body [par .many .val skU, par .unique] (.letE (.value .many) .val (app (v 1) [v 0] .val)
    (add (app (v 0) [.natLit 1] .leaf) (app (v 0) [.natLit 2] .leaf))) .shared .leaf),
  (d1h, body [par .many .val skU, par .unique] (app (v 1) [v 0, .natLit 1] .leaf) .shared .leaf),
  (d2, body [par .unique] (.letE (.value .many) .val (app (.const kc3 .val) [v 0] .val)
    (.letE (.value .many) .val (app (v 0) [.natLit 1] .val)
      (add (app (v 0) [.natLit 2] .leaf) (app (v 0) [.natLit 3] .leaf)))) .shared .leaf),
  (d2h, body [par .unique] (.letE (.value .many) .val (app (.const kc3 .val) [v 0] .val)
    (app (v 0) [.natLit 1, .natLit 2] .leaf)) .shared .leaf)]

def inD1 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, k) := b.alloc (.pap kc17 #[])
  (b.heap, [k, xs])

def dCases : List Case := [
  -- REPAIR D: accepted as landed
  { label := "D1 let h := k x; h 1 + h 2 (k's binder unique)", P := pD, seed := d1, inp := inD1, toCheck := [d1],
    verdict := .refuse "revokedUse", run := [(0, .vioOrOof .revokedUse), (100000, .vio .revokedUse)] },
  -- REPAIR D: accepted as landed; refused now, its run a value (cost of r2)
  { label := "D1' k x 1 (cost: refused, runs clean)", P := pD, seed := d1h, inp := inD1, toCheck := [d1h],
    verdict := .refuse "revokedUse", run := [(0, .valOrOof), (100000, .value)] },
  -- REPAIR D: accepted as landed
  { label := "D2 let h := kc3 x; let h2 := h 1; h2 2 + h2 3", P := pD, seed := d2, inp := oneList,
    toCheck := [d2], verdict := .refuse "revokedUse",
    run := [(0, .vioOrOof .revokedUse), (100000, .vio .revokedUse)] },
  -- REPAIR D: accepted as landed; refused now, its run a value (cost of r2)
  { label := "D2' let h := kc3 x; h 1 2 (cost: refused, runs clean)", P := pD, seed := d2h, inp := oneList,
    toCheck := [d2h], verdict := .refuse "revokedUse", run := [(0, .valOrOof), (100000, .value)] }]

/-! ### Findings 10 and 11: once -/

def callTwice := mem 319
def bad10 := mem 320
def alias10 := mem 321
def capOnce10 := mem 322
def h11 := mem 323
def twiceCall11 := mem 324
def callOnce := mem 357
def ok10 := mem 358
def ok11 := mem 359
def useBox := mem 360
def bad11b := mem 361

def p10 : Prog := prog [
  (callTwice, body [par .many .val arrowSk true] (add (app (v 0) [.natLit 0] .leaf) (app (v 0) [.natLit 1] .leaf))
    .shared .leaf),
  (bad10, body [par .unique] (app (.const callTwice .val)
    [lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf] .leaf) .shared .leaf),
  (alias10, body [par .unique] (.letE (.value .many) .val
    (lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf)
    (.letE (.value .many) .val (v 0) (add (app (v 0) [.natLit 0] .leaf) (app (v 1) [.natLit 0] .leaf)))) .shared .leaf),
  (capOnce10, body [par .unique]
    (.letE (.value .many) .val (lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf)
      (add (app (v 0) [.natLit 0] .leaf) (app (v 0) [.natLit 1] .leaf))) .shared .leaf),
  (h11, body [par .once .val arrowSk] (app (.const callTwice .val) [v 0] .leaf) .shared .leaf),
  (twiceCall11, body [par .once .val arrowSk]
    (add (app (v 0) [.natLit 1] .leaf) (app (v 0) [.natLit 2] .leaf)) .shared .leaf),
  -- `callOnce (@once f : Nat → Nat) : Nat := f 0`
  (callOnce, body [par .once .val arrowSk] (app (v 0) [.natLit 0] .leaf) .shared .leaf),
  -- `ok10 (@unique xs) : Nat := callOnce (fun _ => consume xs)`; `ok11 (@once f) : Nat := callOnce f`
  (ok10, body [par .unique] (app (.const callOnce .val)
    [lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf] .leaf) .shared .leaf),
  (ok11, body [par .once .val arrowSk] (app (.const callOnce .val) [v 0] .leaf) .shared .leaf),
  -- `useBox (b : Box (Nat → Nat)) : Nat := b.1 0 + b.1 1`; `bad11b (@once f) : Nat := useBox ⟨f⟩`
  (useBox, body [par] (add (app (.proj B 0 (v 0) .val) [.natLit 0] .leaf) (app (.proj B 0 (v 0) .val) [.natLit 1] .leaf))
    .shared .leaf),
  (bad11b, body [par .once .val arrowSk] (app (.const useBox .val) [app (.const boxR .val) [v 0]] .leaf) .shared .leaf)]

def f10Cases : List Case := [
  -- REPAIR E: accepted as landed
  { label := "F10a bad10: a once-only closure lent to callTwice", P := p10, seed := bad10, inp := oneList,
    toCheck := [bad10, callTwice], verdict := .refuse "onceReentry",
    run := [(0, .oof), (20, .vio .revokedUse)] },
  -- REPAIR E: accepted as landed
  { label := "F10b alias10: a once-only closure aliased by a let", P := p10, seed := alias10, inp := oneList,
    toCheck := [alias10], verdict := .refuse "revokedUse", run := [(0, .oof), (20, .vio .revokedUse)] },
  { label := "F10 control: their `capOnce`", P := p10, seed := capOnce10, inp := oneList, toCheck := [capOnce10],
    verdict := .refuse "revokedUse", run := [(0, .oof), (20, .vio .revokedUse)] },
  { label := "F10 control: the once-only closure passed to a once parameter", P := p10, seed := ok10, inp := oneList,
    toCheck := [ok10, callOnce], verdict := .accept, run := [(0, .valOrOof), (100000, .value)] }]

def f11Cases : List Case := [
  -- REPAIR E: accepted as landed
  { label := "F11 h11: a once binding passed to callTwice", P := p10, seed := h11, inp := oneFun,
    toCheck := [h11, callTwice], verdict := .refuse "onceReentry", run := [(0, .oof), (20, .vio .onceReentry)] },
  { label := "F11 control: their `once: called twice`", P := p10, seed := twiceCall11, inp := oneFun,
    toCheck := [twiceCall11], verdict := .refuse "onceReentry", run := [(0, .oof), (20, .vio .onceReentry)] },
  { label := "F11 control: the once binding passed to a once parameter", P := p10, seed := ok11, inp := oneFun,
    toCheck := [ok11, callOnce], verdict := .accept, run := [(0, .valOrOof), (100000, .value)] }]

/-! ### Finding 12: a primitive's partial application -/

def addB := mem 325
def addBc := mem 326
def addP := mem 362
def addBb := mem 363

def p12 : Prog := prog [
  (addB, body [par .borrowed .leaf] (app (.const addR .val) [v 0 .leaf] .val) .shared .val arrowSk),
  (addBc, body [par .borrowed .leaf] (app (.const consR .val) [.irr, v 0 .leaf] .val) .shared .val arrowSk),
  -- `addP (n : Nat) : Nat → Nat := Nat.add n`
  (addP, body [par .many .leaf] (app (.const addR .val) [v 0 .leaf] .val) .shared .val arrowSk),
  -- `addBb (@borrowed n : Nat) : Nat := let g := Nat.add n; g 1`
  (addBb, body [par .borrowed .leaf] (.letE (.value .many) .val (app (.const addR .val) [v 0 .leaf] .val)
    (app (v 0) [.natLit 1] .leaf)) .shared .leaf)]

def f12Cases : List Case := [
  -- REPAIR F: accepted as landed
  { label := "F12 addB n := Nat.add n", P := p12, seed := addB, inp := oneNat, toCheck := [addB],
    verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F12 control: a constructor's partial application", P := p12, seed := addBc, inp := oneNat,
    toCheck := [addBc], verdict := .refuse "borrowEscape", run := [(0, .vio .borrowEscape)] },
  { label := "F12 control: n not borrowed", P := p12, seed := addP, inp := oneNat, toCheck := [addP],
    verdict := .accept, run := [(0, .valOrOof), (100000, .value)] },
  -- REPAIR F: accepted before F; refused now, the run clean (the sum is a fresh number): the
  -- partial application carries `n`'s regions, and applying it gives a leaf carrying the function
  -- value's regions (repair D), as a `shared` leaf result carries its arguments' (repair A)
  { label := "F12 cost: let g := Nat.add n; g 1, n borrowed", P := p12, seed := addBb,
    inp := oneNat, toCheck := [addBb], verdict := .refuse "borrowEscape", run := [(0, .valOrOof), (100000, .value)] }]

/-! ### Finding 13: a two-argument function value -/

def sk13 : Skel := .arrow .borrowed .data .shared (.arrow .many .data .shared .data)
def kk := mem 327
def use13 := mem 328
def use13c := mem 329
def kk0 := mem 334

def p13 : Prog := prog [
  -- `kk (@borrowed a : List Nat) (n : Nat) : Nat := match a with | [] => 0 | _ => 1` (MT's `kk`
  -- read `len a`, which the checker refuses since repair A, a borrowed list's length being a
  -- leaf carrying its region; that hid the finding, so `kk` reads `a` by a match instead)
  (kk, body [par .borrowed, par .many .leaf] (onList (v 1) (.natLit 0) (.natLit 1) .val .leaf) .shared .leaf),
  (kk0, body [par .borrowed, par .many .leaf] (.natLit 0) .shared .leaf),
  (use13, body [par .many .val sk13, par .unique]
    (app (v 1) [v 0, app (.const consumeR .val) [v 0] .leaf] .leaf) .shared .leaf),
  (use13c, body [par .unique] (app (.const kk .val) [v 0, app (.const consumeR .val) [v 0] .leaf] .leaf) .shared .leaf)]

def in13 (k : Ref) : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, f) := b.alloc (.pap k #[])
  (b.heap, [f, xs])

def f13Cases : List Case := [
  -- REPAIR D: accepted as landed; refused since D (the first application's result aliases `y`,
  -- consumed before the second application); repair G is the finding's own repair
  { label := "F13 use13: k y (consume y)", P := p13, seed := use13, inp := in13 kk, toCheck := [use13, kk],
    verdict := .refuse "revokedUse", run := [(0, .vio .revokedUse)] },
  { label := "F13 control: the saturated call kk y (consume y)", P := p13, seed := use13c, inp := oneList,
    toCheck := [use13c, kk], verdict := .refuse "revokedUse", run := [(0, .vio .revokedUse)] },
  -- REPAIR D: accepted as landed; refused now (the checker judges `use13` by `k`'s skeleton,
  -- which lets `k` read its first argument); the run is a value, `k` never reading it
  { label := "F13 localiser: a k that never reads its first argument", P := p13, seed := use13, inp := in13 kk0,
    toCheck := [use13], verdict := .refuse "revokedUse", run := [(0, .valOrOof), (20, .value)] }]

/-! ### Finding 14: `DefaultOk` -/

def mk14 := mem 330
def s14 := mem 331

def p14 : Prog :=
  { defs := lib.filter (·.2.defaultModes) ++ #[
      (mk14, .extern #[par .many .leaf] .shared .val .data),
      (s14, body [par .many .leaf] (lenOf (app (.const mk14 .val) [v 0 .leaf])) .shared .leaf)],
    nat := some natR }

def ext14 (off : Nat) : ExternOracle := fun r args h =>
  if r == mk14 then
    match args with
    | [a] => some ({ h with objs := h.objs.push ⟨.ctor consR #[a, .imm (.con nilR)], h.nextCap⟩,
                            nextCap := h.nextCap + 1 },
        .ref h.objs.size (h.nextCap + off) [])
    | _ => none
  else none

def f14Cases : List Case := [
  { label := "F14 an all-default program, an extern returning a dead reference", P := p14, ext := ext14 7,
    seed := s14, inp := oneNat, toCheck := [s14], verdict := .accept, run := [(0, .vio .revokedUse)], open_ := true },
  { label := "F14 control: the extern returns its cell's capability", P := p14, ext := ext14 0, seed := s14,
    inp := oneNat, toCheck := [s14], verdict := .accept, run := [(0, .oof), (20, .value)] }]

/-! ### Finding 15: an input cell's field outside its class (MT's encoding) -/

def NP := mem 8
def npR := ctr 8 0
def caseNP : CaseInfo := { ind := NP, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0, .field 1] }] }
def mkK := mem 332
def g15 := mem 333

def p15 : Prog := prog [
  (NP, .ind #[npR]), (npR, .ctor NP 0 0 #[fld .leaf, fld .leaf]),
  (mkK, body [par .many .irr, par .many .irr, par .many .val .unknown, par .many .val .unknown]
    (lam (par .many .leaf) (v 2) .shared .val) .shared .val (.arrow .many .data .shared .unknown)),
  (g15, body [par .borrowed] (.case caseNP (v 0) #[app (.const mkK .val) [.irr, .irr]] #[] .val)
    .shared .val arrowSk)]

def in15 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1]
  let (b, n) := b.alloc (.num 3)
  let (b, k) := b.alloc (.ctor npR #[xs, n])
  (b.heap, [k])

def in15ok : Heap × List Val :=
  let (b, n0) := ({} : HB).alloc (.num 2)
  let (b, n) := b.alloc (.num 3)
  let (b, k) := b.alloc (.ctor npR #[n0, n])
  (b.heap, [k])

def f15Cases : List Case := [
  { label := "F15 g15 on an ill-typed input (field 0 a list cell)", P := p15, seed := g15, inp := in15,
    toCheck := [g15, mkK], verdict := .accept, run := [(0, .vio .borrowEscape)], open_ := true },
  { label := "F15 control: a well-typed input", P := p15, seed := g15, inp := in15ok, toCheck := [g15, mkK],
    verdict := .accept, run := [(0, .value)] }]

/-! ### Finding 16: a case's extra arguments judged at the case's class -/

def E2 := mem 9
def e0R := ctr 9 0
def e1R := ctr 9 1
def caseE : CaseInfo :=
  { ind := E2, arity := 3, major := 0, alts := #[{ alt := 1, args := #[] }, { alt := 2, args := #[] }] }
def kk16 := mem 337
def use16 := mem 338
def use16c := mem 339
def use16v := mem 340
def use16p := mem 364

def sk16 : Skel := .arrow .many .data .shared (.arrow .many .data .shared .data)

def p16 : Prog := prog [
  (E2, .ind #[e0R, e1R]), (e0R, .ctor E2 0 0 #[]), (e1R, .ctor E2 1 0 #[]),
  (kk16, body [par, par .many .leaf] (lenOf (v 1)) .shared .leaf),
  (use16, body [par .many .val sk16 true, par .unique, par .many .imm .data true]
    (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, app (.const consumeR .val) [v 1] .leaf] .leaf) .shared .leaf),
  (use16c, body [par .many .val sk16 true, par .unique, par .many .imm .data true]
    (app (v 2) [v 1, app (.const consumeR .val) [v 1] .leaf] .leaf) .shared .leaf),
  (use16v, body [par .many .val sk16 true, par .unique, par .many .imm .data true]
    (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, app (.const consumeR .val) [v 1] .leaf] .val) .shared .val),
  -- `use16p (k) (y : List Nat) (b : E) : Nat := (match b with | e0 => k | e1 => k) y 1`
  (use16p, body [par .many .val sk16 true, par .many, par .many .imm .data true]
    (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, .natLit 1] .leaf) .shared .leaf)]

def in16 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, k) := b.alloc (.pap kk16 #[])
  (b.heap, [k, xs, .imm (.con e0R)])

def f16Cases : List Case := [
  -- REPAIR G: accepted as landed
  { label := "F16 use16: (match b with | _ => k) y (consume y), the case of class leaf", P := p16, seed := use16,
    inp := in16, toCheck := [use16, kk16], verdict := .refuse "revokedUse", run := [(0, .vio .revokedUse)] },
  { label := "F16 control: no case", P := p16, seed := use16c, inp := in16, toCheck := [use16c, kk16],
    verdict := .refuse "revokedUse", run := [(0, .oof), (20, .vio .revokedUse)] },
  { label := "F16 control: the case at class val", P := p16, seed := use16v, inp := in16, toCheck := [use16v, kk16],
    verdict := .refuse "revokedUse", run := [(0, .vio .revokedUse)] },
  { label := "F16 control: the case applied to a plain list and a number", P := p16, seed := use16p, inp := in16,
    toCheck := [use16p, kk16], verdict := .accept, run := [(0, .valOrOof), (100000, .value)] }]

/-! ### The routes of a once binding and of a once-only value (repair Q and after)

Every way a value read from a `@once` binding `f` can be stored, duplicated or passed on, each
beside the same program with `f` plain (the control, accepted, runs clean), and the routes of a
once-only closure `g := fun _ => consume xs` where its rules differ. `bad11b` (route 1) is the
counterexample found after E. -/

def useSBox := mem 365
def apply2 := mem 366
def retF := mem 367
def retP := mem 368
def ext9 := mem 369
def retG := mem 400

/-- The once-only closure `fun _ => consume xs`, under `n` binders above `xs`. -/
def gClo (n : Nat) : Term := lam (par .many .leaf) (app (.const consumeR .val) [v (n + 1)] .leaf) .shared .leaf

def callBoth (t : Term) : Term := add (app t [.natLit 0] .leaf) (app t [.natLit 1] .leaf)

/-- Route `i`'s body over a parameter `f` (and, for the case routes, `b : E` after it). -/
def routeBody : Nat → Term
  | 1 => app (.const useBox .val) [app (.const boxR .val) [v 0]] .leaf
  | 2 => app (.const useSBox .val) [app (.const sboxR .val) [v 0]] .leaf
  | 3 => .letE (.value .many) .val (app (.const apply2 .val) [v 0] .val) (app (v 0) [.natLit 0] .leaf)
  | 4 => app (.const callTwice .val) [lam (par .many .leaf) (app (v 1) [v 0 .leaf] .leaf) .shared .leaf] .leaf
  | 5 => .letE (.value .many) .val (v 0) (callBoth (v 0))
  | 6 => .case caseE (v 0 .imm) #[.const callTwice .val, .const callTwice .val] #[v 1] .leaf
  | 7 => app (.const callTwice .val) [.case caseE (v 0 .imm) #[v 1, v 1] #[] .val] .leaf
  | 8 => .letE (.value .many) .val (app (.const retF .val) [v 0] .val) (callBoth (v 0))
  | 9 => app (.const ext9 .val) [v 0] .leaf
  | _ => add (app (.const callOnce .val) [v 0] .leaf) (app (.const callOnce .val) [v 0] .leaf)

def routeBodyPlain (i : Nat) : Term :=
  if i == 8 then .letE (.value .many) .val (app (.const retP .val) [v 0] .val) (callBoth (v 0)) else routeBody i

def routeName : Nat → String
  | 1 => "an inherited constructor field (useBox ⟨f⟩)"
  | 2 => "a @shared constructor field (useSBox ⟨f⟩)"
  | 3 => "a partial application's argument (let p := apply2 f; p 0)"
  | 4 => "a closure's capture (callTwice (fun n => f n))"
  | 5 => "a plain let (let h := f; h 0 + h 1)"
  | 6 => "a case's extra argument ((match b with | _ => callTwice) f)"
  | 7 => "a case alternative's result (callTwice (match b with | _ => f))"
  | 8 => "the function's own result (let h := retF f; h 0 + h 1)"
  | 9 => "an extern's argument (ext9 f)"
  | _ => "two once positions (callOnce f + callOnce f)"

def routeOnce (i : Nat) : Ref := mem (369 + i)
def routePlain (i : Nat) : Ref := mem (379 + i)
def isCaseRoute (i : Nat) : Bool := i == 6 || i == 7

def routeParams (m : BinderMode) (i : Nat) : List Param :=
  if isCaseRoute i then [par m .val arrowSk, par .many .imm] else [par m .val arrowSk]

/-- The once-only closure's routes: in a cell, a case alternative's result, the function's own
result, two once positions. -/
def gBody : Nat → Term
  | 1 => .letE (.value .many) .val (gClo 0) (app (.const useBox .val) [app (.const boxR .val) [v 0]] .leaf)
  | 7 => .letE (.value .many) .val (gClo 1)
      (app (.const callTwice .val) [.case caseE (v 1 .imm) #[v 0, v 0] #[] .val] .leaf)
  | 8 => .letE (.value .many) .val (app (.const retG .val) [v 0] .val) (callBoth (v 0))
  | _ => .letE (.value .many) .val (gClo 0)
      (add (app (.const callOnce .val) [v 0] .leaf) (app (.const callOnce .val) [v 0] .leaf))

def routeG (i : Nat) : Ref := mem (389 + i)

def pQ : Prog := { p10 with defs := p10.defs ++ #[
  (E2, .ind #[e0R, e1R]), (e0R, .ctor E2 0 0 #[]), (e1R, .ctor E2 1 0 #[]),
  -- `useSBox (b : SBox (Nat → Nat)) : Nat := b.1 0 + b.1 1`
  (useSBox, body [par] (callBoth (.proj S 0 (v 0) .val)) .shared .leaf),
  -- `apply2 (k : Nat → Nat) (n : Nat) : Nat := k n + k n`
  (apply2, body [par .many .val arrowSk, par .many .leaf]
    (add (app (v 1) [v 0 .leaf] .leaf) (app (v 1) [v 0 .leaf] .leaf)) .shared .leaf),
  -- `retF (@once f : Nat → Nat) : Nat → Nat := f`; `retP` the same with `f` plain
  (retF, body [par .once .val arrowSk] (v 0) .shared .val arrowSk),
  (retP, body [par .many .val arrowSk] (v 0) .shared .val arrowSk),
  (ext9, .extern #[par .many .val arrowSk] .shared .leaf .data),
  -- `retG (@unique xs : List Nat) : Nat → Nat := fun _ => consume xs`
  (retG, body [par .unique] (gClo 0) .shared .val arrowSk)] ++
  ((List.range 10).map (· + 1)).toArray.flatMap (fun i => #[
    (routeOnce i, body (routeParams .once i) (routeBody i) .shared .leaf),
    (routePlain i, body (routeParams .many i) (routeBodyPlain i) .shared .leaf)]) ++
  #[(routeG 1, body [par .unique] (gBody 1) .shared .leaf),
    (routeG 7, body [par .unique, par .many .imm] (gBody 7) .shared .leaf),
    (routeG 8, body [par .unique] (gBody 8) .shared .leaf),
    (routeG 10, body [par .unique] (gBody 10) .shared .leaf)] }

def funAndE0 : Heap × List Val :=
  let (b, f) := ({} : HB).alloc (.pap incR #[])
  (b.heap, [f, .imm (.con e0R)])

def listAndE0 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  (b.heap, [xs, .imm (.con e0R)])

/-- What each route's once version does after this repair: the verdict (`none` an open
finding, accepted), its run. -/
def routeExpect : Nat → Option String × OExp
  | 1 => (some "onceReentry", .vio .onceReentry)          -- repair Q
  | 2 => (some "onceReentry", .vio .onceReentry)          -- E (flowTo .share)
  | 3 => (some "onceReentry", .vio .onceReentry)          -- E (papVal's flowTo .share)
  | 4 => (some "onceReentry", .vio .onceReentry)          -- E (anLam's flowTo .share)
  | 5 => (some "onceReentry", .vio .onceReentry)          -- E (bindInner)
  | 6 => (some "onceReentry", .vio .onceReentry)          -- E and G (applyValue's callResult)
  | 7 => (none, .vio .onceReentry)                         -- OPEN: the join drops `src`
  | 8 => (none, .vio .onceReentry)                         -- OPEN: retCheck looks at onceOnly only
  | 9 => (some "onceReentry", .stuck)                      -- E (callResult); no extern oracle
  | _ => (none, .vio .onceReentry)                         -- OPEN: `.once` does not test `spent`

def routeCases : List Case := ((List.range 10).map (· + 1)).flatMap fun i =>
  let inp := if isCaseRoute i then funAndE0 else oneFun
  let toCheck := if i == 8 then [routeOnce i, retF] else [routeOnce i]
  let toCheckP := if i == 8 then [routePlain i, retP] else [routePlain i]
  let (vx, ox) := routeExpect i
  let tbl (o : OExp) : Table := match o with
    | .vio k => [(0, .vioOrOof k), (100000, .vio k)]
    | .stuck => [(0, .stuck)]
    | o => [(0, o)]
  [{ label := s!"route {i}, once f: {routeName i}", P := pQ, seed := routeOnce i, inp, toCheck,
     verdict := (match vx with | some w => .refuse w | none => .accept), run := tbl ox, open_ := vx.isNone },
   { label := s!"route {i}, control, f plain: {routeName i}", P := pQ, seed := routePlain i, inp,
     toCheck := toCheckP, verdict := .accept,
     run := if i == 9 then [(0, .stuck)] else [(0, .valOrOof), (100000, .value)] }]

def routeGCases : List Case := [1, 7, 8, 10].map fun i =>
  { label := s!"route {i}, the once-only closure g: {routeName i}", P := pQ, seed := routeG i,
    inp := if i == 7 then listAndE0 else oneList,
    toCheck := if i == 8 then [routeG i, retG] else [routeG i],
    verdict := .refuse, run := [(0, .vioOrOof .revokedUse), (100000, .vio .revokedUse)] }

/-! ### Repair N: a spine longer than the checker's depth left at it (found by reading; run)

`termSpine n` cut a spine at the checker's remaining depth, so `S6.mk 1 2 3 4 5 xs` checked at
depth 6 (spine cut at 4) was judged as a partial application of `S6.mk` to two arguments followed
by four applications of a function value: `anCtor`'s partial branch does not apply the `@shared`
field's region test, and `anProj` gives a `@shared` field no region. -/

def S6 := mem 354
def s6mk := ctr 354 0
def g6 := mem 355
def g6p := mem 356

def p6 : Prog := prog [(S6, .ind #[s6mk]),
  (s6mk, .ctor S6 0 0 #[fld .leaf, fld .leaf, fld .leaf, fld .leaf, fld .leaf, fld .val .shared]),
  (g6, body [par .borrowed] (.proj S6 5 (app (.const s6mk .val)
    [.natLit 1, .natLit 2, .natLit 3, .natLit 4, .natLit 5, v 0]) .val)),
  (g6p, body [par] (.proj S6 5 (app (.const s6mk .val)
    [.natLit 1, .natLit 2, .natLit 3, .natLit 4, .natLit 5, v 0]) .val))]

def nCases : List Case := [
  -- REPAIR N: accepted as landed (at this depth)
  { label := "N g6 = (S6.mk 1 2 3 4 5 xs).sh, xs borrowed, at checker depth 6", P := p6, seed := g6, inp := oneList,
    toCheck := [g6], verdict := .refuse "borrowEscape: a borrowed value stored in a @shared field",
    run := [(0, .vioOrOof .borrowEscape), (100000, .vio .borrowEscape)], lim := { depth := 6 } },
  { label := "N control: the same at the default depth", P := p6, seed := g6, inp := oneList, toCheck := [g6],
    verdict := .refuse "borrowEscape: a borrowed value stored in a @shared field",
    run := [(0, .vioOrOof .borrowEscape), (100000, .vio .borrowEscape)] },
  { label := "N control: xs not borrowed, at checker depth 6", P := p6, seed := g6p, inp := oneList,
    toCheck := [g6p], verdict := .accept, run := [(0, .valOrOof), (100000, .value)], lim := { depth := 6 } },
  -- the borrowed one at other depths: now a refusal from depth 4 (what the whole call needs),
  -- a decline below it
  { label := "N g6 at checker depth 3", P := p6, seed := g6, inp := oneList, toCheck := [g6], verdict := .decline,
    run := [(0, .vioOrOof .borrowEscape), (100000, .vio .borrowEscape)], lim := { depth := 3 } },
  { label := "N g6 at checker depth 5", P := p6, seed := g6, inp := oneList, toCheck := [g6],
    verdict := .refuse "borrowEscape: a borrowed value stored in a @shared field",
    run := [(0, .vioOrOof .borrowEscape), (100000, .vio .borrowEscape)], lim := { depth := 5 } },
  { label := "N g6 at checker depth 7", P := p6, seed := g6, inp := oneList, toCheck := [g6],
    verdict := .refuse "borrowEscape: a borrowed value stored in a @shared field",
    run := [(0, .vioOrOof .borrowEscape), (100000, .vio .borrowEscape)], lim := { depth := 7 } },
  { label := "N g6 at checker depth 8", P := p6, seed := g6, inp := oneList, toCheck := [g6],
    verdict := .refuse "borrowEscape: a borrowed value stored in a @shared field",
    run := [(0, .vioOrOof .borrowEscape), (100000, .vio .borrowEscape)], lim := { depth := 8 } }]

def findingCases : List Case :=
  f1Cases ++ f2Cases ++ f3Cases ++ f4Cases ++ f5Cases ++ f7Cases ++ f8Cases ++ f9Cases ++ dCases ++ f10Cases ++
    f11Cases ++ routeCases ++ routeGCases ++ f12Cases ++ f13Cases ++ f14Cases ++ f15Cases ++ f16Cases ++ nCases

def run : IO UInt32 := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "== Part 1: the suite's cases without a record fixture"
  for c in suiteCases do runCase t c
  limitCase t
  fastPathCase t
  IO.println "== Part 1b: the finding cases as added to the suite"
  for c in SuiteFindings.findingCases do runCase t c
  IO.println "== Part 2: the findings"
  for c in findingCases do runCase t c
  try finding1b t false catch e => check1 t "F1b" false s!"error: {e}"
  try finding6 t true catch e => check1 t "F6" false s!"error: {e}"
  finding4oracle
  let s ← t.get
  IO.println s!"== {s.pass} passed, {s.fail} failed"
  for l in s.failed do IO.println s!"   failed: {l}"
  return if s.fail == 0 then 0 else 1

end ModeRepair

def main : IO UInt32 := ModeRepair.run
