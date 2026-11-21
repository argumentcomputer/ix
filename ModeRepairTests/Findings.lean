/- MT: the fifteen mode findings run on `jcb/ixvmc-mo` at 6db9089a7 (kernel package only).
Lines marked COPIED are copied verbatim from their Tests/Ix/ResourceModes.lean:36-152 and :156-167,
which cannot be imported (it imports the root package). Brought from `jcb/ixcc-mode-findings`
(be26cb1a8, `IxCC/plans/mt/Findings.lean`) by engineer MV; its two hand-built records carry their
binder-data sections (Ixon v5). It prints and asserts nothing: the driver (`Main.lean`) asserts the
same encodings. Run in this package: `lake -d ModeRepairTests env lean --run
ModeRepairTests/Findings.lean [all|b4]` (see README.md). -/
import IxC.Resource
import IxC.Kernel.Ixon.Prelude
-- the tester's decision procedure for `InputsOk` (difftest/DiffTest/Hyp.lean); run from the difftest package
import DiffTest.Hyp

namespace MT.Findings

open IxC.Resource Ixon

/-! ## COPIED verbatim from their Tests/Ix/ResourceModes.lean:36-152 at 6db9089a7 (branch jcb/ixvmc-mo) -/


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

/-! ## COPIED verbatim from their Tests/Ix/ResourceModes.lean:156-167 at 6db9089a7 -/

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

/-! ## END OF COPIED LINES (everything below is MT's) -/

/-! ## Driver (MT) -/

def outcomeLong : Outcome → String
  | .value v _ => s!"a value {repr v}"
  | o => outcomeName o

def stdFuels : List Nat := [10, 20, 50, 100, 1000, 100000]

/-- The checker's verdict on `toCheck`, then `runR` of `seed` at each fuel. -/
def report (label : String) (P : Prog) (ext : ExternOracle) (fuels : List Nat) (seed : Ref)
    (inp : Heap × List Val) (toCheck : List Ref) : IO Unit := do
  IO.println s!"[{label}] checker on {toCheck.length} bodies: {verdictName (checkBodies {} P toCheck)}"
  match P.find? seed with
  | some (.body ps ..) => IO.println s!"[{label}] inputs meet InputsOk (decided by inputsOkB): {MT.DiffTest.inputsOkB P inp.1 ps inp.2}"
  | _ => pure ()
  for f in fuels do
    IO.println s!"[{label}]   fuel {f}: run: {outcomeLong (runR P ext f seed inp.1 inp.2)}"

def must {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-! ## Finding 1: `noLeaf` true for `Nat` -/

def idN := mem 300
def g4 := mem 301

def p1 (noLeafIdN : Bool) : Prog := prog [
  (idN, body [par .many .leaf .data noLeafIdN] (v 0 .leaf) .shared .leaf),
  (g4, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .shared .leaf)]

def finding1a : IO Unit := do
  report "F1 noLeaf:=true" (p1 true) noExtern stdFuels g4 oneNat [g4]
  report "F1 control noLeaf:=false" (p1 false) noExtern stdFuels g4 oneNat [g4]

/-- The premise on the real `Nat` record: a store of the prelude's records, the
evidence records, and one hand-built record `idN : Nat → Nat := fun n => n`. -/
def finding1b : IO Unit := do
  let tbl ← must "defaultTable" Ix.Kernel.Reader.defaultTable
  let recs ← must "preludeRecords" Ix.Kernel.Reader.preludeRecords
  let evid ← must "evidenceRecords" Ix.Kernel.Reader.evidenceRecords
  let blobs ← must "evidenceBlobs" Ix.Kernel.Reader.evidenceBlobs
  IO.println s!"[F1b] prelude records {recs.size}, evidence records {evid.size}, blobs {blobs.length}"
  let some natA := tbl.addressOf? .nat | throw (IO.userError "no nat role")
  let idNA := addr 250
  let idNDef : Ixon.Definition :=
    { kind := Ix.DefKind.defn, safety := Ix.DefinitionSafety.safe, lvls := 0,
      typ := Ixon.Expr.leanAll (.ref 0 #[]) (.ref 0 #[]), value := Ixon.Expr.leanLam (.ref 0 #[]) (.var 0) }
  let idNRec : Ixon.Constant :=
    { info := Ixon.ConstantInfo.defn idNDef, sharing := #[], refs := #[natA], univs := #[],
      -- v5: the section holds the binder modes (type root 0, value root 1, one node each)
      binders := #[{ shared := false, index := 0, variant := 0, nodes := #[.never {}] },
                   { shared := false, index := 1, variant := 0, nodes := #[.never {}] }] }
  let base : Ix.Kernel.Reader.Store := fun a =>
    ((recs.find? (·.1 == a)).map (·.2)) <|> ((evid.find? (·.1 == a)).map (·.2))
  let store : Ix.Kernel.Reader.Store := fun a => if a == idNA then some idNRec else base a
  let blob : Address → Option ByteArray := fun a => blobs.lookup a
  let natRef? := Ix.Kernel.Reader.resolve store natA
  IO.println s!"[F1b] nat role address {natA} resolves to {repr natRef?}"
  let s : Subject := { table := tbl, store, blob, seeds := [idNA] }
  match natRef? with
  | some nr =>
    match inductiveAt? s nr with
    | some ind => IO.println s!"[F1b] the inductive at Nat's reference: {ind.ctors.size} constructors, {ind.params} params"
    | none => IO.println "[F1b] no inductive at Nat's reference"
  | none => pure ()
  let rd := Reading.make s
  IO.println s!"[F1b] closure of idN: {rd.closure.size} records"
  let x ← must "rcx idN" (rd.rcx noClasses (.member idNA 0))
  IO.println s!"[F1b] RCx.noLeafType at the domain `Nat` (Expr.ref 0, refs[0] = nat role address): {x.noLeafType (.ref 0 #[])}"
  match rd.readDef noClasses #[] true (.member idNA 0) with
  | .ok (.body ps res rc rs _) =>
    IO.println s!"[F1b] readDef idN (call site openParams, Read.lean:399): params {repr ps}, result {repr res} {repr rc} {repr rs}"
  | .ok _ => IO.println "[F1b] readDef idN: not a body"
  | .error e => IO.println s!"[F1b] readDef idN fails: {e}"
  -- the real recursor record `Nat.rec`: its interface's parameters (stuckAt → readIface → openParams)
  match tbl.addressOf? .natRec with
  | none => IO.println "[F1b] no natRec role"
  | some recA =>
    let s2 : Subject := { table := tbl, store, blob, seeds := [recA] }
    let rd2 := Reading.make s2
    match Ix.Kernel.Reader.resolve store recA with
    | none => IO.println "[F1b] natRec does not resolve"
    | some rr =>
      match rd2.readDef noClasses #[] false rr with
      | .ok (.stuck ps _ _ _) =>
        IO.println s!"[F1b] Nat.rec's interface (prelude record, untouched): {ps.size} params, noLeaf per param {repr (ps.map (fun (p : Param) => p.noLeaf))}"
      | .ok _ => IO.println "[F1b] Nat.rec: not stuck"
      | .error e => IO.println s!"[F1b] readDef Nat.rec fails: {e}"

/-! ## Finding 2: `noLeaf` on a function type -/

def app1 := mem 302
def g3 := mem 303

def p2 (noLeafApp1 : Bool) : Prog := prog [
  (app1, body [par .many .val arrowSk noLeafApp1] (app (v 0) [.natLit 0] .leaf) .shared .leaf),
  (g3, body [par .borrowed .leaf] (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf)
    .shared .leaf)]

def finding2 : IO Unit := do
  report "F2 noLeaf:=true" (p2 true) noExtern stdFuels g3 oneNat [g3, app1]
  report "F2 control noLeaf:=false" (p2 false) noExtern stdFuels g3 oneNat [g3, app1]

/-! ## Finding 7: `collect` cut by fuel -/

def fR := mem 304
def gR := mem 305
def fX := mem 306
def gX := mem 307

def six : List Param :=
  [par .many .leaf, par .many .leaf, par .erased .leaf, par .many .leaf, par .many .leaf, par .many .leaf]
def sixX : List Param :=
  [par .erased .leaf, par .many .leaf, par .many .leaf, par .many .leaf, par .many .leaf, par .many .leaf]

def allArgs : Term := app (.const fR .val) [v 5 .leaf, v 4 .leaf, v 3 .leaf, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf

def p7 : Prog := prog [
  (fR, body six (v 5 .leaf) .shared .leaf),
  (gR, body six allArgs .shared .leaf)]

/-- Control: the erased parameter first. -/
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

def fuels7 : List Nat := (List.range 13) ++ [100000]

def finding7 : IO Unit := do
  report "F7 x at position 2" p7 noExtern fuels7 gR in7 [gR, fR]
  report "F7 control x at position 0" p7x noExtern fuels7 gX in7x [gX, fX]

/-! ## Finding 3: absurd hypothesis -/

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

def finding3 : IO Unit := do
  report "F3 g2" p3 noExtern stdFuels g2 in3 [g2, bad3]
  report "F3 control: bad on a real list" p3 noExtern stdFuels bad3 irrAndList [bad3]

/-! ## Finding 4: the oracle's program (Po) against the canonical one (Pc) -/

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

/-- The oracle's class of `Type → Type` and of a 17-ary former at depths 1, 2, 16, 17
(no constant is involved, so the empty environment suffices). -/
def former (k : Nat) : Ix.Kernel.Expr .anon :=
  (List.range k).foldl (fun acc _ => .forallE (.sort (.succ .zero)) acc default) (.sort (.succ .zero))

def finding4 : IO Unit := do
  report "F4 Po (oracle's program): check; run for information" po4 noExtern stdFuels leak4 in4 [leak4]
  report "F4 Pc (canonical program)" pc4 noExtern stdFuels leak4 in4 [leak4]
  let sh : Ix.Kernel.Key .anon → Option (List CtorShape) := fun _ => none
  for (k, d) in [(1, 1), (1, 2), (17, 16), (17, 17), (16, 16)] do
    let c := oTypeClass Ix.Kernel.Env.empty sh {} d [] 0 (former k)
    let cs := match c with | .ok x => s!"ok {repr x}" | .error e => s!"error {e}"
    IO.println s!"[F4 oracle] oTypeClass, empty env, depth {d}, a {k}-ary former (Type → … → Type): {cs}"

/-! ## Finding 5: an extern stores a confined argument in a `@shared` field -/

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

def finding5 : IO Unit := do
  report "F5 extern mkS" p5 extS stdFuels leak5 oneList [leak5]
  report "F5 control: SBox.mk itself" p5 extS stdFuels leak5c oneList [leak5c]

/-! ## Finding 6: `check` accepts a store that does not read -/

def allIrr : Classifier := { type := fun _ _ => .ok .irr, node := fun _ _ => .ok .irr }

def verdictLong : Verdict → String
  | .accept n fp => s!"accept (checked {n}, fastPath {fp})"
  | v => verdictName v

def readName : Except String Prog → String
  | .ok P => s!"reads ({P.defs.size} constants)"
  | .error e => s!"does not read: {e}"

def finding6 : IO Unit := do
  let table : Ix.Kernel.RoleTable := { version := 0, bound := #[], evidence := #[] }
  let mkAx (ty : Ixon.Expr) : Ixon.Constant :=
    { info := .axio ⟨false, 0, ty⟩, sharing := #[], refs := #[], univs := #[.zero] }
  let plain := mkAx (.sort 0)
  let broken := mkAx (.ref 0 #[])
  let mk (c : Ixon.Constant) : Subject :=
    { table, store := fun a => if a == addr 200 then some c else none, seeds := [addr 200] }
  for (lbl, c) in [("F6 control: their `plain` (type Sort 0)", plain), ("F6 fast path: type a reference out of range", broken)] do
    let s := mk c
    IO.println s!"[{lbl}] check (default limits, Env.empty): {verdictLong (check {} Ix.Kernel.Env.empty s)}"
    IO.println s!"[{lbl}] readProg noClasses: {readName (readProg s noClasses)}"
    IO.println s!"[{lbl}] readProg allIrr: {readName (readProg s allIrr)}"
  -- the slow path: a second seed, default and unreadable, beside a non-default record
  let erasedM : AllMode := { input := .erased }
  let aDef : Ixon.Definition :=
    { kind := Ix.DefKind.defn, safety := Ix.DefinitionSafety.safe, lvls := 0,
      typ := Ixon.Expr.all (.sort 0) (.sort 0), value := Ixon.Expr.lam (.sort 0) (.var 0) }
  let aRec : Ixon.Constant :=
    { info := Ixon.ConstantInfo.defn aDef, sharing := #[], refs := #[], univs := #[.zero],
      binders := #[{ shared := false, index := 0, variant := 0, nodes := #[.never erasedM] },
                   { shared := false, index := 1, variant := 0, nodes := #[.never erasedM] }] }
  let s2 : Subject :=
    { table, store := fun a => if a == addr 201 then some aRec else if a == addr 200 then some broken else none,
      seeds := [addr 201, addr 200] }
  IO.println s!"[F6 slow path: seeds A (erased binder) and the broken axiom] check (default limits, Env.empty): {verdictLong (check {} Ix.Kernel.Env.empty s2)}"
  IO.println s!"[F6 slow path] readProg noClasses: {readName (readProg s2 noClasses)}"
  let s3 : Subject := { s2 with seeds := [addr 201] }
  IO.println s!"[F6 slow path control: seed A alone] check (default limits, Env.empty): {verdictLong (check {} Ix.Kernel.Env.empty s3)}"
  IO.println s!"[F6 slow path control] readProg noClasses: {readName (readProg s3 noClasses)}"

/-! ## Finding 8: a unique value stored twice in one cell -/

def dup := mem 315
def deep8 := mem 316

def p8 : Prog := prog [
  (dup, body [par .unique] (app (.const consumeR .val) [app (.const consR .val) [.irr, v 0, v 0]] .leaf) .shared .leaf),
  (deep8, body [par .unique] (onList (v 0) (.natLit 0)
      (add (app (.const consumeR .val) [app (.const consR .val) [.irr, v 1, v 0]] .leaf) (lenOf (v 0))) .val .leaf)
    .shared .leaf)]

def finding8 : IO Unit := do
  report "F8 dup" p8 noExtern stdFuels dup oneList [dup]
  report "F8 control: their `deep`" p8 noExtern stdFuels deep8 oneList [deep8]

/-! ## Finding 9: `applyValue` drops the function's regions -/

def g5 := mem 317
def g5c := mem 318

def p9 : Prog := prog [
  (g5, body [par .borrowed] (.letE (.value .many) .val (lam (par .many .leaf) (v 1) .shared .val) (app (v 0) [.natLit 0]))),
  (g5c, body [par .borrowed] (lam (par .many .leaf) (v 1) .shared .val) .shared .val arrowSk)]

def finding9 : IO Unit := do
  report "F9 g5" p9 noExtern stdFuels g5 oneList [g5]
  report "F9 control: the closure returned" p9 noExtern stdFuels g5c oneList [g5c]

/-! ## Finding 10: a once-only closure lent; Finding 11: a once binding passed on -/

def callTwice := mem 319
def bad10 := mem 320
def alias10 := mem 321
def capOnce10 := mem 322
def h11 := mem 323
def twiceCall11 := mem 324

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
    (add (app (v 0) [.natLit 1] .leaf) (app (v 0) [.natLit 2] .leaf)) .shared .leaf)]

def finding10 : IO Unit := do
  report "F10a bad10" p10 noExtern stdFuels bad10 oneList [bad10, callTwice]
  report "F10b alias10" p10 noExtern stdFuels alias10 oneList [alias10]
  report "F10 control: their `capOnce`" p10 noExtern stdFuels capOnce10 oneList [capOnce10]

def finding11 : IO Unit := do
  report "F11 h11" p10 noExtern stdFuels h11 oneFun [h11, callTwice]
  report "F11 control: their `once: called twice`" p10 noExtern stdFuels twiceCall11 oneFun [twiceCall11]

/-! ## Finding 12: a primitive's partial application -/

def addB := mem 325
def addBc := mem 326

def p12 : Prog := prog [
  (addB, body [par .borrowed .leaf] (app (.const addR .val) [v 0 .leaf] .val) .shared .val arrowSk),
  (addBc, body [par .borrowed .leaf] (app (.const consR .val) [.irr, v 0 .leaf] .val) .shared .val arrowSk)]

def finding12 : IO Unit := do
  report "F12 addB" p12 noExtern stdFuels addB oneNat [addB]
  report "F12 control: a constructor's partial application" p12 noExtern stdFuels addBc oneNat [addBc]

/-! ## Finding 13: a two-argument function value -/

def sk13 : Skel := .arrow .borrowed .data .shared (.arrow .many .data .shared .data)
def kk := mem 327
def use13 := mem 328
def use13c := mem 329

def p13 : Prog := prog [
  (kk, body [par .borrowed, par .many .leaf] (lenOf (v 1)) .shared .leaf),
  (use13, body [par .many .val sk13, par .unique]
    (app (v 1) [v 0, app (.const consumeR .val) [v 0] .leaf] .leaf) .shared .leaf),
  (use13c, body [par .unique] (app (.const kk .val) [v 0, app (.const consumeR .val) [v 0] .leaf] .leaf) .shared .leaf)]

def in13 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, k) := b.alloc (.pap kk #[])
  (b.heap, [k, xs])

def finding13 : IO Unit := do
  report "F13 use13" p13 noExtern stdFuels use13 in13 [use13, kk]
  report "F13 control: the saturated call kk y (consume y)" p13 noExtern stdFuels use13c oneList [use13c, kk]
  -- localiser: the same use13 with a k that never reads its borrowed argument
  let kk0 := mem 334
  let p13z : Prog := { p13 with defs := p13.defs.push (kk0, body [par .borrowed, par .many .leaf] (.natLit 0) .shared .leaf) }
  let in13z : Heap × List Val :=
    let (b, xs) := ({} : HB).list [1, 2]
    let (b, k) := b.alloc (.pap kk0 #[])
    (b.heap, [k, xs])
  report "F13 localiser: k never reads a" p13z noExtern stdFuels use13 in13z [use13]

/-! ## Finding 14: `DefaultOk` -/

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

def finding14 : IO Unit := do
  IO.println s!"[F14] every constant of p14 has default modes: {p14.defs.all (·.2.defaultModes)} ({p14.defs.size} constants; dropped from lib: {lib.size - (lib.filter (·.2.defaultModes)).size})"
  report "F14 oracle returns cap nextCap+7" p14 (ext14 7) stdFuels s14 oneNat [s14]
  report "F14 control: oracle returns cap nextCap" p14 (ext14 0) stdFuels s14 oneNat [s14]

/-! ## Finding 15 (MT's encoding, not MS's): an input cell's field outside its class -/

def NP := mem 8
def npR := ctr 8 0
def caseNP : CaseInfo := { ind := NP, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0, .field 1] }] }
def mkK := mem 332
def g15 := mem 333

/-- `mkK {α β} (a : α) (b : β) : Nat → α := fun _ => a`;
`g15 (@borrowed k : NP) : Nat → Nat := NP.casesOn k (@mkK Nat Nat)` (a non-λ alternative). -/
def p15 : Prog := prog [
  (NP, .ind #[npR]), (npR, .ctor NP 0 0 #[fld .leaf, fld .leaf]),
  (mkK, body [par .many .irr, par .many .irr, par .many .val .unknown, par .many .val .unknown]
    (lam (par .many .leaf) (v 2) .shared .val) .shared .val (.arrow .many .data .shared .unknown)),
  (g15, body [par .borrowed] (.case caseNP (v 0) #[app (.const mkK .val) [.irr, .irr]] #[] .val)
    .shared .val arrowSk)]

/-- Ill-typed: field 0 (class leaf, `Nat`) holds a list cell. -/
def in15 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1]
  let (b, n) := b.alloc (.num 3)
  let (b, k) := b.alloc (.ctor npR #[xs, n])
  (b.heap, [k])

/-- Well-typed control: both fields number cells. -/
def in15ok : Heap × List Val :=
  let (b, n0) := ({} : HB).alloc (.num 2)
  let (b, n) := b.alloc (.num 3)
  let (b, k) := b.alloc (.ctor npR #[n0, n])
  (b.heap, [k])

def finding15 : IO Unit := do
  report "F15 ill-typed input (field 0 a list cell)" p15 noExtern stdFuels g15 in15 [g15, mkK]
  report "F15 control: well-typed input" p15 noExtern stdFuels g15 in15ok [g15, mkK]

/-! ## Finding 7, variant: the erased parameter of class `val` (an erased `Nat` parameter has
no input meeting `InputsOk`: `ArgOk` asks it for `irr` and for a number cell) -/

def fV := mem 335
def gV := mem 336

def sixV : List Param :=
  [par .many .leaf, par .many .leaf, par .erased .val (.dataApp .data .data) true, par .many .leaf, par .many .leaf,
   par .many .leaf]

def p7v : Prog := prog [
  (fV, body sixV (v 5 .leaf) .shared .leaf),
  (gV, body sixV (app (.const fV .val) [v 5 .leaf, v 4 .leaf, v 3, v 2 .leaf, v 1 .leaf, v 0 .leaf] .leaf) .shared .leaf)]

def finding7v : IO Unit := do
  report "F7v x : List Nat erased, at position 2" p7v noExtern fuels7 gV in7 [gV, fV]

/-! ## Candidate 16: a case's extra arguments judged at the case's class -/

def E2 := mem 9
def e0R := ctr 9 0
def e1R := ctr 9 1
def caseE : CaseInfo := { ind := E2, arity := 3, major := 0, alts := #[{ alt := 1, args := #[] }, { alt := 2, args := #[] }] }
def kk16 := mem 337
def use16 := mem 338
def use16c := mem 339
def use16v := mem 340

def sk16 : Skel := .arrow .many .data .shared (.arrow .many .data .shared .data)

/-- `use16 (k : List Nat → Nat → Nat) (@unique y : List Nat) (b : E) : Nat :=
  (match b with | e0 => k | e1 => k) y (consume y)`. -/
def p16 : Prog := prog [
  (E2, .ind #[e0R, e1R]), (e0R, .ctor E2 0 0 #[]), (e1R, .ctor E2 1 0 #[]),
  (kk16, body [par, par .many .leaf] (lenOf (v 1)) .shared .leaf),
  (use16, body [par .many .val sk16 true, par .unique, par .many .imm .data true]
    (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, app (.const consumeR .val) [v 1] .leaf] .leaf) .shared .leaf),
  -- control: the same application without the case
  (use16c, body [par .many .val sk16 true, par .unique, par .many .imm .data true]
    (app (v 2) [v 1, app (.const consumeR .val) [v 1] .leaf] .leaf) .shared .leaf),
  -- control: the case at class `val` (the result of a polymorphic `id`)
  (use16v, body [par .many .val sk16 true, par .unique, par .many .imm .data true]
    (.case caseE (v 0 .imm) #[v 2, v 2] #[v 1, app (.const consumeR .val) [v 1] .leaf] .val) .shared .val)]

def in16 : Heap × List Val :=
  let (b, xs) := ({} : HB).list [1, 2]
  let (b, k) := b.alloc (.pap kk16 #[])
  (b.heap, [k, xs, .imm (.con e0R)])

def finding16 : IO Unit := do
  report "F16 use16 (case of class leaf, two extra arguments)" p16 noExtern stdFuels use16 in16 [use16, kk16]
  report "F16 control: no case" p16 noExtern stdFuels use16c in16 [use16c, kk16]
  report "F16 control: the case at class val" p16 noExtern stdFuels use16v in16 [use16v, kk16]

/-! ## Candidate 17 (found by the tester): a unique mode on a leaf keeps its confinement in `runR`
(`transfer` of a leaf is a no-op, Eval.lean:310) but loses its regions in the checker -/

def u17a := mem 341
def u17ac := mem 342
def idU := mem 343
def u17b := mem 344
def idS := mem 345
def u17bc := mem 346

/-- (a) `u17a (@borrowed n : Nat) : Nat := let (@unique m) := n; m`; control: a plain `let`.
(b) `idU (w : WrapN) : @unique WrapN := w`, `u17b (@borrowed w : WrapN) : WrapN := idU w`, with
`WrapN` a one-constructor wrapper of `Nat` (class leaf, `noLeaf := false`); control: `idS` returning
`shared`. -/
def p17 : Prog := prog [
  (u17a, body [par .borrowed .leaf] (.letE (.value .unique) .leaf (v 0 .leaf) (v 0 .leaf)) .shared .leaf),
  (u17ac, body [par .borrowed .leaf] (.letE (.value .many) .leaf (v 0 .leaf) (v 0 .leaf)) .shared .leaf),
  (idU, body [par .many .leaf .data false] (v 0 .leaf) .unique .leaf),
  (u17b, body [par .borrowed .leaf .data false] (app (.const idU .val) [v 0 .leaf] .leaf) .shared .leaf),
  (idS, body [par .many .leaf .data false] (v 0 .leaf) .shared .leaf),
  (u17bc, body [par .borrowed .leaf .data false] (app (.const idS .val) [v 0 .leaf] .leaf) .shared .leaf)]

def finding17 : IO Unit := do
  report "C17a let (@unique m) := n" p17 noExtern stdFuels u17a oneNat [u17a]
  report "C17a control: a plain let" p17 noExtern stdFuels u17ac oneNat [u17ac]
  report "C17b a unique result of class leaf" p17 noExtern stdFuels u17b oneNat [u17b, idU]
  report "C17b control: a shared result" p17 noExtern stdFuels u17bc oneNat [u17bc, idS]

/-! ## Candidate 18 (found by the tester): a `@shared` field built by a callee from a plain
parameter holds the caller's confined value (`anProj`, Check.lean:376, as in finding 5, but with a
run body in place of the extern) -/

def mkSB := mem 347
def leak18 := mem 348
def mkSBb := mem 349
def leak18c := mem 350

def p18 : Prog := prog [
  (mkSB, body [par] (app (.const sboxR .val) [v 0])),
  (leak18, body [par .borrowed] (.proj S 0 (app (.const mkSB .val) [v 0]) .val)),
  -- control: the callee's parameter borrowed, so `anCtor` sees the confinement
  (mkSBb, body [par .borrowed] (app (.const sboxR .val) [v 0])),
  (leak18c, body [par .borrowed] (.proj S 0 (app (.const mkSBb .val) [v 0]) .val))]

def finding18 : IO Unit := do
  report "C18 (mkSB xs).val, mkSB (x : List Nat) : SBox := SBox.mk x" p18 noExtern stdFuels leak18 oneList [leak18, mkSB]
  report "C18 control: mkSB's parameter borrowed" p18 noExtern stdFuels leak18c oneList [leak18c, mkSBb]

/-! ## Candidate 19 (MU; found by the tester, `MU-dt-r2` seed 3 case 97815, labelled F9 family on
every tree): a borrowed leaf passed at a plain parameter keeps its confinement in `runR` (`bindAt`
taints nothing away at a plain binder), so a cell the callee builds from it is confined, and the
callee's unique return transfers a confined value: `borrowEscape` (Eval.lean `ret` `.unique` →
`transfer` → `confinedOpen`). The checker gives a leaf at a plain parameter no region (`flowTo`
checks regions at class val only) and the callee, checked alone, builds a fresh cell. Not finding 17:
no unique mode is on a leaf. -/

def mkL19 := mem 351
def c19 := mem 352
def mkL19s := mem 353
def c19s := mem 354
def c19p := mem 355
def c19f := mem 356

def consOf (h : Term) : Term := app (.const consR .val) [.irr, h, app (.const nilR .val) [.irr] .imm]

def p19 : Prog := prog [
  -- mkL (n : Nat) : @unique List Nat := [n]
  (mkL19, body [par .many .leaf] (consOf (v 0 .leaf)) .unique .val),
  -- c19 (@borrowed n : Nat) : List Nat := mkL n
  (c19, body [par .borrowed .leaf] (app (.const mkL19 .val) [v 0 .leaf] .val) .shared .val),
  -- control: mkL's result shared
  (mkL19s, body [par .many .leaf] (consOf (v 0 .leaf)) .shared .val),
  (c19s, body [par .borrowed .leaf] (app (.const mkL19s .val) [v 0 .leaf] .val) .shared .val),
  -- control: n plain
  (c19p, body [par .many .leaf] (app (.const mkL19 .val) [v 0 .leaf] .val) .shared .val),
  -- the tester's shape: (f : Nat → @unique List Nat) (@uniqueBorrowed n : Nat) : @borrowed List Nat := f n
  (c19f, body [par .many .val (.arrow .many .data .unique .data), par .uniqueBorrowed .leaf]
    (app (v 1) [v 0 .leaf] .val) .borrowed .val)]

def in19f : Heap × List Val :=
  let (b, f) := ({} : HB).alloc (.pap mkL19 #[])
  let (b, n) := b.alloc (.num 7)
  (b.heap, [f, n])

def finding19 : IO Unit := do
  report "C19 c19 (@borrowed n : Nat) : List Nat := mkL n, mkL (n : Nat) : @unique List Nat := [n]" p19 noExtern stdFuels c19 oneNat [c19, mkL19]
  report "C19 control: mkL's result shared" p19 noExtern stdFuels c19s oneNat [c19s, mkL19s]
  report "C19 control: n plain" p19 noExtern stdFuels c19p oneNat [c19p, mkL19]
  report "C19 the tester's shape (f n, f an input partial application of mkL)" p19 noExtern stdFuels c19f in19f [c19f, mkL19]

/-! ## A completeness note (MU; `MU-dt-r2` seed 1 case 5130): a once binding of a two-argument
function, called with both arguments (`f 1 2`), refused after repair D ("a once binding called a
second time: an application"); the run is a value. -/

def k2 := mem 357
def cc := mem 358

def pcc : Prog := prog [
  -- k2 (a b : Nat) : Nat := a
  (k2, body [par .many .leaf, par .many .leaf] (v 1 .leaf) .shared .leaf),
  -- cc (@once f : Nat → Nat → Nat) : Nat := f 1 2
  (cc, body [par .once .val (.arrow .many .data .shared (.arrow .many .data .shared .data))]
    (app (v 0) [.natLit 1, .natLit 2] .leaf) .shared .leaf)]

def incc : Heap × List Val := let (b, f) := ({} : HB).alloc (.pap k2 #[]); (b.heap, [f])

def completenessD : IO Unit := do
  report "D-cost cc (@once f : Nat → Nat → Nat) : Nat := f 1 2" pcc noExtern stdFuels cc incc [cc, k2]

def run (args : List String) : IO Unit := do
  let which := args.headD "all"
  if which == "all" || which == "b4" then
    finding19
    completenessD
  if which == "all" || which == "b1" then
    finding1a
    finding2
    finding7
    try finding1b catch e => IO.println s!"[F1b] error: {e}"
  if which == "all" || which == "b2" then
    finding3
    finding4
    finding5
    try finding6 catch e => IO.println s!"[F6] error: {e}"
    finding8
    finding9
    finding10
    finding11
    finding12
    finding13
    finding14
    finding15
  if which == "all" || which == "b3" then
    finding7v
    finding16
    finding17
    finding18

end MT.Findings

def main (args : List String) : IO Unit := MT.Findings.run args
