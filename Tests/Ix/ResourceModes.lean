module

public import IxC.Resource
public import LSpec
public import Ix.CompileCertified
public import Ix.Typing
public import Ix.EnvScope
public import Ix.Meta

/-! # The resource-mode model and checker on small run programs (`resource-modes`)

Each case is a run program built by hand, with an entry and inputs meeting its
declared modes: the reference evaluator `runR` must end as stated (a value, or
the named violation), and the uncertified checker (`IxC.Resource.checkBodies`)
must accept or refuse as stated. Every case the checker accepts runs without a
violation (`consistent`), which is what its soundness would give on these
inputs. The cases follow the mode rules: erased binders and fields; unique
transfer, consuming match, deep uniqueness, `@shared` fields, leaves; borrows of
parameters, of `let`s and of leaves, leaves read out of a borrowed container;
once binders; capture and partial-application transfers; mode skeletons;
statics; limits; the fast path.

The must-reject cases are records whose interface erases a position that a run
behaviour supplied other than by a checked body reads: a case definition's
alternative, a primitive's argument, a recursor's minor premise, a quotient's
element, a parameter past a run body's λs, and an erased field passed to an
alternative that is not a λ for it. The record cases compile a small fixture
(`Tests/Ix/ResourceModesFixture.lean`), write the mode into one record as a
producer of records could, and read, run and check the result.

The recursive-type cases compile a second fixture
(`Tests/Ix/ResourceModesRecFixture.lean`: a list-like type, Lean's `List`, a
mutual pair, a nested and an indexed type, each matched by an honest program)
and read, run and check it unchanged: the class oracle must answer on values of
such types (the mode-repair branch, V7). -/

namespace Tests.ResourceModes

open IxC.Resource Ixon

/-! ## A small library -/

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

/-! ## Cases -/

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

/-- Run `entry` on `input` and check `toCheck`: the run ends as `run` says (a
value, or the violation), and the checker accepts exactly when `accept`. -/
def runCase (label : String) (defs : List (Ref × RunDef)) (entry : Ref) (input : Heap × List Val)
    (run : Option Violation) (accept : Bool) (toCheck : List Ref := [entry]) (lim : Limits := {}) :
    LSpec.TestSeq :=
  .individualIO label none (do
    let P := prog defs
    let o := runR P noExtern 100000 entry input.1 input.2
    let runOk := match o, run with
      | .value .., none => true
      | .violation k, some k' => k == k'
      | _, _ => false
    let verdict := checkBodies lim P toCheck
    let checkOk := verdict.isAccept == accept
    -- what soundness gives on these inputs: accepted runs do not violate
    let consistent := !verdict.isAccept || match o with
      | .violation _ => false
      | _ => true
    let msg := s!"run: {outcomeName o}; checker: {verdictName verdict}"
    return (runOk && checkOk && consistent, 0, 0, if runOk && checkOk && consistent then none else some msg)) .done

/-- Run `entry` on `input` (an ill-typed input): the run is stuck, which is not
a violation, and the checker accepts exactly when `accept`. -/
def stuckCase (label : String) (defs : List (Ref × RunDef)) (entry : Ref) (input : Heap × List Val)
    (accept : Bool) (toCheck : List Ref := [entry]) : LSpec.TestSeq :=
  .individualIO label none (do
    let P := prog defs
    let o := runR P noExtern 100000 entry input.1 input.2
    let runOk := match o with | .stuck => true | _ => false
    let verdict := checkBodies {} P toCheck
    let checkOk := verdict.isAccept == accept
    let msg := s!"run: {outcomeName o}; checker: {verdictName verdict}"
    return (runOk && checkOk, 0, 0, if runOk && checkOk then none else some msg)) .done

/-! ### Erased binders and fields -/

-- `useErased (@erased n : Nat) : Nat := n + 1`
def useErased := mem 100
-- `keep (@erased n : Nat) (b : List) : List := b`
def keepE := mem 101
-- `leak (k : Key) : Nat := k.ghost`; `idOf (k : Key) : Nat := k.id`
def leak := mem 102
def idOf := mem 103
-- `let (@erased x) := xs; len x`
def eraseLet := mem 104

def erasedCases : List LSpec.TestSeq := [
  runCase "erased: reading an erased parameter" [(useErased, body [par .erased .leaf]
    (add (v 0 .leaf) (.natLit 1)) .shared .leaf)] useErased irrArg (some .erasedRead) false,
  runCase "erased: an erased parameter never read" [(keepE, body [par .erased .leaf, par]
    (v 0))] keepE irrAndList none true,
  runCase "erased: projecting an erased field" [(leak, body [par] (.proj K 0 (v 0) .leaf) .shared .leaf)]
    leak oneKey (some .erasedRead) false,
  runCase "erased: projecting a kept field" [(idOf, body [par] (.proj K 1 (v 0) .leaf) .shared .leaf)]
    idOf oneKey none true,
  runCase "erased: reading an erased let" [(eraseLet, body [par]
    (.letE (.value .erased) .val (v 0) (lenOf (v 0))) .shared .leaf)] eraseLet oneList
    (some .erasedRead) false
]

/-! ### Unique transfer -/

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

def uniqueCases : List LSpec.TestSeq := [
  -- `twice (@unique xs) := consume xs + consume xs`
  runCase "unique: a binding transferred twice" [(twice, body [par .unique]
    (add (app (.const consumeR .val) [v 0] .leaf) (app (.const consumeR .val) [v 0] .leaf)) .shared .leaf)]
    twice oneList (some .revokedUse) false,
  runCase "unique: a binding transferred once" [(once1, body [par .unique]
    (app (.const consumeR .val) [v 0] .leaf) .shared .leaf)] once1 oneList none true,
  -- `share1 (xs : List) := consume xs`; `caller (xs) := share1 xs + len xs`
  runCase "unique: a shared parameter given away, then read by its caller"
    [(share1, body [par] (app (.const consumeR .val) [v 0] .leaf) .shared .leaf),
     (caller, body [par] (add (app (.const share1 .val) [v 0] .leaf) (lenOf (v 0))) .shared .leaf)]
    caller oneList (some .revokedUse) false [share1, caller],
  -- `headU (@unique xs) := match xs with | [] => 0 | _ :: t => len t`
  runCase "unique: a consuming match, the fields used" [(headU, body [par .unique]
    (onList (v 0) (.natLit 0) (lenOf (v 0)) .val .leaf) .shared .leaf)] headU oneList none true,
  -- `headBad (@unique xs) := match xs with | [] => 0 | _ :: _ => len xs`
  runCase "unique: a consumed major read in an alternative" [(headBad, body [par .unique]
    (onList (v 0) (.natLit 0) (lenOf (v 2)) .val .leaf) .shared .leaf)] headBad oneList
    (some .revokedUse) false,
  -- `deep (@unique xs) := match xs with | [] => 0 | h :: t => consume (h :: t) + len t`
  runCase "unique: deep transfer revokes the fields" [(deep, body [par .unique]
    (onList (v 0) (.natLit 0)
      (add (app (.const consumeR .val) [app (.const consR .val) [.irr, v 1, v 0]] .leaf) (lenOf (v 0))) .val .leaf)
    .shared .leaf)] deep oneList (some .revokedUse) false,
  -- `boxS (x : List) := let s := ⟨x⟩ : S; consumeS s + len x` (a `@shared` field)
  runCase "unique: a @shared field stops deep uniqueness" [(boxS, body [par]
    (.letE (.value .many) .val (app (.const sboxR .val) [v 0])
      (add (app (.const consumeSR .val) [v 0] .leaf) (lenOf (v 1)))) .shared .leaf)] boxS oneList none true,
  -- `boxI (x : List) := let s := ⟨x⟩ : B; consumeB s + len x` (an inherited field)
  runCase "unique: an inherited field is transferred with its box" [(boxI, body [par]
    (.letE (.value .many) .val (app (.const boxR .val) [v 0])
      (add (app (.const consumeBR .val) [v 0] .leaf) (lenOf (v 1)))) .shared .leaf)] boxI oneList
    (some .revokedUse) false,
  -- `twiceN (@unique n : Nat) := consumeN n + consumeN n` (a leaf is never unique)
  runCase "unique: a leaf transferred twice" [(twiceN, body [par .unique .leaf]
    (add (app (.const consumeNR .val) [v 0 .leaf] .leaf) (app (.const consumeNR .val) [v 0 .leaf] .leaf))
    .shared .leaf)] twiceN oneNat none true
]

/-! ### Borrows -/

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

def borrowCases : List LSpec.TestSeq := [
  runCase "borrow: a borrowed parameter returned" [(esc, body [par .borrowed] (v 0))] esc oneList
    (some .borrowEscape) false,
  -- refused after repair A (the leaf-result refinement dropped, findings 1 to 3); accepted again
  -- under the leaf ruling L1 (a number is never confined): `len`'s leaf result carries no region.
  runCase "borrow: a borrowed parameter read" [(peek, body [par .borrowed] (lenOf (v 0)) .shared .leaf)]
    peek oneList none true,
  runCase "borrow: a borrowed parameter returned borrowed" [(same, body [par .borrowed] (v 0) .borrowed)]
    same oneList none true,
  -- `stash (@borrowed b : List) : List := [b]`
  runCase "borrow: a borrowed parameter stored in a cell" [(stash, body [par .borrowed]
    (app (.const consR .val) [.irr, v 0, app (.const nilR .val) [.irr] .imm]))] stash oneList
    (some .borrowEscape) false,
  runCase "borrow: a borrowed parameter given away" [(give, body [par .borrowed]
    (app (.const consumeR .val) [v 0] .leaf) .shared .leaf)] give oneList (some .borrowEscape) false,
  runCase "borrow: a let's loan returned" [(letEsc, body [par] (.letE .borrow .val (v 0) (v 0)))]
    letEsc oneList (some .borrowEscape) false,
  -- refused after repair A, accepted again under L1: `len x` carries no region of the let's.
  runCase "borrow: a let's loan read" [(letOk, body [par] (.letE .borrow .val (v 0) (lenOf (v 0)))
    .shared .leaf)] letOk oneList none true,
  -- under L1 a borrowed number is not confined: the run returns it and the checker accepts
  -- (before L1, borrowEscape and a refusal)
  runCase "borrow: a borrowed leaf returned" [(escN, body [par .borrowed .leaf] (v 0 .leaf) .shared .leaf)]
    escN oneNat none true,
  runCase "borrow: arithmetic on a borrowed leaf" [(addN, body [par .borrowed .leaf]
    (add (v 0 .leaf) (.natLit 1)) .shared .leaf)] addN oneNat none true,
  -- `headN (@borrowed xs : List Nat) : Nat := match xs with | [] => 0 | h :: _ => h`
  runCase "borrow: a leaf read out of a borrowed container is not confined" [(headN, body [par .borrowed]
    (onList (v 0) (.natLit 0) (v 1 .leaf) .leaf .leaf) .shared .leaf)] headN oneList none true,
  -- `storeN (@borrowed n : Nat) : Nat := match [n] with | [] => 0 | h :: _ => h`
  runCase "borrow: a borrowed leaf stored in a cell and read back is a counted value" [(storeN,
    body [par .borrowed .leaf]
      (onList (app (.const consR .val) [.irr, v 0 .leaf, app (.const nilR .val) [.irr] .imm])
        (.natLit 0) (v 1 .leaf) .leaf .leaf) .shared .leaf)] storeN oneNat none true,
  -- `shf (@borrowed b : List) : List := (⟨b⟩ : S).1` (a borrowed value in a `@shared` field)
  runCase "borrow: a borrowed value stored in a @shared field and returned" [(shf,
    body [par .borrowed] (.proj S 0 (app (.const sboxR .val) [v 0]) .val))] shf oneList
    (some .borrowEscape) false
]

/-! ### Once -/

def twiceCall := mem 130
def onceCall := mem 131

def onceCases : List LSpec.TestSeq := [
  runCase "once: a once parameter called twice" [(twiceCall, body [par .once .val arrowSk]
    (add (app (v 0) [.natLit 1] .leaf) (app (v 0) [.natLit 2] .leaf)) .shared .leaf)] twiceCall oneFun
    (some .onceReentry) false,
  runCase "once: a once parameter called once" [(onceCall, body [par .once .val arrowSk]
    (app (v 0) [.natLit 1] .leaf) .shared .leaf)] onceCall oneFun none true
]

/-! ### Captures and partial applications -/

def capOnce := mem 140
def capOuter := mem 141
def capPlain := mem 142
def papT := mem 143

def captureCases : List LSpec.TestSeq := [
  -- `capOnce (@unique xs) := let g := fun u => consume xs; g 0 + g 1`
  runCase "capture: a closure consuming its capture called twice" [(capOnce, body [par .unique]
    (.letE (.value .many) .val (lam (par .many .leaf) (app (.const consumeR .val) [v 1] .leaf) .shared .leaf)
      (add (app (v 0) [.natLit 0] .leaf) (app (v 0) [.natLit 1] .leaf))) .shared .leaf)] capOnce oneList
    (some .revokedUse) false,
  -- `capOuter (@unique xs) := let g := fun u => len xs; len xs`
  runCase "capture: a unique binding captured, then read outside" [(capOuter, body [par .unique]
    (.letE (.value .many) .val (lam (par .many .leaf) (lenOf (v 1)) .shared .leaf) (lenOf (v 1)))
    .shared .leaf)] capOuter oneList (some .revokedUse) false,
  -- `capPlain (xs : List) := let g := fun u => len xs; g 0 + len xs`
  runCase "capture: a shared binding captured and read" [(capPlain, body [par]
    (.letE (.value .many) .val (lam (par .many .leaf) (lenOf (v 1)) .shared .leaf)
      (add (app (v 0) [.natLit 0] .leaf) (lenOf (v 1)))) .shared .leaf)] capPlain oneList none true,
  -- `papT (@unique xs) := let g := consume2 xs; len xs`
  runCase "capture: a partial application transfers its unique argument" [(papT, body [par .unique]
    (.letE (.value .many) .val (app (.const consume2R .val) [v 0]) (lenOf (v 1))) .shared .leaf)] papT oneList
    (some .revokedUse) false
]

/-! ### Skeletons and statics -/

def callUse := mem 150
def callUseOk := mem 151
def badStatic := mem 152
def okStatic := mem 153

def skeletonCases : List LSpec.TestSeq := [
  -- `callUse (xs) := use (fun (@unique y) => consume y) xs`
  runCase "skeleton: a closure with a unique binder at a plain arrow" [(callUse, body [par]
    (app (.const useR .val) [lam (par .unique) (app (.const consumeR .val) [v 0] .leaf) .shared .leaf, v 0] .leaf)
    .shared .leaf)] callUse oneList (some .revokedUse) false,
  runCase "skeleton: a closure with a plain binder at a plain arrow" [(callUseOk, body [par]
    (app (.const useR .val) [lam (par .many) (lenOf (v 0)) .shared .leaf, v 0] .leaf) .shared .leaf)]
    callUseOk oneList none true,
  -- `badStatic := consume tbl + len tbl`
  runCase "static: a static given away, then read" [(badStatic, body []
    (add (app (.const consumeR .val) [.const tblR .val] .leaf) (lenOf (.const tblR .val))) .shared .leaf)] badStatic
    noArgs (some .revokedUse) false,
  runCase "static: a static read twice" [(okStatic, body []
    (add (lenOf (.const tblR .val)) (lenOf (.const tblR .val))) .shared .leaf)] okStatic noArgs none true
]

/-! ### Limits and the fast path -/

/-- A step limit declines. -/
def limitCase : LSpec.TestSeq :=
  .individualIO "limits: the step limit declines" none (do
    let verdict := checkBodies { steps := 3 } (prog []) [lenR]
    let ok := match verdict with
      | .decline _ => true
      | _ => false
    return (ok, 0, 0, if ok then none else some (verdictName verdict))) .done

/-- A closure of default records is accepted without reading; an annotated axiom
is read and refused outside the extern set, accepted inside it. -/
def fastPathCase : LSpec.TestSeq :=
  .individualIO "fast path and externs: default records unread; an annotated axiom only as an extern" none (do
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
    return (ok, 0, 0, if ok then none else
      some s!"{verdictName v1}; {verdictName v2}; {verdictName v3}")) .done

/-! ### Must-reject cases: an erased field at an alternative -/

/-- A case on `Key`: `key g n => alt g n`. -/
def caseK : CaseInfo :=
  { ind := K, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0, .field 1] }] }

def firstOf := mem 160
def altConst := mem 161
def secondOf := mem 162
def altLam := mem 163

def alternativeCases : List LSpec.TestSeq := [
  -- `firstOf (a : List) (b : Nat) : List := a`; `altConst (k : Key) := Key.casesOn k firstOf`
  runCase "must-reject: an erased field passed to an alternative that is not a λ" [
    (firstOf, body [par, par .many .leaf] (v 1)),
    (altConst, body [par] (.case caseK (v 0) #[.const firstOf .val] #[] .val))]
    altConst oneKey (some .erasedRead) false,
  -- `secondOf (b : Nat) : Nat := b`; `altLam (k : Key) := Key.casesOn k (fun (@erased g) => secondOf)`
  runCase "erased: a λ alternative binds the erased field, the rest passed on" [
    (secondOf, body [par .many .leaf] (v 0 .leaf) .shared .leaf),
    (altLam, body [par] (.case caseK (v 0) #[lam (par .erased) (.const secondOf .val) .shared .leaf] #[]
      .leaf) .shared .leaf)]
    altLam oneKey none true
]

/-! ### Findings of the mode study (REPLY-2-TO-IXVM.md §4), with their controls

Each program the checker accepted while its run violated, now refused, beside
the nearest program it refuses or accepts as it should. The same cases, with
the run at every fuel tried, are in `ModeRepairTests/Main.lean`, which runs on
the kernel package alone. Under the owner's provisional leaf ruling (L1: a
number is never confined), the programs of findings 1, 2, 3, 12 and 17 run a
value and are accepted (marked `L1`). -/

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
-- Repair R: `retAlt (@once f : Nat → Nat) (b : E) : Nat := callTwice (match b with | e0 => f | e1 => f)`;
-- the control `retAltP` has `f` plain
def retAlt := mem 377
def retAltP := mem 387
def funAndE0 : Heap × List Val :=
  let (b, f) := ({} : HB).alloc (.pap incR #[])
  (b.heap, [f, .imm (.con e0R)])
def retAltBody : Term := app (.const callTwice .val) [.case caseE (v 0 .imm) #[v 1, v 1] #[] .val] .leaf
-- Repair S: `retF (@once f : Nat → Nat) : Nat → Nat := f`; `useRet (@once f) : Nat := let h := retF f; h 0 + h 1`;
-- the control `useRetP` calls `retP`, the same with `f` plain
def retF := mem 367
def retP := mem 368
def useRet := mem 378
def useRetP := mem 388
def useRetBody (r : Ref) : Term := .letE (.value .many) .val (app (.const r .val) [v 0] .val)
  (add (app (v 0) [.natLit 0] .leaf) (app (v 0) [.natLit 1] .leaf))
-- Repair T: `twiceOnce (@once f : Nat → Nat) : Nat := callOnce f + callOnce f`; the control
-- `twiceOnceP` has `f` plain
def twiceOnce := mem 379
def twiceOnceP := mem 389
def twiceOnceBody : Term := add (app (.const callOnce .val) [v 0] .leaf) (app (.const callOnce .val) [v 0] .leaf)
-- Finding 17 (repair O): a unique mode on a leaf. `u17a (@borrowed n : Nat) : Nat := let (@unique m) := n; m`
-- (control `u17ap`, `n` plain); `idU (w : WrapN) : @unique WrapN := w`, `u17b (@borrowed w : WrapN) : WrapN := idU w`;
-- `idUP {α} (@unique x : α) : @unique α := x`, `u17c (@borrowed n : Nat) : Nat := idUP n` (control `u17cp`, `n` plain);
-- `u17d (@borrowed w : WrapN) : Nat := match w with | ⟨@unique m⟩ => m` (control `u17dp`, `w` plain)
def WNi := mem 420
def wnR := ctr 420 0
def caseWN : CaseInfo := { ind := WNi, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0] }] }
def u17a := mem 410
def u17ap := mem 411
def idU := mem 412
def u17b := mem 413
def idUP := mem 414
def u17c := mem 415
def u17cp := mem 416
def u17d := mem 417
def u17dp := mem 418
def matchWNU : Term := .case caseWN (v 0 .leaf) #[lam (par .unique .leaf) (v 0 .leaf) .shared .leaf] #[] .leaf
def oDefs : List (Ref × RunDef) := [
  (WNi, .ind #[wnR]), (wnR, .ctor WNi 0 0 #[fld .leaf]),
  (u17a, body [par .borrowed .leaf] (.letE (.value .unique) .leaf (v 0 .leaf) (v 0 .leaf)) .shared .leaf),
  (u17ap, body [par .many .leaf] (.letE (.value .unique) .leaf (v 0 .leaf) (v 0 .leaf)) .shared .leaf),
  (idU, body [par .many .leaf] (v 0 .leaf) .unique .leaf),
  (u17b, body [par .borrowed .leaf] (app (.const idU .val) [v 0 .leaf] .leaf) .shared .leaf),
  (idUP, body [par .many .irr, par .unique .val .unknown] (v 0) .unique .val .unknown),
  (u17c, body [par .borrowed .leaf] (app (.const idUP .val) [.irr, v 0 .leaf] .leaf) .shared .leaf),
  (u17cp, body [par .many .leaf] (app (.const idUP .val) [.irr, v 0 .leaf] .leaf) .shared .leaf),
  (u17d, body [par .borrowed .leaf] matchWNU .shared .leaf),
  (u17dp, body [par .many .leaf] matchWNU .shared .leaf)]
-- Finding 18 (repair P): `mkSB (x : List Nat) : SBox := SBox.mk x`; `leak18 (@borrowed xs : List Nat) :
-- List Nat := (mkSB xs).val`, `leak18m … := match mkSB xs with | ⟨y⟩ => y`; the controls have `xs` plain
def mkSB := mem 430
def leak18 := mem 445
def leak18p := mem 465
def leak18m := mem 447
def leak18mp := mem 467
def caseS : CaseInfo := { ind := S, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0] }] }
def mkSBDef : Ref × RunDef := (mkSB, body [par] (app (.const sboxR .val) [v 0]))
def projSB : Term := .proj S 0 (app (.const mkSB .val) [v 0]) .val
def matchSB : Term := .case caseS (app (.const mkSB .val) [v 0]) #[lam par (v 0) .shared .val] #[] .val
-- Repair U: `mkSBU (x : List Nat) : @unique SBox := SBox.mk x`; `isSB (b : SBox) : E := e0`;
-- `leakU (@borrowed xs : List Nat) : E := isSB (mkSBU xs)` (its run ends in borrowEscape at mkSBU's
-- unique return); the control has `xs` plain
def mkSBU := mem 431
def isSB := mem 441
def leakU := mem 456
def leakUp := mem 476
def uDefs : List (Ref × RunDef) := [(E2, .ind #[e0R, e1R]), (e0R, .ctor E2 0 0 #[]), (e1R, .ctor E2 1 0 #[]),
  (mkSBU, body [par] (app (.const sboxR .val) [v 0]) .unique),
  (isSB, body [par] (.const e0R .imm) .shared .imm)]
def isSBmk : Term := app (.const isSB .val) [app (.const mkSBU .val) [v 0]] .imm
-- Finding 15 (repair J): `NP` with one constructor and two `Nat` fields; `mkK {α β} (a : α) (b : β) : Nat → α :=
-- fun _ => a`; `g15 (@borrowed k : NP) : Nat → Nat := NP.casesOn k (@mkK Nat Nat)`, on an input whose first
-- field holds a list cell (ill-typed): a stuck run since repair J; on a well-typed input, a value
def NP := mem 8
def npR := ctr 8 0
def caseNP : CaseInfo := { ind := NP, arity := 2, major := 0, alts := #[{ alt := 1, args := #[.field 0, .field 1] }] }
def mkK := mem 332
def g15 := mem 333
def p15Defs : List (Ref × RunDef) := [
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
def useBoxDef : Ref × RunDef :=
  (useBox, body [par] (add (app (.proj B 0 (v 0) .val) [.natLit 0] .leaf) (app (.proj B 0 (v 0) .val) [.natLit 1] .leaf))
    .shared .leaf)

/-- Run `entry` at every fuel of `fuels` (ascending): no run violates, the runs
are out of fuel up to some fuel and a value from there on (the evaluator spends
fuel per step and does not change what it runs with it), and the checker
accepts exactly when `accept`. -/
def fuelCase (label : String) (defs : List (Ref × RunDef)) (entry : Ref) (input : Heap × List Val)
    (fuels : List Nat) (accept : Bool) (toCheck : List Ref := [entry]) : LSpec.TestSeq :=
  .individualIO label none (do
    let P := prog defs
    let os := fuels.map fun f => runR P noExtern f entry input.1 input.2
    let rest := os.dropWhile fun o => match o with | .outOfFuel => true | _ => false
    let runOk := !rest.isEmpty && rest.all fun o => match o with | .value .. => true | _ => false
    let verdict := checkBodies {} P toCheck
    let checkOk := verdict.isAccept == accept
    let msg := s!"runs: {", ".intercalate (os.map outcomeName)}; checker: {verdictName verdict}"
    return (runOk && checkOk, 0, 0, if runOk && checkOk then none else some msg)) .done

def findingCases : List LSpec.TestSeq := [
  runCase "finding 1: a borrowed number through a call of `Nat → Nat` (its parameter read as no-leaf)"
    [idNDef true, (g4, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .shared .leaf)]
    g4 oneNat none true,  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 1, control: the parameter not read as no-leaf"
    [idNDef false, (g4, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .shared .leaf)]
    g4 oneNat none true,  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 1, control: the result returned borrowed"
    [idNDef true, (g4b, body [par .borrowed .leaf] (app (.const idN .val) [v 0 .leaf] .leaf) .borrowed .leaf)]
    g4b oneNat none true,
  runCase "finding 2: a borrowed number captured by a closure passed at a function type"
    [app1Def true, (g3, body [par .borrowed .leaf]
      (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf) .shared .leaf)]
    g3 oneNat none true [g3, app1],  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 2, control: the parameter not read as no-leaf"
    [app1Def false, (g3, body [par .borrowed .leaf]
      (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf) .shared .leaf)]
    g3 oneNat none true [g3, app1],  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 2, control: the captured number not borrowed"
    [app1Def true, (g3p, body [par .many .leaf]
      (app (.const app1 .val) [lam (par .many .leaf) (v 1 .leaf) .shared .leaf] .leaf) .shared .leaf)]
    g3p oneNat none true [g3p, app1],
  runCase "finding 3: a borrowed number cast to a list under an absurd hypothesis"
    (eqDefs ++ [(g2, body [par .many .irr, par .many .irr, par .borrowed .leaf]
      (app (.const bad3 .val) [.irr, .case caseEq .irr #[v 0 .leaf] #[] .val] .leaf) .shared .leaf)])
    g2 in3 none true [g2, bad3],  -- L1 W1: borrowEscape before  -- L1: accepted
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
    addB oneNat none true,  -- L1 W1: borrowEscape before  -- L1: accepted
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
      .shared .leaf)] ok11b oneFun none true [ok11b, useBox],
  runCase "a once parameter returned by a case alternative, the case's value lent to a body that calls it twice"
    (onceDefs ++ p16Defs ++ [(retAlt, body [par .once .val arrowSk, par .many .imm] retAltBody .shared .leaf)])
    retAlt funAndE0 (some .onceReentry) false,
  runCase "the same, the parameter plain"
    (onceDefs ++ p16Defs ++ [(retAltP, body [par .many .val arrowSk, par .many .imm] retAltBody .shared .leaf)])
    retAltP funAndE0 none true,
  runCase "a once parameter returned, the result called twice by the caller"
    [(retF, body [par .once .val arrowSk] (v 0) .shared .val arrowSk),
     (useRet, body [par .once .val arrowSk] (useRetBody retF) .shared .leaf)]
    useRet oneFun (some .onceReentry) false [useRet, retF],
  runCase "the same, the parameter plain"
    [(retP, body [par .many .val arrowSk] (v 0) .shared .val arrowSk),
     (useRetP, body [par .many .val arrowSk] (useRetBody retP) .shared .leaf)]
    useRetP oneFun none true [useRetP, retP],
  runCase "a once parameter passed to two once parameters"
    (onceDefs ++ [(twiceOnce, body [par .once .val arrowSk] twiceOnceBody .shared .leaf)])
    twiceOnce oneFun (some .onceReentry) false [twiceOnce, callOnce],
  runCase "the same, the parameter plain"
    (onceDefs ++ [(twiceOnceP, body [par .many .val arrowSk] twiceOnceBody .shared .leaf)])
    twiceOnceP oneFun none true [twiceOnceP, callOnce],
  runCase "finding 17: a borrowed number bound at a unique let, returned" oDefs u17a oneNat none true,  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 17, control: the number not borrowed" oDefs u17ap oneNat none true,
  runCase "finding 17: a borrowed number through a unique result of class leaf" oDefs u17b oneNat
    none true [u17b, idU],  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 17: a borrowed number through a polymorphic unique result" oDefs u17c oneNat
    none true [u17c, idUP],  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 17, control: the number not borrowed" oDefs u17cp oneNat none true [u17cp, idUP],
  runCase "finding 17: a borrowed wrapper of a number matched, its field bound unique and returned" oDefs u17d oneNat
    none true,  -- L1 W1: borrowEscape before  -- L1: accepted
  runCase "finding 17, control: the wrapper not borrowed" oDefs u17dp oneNat none true,
  runCase "finding 18: a borrowed list stored in a @shared field by a callee, projected"
    [mkSBDef, (leak18, body [par .borrowed] projSB)] leak18 oneList (some .borrowEscape) false [leak18, mkSB],
  runCase "finding 18, control: the list not borrowed"
    [mkSBDef, (leak18p, body [par] projSB)] leak18p oneList none true [leak18p, mkSB],
  runCase "finding 18: the same field matched"
    [mkSBDef, (leak18m, body [par .borrowed] matchSB)] leak18m oneList (some .borrowEscape) false [leak18m, mkSB],
  runCase "finding 18, control: the list not borrowed"
    [mkSBDef, (leak18mp, body [par] matchSB)] leak18mp oneList none true [leak18mp, mkSB],
  runCase "a borrowed list retained by a call whose result is unique"
    (uDefs ++ [(leakU, body [par .borrowed] isSBmk .shared .imm)]) leakU oneList (some .borrowEscape) false
    [leakU, mkSBU, isSB],
  runCase "the same, the list not borrowed"
    (uDefs ++ [(leakUp, body [par] isSBmk .shared .imm)]) leakUp oneList none true [leakUp, mkSBU, isSB],
  stuckCase "finding 15: an input cell's Nat field holding a list, read by a case" p15Defs g15 in15 true [g15, mkK],
  runCase "finding 15, control: a well-typed input" p15Defs g15 in15ok none true [g15, mkK]
]

/-! ### Must-reject cases from records -/

/-- The fixture compiled: its records and the prelude's, its literal blobs, the
kernel environment its typing installs, its role table, its names' addresses. -/
structure Built where
  env : Ix.Kernel.Env .anon
  table : Ix.Kernel.RoleTable
  store : Ix.Kernel.Reader.Store
  blob : Address → Option ByteArray
  named : Lean.Name → Option Address

def fixtureSeeds : List Lean.Name :=
  [`ModeFixture.main, `ModeFixture.mainRec, `ModeFixture.callF, `ModeFixture.callAdd, `ModeFixture.mkQ]

/-- Compile the fixture at `path` from `seeds`. -/
def buildFixtureAt (path : System.FilePath) (seeds : List Lean.Name) : IO (Except String Built) := do
  let lenv ← getFileEnv path
  let consts := Ix.EnvScope.collectSelectedDeps lenv seeds
  let (prepared, annotated) ← match Ix.Compile.prepareSourceConstants consts >>= fun p =>
      (Ix.CompileM.checkPreparedSource p).map (p, ·) with
    | .ok p => pure p
    | .error e => return .error s!"preparing: {e}"
  let out ← match ← Ix.CompileM.compileCertifiedPrepared prepared annotated 1 (binderData := true) with
    | .ok o => pure o
    | .error e => return .error s!"compiling: {e}"
  unless out.failures.isEmpty do return .error "compiling: some constants failed"
  let input ← match Ix.Typing.typingInput out.env with
    | .ok i => pure i
    | .error e => return .error s!"typing input: {e}"
  let env ← match Ix.Typing.checkCertified input (Ix.Typing.splitOf input) with
    | .ok env => pure env
    | .error (e, _) => return .error s!"typing: {e}"
  let records : Std.HashMap Address Ixon.Constant :=
    input.ordered.foldl (fun m (a, c, _) => m.insert a c) {}
  let prelude : Std.HashMap Address Ixon.Constant :=
    (input.pre.records ++ input.pre.evidence).foldl (fun m (a, c) => m.insert a c) {}
  let blobs : Std.HashMap Address ByteArray :=
    (input.blobs ++ input.pre.blobs).foldl (fun m (a, b) => m.insert a b) {}
  let named := out.env.named
  let store : Ix.Kernel.Reader.Store := fun a => records[a]? <|> prelude[a]?
  let blob : Address → Option ByteArray := fun a => blobs[a]?
  let addrOf : Lean.Name → Option Address := fun n => (named.get? (Ix.Name.fromLeanName n)).map (·.addr)
  let built : Built := { env := env, table := input.table, store := store, blob := blob, named := addrOf }
  return .ok built

def buildFixture : IO (Except String Built) :=
  buildFixtureAt "Tests/Ix/ResourceModesFixture.lean" fixtureSeeds

/-- Erase the `i`-th leading binder of root `root` of `c` (whose expression is `e`; its
λs with `lam`, else its ∀s): its input mode, in the record's binder-data section, becomes
`erased`. -/
def eraseBinder (c : Ixon.Constant) (root : Nat) (e : Ixon.Expr) (lam : Bool) (i : Nat) :
    Option Ixon.Constant := do
  let full := IxC.Resource.binderfulEntries c.sharing
  let pos ← (IxC.Resource.leadingBinders full (!lam) (i + 1) e 0).toOption
  let p ← pos[i]?
  let bi ← c.binders.findIdx? fun b => !b.shared && b.index == root.toUInt64 && b.variant == 0
  let b ← c.binders[bi]?
  let node ← b.nodes[p]?
  let node' : Ixon.BinderNode ← match node with
    | .never m => some (.never { m with input := .erased })
    | .zero m => some (.zero { m with input := .erased })
    | .ifAllZero ps m => some (.ifAllZero ps { m with input := .erased })
    | .undecided m => some (.undecided { m with input := .erased })
    | .share _ => none
  pure { c with binders := c.binders.set! bi { b with nodes := b.nodes.set! p node' } }

/-- Erase parameter `i` of the constant `r` in its record `c`: its type's ∀, and
its value's λ with `inValue`. -/
def eraseParam (c : Ixon.Constant) (r : Ref) (i : Nat) (inValue : Bool) : Option Ixon.Constant :=
  let onDef (base : Nat) (d : Ixon.Definition) : Option Ixon.Constant := do
    let c' ← eraseBinder c base d.typ false i
    if inValue then eraseBinder c' (base + 1) d.value true i else pure c'
  match r, c.info with
  | .member _ 0, .defn d => onDef 0 d
  | .member _ 0, .recr rr => eraseBinder c 0 rr.typ false i
  | .member _ 0, .quot q => eraseBinder c 0 q.typ false i
  | .member _ j, .muts ms => do
    match ← ms[j]? with
    | .defn d => onDef (IxC.Resource.rootBase c j) d
    | .recr rr => eraseBinder c (IxC.Resource.rootBase c j) rr.typ false i
    | .indc _ => none
  | _, _ => none

/-- A record case: an entry, the parameter erased in one constant's record (in
its type, and in its value with the flag), the constant the role `natAdd` is
bound to; what the reading, the run and the checker must do. -/
structure RecCase where
  label : String
  entry : Lean.Name
  erase : Option (Lean.Name × Nat × Bool) := none
  prim : Option Lean.Name := none
  reads : Bool
  accept : Bool
  /-- the constructor the run must return, when it reads -/
  value : Option Lean.Name := none
  /-- the run must be stuck, when it reads -/
  stuck : Bool := false
  /-- constants whose reading the case line reports (a case definition or not), when it reads -/
  report : List Lean.Name := []

def recordCases : List RecCase := [
  { label := "the fixture as compiled", entry := `ModeFixture.main, reads := true, accept := true,
    value := some `ModeFixture.E.c₂ },
  { label := "must-reject: a case definition's alternative erased, the alternative its case rule selects",
    entry := `ModeFixture.main, erase := some (`ModeFixture.cases', 3, true), reads := false, accept := false },
  { label := "case definition: its motive erased, which its case rule does not read",
    entry := `ModeFixture.main, erase := some (`ModeFixture.cases', 0, true), reads := true, accept := true,
    value := some `ModeFixture.E.c₂ },
  { label := "primitive: a role-bound operation with default modes",
    entry := `ModeFixture.callAdd, prim := some `ModeFixture.myAdd, reads := true, accept := true },
  { label := "must-reject: a role-bound operation with an erased parameter",
    entry := `ModeFixture.callAdd, erase := some (`ModeFixture.myAdd, 0, true), prim := some `ModeFixture.myAdd,
    reads := false, accept := false },
  { label := "must-reject: a recursor's minor premise erased",
    entry := `ModeFixture.mainRec, erase := some (`ModeFixture.E.rec, 2, false), reads := false, accept := false },
  { label := "must-reject: a quotient's element erased",
    entry := `ModeFixture.mkQ, erase := some (`Quot.mk, 2, false), reads := false, accept := false },
  { label := "η-short: an erased parameter past a run body's λs",
    entry := `ModeFixture.callF, erase := some (`ModeFixture.f, 0, false), reads := false, accept := false }
]

/-- `RespectsErasure`, decided over a program's constants. -/
def respectsErasure (s : Subject) (P : Prog) : Bool :=
  P.defs.all fun (r, d) =>
    match d.suppliedReads with
    | none => true
    | some reads =>
      match ifaceErased s r with
      | .ok es => es.all fun i => !reads i
      | .error _ => false

/-- Change the fixture's records as the case says, then read (and decide
`RespectsErasure` of what reads), run and check. -/
def runRecCase (b : Built) (c : RecCase) : Except String (Bool × String) := do
  let refOf (n : Lean.Name) : Except String (Address × Ref) := do
    let some a := b.named n | throw s!"{n} has no address"
    let some r := Ix.Kernel.Reader.resolve b.store a | throw s!"{n} does not resolve"
    pure (a, r)
  let (entryA, entryR) ← refOf c.entry
  let mut store := b.store
  let mut table := b.table
  if let some (n, i, inValue) := c.erase then
    let (_, r) ← refOf n
    let some rc := b.store r.block | throw s!"{n}: no record"
    let some rc' := eraseParam rc r i inValue | throw s!"{n}: the record is not of the expected shape"
    let prev := store
    store := fun x => if x == r.block then some rc' else prev x
  if let some n := c.prim then
    let (a, _) ← refOf n
    table := { table with bound := table.bound.map fun (role, x) =>
      if role == .natAdd then (role, a) else (role, x) }
  let s : Subject := { table, store, blob := b.blob, seeds := [entryA] }
  let cl := oracleClassifier b.env (ctorShapes (Reading.make s)) {}
  let expected ← match c.value with
    | some n => do pure (some (← refOf n).2)
    | none => pure none
  let reported : List (Lean.Name × Option Ref) :=
    c.report.map fun n => (n, (b.named n).bind (Ix.Kernel.Reader.resolve b.store ·))
  let (readOk, readStr, runStr, valueOk) := match readProg s cl with
    | .error e => (false, s!"the reading fails ({e})", "not run", true)
    | .ok P =>
      let o := runR P noExtern 100000 entryR ({} : HB).heap []
      let valueOk := match expected, o with
        | none, _ => true
        | some r, .value (.imm (.con r')) _ => r == r'
        | some _, _ => false
      let stuckOk := !c.stuck || match o with | .stuck => true | _ => false
      let erasureOk := respectsErasure s P
      let kinds := reported.map fun ((n, r) : Lean.Name × Option Ref) => match Option.bind r P.find? with
        | some (.caseDef _) => s!"{n} a case definition"
        | some (.body ..) => s!"{n} a body"
        | some _ => s!"{n} other"
        | none => s!"{n} not in the program"
      (true, s!"reads (supplied behaviours respect erasure: {erasureOk}){if kinds.isEmpty then "" else s!"; {", ".intercalate kinds}"}",
        outcomeName o, valueOk && stuckOk && erasureOk)
  let v := check {} b.env s
  let ok := readOk == c.reads && v.isAccept == c.accept && valueOk
  pure (ok, s!"{c.label}: {readStr}; run: {runStr}; checker: {verdictName v}")

def recordCasesTest : LSpec.TestSeq :=
  .individualIO "must-reject cases from records: case definitions, primitives, recursors, quotients, \
    η-short interfaces" none (do
    match ← buildFixture with
    | .error e => return (false, 0, 0, some s!"the fixture: {e}")
    | .ok b =>
      let mut allOk := true
      let mut failed : Array String := #[]
      for c in recordCases do
        let (ok, line) := match runRecCase b c with
          | .ok r => r
          | .error e => (false, s!"{c.label}: {e}")
        IO.println s!"    {if ok then "ok" else "FAIL"} {line}"
        unless ok do
          allOk := false
          failed := failed.push line
      return (allOk, 0, 0, if allOk then none else some ("; ".intercalate failed.toList))) .done

/-! ### Recursive, mutual, nested and indexed types from records (the mode-repair branch, V7)

The class oracle classes a value of an inductive type by its constructors, and a
recursive field's type is the type itself. Before V7 it followed such a field to
its depth limit, where it declines (repair L), so `check` declined on each of
these honest programs. The run enters a match only through a case shape, a
definition over a recursor with one motive (`caseShape`, `motives == 1`) whose
alternatives forward their fields; each case reports how its matcher and its
`casesOn` read. Lean's matchers here are bodies, and the run reaches a value
through `L.casesOn` and `List.casesOn`. `A.casesOn` and `T.casesOn` are not case
shapes, their recursors having two motives (a mutual block's, a nested type's).
`V.casesOn` is not one either: as compiled, its minor premise forwards `cons h
n t` with the prefix `cons h n` behind a sharing reference, and `caseShape`'s
spine (`ixSpine`) does not read through a sharing reference in function
position. So `runR` is stuck on those three, limits of the run older than the
oracle's. -/

def recFixtureSeeds : List Lean.Name :=
  [`ModeRecFixture.mainL, `ModeRecFixture.mainList, `ModeRecFixture.mainA, `ModeRecFixture.mainT,
    `ModeRecFixture.mainV]

def recTypeCases : List RecCase := [
  { label := "a list-like inductive (mainL)", entry := `ModeRecFixture.mainL, reads := true, accept := true,
    value := some `ModeRecFixture.E.c₁, report := [`ModeRecFixture.headOr.match_1, `ModeRecFixture.L.casesOn] },
  { label := "Lean's List (mainList)", entry := `ModeRecFixture.mainList, reads := true, accept := true,
    value := some `ModeRecFixture.E.c₁, report := [`ModeRecFixture.headOrList.match_1, `List.casesOn] },
  { label := "a mutual pair (mainA); stuck: A.casesOn is not a case shape, A.rec having two motives",
    entry := `ModeRecFixture.mainA, reads := true, accept := true, stuck := true,
    report := [`ModeRecFixture.isA0.match_1, `ModeRecFixture.A.casesOn] },
  { label := "a nested inductive (mainT); stuck: T.casesOn is not a case shape, T.rec having two motives",
    entry := `ModeRecFixture.mainT, reads := true, accept := true, stuck := true,
    report := [`ModeRecFixture.isLeaf.match_1, `ModeRecFixture.T.casesOn] },
  { label := "an indexed family (mainV); stuck: V.casesOn is not read as a case shape (a spine through a sharing reference)",
    entry := `ModeRecFixture.mainV, reads := true, accept := true, stuck := true,
    report := [`ModeRecFixture.isNil.match_1, `ModeRecFixture.V.casesOn] }
]

def recTypeCasesTest : LSpec.TestSeq :=
  .individualIO "recursive, mutual, nested and indexed types from records: the class oracle answers" none (do
    match ← buildFixtureAt "Tests/Ix/ResourceModesRecFixture.lean" recFixtureSeeds with
    | .error e => return (false, 0, 0, some s!"the fixture: {e}")
    | .ok b =>
      let mut allOk := true
      let mut failed : Array String := #[]
      for c in recTypeCases do
        let (ok, line) := match runRecCase b c with
          | .ok r => r
          | .error e => (false, s!"{c.label}: {e}")
        IO.println s!"    {if ok then "ok" else "FAIL"} {line}"
        unless ok do
          allOk := false
          failed := failed.push line
      return (allOk, 0, 0, if allOk then none else some ("; ".intercalate failed.toList))) .done

public def suite : List LSpec.TestSeq :=
  erasedCases ++ uniqueCases ++ borrowCases ++ onceCases ++ captureCases ++ skeletonCases ++
    alternativeCases ++ findingCases ++ [limitCase, fastPathCase, recordCasesTest, recTypeCasesTest]

end Tests.ResourceModes
