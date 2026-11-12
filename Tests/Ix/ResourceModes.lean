module

public import IxC.Resource
public import LSpec

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
statics; limits; the fast path. -/

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
    (run : Option Violation) (accept : Bool) (toCheck : List Ref := [entry]) : LSpec.TestSeq :=
  .individualIO label none (do
    let P := prog defs
    let o := runR P noExtern 100000 entry input.1 input.2
    let runOk := match o, run with
      | .value .., none => true
      | .violation k, some k' => k == k'
      | _, _ => false
    let verdict := checkBodies {} P toCheck
    let checkOk := verdict.isAccept == accept
    -- what soundness gives on these inputs: accepted runs do not violate
    let consistent := !verdict.isAccept || match o with
      | .violation _ => false
      | _ => true
    let msg := s!"run: {outcomeName o}; checker: {verdictName verdict}"
    return (runOk && checkOk && consistent, 0, 0, if runOk && checkOk && consistent then none else some msg)) .done

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
  runCase "borrow: a let's loan read" [(letOk, body [par] (.letE .borrow .val (v 0) (lenOf (v 0)))
    .shared .leaf)] letOk oneList none true,
  runCase "borrow: a borrowed leaf returned" [(escN, body [par .borrowed .leaf] (v 0 .leaf) .shared .leaf)]
    escN oneNat (some .borrowEscape) false,
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
      { info := .axio ⟨false, 0, .all ⟨.many, .unique⟩ .shared (.sort 0) (.sort 0)⟩,
        sharing := #[], refs := #[], univs := #[.zero] }
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

public def suite : List LSpec.TestSeq :=
  erasedCases ++ uniqueCases ++ borrowCases ++ onceCases ++ captureCases ++ skeletonCases ++
    [limitCase, fastPathCase]

end Tests.ResourceModes
