import IxCC.Own.Plain.Owned

/-! # Liveness-based plain-RC ownership producer (untrusted)

Places `inc`/`dec` by backwards liveness over `Fir.Code`:
* A variable is dropped right after its last use on each path (at function/join entry if unused,
  at the start of a `case` branch that does not use it, after a `proj` or `prim` that was its last
  use, and on entry to a join continuation if a dead join forced a capture to stay alive until
  declaration).
* A variable is moved (not incremented) into its last consuming use (`ctor`, `call`, `arg`, `jmp`,
  `ret`, `tcall`), and incremented only for occurrences beyond the one it moves.
* A `proj` result is incremented immediately when live in its continuation (and skipped when dead);
  immediates (`prim` results and `primImmArgs`, literals, erased values, 0-arity constructors, and
  projections/copies of immediates) incur zero RC actions and are excluded from join captures.
* A join captures exactly the non-immediate variables its body uses besides its parameters.
* `trap` drops nothing (it terminates execution immediately).

This producer is **untrusted** and validated by the formally proved ownership checker
(`IxCC.Own.Plain.checkOwned`) plus the captured-work and certificate text/depth gates. Every
function here is total (zero `partial`, zero `sorry`), uses structural trie operations over
`Src.NatSet` (avoiding quadratic list scans), and emits actions and capture lists in deterministic
ascending `Var` order. -/

set_option autoImplicit false

namespace IxCC.Own.Plain.Live

open IxCC.Own.Plain
open IxCC.Fir (Var JoinId FunId Arg Rhs)

/-- Persistent variable set backed by `Src.NatSet` with structural pruning operations. -/
abbrev VSet := Src.NatSet

namespace VSet

def empty : VSet := .leaf

def singleton (x : Var) : VSet := Src.NatSet.insert .leaf x

/-- Smart node constructor that collapses empty subtries back to `.leaf`. -/
def mkNode (v : Option Unit) (z o : VSet) : VSet :=
  match v, z, o with
  | none, .leaf, .leaf => .leaf
  | _, _, _ => .node v z o

def isEmpty : VSet → Bool
  | .leaf => true
  | .node v z o => v.isNone && isEmpty z && isEmpty o

/-- Structural erasure that prunes empty subtries back to `.leaf`. -/
def eraseP : VSet → Var → VSet
  | .leaf, _ => .leaf
  | .node v z o, k =>
    if k == 0 then mkNode none z o
    else if k % 2 == 0 then mkNode v (eraseP z (k / 2)) o
    else mkNode v z (eraseP o (k / 2))

def addVars (s : VSet) (xs : List Var) : VSet :=
  xs.foldl (fun s x => Src.NatSet.insert s x) s

def ofVars (xs : List Var) : VSet := addVars .leaf xs

/-- Structural trie union (`O(|a| + |b|)`) without list conversion. -/
def union : VSet → VSet → VSet
  | .leaf, b => b
  | a, .leaf => a
  | .node va za oa, .node vb zb ob =>
    mkNode (va <|> vb) (union za zb) (union oa ob)

/-- Structural trie difference `a \ b` (`O(|a| + |b|)`) with empty-subtrie pruning. -/
def diff : VSet → VSet → VSet
  | .leaf, _ => .leaf
  | a, .leaf => a
  | .node va za oa, .node vb zb ob =>
    mkNode (if vb.isSome then none else va) (diff za zb) (diff oa ob)

/-- Structural trie intersection `a ∩ b` (`O(|a| + |b|)`) with empty-subtrie pruning. -/
def inter : VSet → VSet → VSet
  | .leaf, _ => .leaf
  | _, .leaf => .leaf
  | .node va za oa, .node vb zb ob =>
    mkNode (if va.isSome && vb.isSome then some () else none) (inter za zb) (inter oa ob)

/-- Structural subset check `a ⊆ b` (`O(|a|)`) with zero allocations. -/
def subset : VSet → VSet → Bool
  | .leaf, _ => true
  | a, .leaf => isEmpty a
  | .node va za oa, .node vb zb ob =>
    (va.isNone || vb.isSome) && subset za zb && subset oa ob

/-- Collect keys in trie order without allocating `(k, ())` pairs. -/
def varsAux : VSet → Nat → Nat → List Var → List Var
  | .leaf, _, _, acc => acc
  | .node v z o, k, w, acc =>
    let acc := varsAux o (k + w) (2 * w) acc
    let acc := varsAux z k (2 * w) acc
    match v with
    | some () => k :: acc
    | none => acc

/-- Structural fuel-bounded `O(|xs| + |ys|)` merge (no `WellFounded.fix`). -/
def mergeByF {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | _, [], ys => ys
  | _, xs, [] => xs
  | 0, xs, ys => xs ++ ys
  | fuel + 1, x :: xs, y :: ys =>
    if le x y then x :: mergeByF le fuel xs (y :: ys)
    else y :: mergeByF le fuel (x :: xs) ys

def mergeBy {α : Type} (le : α → α → Bool) (xs ys : List α) : List α :=
  mergeByF le (xs.length + ys.length) xs ys

def mergePairs {α : Type} (le : α → α → Bool) : List (List α) → List (List α)
  | a :: b :: rest => mergeBy le a b :: mergePairs le rest
  | xs => xs

def mergeAll {α : Type} (le : α → α → Bool) : Nat → List (List α) → List α
  | _, [] => []
  | _, [xs] => xs
  | 0, xss => xss.foldl (mergeBy le) []
  | fuel + 1, xss => mergeAll le fuel (mergePairs le xss)

/-- Total, kernel-reducible `O(n log n)` bottom-up merge sort (zero `WellFounded.fix`). -/
def sortBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | xs => mergeAll le xs.length (xs.map ([·]))

/-- All variables in `s`, sorted in deterministic ascending `Var` order. -/
def toSortedVars (s : VSet) : List Var :=
  sortBy (· ≤ ·) (varsAux s 0 1 [])

end VSet

def rhsVars : Rhs → List Var
  | .arg a => argVars [a]
  | .ctor c args => if c.arity == 0 then [] else argVars args
  | .call _ args | .prim _ args => argVars args
  | .proj y _ _ => [y]

/-! ## Pass 1: Backwards liveness annotation -/

mutual
inductive ACode where
  | bind (x : Var) (r : Rhs) (k : ACode) (liveK : VSet)
  | jp (j : JoinId) (ps : List Var) (rec : Bool) (body k : ACode)
      (captured : List Var) (liveBody liveK : VSet)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List AAlt) (dflt : Option (ACode × VSet))
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap

inductive AAlt where
  | mk (key : Key.CtorKey) (body : ACode) (live : VSet)
end

mutual
/-- Pure live-in computation over `Fir.Code` without building `ACode`.
Because every node's live-in map is additive in `Δ[j]` (`liveOf (Δ[j ↦ c]) e ⊆ liveOf (Δ[j ↦ ∅]) e ∪ c`),
a recursive join's exact least capture set is already `liveOf (Δ[j ↦ ∅]) body \ ps`, keeping
nested joins strictly linear instead of exponential. Including `captured` in `.jp`'s live-in ensures
even a dead (uncalled) join's captured variables remain available for `needCaptured` at declaration. -/
def liveOf (Δ : Src.NatMap VSet) : Fir.Code → VSet
  | .bind x r k =>
    VSet.addVars (VSet.eraseP (liveOf Δ k) x) (rhsVars r)
  | .jp j ps rec body k =>
    let psSet := VSet.ofVars ps
    let liveBody := liveOf (if rec then Δ.insert j .leaf else Δ) body
    let captured := VSet.diff liveBody psSet
    VSet.union (liveOf (Δ.insert j captured) k) captured
  | .jmp j args =>
    VSet.addVars (Δ.getD j .leaf) (argVars args)
  | .case x alts d =>
    VSet.union (VSet.singleton x) (VSet.union (liveOfAlts Δ alts) (liveOfOpt Δ d))
  | .ret a => VSet.ofVars (argVars [a])
  | .tcall _ args => VSet.ofVars (argVars args)
  | .trap => .leaf

def liveOfAlts (Δ : Src.NatMap VSet) : List Fir.Alt → VSet
  | [] => .leaf
  | .mk _ body :: rest => VSet.union (liveOf Δ body) (liveOfAlts Δ rest)

def liveOfOpt (Δ : Src.NatMap VSet) : Option Fir.Code → VSet
  | none => .leaf
  | some dc => liveOf Δ dc
end

/-- Fuel-bounded fixpoint loop for a recursive join's captured set. Seeded with the single-pass
`liveOf` set, this converges on the first check; explicit fuel keeps termination structural. -/
def fixCaptured (Δ : Src.NatMap VSet) (j : JoinId) (ps : VSet) (body : Fir.Code) :
    Nat → VSet → VSet
  | 0, c => c
  | fuel + 1, c =>
    let c' := VSet.diff (liveOf (Δ.insert j c) body) ps
    if VSet.subset c' c then c' else fixCaptured Δ j ps body fuel c'

/-- Default fixpoint fuel for `fixCaptured`. -/
def fixFuel : Nat := 1024

mutual
def annotate (Δ : Src.NatMap VSet) : Fir.Code → ACode × VSet
  | .bind x r k =>
    let (ak, lk) := annotate Δ k
    (.bind x r ak lk, VSet.addVars (VSet.eraseP lk x) (rhsVars r))
  | .jp j ps rec body k =>
    let psSet := VSet.ofVars ps
    let (ab, lb, capturedSet) :=
      if rec then
        let c0 := VSet.diff (liveOf (Δ.insert j .leaf) body) psSet
        let cap := if VSet.isEmpty c0 then .leaf else fixCaptured Δ j psSet body fixFuel c0
        let (ab, lb) := annotate (Δ.insert j cap) body
        (ab, lb, cap)
      else
        let (ab, lb) := annotate Δ body
        (ab, lb, VSet.diff lb psSet)
    let (ak, lk) := annotate (Δ.insert j capturedSet) k
    let captured := VSet.toSortedVars capturedSet
    (.jp j ps rec ab ak captured lb lk, VSet.union lk capturedSet)
  | .jmp j args =>
    (.jmp j args, VSet.addVars (Δ.getD j .leaf) (argVars args))
  | .case x alts d =>
    let (as, la) := annotateAlts Δ alts
    let (ad, ld) := annotateOpt Δ d
    (.case x as ad, VSet.union (VSet.singleton x) (VSet.union la ld))
  | .ret a => (.ret a, VSet.ofVars (argVars [a]))
  | .tcall f args => (.tcall f args, VSet.ofVars (argVars args))
  | .trap => (.trap, .leaf)

def annotateAlts (Δ : Src.NatMap VSet) : List Fir.Alt → List AAlt × VSet
  | [] => ([], .leaf)
  | .mk key body :: rest =>
    let (ab, lb) := annotate Δ body
    let (as, lr) := annotateAlts Δ rest
    (.mk key ab lb :: as, VSet.union lb lr)

def annotateOpt (Δ : Src.NatMap VSet) : Option Fir.Code → Option (ACode × VSet) × VSet
  | none => (none, .leaf)
  | some c =>
    let (ac, lc) := annotate Δ c
    (some (ac, lc), lc)
end

/-! ## Pass 2: Forward ownership action placement -/

/-- Count non-immediate variable occurrences in `args` in `O(|args| log V)`. -/
def countNonImmArgs (imm : VSet) (args : List Arg) : Src.NatMap Nat :=
  args.foldl (fun counts a =>
    match a with
    | .var v =>
      if imm.contains v then counts
      else counts.insert v (counts.getD v 0 + 1)
    | _ => counts) .leaf

def pushIncs (v : Var) : Nat → List Action → List Action
  | 0, acc => acc
  | n + 1, acc => pushIncs v n (.inc v 1 :: acc)

/-- Tokens for a consuming use: move one owned token of each variable not live afterwards,
increment for every other occurrence. Returns `(incs, ownedAfterMoves)` with increments ordered
by deterministic ascending `Var`. -/
def consume (owned imm liveAfter : VSet) (args : List Arg) : List Action × VSet :=
  let counts := countNonImmArgs imm args
  let pairs := VSet.sortBy (fun a b => a.1 ≤ b.1) counts.toList
  pairs.foldr (fun (v, n) (incs, owned) =>
    if owned.contains v && !liveAfter.contains v then
      (pushIncs v (n - 1) incs, VSet.eraseP owned v)
    else
      (pushIncs v n incs, owned)) ([], owned)

def decs (xs : List Var) : List Action := xs.map .dec

/-- Apply `Own.Plain.primImmArgs` to `(owned, imm)`: every argument position marked immediate
moves from `owned` into `imm`, matching `Ctx.immArgs`. -/
def applyPrimImm : List Bool → List Arg → VSet × VSet → VSet × VSet
  | true :: ms, .var v :: as, (owned, imm) =>
    applyPrimImm ms as (VSet.eraseP owned v, Src.NatSet.insert imm v)
  | _ :: ms, _ :: as, st => applyPrimImm ms as st
  | _, _, st => st

mutual
def place (Δ : Src.NatMap VSet) (owned imm : VSet) : ACode → Code
  | .bind x r k liveK =>
    match r with
    | .proj y _ _ =>
      if imm.contains y then
        .bind x r (place Δ owned (Src.NatSet.insert imm x) k)
      else
        let (owned, incs) :=
          if liveK.contains x then (Src.NatSet.insert owned x, [Action.inc x 1])
          else (owned, [])
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned' := VSet.inter owned liveK
        .bind x r (actionPrefix (incs ++ decs dead) (place Δ owned' imm k))
    | .prim op args =>
      let (owned, imm) := applyPrimImm (primImmArgs op args.length) args (owned, imm)
      let imm := Src.NatSet.insert imm x
      let dead := VSet.toSortedVars (VSet.diff owned liveK)
      let owned' := VSet.inter owned liveK
      .bind x r (actionPrefix (decs dead) (place Δ owned' imm k))
    | .arg (.var y) =>
      if imm.contains y then
        .bind x r (place Δ owned (Src.NatSet.insert imm x) k)
      else
        let (incs, owned) := consume owned imm liveK [.var y]
        let (owned, post) :=
          if liveK.contains x then (Src.NatSet.insert owned x, [])
          else (owned, [Action.dec x])
        actionPrefix incs (.bind x r (actionPrefix post (place Δ owned imm k)))
    | .arg _ =>
      .bind x r (place Δ owned (Src.NatSet.insert imm x) k)
    | .ctor c args =>
      if c.arity == 0 then
        .bind x r (place Δ owned (Src.NatSet.insert imm x) k)
      else
        let (incs, owned) := consume owned imm liveK args
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned := VSet.inter owned liveK
        let (owned, post) :=
          if liveK.contains x then (Src.NatSet.insert owned x, [])
          else (owned, [Action.dec x])
        actionPrefix (decs dead ++ incs) (.bind x r (actionPrefix post (place Δ owned imm k)))
    | .call _ args =>
      let (incs, owned) := consume owned imm liveK args
      let dead := VSet.toSortedVars (VSet.diff owned liveK)
      let owned := VSet.inter owned liveK
      let (owned, post) :=
        if liveK.contains x then (Src.NatSet.insert owned x, [])
        else (owned, [Action.dec x])
      actionPrefix (decs dead ++ incs) (.bind x r (actionPrefix post (place Δ owned imm k)))
  | .jp j ps rec body k captured liveBody liveK =>
    let captured := captured.filter (!imm.contains ·)
    let capturedSet := VSet.ofVars captured
    let ownedBody := VSet.addVars capturedSet ps
    let deadBody := VSet.toSortedVars (VSet.diff ownedBody liveBody)
    let ownedBody' := VSet.inter ownedBody liveBody
    let Δbody := if rec then Δ.insert j capturedSet else Δ
    let bodyCode := actionPrefix (decs deadBody) (place Δbody ownedBody' imm body)
    let deadK := VSet.toSortedVars (VSet.diff owned liveK)
    let ownedK := VSet.inter owned liveK
    let kCode := actionPrefix (decs deadK) (place (Δ.insert j capturedSet) ownedK imm k)
    .jp j ps captured rec bodyCode kCode
  | .jmp j args =>
    let keep := Δ.getD j .leaf
    let (incs, owned) := consume owned imm keep args
    let dead := VSet.toSortedVars (VSet.diff owned keep)
    actionPrefix (incs ++ decs dead) (.jmp j args)
  | .case x alts d =>
    .case x (placeAlts Δ owned imm alts) (placeOpt Δ owned imm d)
  | .ret a =>
    let (incs, owned) := consume owned imm .leaf [a]
    actionPrefix (incs ++ decs (VSet.toSortedVars owned)) (.ret a)
  | .tcall f args =>
    let (incs, owned) := consume owned imm .leaf args
    actionPrefix (incs ++ decs (VSet.toSortedVars owned)) (.tcall f args)
  | .trap => .trap

def placeAlts (Δ : Src.NatMap VSet) (owned imm : VSet) : List AAlt → List Alt
  | [] => []
  | .mk key ab lb :: rest =>
    let dead := VSet.toSortedVars (VSet.diff owned lb)
    let owned' := VSet.inter owned lb
    .mk key (actionPrefix (decs dead) (place Δ owned' imm ab)) :: placeAlts Δ owned imm rest

def placeOpt (Δ : Src.NatMap VSet) (owned imm : VSet) : Option (ACode × VSet) → Option Code
  | none => none
  | some (ad, ld) =>
    let dead := VSet.toSortedVars (VSet.diff owned ld)
    let owned' := VSet.inter owned ld
    some (actionPrefix (decs dead) (place Δ owned' imm ad))
end

/-- Select arguments at non-borrowed (`false`) positions according to `bs`. -/
def selectOwnedArgs : List Bool → List Arg → List Arg
  | _, [] => []
  | true :: bs, _ :: as => selectOwnedArgs bs as
  | false :: bs, a :: as => a :: selectOwnedArgs bs as
  | [], as => as

/-- Select arguments at borrowed (`true`) positions according to `bs`. -/
def selectBorrowedArgs : List Bool → List Arg → List Arg
  | _, [] => []
  | true :: bs, a :: as => a :: selectBorrowedArgs bs as
  | false :: bs, _ :: as => selectBorrowedArgs bs as
  | [], _ => []

mutual
/-- Size classes of reusable heap constructors allocated in a `Fir.Code` body. -/
def allocClassesCode : Fir.Code → VSet
  | .bind _ (.ctor c _) k =>
    let rest := allocClassesCode k
    match Ctx.validReuseCtor c with
    | some cls => Src.NatSet.insert rest cls
    | none => rest
  | .bind _ _ k => allocClassesCode k
  | .jp _ _ _ b k => VSet.union (allocClassesCode b) (allocClassesCode k)
  | .case _ alts d => VSet.union (allocClassesAlts alts) (allocClassesOpt d)
  | .jmp .. | .ret .. | .tcall .. | .trap => .leaf
def allocClassesAlts : List Fir.Alt → VSet
  | [] => .leaf
  | .mk _ b :: rest => VSet.union (allocClassesCode b) (allocClassesAlts rest)
def allocClassesOpt : Option Fir.Code → VSet
  | none => .leaf
  | some c => allocClassesCode c
end

/-- Whether any arm of `alts` scrutinizes a non-Nat reusable heap constructor whose size class
is allocated in the enclosing function (so keeping the scrutinee owned enables FBIP reuse). -/
def caseCanReset (ctors : List Lam.CtorInfo) (known : Lam.Known) (allocClasses : VSet)
    (alts : List Fir.Alt) : Bool :=
  !VSet.isEmpty allocClasses &&
  alts.any fun alt =>
    !(known.natZero == some alt.key || known.natSucc == some alt.key) &&
    match Fir.CtorInfo.ofKey ctors alt.key with
    | some c =>
      match Ctx.validReuseCtor c with
      | some cls => allocClasses.contains cls
      | none => false
    | none => false

/-- Clear `(f, idx)` to `false` in `borrows`, returning `(borrows', changed)`. -/
def clearBorrow (borrows : BorrowSigs) (f idx : Nat) : BorrowSigs × Bool :=
  match borrows.get? f with
  | none => (borrows, false)
  | some bs =>
    if bs.getD idx false then
      (borrows.insert f (bs.set idx false), true)
    else (borrows, false)

/-- Clear `(f, i)` for every variable `v` in `args` whose `pbrwSrc` records `(f, i)`
(optionally restricted to `direct` aliases). -/
def clearArgsBorrows (f : FunId) (pbrwSrc : Src.NatMap Nat) (directOnly : Bool) (direct : VSet)
    (args : List Arg) (st : BorrowSigs × Bool) : BorrowSigs × Bool :=
  args.foldl (fun acc a =>
    match a with
    | .var v =>
      match pbrwSrc.get? v with
      | some i =>
        if !directOnly || direct.contains v then clearBorrow acc.1 f i |>.map id (acc.2 || ·)
        else acc
      | none => acc
    | _ => acc) st

/-- Clear `(f, i)` for a single variable if present in `pbrwSrc`. -/
def clearVarBorrow (f : FunId) (pbrwSrc : Src.NatMap Nat) (directOnly : Bool) (direct : VSet)
    (v : Var) (st : BorrowSigs × Bool) : BorrowSigs × Bool :=
  match pbrwSrc.get? v with
  | some i =>
    if !directOnly || direct.contains v then
      let (b', ch) := clearBorrow st.1 f i
      (b', st.2 || ch)
    else st
  | none => st

/-- Check arguments of a `.call` or `.tcall` to callee `g` against `borrows`:
* owned callee positions force any direct-aliased borrowed param of `f` to become owned;
* for tail calls (`isTail = true`), borrowed callee positions whose argument is neither immediate
  nor derived from a borrowed param of `f` force the *callee's* parameter to become owned. -/
def checkCallArgsBorrow (f g : FunId) (isTail : Bool) (imm direct : VSet)
    (pbrwSrc : Src.NatMap Nat) (args : List Arg) (st : BorrowSigs × Bool) : BorrowSigs × Bool :=
  let gbs := st.1.getD g []
  (args.zipIdx).foldl (fun acc (a, k) =>
    let isCalleeBrw := gbs.getD k false
    if isCalleeBrw then
      if isTail then
        match a with
        | .var v =>
          if !imm.contains v && !pbrwSrc.contains v then
            let (b', ch) := clearBorrow acc.1 g k
            (b', acc.2 || ch)
          else acc
        | _ => acc
      else acc
    else
      match a with
      | .var v => clearVarBorrow f pbrwSrc false direct v acc
      | _ => acc) st

/-- Apply `primImmArgs` to `imm` only (matching `Ctx.immArgs`). -/
def addPrimImm : List Bool → List Arg → VSet → VSet
  | true :: ms, .var v :: as, imm => addPrimImm ms as (Src.NatSet.insert imm v)
  | _ :: ms, _ :: as, imm => addPrimImm ms as imm
  | _, _, imm => imm

mutual
/-- One pass over `fd.body` clearing any borrow flags invalidated by consuming uses,
FBIP-resettable scrutiny (kept owned for reuse), or non-caller-backed tail calls. -/
def refineBorrowCode (ctors : List Lam.CtorInfo) (known : Lam.Known) (f : FunId)
    (allocClasses imm direct : VSet) (pbrwSrc : Src.NatMap Nat)
    (st : BorrowSigs × Bool) : Fir.Code → BorrowSigs × Bool
  | .bind x r k =>
    match r with
    | .arg (.var y) =>
      if imm.contains y then
        refineBorrowCode ctors known f allocClasses (Src.NatSet.insert imm x) direct pbrwSrc st k
      else
        let pbrwSrc' := match pbrwSrc.get? y with
          | some i => pbrwSrc.insert x i
          | none => pbrwSrc
        let direct' := if direct.contains y then Src.NatSet.insert direct x else direct
        refineBorrowCode ctors known f allocClasses imm direct' pbrwSrc' st k
    | .arg _ =>
      refineBorrowCode ctors known f allocClasses (Src.NatSet.insert imm x) direct pbrwSrc st k
    | .ctor c args =>
      if c.arity == 0 then
        refineBorrowCode ctors known f allocClasses (Src.NatSet.insert imm x) direct pbrwSrc st k
      else
        let st := clearArgsBorrows f pbrwSrc false direct args st
        refineBorrowCode ctors known f allocClasses imm direct pbrwSrc st k
    | .call g args =>
      let st := checkCallArgsBorrow f g false imm direct pbrwSrc args st
      refineBorrowCode ctors known f allocClasses imm direct pbrwSrc st k
    | .proj y _ _ =>
      if imm.contains y then
        refineBorrowCode ctors known f allocClasses (Src.NatSet.insert imm x) direct pbrwSrc st k
      else
        let pbrwSrc' := match pbrwSrc.get? y with
          | some i => pbrwSrc.insert x i
          | none => pbrwSrc
        refineBorrowCode ctors known f allocClasses imm direct pbrwSrc' st k
    | .prim op args =>
      let imm' := Src.NatSet.insert (addPrimImm (primImmArgs op args.length) args imm) x
      refineBorrowCode ctors known f allocClasses imm' direct pbrwSrc st k
  | .jp _ _ _ body k =>
    let st := refineBorrowCode ctors known f allocClasses imm direct pbrwSrc st body
    refineBorrowCode ctors known f allocClasses imm direct pbrwSrc st k
  | .jmp _ args =>
    clearArgsBorrows f pbrwSrc false direct args st
  | .case x alts d =>
    let st := if caseCanReset ctors known allocClasses alts then clearVarBorrow f pbrwSrc true direct x st else st
    let st := refineBorrowAlts ctors known f allocClasses imm direct pbrwSrc st alts
    refineBorrowOpt ctors known f allocClasses imm direct pbrwSrc st d
  | .ret a =>
    clearArgsBorrows f pbrwSrc false direct [a] st
  | .tcall g args =>
    checkCallArgsBorrow f g true imm direct pbrwSrc args st
  | .trap => st

def refineBorrowAlts (ctors : List Lam.CtorInfo) (known : Lam.Known) (f : FunId)
    (allocClasses imm direct : VSet) (pbrwSrc : Src.NatMap Nat)
    (st : BorrowSigs × Bool) : List Fir.Alt → BorrowSigs × Bool
  | [] => st
  | .mk _ body :: rest =>
    let st := refineBorrowCode ctors known f allocClasses imm direct pbrwSrc st body
    refineBorrowAlts ctors known f allocClasses imm direct pbrwSrc st rest

def refineBorrowOpt (ctors : List Lam.CtorInfo) (known : Lam.Known) (f : FunId)
    (allocClasses imm direct : VSet) (pbrwSrc : Src.NatMap Nat)
    (st : BorrowSigs × Bool) : Option Fir.Code → BorrowSigs × Bool
  | none => st
  | some c => refineBorrowCode ctors known f allocClasses imm direct pbrwSrc st c
end

/-- One full program sweep of interprocedural borrow refinement. -/
def refineBorrowPass (F : Fir.Program) (allocs : Src.NatMap VSet) (borrows : BorrowSigs) :
    BorrowSigs × Bool :=
  (List.range F.size).foldl (fun st f =>
    match F.fun? f with
    | none => st
    | some fd =>
      let bs := st.1.getD f []
      let (pbrwSrc, direct) := (fd.params.zipIdx).foldl (fun (pm, dm) ((p, _), i) =>
        if bs.getD i false then (pm.insert p i, Src.NatSet.insert dm p) else (pm, dm)) (.leaf, .leaf)
      refineBorrowCode F.ctors F.known f (allocs.getD f .leaf) .leaf direct pbrwSrc st fd.body) (borrows, false)

def borrowFixLoop (F : Fir.Program) (allocs : Src.NatMap VSet) : Nat → BorrowSigs → BorrowSigs
  | 0, borrows => borrows
  | fuel + 1, borrows =>
    let (borrows', changed) := refineBorrowPass F allocs borrows
    if changed then borrowFixLoop F allocs fuel borrows' else borrows'

/-- Total fuel-bounded interprocedural borrow inference. Starts optimistic (`true`) on every
parameter of every non-exported function and monotonically clears parameters to `false` (owned)
until fixpoint. Exported functions always own all parameters. -/
def inferBorrows (F : Fir.Program) : BorrowSigs :=
  let expSet := VSet.ofVars F.exports
  let init : BorrowSigs := (List.range F.size).foldl (fun m f =>
    match F.fun? f with
    | none => m
    | some fd =>
      let b := !expSet.contains f
      m.insert f (List.replicate fd.params.length b)) .leaf
  let allocs : Src.NatMap VSet := (List.range F.size).foldl (fun m f =>
    match F.fun? f with
    | none => m
    | some fd => m.insert f (allocClassesCode fd.body)) .leaf
  let fuel := 64
  borrowFixLoop F allocs fuel init

/-- Whether a freshly projected variable `x` can stay epoch-borrowed with zero `inc`/`dec`:
immediately scrutinized by `case x` and dead in all arms, or immediately passed to a
primitive position marked immediate (`primImmArgs`). Requires no intervening release. -/
def canBorrowProj (x : Var) : ACode → Bool
  | .case s alts d =>
    s == x &&
    alts.all (fun | .mk _ _ lb => !lb.contains x) &&
    (match d with | none => true | some (_, ld) => !ld.contains x)
  | .bind _ (.prim op args) _ _ =>
    ((primImmArgs op args.length).zip args).any fun (m, a) => m && a == .var x
  | _ => false

mutual
def placeWith (borrows : BorrowSigs) (Δ : Src.NatMap VSet) (owned imm pbrw : VSet) : ACode → Code
  | .bind x r k liveK =>
    match r with
    | .proj y _ _ =>
      if imm.contains y then
        .bind x r (placeWith borrows Δ owned (Src.NatSet.insert imm x) pbrw k)
      else if pbrw.contains y then
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned' := VSet.inter owned liveK
        .bind x r (actionPrefix (decs dead) (placeWith borrows Δ owned' imm (Src.NatSet.insert pbrw x) k))
      else
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let (owned, incs) :=
          if liveK.contains x && !(dead.isEmpty && canBorrowProj x k) then
            (Src.NatSet.insert owned x, [Action.inc x 1])
          else (owned, [])
        let owned' := VSet.inter owned liveK
        .bind x r (actionPrefix (incs ++ decs dead) (placeWith borrows Δ owned' imm pbrw k))
    | .prim op args =>
      let (owned, imm) := applyPrimImm (primImmArgs op args.length) args (owned, imm)
      let imm := Src.NatSet.insert imm x
      let dead := VSet.toSortedVars (VSet.diff owned liveK)
      let owned' := VSet.inter owned liveK
      .bind x r (actionPrefix (decs dead) (placeWith borrows Δ owned' imm pbrw k))
    | .arg (.var y) =>
      if imm.contains y then
        .bind x r (placeWith borrows Δ owned (Src.NatSet.insert imm x) pbrw k)
      else if !owned.contains y && pbrw.contains y then
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned' := VSet.inter owned liveK
        .bind x r (actionPrefix (decs dead) (placeWith borrows Δ owned' imm (Src.NatSet.insert pbrw x) k))
      else
        let (incs, owned) := consume owned imm liveK [.var y]
        let (owned, post) :=
          if liveK.contains x then (Src.NatSet.insert owned x, [])
          else (owned, [Action.dec x])
        actionPrefix incs (.bind x r (actionPrefix post (placeWith borrows Δ owned imm pbrw k)))
    | .arg _ =>
      .bind x r (placeWith borrows Δ owned (Src.NatSet.insert imm x) pbrw k)
    | .ctor c args =>
      if c.arity == 0 then
        .bind x r (placeWith borrows Δ owned (Src.NatSet.insert imm x) pbrw k)
      else
        let (incs, owned) := consume owned imm liveK args
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned := VSet.inter owned liveK
        let (owned, post) :=
          if liveK.contains x then (Src.NatSet.insert owned x, [])
          else (owned, [Action.dec x])
        actionPrefix (decs dead ++ incs) (.bind x r (actionPrefix post (placeWith borrows Δ owned imm pbrw k)))
    | .call f args =>
      let bs := borrows.getD f []
      let ownedArgs := selectOwnedArgs bs args
      let borrowedArgs := selectBorrowedArgs bs args
      let keepAlive := VSet.union liveK (VSet.ofVars (argVars borrowedArgs))
      let (incs, ownedAfterTake) := consume owned imm keepAlive ownedArgs
      let deadBefore := VSet.toSortedVars (VSet.diff ownedAfterTake keepAlive)
      let ownedAcross := VSet.inter ownedAfterTake keepAlive
      let deadAfter := VSet.toSortedVars (VSet.diff ownedAcross liveK)
      let ownedAfterCall := VSet.inter ownedAcross liveK
      let (ownedFinal, post) :=
        if liveK.contains x then (Src.NatSet.insert ownedAfterCall x, decs deadAfter)
        else (ownedAfterCall, Action.dec x :: decs deadAfter)
      actionPrefix (decs deadBefore ++ incs) (.bind x r (actionPrefix post (placeWith borrows Δ ownedFinal imm pbrw k)))
  | .jp j ps rec body k captured liveBody liveK =>
    let captured := captured.filter (fun c => !imm.contains c && !pbrw.contains c)
    let capturedSet := VSet.ofVars captured
    let ownedBody := VSet.addVars capturedSet ps
    let deadBody := VSet.toSortedVars (VSet.diff ownedBody liveBody)
    let ownedBody' := VSet.inter ownedBody liveBody
    let Δbody := if rec then Δ.insert j capturedSet else Δ
    let bodyCode := actionPrefix (decs deadBody) (placeWith borrows Δbody ownedBody' imm pbrw body)
    let deadK := VSet.toSortedVars (VSet.diff owned liveK)
    let ownedK := VSet.inter owned liveK
    let kCode := actionPrefix (decs deadK) (placeWith borrows (Δ.insert j capturedSet) ownedK imm pbrw k)
    .jp j ps captured rec bodyCode kCode
  | .jmp j args =>
    let keep := Δ.getD j .leaf
    let (incs, owned) := consume owned imm keep args
    let dead := VSet.toSortedVars (VSet.diff owned keep)
    actionPrefix (incs ++ decs dead) (.jmp j args)
  | .case x alts d =>
    .case x (placeAltsWith borrows Δ owned imm pbrw alts) (placeOptWith borrows Δ owned imm pbrw d)
  | .ret a =>
    let (incs, owned) := consume owned imm .leaf [a]
    actionPrefix (incs ++ decs (VSet.toSortedVars owned)) (.ret a)
  | .tcall f args =>
    let bs := borrows.getD f []
    let ownedArgs := selectOwnedArgs bs args
    let (incs, owned) := consume owned imm .leaf ownedArgs
    actionPrefix (incs ++ decs (VSet.toSortedVars owned)) (.tcall f args)
  | .trap => .trap

def placeAltsWith (borrows : BorrowSigs) (Δ : Src.NatMap VSet) (owned imm pbrw : VSet) :
    List AAlt → List Alt
  | [] => []
  | .mk key ab lb :: rest =>
    let dead := VSet.toSortedVars (VSet.diff owned lb)
    let owned' := VSet.inter owned lb
    .mk key (actionPrefix (decs dead) (placeWith borrows Δ owned' imm pbrw ab)) ::
      placeAltsWith borrows Δ owned imm pbrw rest

def placeOptWith (borrows : BorrowSigs) (Δ : Src.NatMap VSet) (owned imm pbrw : VSet) :
    Option (ACode × VSet) → Option Code
  | none => none
  | some (ad, ld) =>
    let dead := VSet.toSortedVars (VSet.diff owned ld)
    let owned' := VSet.inter owned ld
    some (actionPrefix (decs dead) (placeWith borrows Δ owned' imm pbrw ad))
end

/-- Place `inc`/`dec` on one FIR function body using liveness and interprocedural borrow masks. -/
def liveBodyWith (borrows : BorrowSigs) (selfBorrows : List Bool) (params : List Var)
    (body : Fir.Code) : Code :=
  let (ab, lb) := annotate .leaf body
  let owned := VSet.ofVars (Ctx.entryOwned params selfBorrows)
  let pbrw := VSet.ofVars (Ctx.entryBorrowed params selfBorrows)
  let dead := VSet.toSortedVars (VSet.diff owned lb)
  let owned' := VSet.inter owned lb
  actionPrefix (decs dead) (placeWith borrows .leaf owned' .leaf pbrw ab)

/-- Map a `Src.NatMap` preserving its exact trie shape while passing each entry's key. -/
def mapWithKeyAux {α β : Type} (f : Nat → α → β) : Nat → Nat → Src.NatMap α → Src.NatMap β
  | _, _, .leaf => .leaf
  | k, w, .node v z o =>
    .node (v.map (f k)) (mapWithKeyAux f k (2 * w) z) (mapWithKeyAux f (k + w) (2 * w) o)

/-! ## Track A4: Interprocedural `@unique` inference and FBIP `reset`/`reuse` placement -/

/-- Clear param `idx`'s `@unique` flag for function `f` in `uniqs`. -/
def clearParamUniq (uniqs : UniqSigs) (f idx : Nat) : UniqSigs × Bool :=
  match uniqs.get? f with
  | none => (uniqs, false)
  | some (us, retU) =>
    if us.getD idx false then
      (uniqs.insert f (us.set idx false, retU), true)
    else (uniqs, false)

/-- Clear `retUnique` for function `f` in `uniqs`. -/
def clearRetUniq (uniqs : UniqSigs) (f : Nat) : UniqSigs × Bool :=
  match uniqs.get? f with
  | none => (uniqs, false)
  | some (us, retU) =>
    if retU then (uniqs.insert f (us, false), true) else (uniqs, false)

/-- Check call/tcall arguments against callee `g`'s `@unique` parameter mask, clearing any
position that is not guaranteed uniquely moved (or immediate). Returns `(uniqs', changed, uniqVarsAfter)`. -/
def checkCallArgsUniq (borrows : BorrowSigs) (g : FunId) (imm uniq : VSet)
    (keepAlive : VSet) (args : List Arg) (st : UniqSigs × Bool) : UniqSigs × Bool × VSet :=
  let bs := borrows.getD g []
  let ownedArgs := selectOwnedArgs bs args
  let counts := countNonImmArgs imm ownedArgs
  let (st', uniq') := (args.zipIdx).foldl (fun (acc, u) (a, idx) =>
    let isBrw := bs.getD idx false
    let isCalleeUniq := (acc.1.getD g ([], false)).1.getD idx false
    match a with
    | .var v =>
      if isBrw then
        (acc, VSet.eraseP u v)
      else
        let ok := imm.contains v || (u.contains v && !keepAlive.contains v && counts.getD v 0 == 1)
        let acc' :=
          if isCalleeUniq && !ok then
            let (m', ch) := clearParamUniq acc.1 g idx
            (m', acc.2 || ch)
          else acc
        (acc', VSet.eraseP u v)
    | _ => (acc, u)) (st, uniq)
  (st'.1, st'.2, uniq')

mutual
/-- One pass over annotated `ACode` refining `uniqs` (`@unique` params and `retUnique`). -/
def refineUniqCode (borrows : BorrowSigs) (f : FunId) (imm uniq : VSet)
    (st : UniqSigs × Bool) : ACode → UniqSigs × Bool
  | .bind x r k liveK =>
    match r with
    | .proj y _ _ =>
      if imm.contains y then
        refineUniqCode borrows f (Src.NatSet.insert imm x) (Src.NatSet.insert uniq x) st k
      else
        refineUniqCode borrows f imm uniq st k
    | .prim op args =>
      let imm' := Src.NatSet.insert (addPrimImm (primImmArgs op args.length) args imm) x
      let uniq' := Src.NatSet.insert (addPrimImm (primImmArgs op args.length) args uniq) x
      refineUniqCode borrows f imm' uniq' st k
    | .arg (.var y) =>
      if imm.contains y then
        refineUniqCode borrows f (Src.NatSet.insert imm x) (Src.NatSet.insert uniq x) st k
      else if uniq.contains y && !liveK.contains y then
        let uniq' := Src.NatSet.insert (VSet.eraseP uniq y) x
        refineUniqCode borrows f imm uniq' st k
      else
        refineUniqCode borrows f imm (VSet.eraseP uniq y) st k
    | .arg _ =>
      refineUniqCode borrows f (Src.NatSet.insert imm x) (Src.NatSet.insert uniq x) st k
    | .ctor c args =>
      if c.arity == 0 then
        refineUniqCode borrows f (Src.NatSet.insert imm x) (Src.NatSet.insert uniq x) st k
      else
        let uniq' := (argVars args).foldl (fun u v => VSet.eraseP u v) uniq
        refineUniqCode borrows f imm (Src.NatSet.insert uniq' x) st k
    | .call g args =>
      let bs := borrows.getD g []
      let borrowedArgs := selectBorrowedArgs bs args
      let keepAlive := VSet.union liveK (VSet.ofVars (argVars borrowedArgs))
      let (m', ch', uniq') := checkCallArgsUniq borrows g imm uniq keepAlive args st
      let calleeRetU := (m'.getD g ([], false)).2
      let uniq'' := if calleeRetU then Src.NatSet.insert uniq' x else uniq'
      refineUniqCode borrows f imm uniq'' (m', ch') k
  | .jp _ _ _ body k _ _ _ =>
    let st := refineUniqCode borrows f imm imm st body
    refineUniqCode borrows f imm uniq st k
  | .jmp _ _ => st
  | .case _ alts d =>
    let st := refineUniqAlts borrows f imm uniq st alts
    refineUniqOpt borrows f imm uniq st d
  | .ret a =>
    let retU := (st.1.getD f ([], false)).2
    if retU then
      match a with
      | .var y =>
        if imm.contains y || uniq.contains y then st
        else
          let (m', ch) := clearRetUniq st.1 f
          (m', st.2 || ch)
      | _ => st
    else st
  | .tcall g args =>
    let (m', ch', _) := checkCallArgsUniq borrows g imm uniq .leaf args st
    let selfRetU := (m'.getD f ([], false)).2
    let calleeRetU := (m'.getD g ([], false)).2
    if selfRetU && !calleeRetU then
      let (m'', ch2) := clearRetUniq m' f
      (m'', ch' || ch2)
    else (m', ch')
  | .trap => st

def refineUniqAlts (borrows : BorrowSigs) (f : FunId) (imm uniq : VSet)
    (st : UniqSigs × Bool) : List AAlt → UniqSigs × Bool
  | [] => st
  | .mk _ ab _ :: rest =>
    let st := refineUniqCode borrows f imm uniq st ab
    refineUniqAlts borrows f imm uniq st rest

def refineUniqOpt (borrows : BorrowSigs) (f : FunId) (imm uniq : VSet)
    (st : UniqSigs × Bool) : Option (ACode × VSet) → UniqSigs × Bool
  | none => st
  | some (ac, _) => refineUniqCode borrows f imm uniq st ac
end

def refineUniqPass (F : Fir.Program) (borrows : BorrowSigs) (annotated : Src.NatMap ACode)
    (uniqs : UniqSigs) : UniqSigs × Bool :=
  (List.range F.size).foldl (fun st f =>
    match F.fun? f, annotated.get? f with
    | some fd, some ab =>
      let bs := borrows.getD f []
      let us := (st.1.getD f ([], false)).1
      let initUniq := VSet.ofVars (Ctx.entryUnique (fd.params.map (·.1)) bs us)
      refineUniqCode borrows f .leaf initUniq st ab
    | _, _ => st) (uniqs, false)

def uniqFixLoop (F : Fir.Program) (borrows : BorrowSigs) (annotated : Src.NatMap ACode) :
    Nat → UniqSigs → UniqSigs
  | 0, uniqs => uniqs
  | fuel + 1, uniqs =>
    let (uniqs', changed) := refineUniqPass F borrows annotated uniqs
    if changed then uniqFixLoop F borrows annotated fuel uniqs' else uniqs'

/-- Total fuel-bounded interprocedural `@unique` parameter and return uniqueness inference.
Exported functions never assume `@unique` parameters; `@borrowed` parameters are never `@unique`. -/
def inferUniqs (F : Fir.Program) (borrows : BorrowSigs) (annotated : Src.NatMap ACode) : UniqSigs :=
  let expSet := VSet.ofVars F.exports
  let init : UniqSigs := (List.range F.size).foldl (fun m f =>
    match F.fun? f with
    | none => m
    | some fd =>
      let isExp := expSet.contains f
      let bs := borrows.getD f []
      let us := (List.range fd.params.length).map fun i =>
        if isExp then false else !(bs.getD i false)
      m.insert f (us, true)) .leaf
  uniqFixLoop F borrows annotated 64 init

mutual
/-- Whether `ab` contains a heap `.ctor` of size class `cls` (without entering a `.jp` body). -/
def hasMatchingCtor (cls : Nat) : ACode → Bool
  | .bind _ (.ctor c _) k _ => (Ctx.validReuseCtor c == some cls) || hasMatchingCtor cls k
  | .bind _ _ k _ => hasMatchingCtor cls k
  | .jp _ _ _ _ k _ _ _ => hasMatchingCtor cls k
  | .case _ alts d => hasMatchingCtorAlts cls alts || hasMatchingCtorOpt cls d
  | .jmp .. | .ret .. | .tcall .. | .trap => false

def hasMatchingCtorAlts (cls : Nat) : List AAlt → Bool
  | [] => false
  | .mk _ ab _ :: rest => hasMatchingCtor cls ab || hasMatchingCtorAlts cls rest

def hasMatchingCtorOpt (cls : Nat) : Option (ACode × VSet) → Bool
  | none => false
  | some (ac, _) => hasMatchingCtor cls ac
end

/-- Peel leading `.proj x key j` bindings from `ab` (returning `(projected, rest, liveAfter)`). -/
def peelProjs (x : Var) (key : Key.CtorKey) (arity : Nat) :
    ACode → VSet → List (Var × Nat) × ACode × VSet
  | .bind v (.proj y key' j) k liveK, _ =>
    if y == x && key' == key && j < arity then
      let (more, rest, liveAfter) := peelProjs x key arity k liveK
      ((v, j) :: more, rest, liveAfter)
    else ([], .bind v (.proj y key' j) k liveK, VSet.addVars (VSet.eraseP liveK v) [y])
  | ac, lb => ([], ac, lb)

mutual
def ACode.sz : ACode → Nat
  | .bind _ _ k _ => k.sz + 1
  | .jp _ _ _ b k _ _ _ => b.sz + k.sz + 1
  | .case _ alts d => ACode.altsSz alts + ACode.optSz d + 2
  | _ => 1
def ACode.altsSz : List AAlt → Nat
  | [] => 0
  | .mk _ b _ :: rest => b.sz + ACode.altsSz rest + 1
def ACode.optSz : Option (ACode × VSet) → Nat
  | none => 0
  | some (c, _) => c.sz + 1
end

theorem peelProjs_sz_le (x : Var) (key : Key.CtorKey) (arity : Nat) :
    ∀ (ab : ACode) (lb : VSet), (peelProjs x key arity ab lb).2.1.sz ≤ ab.sz
  | .bind v (.proj y key' j) k liveK, lb => by
    simp only [peelProjs]
    split
    · have ih := peelProjs_sz_le x key arity k liveK
      simpa only [ACode.sz] using Nat.le_trans ih (Nat.le_succ _)
    · exact Nat.le_refl _
  | .bind _ (.arg _) _ _, _ | .bind _ (.ctor _ _) _ _, _ | .bind _ (.call _ _) _ _, _
  | .bind _ (.prim _ _) _ _, _ | .jp .., _ | .jmp .., _ | .case .., _ | .ret _, _
  | .tcall .., _ | .trap, _ => Nat.le_refl _

/-- Build the `Option Var` field list of length `arity` for `reset` from peeled projections,
returning `none` if the same field index has two distinct live projections. -/
def buildResetFields (arity : Nat) (liveAfter : VSet) (projs : List (Var × Nat)) :
    Option (List (Option Var)) :=
  let init : List (Option Var) := List.replicate arity none
  projs.foldlM (fun acc (v, j) =>
    if liveAfter.contains v then
      match acc[j]? with
      | some none => some (acc.set j (some v))
      | _ => none
    else some acc) init

/-- Active reset slots tracked during placement: `(slotId, sizeClass, isGuaranteedUnique)`. -/
abbrev ActiveSlots := List (Nat × Nat × Bool)

def dropSlotsPrefix (slots : ActiveSlots) (k : Code) : Code :=
  slots.foldr (fun (s, _, _) acc => .dropSlot s acc) k

/-- Pick and remove a matching active slot for size class `cls`, preferring statically unique slots. -/
def pickSlot (cls : Nat) (slots : ActiveSlots) : Option ((Nat × Bool) × ActiveSlots) :=
  match slots.find? (fun p => p.2.1 == cls && p.2.2) with
  | some (s, _, u) => some ((s, u), slots.filter (fun p => p.1 != s))
  | none =>
    match slots.find? (fun p => p.2.1 == cls) with
    | some (s, _, u) => some ((s, u), slots.filter (fun p => p.1 != s))
    | none => none

/-- Partition active slots into those still matching a constructor in `ab` vs those to drop now. -/
def splitSlotsFor (ab : ACode) (slots : ActiveSlots) : ActiveSlots × ActiveSlots :=
  slots.partition (fun (_, cls, _) => hasMatchingCtor cls ab)

/-- Wrap peeled `.proj x key j` bindings around `k`. -/
def wrapProjs (x : Var) (key : Key.CtorKey) : List (Var × Nat) → Code → Code
  | [], k => k
  | (v, j) :: rest, k => .bind v (.proj x key j) (wrapProjs x key rest k)

mutual
def placeFbip (ctors : List Lam.CtorInfo) (known : Lam.Known) (borrows : BorrowSigs) (uniqs : UniqSigs)
    (Δ : Src.NatMap VSet) (owned imm pbrw uniq : VSet) (slots : ActiveSlots) (nextSlot : Nat)
    (ac : ACode) : Code × Nat :=
  match ac with
  | .bind x r k liveK =>
    match r with
    | .proj y _ _ =>
      if imm.contains y then
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned (Src.NatSet.insert imm x) pbrw
          (Src.NatSet.insert uniq x) slots nextSlot k
        (.bind x r k', ns)
      else if pbrw.contains y then
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned' := VSet.inter owned liveK
        let uniq' := VSet.inter uniq owned'
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned' imm (Src.NatSet.insert pbrw x) uniq' slots nextSlot k
        (.bind x r (actionPrefix (decs dead) k'), ns)
      else
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let (owned, incs) :=
          if liveK.contains x && !(dead.isEmpty && canBorrowProj x k) then
            (Src.NatSet.insert owned x, [Action.inc x 1])
          else (owned, [])
        let owned' := VSet.inter owned liveK
        let uniq' := VSet.inter uniq owned'
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned' imm pbrw uniq' slots nextSlot k
        (.bind x r (actionPrefix (incs ++ decs dead) k'), ns)
    | .prim op args =>
      let (owned, imm) := applyPrimImm (primImmArgs op args.length) args (owned, imm)
      let imm := Src.NatSet.insert imm x
      let dead := VSet.toSortedVars (VSet.diff owned liveK)
      let owned' := VSet.inter owned liveK
      let uniq' := VSet.inter uniq owned'
      let (k', ns) := placeFbip ctors known borrows uniqs Δ owned' imm pbrw uniq' slots nextSlot k
      (.bind x r (actionPrefix (decs dead) k'), ns)
    | .arg (.var y) =>
      if imm.contains y then
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned (Src.NatSet.insert imm x) pbrw uniq slots nextSlot k
        (.bind x r k', ns)
      else if !owned.contains y && pbrw.contains y then
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned' := VSet.inter owned liveK
        let uniq' := VSet.inter uniq owned'
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned' imm (Src.NatSet.insert pbrw x) uniq' slots nextSlot k
        (.bind x r (actionPrefix (decs dead) k'), ns)
      else
        let movedUniq := uniq.contains y && !liveK.contains y
        let (incs, owned) := consume owned imm liveK [.var y]
        let uniq := VSet.eraseP uniq y
        let (owned, uniq, post) :=
          if liveK.contains x then
            (Src.NatSet.insert owned x, if movedUniq then Src.NatSet.insert uniq x else uniq, [])
          else (owned, uniq, [Action.dec x])
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned imm pbrw (VSet.inter uniq owned) slots nextSlot k
        (actionPrefix incs (.bind x r (actionPrefix post k')), ns)
    | .arg _ =>
      let (k', ns) := placeFbip ctors known borrows uniqs Δ owned (Src.NatSet.insert imm x) pbrw uniq slots nextSlot k
      (.bind x r k', ns)
    | .ctor c args =>
      if c.arity == 0 then
        let (k', ns) := placeFbip ctors known borrows uniqs Δ owned (Src.NatSet.insert imm x) pbrw uniq slots nextSlot k
        (.bind x r k', ns)
      else
        let (incs, owned) := consume owned imm liveK args
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
        let owned := VSet.inter owned liveK
        let uniq := (argVars args).foldl (fun u v => VSet.eraseP u v) uniq
        let uniq := VSet.inter uniq owned
        let (owned, uniq, post) :=
          if liveK.contains x then (Src.NatSet.insert owned x, Src.NatSet.insert uniq x, [])
          else (owned, uniq, [Action.dec x])
        let isNat := known.natZero == some c.key || known.natSucc == some c.key
        match (if isNat then none else Ctx.validReuseCtor c >>= fun cls => pickSlot cls slots) with
        | some ((s, sUniq), slots') =>
          let (k', ns) := placeFbip ctors known borrows uniqs Δ owned imm pbrw uniq slots' nextSlot k
          (actionPrefix (decs dead ++ incs) (.reuse x s c args sUniq (actionPrefix post k')), ns)
        | none =>
          let (k', ns) := placeFbip ctors known borrows uniqs Δ owned imm pbrw uniq slots nextSlot k
          (actionPrefix (decs dead ++ incs) (.bind x r (actionPrefix post k')), ns)
    | .call f args =>
      let bs := borrows.getD f []
      let calleeRetU := (uniqs.getD f ([], false)).2
      let ownedArgs := selectOwnedArgs bs args
      let borrowedArgs := selectBorrowedArgs bs args
      let keepAlive := VSet.union liveK (VSet.ofVars (argVars borrowedArgs))
      let (incs, ownedAfterTake) := consume owned imm keepAlive ownedArgs
      let deadBefore := VSet.toSortedVars (VSet.diff ownedAfterTake keepAlive)
      let ownedAcross := VSet.inter ownedAfterTake keepAlive
      let deadAfter := VSet.toSortedVars (VSet.diff ownedAcross liveK)
      let ownedAfterCall := VSet.inter ownedAcross liveK
      let uniq := (argVars args).foldl (fun u v => VSet.eraseP u v) uniq
      let uniq := VSet.inter uniq ownedAfterCall
      let (ownedFinal, uniqFinal, post) :=
        if liveK.contains x then
          (Src.NatSet.insert ownedAfterCall x,
           if calleeRetU then Src.NatSet.insert uniq x else uniq,
           decs deadAfter)
        else (ownedAfterCall, uniq, Action.dec x :: decs deadAfter)
      let (k', ns) := placeFbip ctors known borrows uniqs Δ ownedFinal imm pbrw uniqFinal slots nextSlot k
      (actionPrefix (decs deadBefore ++ incs) (.bind x r (actionPrefix post k')), ns)
  | .jp j ps rec body k captured liveBody liveK =>
    let captured := captured.filter (fun c => !imm.contains c && !pbrw.contains c)
    let capturedSet := VSet.ofVars captured
    let ownedBody := VSet.addVars capturedSet ps
    let deadBody := VSet.toSortedVars (VSet.diff ownedBody liveBody)
    let ownedBody' := VSet.inter ownedBody liveBody
    let Δbody := if rec then Δ.insert j capturedSet else Δ
    let (bodyInner, ns1) := placeFbip ctors known borrows uniqs Δbody ownedBody' imm pbrw .leaf [] nextSlot body
    let bodyCode := actionPrefix (decs deadBody) bodyInner
    let deadK := VSet.toSortedVars (VSet.diff owned liveK)
    let ownedK := VSet.inter owned liveK
    let uniqK := VSet.inter uniq ownedK
    let (keepSlots, dropSlots) := splitSlotsFor k slots
    let (kInner, ns2) := placeFbip ctors known borrows uniqs (Δ.insert j capturedSet) ownedK imm pbrw uniqK keepSlots ns1 k
    let kCode := dropSlotsPrefix dropSlots (actionPrefix (decs deadK) kInner)
    (.jp j ps captured rec bodyCode kCode, ns2)
  | .jmp j args =>
    let keep := Δ.getD j .leaf
    let (incs, owned) := consume owned imm keep args
    let dead := VSet.toSortedVars (VSet.diff owned keep)
    (dropSlotsPrefix slots (actionPrefix (incs ++ decs dead) (.jmp j args)), nextSlot)
  | .case x alts d =>
    let (alts', ns1) := placeAltsFbip ctors known borrows uniqs Δ owned imm pbrw uniq slots nextSlot x alts
    let (d', ns2) := placeOptFbip ctors known borrows uniqs Δ owned imm pbrw uniq slots ns1 d
    (.case x alts' d', ns2)
  | .ret a =>
    let (incs, owned) := consume owned imm .leaf [a]
    (dropSlotsPrefix slots (actionPrefix (incs ++ decs (VSet.toSortedVars owned)) (.ret a)), nextSlot)
  | .tcall f args =>
    let bs := borrows.getD f []
    let ownedArgs := selectOwnedArgs bs args
    let (incs, owned) := consume owned imm .leaf ownedArgs
    (dropSlotsPrefix slots (actionPrefix (incs ++ decs (VSet.toSortedVars owned)) (.tcall f args)), nextSlot)
  | .trap => (.trap, nextSlot)
termination_by ac.sz
decreasing_by
  all_goals simp_wf
  all_goals simp only [ACode.sz]
  all_goals omega

def placeAltsFbip (ctors : List Lam.CtorInfo) (known : Lam.Known) (borrows : BorrowSigs) (uniqs : UniqSigs)
    (Δ : Src.NatMap VSet) (owned imm pbrw uniq : VSet) (slots : ActiveSlots) (nextSlot : Nat)
    (x : Var) (alts : List AAlt) : List Alt × Nat :=
  match alts with
  | [] => ([], nextSlot)
  | .mk key ab lb :: rest =>
    let (keepSlots, dropSlots) := splitSlotsFor ab slots
    let tryReset : Option (Code × Nat) :=
      if !owned.contains x || imm.contains x || pbrw.contains x ||
          known.natZero == some key || known.natSucc == some key then none
      else match Fir.CtorInfo.ofKey ctors key with
      | none => none
      | some ctor =>
        match Ctx.validReuseCtor ctor with
        | none => none
        | some cls =>
          match _hpeel : peelProjs x key ctor.arity ab lb with
          | (projs, bodyAfter, liveAfter) =>
            if liveAfter.contains x || !hasMatchingCtor cls bodyAfter then none
            else match buildResetFields ctor.arity liveAfter projs with
            | none => none
            | some fields =>
              let deadOther := VSet.toSortedVars (VSet.diff (VSet.eraseP owned x) lb)
              let ownedMid := VSet.inter (VSet.eraseP owned x) lb
              let liveVars := fields.filterMap id
              let ownedAfter := VSet.inter (VSet.addVars ownedMid liveVars) liveAfter
              let deadAfter := VSet.toSortedVars (VSet.diff (VSet.addVars ownedMid liveVars) liveAfter)
              let uniqAfter := VSet.inter (VSet.eraseP uniq x) ownedAfter
              let isU := uniq.contains x
              let slots' := (nextSlot, cls, isU) :: keepSlots
              let (bodyCode, ns1) := placeFbip ctors known borrows uniqs Δ ownedAfter imm pbrw uniqAfter slots' (nextSlot + 1) bodyAfter
              let cont := actionPrefix (decs deadAfter) bodyCode
              some (dropSlotsPrefix dropSlots (actionPrefix (decs deadOther)
                (wrapProjs x key projs (.reset nextSlot x ctor fields isU cont))), ns1)
    let (armCode, ns1) :=
      match tryReset with
      | some r => r
      | none =>
        let dead := VSet.toSortedVars (VSet.diff owned lb)
        let owned' := VSet.inter owned lb
        let uniq' := VSet.inter uniq owned'
        let (inner, ns1) := placeFbip ctors known borrows uniqs Δ owned' imm pbrw uniq' keepSlots nextSlot ab
        (dropSlotsPrefix dropSlots (actionPrefix (decs dead) inner), ns1)
    let (rest', ns2) := placeAltsFbip ctors known borrows uniqs Δ owned imm pbrw uniq slots ns1 x rest
    (.mk key armCode :: rest', ns2)
termination_by ACode.altsSz alts
decreasing_by
  all_goals simp_wf
  all_goals simp only [ACode.altsSz]
  all_goals first
    | omega
    | (have hle := peelProjs_sz_le x key ctor.arity ab lb
       rw [_hpeel] at hle
       dsimp only at hle
       omega)

def placeOptFbip (ctors : List Lam.CtorInfo) (known : Lam.Known) (borrows : BorrowSigs) (uniqs : UniqSigs)
    (Δ : Src.NatMap VSet) (owned imm pbrw uniq : VSet) (slots : ActiveSlots) (nextSlot : Nat)
    (opt : Option (ACode × VSet)) : Option Code × Nat :=
  match opt with
  | none => (none, nextSlot)
  | some (ad, ld) =>
    let (keepSlots, dropSlots) := splitSlotsFor ad slots
    let dead := VSet.toSortedVars (VSet.diff owned ld)
    let owned' := VSet.inter owned ld
    let uniq' := VSet.inter uniq owned'
    let (inner, ns1) := placeFbip ctors known borrows uniqs Δ owned' imm pbrw uniq' keepSlots nextSlot ad
    (some (dropSlotsPrefix dropSlots (actionPrefix (decs dead) inner)), ns1)
termination_by ACode.optSz opt
decreasing_by
  simp_wf
  simp only [ACode.optSz]
  omega
end

mutual
/-- Whether sinking `.reset s` through pure non-releasing bindings and `.case` can land
directly adjacent to a `.reuse _ s` (enabling `fusedResetReuse`/`fusedResetUReuseU`). -/
def canFuseReset (s : Nat) : Code → Bool
  | .reuse _ s' _ _ _ _ => s == s'
  | .bind _ (.ctor _ []) k => canFuseReset s k
  | .bind _ (.arg (.lit _)) k => canFuseReset s k
  | .bind _ (.arg .erased) k => canFuseReset s k
  | .bind _ (.prim _ _) k => canFuseReset s k
  | .case _ alts dflt => canFuseResetAlts s alts || canFuseResetOpt s dflt
  | _ => false

def canFuseResetAlts (s : Nat) : List Alt → Bool
  | [] => false
  | .mk _ b :: rest => canFuseReset s b || canFuseResetAlts s rest

def canFuseResetOpt (s : Nat) : Option Code → Bool
  | none => false
  | some b => canFuseReset s b
end

mutual
/-- Rename reset slot `oldS` to `newS` throughout `Code` so duplicated branch resets keep
distinct SSA slot registers during CFG lowering (`Cfg.Rc.Lower.skeleton`). -/
def renameSlot (oldS newS : Nat) : Code → Code
  | .act a k => .act a (renameSlot oldS newS k)
  | .bind x r k => .bind x r (renameSlot oldS newS k)
  | .reset s x c fs u k =>
    .reset (if s == oldS then newS else s) x c fs u (renameSlot oldS newS k)
  | .reuse x s c args u k =>
    .reuse x (if s == oldS then newS else s) c args u (renameSlot oldS newS k)
  | .dropSlot s k =>
    .dropSlot (if s == oldS then newS else s) (renameSlot oldS newS k)
  | .jp j ps cap rec b k =>
    .jp j ps cap rec (renameSlot oldS newS b) (renameSlot oldS newS k)
  | .case x alts dflt =>
    .case x (renameSlotAlts oldS newS alts) (renameSlotOpt oldS newS dflt)
  | c => c

def renameSlotAlts (oldS newS : Nat) : List Alt → List Alt
  | [] => []
  | .mk key b :: rest => .mk key (renameSlot oldS newS b) :: renameSlotAlts oldS newS rest

def renameSlotOpt (oldS newS : Nat) : Option Code → Option Code
  | none => none
  | some b => some (renameSlot oldS newS b)
end

mutual
/-- Push a single `.reset s x c fs u` past pure non-releasing bindings (`ctor` arity 0,
non-var `arg`, `prim` not referencing `x`) and `.case z` (`z ≠ x`) when doing so lands it
directly adjacent to `.reuse _ s`, assigning fresh SSA slot IDs on `.case` splits so every
branch keeps a distinct CFG slot register. -/
def sinkOneReset (s : Nat) (x : Var) (c : Fir.CtorInfo) (fs : List (Option Var))
    (fVars : VSet) (u : Bool) (code : Code) (ns : Nat) : Code × Nat :=
  match code with
  | .bind y (.ctor c0 []) k =>
    if y != x && !fVars.contains y && canFuseReset s k then
      let (k', ns') := sinkOneReset s x c fs fVars u k ns
      (.bind y (.ctor c0 []) k', ns')
    else (.reset s x c fs u (.bind y (.ctor c0 []) k), ns)
  | .bind y (.arg (.lit l)) k =>
    if y != x && !fVars.contains y && canFuseReset s k then
      let (k', ns') := sinkOneReset s x c fs fVars u k ns
      (.bind y (.arg (.lit l)) k', ns')
    else (.reset s x c fs u (.bind y (.arg (.lit l)) k), ns)
  | .bind y (.arg .erased) k =>
    if y != x && !fVars.contains y && canFuseReset s k then
      let (k', ns') := sinkOneReset s x c fs fVars u k ns
      (.bind y (.arg .erased) k', ns')
    else (.reset s x c fs u (.bind y (.arg .erased) k), ns)
  | .bind y (.prim op args) k =>
    if y != x && !fVars.contains y && !(argVars args).contains x && canFuseReset s k then
      let (k', ns') := sinkOneReset s x c fs fVars u k ns
      (.bind y (.prim op args) k', ns')
    else (.reset s x c fs u (.bind y (.prim op args) k), ns)
  | .case z alts dflt =>
    if z != x && (!alts.isEmpty || dflt.isSome) &&
        (canFuseResetAlts s alts || canFuseResetOpt s dflt) then
      let (alts', ns1) := sinkOneResetAlts s x c fs fVars u alts ns
      let (dflt', ns2) := sinkOneResetOpt s x c fs fVars u dflt ns1
      (.case z alts' dflt', ns2)
    else (.reset s x c fs u (.case z alts dflt), ns)
  | k => (.reset s x c fs u k, ns)

def sinkOneResetAlts (s : Nat) (x : Var) (c : Fir.CtorInfo) (fs : List (Option Var))
    (fVars : VSet) (u : Bool) : List Alt → Nat → List Alt × Nat
  | [], ns => ([], ns)
  | .mk key b :: rest, ns =>
    let s' := ns
    let (b', ns1) := sinkOneReset s x c fs fVars u b (ns + 1)
    let (rest', ns2) := sinkOneResetAlts s x c fs fVars u rest ns1
    (.mk key (renameSlot s s' b') :: rest', ns2)

def sinkOneResetOpt (s : Nat) (x : Var) (c : Fir.CtorInfo) (fs : List (Option Var))
    (fVars : VSet) (u : Bool) : Option Code → Nat → Option Code × Nat
  | none, ns => (none, ns)
  | some b, ns =>
    let s' := ns
    let (b', ns1) := sinkOneReset s x c fs fVars u b (ns + 1)
    (some (renameSlot s s' b'), ns1)
end

mutual
def sinkResetsAux : Code → Nat → Code × Nat
  | .act a k, ns =>
    let (k', ns') := sinkResetsAux k ns
    (.act a k', ns')
  | .bind x r k, ns =>
    let (k', ns') := sinkResetsAux k ns
    (.bind x r k', ns')
  | .reset s x c fs u k, ns =>
    let (k', ns1) := sinkResetsAux k ns
    sinkOneReset s x c fs (VSet.ofVars (fs.filterMap id)) u k' ns1
  | .reuse x s c args u k, ns =>
    let (k', ns') := sinkResetsAux k ns
    (.reuse x s c args u k', ns')
  | .dropSlot s k, ns =>
    let (k', ns') := sinkResetsAux k ns
    (.dropSlot s k', ns')
  | .jp j ps cap rec b k, ns =>
    let (b', ns1) := sinkResetsAux b ns
    let (k', ns2) := sinkResetsAux k ns1
    (.jp j ps cap rec b' k', ns2)
  | .case x alts dflt, ns =>
    let (alts', ns1) := sinkResetsAlts alts ns
    let (dflt', ns2) := sinkResetsOpt dflt ns1
    (.case x alts' dflt', ns2)
  | c, ns => (c, ns)

def sinkResetsAlts : List Alt → Nat → List Alt × Nat
  | [], ns => ([], ns)
  | .mk key b :: rest, ns =>
    let (b', ns1) := sinkResetsAux b ns
    let (rest', ns2) := sinkResetsAlts rest ns1
    (.mk key b' :: rest', ns2)

def sinkResetsOpt : Option Code → Nat → Option Code × Nat
  | none, ns => (none, ns)
  | some b, ns =>
    let (b', ns1) := sinkResetsAux b ns
    (some b', ns1)
end

def sinkResets (c : Code) : Code :=
  (sinkResetsAux c (slotBound c)).1

/-- Place `inc`/`dec`, `@borrowed`, `reset`/`reuse`/`dropSlot`, and static `@unique` on one body. -/
def liveBodyFull (ctors : List Lam.CtorInfo) (known : Lam.Known) (borrows : BorrowSigs) (uniqs : UniqSigs)
    (selfBorrows selfUniqs : List Bool) (params : List Var) (ab : ACode) (lb : VSet) : Code :=
  let owned := VSet.ofVars (Ctx.entryOwned params selfBorrows)
  let pbrw := VSet.ofVars (Ctx.entryBorrowed params selfBorrows)
  let uniq := VSet.ofVars (Ctx.entryUnique params selfBorrows selfUniqs)
  let dead := VSet.toSortedVars (VSet.diff owned lb)
  let owned' := VSet.inter owned lb
  let uniq' := VSet.inter uniq owned'
  sinkResets (actionPrefix (decs dead) (placeFbip ctors known borrows uniqs .leaf owned' .leaf pbrw uniq' [] 0 ab).1)

/-- Full Track A3+A4 ownership producer: liveness + interprocedural `@borrowed` + interprocedural
`@unique` + FBIP `reset`/`reuse` placement. -/
def liveMapFull (F : Fir.Program) : Src.NatMap Code × BorrowSigs × UniqSigs :=
  let borrows := inferBorrows F
  let annotatedPairs : Src.NatMap (ACode × VSet) := F.funs.map fun fd => annotate .leaf fd.body
  let annotatedBodies : Src.NatMap ACode := annotatedPairs.map (·.1)
  let uniqs := inferUniqs F borrows annotatedBodies
  let bodies := mapWithKeyAux (fun f fd =>
    let (ab, lb) := (annotatedPairs.get? f).getD (annotate .leaf fd.body)
    let bs := borrows.getD f []
    let us := (uniqs.getD f ([], false)).1
    liveBodyFull F.ctors F.known borrows uniqs bs us (fd.params.map (·.1)) ab lb) 0 1 F.funs
  (bodies, borrows, uniqs)

/-- Place `inc`/`dec` on every function in a FIR program by liveness + interprocedural borrows. -/
def liveMapWith (F : Fir.Program) : Src.NatMap Code × BorrowSigs :=
  let borrows := inferBorrows F
  let bodies := mapWithKeyAux (fun f fd =>
    liveBodyWith borrows (borrows.getD f []) (fd.params.map (·.1)) fd.body) 0 1 F.funs
  (bodies, borrows)

/-- Place `inc`/`dec` on one FIR function body by liveness (without borrowed parameters). -/
def liveBody (params : List Var) (body : Fir.Code) : Code :=
  let (ab, lb) := annotate .leaf body
  let owned := VSet.ofVars params
  let dead := VSet.toSortedVars (VSet.diff owned lb)
  let owned' := VSet.inter owned lb
  actionPrefix (decs dead) (place .leaf owned' .leaf ab)

/-- Place `inc`/`dec` on every function in a FIR program by liveness. -/
def liveMap (F : Fir.Program) : Src.NatMap Code :=
  F.funs.map fun fd => liveBody (fd.params.map (·.1)) fd.body

end IxCC.Own.Plain.Live
