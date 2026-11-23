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
/-- Whether a `Fir.Code` body contains any heap-allocating constructor (`c.arity > 0`). -/
def hasAllocCode : Fir.Code → Bool
  | .bind _ (.ctor c _) k => (c.arity > 0) || hasAllocCode k
  | .bind _ _ k => hasAllocCode k
  | .jp _ _ _ b k => hasAllocCode b || hasAllocCode k
  | .case _ alts d => hasAllocAlts alts || hasAllocOpt d
  | .jmp .. | .ret .. | .tcall .. | .trap => false
def hasAllocAlts : List Fir.Alt → Bool
  | [] => false
  | .mk _ b :: rest => hasAllocCode b || hasAllocAlts rest
def hasAllocOpt : Option Fir.Code → Bool
  | none => false
  | some c => hasAllocCode c
end

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
allocating-function scrutiny (kept owned for FBIP reuse), or non-caller-backed tail calls. -/
def refineBorrowCode (f : FunId) (allocs : Bool) (imm direct : VSet) (pbrwSrc : Src.NatMap Nat)
    (st : BorrowSigs × Bool) : Fir.Code → BorrowSigs × Bool
  | .bind x r k =>
    match r with
    | .arg (.var y) =>
      if imm.contains y then
        refineBorrowCode f allocs (Src.NatSet.insert imm x) direct pbrwSrc st k
      else
        let pbrwSrc' := match pbrwSrc.get? y with
          | some i => pbrwSrc.insert x i
          | none => pbrwSrc
        let direct' := if direct.contains y then Src.NatSet.insert direct x else direct
        refineBorrowCode f allocs imm direct' pbrwSrc' st k
    | .arg _ =>
      refineBorrowCode f allocs (Src.NatSet.insert imm x) direct pbrwSrc st k
    | .ctor c args =>
      if c.arity == 0 then
        refineBorrowCode f allocs (Src.NatSet.insert imm x) direct pbrwSrc st k
      else
        let st := clearArgsBorrows f pbrwSrc false direct args st
        refineBorrowCode f allocs imm direct pbrwSrc st k
    | .call g args =>
      let st := checkCallArgsBorrow f g false imm direct pbrwSrc args st
      refineBorrowCode f allocs imm direct pbrwSrc st k
    | .proj y _ _ =>
      if imm.contains y then
        refineBorrowCode f allocs (Src.NatSet.insert imm x) direct pbrwSrc st k
      else
        let pbrwSrc' := match pbrwSrc.get? y with
          | some i => pbrwSrc.insert x i
          | none => pbrwSrc
        refineBorrowCode f allocs imm direct pbrwSrc' st k
    | .prim op args =>
      let imm' := Src.NatSet.insert (addPrimImm (primImmArgs op args.length) args imm) x
      refineBorrowCode f allocs imm' direct pbrwSrc st k
  | .jp _ _ _ body k =>
    let st := refineBorrowCode f allocs imm direct pbrwSrc st body
    refineBorrowCode f allocs imm direct pbrwSrc st k
  | .jmp _ args =>
    clearArgsBorrows f pbrwSrc false direct args st
  | .case x alts d =>
    let st := if allocs then clearVarBorrow f pbrwSrc true direct x st else st
    let st := refineBorrowAlts f allocs imm direct pbrwSrc st alts
    refineBorrowOpt f allocs imm direct pbrwSrc st d
  | .ret a =>
    clearArgsBorrows f pbrwSrc false direct [a] st
  | .tcall g args =>
    checkCallArgsBorrow f g true imm direct pbrwSrc args st
  | .trap => st

def refineBorrowAlts (f : FunId) (allocs : Bool) (imm direct : VSet) (pbrwSrc : Src.NatMap Nat)
    (st : BorrowSigs × Bool) : List Fir.Alt → BorrowSigs × Bool
  | [] => st
  | .mk _ body :: rest =>
    let st := refineBorrowCode f allocs imm direct pbrwSrc st body
    refineBorrowAlts f allocs imm direct pbrwSrc st rest

def refineBorrowOpt (f : FunId) (allocs : Bool) (imm direct : VSet) (pbrwSrc : Src.NatMap Nat)
    (st : BorrowSigs × Bool) : Option Fir.Code → BorrowSigs × Bool
  | none => st
  | some c => refineBorrowCode f allocs imm direct pbrwSrc st c
end

/-- One full program sweep of interprocedural borrow refinement. -/
def refineBorrowPass (F : Fir.Program) (allocs : Src.NatMap Bool) (borrows : BorrowSigs) :
    BorrowSigs × Bool :=
  (List.range F.size).foldl (fun st f =>
    match F.fun? f with
    | none => st
    | some fd =>
      let bs := st.1.getD f []
      let (pbrwSrc, direct) := (fd.params.zipIdx).foldl (fun (pm, dm) ((p, _), i) =>
        if bs.getD i false then (pm.insert p i, Src.NatSet.insert dm p) else (pm, dm)) (.leaf, .leaf)
      refineBorrowCode f (allocs.getD f false) .leaf direct pbrwSrc st fd.body) (borrows, false)

def borrowFixLoop (F : Fir.Program) (allocs : Src.NatMap Bool) : Nat → BorrowSigs → BorrowSigs
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
  let allocs : Src.NatMap Bool := (List.range F.size).foldl (fun m f =>
    match F.fun? f with
    | none => m
    | some fd => m.insert f (hasAllocCode fd.body)) .leaf
  let fuel := 64
  borrowFixLoop F allocs fuel init

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
        let (owned, incs) :=
          if liveK.contains x then (Src.NatSet.insert owned x, [Action.inc x 1])
          else (owned, [])
        let dead := VSet.toSortedVars (VSet.diff owned liveK)
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
