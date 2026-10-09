import Ix.Ixon.BlockOrder.Theorems
import Tests.Ix.Kernel.Projection

/-! Canonical block order (`Ixon.BlockOrder`): canonical classes,
accepted and refused member orders, and the refinement budget, checked at
elaboration. -/

open Ix.Kernel
open Ixon.BlockOrder
open Tests.Ix.Kernel.IxonFixtures (address)

namespace Tests.Ix.Kernel.BlockOrder

local instance [BEq α] : BEq (Except Error α) where
  beq
    | .ok x, .ok y => x == y
    | .error x, .error y => decide (x = y)
    | _, _ => false

def owner : Address := address 42

def defn (value : Ixon.Expr) (typ : Ixon.Expr := .sort 0) : Ixon.MutConst :=
  .defn ⟨.defn, .safe, 0, typ, value⟩

def indc (params : UInt64) (ctors : Array Ixon.Constructor := #[]) : Ixon.MutConst :=
  .indc ⟨false, 0, params, 0, .sort 0, ctors⟩

def record (members : Array Ixon.MutConst) : Ixon.Constant :=
  ⟨.muts members, #[], #[], #[.zero, .succ .zero, .var 0]⟩

def classes (source : Ixon.Constant) (blobs : List (Address × ByteArray) := [])
    (limits : Limits := {}) : Except Error Classes := do
  canonicalClasses limits (← prepare owner source blobs)

def accepts (source : Ixon.Constant) (blobs : List (Address × ByteArray) := []) (limits : Limits := {}) : Bool :=
  (checkBlock limits owner source blobs).isOk

def compareIn (source : Ixon.Constant) (left right : Ixon.Expr)
    (blobs : List (Address × ByteArray) := []) (partition : Classes := []) (fuel : Nat := 32) : Except Error Ordering := do
  let block ← prepare owner source blobs
  let ctx ← localContext block partition
  compareRoot block ctx fuel left right

def simple : Ixon.Constant := record #[indc 0, indc 1, indc 2]
def reversed : Ixon.Constant := record #[indc 2, indc 1, indc 0]
def duplicate : Ixon.Constant := record #[indc 0, indc 0]

#guard classes simple == .ok [[0], [1], [2]]
#guard classes reversed == .ok [[2], [1], [0]]
#guard accepts simple
#guard !accepts reversed
#guard !accepts duplicate
#guard accepts (record #[])
#guard accepts (record #[indc 0])
#guard classes simple [] ⟨32, 0⟩ == .error (.exhausted .refinement)

-- Sorting has to refine a tentative equivalence class before distinguishing
-- the two recursive references; input positions cannot authorize the order.
def weak : Ixon.Constant := record #[defn (.var 0), defn (.recur 0 #[]), defn (.recur 2 #[])]
def weakPermuted : Ixon.Constant := record #[defn (.recur 0 #[]), defn (.recur 2 #[]), defn (.var 0)]
def alphaSelf : Ixon.Constant := record #[defn (.recur 0 #[]), defn (.recur 1 #[])]
def alphaCycle : Ixon.Constant := record #[defn (.recur 1 #[]), defn (.recur 0 #[])]

#guard classes weak == .ok [[0], [1], [2]]
#guard classes weakPermuted == .ok [[2], [1], [0]]
#guard accepts weak
#guard !accepts weakPermuted
#guard !accepts alphaSelf
#guard !accepts alphaCycle
#guard classes weak [] ⟨32, 2⟩ == .error (.exhausted .refinement)
#guard classes weak [] ⟨32, 3⟩ == .ok [[0], [1], [2]]
#guard compareIn simple (.var 0) (.var 0) (fuel := 0) == .error (.exhausted .comparison)

-- The old Lean comparator ordered by length before comparing elements.
-- The Rust comparator, and this path, compare unequal vectors lexically.
def external : Ixon.Constant := { record #[] with refs := #[address 1, address 2] }
#guard compareIn external (.ref 0 #[1]) (.ref 0 #[0, 0]) == .ok .gt
#guard compareIn external (.ref 0 #[0]) (.ref 0 #[0, 0]) == .ok .lt
#guard compareIn external (.ref 0 #[]) (.ref 1 #[]) == .ok .lt
#guard compareIn external (.ref 1 #[0]) (.ref 0 #[1]) == .ok .lt

-- Host ingress simplifies levels before canonical comparison.
def unreduced : Ixon.Constant := { record #[] with
  univs := #[.max .zero (.var 0), .var 0, .imax (.succ .zero) (.var 0)] }
#guard compareIn unreduced (.sort 0) (.sort 1) == .ok .eq
#guard compareIn unreduced (.sort 2) (.sort 1) == .ok .eq

def shared : Ixon.Constant := { record #[] with sharing := #[.var 3, .share 0] }
def cyclic : Ixon.Constant := { record #[] with sharing := #[.share 0] }
def forward : Ixon.Constant := { record #[] with sharing := #[.share 1, .var 3] }
#guard compareIn shared (.share 1) (.var 3) == .ok .eq
#guard compareIn shared (.share 1) (.share 1) == .ok .eq
#guard compareIn shared (.share 1) (.share 1) (fuel := 4) == .error (.exhausted .comparison)
#guard compareIn cyclic (.share 0) (.var 3) ==
  .error (.malformed "sharing reference is not earlier than its use")
#guard compareIn forward (.share 0) (.var 3) ==
  .error (.malformed "sharing reference is not earlier than its use")
#guard compareIn external (.sort 9) (.sort 0) == .error (.malformed "universe index outside table")
#guard compareIn external (.ref 9 #[]) (.ref 0 #[]) == .error (.malformed "reference index outside table")
#guard compareIn external (.recur 0 #[]) (.ref 0 #[]) == .error (.malformed "member index outside block")

-- Literal order is independent of the spelling/address of the backing blob.
def blobs : List (Address × ByteArray) := [(address 1, ⟨#[0, 1]⟩), (address 2, ⟨#[255]⟩)]
#guard compareIn external (.nat 0) (.nat 1) blobs == .ok .gt
#guard compareIn external (.str 0) (.str 1)
  [(address 1, "z".toUTF8), (address 2, "a".toUTF8)] == .ok .gt
#guard compareIn external (.str 0) (.str 1) blobs == .error (.malformed "literal is not UTF-8")

-- Ref and recur denote the same physical key; projection heads use the
-- local constructor offsets. Unequal external alias keys stay unequal.
def localAliases : Ixon.Constant :=
  { weak with refs := #[Ixon.Projection.address ⟨.dPrj ⟨1, owner⟩, #[], #[], #[]⟩, address 1] }
#guard compareIn localAliases (.ref 0 #[]) (.recur 1 #[]) [] [[0], [1], [2]] == .ok .eq
#guard compareIn localAliases (.recur 1 #[]) (.ref 1 #[]) [] [[0], [1], [2]] == .ok .lt
#guard compareIn localAliases (.prj 0 0 (.var 0)) (.prj 1 0 (.var 0)) [] [[0], [1], [2]] == .ok .lt

def ctor (index fields : UInt64) : Ixon.Constructor := ⟨false, 0, index, 0, fields, .sort 0⟩
def ctorBlock : Ixon.Constant := record #[indc 0 #[ctor 0 0, ctor 1 0], indc 0 #[ctor 0 1], indc 1 #[ctor 0 0]]
def ctorContext : Except Error (List (Option Nat)) := do
  let block ← prepare owner ctorBlock []
  let ctx ← localContext block [[0, 1], [2]]
  let keys := block.entries.toList.flatMap fun e => e.address :: e.constructors
  return keys.map (Ingress.lookup ctx)
#guard ctorContext == .ok [some 0, some 2, some 3, some 0, some 2, some 1, some 4]

-- Stable sorting and equal-class grouping retain all members, including ties.
#guard sortM (fun x y => pure (compare (x / 10) (y / 10))) [21, 10, 22, 11, 0] ==
  .ok [0, 10, 11, 21, 22]
#guard groupSorted (fun x y => pure (compare (x / 10) (y / 10))) [0, 10, 11, 21, 22] ==
  .ok [[0], [10, 11], [21, 22]]

-- A block of recursors is checked in motive order, not structurally: member
-- `j` must eliminate motive `j` (the head of its result, as the reader reads
-- it) and declare one motive per member. `motive j` is a recursor of a block
-- with `motives` motives (no parameters, minors or indices) whose type ends in
-- motive `j`; its structural order is the reverse of its motive order, as for
-- the compiler's `Rose.rec`/`Rose.rec_1` block.
def motive (j : Nat) (motives : UInt64 := 2) : Ixon.MutConst :=
  let binder (body : Ixon.Expr) : Ixon.Expr := .all .many .shared (.sort 0) body
  let depth := motives.toNat + 1
  .recr ⟨false, false, 0, 0, 0, motives, 0,
    (List.range depth).foldl (fun body _ => binder body) (.var (UInt64.ofNat (depth - 1 - j))), #[]⟩

def recordCheck (source : Ixon.Constant) : Except Error Unit := checkRecord {} [] owner source

def motiveOrdered : Ixon.Constant := record #[motive 0, motive 1]
def motiveSwapped : Ixon.Constant := record #[motive 1, motive 0]

#guard recursorMotive motiveOrdered (match motive 1 with | .recr r => r | _ => default) == some 1
-- structurally the motive-ordered block is out of order, and the swapped one in order
#guard !accepts motiveOrdered
#guard accepts motiveSwapped
#guard recordCheck motiveOrdered == .ok ()
#guard recordCheck motiveSwapped == .error (.motiveOrder owner 0 (some 1))
#guard recordCheck (record #[motive 0 3, motive 1 3, motive 2 3]) == .ok ()
#guard recordCheck (record #[motive 0 3, motive 2 3, motive 1 3]) == .error (.motiveOrder owner 1 (some 2))
-- a repeated motive, a missing recursor, a motive count that is not the block's
#guard recordCheck (record #[motive 0, motive 0]) == .error (.motiveOrder owner 1 (some 0))
#guard recordCheck (record #[motive 0]) == .error (.motiveOrder owner 0 (some 0))
#guard recordCheck (record #[motive 0 1]) == .ok ()
-- a type whose result is not a motive
#guard recordCheck (record #[.recr ⟨false, false, 0, 0, 0, 1, 0, .sort 0, #[]⟩]) ==
  .error (.motiveOrder owner 0 none)
-- inductive, definition and mixed blocks keep the structural order
#guard recordCheck simple == .ok ()
#guard recordCheck reversed == .error (.nonCanonical owner [[2], [1], [0]])
#guard (recordCheck (record #[motive 0, indc 0])).isOk == accepts (record #[motive 0, indc 0])
#guard (recordCheck (record #[indc 0, motive 0])).isOk == accepts (record #[indc 0, motive 0])
#guard checkConstants {} [] [(owner, motiveOrdered), (owner, simple)] == .ok ()
#guard checkConstants {} [] [(owner, simple), (owner, motiveSwapped)] ==
  .error (.motiveOrder owner 0 (some 1))
-- through the bytes: the motive-ordered block passes the order stage (and the
-- checker then declines recursors without their inductive block); the swapped
-- one stops at the order stage
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, motiveOrdered)]) [] with
  | .error e@(.checker _) => e.outcome == .declined
  | _ => false
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, motiveSwapped)]) [] with
  | .error e@(.order (.motiveOrder _ 0 (some 1))) => e.outcome == .rejected
  | _ => false

-- The certified entry with canonical block order admits the separately
-- stored family/recursor fixture and derives its model through the same
-- checker success.
def byteAccepts : Bool := (checkBytes 16 ByteAdmission.limits {}
  (Projection.encode Projection.separatedInput) []).isOk
#guard byteAccepts

#guard match checkBytes 16 ByteAdmission.limits {}
    (Projection.encode [(owner, reversed)]) [] with
  | .error e@(.order (.nonCanonical _ _)) => e.outcome == .rejected
  | _ => false
#guard match checkBytes 16 ByteAdmission.limits ⟨32, 2⟩
    (Projection.encode [(owner, weak)]) [] with
  | .error e@(.order (.exhausted .refinement)) => e.outcome == .declined
  | _ => false

-- The classification of every order failure (`Error.outcome`): bounds
-- decline; a malformed, non-canonical or motive-misordered block rejects;
-- reconstruction and the byte stage as their own classifiers.
#guard (Error.exhausted .comparison).outcome == .declined
#guard (Error.malformed "member index outside block").outcome == .rejected
#guard (Error.nonCanonical owner [[1], [0]]).outcome == .rejected
#guard (Error.motiveOrder owner 0 none).outcome == .rejected
#guard (Error.projection (.ownerWidth owner)).outcome == .rejected
#guard (Error.projection .limit).outcome == .declined
#guard (Error.admission (.decode 0 owner "")).outcome == .rejected
#guard (Error.admission (.limit .totalBytes)).outcome == .declined

/-! ## A `let`'s nondependency bit is a key

`ndLet b` is `let a : Type := Prop; a` (`b = false`) or the same `have`
(`b = true`) over `record`'s universe table (`.sort 0` is `Prop`, `.sort 1`
is `Type`). The arm compares the type, the value, the body, then the bit
(`false < true`) (`compareExpr_letE`). -/

def ndLet (nonDep : Bool) (body : Ixon.Expr := .var 0) : Ixon.Expr :=
  .letE (.lean nonDep) (.sort 1) (.sort 0) body

-- the bit decides when the type, the value and the body are equal
#guard compareIn simple (ndLet false) (ndLet true) == .ok .lt
#guard compareIn simple (ndLet true) (ndLet false) == .ok .gt
#guard compareIn simple (ndLet true) (ndLet true) == .ok .eq
-- the type, the value and the body each decide before the bit
#guard compareIn simple (.letE (.lean true) (.sort 0) (.sort 0) (.var 0)) (ndLet false) == .ok .lt
#guard compareIn simple (.letE (.lean false) (.sort 1) (.sort 1) (.var 0)) (ndLet true) == .ok .gt
#guard compareIn simple (ndLet false (.var 1)) (ndLet true (.var 0)) == .ok .gt
#guard compareIn simple (ndLet true (.var 0)) (ndLet false (.var 1)) == .ok .lt
-- the body is compared whatever the bits, so a body that fails (`.sort 9` is
-- outside the universe table) fails the comparison with equal or unequal bits
#guard compareIn simple (ndLet false (.sort 9)) (ndLet true (.sort 9)) ==
  .error (.malformed "universe index outside table")
#guard compareIn simple (ndLet false (.sort 9)) (ndLet false (.sort 9)) ==
  .error (.malformed "universe index outside table")
-- under a binder and an application, as anywhere in a member
#guard compareIn simple (.app (.var 0) (ndLet true)) (.app (.var 0) (ndLet false)) == .ok .gt
#guard compareIn simple (.all .many .shared (ndLet false) (.var 0))
  (.all .many .shared (ndLet true) (.var 0)) == .ok .lt
-- a `let`'s kind and binder contract are not keys
#guard compareIn simple (.letE (.borrow false) (.sort 1) (.sort 0) (.var 0)) (ndLet false) == .ok .eq

/-- `e` with every recursive reference `.recur i` renumbered to `.recur (σ i)`. -/
def ndRelabel (σ : UInt64 → UInt64) : Ixon.Expr → Ixon.Expr
  | .recur i us => .recur (σ i) us
  | .app f a => .app (ndRelabel σ f) (ndRelabel σ a)
  | .lam c t b => .lam c (ndRelabel σ t) (ndRelabel σ b)
  | .all c r t b => .all c r (ndRelabel σ t) (ndRelabel σ b)
  | .letE c t v b => .letE c (ndRelabel σ t) (ndRelabel σ v) (ndRelabel σ b)
  | .prj t i v => .prj t i (ndRelabel σ v)
  | e => e

def ndRelabelMember (σ : UInt64 → UInt64) : Ixon.MutConst → Ixon.MutConst
  | .defn d => .defn { d with typ := ndRelabel σ d.typ, value := ndRelabel σ d.value }
  | .indc i => .indc { i with
      typ := ndRelabel σ i.typ
      ctors := i.ctors.map fun c => { c with typ := ndRelabel σ c.typ } }
  | .recr r => .recr { r with
      typ := ndRelabel σ r.typ
      rules := r.rules.map fun x => { x with rhs := ndRelabel σ x.rhs } }

/-- A block rearranged: position `k` holds member `order[k]`, and recursive
references follow their members to the new positions. -/
def ndArrange (source : Ixon.Constant) (order : List Nat) : Ixon.Constant :=
  match source.info with
  | .muts members =>
    let σ (i : UInt64) : UInt64 := UInt64.ofNat (order.idxOf i.toNat)
    { source with info := .muts (order.toArray.map fun i => ndRelabelMember σ members[i]!) }
  | _ => source

/-- The bytes of a block put in its canonical order (its classes flattened). -/
def ndCanonicalBytes (source : Ixon.Constant) : Except Error (Array UInt8) := do
  return (Ixon.serConstant (ndArrange source (← classes source).flatten)).data

-- Two definitions that differ only in the bit: two classes in either listing
-- order, the same canonical bytes; only the canonical listing is accepted, the
-- other is refused as non-canonical (a reject)
def ndDefn (nonDep : Bool) : Ixon.MutConst := defn (ndLet nonDep) (.sort 1)
def letHave : Ixon.Constant := record #[ndDefn false, ndDefn true]
def haveLet : Ixon.Constant := record #[ndDefn true, ndDefn false]

#guard classes letHave == .ok [[0], [1]]
#guard classes haveLet == .ok [[1], [0]]
#guard accepts letHave
#guard !accepts haveLet
#guard checkBlock {} owner haveLet [] == .error (.nonCanonical owner [[1], [0]])
#guard ndCanonicalBytes letHave == .ok (Ixon.serConstant letHave).data
#guard ndCanonicalBytes haveLet == ndCanonicalBytes letHave
#guard accepts (ndArrange haveLet [1, 0])

/-- One class holding both members of a two-member block (within a class,
members keep the seed's address order). -/
def ndOneClass : Classes → Bool
  | [members] => members.length == 2 && members.contains 0 && members.contains 1
  | _ => false

-- The same-bit neighbour (the binder renamed: Ixon stores no names, so these
-- are the same bytes) is one class: stored uncollapsed it is refused, stored
-- collapsed (one member) it is accepted
def letLet : Ixon.Constant := record #[ndDefn false, ndDefn false]
#guard match classes letLet with | .ok c => ndOneClass c | .error _ => false
#guard match checkBlock {} owner letLet [] with
  | .error (.nonCanonical o c) => o == owner && ndOneClass c
  | _ => false
#guard accepts (record #[ndDefn false])

-- The census's reproducer, a mutual inductive block: `Left.mk : (let a : Type
-- := Prop; a) → Right → Left` and `Right.mk`, the same with `have`, `→ Left →
-- Right`. `ndMember b self other` is the member at `self` whose other member
-- is at `other`.
def ndMember (nonDep : Bool) (self other : UInt64) : Ixon.MutConst :=
  .indc ⟨false, 0, 0, 0, .sort 1, #[⟨false, 0, 0, 0, 2,
    .all .many .shared (ndLet nonDep) (.all .many .shared (.recur other #[]) (.recur self #[]))⟩]⟩
def leftRight : Ixon.Constant := record #[ndMember false 0 1, ndMember true 1 0]
def rightLeft : Ixon.Constant := record #[ndMember true 0 1, ndMember false 1 0]

#guard classes leftRight == .ok [[0], [1]]
#guard classes rightLeft == .ok [[1], [0]]
#guard accepts leftRight
#guard checkBlock {} owner rightLeft [] == .error (.nonCanonical owner [[1], [0]])
#guard ndCanonicalBytes leftRight == .ok (Ixon.serConstant leftRight).data
#guard ndCanonicalBytes rightLeft == ndCanonicalBytes leftRight
#guard accepts (ndArrange rightLeft [1, 0])
-- with equal bits the two members are one class (the recursive references are
-- tentatively equal), so the uncollapsed block is refused
#guard match classes (record #[ndMember false 0 1, ndMember false 1 0]) with
  | .ok c => ndOneClass c
  | .error _ => false
#guard !accepts (record #[ndMember false 0 1, ndMember false 1 0])
-- The order check sees the stored members, not the names a member stands for:
-- a block that collapses the pair into one member (what a comparator blind to
-- the bit made the compiler store, with either representative) is a canonical
-- singleton, accepted whichever bit it kept. Not collapsing them is the
-- compiler's obligation, under the same key.
#guard accepts (record #[ndMember false 0 0])
#guard accepts (record #[ndMember true 0 0])

-- Through the bytes: the non-canonical listing stops at the order stage as a
-- reject; the canonical one passes it (whatever the checker then says)
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, rightLeft)]) [] with
  | .error e@(.order (.nonCanonical _ [[1], [0]])) => e.outcome == .rejected
  | _ => false
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, leftRight)]) [] with
  | .error (.order _) => false
  | _ => true
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, haveLet)]) [] with
  | .error e@(.order (.nonCanonical _ [[1], [0]])) => e.outcome == .rejected
  | _ => false
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, letHave)]) [] with
  | .error (.order _) => false
  | _ => true

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : checkBytes 16 ByteAdmission.limits {}
      (Projection.encode Projection.separatedInput) [] = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V h

end Tests.Ix.Kernel.BlockOrder
