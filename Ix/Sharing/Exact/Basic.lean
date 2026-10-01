/-
  Exact minimum sharing (W1): shared vocabulary.

  This file fixes the pieces every other part of the exact optimizer uses:

  * exact serializer lengths for the Ixon integer headers (`tag0Size`,
    `tag4Size`) and for complete expressions (`exprSize`), mirroring
    `Ixon.putTag0`, `Ixon.putTag4` and `Ixon.putExpr` byte for byte;
  * the structural node alphabet (`Head`, `Node`) and the §3.2 key order;
  * unsigned byte-lexicographic comparison;
  * errors, resource limits and deterministic work counters.

  Everything is pure Ixon data. Costs are `Nat`; values that must be written
  as a `UInt64` are checked against `2^64` before conversion.
-/
module

public import Ix.Ixon
public import Std.Data.HashMap

public section

namespace Ix.Sharing.Exact

open Ixon

/-! ## Unsigned integer widths -/

/-- Number of bytes in the minimal little-endian representation of `n`
(`0 ↦ 0`). Below `2^64` it equals `Ixon.u64ByteCount`. -/
def natByteCount (n : Nat) : Nat :=
  if h : n = 0 then 0 else natByteCount (n / 256) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Exact byte length of `Ixon.putTag0 ⟨n⟩`, for `n < 2^64`. -/
def tag0Size (n : Nat) : Nat := if n < 128 then 1 else 1 + natByteCount n

/-- Exact byte length of `Ixon.putTag4 ⟨flag, n⟩`, for `n < 2^64`
(independent of the flag). -/
def tag4Size (n : Nat) : Nat := if n < 8 then 1 else 1 + natByteCount n

/-- Width in bytes of `Share(idx)`: one byte for indices `0..7`, then one
header byte plus the minimal little-endian index bytes. -/
def shareWidth (idx : Nat) : Nat := tag4Size idx

/-- Values written through a `UInt64` wire field must be below this bound. -/
def wordBound : Nat := UInt64.size

/-- `f` applied to the state at `k, k + 1, …, k + i - 1` in order (a
tail-recursive counted loop). -/
@[specialize] def foldRange {σ : Type} (f : σ → Nat → σ) : Nat → Nat → σ → σ
  | _, 0, st => st
  | k, i + 1, st => foldRange f (k + 1) i (f st k)


/-! ## Exact expression length -/

/-- Size facts about one expression, computed bottom-up. `full` is the
standalone serialized length. For a telescope family `appCont` (resp.
`lamCont`, `allCont`) is `(n, b)`: if the expression is a node of that
family, `n` is the number of nodes in its maximal same-family spine and `b`
the spine's bytes excluding the one Tag4 header; otherwise `(0, full)`. -/
structure SizeInfo where
  full : Nat
  appCont : Nat × Nat
  lamCont : Nat × Nat
  allCont : Nat × Nat
  deriving Repr, Inhabited

/-- Size facts of a node that continues no telescope. -/
def SizeInfo.plain (n : Nat) : SizeInfo := ⟨n, (0, n), (0, n), (0, n)⟩

/-- Sum of the `Tag0` lengths of universe indices. -/
def univIdxsSize (us : Array UInt64) : Nat :=
  us.foldl (fun acc u => acc + tag0Size u.toNat) 0

/-- Size facts of an Ixon expression (which may contain `Share` leaves), with
`Share(i)` priced `shareCost i`. Structurally recursive; mirrors the
maximal-telescope rule of `putExpr`. -/
def sizeInfoWith (shareCost : Nat → Nat) : Ixon.Expr → SizeInfo
  | .sort i => .plain (tag4Size i.toNat)
  | .var i => .plain (tag4Size i.toNat)
  | .ref r us => .plain (tag4Size us.size + tag0Size r.toNat + univIdxsSize us)
  | .recur r us => .plain (tag4Size us.size + tag0Size r.toNat + univIdxsSize us)
  | .prj t f v => .plain (tag4Size f.toNat + tag0Size t.toNat + (sizeInfoWith shareCost v).full)
  | .str i => .plain (tag4Size i.toNat)
  | .nat i => .plain (tag4Size i.toNat)
  | .app f a =>
    let (n, b) := (sizeInfoWith shareCost f).appCont
    let n' := n + 1
    let b' := b + (sizeInfoWith shareCost a).full
    let full := tag4Size n' + b'
    ⟨full, (n', b'), (0, full), (0, full)⟩
  | .lam _ ty body =>
    let (n, b) := (sizeInfoWith shareCost body).lamCont
    let n' := n + 1
    let b' := 1 + (sizeInfoWith shareCost ty).full + b
    let full := tag4Size n' + b'
    ⟨full, (0, full), (n', b'), (0, full)⟩
  | .all _ _ ty body =>
    let (n, b) := (sizeInfoWith shareCost body).allCont
    let n' := n + 1
    let b' := 1 + (sizeInfoWith shareCost ty).full + b
    let full := tag4Size n' + b'
    ⟨full, (0, full), (0, full), (n', b')⟩
  | .letE c ty v body =>
    .plain (tag4Size c.flags.toNat + 1 + (sizeInfoWith shareCost ty).full + (sizeInfoWith shareCost v).full +
      (sizeInfoWith shareCost body).full)
  | .share i => .plain (shareCost i.toNat)

/-- Size facts with the real `Share` widths. -/
def sizeInfo : Ixon.Expr → SizeInfo := sizeInfoWith tag4Size

/-- Exact byte length of `Ixon.runPut (Ixon.putExpr e)` whenever every
telescope count and payload is below `2^64` (the codec `wireWF` domain). -/
def exprSize (e : Ixon.Expr) : Nat := (sizeInfo e).full

/-- Sum of `exprSize` over an array. -/
def exprsSize (es : Array Ixon.Expr) : Nat := es.foldl (fun acc e => acc + exprSize e) 0

/-! ## Byte and vector order -/

/-- Unsigned lexicographic comparison of byte strings; a proper prefix sorts
first (core `List.compareLex` on the bytes, a lawful total order). -/
def compareBytes (a b : ByteArray) : Ordering :=
  List.compareLex compare a.data.toList b.data.toList

/-- Lexicographic comparison of natural-number vectors, numeric on entries; a
proper prefix sorts first (core `List.compareLex`, a lawful total order). -/
def lexCompare (a b : List Nat) : Ordering := List.compareLex compare a b

/-- `Array` form of `lexCompare`. -/
def compareNatArray (a b : Array Nat) : Ordering := lexCompare a.toList b.toList

/-! ## Structural node alphabet (§3.2) -/

/-- The scalar part of an expanded (Share-free) Ixon expression node. -/
inductive Head where
  | sort (idx : UInt64)
  | var (idx : UInt64)
  | ref (refIdx : UInt64) (univIdxs : Array UInt64)
  | recur (recIdx : UInt64) (univIdxs : Array UInt64)
  | prj (typeRefIdx : UInt64) (fieldIdx : UInt64)
  | str (refIdx : UInt64)
  | nat (refIdx : UInt64)
  | app
  | lam (contract : BinderContract)
  | all (contract : BinderContract) (result : ValueContract)
  | letE (contract : LetContract)
  deriving BEq, Hashable, Repr, Inhabited

namespace Head

/-- §3.2 constructor tag (equal to the Ixon expression flag). -/
def tag : Head → Nat
  | .sort _ => 0x0
  | .var _ => 0x1
  | .ref .. => 0x2
  | .recur .. => 0x3
  | .prj .. => 0x4
  | .str _ => 0x5
  | .nat _ => 0x6
  | .app => 0x7
  | .lam _ => 0x8
  | .all .. => 0x9
  | .letE _ => 0xA

/-- §3.2 scalar payload vector, compared numerically. -/
def scalars : Head → List Nat
  | .sort i => [i.toNat]
  | .var i => [i.toNat]
  | .ref r us => r.toNat :: us.size :: us.toList.map UInt64.toNat
  | .recur r us => r.toNat :: us.size :: us.toList.map UInt64.toNat
  | .prj t f => [t.toNat, f.toNat]
  | .str i => [i.toNat]
  | .nat i => [i.toNat]
  | .app => []
  | .lam c => [c.toBits.toNat]
  | .all c r => [(packAllContract c r).toNat]
  | .letE c => [c.flags.toNat, c.binder.toBits.toNat]

/-- Number of ordered children. -/
def arity : Head → Nat
  | .prj .. => 1
  | .app | .lam _ | .all .. => 2
  | .letE _ => 3
  | _ => 0

/-- Ixon expression flag of the inline node. -/
def flag : Head → UInt8
  | .sort _ => Ixon.Expr.FLAG_SORT
  | .var _ => Ixon.Expr.FLAG_VAR
  | .ref .. => Ixon.Expr.FLAG_REF
  | .recur .. => Ixon.Expr.FLAG_REC
  | .prj .. => Ixon.Expr.FLAG_PRJ
  | .str _ => Ixon.Expr.FLAG_STR
  | .nat _ => Ixon.Expr.FLAG_NAT
  | .app => Ixon.Expr.FLAG_APP
  | .lam _ => Ixon.Expr.FLAG_LAM
  | .all .. => Ixon.Expr.FLAG_ALL
  | .letE _ => Ixon.Expr.FLAG_LET

/-- The Tag4 size field written by `putExpr` for a non-telescope head. -/
def tag4Field : Head → UInt64
  | .sort i => i
  | .var i => i
  | .ref _ us => us.size.toUInt64
  | .recur _ us => us.size.toUInt64
  | .prj _ f => f
  | .str i => i
  | .nat i => i
  | .letE c => c.flags
  | .app | .lam _ | .all .. => 0

/-- Bytes a non-telescope node writes itself, excluding its children.
Telescope heads (`app`/`lam`/`all`) are priced by the telescope recurrence
and return 0 here. -/
def ownBytes : Head → Nat
  | .sort i => tag4Size i.toNat
  | .var i => tag4Size i.toNat
  | .ref r us => tag4Size us.size + tag0Size r.toNat + univIdxsSize us
  | .recur r us => tag4Size us.size + tag0Size r.toNat + univIdxsSize us
  | .prj t f => tag4Size f.toNat + tag0Size t.toNat
  | .str i => tag4Size i.toNat
  | .nat i => tag4Size i.toNat
  | .letE c => tag4Size c.flags.toNat + 1
  | .app | .lam _ | .all .. => 0

end Head

/-- A structural node: head scalars plus ordered child term IDs. -/
structure Node where
  head : Head
  children : Array Nat
  deriving BEq, Hashable, Repr, Inhabited

/-- The §3.2 total key order: constructor tag, then scalar vector, then the
ordered child-ID vector, each compared numerically/lexicographically with a
proper prefix first. -/
def Node.compareKey (x y : Node) : Ordering :=
  (compare x.head.tag y.head.tag).then
    ((lexCompare x.head.scalars y.head.scalars).then
      (lexCompare x.children.toList y.children.toList))

/-- The `i`-th child ID (the arity invariant makes the default unreachable). -/
@[inline] def Node.child (n : Node) (i : Nat) : Nat := n.children.getD i 0

/-- Rebuild an Ixon expression node from its head and child expressions. -/
def Node.toExpr (n : Node) (child : Nat → Ixon.Expr) : Ixon.Expr :=
  match n.head with
  | .sort i => .sort i
  | .var i => .var i
  | .ref r us => .ref r us
  | .recur r us => .recur r us
  | .prj t f => .prj t f (child (n.child 0))
  | .str i => .str i
  | .nat i => .nat i
  | .app => .app (child (n.child 0)) (child (n.child 1))
  | .lam c => .lam c (child (n.child 0)) (child (n.child 1))
  | .all c r => .all c r (child (n.child 0)) (child (n.child 1))
  | .letE c => .letE c (child (n.child 0)) (child (n.child 1)) (child (n.child 2))

/-! ## Errors, limits and work counters -/

/-- Metered resources. -/
inductive Resource where
  | exprVisits
  | depth
  | nodes
  | states
  | transitions
  | costEvals
  | outputBytes
  | materialize
  | materializeWork
  | oracleTables
  | oracleVariants
  deriving BEq, Repr, Inhabited

/-- Why an exact sharing operation did not produce a certified result. -/
inductive SharingError where
  /-- A `Share` leaf where an expanded (Share-free) AST was required. -/
  | shareInExpandedInput (rootIdx : Nat) (shareIdx : UInt64)
  /-- A `Share` index that does not name any table entry. `entry = none`
  means a root. -/
  | shareOutOfRange (entry : Option Nat) (shareIdx : UInt64) (tableSize : Nat)
  /-- Entry `entry` refers to itself or to a later entry. Only strictly
  backward references are admitted, which also excludes cycles. -/
  | nonBackwardShare (entry : Nat) (shareIdx : UInt64)
  /-- A count or index that cannot be written through a `UInt64` field. -/
  | formatBound (what : String) (value : Nat)
  /-- Root reassembly received a different number of roots than extraction
  produced. -/
  | rootCountMismatch (expected actual : Nat)
  /-- A deterministic resource limit was reached before certification. -/
  | resourceExhausted (resource : Resource) (limit : Nat)
  /-- An internal self-check failed. Never returned for a correct
  implementation; reported instead of an unverified result. -/
  | internal (msg : String)
  deriving BEq, Repr, Inhabited

instance : ToString SharingError where
  toString e := reprStr e

/-- Deterministic resource limits. Exceeding any limit returns
`SharingError.resourceExhausted`; limits never change a successful result. -/
structure Limits where
  /-- Expression nodes walked while expanding input (tables, roots, and the
  self-check of the output). -/
  maxExprVisits : Nat := 1 <<< 26
  /-- Recursion depth of expression walks. -/
  maxDepth : Nat := 1 <<< 14
  /-- Distinct structural subterms. -/
  maxNodes : Nat := 1 <<< 20
  /-- Width states inserted into the search frontier. -/
  maxStates : Nat := 1 <<< 20
  /-- Transitions (state, appended term) examined. -/
  maxTransitions : Nat := 1 <<< 24
  /-- Term cost evaluations plus telescope spine steps. -/
  maxCostEvals : Nat := 1 <<< 30
  /-- Variable bytes (roots, table count, table bodies) of the result. -/
  maxOutputBytes : Nat := 1 <<< 28
  /-- Predicted size of the materialized output (an upper bound on the
  expression nodes built), checked before materializing. -/
  maxMaterialize : Nat := 1 <<< 26
  /-- Cumulative evaluation work of materializing a table entry by entry (the
  tiered phase re-evaluates the DAG once per entry, about `2·k·N`); matches
  the Rust `max_work`. -/
  maxMaterializeWork : Nat := 1 <<< 36
  /-- Tables enumerated by the exhaustive oracle. -/
  maxOracleTables : Nat := 1 <<< 20
  /-- Representations enumerated by the exhaustive oracle. -/
  maxOracleVariants : Nat := 1 <<< 24
  /-- Use the existing heuristic (`Ix.Sharing.applySharing`) as an extra
  pruning upper bound. It never influences which result is returned. -/
  useHeuristicBound : Bool := true
  /-- Run the heuristic only when the unshared variable length is at most
  this many bytes (bounds its tree walks). -/
  heuristicMaxUnsharedBytes : Nat := 1 <<< 20
  /-- Lower-bound pruning. Disabling it (for testing) explores every
  reachable width state; the result must not change. -/
  prune : Bool := true
  /-- Uniform width: search each component by plain subset enumeration (the
  reference) instead of the reclassifying branch and bound. The result must
  not change. -/
  uniformSubsetSearch : Bool := false
  deriving Repr, Inhabited

/-- Nonsemantic work statistics. -/
structure Stats where
  exprVisits : Nat := 0
  internedNodes : Nat := 0
  distinctSubterms : Nat := 0
  candidates : Nat := 0
  layers : Nat := 0
  statesReached : Nat := 0
  statesExpanded : Nat := 0
  statesPruned : Nat := 0
  transitions : Nat := 0
  transitionsPruned : Nat := 0
  costEvals : Nat := 0
  materializedNodes : Nat := 0
  outputBytes : Nat := 0
  heuristicBytes : Option Nat := none
  deriving BEq, Repr, Inhabited

/-- Checked counter increment: `count + n` must stay within `limit`. -/
@[inline] def bump (count n limit : Nat) (r : Resource) : Except SharingError Nat :=
  let count' := count + n
  if count' > limit then .error (.resourceExhausted r limit) else .ok count'

end Ix.Sharing.Exact

end
