/-
  Exact minimum sharing (W1): tiny exhaustive reference oracle (§6.3, P1).

  Deliberately independent of the telescope recurrence and the width-state
  search. It enumerates

  * every ordered table over *all* distinct subterms of the roots (every
    ordered subset, including leaves, roots, and useless entries), and
  * every representation of each table entry and root obtained by choosing,
    independently at each occurrence, the inline constructor or a reference
    to an equal available entry (entry `i` may use entries `< i`),

  serializes candidates with the production writer (`putExpr`, or a
  caller-supplied complete-Constant writer) and keeps the least full key
  `(byte length, table term IDs, bytes)` of §3.3.

  `oracle` uses one standard reduction: for a fixed table the entries and
  roots serialize as independent fixed-position parts, so the least key for
  that table is obtained by choosing each part's least `(length, bytes)`
  representation. `oracleProduct` drops even that reduction and enumerates
  the full Cartesian product of all parts; it is only feasible for the
  smallest inputs and exists to cross-check `oracle`.

  Exponential by design; every enumeration is metered and fails closed.
-/
module

public import Ix.Sharing.Exact.Dictionary

public section

namespace Ix.Sharing.Exact

open Ixon

/-- Oracle work counters. `candidates` counts complete candidates compared
(one per table for `oracle`, the whole product for `oracleProduct`). -/
structure OracleWork where
  tables : Nat := 0
  variants : Nat := 0
  candidates : Nat := 0
  deriving Inhabited, Repr

abbrev OracleM := StateT OracleWork (Except SharingError)

def chargeVariants (limits : Limits) (k : Nat) : OracleM Unit := do
  let w ← get
  if w.variants + k > limits.maxOracleVariants then
    throw (.resourceExhausted .oracleVariants limits.maxOracleVariants)
  set { w with variants := w.variants + k }

def chargeTable (limits : Limits) (candidates : Nat) : OracleM Unit := do
  let w ← get
  if w.tables + 1 > limits.maxOracleTables then
    throw (.resourceExhausted .oracleTables limits.maxOracleTables)
  set { w with tables := w.tables + 1, candidates := w.candidates + candidates }

/-- Every representation of term `t`: a Share to its entry if available,
plus the inline node over every combination of child representations. -/
def variantsOf (dag : Dag) (index : Array (Option Nat)) (limits : Limits) :
    Nat → Nat → OracleM (List Ixon.Expr)
  | 0, _ => throw (.internal "oracle fuel exhausted")
  | fuel + 1, t => do
    let node := dag.node t
    let go := variantsOf dag index limits fuel
    let inl : List Ixon.Expr ← match node.head with
      | .prj ti f => do
        let vs ← go (node.child 0)
        pure (vs.map (Ixon.Expr.prj ti f))
      | .app => do
        let fs ← go (node.child 0)
        let as ← go (node.child 1)
        pure (fs.flatMap fun f => as.map (Ixon.Expr.app f))
      | .lam c => do
        let tys ← go (node.child 0)
        let bs ← go (node.child 1)
        pure (tys.flatMap fun ty => bs.map (Ixon.Expr.lam c ty))
      | .all c r => do
        let tys ← go (node.child 0)
        let bs ← go (node.child 1)
        pure (tys.flatMap fun ty => bs.map (Ixon.Expr.all c r ty))
      | .letE c => do
        let tys ← go (node.child 0)
        let vs ← go (node.child 1)
        let bs ← go (node.child 2)
        pure (tys.flatMap fun ty => vs.flatMap fun v => bs.map (Ixon.Expr.letE c ty v))
      | _ => pure [node.toExpr fun _ => default]
    let sh := match index[t]?.getD none with
      | some i => [Ixon.Expr.share i.toUInt64]
      | none => []
    let out := sh ++ inl
    chargeVariants limits out.length
    return out

/-- `(length, bytes)` order of serialized candidates. -/
def keyLess (a b : ByteArray) : Bool :=
  a.size < b.size || (a.size == b.size && compareBytes a b == .lt)

/-- The representation of `t` whose serialization has least
`(length, bytes)`. -/
def bestPart (dag : Dag) (index : Array (Option Nat)) (limits : Limits) (t : Nat) :
    OracleM (Ixon.Expr × ByteArray) := do
  let vs ← variantsOf dag index limits (dag.size + 1) t
  let mut best : Option (Ixon.Expr × ByteArray) := none
  for v in vs do
    let bytes := runPut (putExpr v)
    match best with
    | none => best := some (v, bytes)
    | some (_, bb) => if keyLess bytes bb then best := some (v, bytes)
  match best with
  | some b => return b
  | none => throw (.internal "term without representation")

/-- Every ordered subset (sequence without repetition) of `xs`. -/
def orderedSubsets : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | fuel + 1, xs => [] :: xs.flatMap fun x => (orderedSubsets fuel (xs.erase x)).map (x :: ·)

/-- Serialized variable part in Constant order: roots, table count, entries.
For candidates of equal length and equal table, every part has the same
length, so this order agrees with comparing complete Constants. -/
def variablePartBytes (sharing roots : Array Ixon.Expr) : Except SharingError ByteArray :=
  .ok <| runPut do
    for r in roots do putExpr r
    putTagN 0 0 sharing.size.toUInt64
    for e in sharing do putExpr e

/-- Oracle result. -/
structure OracleResult where
  /-- Bytes of the winning candidate (as produced by the writer). -/
  bytes : ByteArray
  /-- Table term IDs of the winner. -/
  table : Array Nat
  sharing : Array Ixon.Expr
  roots : Array Ixon.Expr
  work : OracleWork
  /-- Distinct byte strings of the per-table winners that attain the minimum
  length, in enumeration order. -/
  minima : Array ByteArray
  deriving Inhabited

/-- Candidate key `(length, table, bytes)` strictly smaller. -/
def fullKeyLess (bytes : ByteArray) (table : Array Nat) (bytes' : ByteArray)
    (table' : Array Nat) : Bool :=
  bytes.size < bytes'.size ||
    (bytes.size == bytes'.size &&
      (compareNatArray table table' == .lt ||
        (compareNatArray table table' == .eq && compareBytes bytes bytes' == .lt)))

/-- Record a candidate in the running best and minima. -/
def OracleResult.consider (best : Option OracleResult) (bytes : ByteArray)
    (table : Array Nat) (sharing roots : Array Ixon.Expr) : Option OracleResult :=
  match best with
  | none => some { bytes, table, sharing, roots, work := {}, minima := #[bytes] }
  | some b =>
    let minima :=
      if bytes.size < b.bytes.size then #[bytes]
      else if bytes.size == b.bytes.size && !b.minima.contains bytes then b.minima.push bytes
      else b.minima
    if fullKeyLess bytes table b.bytes b.table then
      some { b with bytes, table, sharing, roots, minima }
    else some { b with minima }

/-- Exhaustive oracle with per-part selection. `write sharing roots` must
produce the serialized candidate (e.g. the complete Constant). -/
def oracle (dag : Dag) (rootIds : Array Nat)
    (write : Array Ixon.Expr → Array Ixon.Expr → Except SharingError ByteArray)
    (limits : Limits) : Except SharingError OracleResult := do
  let n := dag.size
  let run : OracleM (Option OracleResult) := do
    let mut best : Option OracleResult := none
    for order in orderedSubsets n (List.range n) do
      chargeTable limits 1
      let table := order.toArray
      let mut entries : Array Ixon.Expr := #[]
      for h : i in [0:table.size] do
        let (e, _) ← bestPart dag (indexOfPrefix n table i) limits table[i]
        entries := entries.push e
      let full := indexOfPrefix n table table.size
      let mut roots : Array Ixon.Expr := #[]
      for r in rootIds do
        let (e, _) ← bestPart dag full limits r
        roots := roots.push e
      let bytes ← liftM (write entries roots)
      best := OracleResult.consider best bytes table entries roots
    return best
  let (best, work) ← run.run {}
  match best with
  | some b => return { b with work }
  | none => throw (.internal "oracle enumerated no table")
where
  liftM {α} (x : Except SharingError α) : OracleM α :=
    match x with
    | .ok a => pure a
    | .error e => throw e

/-- Stream the Cartesian product of `parts`, folding every complete
combination (in part order) into the accumulator. -/
def forProduct (parts : List (List Ixon.Expr)) (acc : Array Ixon.Expr)
    (f : Array Ixon.Expr → Option OracleResult → Except SharingError (Option OracleResult))
    (best : Option OracleResult) : Except SharingError (Option OracleResult) :=
  match parts with
  | [] => f acc best
  | p :: rest => p.foldlM (fun b x => forProduct rest (acc.push x) f b) best

/-- Exhaustive oracle over the full Cartesian product of every part's
representations (no separability reduction). -/
def oracleProduct (dag : Dag) (rootIds : Array Nat)
    (write : Array Ixon.Expr → Array Ixon.Expr → Except SharingError ByteArray)
    (limits : Limits) : Except SharingError OracleResult := do
  let n := dag.size
  let run : OracleM (Option OracleResult) := do
    let mut best : Option OracleResult := none
    for order in orderedSubsets n (List.range n) do
      chargeTable limits 0
      let table := order.toArray
      let mut parts : List (List Ixon.Expr) := []
      for h : i in [0:table.size] do
        parts := parts ++ [← variantsOf dag (indexOfPrefix n table i) limits (n + 1) table[i]]
      let full := indexOfPrefix n table table.size
      for r in rootIds do
        parts := parts ++ [← variantsOf dag full limits (n + 1) r]
      let count := parts.foldl (fun acc p => acc * p.length) 1
      chargeVariants limits count
      modify fun w => { w with candidates := w.candidates + count }
      let step (combo : Array Ixon.Expr) (b : Option OracleResult) :
          Except SharingError (Option OracleResult) := do
        let entries := combo.extract 0 table.size
        let roots := combo.extract table.size combo.size
        let bytes ← write entries roots
        return OracleResult.consider b bytes table entries roots
      best ← match forProduct parts #[] step best with
        | .ok b => pure b
        | .error e => throw e
    return best
  let (best, work) ← run.run {}
  match best with
  | some b => return { b with work }
  | none => throw (.internal "oracle enumerated no table")

end Ix.Sharing.Exact

end
