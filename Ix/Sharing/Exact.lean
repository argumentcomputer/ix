/-
  Exact minimum sharing for anonymous Ixon constants (workstream W1).

  Specification: `docs/sharing-minimum.md` (§3 canonical rule, §4.1
  reductions, §5 fixed-dictionary recurrence, §6 width-state search, §7 API).
  For a resolved Constant, the canonical sharing encoding is the feasible
  backward-reference encoding with the least key

    (complete serialized length, table structural-ID vector, bytes)

  over all table choices, table orders and per-occurrence inline/reference
  choices, with every non-sharing field, the refs and univs tables and the
  ordered roots fixed. Only strictly backward table references are feasible
  (entry `i` may use entries `< i`, roots may use every entry); forward and
  self references are rejected rather than optimized over.

  Every operation is pure over Ixon data (no Lean frontend) and returns an
  explicit error instead of an uncertified result. Resource limits may turn a
  success into `resourceExhausted`, but never change a successful result.

  Modules:
  * `Exact.Basic`      exact serializer lengths, node alphabet, errors, limits
  * `Exact.Dag`        bounded share expansion, structural IDs, root API
  * `Exact.Dictionary` fixed-dictionary optimizer `C_M` and materialization
  * `Exact.Search`     width-state DP with LB pruning and self-verification
  * `Exact.Oracle`     tiny exhaustive reference search (tests only)
-/
module

public import Ix.Sharing.Exact.Basic
public import Ix.Sharing.Exact.Dag
public import Ix.Sharing.Exact.Dictionary
public import Ix.Sharing.Exact.Search
public import Ix.Sharing.Exact.Oracle

public section

namespace Ix.Sharing.Exact

open Ixon

/-- Exact minimum sharing of expanded (Share-free) roots. A `Share` leaf in
the input is an error. -/
def optimizeSharing (roots : Array Ixon.Expr) (limits : Limits := {}) :
    Except SharingError ExactSharingResult := do
  let ex ← expand limits #[] roots false
  optimizeExpanded limits ex

/-- Exact minimum sharing of roots given with an existing sharing table,
which is first expanded logically (backward references only). -/
def optimizeSharingTable (sharing roots : Array Ixon.Expr) (limits : Limits := {}) :
    Except SharingError ExactSharingResult := do
  let ex ← expand limits sharing roots true
  optimizeExpanded limits ex

/-- The Share-free equivalent of a Constant: roots expanded (with pointer
sharing, no occurrence-tree allocation) and an empty table. -/
def expandConstantSharing (c : Constant) (limits : Limits := {}) :
    Except SharingError Constant := do
  let ex ← expand limits c.sharing (constantInfoRoots c.info) true
  let exprs := ex.dag.toExprs
  let info ← withRoots c.info (ex.roots.map (exprs[·]!))
  return { c with info, sharing := #[] }

/-- The canonical exact-minimum sharing of a Constant: expand its table,
optimize, and reassemble the same ConstantInfo, refs and univs. -/
def normalizeConstantSharing (c : Constant) (limits : Limits := {}) :
    Except SharingError Constant := do
  let r ← optimizeSharingTable c.sharing (constantInfoRoots c.info) limits
  let info ← withRoots c.info r.roots
  return { c with info, sharing := r.sharing }

/-- Outcome of a canonicality check. -/
inductive CanonicalCheck where
  | canonical
  /-- The canonical serialized Constant differs; here are its bytes. -/
  | noncanonical (expected : ByteArray)
  deriving Inhabited

/-- Whether `c` is byte-identical to its exact canonical sharing. -/
def checkCanonicalSharing (c : Constant) (limits : Limits := {}) :
    Except SharingError CanonicalCheck := do
  let n ← normalizeConstantSharing c limits
  let expected := serConstant n
  return if serConstant c == expected then .canonical else .noncanonical expected

/-- Bytes of `c`'s serialization that do not depend on sharing: everything
except the expression roots, the sharing count and the table bodies. Then
`(serConstant c).size = fixedConstantBytes c + Σ exprSize roots
+ tag0Size c.sharing.size + Σ exprSize c.sharing`. -/
def fixedConstantBytes (c : Constant) : Except SharingError Nat := do
  let roots := constantInfoRoots c.info
  let info ← withRoots c.info (roots.map fun _ => Ixon.Expr.var 0)
  let size := (serConstant { c with info, sharing := #[] }).size
  return size - roots.size - tag0Size 0

/-- Writer of complete candidate Constants for the oracle. -/
def constantWriter (c : Constant) (sharing roots : Array Ixon.Expr) :
    Except SharingError ByteArray := do
  let info ← withRoots c.info roots
  return serConstant { c with info, sharing }

/-- Run the exhaustive oracle (`product := true` for the full Cartesian
product) on a Constant and return the oracle's canonical Constant. -/
def oracleConstant (c : Constant) (limits : Limits := {}) (product : Bool := false) :
    Except SharingError (Constant × OracleResult) := do
  let ex ← expand limits c.sharing (constantInfoRoots c.info) true
  let r ← (if product then oracleProduct else oracle) ex.dag ex.roots (constantWriter c) limits
  let info ← withRoots c.info r.roots
  return ({ c with info, sharing := r.sharing }, r)

end Ix.Sharing.Exact

end
