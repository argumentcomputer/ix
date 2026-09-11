import Ix.Compiler.Ixon.Const

/-!
# Structural work accounting

The proof-facing codec, sharing checker, compressor, eraser, and certificate
builder are total definitions.  Corpus execution additionally needs a cheap
preflight which prevents their intentionally simple list/structural
implementations from receiving an unbounded job.

The counters here are deterministic structure-derived units, never wall-clock
limits.  In particular:

* `layer1NodeVisits` charges the expression-node visits performed by the
  quadratic `entriesUsedTwice` sharing check, plus its repeated list
  materialization, drops, and range traversal;
* `expandedUnits?` computes the size of a sharing expansion without allocating
  that expansion;
* `programStats` charges the current append-based whole-program eraser and the
  worst-case number of certificate validation attempts.

Keeping these counters separate from the proof definitions lets proofs retain
their transparent models while every corpus-facing executable boundary can
fail before starting superlinear work.
-/

namespace Ix.Compiler.Ixon.Work

/-- A stable name for each independently configurable resource counter. -/
inductive Metric where
  | catalogManifestBytes
  | catalogMembers
  | catalogDependencyEdges
  | catalogStorageUnits
  | catalogPieceBytes
  | catalogConstantEntries
  | catalogConstantBytes
  | catalogBlobEntries
  | catalogBlobBytes
  | catalogAssumptions
  | catalogHints
  | layer1NodeVisits
  | compressionInputUnits
  | programConstants
  | programExpressionUnits
  | programExpandedExpressionUnits
  | erasedDeclarations
  | erasureAppendCells
  | certificateCandidates
  | certificateValidationAttempts
  | certificateSourceNodeWork
  | usageFuel
  | erasureFuel
  | validationFuel
  | loweringFuel
  deriving BEq, DecidableEq, Repr

/-- A resource failure always records the measured value and the applicable
inclusive limit. -/
structure Exceeded where
  metric : Metric
  actual : Nat
  limit : Nat
  deriving BEq, DecidableEq, Repr

/-- Inclusive structural budget check. -/
def ensure (metric : Metric) (actual limit : Nat) : Except Exceeded Unit :=
  if actual ≤ limit then .ok () else .error ⟨metric, actual, limit⟩

/-- Expression work units used for compressor admission.  This is the AST
constructor count plus every universe-instantiation index traversed by
serialization, hashing, and structural comparisons. -/
def exprUnits : Expr → Nat
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => 1
  | .ref _ indices | .recur _ indices => indices.size + 1
  | .prj _ _ value => exprUnits value + 1
  | .app fn arg => exprUnits fn + exprUnits arg + 1
  | .lam _ type body | .all _ _ type body =>
    exprUnits type + exprUnits body + 1
  | .letE _ type value body =>
    exprUnits type + exprUnits value + exprUnits body + 1

def exprArrayUnits (exprs : Array Expr) : Nat :=
  exprs.foldl (fun total expr => total + exprUnits expr) 0

def exprListUnits (exprs : List Expr) : Nat :=
  exprs.foldl (fun total expr => total + exprUnits expr) 0

def exprArrayNodes (exprs : Array Expr) : Nat :=
  exprs.foldl (fun total expr => total + expr.codecSize) 0

/-- A conservative expression/list-cell charge for the current `layer1WF`
implementation.  Entry `j` is scanned once by `tableWF` and once for every
earlier sharing index; every body is scanned once for bounds and once per table
entry.  The charge also includes every `table.toList`, repeated
`drop (i + 1)`, and construction/traversal of `List.range`. -/
def layer1NodeVisits (table bodies : Array Expr) : Nat :=
  let (_, weightedTable) := table.foldl (init := (0, 0)) fun state expr =>
    let index := state.1
    (index + 1, state.2 + (index + 1) * expr.codecSize)
  let tableSize := table.size
  let bodyNodes := exprArrayNodes bodies
  weightedTable + (tableSize + 1) * bodyNodes +
    tableSize * (tableSize + 1) +
    tableSize * (tableSize + 1) / 2 + 2 * tableSize

/-! ## Expansion accounting without expansion allocation -/

/-- Expression units after replacing every `.share` with the already-computed
size of its table entry.  `none` identifies a forward/out-of-range share. -/
def expandedExprUnits (tableSizes : Array Nat) : Expr → Option Nat
  | .sort _ | .var _ | .str _ | .nat _ => some 1
  | .ref _ indices | .recur _ indices => some (indices.size + 1)
  | .share index => tableSizes[index.toNat]?
  | .prj _ _ value => do
    return (← expandedExprUnits tableSizes value) + 1
  | .app fn arg => do
    return (← expandedExprUnits tableSizes fn) +
      (← expandedExprUnits tableSizes arg) + 1
  | .lam _ type body | .all _ _ type body => do
    return (← expandedExprUnits tableSizes type) +
      (← expandedExprUnits tableSizes body) + 1
  | .letE _ type value body => do
    return (← expandedExprUnits tableSizes type) +
      (← expandedExprUnits tableSizes value) +
      (← expandedExprUnits tableSizes body) + 1

def expandedTableSizes? (table : Array Expr) : Option (Array Nat) :=
  table.foldlM (init := #[]) fun sizes expr => do
    let size ← expandedExprUnits sizes expr
    return sizes.push size

/-- Exact work-unit size of fully inlined bodies, computed in time linear in
the stored representation and without materializing an exponentially larger
tree. -/
def expandedUnits? (table bodies : Array Expr) : Option Nat := do
  let tableSizes ← expandedTableSizes? table
  bodies.foldlM (init := 0) fun total expr => do
    let size ← expandedExprUnits tableSizes expr
    return total + size

/-! ## Whole-program accounting -/

def erasedDeclarationCount (constant : Constant) : Nat :=
  match constant.info with
  | .muts members => members.size
  | _ => 1

def certificateCandidateCount (constant : Constant) : Nat :=
  match constant.info with
  | .muts _ => 0
  | _ => 1

private def triangularBelow (count : Nat) : Nat :=
  count * (count - 1) / 2

/-- All counters needed before entering checking, erasure, or validation. -/
structure ProgramStats where
  constants : Nat
  expressionUnits : Nat
  /-- Sum of fully expanded body units. Malformed forward/out-of-range tables
  fall back to stored body units and remain the semantic checker's concern. -/
  expandedExpressionUnits : Nat
  layer1NodeVisits : Nat
  erasedDeclarations : Nat
  erasureAppendCells : Nat
  certificateCandidates : Nat
  certificateValidationAttempts : Nat
  certificateSourceNodeWork : Nat
  deriving BEq, DecidableEq, Repr

private structure ProgramAccum where
  constants : Nat := 0
  expressionUnits : Nat := 0
  expandedExpressionUnits : Nat := 0
  layer1NodeVisits : Nat := 0
  erasedDeclarations : Nat := 0
  erasureAppendCells : Nat := 0
  certificateCandidates : Nat := 0

private def addConstant (acc : ProgramAccum) (constant : Constant) :
    ProgramAccum :=
  let bodies := constant.info.exprs.toArray
  let bodyUnits := exprArrayUnits bodies
  let expandedUnits := (expandedUnits? constant.sharing bodies).getD bodyUnits
  let outputCount := erasedDeclarationCount constant
  { constants := acc.constants + 1
    expressionUnits := acc.expressionUnits + bodyUnits +
      exprArrayUnits constant.sharing
    expandedExpressionUnits := acc.expandedExpressionUnits + expandedUnits
    layer1NodeVisits := acc.layer1NodeVisits +
      layer1NodeVisits constant.sharing bodies
    erasedDeclarations := acc.erasedDeclarations + outputCount
    -- `eraseConstant` appends each mutual member; `eraseProgram` then appends
    -- that chunk to the prefix accumulated from earlier constants.
    erasureAppendCells := acc.erasureAppendCells +
      triangularBelow outputCount + acc.erasedDeclarations
    certificateCandidates := acc.certificateCandidates +
      certificateCandidateCount constant }

/-- Worst-case calls made by the dependency-discovery fixpoint, followed by
one dependency-ordered proof-producing pass.  A productive discovery round
can accept only one of the remaining candidates, hence the triangular term. -/
def certificateAttempts (candidates : Nat) : Nat :=
  candidates * (candidates + 1) / 2 + candidates

def programStats (constants : List (Address × Constant)) : ProgramStats :=
  let acc := constants.foldl (fun acc entry => addConstant acc entry.2) {}
  let attempts := certificateAttempts acc.certificateCandidates
  { constants := acc.constants
    expressionUnits := acc.expressionUnits
    expandedExpressionUnits := acc.expandedExpressionUnits
    layer1NodeVisits := acc.layer1NodeVisits
    erasedDeclarations := acc.erasedDeclarations
    erasureAppendCells := acc.erasureAppendCells
    certificateCandidates := acc.certificateCandidates
    certificateValidationAttempts := attempts
    -- Deliberately conservative combined scaling charge: each possible
    -- validation attempt is priced as one scan of every fully expanded body.
    certificateSourceNodeWork := attempts * acc.expandedExpressionUnits }

end Ix.Compiler.Ixon.Work
