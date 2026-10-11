/-
  Sharing tables of anonymous Ixon constants: the canonical construction and
  its reference searches (`docs/sharing-minimum.md`).

  The compiler shares every block with the tiered canonical construction
  `canonicalSharingTiered` (`Exact.Tiered`; Rust
  `ixon::sharing_exact::canonical_sharing_tiered`): phase 1 is the exact
  uniform-width optimizer (`Exact.Uniform`) at widths 1, 2 and 3, phase 2
  allocates the table slots, phase 3 re-materializes every part under the
  real TagN widths, and the candidate with the fewest bytes wins.

  The global exact minimum of `docs/sharing-minimum.md` §3 is computed by the
  width-state search (`optimizeSharing`, `normalizeConstantSharing`,
  `Exact.Search`): for a resolved Constant, the feasible backward-reference
  encoding with the least key

    (complete serialized length, table structural-ID vector, bytes)

  over all table choices, table orders and per-occurrence inline/reference
  choices, with every non-sharing field, the refs and univs tables and the
  ordered roots fixed. Only strictly backward table references are feasible
  (entry `i` may use entries `< i`, roots may use every entry); forward and
  self references are rejected rather than optimized over. The search is
  exponential in the candidates: it is a test oracle for small inputs, not
  the compiler path.

  Every operation is pure over Ixon data (no Lean frontend) and returns an
  explicit error instead of an uncertified result. Resource limits may turn a
  success into `resourceExhausted`, but never change a successful result.

  Modules. A specification module defines what the theorems
  (`Ix.Sharing.Verify`) describe; a fast twin holds a faster body proved equal
  to a specification for every input by a `@[csimp]` theorem `@f = @fFast`,
  so compiled code runs the twin while every theorem keeps talking about the
  specification. All 19 csimp theorems are audit roots
  (`Ix.Sharing.Verify.Audit.CompiledCode` fails the build otherwise), and a
  twin that drifts from its specification breaks its equality proof.

  Specifications (with the csimp theorems declared in the same module):
  * `Exact.Basic`      exact serializer lengths, node alphabet, errors, limits
                       (`tagNByteWidth_eq_fast`)
  * `Exact.Dag`        bounded share expansion, structural IDs, root API
                       (`propagateCounts_eq_fast`)
  * `Exact.Dictionary` fixed-dictionary optimizer `C_M` and materialization
                       (`build_eq_fast`, `inlineCost_eq_fast`)
  * `Exact.Search`     width-state search for the global minimum (test oracle),
                       and the table materialization the construction uses
                       (`materializeTable_eq_fast`, whose fast body walks
                       `Exact.Phase3`)
  * `Exact.UniformSearch` graph facts, classes, components and the
                       per-component exact search of the uniform optimizer
                       (`SCtx.phiE_eq_fast`)
  * `Exact.Uniform`    exact optimizer for a uniform Share width (phase 1)
                       (`searchComponents_eq_via`, `csBase_eq_fast`)
  * `Exact.Tiered`     the canonical tiered construction (TagN layout)

  Fast twins (the csimp theorem; the specification it replaces):
  * `Exact.Phase3`     re-evaluation after one dictionary change by a walk up
                       the parent lists (proved equal to `evalUp`; used by
                       the fast `materializeTable`)
  * `Exact.Reexpand`   re-expansion without hashing whole nodes
                       (`reexpand_eq_fast`; `reexpand`)
  * `Exact.UniformSearchLocal` the component search on the components' areas
                       and closures (`searchComponentsWith_eq_fast`; the loop
                       of `searchComponents`)
  * `Exact.TierFast`   the first-tier search with a derived excluded set
                       (`firstTier_eq_fast`; `firstTier`)
  * `Exact.PinnedDeps` nearest stored descendants with one stamp array
                       (`pinnedDeps_eq_fast`; `pinnedDeps`)
  * `Exact.PinnedFast` the pinned table order with a priority set of ready
                       terms (`pinnedOrder_eq_fast`; `pinnedOrder`)
  * `Exact.KnapsackFast` the rank-based table-count knapsack
                       (`uniformKnapsack_eq_fast`; `uniformKnapsack`)
  * `Exact.AreaSearch` the component search on the components' areas only,
                       with the truncated evaluation and a checked opacity
                       test (`searchComponentsArea`; equal to the loop
                       `searchComponentsWith` on a stage's tables,
                       `AreaProof.searchComponentsArea_eq`, proved in
                       `Exact.AreaRowsRel`, `Exact.AreaClosureRows`,
                       `Exact.AreaTruncRows`, `Exact.AreaCostEq`,
                       `Exact.AreaBlockEq` and `Exact.AreaSearchEq`)
  * `Exact.TieredFast` recompiled copies of `allocate`, `tieredAtWidth`,
                       `canonicalTieredCore`, `canonicalTieredExpanded` and
                       `optimizeUniformExpanded` (`*_eq_C`), so their callers
                       reach the fast parts above (a csimp applies only to
                       code compiled after it); their component loop is
                       `searchComponentsArea`

  Shared helpers and oracles:
  * `Exact.SortedSets` ascending lists as sets: first differences, the tie
                       order, range minima (sparse table)
  * `Exact.Oracle`     tiny exhaustive reference search (test oracle)

  Names of twins: `fFast` is a fast twin attached by `f_eq_fast`; `fC` is a
  recompiled copy attached by `f_eq_C` (`Exact.TieredFast`); `fF` and `fP`
  take precomputed tables (`Prep`, graph facts) as arguments and are proved
  equal by unfolding (`f_eq_F`, `rematerialize_eq_P`); `fL` is the area- and
  closure-local form of a uniform-search step, `fA` its area-only form;
  `fG` is an `fF` whose component loop is `searchComponentsArea`, proved equal
  after the DAG checks (`Exact.TieredFast`); `searchComponentsVia` is
  `searchComponents` written as `searchComponentsWith` on the stage's tables,
  so that compiled code reaches `searchComponentsWithFast`.
-/
module

public import Ix.Sharing.Exact.Basic
public import Ix.Sharing.Exact.Dag
public import Ix.Sharing.Exact.Dictionary
public import Ix.Sharing.Exact.Search
public import Ix.Sharing.Exact.Oracle
public import Ix.Sharing.Exact.Uniform
public import Ix.Sharing.Exact.Tiered
public import Ix.Sharing.Exact.TieredFast

public section

namespace Ix.Sharing.Exact

open Ixon

/-- Exact minimum sharing of expanded (Share-free) roots: the width-state
search, a test oracle (the compiler path is `canonicalSharingTiered`). A
`Share` leaf in the input is an error. -/
def optimizeSharing (roots : Array Ixon.Expr) (limits : Limits := {}) :
    Except SharingError ExactSharingResult := do
  let ex ← expand limits #[] roots false
  optimizeExpanded limits ex

/-- Exact minimum sharing (test oracle, `optimizeSharing`) of roots given with
an existing sharing table, which is first expanded logically (backward
references only). -/
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

/-- The exact-minimum sharing of a Constant (test oracle, `optimizeSharing`):
expand its table, optimize, and reassemble the same ConstantInfo, refs and
univs. -/
def normalizeConstantSharing (c : Constant) (limits : Limits := {}) :
    Except SharingError Constant := do
  let r ← optimizeSharingTable c.sharing (constantInfoRoots c.info) limits
  let info ← withRoots c.info r.roots
  return { c with info, sharing := r.sharing }

/-- Outcome of `checkExactMinimum` (Rust `ExactMinimumCheck`). -/
inductive ExactMinimumCheck where
  /-- The Constant is its exact-minimum encoding. -/
  | minimum
  /-- The exact-minimum serialized Constant differs; here are its bytes. -/
  | notMinimum (expected : ByteArray)
  deriving Inhabited

/-- Whether `c` is byte-identical to its exact-minimum sharing: a check
against the test oracle `normalizeConstantSharing`, not against the
compiler's canonical construction (`canonicalSharingTiered`). Rust
`check_exact_minimum`. -/
def checkExactMinimum (c : Constant) (limits : Limits := {}) :
    Except SharingError ExactMinimumCheck := do
  let n ← normalizeConstantSharing c limits
  let expected := serConstant n
  return if serConstant c == expected then .minimum else .notMinimum expected

/-- Bytes of `c`'s serialization that do not depend on sharing: everything
except the expression roots, the sharing count and the table bodies. Then
`(serConstant c).size = fixedConstantBytes c + Σ exprSize roots
+ tag0Size c.sharing.size + Σ exprSize c.sharing`. -/
def fixedConstantBytes (c : Constant) : Nat :=
  let roots := constantInfoRoots c.info
  let info := mapRoots (fun _ => Ixon.Expr.var 0) c.info
  (serConstant { c with info, sharing := #[] }).size - roots.size - tag0Size 0

/-- Size profile of a Constant's sharing problem, without running the search
(for corpus measurements). All byte counts are variable bytes: roots, table
count and table bodies. -/
structure SharingProfile where
  /-- Distinct subterms of the expanded roots (`N`). -/
  distinctSubterms : Nat
  /-- Subterms with at least two logical occurrences. -/
  repeated : Nat
  /-- Search candidates after R1 and R2. -/
  candidates : Nat
  /-- Height of the expanded DAG. -/
  height : Nat
  /-- Variable bytes of the unshared encoding. -/
  unsharedBytes : Nat
  /-- Variable bytes of the input encoding as stored. -/
  inputBytes : Nat
  deriving Repr, Inhabited

/-- Expand `c` and report its sharing-problem profile. -/
def sharingProfile (c : Constant) (limits : Limits := {}) :
    Except SharingError SharingProfile := do
  let roots := constantInfoRoots c.info
  let ex ← expand limits c.sharing roots true
  let p := Prep.ofDag ex.dag
  let occ := occurrences ex.dag ex.roots
  let unshared := tag0Size 0 + rootsCost p.base ex.roots
  return {
    distinctSubterms := ex.dag.size
    repeated := (occ.filter (· ≥ 2)).size
    candidates := (candidateTerms p occ).size
    height := (nodeHeights ex.dag.nodes).foldl max 0
    unsharedBytes := unshared
    inputBytes := tag0Size c.sharing.size + exprsSize c.sharing + exprsSize roots }

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

/-! ## Uniform Share width -/

/-- Exact minimum sharing of Share-free roots when every Share costs `w`
bytes (see `Exact.Uniform`). `result.modelBytes` is the minimum model
length; `result.variableBytes` is the real serialized length of the output. -/
def optimizeSharingUniform (w : Nat) (roots : Array Ixon.Expr) (limits : Limits := {}) :
    Except SharingError UniformSharingResult := do
  let ex ← expand limits #[] roots false
  optimizeUniformExpanded w limits ex

/-- `optimizeSharingUniform` for roots given with an existing sharing table. -/
def optimizeSharingUniformTable (w : Nat) (sharing roots : Array Ixon.Expr)
    (limits : Limits := {}) : Except SharingError UniformSharingResult := do
  let ex ← expand limits sharing roots true
  optimizeUniformExpanded w limits ex

/-- Re-share a Constant with the uniform-width optimum. -/
def normalizeConstantSharingUniform (w : Nat) (c : Constant) (limits : Limits := {}) :
    Except SharingError Constant := do
  let r ← optimizeSharingUniformTable w c.sharing (constantInfoRoots c.info) limits
  let info ← withRoots c.info r.result.roots
  return { c with info, sharing := r.result.sharing }

/-- Reference for the uniform model: the width-state search with every Share
priced `w` (exponential in the candidates; for tests). With `minInDegree2`
it searches the same candidate space as the uniform optimizer. -/
def optimizeSharingUniformReference (w : Nat) (roots : Array Ixon.Expr)
    (limits : Limits := {}) (minInDegree2 : Bool := false) :
    Except SharingError ExactSharingResult := do
  let ex ← expand limits #[] roots false
  optimizeExpanded limits ex (some w) minInDegree2

/-! ## Tiered construction -/

/-- Tiered canonical sharing of Share-free roots under a Share layout: the
fewest final layout bytes over the phase-1 widths 1, 2, 3 (see
`Exact.Tiered` for the claim of each phase). This is the compiler's sharing
(`Ix.CompileM.buildConstantWithSharing`). -/
def canonicalSharingTiered (layout : ShareLayout) (roots : Array Ixon.Expr)
    (limits : Limits := {}) : Except SharingError TieredSharingResult := do
  let ex ← expand limits #[] roots false
  canonicalTieredExpanded layout limits ex

/-- `canonicalSharingTiered` for roots given with an existing sharing table. -/
def canonicalSharingTieredTable (layout : ShareLayout) (sharing roots : Array Ixon.Expr)
    (limits : Limits := {}) : Except SharingError TieredSharingResult := do
  let ex ← expand limits sharing roots true
  canonicalTieredExpanded layout limits ex

/-- Re-share a Constant with the tiered construction. -/
def normalizeConstantSharingTiered (layout : ShareLayout) (c : Constant)
    (limits : Limits := {}) : Except SharingError Constant := do
  let r ← canonicalSharingTieredTable layout c.sharing (constantInfoRoots c.info) limits
  let info ← withRoots c.info r.result.roots
  return { c with info, sharing := r.result.sharing }

end Ix.Sharing.Exact

end
