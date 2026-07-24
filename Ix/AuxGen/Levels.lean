/-
  Ix.AuxGen.Levels: the pure level-arithmetic suite for auxiliary
  generation.

  Port of the pure `Level` half of Rust
  `crates/compile/src/compile/aux_gen/below.rs` (lines 1311-1788): the
  normalizing `max` (`level_max`), the mirror of Lean's `Level.normalize`
  (`level_normalize`, `refs/lean4/src/Lean/Level.lean:379-401`) with all
  its helpers, plus the tiny `PProd`/`PUnit` expression builders that the
  `.below` generators construct field types with.

  NOT here: `kuniv_to_level` (below.rs:1689) and everything else touching
  `ix_kernel::` types — that is the kernel-bridge milestone — and none of
  the below-constant generation logic.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Level.mkMax`, `Expr.mkApp`, ...)
  so the embedded blake3 hashes stay bit-identical with the Rust compiler.
  The `Ix.Environment` constructors are RAW (no simplification), exactly
  like Rust `Level::max` / `Level::succ` — all smart behavior lives in the
  functions below.
-/
module

public import Ix.Environment
public import Ix.AuxGen.ExprUtils

public section

namespace Ix.AuxGen

/-! ## Level predicates and offset helpers (aux_gen/below.rs:1341) -/

/-- Mirrors Rust `is_explicit` (aux_gen/below.rs:1343).

    Whether a level is an explicit numeric constant (a Succ-chain over
    Zero). Matches Lean's `Level.isExplicit`. Reuses ExprUtils'
    `levelExplicitOffset` (common/src/env.rs:434), which recognizes
    exactly the same `Succ^n(Zero)` shape. -/
def isExplicit (l : Level) : Bool :=
  (levelExplicitOffset l).isSome

/-- Mirrors Rust `get_offset` (aux_gen/below.rs:1352).

    Count the outermost Succ wrappers. Matches Lean's `Level.getOffset`.
    Identical semantics to the second component of ExprUtils'
    `levelPeelSucc` (common/src/env.rs:424) — reused rather than
    re-implemented, kept under the below.rs-derived name so the port
    reads 1:1 against the Rust. -/
def getOffset (l : Level) : Nat :=
  (levelPeelSucc l).2

/-- Mirrors Rust `get_level_offset` (aux_gen/below.rs:1360).

    Strip all outermost Succ wrappers. Matches Lean's
    `Level.getLevelOffset`. Identical semantics to the first component of
    ExprUtils' `levelPeelSucc` — same reuse note as `getOffset`. -/
def getLevelOffset (l : Level) : Level :=
  (levelPeelSucc l).1

/-- Mirrors Rust `level_subsumes` (aux_gen/below.rs:1374).

    Check whether `u` subsumes `v` (i.e., `u >= v` for all parameter
    assignments). Matches the `subsumes` local in Lean's `mkLevelMaxCore`.

    Two cases:
    1. `v` is an explicit numeric (Succ-chain over Zero) and `u` has at
       least as many Succ wrappers — the base of `u` is always >= 0.
    2. `u = max(u1, u2)` and `v` equals one of the direct children. -/
def levelSubsumes (u v : Level) : Bool := Id.run do
  if isExplicit v && getOffset u >= getOffset v then
    return true
  if let .max u1 u2 _ := u then
    return v == u1 || v == u2
  return false

/-! ## Smart max (aux_gen/below.rs:1384) -/

/-- Mirrors Rust `level_max` (aux_gen/below.rs:1391).

    Normalizing `max` for universe levels, matching Lean's
    `mkLevelMaxCore` / `mkLevelMax'` (`refs/lean4/src/Lean/Level.lean:516-534`).

    Applies cheap simplifications beyond zero-elimination and equality:
    - Subsumption: `max(max(a, b), a) = max(a, b)` (one-level subtree check)
    - Explicit absorption: `max(succ(u), 1) = succ(u)` when
      `offset(succ(u)) >= 1`
    - Same-base offset: `max(succ(succ(u)), succ(u)) = succ(succ(u))`

    NOTE: deliberately distinct from ExprUtils' `levelMaxSmart`
    (`Level::max_smart`, common/src/env.rs:356) — that one mirrors the
    kernel's `KUniv::max` and lacks the explicit-absorption case (e.g.
    `max 1 (succ u)` stays a `Max` node there but collapses to `succ u`
    here), and its checks run in a different order. -/
def levelMax (a b : Level) : Level := Id.run do
  if a == b then
    return a
  if let .zero _ := a then
    return b
  if let .zero _ := b then
    return a
  if levelSubsumes a b then
    return a
  if levelSubsumes b a then
    return b
  -- Same base (after stripping Succs), different offsets: keep the larger.
  if getLevelOffset a == getLevelOffset b then
    return if getOffset a >= getOffset b then a else b
  return Level.mkMax a b

/-- Mirrors Rust `mk_level_succ` (aux_gen/below.rs:1332).

    Compute `Succ(l)`, distributing over `Max`/`IMax` to match Lean's
    `mkLevelSucc`:

      `mkLevelSucc(Max(a, b))  = Max(mkLevelSucc(a), mkLevelSucc(b))`
      `mkLevelSucc(IMax(a, b)) = Max(mkLevelSucc(a), mkLevelSucc(b))`
      `mkLevelSucc(l)          = Succ(l)`  (otherwise)

    Used to compute the sort level of `PProd.{u, v}` applications
    (`Sort (max 1 u v)`). Note: for recursor elimination levels (e.g.,
    the `.below` value's `I.rec.{succ(rlvl)}`), use `Level.mkSucc`
    directly instead — Lean's elaborator does NOT distribute there.

    (Defined after `levelMax` — its callee — instead of at its Rust
    source position before it; no semantic difference.) -/
partial def mkLevelSucc (l : Level) : Level :=
  match l with
  | .max a b _ | .imax a b _ => levelMax (mkLevelSucc a) (mkLevelSucc b)
  | _ => Level.mkSucc l

/-! ## Normalization helpers (aux_gen/below.rs:1481) -/

/-- Mirrors Rust `is_already_normalized_cheap` (aux_gen/below.rs:1482).
    Quick check: `l` is already in `Succ*(Param|MVar|Zero)` form. -/
partial def isAlreadyNormalizedCheap (l : Level) : Bool :=
  match l with
  | .zero _ | .param _ _ | .mvar _ _ => true
  | .succ inner _ => isAlreadyNormalizedCheap inner
  | _ => false

/-- Mirrors Rust `add_offset` (aux_gen/below.rs:1491).
    Add `k` `Succ` wrappers to `l`. Matches Lean's `Level.addOffset`. -/
def addOffset (l : Level) (k : Nat) : Level := Id.run do
  let mut cur := l
  for _ in [0:k] do
    cur := Level.mkSucc cur
  return cur

/-- Mirrors Rust `is_never_zero` (aux_gen/below.rs:1502).

    Recognize `Level.isNeverZero`: `l` is provably non-zero for every
    parameter assignment. Matches the kernel's `isNeverZero` check used by
    `mkLevelIMax` to decide whether `imax a b` collapses to `max a b`. -/
partial def isNeverZero (l : Level) : Bool :=
  match l with
  | .succ _ _ => true
  | .max a b _ => isNeverZero a || isNeverZero b
  | .imax _ b _ => isNeverZero b
  | _ => false

/-- Mirrors Rust `ctor_to_nat` (aux_gen/below.rs:1530).

    Constructor tag for total-order tie-breaking in `normLt`. Matches
    Lean's `Level.ctorToNat`; MVar gets slot 2 so our numbering lines up
    even though MVars should never survive to the aux_gen output. -/
def ctorToNat (l : Level) : Nat :=
  match l with
  | .zero _ => 0
  | .param _ _ => 1
  | .mvar _ _ => 2
  | .succ _ _ => 3
  | .max _ _ _ => 4
  | .imax _ _ _ => 5

/-- Mirrors Rust `norm_lt_aux` (aux_gen/below.rs:1548).

    The name comparison mirrors Rust `n1.pretty() < n2.pretty()`:
    `Ix.Name.pretty` is a byte-for-byte mirror of Rust `Name::pretty`
    (Environment.lean:114-125), and Lean `String <` (code-point
    lexicographic) agrees with Rust `String` `Ord` (UTF-8 byte
    lexicographic) because UTF-8 byte order preserves code-point order. -/
partial def normLtAux (l1 : Level) (k1 : Nat) (l2 : Level) (k2 : Nat) : Bool :=
  -- Float Succ offsets into `k1`/`k2`.
  if let .succ inner _ := l1 then
    normLtAux inner (k1 + 1) l2 k2
  else if let .succ inner _ := l2 then
    normLtAux l1 k1 inner (k2 + 1)
  else
    -- Equal-kind recursion for Max / IMax.
    match l1, l2 with
    | .max a1 a2 _, .max b1 b2 _
    | .imax a1 a2 _, .imax b1 b2 _ =>
      if l1 == l2 then
        decide (k1 < k2)
      else if a1 != b1 then
        normLtAux a1 0 b1 0
      else
        normLtAux a2 0 b2 0
    | .param n1 _, .param n2 _ =>
      if n1 == n2 then
        decide (k1 < k2)
      else
        -- Lean uses lexicographic `Name.lt`; we approximate with the
        -- pretty-printed form. Name equality comparisons we care about
        -- are for same-declaration level params whose pretty names are
        -- already unique strings.
        decide (n1.pretty < n2.pretty)
    | _, _ =>
      if l1 == l2 then
        decide (k1 < k2)
      else
        decide (ctorToNat l1 < ctorToNat l2)

/-- Mirrors Rust `norm_lt` (aux_gen/below.rs:1544).

    Total order on levels used to sort `max` children during
    normalization. Matches Lean's `normLt` / `normLtAux`, with `Succ`
    offsets floated into an accumulator so that `succ^n(x)` and
    `succ^m(x)` compare by `(x, n)`. -/
def normLt (a b : Level) : Bool :=
  normLtAux a 0 b 0

/-! ## Stable sort by `normLt` (aux_gen/below.rs:1446)

Rust `level_normalize` sorts the flattened `max` arguments with
`lvls.sort_by(...)` — `slice::sort_by` is documented STABLE, and the
comparator returns `Ordering::Equal` whenever neither `norm_lt(a, b)` nor
`norm_lt(b, a)` holds, so tied elements keep their original relative
order. Lean's `Array.qsort` is NOT stable, so we hand-roll a top-down
stable merge sort: the merge takes from the left run unless the right
head is strictly `normLt`-smaller, which is exactly the tie behavior of a
stable sort under that comparator. Any two stable sorts agree elementwise
for a strict-weak-order comparator, so this is bit-identical to the Rust
`sort_by` output. (`normLt` is a strict weak order on MVar-free input;
MVars never reach aux_gen levels — see `ctorToNat`.) -/

/-- Stable merge of two `normLt`-sorted runs; left-biased on ties. -/
partial def normLtMerge : List Level → List Level → List Level
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if normLt y x then
      y :: normLtMerge (x :: xs) ys
    else
      x :: normLtMerge xs (y :: ys)

/-- Stable top-down merge sort by `normLt`. -/
partial def normLtMergeSort : List Level → List Level
  | [] => []
  | [x] => [x]
  | xs =>
    let n := xs.length / 2
    normLtMerge (normLtMergeSort (xs.take n)) (normLtMergeSort (xs.drop n))

/-- Mirrors the Rust `lvls.sort_by(|a, b| ...)` call in `level_normalize`
    (aux_gen/below.rs:1446-1454). See the section comment for the
    stability argument. -/
def sortByNormLt (lvls : Array Level) : Array Level :=
  (normLtMergeSort lvls.toList).toArray

/-- Mirrors Rust `skip_explicit` (aux_gen/below.rs:1592).

    Returns the index of the first level in `lvls` that isn't an explicit
    numeral (`succ^n(zero)`). Used to locate the split point in the sorted
    `max`-argument list. -/
def skipExplicit (lvls : Array Level) (start : Nat) : Nat := Id.run do
  let mut i := start
  repeat
    if i < lvls.size then
      match getLevelOffset lvls[i]! with
      | .zero _ => i := i + 1
      | _ => break
    else
      break
  return i

/-- Mirrors Rust `is_explicit_subsumed` (aux_gen/below.rs:1604).

    True when the largest explicit numeral in `lvls[..firstNonExplicit]`
    is <= the offset of some non-explicit level (which therefore
    dominates). -/
def isExplicitSubsumed (lvls : Array Level) (firstNonExplicit : Nat) : Bool :=
  Id.run do
    if firstNonExplicit == 0 then
      return false
    let maxExplicit := getOffset lvls[firstNonExplicit - 1]!
    let mut i := firstNonExplicit
    repeat
      if i < lvls.size then
        if getOffset lvls[i]! >= maxExplicit then
          return true
        i := i + 1
      else
        break
    return false

/-- Mirrors Rust `acc_max` (aux_gen/below.rs:1622).

    `accMax result prev offset`: wrap `prev` in `offset` Succs then `max`
    it into `result` (treating `zero` as identity). Used by `mkMaxAux` to
    accumulate distinct base-levels while re-adding the stripped offset.
    Builds a RAW `Max` node (Rust `Level::max`), not `levelMax`. -/
def accMax (result : Level) (prev : Level) (offset : Nat) : Level :=
  let p := addOffset prev offset
  match result with
  | .zero _ => p
  | _ => Level.mkMax result p

/-- Mirrors Rust `mk_max_aux` (aux_gen/below.rs:1634).

    Scan the sorted `lvls` and combine same-base-level items by their max
    offset, producing a right-combined `max` chain + the stripped outer
    offset `extraK`. Matches Lean's `mkMaxAux`. -/
def mkMaxAux (lvls : Array Level) (extraK : Nat) (start : Nat)
    (initPrev : Level) (initPrevK : Nat) (initResult : Level) : Level := Id.run do
  let mut i := start
  let mut prev := initPrev
  let mut prevK := initPrevK
  let mut result := initResult
  repeat
    if i < lvls.size then
      let lvl := lvls[i]!
      let curr := getLevelOffset lvl
      let currK := getOffset lvl
      if curr == prev then
        prev := curr
        prevK := Nat.max prevK currK
      else
        result := accMax result prev (extraK + prevK)
        prev := curr
        prevK := currK
      i := i + 1
    else
      break
  return accMax result prev (extraK + prevK)

/-- Mirrors Rust `mk_imax_aux` (aux_gen/below.rs:1666).

    `mkIMaxAux`: build `imax l1 l2` with the kernel's cheap rewrites. Used
    by `levelNormalize` for the `imax` case where `l2` isn't provably
    non-zero (otherwise the outer branch collapses `imax` to `max`). -/
def mkImaxAux (l1 l2 : Level) : Level := Id.run do
  if let .zero _ := l2 then
    return Level.mkZero
  if let .zero _ := l1 then
    return l2
  if let .succ inner _ := l1 then
    if let .zero _ := inner then
      return l2
  if l1 == l2 then
    return l1
  return Level.mkIMax l1 l2

/-! ## Normalization (aux_gen/below.rs:1414) -/

mutual

/-- Mirrors Rust `level_normalize` (aux_gen/below.rs:1435).

    Normalizing level rewrite, mirroring Lean's `Level.normalize`
    (`refs/lean4/src/Lean/Level.lean:379-401`). Applied by
    `inferForallType` before returning the sort of a forall type, so any
    level reported by `getLevel` on a forall-typed expression is already
    in this canonical form. Without it, our level tree stays in
    `mkLevelMax'` / `mkLevelIMax'` local-simp form — semantically
    equivalent, but with structurally different `max`/`Succ` nestings
    that break hash-level equality against the original Lean-produced
    aux_gen constants.

    The algorithm:
      1. If already in `Succ*(Param|MVar|Zero)` shape, return as-is.
      2. Strip the outer offset `k`.
      3. For `max l1 l2`: flatten to a list of recursively-normalized
         atoms, sort with `normLt`, drop explicit numerals that are
         subsumed by a larger non-explicit offset, rebuild with `mkMaxAux`
         combining same-base-level items by their max offset, and finally
         re-add `k`.
      4. For `imax l1 l2`:
         - if `l2` is never zero, normalize `max l1 l2` and add `k`.
         - else normalize each side separately and rebuild via
           `mkImaxAux`, then add `k`. -/
partial def levelNormalize (l : Level) : Level :=
  if isAlreadyNormalizedCheap l then
    l
  else
    let k := getOffset l
    let u := getLevelOffset l
    match u with
    | .max l1 l2 _ => Id.run do
      let mut lvls : Array Level := #[]
      lvls := getMaxArgsAux l1 false lvls
      lvls := getMaxArgsAux l2 false lvls
      lvls := sortByNormLt lvls
      let firstNonExplicit := skipExplicit lvls 0
      -- Rust `saturating_sub(1)`; Nat subtraction saturates at 0 already.
      let i := if isExplicitSubsumed lvls firstNonExplicit then
          firstNonExplicit
        else
          firstNonExplicit - 1
      -- `i` is always in bounds: `lvls` has >= 2 entries (each
      -- `getMaxArgsAux` call pushes at least one), and
      -- `isExplicitSubsumed` returning true forces
      -- `firstNonExplicit < lvls.size`.
      let lvl1 := lvls[i]!
      let prev := getLevelOffset lvl1
      let prevK := getOffset lvl1
      return mkMaxAux lvls k (i + 1) prev prevK Level.mkZero
    | .imax l1 l2 _ =>
      if isNeverZero l2 then
        -- RAW `Max` node (Rust `Level::max`), normalized as a whole.
        let m := Level.mkMax l1 l2
        addOffset (levelNormalize m) k
      else
        let l1n := levelNormalize l1
        let l2n := levelNormalize l2
        addOffset (mkImaxAux l1n l2n) k
    -- Zero / Param: already normalized.
    | _ => l

/-- Mirrors Rust `get_max_args_aux` (aux_gen/below.rs:1514).

    Flatten a nested `max` tree, recursively normalizing any sub-term
    that isn't yet known to be normalized. Matches Lean's `getMaxArgsAux`
    with `normalize` as the recursive normalizer. The Rust
    `&mut Vec<Level>` out-parameter becomes pass-in/return of `out`. -/
partial def getMaxArgsAux (l : Level) (alreadyNormalized : Bool)
    (out : Array Level) : Array Level :=
  match l with
  | .max l1 l2 _ =>
    let out := getMaxArgsAux l1 alreadyNormalized out
    getMaxArgsAux l2 alreadyNormalized out
  | _ =>
    if alreadyNormalized then
      out.push l
    else
      getMaxArgsAux (levelNormalize l) true out

end

/-! ## PProd / PUnit builders (aux_gen/below.rs:1714) -/

/-- Mirrors Rust `mk_pprod` (aux_gen/below.rs:1718).

    Build `PProd.{u, v} a b` with separate universe levels for each
    component. Matches Lean's `mkPProd` which infers levels from the
    actual types. Callers should compute `lvl1` from `a`'s sort level and
    `lvl2` from `b`'s sort level. -/
def mkPProd (lvl1 lvl2 : Level) (a b : Expr) : Expr :=
  let pprod := Expr.mkConst (Name.mkStr .mkAnon "PProd") #[lvl1, lvl2]
  Expr.mkApp (Expr.mkApp pprod a) b

/-- Mirrors Rust `punit_const` (aux_gen/below.rs:1732).
    Build `PUnit.{u}` (the type, at `Sort (u+1)`). -/
def punitConst (lvl : Level) : Expr :=
  Expr.mkConst (Name.mkStr .mkAnon "PUnit") #[lvl]

/-- Mirrors Rust `mk_pprod_mk` (aux_gen/below.rs:1740).
    Build `PProd.mk.{u, v} type_a type_b val_a val_b`. -/
def mkPProdMk (lvlU lvlV : Level) (typeA typeB valA valB : Expr) : Expr :=
  let pprodMk := Expr.mkConst
    (Name.mkStr (Name.mkStr .mkAnon "PProd") "mk") #[lvlU, lvlV]
  Expr.mkApp
    (Expr.mkApp (Expr.mkApp (Expr.mkApp pprodMk typeA) typeB) valA)
    valB

/-- Mirrors Rust `mk_punit_unit` (aux_gen/below.rs:1762).
    Build `PUnit.unit.{u}` (the term, not the type). -/
def mkPUnitUnit (lvl : Level) : Expr :=
  Expr.mkConst (Name.mkStr (Name.mkStr .mkAnon "PUnit") "unit") #[lvl]

/-- Mirrors Rust `replace_result_sort_with_prop` (aux_gen/below.rs:1777).

    Replace the result sort of a forall chain with `Sort 0` (Prop).
    Given `∀ (x1 : A1) ... (xn : An), Sort u`, returns
    `∀ (x1 : A1) ... (xn : An), Prop`.

    Used when extracting motive domains from the recursor type for
    Prop-level `.below` inductives. The recursor may have large
    elimination (extra `u` param), but `.below` motives always target
    Prop. -/
partial def replaceResultSortWithProp (expr : Expr) : Expr :=
  match expr with
  | .forallE name dom body bi _ =>
    Expr.mkForallE name dom (replaceResultSortWithProp body) bi
  | .sort _ _ => Expr.mkSort Level.mkZero
  | _ => expr

end Ix.AuxGen

end
