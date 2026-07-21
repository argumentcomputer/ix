/-
  Ix.AuxGen.Surgery: call-site surgery — PLAN COMPUTATION half.

  Port of the plan-computation half of
  `crates/compile/src/compile/surgery.rs`.

  When `sort_consts` reorders or collapses mutual inductives into
  equivalence classes, the aux-gen pipeline regenerates auxiliaries
  (`.rec`, `.below`, `.brecOn`, …) with canonical argument ordering.
  User-written Lean code calling these auxiliaries still has arguments in
  source order. This module provides:

  1. `CallSitePlan`: per-auxiliary surgery plan describing how source-order
     motive/minor arguments map to canonical positions (permutation + keep
     mask), with an optional `AuxHeadRewrite` for evaporated aux recursors.
  2. Telescope utilities: `collectLeanTelescope` / `collectIxonTelescope`.
  3. Plan computation: `computeCallSitePlans` derives plans from the
     canonical class ordering and the original Lean recursor structure.
  4. The shared signature extractor `auxMotiveSigs` and the head-rewrite
     derivation `deriveHeadRewriteApp`.

  The surgery plan differs per original recursor name: for mutual `[A, B]`
  where `A ~ B`, `A.rec` keeps `motive_A` while `B.rec` keeps `motive_B`,
  because each recursor's result type uses the motive for its "self" type.

  NOT ported here — the CONSUMPTION half (call-site expression rewriting
  applied by compile.rs's `compile_expr` arms), a later milestone:

  - `adapt_split_minor`        (surgery.rs:834) — wraps a kept source minor
    in a lambda that synthesizes IHs for fields targeting other SCCs;
  - `source_ctor_for_minor`    (surgery.rs:942) — source minor index →
    `(sourcePos, ConstructorVal)` across user + aux minor bands;
  - `source_minor_type`        (surgery.rs:1168) — instantiated type of the
    `srcMinorIdx`-th minor binder of a source recursor;
  - `peel_binders`             (surgery.rs:1197) — open `n` foralls into
    fresh-FVar `LocalDecl`s;
  - `SourceRecTarget` / `find_source_rec_target` (surgery.rs:1226/1233) —
    detect a minor field whose type targets a source (or aux) inductive;
  - `synthesize_external_ih`   (surgery.rs:1306) — build the recursive-call
    IH for an out-of-block target;
  - `dump_plan_state`          (surgery.rs:1354) — `IX_SURGERY_DUMP` gated
    stderr diagnostic (env-var debug blocks are not ported, matching the
    `IX_RECURSOR_DUMP` precedent in `Ix.AuxGen.Nested`).

  Those consumers will need `auxMotiveSigs` / `AuxMotiveSig`,
  `deriveHeadRewriteApp`, and the telescope collectors ported below.

  Environment access: Rust threads `lean_env: &LeanEnv`; the Lean port
  reads the base compile environment via `lookupConst?` (CompileM), the
  same view `generate_aux_patches` hands the Rust generator.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Name.mkStr`, ...)
  so the embedded blake3 hashes stay bit-identical with the Rust compiler.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public import Ix.CompileM
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Nested
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-! ## Plan data model (surgery.rs:50-175)

Declaration order deviation: Rust declares `CallSitePlan` (surgery.rs:56)
before `AuxHeadRewrite` (surgery.rs:101); Lean needs the dependency
first. Field-for-field identical. -/

/-- Head-rewrite directive carried by `CallSitePlan.headRewrite`.
    Mirrors Rust `AuxHeadRewrite` (surgery.rs:101). -/
structure AuxHeadRewrite where
  /-- The external inductive's recursor (the alias target, e.g. `List.rec`). -/
  targetRec : Name
  /-- Source motive position of the evaporated aux (`nUserMotives + j`). -/
  targetMotivePos : Nat
  deriving Repr, Nonempty, Inhabited

/-- Per-auxiliary surgery plan for call-site argument reordering.

    Computed per original recursor name (not per equivalence class),
    because the choice of which collapsed motive to keep depends on which
    member of the equivalence class the recursor "belongs to".
    Mirrors Rust `CallSitePlan` (surgery.rs:56). -/
structure CallSitePlan where
  /-- Number of parameters (unchanged between source and canonical). -/
  nParams : Nat
  /-- Source-order motive count (from original `rec.all.size`). -/
  nSourceMotives : Nat
  /-- Source-order minor count. -/
  nSourceMinors : Nat
  /-- Number of indices (between minors and major premise). -/
  nIndices : Nat
  /-- `keep[i]`: true if source motive `i` survives collapse.
      For `A.rec`, `keep[A_pos]` = true. For `B.rec`, `keep[B_pos]` = true. -/
  motiveKeep : Array Bool
  /-- `keep[i]`: true if source minor `i` survives collapse. -/
  minorKeep : Array Bool
  /-- `sourceToCanonMotive[i]` = canonical position of source motive `i`.
      Collapsed positions share the canonical index of their representative. -/
  sourceToCanonMotive : Array Nat
  /-- Same for minors. -/
  sourceToCanonMinor : Array Nat
  /-- `true` when the source motive belongs to this canonical SCC.

      Source recursor types use Lean's original `all` block, but canonical
      recursors are generated per minimal SCC. A source motive can
      therefore be present in the source telescope while absent from this
      canonical block. Call-site minor adaptation uses this bit to
      distinguish "canonical recursor supplies an IH binder" from "the IH
      must be synthesized by a recursive call into another canonical
      block". -/
  sourceInBlock : Array Bool
  /-- `some` when the callee is an EVAPORATED aux recursor — a
      `<all0>.rec_N` whose nested occurrence lost every spec-param
      inductive to another SCC. Its claim is aliased to the external
      inductive's own recursor (see the evaporated-aux alias pass in
      `aux_gen.rs`), so the call spine must be rebuilt onto that
      telescope:

        source: params… motives… minors… indices… major   (over-merged)
        target: specs…  motive   minors′… indices… major  (external rec)

      The spec args and extended level list are derived at the apply site
      from the source recursor's type instantiated with the call-site args
      (`deriveHeadRewriteApp`). -/
  headRewrite : Option AuxHeadRewrite
  deriving Repr, Nonempty, Inhabited

namespace CallSitePlan

/-- Number of canonical (kept) motives.
    Mirrors Rust `CallSitePlan::n_canonical_motives` (surgery.rs:110). -/
def nCanonicalMotives (plan : CallSitePlan) : Nat :=
  plan.motiveKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Number of canonical (kept) minors.
    Mirrors Rust `CallSitePlan::n_canonical_minors` (surgery.rs:115). -/
def nCanonicalMinors (plan : CallSitePlan) : Nat :=
  plan.minorKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Total canonical args in the telescope (params + kept motives + kept
    minors + indices + 1 major).
    Mirrors Rust `CallSitePlan::n_canonical_args` (surgery.rs:120). -/
def nCanonicalArgs (plan : CallSitePlan) : Nat :=
  plan.nParams
    + plan.nCanonicalMotives
    + plan.nCanonicalMinors
    + plan.nIndices
    + 1 -- major premise

/-- Whether this plan is an identity (no reordering, no collapse).
    Mirrors Rust `CallSitePlan::is_identity` (surgery.rs:129). -/
def isIdentity (plan : CallSitePlan) : Bool :=
  plan.headRewrite.isNone
    && plan.motiveKeep.all (fun k => k)
    && plan.minorKeep.all (fun k => k)
    && plan.sourceToCanonMotive.zipIdx.all (fun (c, i) => c == i)
    && plan.sourceToCanonMinor.zipIdx.all (fun (c, i) => c == i)

end CallSitePlan

/-- Call-site surgery plan for `.brecOn` / `.brecOn_N`.

    `.rec` telescope layout is:
    `params, motives, minors, indices, major`.

    `.brecOn` telescope layout is:
    `params, motives, indices, major, handlers`, with one handler per
    motive. The motive permutation/drop decision is the same as the
    corresponding recursor plan, and the handlers mirror that motive
    layout. Mirrors Rust `BRecOnCallSitePlan` (surgery.rs:148). -/
structure BRecOnCallSitePlan where
  nParams : Nat
  nSourceMotives : Nat
  nIndices : Nat
  motiveKeep : Array Bool
  sourceToCanonMotive : Array Nat
  deriving Repr, Nonempty, Inhabited

namespace BRecOnCallSitePlan

/-- Mirrors Rust `BRecOnCallSitePlan::from_rec_plan` (surgery.rs:157). -/
def fromRecPlan (plan : CallSitePlan) : BRecOnCallSitePlan :=
  { nParams := plan.nParams
    nSourceMotives := plan.nSourceMotives
    nIndices := plan.nIndices
    motiveKeep := plan.motiveKeep
    sourceToCanonMotive := plan.sourceToCanonMotive }

/-- Mirrors Rust `BRecOnCallSitePlan::n_canonical_motives` (surgery.rs:167). -/
def nCanonicalMotives (plan : BRecOnCallSitePlan) : Nat :=
  plan.motiveKeep.foldl (fun acc k => if k then acc + 1 else acc) 0

/-- Mirrors Rust `BRecOnCallSitePlan::is_identity` (surgery.rs:171). -/
def isIdentity (plan : BRecOnCallSitePlan) : Bool :=
  plan.motiveKeep.all (fun k => k)
    && plan.sourceToCanonMotive.zipIdx.all (fun (c, i) => c == i)

end BRecOnCallSitePlan

/-- Mirrors Rust `rec_name_to_brecon_name` (surgery.rs:177).
    `X.rec → X.brecOn`, `X.rec_N → X.brecOn_N`, otherwise `none`. -/
def recNameToBreconName (name : Name) : Option Name :=
  match name with
  | .str parent s _ =>
    if s == "rec" then
      some (Name.mkStr parent "brecOn")
    else if s.startsWith "rec_" then
      some (Name.mkStr parent s!"brecOn_{s.drop 4}")
    else
      none
  | _ => none

/-- Mirrors Rust `rec_name_to_below_name` (surgery.rs:189).
    `X.rec → X.below`, `X.rec_N → X.below_N`, otherwise `none`. -/
def recNameToBelowName (name : Name) : Option Name :=
  match name with
  | .str parent s _ =>
    if s == "rec" then
      some (Name.mkStr parent "below")
    else if s.startsWith "rec_" then
      some (Name.mkStr parent s!"below_{s.drop 4}")
    else
      none
  | _ => none

/-! ## Telescope utilities (surgery.rs:201) -/

/-- Mirrors Rust `collect_lean_telescope` (surgery.rs:208).

    Collect a Lean App telescope: peel App nodes to get
    `(head, #[a1, ..., aN])`, arguments in application order (leftmost
    first). Same walk as `decomposeApps` (Rust keeps both — surgery.rs's
    reference-based collector and expr_utils' owned `decompose_apps`);
    the Lean port delegates so the two can never drift. -/
def collectLeanTelescope (e : Expr) : Expr × Array Expr :=
  decomposeApps e

/-- Mirrors Rust `collect_ixon_telescope` (surgery.rs:225).

    Collect an Ixon App telescope: peel App nodes to get
    `(head, #[a1, ..., aN])`, arguments in application order (leftmost
    first). -/
def collectIxonTelescope (e : Ixon.Expr) : Ixon.Expr × Array Ixon.Expr :=
  Id.run do
    let mut args : Array Ixon.Expr := #[]
    let mut cur := e
    repeat
      match cur with
      | .app f a =>
        args := args.push a
        cur := f
      | _ => break
    return (cur, args.reverse)

/-! ## Plan computation (surgery.rs:238)

`PERM_OUT_OF_SCC` (surgery.rs:268, `usize::MAX`) is reused from
`Ix.AuxGen.Nested` — numerically identical to the `u64::MAX` sentinel
stored in serialized `Ixon.AuxLayout.perm` entries. -/

/-- Compute call-site surgery plans for all auxiliary names in a collapsed
    block. Mirrors Rust `compute_call_site_plans` (surgery.rs:270).

    - `sortedClasses`: canonical equivalence classes from `sort_consts`,
      each inner array is a list of inductive names in the class (first =
      representative).
    - `originalAll`: the original `rec.all` list from the Lean recursor
      (source order).
    - `auxLayout`: paired source→canonical aux permutation and
      per-source-position aux ctor counts (`Ixon.AuxLayout`; `u64` fields
      are normalized to `Nat` up front — Rust stores `Vec<usize>`
      serialized as u64, so `usize::MAX ≡ PERM_OUT_OF_SCC` survives
      `.toNat` exactly).

    Returns a map from auxiliary name (e.g. `A.rec`, `B.rec`) to its
    surgery plan. Only produces plans for `.rec` auxiliaries.

    (Rust threads `lean_env: &LeanEnv`; here constructor counts and
    recursor structure are read through `lookupConst?`.)

    Note on "phantom" names: Lean's `all` field on a recursor is the full
    user-written mutual block. SCC analysis may split that block into
    several canonical blocks; in that case `originalAll` legitimately
    contains names that are NOT in the current block's `sortedClasses`.
    Such phantom names get their motive/minors dropped by the surgery
    plan (they belong to a different canonical block which will produce
    its own plan). We skip generating a plan for a phantom `X.rec`
    itself, since that belongs to the block owning `X`.

    (The `IX_SURGERY_DUMP`-gated `dump_plan_state` diagnostic at
    surgery.rs:787-817/1354 is not ported.) -/
def computeCallSitePlans (sortedClasses : Array (Array Name))
    (originalAll : Array Name) (auxLayout : Option Ixon.AuxLayout) :
    CompileM (Std.HashMap Name CallSitePlan) := do
  let mut plans : Std.HashMap Name CallSitePlan := {}
  let nClasses := sortedClasses.size
  let nSource := originalAll.size

  if nSource == 0 || nClasses == 0 then
    return plans

  -- Build name → class index (surgery.rs:284).
  let mut nameToClassM : Std.HashMap Name Nat := {}
  for (cls, ci) in sortedClasses.zipIdx do
    for name in cls do
      nameToClassM := nameToClassM.insert name ci
  let nameToClass := nameToClassM

  -- Per-source-inductive constructor counts, indexed by `originalAll`
  -- position. Only covers USER-visible source inductives; nested-aux
  -- inductives' ctor counts are handled separately below (surgery.rs:292).
  let mut ctorCountsM : Array Nat := #[]
  for n in originalAll do
    match ← lookupConst? n with
    | some (.inductInfo v) => ctorCountsM := ctorCountsM.push v.ctors.size
    | _ => ctorCountsM := ctorCountsM.push 0
  let ctorCounts := ctorCountsM

  -- Read the Lean source recursor's structural info directly. Crucially,
  -- `numMotives` / `numMinors` already include nested-auxiliary counts —
  -- see `IndGroupInfo.numMotives = all.size + numNested` in
  -- `refs/lean4/src/Lean/Elab/PreDefinition/Structural/IndGroupInfo.lean:40`.
  -- Deriving `nSourceMotives` from `originalAll.size` alone would
  -- undercount by `numNested`, which then mis-slices the call telescope
  -- at the consumption site (surgery.rs:303-327).
  let recStructural : Option (Nat × Nat × Nat × Nat) ←
    originalAll.findSomeM? fun n => do
      match ← lookupConst? (Name.mkStr n "rec") with
      | some (.recInfo r) =>
        pure (some (r.numParams, r.numIndices, r.numMotives, r.numMinors))
      | _ => pure none
  let (nParams, nIndices, leanNumMotives, leanNumMinors) :=
    recStructural.getD (0, 0, nSource, ctorCounts.foldl (· + ·) 0)

  -- User vs aux split (surgery.rs:330-338). The user-visible portion has
  -- one motive per `originalAll` entry; anything beyond is a nested-aux
  -- motive (e.g. `Array Alt`'s motive for LCNF).
  let nUserMotives := nSource
  let nSourceMotives := Nat.max leanNumMotives nUserMotives
  let nSourceAuxMotives := nSourceMotives - nUserMotives
  let nUserMinors : Nat := ctorCounts.foldl (· + ·) 0
  let nSourceMinors := Nat.max leanNumMinors nUserMinors
  let nAuxMinors := nSourceMinors - nUserMinors
  -- Normalize serialized u64 layout fields to Nat once.
  let layoutNat : Option (Array Nat × Array Nat) := auxLayout.map fun l =>
    (l.perm.map (·.toNat), l.sourceCtorCounts.map (·.toNat))
  let auxPerm : Option (Array Nat) := layoutNat.map (·.1)

  -- When a perm is present, the canonical aux count comes from it — and an
  -- all-out-of-SCC perm means ZERO canonical auxes (every source aux
  -- evaporated with the SCC split), not the source count (surgery.rs:341).
  let auxCanonicalCount : Nat :=
    match auxPerm with
    | none => nSourceAuxMotives
    | some p => p.foldl (init := 0) fun acc c =>
        if c != PERM_OUT_OF_SCC then Nat.max acc (c + 1) else acc

  -- surgery.rs:353: perm entry `PERM_OUT_OF_SCC` → none; present entry →
  -- that canonical index; absent perm (or index past its end) → identity.
  let auxCanonOfSource : Nat → Option Nat := fun sourceAuxJ =>
    match auxPerm.bind fun p => p[sourceAuxJ]? with
    | some c => if c == PERM_OUT_OF_SCC then none else some c
    | none => some sourceAuxJ

  -- Representative source aux for each canonical aux class
  -- (surgery.rs:362-374). Under aux-alpha-collapse, multiple Lean-source
  -- `_N`s can point at the same canonical aux slot; keep the FIRST.
  -- Sentinel is Rust `usize::MAX`, numerically `PERM_OUT_OF_SCC`.
  let mut auxReprForCanonM : Array Nat :=
    Array.replicate auxCanonicalCount PERM_OUT_OF_SCC
  for sourceAuxJ in [0:nSourceAuxMotives] do
    if let some canonI := auxCanonOfSource sourceAuxJ then
      if canonI < auxReprForCanonM.size then
        if auxReprForCanonM[canonI]! == PERM_OUT_OF_SCC then
          auxReprForCanonM := auxReprForCanonM.set! canonI sourceAuxJ
  let auxReprForCanon := auxReprForCanonM

  -- surgery.rs:390: phantom = user motive whose name is not in this
  -- block's classes; aux motives are never phantom.
  let isPhantom : Array Bool := (Array.range nSourceMotives).map fun srcI =>
    if srcI < nUserMotives then
      !(nameToClass.contains originalAll[srcI]!)
    else
      false
  -- surgery.rs:399.
  let sourceInBlock : Array Bool := (Array.range nSourceMotives).map fun srcI =>
    if srcI < nUserMotives then
      !isPhantom[srcI]!
    else
      (auxCanonOfSource (srcI - nUserMotives)).isSome
  -- surgery.rs:408: user motives map through `nameToClass` (placeholder 0
  -- for phantoms — consumers only read it when motiveKeep is true); aux
  -- motives map into the aux band after the user classes.
  let sourceToCanonMotive : Array Nat :=
    (Array.range nSourceMotives).map fun srcI =>
      if srcI < nUserMotives then
        (nameToClass.get? originalAll[srcI]!).getD 0
      else
        match auxCanonOfSource (srcI - nUserMotives) with
        | some canonAuxI => nClasses + canonAuxI
        | none => 0

  -- Canonical ctor counts per class (surgery.rs:427): representative's
  -- ctor count; only covers user classes.
  let mut canonCtorCountsM : Array Nat := #[]
  for cls in sortedClasses do
    let rep := cls[0]!
    match ← lookupConst? rep with
    | some (.inductInfo v) => canonCtorCountsM := canonCtorCountsM.push v.ctors.size
    | _ => canonCtorCountsM := canonCtorCountsM.push 0
  let canonCtorCounts := canonCtorCountsM
  let nCanonUserMinors : Nat := canonCtorCounts.foldl (· + ·) 0

  -- Cumulative canonical minor offset per user class (surgery.rs:441).
  let mut canonMinorOffsetM : Array Nat := Array.replicate nClasses 0
  let mut offsetAcc := 0
  for (cc, ci) in canonCtorCounts.zipIdx do
    canonMinorOffsetM := canonMinorOffsetM.set! ci offsetAcc
    offsetAcc := offsetAcc + cc
  let canonMinorOffset := canonMinorOffsetM

  -- Build one CallSitePlan for a specific target xPos (the source motive
  -- index this recursor is "for"). Mirrors the `build_plan` closure
  -- (surgery.rs:454). Pure — all captures are frozen above.
  let buildPlan : Nat → CallSitePlan := fun xPos => Id.run do
    let xClass := sourceToCanonMotive[xPos]!

    -- Motive keep/permute (surgery.rs:457). User motives: alpha-collapse
    -- logic (keep-self-in-class, keep-rep-in-other-class).
    let mut motiveKeep : Array Bool := Array.replicate nSourceMotives false
    for (srcName, srcI) in originalAll.zipIdx do
      if isPhantom[srcI]! then
        -- Phantom srcI's motive belongs to another canonical block.
        continue
      let srcClass := sourceToCanonMotive[srcI]!
      if srcClass == xClass then
        -- Self class: keep only X's own motive.
        motiveKeep := motiveKeep.set! srcI (srcI == xPos)
      else
        -- Non-self class: keep the representative's motive.
        let rep := sortedClasses[srcClass]![0]!
        motiveKeep := motiveKeep.set! srcI (srcName == rep)
    -- Aux motives mirror the user-class collapse rule (surgery.rs:481).
    -- For each canonical aux class, keep the representative source aux;
    -- if the target recursor itself is an aux in that canonical class,
    -- keep the target source aux instead.
    let targetAux : Option Nat :=
      if xPos >= nUserMotives then some (xPos - nUserMotives) else none
    let targetAuxCanon : Option Nat := targetAux.bind auxCanonOfSource
    for sourceAuxJ in [0:nSourceAuxMotives] do
      let srcI := nUserMotives + sourceAuxJ
      let keep : Bool :=
        match auxCanonOfSource sourceAuxJ with
        | some canonI =>
          if some canonI == targetAuxCanon then
            targetAux == some sourceAuxJ
          else
            auxReprForCanon[canonI]? == some sourceAuxJ
        | none => false
      motiveKeep := motiveKeep.set! srcI keep

    -- Minor keep/permute (surgery.rs:509). Source minors layout:
    -- [user0.ctors … userN.ctors | aux0.ctors … auxM.ctors]. User minors
    -- follow alpha-collapse (kept iff parent motive kept, permuted to
    -- canonical class-grouped order); aux minors follow the aux motive's
    -- decision, mapped into the canonical aux band at `nCanonUserMinors`.
    let mut minorKeep : Array Bool := #[]
    let mut sourceToCanonMinor : Array Nat := #[]
    let mut classMinorPlaced : Array Nat := Array.replicate nClasses 0

    -- User minors (surgery.rs:523).
    for srcI in [0:originalAll.size] do
      let nCtors := ctorCounts[srcI]!
      let srcClass := sourceToCanonMotive[srcI]!
      let parentKept := motiveKeep[srcI]!
      for ctorJ in [0:nCtors] do
        minorKeep := minorKeep.push parentKept
        if parentKept then
          let canonPos :=
            canonMinorOffset[srcClass]! + classMinorPlaced[srcClass]!
          sourceToCanonMinor := sourceToCanonMinor.push canonPos
          classMinorPlaced :=
            classMinorPlaced.set! srcClass (classMinorPlaced[srcClass]! + 1)
        else
          -- Collapsed — dropped at the call site, so consumers never read
          -- this value; push a placeholder (rep's ctorJ) purely to keep
          -- the index space aligned with the source minor count
          -- (surgery.rs:539).
          let repMinorBase := canonMinorOffset[srcClass]!
          sourceToCanonMinor := sourceToCanonMinor.push (repMinorBase + ctorJ)

    -- Aux minors — permuted through the aux band (surgery.rs:551).
    -- Without a layout, identity mapping (correct when source walk ==
    -- canonical, the common pre-fix case).
    match layoutNat with
    | some (permArr, counts) =>
      -- Canonical aux ctor counts, indexed by canonical aux position
      -- (surgery.rs:564).
      let mut canonAuxCtorCounts : Array Nat :=
        Array.replicate auxCanonicalCount 0
      for (canonI, sourceJ) in permArr.zipIdx do
        if canonI != PERM_OUT_OF_SCC && canonI < auxCanonicalCount then
          if let some cc := counts[sourceJ]? then
            canonAuxCtorCounts := canonAuxCtorCounts.set! canonI cc
      -- Cumulative canonical aux minor offsets (surgery.rs:574).
      let mut canonAuxOffset : Array Nat :=
        Array.replicate auxCanonicalCount 0
      let mut offset := 0
      for (cc, canonI) in canonAuxCtorCounts.zipIdx do
        canonAuxOffset := canonAuxOffset.set! canonI offset
        offset := offset + cc
      -- Walk source aux classes in source order, placing their minors at
      -- the canonical positions of perm[j]'s class (surgery.rs:583).
      for (nCtors, sourceJ) in counts.zipIdx do
        let srcI := nUserMotives + sourceJ
        let parentKept := (motiveKeep[srcI]?).getD true
        let canonI := auxCanonOfSource sourceJ
        let base := (canonI.bind fun ci => canonAuxOffset[ci]?).getD 0
        for k in [0:nCtors] do
          minorKeep := minorKeep.push parentKept
          -- Both kept and unkept positions reuse the canonical slot — this
          -- mirrors the user-side mapping where dropped sources still
          -- record where their canonical sibling landed.
          sourceToCanonMinor :=
            sourceToCanonMinor.push (nCanonUserMinors + base + k)
      -- Safety fallback (surgery.rs:599): if layout inventories don't sum
      -- to nAuxMinors, pad with identity entries to keep the minor arrays
      -- sized to nSourceMinors. (Nat subtraction ≡ `saturating_sub`.)
      while minorKeep.size < nSourceMinors do
        let k := sourceToCanonMinor.size - nUserMinors
        minorKeep := minorKeep.push true
        sourceToCanonMinor := sourceToCanonMinor.push (nCanonUserMinors + k)
    | none =>
      -- Identity mapping when no layout is provided (surgery.rs:609).
      for k in [0:nAuxMinors] do
        minorKeep := minorKeep.push true
        sourceToCanonMinor := sourceToCanonMinor.push (nCanonUserMinors + k)

    return {
      nParams, nSourceMotives, nSourceMinors, nIndices
      motiveKeep, minorKeep
      sourceToCanonMotive, sourceToCanonMinor
      sourceInBlock
      headRewrite := none }

  -- Build a plan for an EVAPORATED aux recursor `<all0>.rec_{auxJ+1}`
  -- (surgery.rs:630-675): every spec-param inductive of source aux `auxJ`
  -- left this SCC, the claim is aliased to the external inductive's
  -- recursor, and call sites are rebuilt onto that telescope. Only the
  -- aux's own motive and its own minor band survive; the external
  -- recursor supplies the aux's IH binders (`sourceInBlock[xPos] = true`),
  -- while IHs consumed from other dropped motives are synthesized by
  -- `adapt_split_minor` (consumption half). `recNIndices` mirrors the
  -- Rust closure's shadowing `n_indices` parameter.
  let buildOutOfSccPlan : Nat → Nat → Name → Nat → CallSitePlan :=
    fun xPos auxJ targetRec recNIndices => Id.run do
      let mut motiveKeep : Array Bool := Array.replicate nSourceMotives false
      motiveKeep := motiveKeep.set! xPos true
      let mut planMotiveMap : Array Nat := Array.replicate nSourceMotives 0
      planMotiveMap := planMotiveMap.set! xPos 0
      let counts : Array Nat := (layoutNat.map (·.2)).getD #[]
      let bandStart : Nat :=
        nUserMinors + (counts.extract 0 auxJ).foldl (· + ·) 0
      let bandLen := (counts[auxJ]?).getD 0
      let mut minorKeep : Array Bool := Array.replicate nSourceMinors false
      let mut planMinorMap : Array Nat := Array.replicate nSourceMinors 0
      for k in [0:bandLen] do
        -- Rust uses guarded `get_mut` — mirror the bounds checks.
        if bandStart + k < minorKeep.size then
          minorKeep := minorKeep.set! (bandStart + k) true
        if bandStart + k < planMinorMap.size then
          planMinorMap := planMinorMap.set! (bandStart + k) k
      let mut planInBlock : Array Bool := Array.replicate nSourceMotives false
      planInBlock := planInBlock.set! xPos true
      return {
        nParams, nSourceMotives, nSourceMinors
        nIndices := recNIndices
        motiveKeep, minorKeep
        sourceToCanonMotive := planMotiveMap
        sourceToCanonMinor := planMinorMap
        sourceInBlock := planInBlock
        headRewrite := some { targetRec, targetMotivePos := xPos } }

  -- Register plans for each user inductive's `X.rec`
  -- (xPos ∈ [0, nUser); surgery.rs:677).
  for (xName, xPos) in originalAll.zipIdx do
    -- Skip phantom X names: their plan belongs to the block owning X.
    if isPhantom[xPos]! then
      continue
    let plan := buildPlan xPos
    if plan.isIdentity then
      continue
    let recName := Name.mkStr xName "rec"
    if (← lookupConst? recName).isSome then
      plans := plans.insert recName plan

  -- Register plans for each nested-auxiliary recursor `all[0].rec_N`
  -- (xPos ∈ [nUser, nSourceMotives); surgery.rs:695).
  --
  -- Why: Lean's `mkSizeOfFns` (refs/lean4/src/Lean/Meta/SizeOf.lean:167)
  -- generates `_sizeOf_{all.size + j + 1}` bodies that call
  -- `(mkRecName all[0]).appendIndexAfter (j+1)` for each nested aux.
  -- Those rec_N recursors share the main recursor's motive/minor layout;
  -- without plans for them, aux `_sizeOf_N` bodies pass source-order args
  -- to the canonical rec_N (AppTypeMismatch on e.g. `LCNF.Alt._sizeOf_6`).
  if nSourceMotives > nUserMotives then
    if let some headName := originalAll[0]? then
      -- (owner, external head) per source aux — only needed when some
      -- source aux is out-of-SCC, i.e. potentially evaporated
      -- (surgery.rs:714).
      let anyOut : Bool :=
        match auxPerm with
        | some p => p.contains PERM_OUT_OF_SCC
        | none => false
      let srcOwnerHeads : Array (Name × Name) ←
        if anyOut then do
          let order ← sourceAuxOrderWithOwner originalAll
          pure (order.map fun (owner, head, _) => (owner, head))
        else
          pure #[]

      for auxIdx in [0:nSourceMotives - nUserMotives] do
        let xPos := nUserMotives + auxIdx
        let recName := Name.mkStr headName s!"rec_{auxIdx + 1}"
        if (← lookupConst? recName).isNone then
          continue
        let outOfScc : Bool :=
          match auxPerm.bind fun p => p[auxIdx]? with
          | some canonI => canonI == PERM_OUT_OF_SCC
          | none => false
        if outOfScc then
          -- Evaporated-aux head rewrite (surgery.rs:737). Owner gate
          -- mirrors the alias pass in `aux_gen.rs`: an out-of-SCC aux
          -- whose OWNER is also out-of-SCC is another SCC's canonical aux
          -- (that SCC registers its plan). The target guard also mirrors
          -- the alias pass — no alias means no rewrite, and vice versa.
          let some (owner, extHead) := srcOwnerHeads[auxIdx]? | continue
          if !(nameToClass.contains owner) then
            continue
          let targetRec := Name.mkStr extHead "rec"
          let targetOk : Bool :=
            match ← lookupConst? targetRec with
            | some (.recInfo r) => r.numMotives == 1
            | _ => false
          if !targetOk then
            continue
          -- Index count comes from the aux recursor itself (the external
          -- inductive's indices), not the block-wide default.
          let recNIndices : Nat ←
            match ← lookupConst? recName with
            | some (.recInfo r) => pure r.numIndices
            | _ => pure nIndices
          plans := plans.insert recName
            (buildOutOfSccPlan xPos auxIdx targetRec recNIndices)
          continue
        let plan := buildPlan xPos
        if plan.isIdentity then
          continue
        plans := plans.insert recName plan

  return plans

/-! ## Aux motive signatures (surgery.rs:988)

Shared with the consumption half: `adapt_split_minor`,
`source_ctor_for_minor`, and `find_source_rec_target` (surgery.rs:834/
942/1233) all take the `AuxMotiveSig` list extracted here. -/

/-- Signature of a nested-aux motive read off a source recursor's type:
    motive `sourcePos` targets `extName specs… idx…`. Spec args are
    concrete (the recursor type is instantiated with call-site params
    before extraction), so field types can be matched against them by
    hash. Mirrors Rust `AuxMotiveSig` (surgery.rs:992). -/
structure AuxMotiveSig where
  sourcePos : Nat
  extName : Name
  extNParams : Nat
  specs : Array Expr
  deriving Repr, Nonempty, Inhabited

/-- Extract `AuxMotiveSig`s for every aux motive position (`≥ all.size`)
    of `recVal`, by walking its type instantiated with the call site's
    levels, params, and motives. Mirrors Rust `aux_motive_sigs`
    (surgery.rs:1002). -/
def auxMotiveSigs (recVal : RecursorVal) (recLevels : Array Level)
    (params : Array Expr) (motives : Array Expr) :
    CompileM (Array AuxMotiveSig) := do
  let nUser := recVal.all.size
  let nMotives := recVal.numMotives
  let mut out : Array AuxMotiveSig := #[]
  if nMotives <= nUser then
    return out
  let mut cur :=
    substLevels recVal.cnst.type recVal.cnst.levelParams recLevels
  for arg in params do
    match cur with
    | .forallE _ _ body _ _ =>
      -- Shift-aware substitution — args may reference the caller's
      -- telescope (see `source_minor_type`, surgery.rs:1019).
      cur := instantiateRev body #[arg]
    | _ => return out
  for (motive, mIdx) in motives.zipIdx do
    if mIdx >= nMotives then
      break
    match cur with
    | .forallE _ dom body _ _ =>
      if mIdx >= nUser then
        -- dom = `∀ idx…, Ext specs… idx… → Sort _` — the major's type is
        -- the last peeled domain (surgery.rs:1031).
        let mut d := consumeTypeAnnotations dom
        let mut lastDom : Option Expr := none
        let mut i : Nat := 0
        repeat
          match d with
          | .forallE _ dd db _ _ =>
            lastDom := some (consumeTypeAnnotations dd)
            let (_, fv) := freshFVar "aux_sig_idx" (mIdx * 64 + i)
            d := instantiate1 db fv
            i := i + 1
          | _ => break
        if let some t := lastDom then
          let (head, tArgs) := decomposeApps t
          if let .const extName _ _ := head then
            match ← lookupConst? extName with
            | some (.inductInfo ind) =>
              let extNParams := ind.numParams
              if tArgs.size >= extNParams then
                out := out.push {
                  sourcePos := mIdx
                  extName, extNParams
                  specs := tArgs.extract 0 extNParams }
            | _ => pure ()
      cur := instantiateRev body #[motive]
    | _ => return out
  return out

/-- Derive the pieces needed to rebuild a head-rewritten call site onto
    the external recursor's telescope: the extended universe-level list
    and the external inductive's parameter (spec) arguments.

    Both are read off the SOURCE aux recursor's type — the motive binder
    at `hr.targetMotivePos` has domain `∀ idx…, Ext.{occ} specs… idx… →
    Sort _` — instantiated with the call site's levels, params, and
    preceding motives, so the result is expressed in caller terms.

    Mirrors Rust `derive_head_rewrite_app` (surgery.rs:1076), including
    its `Result<_, String>` error channel (`Except String` — the
    consumption caller decides how to wrap failures). -/
def deriveHeadRewriteApp (recName : Name) (recLevels : Array Level)
    (hr : AuxHeadRewrite) (params : Array Expr) (motives : Array Expr) :
    CompileM (Except String (Array Level × Array Expr)) := do
  let some (.recInfo recVal) ← lookupConst? recName
    | return .error s!"'{recName.pretty}' is not a recursor"
  let sigs ← auxMotiveSigs recVal recLevels params motives
  let some sig := sigs.find? fun s => s.sourcePos == hr.targetMotivePos
    | return .error s!"no aux motive signature at position {hr.targetMotivePos}"
  if Name.mkStr sig.extName "rec" != hr.targetRec then
    return .error s!"aux motive targets '{sig.extName.pretty}' but the \
plan's target is '{hr.targetRec.pretty}'"
  -- Occurrence levels: re-extract the external const's level args from
  -- the motive's major type — `auxMotiveSigs` keeps only the value args
  -- (surgery.rs:1105).
  let mut cur :=
    substLevels recVal.cnst.type recVal.cnst.levelParams recLevels
  for arg in params ++ motives.extract 0 hr.targetMotivePos do
    match cur with
    | .forallE _ _ body _ _ =>
      -- Shift-aware substitution — args may reference the caller's
      -- telescope (see `source_minor_type`, surgery.rs:1110).
      cur := instantiateRev body #[arg]
    | _ => return .error "recursor telescope too short"
  let .forallE _ dom _ _ _ := cur
    | return .error "missing target motive binder"
  let mut d := consumeTypeAnnotations dom
  let mut lastDom : Option Expr := none
  let mut i : Nat := 0
  repeat
    match d with
    | .forallE _ dd db _ _ =>
      lastDom := some (consumeTypeAnnotations dd)
      let (_, fv) := freshFVar "hr_idx" i
      d := instantiate1 db fv
      i := i + 1
    | _ => break
  let some t := lastDom
    | return .error "motive domain has no major binder"
  let (head, _) := decomposeApps t
  let occLevels : Array Level ←
    match head with
    | .const _ lvls _ => pure lvls
    | _ => return .error "major type head is not a constant"
  let some (.recInfo target) ← lookupConst? hr.targetRec
    | return .error
        s!"target recursor '{hr.targetRec.pretty}' missing from env"
  let needed := target.cnst.levelParams.size
  let targetLevels : Array Level ←
    if needed == occLevels.size + 1 then
      -- Elimination level first (Lean's recursor level convention), then
      -- the external inductive's own levels from the occurrence.
      let some elim := recLevels[0]?
        | return .error "source recursor has no elimination level"
      pure (#[elim] ++ occLevels)
    else if needed == occLevels.size then
      pure occLevels
    else
      return .error s!"cannot map universe levels: target \
'{hr.targetRec.pretty}' has {needed} level params, occurrence supplies \
{occLevels.size}"
  return .ok (targetLevels, sig.specs)

end Ix.AuxGen
