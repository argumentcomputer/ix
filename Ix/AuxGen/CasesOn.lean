/-
  Ix.AuxGen.CasesOn: `.casesOn` generation — per-inductive eliminator
  without inductive hypotheses.

  Port of `crates/compile/src/compile/aux_gen/cases_on.rs`.

  `.casesOn` is a **definition** (not a recursor) whose value calls `.rec`
  with:
  - Non-target motives replaced by `λ _ ... _, PUnit`
  - Non-target minors replaced by `λ _ ... _, PUnit.unit`
  - Target minors rebuilt to strip IH fields (keep only non-recursive
    params)

  casesOn binder order: params, target_motive, indices, major,
  target_minors (same reordering as recOn: indices+major before minors).

  Follows `refs/lean4/src/library/constructions/cases_on.cpp`.

  Environment access: Rust threads `lean_env: &LeanEnv`; the Lean port
  reads the base compile environment via `lookupConst?` (CompileM), the
  same view `generate_aux_patches` hands the Rust generator.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Level.mkParam`,
  ...) so the embedded blake3 hashes stay bit-identical with the Rust
  compiler.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Levels
public import Ix.AuxGen.Nested
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM)

/-- Mirrors Rust `mk_pi_unit` (aux_gen/cases_on.rs:29).

    Replace the innermost return type of a forall chain with `unit`.
    Matches Lean's `mk_pi_unit` in `cases_on.cpp`:
    `∀ (x : A) (y : B), C x y` → `∀ (x : A) (y : B), unit`. -/
partial def mkPiUnit (e : Expr) (unit : Expr) : Expr :=
  match e with
  | .forallE name dom body bi _ =>
    Expr.mkForallE name dom (mkPiUnit body unit) bi
  | _ => unit

/-! ## Name-component helpers (common/src/env.rs:129-226)

`getMinorName` mirrors Rust `Name::strip_prefix` / `append_components`,
which operate on the component spine of a hierarchical name. Ported here
(their only aux_gen consumer) rather than into `Ix.Environment`. -/

/-- Mirrors Rust `NameComponent` (common/src/env.rs:129): one component of
    a hierarchical name. -/
inductive NameComponent where
  | str : String → NameComponent
  | num : Nat → NameComponent
  deriving BEq, Repr, Inhabited

/-- Mirrors Rust `Name::components` (common/src/env.rs:183): the component
    spine, outermost (root-adjacent) first. -/
def nameComponents (n : Name) : Array NameComponent := Id.run do
  let mut components : Array NameComponent := #[]
  let mut current := n
  repeat
    match current with
    | .anonymous _ => break
    | .str pre s _ =>
      components := components.push (.str s)
      current := pre
    | .num pre i _ =>
      components := components.push (.num i)
      current := pre
  return components.reverse

/-- Mirrors Rust `Name::strip_prefix` (common/src/env.rs:204): strip a
    prefix from this name, returning the suffix components. -/
def nameStripPrefix (n pfx : Name) : Option (Array NameComponent) :=
  let selfComponents := nameComponents n
  let prefixComponents := nameComponents pfx
  if selfComponents.size < prefixComponents.size then
    none
  else if selfComponents.extract 0 prefixComponents.size != prefixComponents then
    none
  else
    some (selfComponents.extract prefixComponents.size selfComponents.size)

/-- Mirrors Rust `Name::append_components` (common/src/env.rs:217): append
    suffix components to this name. -/
def nameAppendComponents (n : Name) (suffix : Array NameComponent) : Name :=
  Id.run do
    let mut result := n
    for component in suffix do
      match component with
      | .str s => result := Name.mkStr result s
      | .num i => result := Name.mkNat result i
    return result

/-- Mirrors Rust `get_minor_name` (aux_gen/cases_on.rs:351).

    Extract a minor premise name for the casesOn binder. Uses the
    constructor name suffix (e.g., "A.mk" → "mk").

    (Deviation: Rust passes `target_range: &Range<usize>` but reads only
    `.start` — the Lean port takes the start directly.) -/
def getMinorName (minorIdx : Nat) (targetRangeStart : Nat) (targetInd : Name) :
    CompileM Name := do
  let ctorIdx := minorIdx - targetRangeStart
  match ← lookupConst? targetInd with
  | some (.inductInfo v) =>
    match v.ctors[ctorIdx]? with
    | some ctorName =>
      -- Strip prefix to get suffix (e.g., "A.mk" → "mk")
      match nameStripPrefix ctorName targetInd with
      | some suffix => pure (nameAppendComponents Name.mkAnon suffix)
      | none => pure ctorName
    | none => pure (Name.mkStr .mkAnon s!"minor_{ctorIdx}")
  | _ => pure (Name.mkStr .mkAnon s!"minor_{ctorIdx}")

/-- Mirrors Rust `generate_cases_on` (aux_gen/cases_on.rs:56).

    Generate a `.casesOn` definition from a canonical `.rec`.

    Returns `none` if the recursor type cannot be decomposed.

    Uses FVar-based construction: opens the rec type into FVars, builds
    casesOn type and value using FVar references, then abstracts with
    `mkForall`/`mkLambda`.

    (Deviation: the Rust `num_*.to_u64()?` big-nat conversions cannot fail
    here — `Ix.RecursorVal` carries native `Nat` counts.) -/
def generateCasesOn (name : Name) (recVal : RecursorVal) :
    CompileM (Option AuxDef) := do
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices

  -- Extract target inductive name from "A.casesOn" → "A"
  -- (Rust cases_on.rs:67-72).
  let some targetInd := (match name with
    | .str parent s _ => if s == "casesOn" then some parent else none
    | _ => none)
    | return none

  -- Find target index in recVal.all (cases_on.rs:75).
  let some targetIdx := recVal.all.findIdx? (· == targetInd)
    | return none

  -- Determine elimination level (cases_on.rs:78-87).
  let indNLparams ← match ← lookupConst? targetInd with
    | some (.inductInfo v) => pure v.cnst.levelParams.size
    | _ => return none
  let elimToProp := recVal.cnst.levelParams.size == indNLparams
  let elimLvl := if elimToProp then
      Level.mkZero
    else
      Level.mkParam recVal.cnst.levelParams[0]!

  -- Count constructors per inductive (cases_on.rs:90-97).
  let mut ctorCounts : Array Nat := #[]
  for indName in recVal.all do
    match ← lookupConst? indName with
    | some (.inductInfo v) => ctorCounts := ctorCounts.push v.ctors.size
    | _ => ctorCounts := ctorCounts.push 0

  -- Universe levels for the rec application (cases_on.rs:100-105).
  let recUnivs : Array Level := recVal.cnst.levelParams.map Level.mkParam

  -- === Step 1: Open rec type into FVars (cases_on.rs:107-149) ===

  let (paramFvars, paramDecls, afterParams) :=
    forallTelescope recVal.cnst.type nParams "cop" 0

  -- Open ALL motives as FVars (needed for IH detection in minor fields).
  -- Only the target motive becomes a casesOn binder; non-target FVars
  -- will be replaced in the final value by PUnit functions.
  let mut motiveFvars : Array Expr := #[]
  let mut allMotiveDecls : Array LocalDecl := #[]
  let mut afterMotives := afterParams
  for mi in [0:nMotives] do
    match afterMotives with
    | .forallE bname dom body bi _ =>
      let (fvName, fv) := freshFVar "com" mi
      allMotiveDecls := allMotiveDecls.push
        { fvarName := fvName, binderName := bname, domain := dom, info := bi }
      motiveFvars := motiveFvars.push fv
      afterMotives := instantiate1 body fv
    | _ => pure ()
  let targetMotiveDecl := allMotiveDecls[targetIdx]!

  -- Open minors (keep FVar-based domains; dummy FVars for instantiation).
  let mut minorDoms : Array Expr := #[]
  let mut afterMinors := afterMotives
  for mi in [0:nMinors] do
    match afterMinors with
    | .forallE _ dom body _ _ =>
      minorDoms := minorDoms.push dom
      let (_, dummy) := freshFVar "cox" mi
      afterMinors := instantiate1 body dummy
    | _ => pure ()

  -- Open indices and major.
  let (indexFvars, indexDecls, afterIndices) :=
    forallTelescope afterMinors nIndices "coi" 0
  let (majorFvars, majorDecls, recReturnType) :=
    forallTelescope afterIndices 1 "coj" 0

  -- === Step 2: Build casesOn binder list (cases_on.rs:151-157) ===

  let mut coDecls : Array LocalDecl := #[]
  coDecls := coDecls ++ paramDecls -- params
  coDecls := coDecls.push targetMotiveDecl -- target motive only
  coDecls := coDecls ++ indexDecls -- indices
  coDecls := coDecls ++ majorDecls -- major

  -- === Step 3: Build stripped target minors + minor wrappers for rec
  -- (cases_on.rs:159-261) ===

  -- Track which minors belong to target inductive.
  let mut minorOffset : Nat := 0
  let mut targetMinorStart : Nat := 0
  let mut targetMinorStop : Nat := 0
  for (count, j) in ctorCounts.zipIdx do
    if j == targetIdx then
      targetMinorStart := minorOffset
      targetMinorStop := minorOffset + count
    minorOffset := minorOffset + count

  -- For each minor, build:
  -- - If target: casesOn minor binder (stripped of IH) + rec arg wrapper
  -- - If non-target: rec arg = λ (all_fields), PUnit.unit
  -- (Deviation: Rust's single-field local `struct MinorInfo { rec_arg }`
  -- is flattened to a plain `Array Expr` of rec args.)
  let mut minorRecArgs : Array Expr := #[]

  for (minorDom, mi) in minorDoms.zipIdx do
    let isTarget := targetMinorStart <= mi && mi < targetMinorStop

    if isTarget then
      -- Open minor fields.
      let nFields := countForalls minorDom
      let (fieldFvars, fieldDecls, minorRet) :=
        forallTelescope minorDom nFields s!"cof{mi}" 0

      -- Classify fields: non-IH go into casesOn minor, IH fields are
      -- dropped.
      let mut nonIhDecls : Array LocalDecl := #[]
      let mut nonIhFvars : Array Expr := #[]
      let mut wrapperDecls : Array LocalDecl := #[] -- all fields for the rec lambda

      for (decl, fvar) in fieldDecls.zip fieldFvars do
        match findMotiveFVar decl.domain motiveFvars with
        | some idx =>
          if idx == targetIdx then
            -- Target-motive IH: keep original domain in wrapper.
            wrapperDecls := wrapperDecls.push decl
          else
            -- Non-target-motive IH: wrap domain with mkPiUnit.
            -- Matches C++ lines 134-140: replace type with `∀ args, PUnit`.
            let wrappedDomain := mkPiUnit decl.domain (punitConst elimLvl)
            wrapperDecls := wrapperDecls.push { decl with domain := wrappedDomain }
        | none =>
          -- Non-IH field: appears in both wrapper and casesOn minor.
          nonIhDecls := nonIhDecls.push decl
          nonIhFvars := nonIhFvars.push fvar
          wrapperDecls := wrapperDecls.push decl

      -- Build casesOn minor type: ∀ (non_ih_fields...), minor_ret
      let coMinorType := mkForall minorRet nonIhDecls

      -- Get original minor name from rec type for the casesOn binder name
      -- (use recVal's constructor name suffix as binder name).
      let coMinorBinderName ← getMinorName mi targetMinorStart targetInd
      let (coFvName, coFv) := freshFVar "coq" mi
      coDecls := coDecls.push
        { fvarName := coFvName, binderName := coMinorBinderName,
          domain := coMinorType, info := .default }

      -- Build rec arg wrapper: λ (all_fields), co_minor_fvar(non_ih_fvars)
      let wrapperBody := mkAppN coFv nonIhFvars
      let recArg := mkLambda wrapperBody wrapperDecls

      minorRecArgs := minorRecArgs.push recArg
    else
      -- Non-target minor: rec arg = λ (all_fields), PUnit.unit
      -- IH fields targeting non-target motives need mkPiUnit wrapping
      -- (matching Lean's process_minor which applies mk_pi_unit for all
      -- non-main IH fields, regardless of whether the minor itself is
      -- main).
      let nFields := countForalls minorDom
      let (_, fieldDecls, _) :=
        forallTelescope minorDom nFields s!"con{mi}" 0
      let wrappedDecls : Array LocalDecl := fieldDecls.map fun decl =>
        match findMotiveFVar decl.domain motiveFvars with
        | some idx =>
          if idx != targetIdx then
            -- Non-target-motive IH: wrap domain.
            { decl with domain := mkPiUnit decl.domain (punitConst elimLvl) }
          else
            decl
        | none => decl
      let recArg := mkLambda (mkPUnitUnit elimLvl) wrappedDecls
      minorRecArgs := minorRecArgs.push recArg

  -- === Step 4: Substitute non-target motive FVars (cases_on.rs:263-292)
  -- Non-target motive FVars may appear in index/major/minor domains.
  -- Replace them with PUnit functions before building final type and
  -- value. ===
  let mut nonTargetSubsts : Array (Name × Expr) := #[]
  for (decl, j) in allMotiveDecls.zipIdx do
    if j == targetIdx then
      continue
    let motiveType := decl.domain
    let nMotiveArgs := countForalls motiveType
    let (_, motiveArgDecls, _) :=
      forallTelescope motiveType nMotiveArgs s!"cos{j}" 0
    let funUnit := mkLambda (punitConst elimLvl) motiveArgDecls
    nonTargetSubsts := nonTargetSubsts.push (decl.fvarName, funUnit)

  -- Apply substitutions to coDecls domains and recReturnType.
  let mut coRet := recReturnType
  for (fvName, replacement) in nonTargetSubsts do
    coRet := substFVar coRet fvName replacement
  let mut coDeclsFinal : Array LocalDecl := #[]
  for d in coDecls do
    let mut dom := d.domain
    for (fvName, replacement) in nonTargetSubsts do
      dom := substFVar dom fvName replacement
    coDeclsFinal := coDeclsFinal.push { d with domain := dom }

  -- === Step 5: Build casesOn type (cases_on.rs:294-296) ===

  let coType := mkForall coRet coDeclsFinal

  -- === Step 5: Build casesOn value (cases_on.rs:298-334) ===

  let mut val := mkConst recVal.cnst.name recUnivs

  -- Apply params.
  val := mkAppN val paramFvars

  -- Apply motives: target motive directly, others as λ targs, unit_type.
  -- (Rust `.take(n_motives)` is a no-op guard — the motive loop above
  -- pushes at most `nMotives` decls.)
  for (motiveDecl, j) in allMotiveDecls.zipIdx do
    if j == targetIdx then
      val := Expr.mkApp val motiveFvars[targetIdx]!
    else
      -- Build λ (motive_args...), unit_type
      let motiveType := motiveDecl.domain
      let nMotiveArgs := countForalls motiveType
      let (_, motiveArgDecls, _) :=
        forallTelescope motiveType nMotiveArgs s!"cou{j}" 0
      let funUnit := mkLambda (punitConst elimLvl) motiveArgDecls
      val := Expr.mkApp val funUnit

  -- Apply minors.
  for recArg in minorRecArgs do
    val := Expr.mkApp val recArg

  -- Apply indices and major.
  val := mkAppN val indexFvars
  val := mkAppN val majorFvars

  -- Replace non-target motive FVars in the value (same substitutions as
  -- type).
  for (fvName, replacement) in nonTargetSubsts do
    val := substFVar val fvName replacement

  let coValue := mkLambda val coDeclsFinal

  return some {
    name
    levelParams := recVal.cnst.levelParams
    typ := coType
    value := coValue
    -- `.casesOn` mirrors the recursor's safety — its value references the
    -- parent inductive's `.rec`, so Lean's
    -- `mkDefinitionValInferringUnsafe` always infers the same safety as
    -- the inductive.
    isUnsafe := recVal.isUnsafe }

end Ix.AuxGen

end
