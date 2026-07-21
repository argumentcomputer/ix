/-
  Ix.AuxGen.Patches: the `generate_aux_patches` orchestrator shell.

  Port of `crates/compile/src/compile/aux_gen.rs:188-601` (Phase 1 —
  canonical recursor generation with the expand/restore model — plus
  Phase 1b `.casesOn` and Phase 1c `.recOn`). Phases 2 (`.below`),
  3 (`.brecOn`) and the alias registration (aux_gen.rs:603-979) land with
  their respective milestones; until then `patches` carries only
  `kind=rec`/`kind=casesOn`/`kind=recOn` entries and `aliases` is empty —
  the cross-compiler gate filters by kind accordingly.
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
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Recursor
public import Ix.AuxGen.CasesOn
public import Ix.AuxGen.RecOn
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- Generate all canonical auxiliary patches for a collapsed inductive
    block. Called (eventually, from the compile_mutual mirror) after
    `sortConsts` determines the canonical classes; `originalAll` is the
    Lean-source `InductiveVal.all` list driving `<all0>.rec_N` naming and
    the source-aux walk. Mirrors Rust `generate_aux_patches`
    (aux_gen.rs:188). Currently Phase 1 only (see module doc). -/
def generateAuxPatches (sortedClasses : Array (Array Name))
    (originalAll : Array Name) (maps : AddrMaps)
    : KBridgeM AuxPatchesOutput := do
  let patches : Std.HashMap Name PatchedConstant := {}
  let aliases : Std.HashMap Name Name := {}

  if originalAll.isEmpty then
    return { patches, aliases, perm := none,
             nClasses := sortedClasses.size, nCanonicalAux := 0,
             nSourceAux := 0 }

  let nClasses := sortedClasses.size
  let mut capturedPerm : Option (Array Nat) := none
  let mut capturedNCanonicalAux : Nat := 0
  let mut capturedNSourceAux : Nat := 0

  -- PUnit/PProd must be authoritative BEFORE any ingress (aux_gen.rs:229).
  ensurePreludeInKenvOf maps

  -- Phase 1: canonical recursors (aux_gen.rs:231-549).
  let orderedOriginals : Array Name := sortedClasses.map (·[0]!)
  let mut aliasToRep : Std.HashMap Name Name := {}
  for cls in sortedClasses do
    let rep := cls[0]!
    for aliasName in cls.toList.drop 1 do
      aliasToRep := aliasToRep.insert aliasName rep
  let expandedProbe ← liftM
    (Ix.AuxGen.expandNestedBlock orderedOriginals aliasToRep : CompileM _)
  let structuralHasNested : Bool :=
    expandedProbe.types.size > expandedProbe.nOriginals
  let mut metadataHasNested := false
  for name in originalAll do
    if let some (.inductInfo v) ← liftM (lookupConst? name : CompileM _) then
      if v.numNested > 0 then metadataHasNested := true

  let (canonicalRecs, _isProp) ←
    if metadataHasNested && structuralHasNested then do
      -- Canonicalize the aux tail; every downstream patch layout depends
      -- on this order (aux_gen.rs:280).
      let (expanded, _sortPerm) ← liftM
        (Ix.AuxGen.sortAuxByPartitionRefinement expandedProbe : CompileM _)
      if expanded.types.size > expanded.nOriginals then do
        -- Source→canonical permutation FIRST, so the generator emits
        -- Lean-source-indexed `_N` suffixes directly (aux_gen.rs:283).
        let mut origToCanonMap : Std.HashMap Name Name := {}
        for cls in sortedClasses do
          let rep := cls[0]!
          for n in cls do
            origToCanonMap := origToCanonMap.insert n rep
        let nCanon := expanded.types.size - expanded.nOriginals
        let perm ← liftM
          (Ix.AuxGen.computeAuxPerm expanded originalAll origToCanonMap
            (fun n => some (maps.resolve n)) : CompileM _)
        capturedPerm := some perm
        capturedNCanonicalAux := nCanon
        capturedNSourceAux := perm.size

        -- canonRepr[canonical_i] = min source_j (deterministic under
        -- alpha-collapse); every canonical slot MUST have a source
        -- mapping (aux_gen.rs:318-341).
        let mut canonRepr : Array Nat := Array.replicate nCanon PERM_OUT_OF_SCC
        for (canonI, srcJ) in perm.zipIdx.map (fun (p, i) => (p, i)) do
          if canonI != PERM_OUT_OF_SCC && canonI < nCanon
              && canonRepr[canonI]! == PERM_OUT_OF_SCC then
            canonRepr := canonRepr.set! canonI srcJ
        for (srcJ, ci) in canonRepr.zipIdx do
          if srcJ == PERM_OUT_OF_SCC then
            throw (.invalidMutualBlock
              s!"aux_gen canonical aux #{ci} has no Lean source mapping; \
refusing to synthesize canonical-indexed _N names")
        let sourceOfCanonical := canonRepr

        let (rawRecs, isProp) ← generateRecursorsFromExpanded sortedClasses
          expanded (some sourceOfCanonical) maps

        -- aux_rec_map: `_nested.X.rec` → `<source_all0>.rec_{source_j+1}`
        -- (aux_gen.rs:381-393; source_all0 is the LEAN source first
        -- inductive, NOT the class rep — below/brecOn hang their `_N`
        -- names off it too).
        let sourceAll0 := originalAll[0]!
        let mut auxRecMap : Std.HashMap Name Name := {}
        for (mem, canonicalI) in
            ((expanded.types.toList.drop expanded.nOriginals).toArray).zipIdx do
          let sourceJ := sourceOfCanonical[canonicalI]!
          let auxNestedRecName := Name.mkStr mem.name "rec"
          let sourceRecName := Name.mkStr sourceAll0 s!"rec_{sourceJ + 1}"
          auxRecMap := auxRecMap.insert auxNestedRecName sourceRecName

        let mut restoreCtx := RestoreCtx.new expanded.auxToNested
          expanded.auxCtorMap auxRecMap expanded.blockParamFvars
          ((expanded.types[0]?.map (·.nParams)).getD 0)

        -- Restored `all` = the CANONICAL original member names — the
        -- shadowing at aux_gen.rs:406 is deliberate.
        let restoredAll : Array Name :=
          ((expanded.types.toList.take expanded.nOriginals).toArray).map (·.name)

        let mut restoredRecs : Array (Name × RecursorVal) := #[]
        for (name, rv) in rawRecs do
          let newName := (auxRecMap.get? name).getD name
          let (restoredType, ctx1) := restoreCtx.restore rv.cnst.type
          restoreCtx := ctx1
          let mut restoredRules : Array RecursorRule := #[]
          for r in rv.rules do
            let newCtor := match expanded.auxCtorMap.get? r.ctor with
              | some (origCtor, _) => origCtor
              | none => r.ctor
            let (rhs', ctx2) := restoreCtx.restore r.rhs
            restoreCtx := ctx2
            restoredRules := restoredRules.push
              { ctor := newCtor, nfields := r.nfields, rhs := rhs' }
          restoredRecs := restoredRecs.push (newName,
            { rv with
              cnst := { name := newName, type := restoredType,
                        levelParams := rv.cnst.levelParams }
              all := restoredAll
              rules := restoredRules })
        pure (restoredRecs, isProp)
      else do
        -- Defensive: post-sort aux tail empty (aux_gen.rs:454-499).
        if structuralHasNested then do
          let expandedForPerm ← liftM
            (Ix.AuxGen.expandNestedBlock orderedOriginals aliasToRep
              : CompileM _)
          let mut origToCanonMap : Std.HashMap Name Name := {}
          for cls in sortedClasses do
            let rep := cls[0]!
            for n in cls do
              origToCanonMap := origToCanonMap.insert n rep
          let nCanon :=
            expandedForPerm.types.size - expandedForPerm.nOriginals
          let perm ← liftM
            (Ix.AuxGen.computeAuxPerm expandedForPerm originalAll
              origToCanonMap (fun n => some (maps.resolve n)) : CompileM _)
          capturedPerm := some perm
          capturedNCanonicalAux := nCanon
          capturedNSourceAux := perm.size
        generateCanonicalRecursorsWithOverlay sortedClasses none none maps
    else do
      -- Standard flat-block generation; disagreement flavors still need
      -- the perm for surgery/aliases (aux_gen.rs:500-548).
      if structuralHasNested || metadataHasNested then do
        let mut origToCanonMap : Std.HashMap Name Name := {}
        for cls in sortedClasses do
          let rep := cls[0]!
          for n in cls do
            origToCanonMap := origToCanonMap.insert n rep
        let nCanon := expandedProbe.types.size - expandedProbe.nOriginals
        let perm ← liftM
          (Ix.AuxGen.computeAuxPerm expandedProbe originalAll origToCanonMap
            (fun n => some (maps.resolve n)) : CompileM _)
        capturedPerm := some perm
        capturedNCanonicalAux := nCanon
        capturedNSourceAux := perm.size
      generateCanonicalRecursorsWithOverlay sortedClasses none none maps

  -- Only emit `.rec` if the original Lean env has it (aux_gen.rs:552-558).
  let mut patches := patches
  for (recName, recVal) in canonicalRecs do
    if (← liftM (lookupConst? recName : CompileM _)).isSome then
      patches := patches.insert recName (.recr recVal)

  -- Phase 1b: Generate `.casesOn` definitions (aux_gen.rs:560-583).
  -- `.casesOn` is a definition that wraps `.rec`, stripping IH fields
  -- from minors and replacing non-target motives with PUnit. Needed by
  -- `.brecOn.eq` which uses casesOn-based proofs (via Lean's `cases`
  -- tactic).
  --
  -- Only generate for original recursors (first `nClasses` entries of
  -- `canonicalRecs`), not auxiliary `rec_N`. This is intentional: Lean
  -- does NOT generate `casesOn_N` for nested auxiliary types (unlike
  -- `below_N`/`brecOn_N` which ARE generated via BRecOn.lean).
  for (recName, recVal) in canonicalRecs.toList.take nClasses do
    -- Build casesOn name: recName is "I.rec", casesOn name is "I.casesOn"
    -- (Rust matches `NameData::Str(parent, _, _)` — the suffix itself is
    -- not inspected; non-Str names are skipped).
    match recName with
    | .str indName _ _ =>
      let casesOnName := Name.mkStr indName "casesOn"
      -- Only generate if the original env has this constant. Nested ifs:
      -- the generator must only run when the env lookup succeeds
      -- (mirrors Rust's short-circuiting `&&` let-chain).
      if (← liftM (lookupConst? casesOnName : CompileM _)).isSome then
        match ← liftM (generateCasesOn casesOnName recVal : CompileM _) with
        | some auxDef =>
          patches := patches.insert casesOnName (.casesOnDef auxDef)
        | none => pure ()
    | _ => pure ()

  -- Phase 1c: Generate `.recOn` definitions (arg-reordered `.rec`
  -- wrapper) (aux_gen.rs:585-601).
  --
  -- Only generate for original recursors (first `nClasses`), not
  -- auxiliary `rec_N` — same intentional restriction as Phase 1b.
  for (recName, recVal) in canonicalRecs.toList.take nClasses do
    match recName with
    | .str indName _ _ =>
      let recOnName := Name.mkStr indName "recOn"
      if (← liftM (lookupConst? recOnName : CompileM _)).isSome then
        match generateRecOn recOnName recVal with
        | some auxDef =>
          patches := patches.insert recOnName (.recOnDef auxDef)
        | none => pure ()
    | _ => pure ()

  -- Phases 2/3 + alias registration: later milestones.

  return { patches, aliases, perm := capturedPerm,
           nClasses, nCanonicalAux := capturedNCanonicalAux,
           nSourceAux := capturedNSourceAux }

end Ix.AuxGen
