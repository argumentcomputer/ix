/-
  Ix.AuxGen.Patches: the `generate_aux_patches` orchestrator shell.

  Port of `crates/compile/src/compile/aux_gen.rs:188-989` (Phase 1 —
  canonical recursor generation with the expand/restore model — plus
  Phase 1b `.casesOn`, Phase 1c `.recOn`, Phase 2 `.below` with its
  `is_below_shaped` guard, `populate_canon_kenv_with_below`
  (aux_gen.rs:1017), Phase 3 `.brecOn` (aux_gen.rs:659-702), and the
  alias registration (aux_gen.rs:728-979): non-representative class
  members → the rep's patches; extra source aux `_N` names → the one
  canonical patch; evaporated-aux recursors → `<ext>.rec`).
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
public import Ix.AuxGen.Below
public import Ix.AuxGen.BRecOn
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- Mirrors Rust `is_below_shaped` (aux_gen.rs:998).

    Check whether a type expression is shaped like a `.below` auxiliary.

    A genuine `.below` type is a forall telescope ending in `Sort _`:
      `∀ {params} {motives} (indices) (major), Sort rlvl`

    This distinguishes `.below` auxiliaries from coincidental name
    collisions like structure field accessors (e.g.,
    `NewDecl.below : NewDecl → LocalDecl`).

    (Defined before `generateAuxPatches` — its only caller — instead of
    at its Rust source position after it; no semantic difference.) -/
def isBelowShaped (typ : Expr) : Bool := Id.run do
  let mut cur := typ
  repeat
    match cur with
    | .forallE _ _ body _ _ => cur := body
    | .sort _ _ => return true
    | _ => return false
  return false -- unreachable: the loop always returns

/-- Mirrors Rust `populate_canon_kenv_with_below` (aux_gen.rs:1017).

    Populate the bridge kenv with canonical `.below` types and their
    dependencies (parent inductives, constructors, PUnit, PProd). The
    canonical `.below` types match the alpha-collapsed block structure
    and may differ from the originals; Phase 3's TC uses the bridge kenv
    exclusively, so it must see the CANONICAL types for
    PProd(motive, I.below ...) inference.

    (Defined before `generateAuxPatches` — its only caller — instead of
    at its Rust source position after it; no semantic difference.) -/
def populateCanonKenvWithBelow (belowConsts : Array BelowConstant)
    (sortedClasses : Array (Array Name)) (maps : AddrMaps)
    : KBridgeM Unit := do
  -- Ensure PUnit and PProd are in kenv.
  ensurePreludeInKenvOf maps

  -- Ensure parent inductives (and their constructors) are in the kenv —
  -- the .below types reference these in their motive/major domains.
  for cls in sortedClasses do
    let rep := cls[0]!
    ensureInKenvOf rep maps

  -- Insert canonical .below definitions/inductives.
  for bc in belowConsts do
    match bc with
    | .defn d =>
      let addr := maps.resolve d.name
      let zid : MKId := ⟨addr, d.name⟩
      let tyZ ← leanExprToKexpr d.typ d.levelParams maps
      let valZ ← leanExprToKexpr d.value d.levelParams maps
      -- Rust: KConst::Defn { kind: Definition, safety: Safe,
      -- hints: Abbrev, lean_all: vec![], block: zid }.
      kenvInsert zid (.defn d.name d.levelParams .defn .safe .abbrev
        (UInt64.ofNat d.levelParams.size) tyZ valZ #[] zid)
    | .indc i =>
      let addr := maps.resolve i.name
      let zid : MKId := ⟨addr, i.name⟩
      let tyZ ← leanExprToKexpr i.typ i.levelParams maps
      let mut ctorZids : Array MKId := #[]
      for ctor in i.ctors do
        let ctorAddr := maps.resolve ctor.name
        let ctorZid : MKId := ⟨ctorAddr, ctor.name⟩
        let ctorTyZ ← leanExprToKexpr ctor.typ i.levelParams maps
        kenvInsert ctorZid (.ctor ctor.name i.levelParams false
          (UInt64.ofNat i.levelParams.size) zid
          (UInt64.ofNat ctorZids.size) (UInt64.ofNat ctor.nParams)
          (UInt64.ofNat ctor.nFields) ctorTyZ)
        ctorZids := ctorZids.push ctorZid
      kenvInsert zid (.indc i.name i.levelParams
        (UInt64.ofNat i.levelParams.size) (UInt64.ofNat i.nParams)
        (UInt64.ofNat i.nIndices) false zid 0 tyZ ctorZids #[])

/-- Alias-target lookup for original-order `_N` aux aliases. Mirrors the
    Rust `find_target` closure in `generate_aux_patches`
    (aux_gen.rs:834-855): prefer the deterministic representative used by
    generation (`sourceOfCanonical`), then fall back to any
    already-generated patch in the same equivalence class.

    (A top-level def instead of a closure — Lean do-blocks cannot close
    over the `mut patches` variable.) -/
def auxAliasFindTarget (patches : Std.HashMap Name PatchedConstant)
    (perm : Array Nat) (sourceOfCanonical : Array Nat) (canonicalI : Nat)
    (mkName : Nat → Name) : Option Name := Id.run do
  if let some sourceJ := sourceOfCanonical[canonicalI]? then
    if sourceJ != PERM_OUT_OF_SCC then
      let target := mkName sourceJ
      if patches.contains target then
        return some target
  for (sourceCanonicalI, sourceJ) in perm.zipIdx do
    if sourceCanonicalI == canonicalI then
      let target := mkName sourceJ
      if patches.contains target then
        return some target
  return none

/-- Generate all canonical auxiliary patches for a collapsed inductive
    block. Called (eventually, from the compile_mutual mirror) after
    `sortConsts` determines the canonical classes; `originalAll` is the
    Lean-source `InductiveVal.all` list driving `<all0>.rec_N` naming and
    the source-aux walk. Mirrors Rust `generate_aux_patches`
    (aux_gen.rs:188). -/
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

  let (canonicalRecs, isProp) ←
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

  -- Phase 2: Generate `.below` constants (if originals exist)
  -- (aux_gen.rs:603-660).
  let firstClassName := sortedClasses[0]![0]!
  let belowName := Name.mkStr firstClassName "below"
  -- Guard: the existing constant must actually be a `.below` auxiliary,
  -- not a coincidental name collision (e.g., a structure field accessor
  -- like `IndPredBelow.NewDecl.below : NewDecl → LocalDecl`). A genuine
  -- `.below` type always ends in `Sort _` after peeling foralls.
  let belowShaped ←
    match ← liftM (lookupConst? belowName : CompileM _) with
    | some ci => pure (isBelowShaped ci.getCnst.type)
    | none => pure false
  if belowShaped then
    let belowConsts ← generateBelowConstants sortedClasses canonicalRecs
      isProp maps
    -- `Ix.AuxGen.Below` derives `.below_N` names and internal cross-aux
    -- references from already-source-indexed rec names (see
    -- `generateBelowConstants` → `auxRecSuffixIdx`), so there is no
    -- canonical-indexed leftover to rewrite.
    for bc in belowConsts do
      match bc with
      | .defn d => patches := patches.insert d.name (.belowDef d)
      | .indc i => patches := patches.insert i.name (.belowIndc i)

    -- Populate the bridge kenv with canonical .below types for Phase 3.
    -- The canonical TC needs these to infer PProd(motive, I.below ...)
    -- during brecOn generation — uses the SAME renamed belowConsts that
    -- `patches` got, keeping hash addressing consistent end-to-end
    -- (aux_gen.rs:646-657).
    populateCanonKenvWithBelow belowConsts sortedClasses maps

    -- Phase 3: Generate .brecOn constants (if originals exist)
    -- (aux_gen.rs:659-702).
    let brecOnName := Name.mkStr firstClassName "brecOn"
    if (← liftM (lookupConst? brecOnName : CompileM _)).isSome then
      let breconConsts ← generateBreconConstants sortedClasses
        canonicalRecs belowConsts isProp maps
      for d in breconConsts do
        -- Only emit if the original Lean env has this constant (e.g.
        -- .brecOn.eq may not be in the exported env subset). `BRecOn`
        -- emits `.below_N` / sibling `.rec_N` references in
        -- source-indexed form directly — no post-generation rewrite.
        if (← liftM (lookupConst? d.name : CompileM _)).isSome then
          patches := patches.insert d.name (.brecOnDef d)

  -- Register Lean-exported names for non-representative alpha-collapsed
  -- members as aliases of the representative's canonical aux patches
  -- (aux_gen.rs:728-811). The primary inductive block has already
  -- collapsed the class to one content address; keep one patch per
  -- representative and let every non-representative name resolve to it.
  let mut aliases := aliases
  for cls in sortedClasses do
    if cls.size <= 1 then
      continue
    let rep := cls[0]!
    for aliasMem in cls.toList.drop 1 do
      -- For each active suffix that has a representative patch, register
      -- the alias name only when Lean actually exported that name.
      for suffix in #["rec", "recOn", "casesOn", "below", "brecOn"] do
        let repName := Name.mkStr rep suffix
        let aliasName := Name.mkStr aliasMem suffix
        -- Nested ifs: Rust `patches.contains_key(&rep_name) &&
        -- lean_env.get(&alias_name).is_some()`.
        if patches.contains repName then
          if (← liftM (lookupConst? aliasName : CompileM _)).isSome then
            aliases := aliases.insert aliasName repName

            -- Prop-level `.below` is itself an inductive, so Lean also
            -- exports constructor names under the alias-side `.below`.
            -- Register those positionally to the representative `.below`
            -- constructors (aux_gen.rs:754-789).
            if suffix == "below" then
              if let some (.belowIndc _) := patches.get? repName then
                let repCtors ←
                  match ← liftM (lookupConst? rep : CompileM _) with
                  | some (.inductInfo v) => pure v.ctors
                  | _ => pure #[]
                let aliasCtors ←
                  match ← liftM (lookupConst? aliasMem : CompileM _) with
                  | some (.inductInfo v) => pure v.ctors
                  | _ => pure #[]
                for (repCtor, aliasCtor) in repCtors.zip aliasCtors do
                  if let some repSuffix := nameStripPrefix repCtor rep then
                    let aliasSuffix :=
                      (nameStripPrefix aliasCtor aliasMem).getD
                        (nameComponents aliasCtor)
                    let repBelowCtor :=
                      nameAppendComponents repName repSuffix
                    let aliasBelowCtor :=
                      nameAppendComponents aliasName aliasSuffix
                    if (← liftM
                        (lookupConst? aliasBelowCtor : CompileM _)).isSome then
                      aliases := aliases.insert aliasBelowCtor repBelowCtor
      -- Also `.brecOn.go` and `.brecOn.eq` — sub-names of `.brecOn`
      -- generated for Type-level inductives (aux_gen.rs:792-804).
      for sub in #["go", "eq"] do
        let repBase := Name.mkStr rep "brecOn"
        let aliasBase := Name.mkStr aliasMem "brecOn"
        let repName := Name.mkStr repBase sub
        let aliasName := Name.mkStr aliasBase sub
        if patches.contains repName then
          if (← liftM (lookupConst? aliasName : CompileM _)).isSome then
            aliases := aliases.insert aliasName repName

      -- Note: _N suffixed names (rec_1, below_1, brecOn_1, etc.) are NOT
      -- aliased here. They always hang off all[0], not
      -- per-class-representative.

  -- Register original-order auxiliary aliases (aux_gen.rs:813-918). When
  -- alpha-collapse merges inductives, the source Lean block may export
  -- more nested auxiliaries than the canonical block; record address
  -- aliases to the one generated canonical patch instead of creating
  -- renamed synthetic patches.
  if structuralHasNested then
    if let some perm := capturedPerm then
      if capturedNCanonicalAux > 0 then
        if let some firstOrigName := originalAll[0]? then
          -- Rust seeds with usize::MAX — numerically PERM_OUT_OF_SCC.
          let mut sourceOfCanonical : Array Nat :=
            Array.replicate capturedNCanonicalAux PERM_OUT_OF_SCC
          for (canonicalI, sourceJ) in perm.zipIdx do
            if canonicalI != PERM_OUT_OF_SCC
                && canonicalI < capturedNCanonicalAux
                && sourceOfCanonical[canonicalI]! == PERM_OUT_OF_SCC then
              sourceOfCanonical := sourceOfCanonical.set! canonicalI sourceJ

          for (canonicalI, sourceJ) in perm.zipIdx do
            if canonicalI == PERM_OUT_OF_SCC
                || canonicalI >= capturedNCanonicalAux then
              continue

            let sourceIdx := sourceJ + 1
            for suffix in #["rec", "below", "brecOn"] do
              let mkName := fun (j : Nat) =>
                Name.mkStr firstOrigName s!"{suffix}_{j + 1}"
              let sourceName :=
                Name.mkStr firstOrigName s!"{suffix}_{sourceIdx}"
              -- Rust: `patches.contains_key(&source_name) ||
              -- lean_env.get(&source_name).is_none()` → continue
              -- (nested ifs preserve the short-circuit).
              if patches.contains sourceName then
                continue
              if (← liftM (lookupConst? sourceName : CompileM _)).isNone then
                continue
              match auxAliasFindTarget patches perm sourceOfCanonical
                  canonicalI mkName with
              | none =>
                throw (.invalidMutualBlock
                  s!"aux_gen alias target missing: {sourceName.pretty} \
maps to canonical aux #{canonicalI} but no generated {suffix} patch \
exists")
              | some targetName =>
                if targetName != sourceName then
                  aliases := aliases.insert sourceName targetName

            for sub in #["go", "eq"] do
              let mkName := fun (j : Nat) =>
                Name.mkStr (Name.mkStr firstOrigName s!"brecOn_{j + 1}")
                  sub
              let sourceBase :=
                Name.mkStr firstOrigName s!"brecOn_{sourceIdx}"
              let sourceName := Name.mkStr sourceBase sub
              if patches.contains sourceName then
                continue
              if (← liftM (lookupConst? sourceName : CompileM _)).isNone then
                continue
              match auxAliasFindTarget patches perm sourceOfCanonical
                  canonicalI mkName with
              | none =>
                throw (.invalidMutualBlock
                  s!"aux_gen alias target missing: {sourceName.pretty} \
maps to canonical aux #{canonicalI} but no generated brecOn.{sub} patch \
exists")
              | some targetName =>
                if targetName != sourceName then
                  aliases := aliases.insert sourceName targetName

  -- Evaporated aux recursor aliases (aux_gen.rs:920-979). A source aux
  -- whose OWNER is in this SCC but whose spec-param inductives are not
  -- has no home in ANY split SCC: dropping the irrelevant motives/minors
  -- from Lean's `<all0>.rec_{j+1}` leaves exactly the external
  -- inductive's own generic recursor. Alias the Lean-visible name to
  -- `<ext>.rec`. The owner gate matters: an out-of-SCC entry whose owner
  -- is ALSO out-of-SCC is simply another SCC's aux.
  if let some perm := capturedPerm then
    if perm.contains PERM_OUT_OF_SCC then
      if let some firstOrigName := originalAll[0]? then
        let mut inScc : Std.HashSet Name := {}
        for cls in sortedClasses do
          for n in cls do
            inScc := inScc.insert n
        let srcOrder ← liftM
          (Ix.AuxGen.sourceAuxOrderWithOwner originalAll : CompileM _)
        for (canonicalI, sourceJ) in perm.zipIdx do
          if canonicalI != PERM_OUT_OF_SCC then
            continue
          let some (owner, extHead, _) := srcOrder[sourceJ]?
            | continue
          if !inScc.contains owner then
            continue
          let sourceName :=
            Name.mkStr firstOrigName s!"rec_{sourceJ + 1}"
          let targetName := Name.mkStr extHead "rec"
          -- Target guard mirrors the head-rewrite plan registration in
          -- `surgery::compute_call_site_plans` — multi-motive external
          -- targets are outside the supported rewrite domain.
          let targetOk ←
            match ← liftM (lookupConst? targetName : CompileM _) with
            | some (.recInfo r) => pure (r.numMotives == 1)
            | _ => pure false
          -- Rust: `patches.contains_key(&source_name) ||
          -- lean_env.get(&source_name).is_none() || !target_ok` →
          -- continue.
          if patches.contains sourceName then
            continue
          if (← liftM (lookupConst? sourceName : CompileM _)).isNone then
            continue
          if !targetOk then
            continue
          aliases := aliases.insert sourceName targetName

  return { patches, aliases, perm := capturedPerm,
           nClasses, nCanonicalAux := capturedNCanonicalAux,
           nSourceAux := capturedNSourceAux }

end Ix.AuxGen
