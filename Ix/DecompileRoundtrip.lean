/-
  Ix.DecompileRoundtrip: compile→decompile roundtrip for binder-name
  restoration (D3) — the Lean mirror of the roundtrip half of
  `crates/compile/src/decompile.rs`:

    build_block_env            decompile.rs:2222
    def_safety                 decompile.rs:2242
    below_def_to_lean          decompile.rs:2252
    below_indc_to_lean         decompile.rs:2273
    brecon_def_to_lean         decompile.rs:2333
    roundtrip_block            decompile.rs:2692
    recover_aux_from_original  decompile.rs:4088

  Phase A of `roundtrip_block` (decompile.rs:2712-2868) reuses the ported
  compile pipeline verbatim: `Ix.CompileM.sortConsts` +
  `Ix.CompileM.compileMutualBlock` already cover Rust's manual cache
  setup, `preseed_expr_tables` call, per-member compile with one pushed
  representative per class, the bare-constant (non-`Muts`) singleton
  branch, and projection construction — byte-identical with Rust per the
  A-series gates.

  Deliberate omissions (all env-var-gated stderr diagnostics):
  `IX_ROUNDTRIP_DEBUG` dumps, the original-form probe recompile
  (decompile.rs:2909-3091), `print_const_comparison` /
  `print_rec_comparison` and the per-entry debug prints
  (decompile.rs:3134-3159, 3246-3318, 3426-3431). Error PROPAGATION at
  those sites is fully ported; only the prints are dropped.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public import Ix.DecompileM
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.Nested
public import Ix.CallSiteSurgery
public section

namespace Ix.DecompileM

/-- Subset environment for one mutual block: the named inductives plus
    their constructors (Rust `build_block_env`, decompile.rs:2222). -/
def buildBlockEnv (allNames : Array Ix.Name)
    (env : Std.HashMap Ix.Name Ix.ConstantInfo)
    : Std.HashMap Ix.Name Ix.ConstantInfo := Id.run do
  let mut out : Std.HashMap Ix.Name Ix.ConstantInfo := {}
  for indName in allNames do
    if let some ci := env.get? indName then
      out := out.insert indName ci
      if let .inductInfo v := ci then
        for ctorName in v.ctors do
          if let some ctorCi := env.get? ctorName then
            out := out.insert ctorName ctorCi
  return out

/-- Map an `isUnsafe` flag to a `Lean.DefinitionSafety`, in lock-step
    with the compile side (Rust `def_safety`, decompile.rs:2242). -/
def defSafety (isUnsafe : Bool) : Lean.DefinitionSafety :=
  if isUnsafe then .unsafe else .safe

/-- Convert a `BelowDef` (Type-level `.below`) to an `Ix.ConstantInfo`
    (Rust `below_def_to_lean`, decompile.rs:2252). Safety mirrors the
    parent inductive via `BelowDef.isUnsafe`; hints are `.abbrev` per
    Lean's `mkDefinitionValInferringUnsafe … .abbrev`. -/
def belowDefToLean (d : Ix.AuxGen.BelowDef) : Ix.ConstantInfo :=
  .defnInfo {
    cnst := { name := d.name, levelParams := d.levelParams, type := d.typ }
    value := d.value
    hints := .abbrev
    safety := defSafety d.isUnsafe
    all := #[d.name] }

/-- Convert a `BelowIndc` (Prop-level `.below`) to an `InductiveVal` and
    its constructors (Rust `below_indc_to_lean`, decompile.rs:2273).
    `isReflexive` is inherited from the parent; constructor safety
    matches the enclosing inductive (the kernel rejects mixed safety). -/
def belowIndcToLean (indc : Ix.AuxGen.BelowIndc)
    (allBelowNames : Array Ix.Name)
    : Ix.InductiveVal × Array Ix.ConstructorVal :=
  let ctorNames : Array Ix.Name := indc.ctors.map (·.name)
  let indVal : Ix.InductiveVal := {
    cnst := { name := indc.name, levelParams := indc.levelParams
              type := indc.typ }
    numParams := indc.nParams
    numIndices := indc.nIndices
    all := allBelowNames
    ctors := ctorNames
    numNested := 0
    isRec := true
    isReflexive := indc.isReflexive
    isUnsafe := indc.isUnsafe }
  let ctors : Array Ix.ConstructorVal := indc.ctors.zipIdx.map fun (c, cidx) =>
    { cnst := { name := c.name, levelParams := indc.levelParams
                type := c.typ }
      induct := indc.name
      cidx := cidx
      numParams := c.nParams
      numFields := c.nFields
      isUnsafe := indc.isUnsafe }
  (indVal, ctors)

/-- Convert a `BRecOnDef` to an `Ix.ConstantInfo` (Rust
    `brecon_def_to_lean`, decompile.rs:2333), replicating Lean's
    `BRecOn.lean` per-kind decisions: Prop-level `.brecOn` and safe
    `.brecOn.eq` emit theorems; unsafe cases flatten into an unsafe
    definition with `.opaque` hints (Lean's `mkThmOrUnsafeDef`);
    `.brecOn` / `.brecOn.go` definitions carry `.abbrev` hints. -/
def breconDefToLean (d : Ix.AuxGen.BRecOnDef) : Ix.ConstantInfo :=
  let cnst : Ix.ConstantVal :=
    { name := d.name, levelParams := d.levelParams, type := d.typ }
  let isEq := match d.name with
    | .str _ s _ => s == "eq"
    | _ => false
  let asTheorem := (d.isProp || isEq) && !d.isUnsafe
  if asTheorem then
    .thmInfo { cnst, value := d.value, all := #[d.name] }
  else
    let hints : Lean.ReducibilityHints :=
      if d.isUnsafe && (d.isProp || isEq) then .opaque else .abbrev
    .defnInfo { cnst, value := d.value, hints
                safety := defSafety d.isUnsafe, all := #[d.name] }

/-! ## roundtrip_block helpers -/

/-- Constant-kind label for error messages (Rust `ci_kind`,
    decompile.rs:2375). -/
private def ciKind : Ix.ConstantInfo → String
  | .axiomInfo _ => "Axiom"
  | .defnInfo _ => "Defn"
  | .thmInfo _ => "Thm"
  | .opaqueInfo _ => "Opaque"
  | .quotInfo _ => "Quot"
  | .inductInfo _ => "Induct"
  | .ctorInfo _ => "Ctor"
  | .recInfo _ => "Rec"

/-- Content address (blake3 of serialized bytes) of a Constant (Rust
    `ixon_content_address`, decompile.rs:2622). -/
private def ixonContentAddress (c : Ixon.Constant) : Address :=
  Address.blake3 (Ixon.ser c)

/-- Truncated hex for error messages (Rust `{:.12}` on `Address::hex`). -/
private def hex12 (a : Address) : String :=
  ((toString a).take 12).toString

/-- Run a per-constant decompile against the given env with fresh block
    context/state (same shape as `decompileOne`'s run), stringifying the
    error. -/
private def runDecompileM (denv : DecompileEnv) (m : DecompileM α)
    : Except String α :=
  match DecompileM.run denv default {} m with
  | .ok (a, _) => .ok a
  | .error e => .error (toString e)

/-- Decompile one regenerated inductive class member with original
    metadata, then restore the Lean-only flags (`numNested` / `isRec` /
    `isReflexive`) recomputed over the GENERATED constants — the Indc arm
    of `roundtrip_block`'s Phase B dispatch (decompile.rs:3191-3218).
    Returns the inductive entry followed by its constructor entries. -/
private def decompileIndcEntries (denv : DecompileEnv)
    (ind : Ixon.Inductive) (blockConstant : Ixon.Constant)
    (origMeta : Ixon.ConstantMeta) (name : Ix.Name)
    (generatedConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    : Except String (Array (Ix.Name × Ix.ConstantInfo)) := do
  let (iv, cvs) ←
    runDecompileM denv (decompileInductive ind blockConstant origMeta)
  -- Recompute the lean flags, which are not stored by Ixon
  -- (decompile.rs:3195-3210). Rust builds `flags_env` from
  -- `generated_consts`; the Lean run wraps the same map in a synthetic
  -- CompileEnv (the `fixupInductiveFlags` pattern).
  let cenv := Ix.CompileM.CompileEnv.new { consts := generatedConsts }
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := name, mutCtx := default, univCtx := [] }
  let flags ← match Ix.CompileM.CompileM.run cenv blockEnv {}
      (Ix.AuxGen.computeLeanIndFlags iv.all) with
    | .ok (flags, _) => pure flags
    | .error e => throw s!"roundtrip ind-flags for '{name.pretty}': {e}"
  let iv := { iv with
    numNested := flags.numNested
    isRec := flags.isRec
    isReflexive := flags.isReflexive }
  let mut entries : Array (Ix.Name × Ix.ConstantInfo) :=
    #[(name, Ix.ConstantInfo.inductInfo iv)]
  for cv in cvs do
    entries := entries.push (cv.cnst.name, Ix.ConstantInfo.ctorInfo cv)
  pure entries

/-- Compile a batch of regenerated `MutConst`s as a mutual block, then
    decompile each member with ORIGINAL metadata from `Named.original` to
    restore source binder names. Returns restored Lean constants keyed by
    SOURCE names (constructor entries included under their own names).
    Rust `roundtrip_block` (decompile.rs:2692).

    Parameter mapping (see the Rust signature at decompile.rs:2692-2698):
    where Rust reads `stt.env.named` / `stt.env.get_const` this uses
    `ixonEnv.named` / `ixonEnv.getConst?`; where it reads `dstt.env` this
    uses `workEnv`; `orig_env` (the debug-track source env) is `origEnv?`.
    The trailing optional plan maps mirror `stt.call_site_plans` /
    `stt.brec_on_call_site_plans` / `stt.below_call_site_plans`, which in
    Rust ride along inside `stt` (populated by the D2 plan rehydration);
    pass them when available so surgered call sites inside below-ctor
    types recompile byte-identically.

    Phase A (decompile.rs:2712-2868) is `sortConsts` +
    `compileMutualBlock` — the latter already performs Rust's explicit
    preseed (:2735-2746), the per-member representative pushes
    (:2753-2807) and the bare-constant singleton branch (:2834-2868).
    The synthetic `CompileEnv` seeds `nameToNamed := ixonEnv.named` (so
    the aux-regen surgery guard sees `Named.original`, compile.rs:829)
    and folds `nameToAddr` from it (the deserialized resolution map). -/
def roundtripBlock (consts : List Ix.MutConst)
    (generatedConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo))
    (workEnv : Std.HashMap Ix.Name Ix.ConstantInfo)
    (ixonEnv : Ixon.Env)
    (callSitePlans : Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan := {})
    (brecOnCallSitePlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {})
    (belowCallSitePlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {})
    : Except String (Std.HashMap Ix.Name Ix.ConstantInfo) := do
  let mut results : Std.HashMap Ix.Name Ix.ConstantInfo := {}
  -- decompile.rs:2707-2709.
  let some firstConst := consts.head? | return results
  let firstName := firstConst.name

  -- ------------------------------------------------------------------
  -- Phase A: Compile to Ixon (decompile.rs:2712-2868)
  -- ------------------------------------------------------------------
  let cenv : Ix.CompileM.CompileEnv :=
    { Ix.CompileM.CompileEnv.new { consts := workEnv } with
      nameToNamed := ixonEnv.named
      nameToAddr := ixonEnv.named.fold (init := {})
        fun m n named => m.insert n named.addr
      callSitePlans := callSitePlans
      brecOnCallSitePlans := brecOnCallSitePlans
      belowCallSitePlans := belowCallSitePlans }
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := firstName, mutCtx := default, univCtx := [] }
  -- One shared run mirrors Rust's one shared `BlockCache` across
  -- sort_consts (:2717), preseed (:2742) and the member compiles.
  let (sorted, blockRes, cache) ←
    match Ix.CompileM.CompileM.run cenv blockEnv {} (do
        let sorted ← Ix.CompileM.sortConsts consts
        let res ← Ix.CompileM.compileMutualBlock sorted
        pure (sorted, res)) with
    | .ok ((sorted, res), cache) => pure (sorted, res, cache)
    | .error e =>
      throw s!"roundtrip compile for '{firstName.pretty}': {e}"
  let blockConstant := blockRes.block
  let blockAddr := blockRes.blockAddr
  -- Phase-A metadata per name, ctors included (Rust `all_metas`,
  -- :2750/2772/2783/2799-2801), read off the projections array.
  let allMetas : Std.HashMap Ix.Name Ixon.ConstantMeta :=
    blockRes.projections.foldl (init := {}) fun m (n, _, cm) => m.insert n cm

  -- Singleton non-inductive (decompile.rs:2812-2813): `compileMutualBlock`
  -- already emitted the bare (non-Muts) constant for exactly this case.
  let singleton := sorted.length == 1
    && !consts.any (fun c => match c with | .indc _ => true | _ => false)

  -- Verify the recompiled hash matches the original (decompile.rs:2878-3108).
  -- For singletons `blockAddr` IS the constant's compiled address; for
  -- mutual blocks compare against the original block stored in the first
  -- member's projection.
  let origAddr? : Option Address :=
    if singleton then
      (ixonEnv.named.get? firstName).map fun named =>
        match named.original with
        | some (origA, _) => origA
        | none => named.addr
    else
      (ixonEnv.named.get? firstName).bind fun named =>
        let addr := match named.original with
          | some (origA, _) => origA
          | none => named.addr
        (ixonEnv.getConst? addr).map fun c =>
          match c.info with
          | .rPrj p => p.block
          | .dPrj p => p.block
          | .iPrj p => p.block
          | _ => addr -- bare constant, not a projection
  if let some orig := origAddr? then
    if blockAddr != orig then
      -- IX_ROUNDTRIP_DEBUG dump + original-form probe recompile
      -- (decompile.rs:2909-3091) intentionally not ported. The hard
      -- invariant (:3092-3107) is: any mismatch is a regression.
      throw s!"roundtrip recompile hash mismatch for \
'{firstName.pretty}': recompiled={hex12 blockAddr} original={hex12 orig}"

  -- ------------------------------------------------------------------
  -- Phase B: Decompile each member with original metadata
  -- (decompile.rs:3115-3436)
  -- ------------------------------------------------------------------

  -- Synthetic decompile view. Rust decompiles through `stt.env`, whose
  -- interior-mutable names/blobs tables already absorbed Phase A's
  -- writes; the pure port merges the Phase-A `blockNames`/`blockBlobs`
  -- explicitly, stores the just-compiled block + projections, and
  -- installs the ORIGINAL metas on the block's Named entries so
  -- `decompileInductive`'s ctor-meta lookup resolves original-first
  -- (Rust prefers `Named.original` there, decompile.rs:1806-1813).
  let synthEnv : Ixon.Env := Id.run do
    let mut env := { ixonEnv with
      names := cache.blockNames.fold (fun m a n => m.insert a n) ixonEnv.names
      blobs := cache.blockBlobs.fold (fun m a b => m.insert a b) ixonEnv.blobs }
    env := env.storeConst blockAddr blockConstant
    for (_, proj, _) in blockRes.projections do
      env := env.storeConst (ixonContentAddress proj) proj
    for c in consts do
      let mut memberNames : Array Ix.Name := #[c.name]
      if let .indc i := c then
        for ctor in i.ctors do
          memberNames := memberNames.push ctor.cnst.name
      for n in memberNames do
        if let some named := env.named.get? n then
          if let some (_, origMeta) := named.original then
            env := { env with
              named := env.named.insert n { named with constMeta := origMeta } }
    return env
  let denv : DecompileEnv := { ixonEnv := synthEnv }

  -- Extract the Muts members (or the singleton constant), :3120-3123.
  let mutsVec? : Option (Array Ixon.MutConst) :=
    match blockConstant.info with
    | .muts v => some v
    | _ => none

  for (cls, classIdx) in sorted.zipIdx do
    for cnst in cls do
      let name := cnst.name

      -- Original metadata from compile_const_no_aux; fall back to the
      -- Phase-A metadata; skip the member when neither exists
      -- (decompile.rs:3129-3161).
      let origMeta? : Option Ixon.ConstantMeta :=
        match ixonEnv.named.get? name with
        | some named =>
          match named.original with
          | some (_, m) => some m
          | none => allMetas.get? name
        | none => allMetas.get? name
      let some origMeta := origMeta? | continue

      -- Per-member fresh decompile run over the block tables + original
      -- meta. The Lean per-kind decompilers internally rebuild Rust's
      -- `dec_cache` (:3163-3175): block sharing/refs/univs come from
      -- `blockConstant`, `load_meta_extensions` is the `metaSharing`
      -- channel of the passed meta, and the decompile ctx (:3111-3113)
      -- is re-derived from the meta's ctx addrs (identical to
      -- `ctx_to_all(mut_ctx)` — the Phase-A hash equality pins the
      -- layout). `none` = Rust's `_ => continue` arms (:3219/:3232).
      let step? : Option (Except String (Array (Ix.Name × Ix.ConstantInfo))) :=
        match mutsVec? with
        | some muts =>
          -- Multi-class (Muts-wrapped): index into the Muts vec (:3180-3220).
          match muts[classIdx]?, cnst with
          | some (.recr rec), .recr _ =>
            some ((runDecompileM denv
                (decompileRecursor rec blockConstant origMeta)).map
              fun ci => #[(name, ci)])
          | some (.defn d), .defn _ =>
            some ((runDecompileM denv
                (decompileDefinition d blockConstant origMeta)).map
              fun ci => #[(name, ci)])
          | some (.indc ind), .indc _ =>
            some (decompileIndcEntries denv ind blockConstant origMeta name
              generatedConsts)
          | _, _ => none
        | none =>
          -- Singleton (bare constant, no Muts wrapper), :3221-3234.
          match blockConstant.info, cnst with
          | .defn d, .defn _ =>
            some ((runDecompileM denv
                (decompileDefinition d blockConstant origMeta)).map
              fun ci => #[(name, ci)])
          | .recr rec, .recr _ =>
            some ((runDecompileM denv
                (decompileRecursor rec blockConstant origMeta)).map
              fun ci => #[(name, ci)])
          | _, _ => none
      let some decompiled := step? | continue

      -- decompile.rs:3236-3434.
      let entries ← match decompiled with
        | .ok entries => pure entries
        | .error e =>
          -- Debug-gated trace (:3426-3431) omitted; the error propagates
          -- (:3432) — callers recover via `recoverAuxFromOriginal`.
          throw e
      for (n, ci) in entries do
        -- Debug-track Lean-level hash validation against the original
        -- environment (:3239-3327). `==` on Ix.ConstantInfo is full
        -- structural equality over hash-based leaves (Rust get_hash).
        if let some origEnv := origEnv? then
          if let some leanCi := origEnv.get? n then
            if ci != leanCi then
              -- Field-by-field debug dump + print_const_comparison omitted.
              throw s!"roundtrip hash mismatch for '{n.pretty}' \
(decompiled={ciKind ci} original={ciKind leanCi})"
        -- Ixon projection-hash validation for the primary constant
        -- (:3328-3418); constructors have CPrj addresses validated
        -- separately.
        let isPrimary := match ci with
          | .ctorInfo _ => false
          | _ => true
        if isPrimary then
          if !Ix.AuxGen.isAuxGenSuffix n then
            if let some named := ixonEnv.named.get? n then
              if let some (origAddr, _) := named.original then
                let projInfo : Ixon.ConstantInfo := match cnst with
                  | .recr _ => .rPrj ⟨classIdx.toUInt64, blockAddr⟩
                  | .defn _ => .dPrj ⟨classIdx.toUInt64, blockAddr⟩
                  | .indc _ => .iPrj ⟨classIdx.toUInt64, blockAddr⟩
                let projAddr := ixonContentAddress ⟨projInfo, #[], #[], #[]⟩
                if projAddr != origAddr then
                  -- The original might be a singleton (bare constant)
                  -- while roundtrip always wraps in Muts — skip when the
                  -- original is a non-projection or not stored
                  -- (:3362-3376).
                  let origIsSingleton :=
                    match ixonEnv.getConst? origAddr with
                    | none => true -- not found → singleton (not stored)
                    | some c =>
                      match c.info with
                      | .iPrj _ | .rPrj _ | .dPrj _ | .cPrj _ => false
                      | _ => true
                  if !origIsSingleton then
                    let origDetail :=
                      match ixonEnv.getConst? origAddr with
                      | some c =>
                        match c.info with
                        | .rPrj p =>
                          s!"RPrj(idx={p.idx}, block={hex12 p.block})"
                        | .iPrj p =>
                          s!"IPrj(idx={p.idx}, block={hex12 p.block})"
                        | .dPrj p =>
                          s!"DPrj(idx={p.idx}, block={hex12 p.block})"
                        | _ => "other"
                      | none => "none"
                    throw s!"[roundtrip ixon] {n.pretty} proj mismatch: \
orig={hex12 origAddr} [{origDetail}] recomp={hex12 projAddr} \
[idx={classIdx}, block={hex12 blockAddr}]"
        results := results.insert n ci

  return results

/-- Recover an aux constant's Lean-facing view from its ORIGINAL
    compile pair (Rust `recover_aux_from_original`, decompile.rs:4088):
    build a synthetic `Named` from `Named.original` and decompile it via
    `decompileOne`. Returns `none` where Rust returns `false` (no
    original pair, decompile error, entry never landed, or debug-track
    hash mismatch); on success returns the decompiled entries for the
    caller to insert (Rust inserts into `dstt.env` as a side effect).

    Parameter mapping: `ixonEnv` = Rust `stt.env`; `workEnv` = Rust
    `dstt.env` (the decompiled Lean-facing env, for the had-entry and
    recovered-value reads); `origEnv?` = Rust `stt.lean_env` (debug
    track). -/
def recoverAuxFromOriginal (name : Ix.Name) (ixonEnv : Ixon.Env)
    (workEnv : Std.HashMap Ix.Name Ix.ConstantInfo)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo))
    : Option (Array (Ix.Name × Ix.ConstantInfo)) :=
  -- decompile.rs:4093-4099.
  let original := match ixonEnv.named.get? name with
    | some named => named.original
    | none => none
  match original with
  | none => none
  | some (origAddr, origMeta) =>
    let hadEntry := workEnv.contains name
    -- Rust `Named::new(orig_addr, meta)` — no original, no hints.
    let synthetic : Ixon.Named := { addr := origAddr, constMeta := origMeta }
    let denv : DecompileEnv := { ixonEnv }
    match decompileOne denv ixonEnv name synthetic with
    | .error _ => none
    | .ok entries =>
      -- `decompileOne` silently no-ops (ok-empty) when the original's
      -- constant bytes are absent; recovery must not claim success
      -- unless the entry actually landed (decompile.rs:4105-4112).
      let landed := entries.any fun (n, _) => n == name
      if !hadEntry && !landed then
        none
      else
        -- Debug-track validation (decompile.rs:4117-4124): the recovered
        -- constant must be Lean's original bit-for-bit. Read what Rust's
        -- `dstt.env.get(name)` would see AFTER insertion: the fresh
        -- entry when landed, else the pre-existing one.
        match origEnv? with
        | some leanEnv =>
          match leanEnv.get? name with
          | some origCi =>
            let recovered? := match entries.find? (fun (n, _) => n == name) with
              | some (_, ci) => some ci
              | none => workEnv.get? name
            match recovered? with
            | some recovered =>
              if recovered == origCi then some entries else none
            | none => none
          | none => some entries
        | none => some entries

end Ix.DecompileM
