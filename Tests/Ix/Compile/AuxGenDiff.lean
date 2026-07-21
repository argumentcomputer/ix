/-
  aux-gen-diff: cross-compiler differential harness for the compiler-alignment
  work (pure-Lean `Ix.CompileM` vs Rust `crates/compile`).

  Compiles the shared `validateAuxClosure` fixture corpus with the Rust
  compiler (`rsCompilePhasesFFI`), then compiles every SCC block
  INDEPENDENTLY with the pure-Lean compiler against a `CompileEnv` seeded
  with Rust's results for everything else (the `Ix.Commit.mkCompileEnv`
  trick). Because each block sees correct surroundings, a mismatch here is a
  ROOT divergence in that block's own compilation — ripples cannot
  contaminate the inventory.

  Report classes:
  - `defn-only` blocks (no inductive/ctor/recursor member): must MATCH.
    This is the standing drift gate for the five already-mirrored phases
    (canon / graph / condense / sortConsts / sharing / serialization).
  - blocks containing inductive-family members, and Rust-only named entries
    (synthetic `Muts` names, regenerated aux): the expected RED baseline
    that the aux-generation port burns down to zero.

  Exit code: 0 iff no defn-only mismatch, no system error, and no
  missing-in-Rust name (aux-gap classes are informational until the port
  lands; the gate then tightens block by block).

  Invoked via `lake test -- --ignored aux-gen-diff`.
-/
import Ix.CompileM
import Ix.Commit
import Ix.AuxGen.Nested
import Ix.AuxGen.Patches
import Tests.Ix.Compile.ValidateAux

namespace Tests.Compile.AuxGenDiff

open Ix.CompileM (CompilePhases CompileEnv)

/-- FFI (test-ffi only): deterministic text dump of the Rust compiler's
    nested-expansion/canonicity intermediates for every inductive SCC
    block — see `rs_aux_gen_dump_expand` in `crates/ffi/src/compile.rs`
    for the format contract that `leanDumpExpand` below mirrors. -/
@[extern "rs_aux_gen_dump_expand"]
opaque rsAuxGenDumpExpandFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → IO String

/-- FFI (test-ffi only): text dump of `generate_aux_patches` output per
    inductive SCC block — the gate medium for the A3-A6 generator
    milestones (`rs_aux_gen_dump_patches` in crates/ffi/src/compile.rs).
    The Lean comparison filters by patch kind and widens per milestone. -/
@[extern "rs_aux_gen_dump_patches"]
opaque rsAuxGenDumpPatchesFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → IO String

/-- Aux-family name test, by last components (mirrors the Rust aux shapes:
    `.rec`, `.rec_N`, `.recOn`, `.casesOn`, `.below`, `.below_N`, `.brecOn`,
    `.brecOn_N`, `.brecOn.go`, `.brecOn.eq`, `._nested.*`). Purely a
    reporting classifier — never feeds compilation. -/
def isAuxFamily (n : Ix.Name) : Bool :=
  let comps := (n.pretty.splitOn ".")
  comps.any fun c =>
    c == "rec" || c.startsWith "rec_"
    || c == "recOn" || c == "casesOn"
    || c == "below" || c.startsWith "below_"
    || c == "brecOn" || c.startsWith "brecOn_"
    || c == "_nested"

/-- Block kind from the canonical env. `plain-defn` blocks (no
    inductive-family member, no aux-family name) are the drift gate;
    `inductive` and `aux-defn` blocks are the aux-port's red baseline
    (Rust regenerates `.rec`/`.casesOn`/`.below`/`.brecOn`/… and rewrites
    their call sites, which the Lean side cannot yet mirror). -/
def blockKind (env : Ix.Environment) (all : Ix.Set Ix.Name) : String := Id.run do
  let mut sawInd := false
  let mut sawAux := false
  for n in all do
    if isAuxFamily n then sawAux := true
    match env.consts.get? n with
    | some ci =>
      match ci with
      | .inductInfo .. | .ctorInfo .. | .recInfo .. => sawInd := true
      | _ => pure ()
    | none => return "unresolved"
  return if sawInd then "inductive"
    else if sawAux then "aux-defn"
    else "plain-defn"

structure Report where
  blocksTotal : Nat := 0
  blocksMatched : Nat := 0
  defnMismatch : Array Ix.Name := #[]
  defnError : Array (Ix.Name × String) := #[]
  adjMatched : Nat := 0
  adjMismatch : Array Ix.Name := #[]
  adjError : Array (Ix.Name × String) := #[]
  auxMatched : Nat := 0
  auxMismatch : Array Ix.Name := #[]
  auxError : Array (Ix.Name × String) := #[]
  indMatched : Nat := 0
  indMismatch : Array Ix.Name := #[]
  indError : Array (Ix.Name × String) := #[]
  metaMismatch : Nat := 0
  missingInRust : Array Ix.Name := #[]

def sample (xs : Array Ix.Name) (n : Nat := 12) : String :=
  String.intercalate ", " ((xs.toList.take n).map (·.pretty))

/-- Hex render for byte-level divergence hunting (`IX_AUX_DIFF_DEBUG`). -/
def hex (bytes : ByteArray) (maxBytes : Nat := 512) : String := Id.run do
  let toHex (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (n.toNat + 48) else Char.ofNat (n.toNat + 87)
  let mut s := ""
  for i in [:min bytes.size maxBytes] do
    if i > 0 && i % 32 == 0 then s := s.push '\n'
    else if i > 0 && i % 8 == 0 then s := s.push ' '
    let b := bytes.get! i
    s := s.push (toHex (b / 16)) |>.push (toHex (b % 16))
  if bytes.size > maxBytes then s := s ++ s!" …({bytes.size}B)"
  return s

def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  for i in [:min a.size b.size] do
    if a.get! i != b.get! i then return some i
  if a.size != b.size then return some (min a.size b.size)
  return none

/-! ## A2 gate: expansion/canonicity dump parity

`leanDumpExpand` reproduces — byte for byte — the text that
`rs_aux_gen_dump_expand` emits from the Rust side, by running the
pure-Lean `Ix.AuxGen` pipeline (`sortConsts` → `expandNestedBlock` →
`sortAuxByPartitionRefinement` → `computeAuxPerm` →
`sourceAuxOrderWithOwner`) per inductive SCC block. The gate is a line
diff; the first diverging line pinpoints the phase. -/

/-- Expr content hash as lowercase hex (mirrors Rust
    `Address::from_blake3_hash(e.get_hash()).hex()`). -/
private def exprAddr (e : Ix.Expr) : String := toString e.getHash

/-- Per-block half of the Lean dump (runs in CompileM so `sortConsts` and
    the expansion see the Rust-seeded `CompileEnv`). -/
def leanDumpBlock (lo : Ix.Name) (all : Array Ix.Name)
    : Ix.CompileM.CompileM String := do
  let mut out := s!"block {lo.pretty}\n"

  -- Mirror compile_mutual's cs construction over pretty-sorted members.
  let mut cs : Array Ix.MutConst := #[]
  for n in all do
    match (← Ix.AuxGen.lookupConst? n) with
    | none => return out ++ s!"error collect missing {n.pretty}\n"
    | some ci =>
      match ci with
      | .inductInfo val =>
        cs := cs.push (← Ix.CompileM.MutConst.mkIndc val)
      | .defnInfo val => cs := cs.push (Ix.MutConst.fromDefinitionVal val)
      | .opaqueInfo val => cs := cs.push (Ix.MutConst.fromOpaqueVal val)
      | .thmInfo val => cs := cs.push (Ix.MutConst.fromTheoremVal val)
      | .recInfo val => cs := cs.push (.recr val)
      | _ => pure ()

  let sortedClasses ← Ix.CompileM.sortConsts cs.toList

  let orderedOriginals : Array Ix.Name :=
    (sortedClasses.map fun c => (c.head!).name).toArray
  let mut aliasToRep : Std.HashMap Ix.Name Ix.Name := {}
  for cls in sortedClasses do
    let rep := (cls.head!).name
    for aliasConst in cls.drop 1 do
      aliasToRep := aliasToRep.insert aliasConst.name rep
  let originalAll : Array Ix.Name := Id.run do
    for c in cs do
      if let .indc ind := c then
        return ind.all
    return #[]

  let mut metadataHasNested := false
  for name in originalAll do
    if let some (.inductInfo v) ← Ix.AuxGen.lookupConst? name then
      if v.numNested > 0 then metadataHasNested := true

  let expanded ← Ix.AuxGen.expandNestedBlock orderedOriginals aliasToRep
  let structuralHasNested : Bool := expanded.types.size > expanded.nOriginals

  out := out ++ s!"flags meta_nested={metadataHasNested} structural_nested={structuralHasNested} n_classes={sortedClasses.length}\n"
  out := out ++ s!"levels {" ".intercalate (expanded.levelParams.toList.map (·.pretty))}\n"
  for (n, i) in orderedOriginals.zipIdx do
    out := out ++ s!"original {i} {n.pretty}\n"

  for (mem, i) in expanded.types.zipIdx do
    out := out ++ s!"pre {i} name={mem.name.pretty} owner={mem.sourceOwner.pretty} params={mem.nParams} indices={mem.nIndices} typ={exprAddr mem.typ}\n"
    for (ctor, j) in mem.ctors.zipIdx do
      out := out ++ s!"prector {i} {j} name={ctor.name.pretty} fields={ctor.nFields} typ={exprAddr ctor.typ}\n"
  -- Keys are unique (map keys), so first-component ordering is total.
  let nestedEntries := (expanded.auxToNested.toList.map
    fun (n, e) => (n.pretty, exprAddr e)).toArray.qsort (fun a b => a.1 < b.1)
  for (n, h) in nestedEntries do
    out := out ++ s!"nested {n} {h}\n"
  let auxctorEntries := (expanded.auxCtorMap.toList.map
    fun (c, orig, ind) => (c.pretty, orig.pretty, ind.pretty)).toArray.qsort
      (fun a b => a.1 < b.1)
  for (c, o, i) in auxctorEntries do
    out := out ++ s!"auxctor {c} {o} {i}\n"

  if !(metadataHasNested && structuralHasNested) then
    return out

  let (expanded, sortperm) ← Ix.AuxGen.sortAuxByPartitionRefinement expanded
  out := out ++ s!"sortperm {" ".intercalate (sortperm.toList.map toString)}\n"
  for (mem, i) in expanded.types.zipIdx do
    if i < expanded.nOriginals then
      continue
    out := out ++ s!"post {i} name={mem.name.pretty} owner={mem.sourceOwner.pretty} typ={exprAddr mem.typ}\n"
    for (ctor, j) in mem.ctors.zipIdx do
      out := out ++ s!"postctor {i} {j} name={ctor.name.pretty} typ={exprAddr ctor.typ}\n"

  let mut origToCanonMap : Std.HashMap Ix.Name Ix.Name := {}
  for cls in sortedClasses do
    let rep := (cls.head!).name
    for m in cls do
      origToCanonMap := origToCanonMap.insert m.name rep
  let cenv ← Ix.CompileM.getCompileEnv
  let resolveAddr : Ix.Name → Option Address :=
    fun n => (cenv.nameToNamed.get? n).map (·.addr)
  let perm ← Ix.AuxGen.computeAuxPerm expanded originalAll origToCanonMap resolveAddr
  let permStrs := perm.toList.map fun p =>
    if p == Ix.AuxGen.PERM_OUT_OF_SCC then "out" else toString p
  out := out ++ s!"perm {" ".intercalate permStrs}\n"

  let sourceEntries ← Ix.AuxGen.sourceAuxOrderWithOwner originalAll
  for ((owner, head, specs), j) in sourceEntries.zipIdx do
    let specStrs := ",".intercalate (specs.toList.map exprAddr)
    out := out ++ s!"source {j} owner={owner.pretty} head={head.pretty} specs={specStrs}\n"

  return out

/-- Lean half of the patches dump for one block: production inputs
    (cs → sortConsts → classNames/originalAll) into `generateAuxPatches`
    under a fresh bridge context (mirroring the Rust endpoint's fresh
    `KernelCtx::new()` per block), rendered in the exact
    `rs_aux_gen_dump_patches` line format. -/
def leanDumpPatchesBlock (lo : Ix.Name) (all : Array Ix.Name)
    : Ix.CompileM.CompileM String := do
  let mut out := s!"block {lo.pretty}\n"
  let mut cs : Array Ix.MutConst := #[]
  for n in all do
    match (← Ix.AuxGen.lookupConst? n) with
    | none => pure ()
    | some ci =>
      match ci with
      | .inductInfo val => cs := cs.push (← Ix.CompileM.MutConst.mkIndc val)
      | .defnInfo val => cs := cs.push (Ix.MutConst.fromDefinitionVal val)
      | .opaqueInfo val => cs := cs.push (Ix.MutConst.fromOpaqueVal val)
      | .thmInfo val => cs := cs.push (Ix.MutConst.fromTheoremVal val)
      | .recInfo val => cs := cs.push (.recr val)
      | _ => pure ()
  let sortedClasses ← Ix.CompileM.sortConsts cs.toList
  let classNames : Array (Array Ix.Name) :=
    (sortedClasses.map fun c => (c.map (·.name)).toArray).toArray
  let originalAll : Array Ix.Name := Id.run do
    for c in cs do
      if let .indc ind := c then
        return ind.all
    return #[]
  let cenv ← Ix.CompileM.getCompileEnv
  let maps := Ix.AuxGen.AddrMaps.ofCompileEnv cenv
  let auxOut ← (Ix.AuxGen.generateAuxPatches classNames originalAll maps).run'
    Ix.AuxGen.AuxKernelCtx.new
  let patchNames := (auxOut.patches.toList.map (·.1)).toArray.qsort
    (fun a b => a.pretty < b.pretty)
  for name in patchNames do
    match auxOut.patches.get? name with
    | some (.recr rv) =>
      let lps := ",".intercalate (rv.cnst.levelParams.toList.map (·.pretty))
      let allStr := ",".intercalate (rv.all.toList.map (·.pretty))
      out := out ++ s!"patch {name.pretty} kind=rec lvls={lps} k={rv.k} params={rv.numParams} indices={rv.numIndices} motives={rv.numMotives} minors={rv.numMinors} all={allStr} typ={exprAddr rv.cnst.type}\n"
      for (rule, i) in rv.rules.zipIdx do
        out := out ++ s!"rule {name.pretty} {i} ctor={rule.ctor.pretty} fields={rule.nfields} rhs={exprAddr rule.rhs}\n"
    | _ => pure ()
  return out

/-- Whole-env Lean patches dump (same block selection/order as Rust). -/
def leanDumpPatches (cenv : CompileEnv) (condensed : Ix.CondensedBlocks)
    : String := Id.run do
  let mut blocks : Array (String × Ix.Name × Array Ix.Name) := #[]
  for (lo, members) in condensed.blocks do
    let sortedAll := (members.toArray.map (·, ())).map (·.1)
      |>.qsort (fun a b => a.pretty < b.pretty)
    let hasInd := sortedAll.any fun n =>
      match cenv.env.consts.get? n with
      | some (.inductInfo _) => true
      | _ => false
    if hasInd then
      blocks := blocks.push (lo.pretty, lo, sortedAll)
  blocks := blocks.qsort (fun (a, _, _) (b, _, _) => a < b)
  let mut out := ""
  for (_, lo, all) in blocks do
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := lo, mutCtx := default, univCtx := [] }
    match Ix.CompileM.CompileM.run cenv blockEnv {} (leanDumpPatchesBlock lo all) with
    | .ok (s, _) => out := out ++ s
    | .error e => out := out ++ s!"block {lo.pretty}\nerror generate {e}\n"
  return out

/-- Keep only `block` headers plus patch/rule/error lines whose kind is in
    the whitelist — the comparison scope widens per milestone (A3: rec;
    A4: +casesOn/recOn; A5: +below*; A6: +brecOn+aliases). -/
def filterPatchDump (dump : String) (kinds : List String) : String :=
  let keep (l : String) : Bool :=
    l.startsWith "block " || l.startsWith "error "
    || (l.startsWith "patch "
        && kinds.any (fun k => ((l ++ " ").splitOn (" kind=" ++ k ++ " ")).length > 1))
    || (l.startsWith "rule " && kinds.contains "rec")
    || (l.startsWith "belowctor " && kinds.contains "belowIndc")
    || (l.startsWith "alias " && kinds.contains "alias")
  String.intercalate "\n" ((dump.splitOn "\n").filter keep)

/-- Whole-env Lean dump over the same block selection/order as the Rust
    endpoint (inductive-containing SCCs, sorted by lowlink pretty name,
    members pretty-sorted). CompileM errors surface as `error` lines so a
    divergence shows in the diff instead of aborting. -/
def leanDumpExpand (cenv : CompileEnv) (condensed : Ix.CondensedBlocks)
    : String := Id.run do
  let mut blocks : Array (String × Ix.Name × Array Ix.Name) := #[]
  for (lo, members) in condensed.blocks do
    let all := (members.toArray.map (·, ())).map (·.1)
    let sortedAll := all.qsort (fun a b => a.pretty < b.pretty)
    let hasInd := sortedAll.any fun n =>
      match cenv.env.consts.get? n with
      | some (.inductInfo _) => true
      | _ => false
    if hasInd then
      blocks := blocks.push (lo.pretty, lo, sortedAll)
  blocks := blocks.qsort (fun (a, _, _) (b, _, _) => a < b)

  let mut out := ""
  for (_, lo, all) in blocks do
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := lo, mutCtx := default, univCtx := [] }
    match Ix.CompileM.CompileM.run cenv blockEnv {} (leanDumpBlock lo all) with
    | .ok (s, _) => out := out ++ s
    | .error e => out := out ++ s!"block {lo.pretty}\nerror compilem {e}\n"
  return out

/-- Compare the two dumps line-by-line; report the first divergence with
    surrounding context. Returns true iff identical. -/
def compareDumps (rust lean : String) : IO Bool := do
  if rust == lean then
    return true
  let rustLines := rust.splitOn "\n" |>.toArray
  let leanLines := lean.splitOn "\n" |>.toArray
  let n := min rustLines.size leanLines.size
  let mut firstDiff : Option Nat := none
  for i in [0:n] do
    if firstDiff.isNone && rustLines[i]! != leanLines[i]! then
      firstDiff := some i
  let diffAt := firstDiff.getD n
  IO.println s!"[aux-gen-diff] DUMP DIVERGENCE at line {diffAt} (rust {rustLines.size} lines, lean {leanLines.size} lines)"
  let lo := if diffAt ≥ 3 then diffAt - 3 else 0
  for i in [lo:min (diffAt + 4) n] do
    let marker := if i == diffAt then ">" else " "
    IO.println s!"[aux-gen-diff] {marker} rust| {rustLines[i]!}"
    IO.println s!"[aux-gen-diff] {marker} lean| {leanLines[i]!}"
  return false

def run (env : Lean.Environment) : IO UInt32 := do
  let debugConst? := (← IO.getEnv "IX_AUX_DIFF_DEBUG")
  IO.println "[aux-gen-diff] collecting fixture closure..."
  let filtered := validateAuxClosure env
  IO.println s!"[aux-gen-diff] {filtered.length} constants"

  IO.println "[aux-gen-diff] Rust compile (rsCompilePhases)..."
  let raw ← Ix.CompileM.rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let condensed := raw.condensed.toCondensedBlocks
  let rustEnv := raw.compileEnv.toEnv
  let phases : CompilePhases := { rawEnv, condensed, compileEnv := rustEnv }
  IO.println s!"[aux-gen-diff] Rust: {rustEnv.named.size} named, {condensed.blocks.size} blocks"

  -- CompileEnv seeded with Rust results: every block compiles in isolation
  -- against correct surroundings.
  let cenv : CompileEnv := Ix.Commit.mkCompileEnv phases

  let mut rep : Report := {}
  -- Names covered by Lean block outputs (to compute Rust-only extras).
  let mut leanNames : Ix.Set Ix.Name := {}

  -- Deterministic block order for stable output.
  let blocks := condensed.blocks.toArray.qsort fun (a, _) (b, _) =>
    a.pretty < b.pretty

  IO.println s!"[aux-gen-diff] compiling {blocks.size} blocks with Ix.CompileM..."
  for (lo, all) in blocks do
    rep := { rep with blocksTotal := rep.blocksTotal + 1 }
    let kind := Id.run do
      let base := blockKind rawEnv all
      if base != "plain-defn" then return base
      -- A plain defn whose body DIRECTLY references an aux-family
      -- constant can be hit by Rust's call-site surgery (arg
      -- reorder/head rewrite at `.rec`/`.brecOn`/`.below` call sites) —
      -- expected red until the surgery port lands. Verified causally:
      -- the `_sizeOf_N` mismatches show a restructured application
      -- spine, not a table permutation.
      match condensed.blockRefs.get? lo with
      | some refs => if refs.any isAuxFamily then "aux-adjacent" else "plain-defn"
      | none => "plain-defn"
    match Ix.CompileM.compileBlockPure cenv all lo with
    | .error e =>
      if kind == "inductive" then
        rep := { rep with indError := rep.indError.push (lo, toString e) }
      else if kind == "aux-defn" then
        rep := { rep with auxError := rep.auxError.push (lo, toString e) }
      else if kind == "aux-adjacent" then
        rep := { rep with adjError := rep.adjError.push (lo, toString e) }
      else
        rep := { rep with defnError := rep.defnError.push (lo, toString e) }
    | .ok (result, _cache) =>
      -- Member name → Lean address, mirroring the parallel driver's
      -- projection handling (CompileM.compileEnvParallel).
      let mut outs : Array (Ix.Name × Address × Ixon.ConstantMeta) := #[]
      if result.projections.isEmpty then
        outs := #[(lo, Address.blake3 result.blockBytes, result.blockMeta)]
      else
        for (name, proj, constMeta) in result.projections do
          outs := outs.push (name, Address.blake3 (Ixon.ser proj), constMeta)
      let mut blockOk := true
      for (name, leanAddr, leanMeta) in outs do
        leanNames := leanNames.insert name
        match rustEnv.named.get? name with
        | some rustNamed =>
          if leanAddr != rustNamed.addr then blockOk := false
          if debugConst? == some name.pretty then
            let leanBytes :=
              if result.projections.isEmpty then result.blockBytes
              else (result.projections.findSome? fun (n, proj, _) =>
                if n == name then some (Ixon.ser proj) else none).getD default
            let rustBytes := rustEnv.getConst? rustNamed.addr
              |>.map Ixon.ser |>.getD default
            IO.println s!"[debug] {name.pretty}: lean={leanAddr} rust={rustNamed.addr}"
            IO.println s!"[debug] block bytes lean={result.blockBytes.size}B"
            IO.println s!"[debug] proj/const first diff at {repr (firstDiff leanBytes rustBytes)}"
            IO.println s!"[debug] lean bytes:\n{hex leanBytes}"
            IO.println s!"[debug] rust bytes:\n{hex rustBytes}"
            -- If the projection points at a block, also dump both blocks.
            let rustBlockBytes := (rustEnv.getConst? rustNamed.addr).bind (fun c =>
              match c.info with
              | .dPrj p => rustEnv.getConst? p.block |>.map Ixon.ser
              | _ => none) |>.getD default
            if rustBlockBytes.size > 0 then
              IO.println s!"[debug] rust PARENT block ({rustBlockBytes.size}B) first diff vs lean block: {repr (firstDiff result.blockBytes rustBlockBytes)}"
              IO.println s!"[debug] lean block:\n{hex result.blockBytes}"
              IO.println s!"[debug] rust block:\n{hex rustBlockBytes}"
          if leanMeta != rustNamed.constMeta then
            rep := { rep with metaMismatch := rep.metaMismatch + 1 }
        | none =>
          rep := { rep with missingInRust := rep.missingInRust.push name }
      if blockOk then
        rep := { rep with blocksMatched := rep.blocksMatched + 1 }
        if kind == "inductive" then
          rep := { rep with indMatched := rep.indMatched + 1 }
        else if kind == "aux-defn" then
          rep := { rep with auxMatched := rep.auxMatched + 1 }
        else if kind == "aux-adjacent" then
          rep := { rep with adjMatched := rep.adjMatched + 1 }
      else if kind == "inductive" then
        rep := { rep with indMismatch := rep.indMismatch.push lo }
      else if kind == "aux-defn" then
        rep := { rep with auxMismatch := rep.auxMismatch.push lo }
      else if kind == "aux-adjacent" then
        rep := { rep with adjMismatch := rep.adjMismatch.push lo }
      else
        rep := { rep with defnMismatch := rep.defnMismatch.push lo }

  -- Rust-only named entries: synthetic Muts names + anything the Lean side
  -- never emitted (aux regeneration extras land here until the port).
  let mut rustOnlyAux : Array Ix.Name := #[]
  let mut rustOnlyOther : Array Ix.Name := #[]
  for (name, _) in rustEnv.named do
    if !leanNames.contains name then
      if isAuxFamily name then rustOnlyAux := rustOnlyAux.push name
      else rustOnlyOther := rustOnlyOther.push name

  IO.println ""
  IO.println s!"[aux-gen-diff] blocks: {rep.blocksTotal} total, {rep.blocksMatched} fully matched"
  IO.println s!"[aux-gen-diff]   plain-defn mismatches: {rep.defnMismatch.size}  (drift gate — must be 0)"
  if !rep.defnMismatch.isEmpty then
    IO.println s!"[aux-gen-diff]     e.g. {sample rep.defnMismatch}"
  IO.println s!"[aux-gen-diff]   plain-defn errors: {rep.defnError.size}"
  for (n, e) in rep.defnError.toList.take 6 do
    IO.println s!"[aux-gen-diff]     {n.pretty}: {e}"
  IO.println s!"[aux-gen-diff]   aux-adjacent defns: {rep.adjMatched} matched, {rep.adjMismatch.size} mismatched, {rep.adjError.size} errored (call-site surgery red)"
  if !rep.adjMismatch.isEmpty then
    IO.println s!"[aux-gen-diff]     mismatch e.g. {sample rep.adjMismatch}"
  IO.println s!"[aux-gen-diff]   aux-defn blocks: {rep.auxMatched} matched, {rep.auxMismatch.size} mismatched, {rep.auxError.size} errored (red baseline)"
  if !rep.auxMismatch.isEmpty then
    IO.println s!"[aux-gen-diff]     mismatch e.g. {sample rep.auxMismatch}"
  for (n, e) in rep.auxError.toList.take 4 do
    IO.println s!"[aux-gen-diff]     error e.g. {n.pretty}: {e}"
  IO.println s!"[aux-gen-diff]   inductive blocks: {rep.indMatched} matched, {rep.indMismatch.size} mismatched, {rep.indError.size} errored (red baseline)"
  if !rep.indMismatch.isEmpty then
    IO.println s!"[aux-gen-diff]     mismatch e.g. {sample rep.indMismatch}"
  for (n, e) in rep.indError.toList.take 6 do
    IO.println s!"[aux-gen-diff]     error e.g. {n.pretty}: {e}"
  IO.println s!"[aux-gen-diff]   meta mismatches (informational): {rep.metaMismatch}"
  IO.println s!"[aux-gen-diff]   missing in Rust: {rep.missingInRust.size}"
  if !rep.missingInRust.isEmpty then
    IO.println s!"[aux-gen-diff]     e.g. {sample rep.missingInRust}"
  IO.println s!"[aux-gen-diff]   Rust-only named: {rustOnlyAux.size} aux-family, {rustOnlyOther.size} other"
  IO.println s!"[aux-gen-diff]     aux e.g. {sample rustOnlyAux}"
  IO.println s!"[aux-gen-diff]     other e.g. {sample rustOnlyOther}"

  let gateOk := rep.defnMismatch.isEmpty && rep.defnError.isEmpty
    && rep.adjError.isEmpty && rep.missingInRust.isEmpty
  IO.println ""
  IO.println s!"[aux-gen-diff] drift gate: {if gateOk then "PASS" else "FAIL"}"

  -- A2 gate: expansion/canonicity dump parity (Rust intermediates vs the
  -- pure-Lean Ix.AuxGen pipeline).
  IO.println "[aux-gen-diff] A2: expansion dump (Rust)..."
  let rustDump ← rsAuxGenDumpExpandFFI filtered
  IO.println "[aux-gen-diff] A2: expansion dump (Lean)..."
  let leanDump := leanDumpExpand cenv condensed
  let dumpOk ← compareDumps rustDump leanDump
  IO.println s!"[aux-gen-diff] expansion gate: {if dumpOk then "PASS" else "FAIL"} ({(rustDump.splitOn "\n").length} dump lines)"

  -- A3+ gate: generated-patch parity, kind-filtered (widens per milestone).
  IO.println "[aux-gen-diff] A3: patches dump (Rust)..."
  let rustPatchDump ← rsAuxGenDumpPatchesFFI filtered
  IO.println "[aux-gen-diff] A3: patches dump (Lean)..."
  let leanPatchDump := leanDumpPatches cenv condensed
  let kinds := ["rec"]
  let patchesOk ← compareDumps (filterPatchDump rustPatchDump kinds)
    (filterPatchDump leanPatchDump kinds)
  let recCount := ((filterPatchDump rustPatchDump kinds).splitOn "\n").filter
    (·.startsWith "patch ") |>.length
  IO.println s!"[aux-gen-diff] patches gate ({", ".intercalate kinds}): {if patchesOk then "PASS" else "FAIL"} ({recCount} patches compared)"
  -- Optional dump save for inspection (IX_AUX_DUMP_OUT=<path-prefix>).
  match (← IO.getEnv "IX_AUX_DUMP_OUT") with
  | some pathPrefix =>
    IO.FS.writeFile (pathPrefix ++ ".rust.txt") rustDump
    IO.FS.writeFile (pathPrefix ++ ".lean.txt") leanDump
    IO.FS.writeFile (pathPrefix ++ ".patches.rust.txt") rustPatchDump
    IO.FS.writeFile (pathPrefix ++ ".patches.lean.txt") leanPatchDump
    IO.println s!"[aux-gen-diff] dumps saved to {pathPrefix}.*.txt"
  | none => pure ()

  return if gateOk && dumpOk && patchesOk then 0 else 1

end Tests.Compile.AuxGenDiff
