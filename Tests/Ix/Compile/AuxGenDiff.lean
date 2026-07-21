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
import Tests.Ix.Compile.ValidateAux

namespace Tests.Compile.AuxGenDiff

open Ix.CompileM (CompilePhases CompileEnv)

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
  return if gateOk then 0 else 1

end Tests.Compile.AuxGenDiff
