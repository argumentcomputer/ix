/-
  Cross-implementation tests for Compilation.
  Verifies Lean and Rust implementations produce equivalent results.
-/

module
public import Ix.Ixon
public import Ix.Environment
public import Ix.Address
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.CondenseM
public import Ix.GraphM
public import Ix.Sharing
public import Lean
public import LSpec
public import Tests.Ix.Fixtures

open LSpec

namespace Tests.Compile

/-! ## Helpers -/

/-- Show hex dump of first N bytes -/
def hexDump (bytes : ByteArray) (maxBytes : Nat := 64) : String := Id.run do
  let mut s := ""
  for i in [:min bytes.size maxBytes] do
    if i > 0 && i % 16 == 0 then s := s ++ "\n"
    else if i > 0 && i % 8 == 0 then s := s ++ "  "
    else if i > 0 then s := s ++ " "
    let b := bytes.get! i
    let hi := b / 16
    let lo := b % 16
    let toHex (n : UInt8) : Char := if n < 10 then Char.ofNat (n.toNat + 48) else Char.ofNat (n.toNat + 87)
    s := s ++ String.singleton (toHex hi) ++ String.singleton (toHex lo)
  if bytes.size > maxBytes then s := s ++ s!" ... ({bytes.size} bytes total)"
  return s

/-- Find first byte position where two arrays differ -/
def findFirstDiff (a b : ByteArray) : Option Nat := Id.run do
  for i in [:min a.size b.size] do
    if a.get! i != b.get! i then return some i
  if a.size != b.size then return some (min a.size b.size)
  return none

/-! ## Comparison Results -/

/-- Result of comparing a single constant -/
structure ConstCompareResult where
  name : Ix.Name
  leanAddr : Address
  rustAddr : Address
  isMatch : Bool
  leanBytes : ByteArray
  rustBytes : ByteArray

/-- Result of a per-constant metadata comparison -/
structure MetaMismatch where
  name : Ix.Name
  leanByType : Nat × Nat × Nat × Nat × Nat  -- (binder, letBinder, ref, prj, mdata)
  rustByType : Nat × Nat × Nat × Nat × Nat

/-- Result of comparing all constants -/
structure CompareResult where
  totalConstants : Nat
  matchingConstants : Nat
  mismatchedConstants : Array ConstCompareResult
  metaMismatches : Array MetaMismatch
  fullMetaMismatches : Array (Ix.Name × Ixon.ConstantMeta × Ixon.ConstantMeta)
  missingInRust : Array Ix.Name
  missingInLean : Array Ix.Name

/-- Compare Lean and Rust compilation results using Ixon.Env -/
def compareEnvResults
    (leanEnv rustEnv : Ixon.Env)
    : CompareResult := Id.run do
  let mut matching := 0
  let mut mismatched : Array ConstCompareResult := #[]
  let mut metaMismatches : Array MetaMismatch := #[]
  let mut fullMetaMismatches : Array (Ix.Name × Ixon.ConstantMeta × Ixon.ConstantMeta) := #[]
  let mut missingInRust : Array Ix.Name := #[]
  let mut missingInLean : Array Ix.Name := #[]

  -- Check all Lean constants against Rust
  for (name, leanNamed) in leanEnv.named do
    let leanAddr := leanNamed.addr
    match rustEnv.named.get? name with
    | some rustNamed =>
      let rustAddr := rustNamed.addr
      if leanAddr == rustAddr then
        matching := matching + 1
      else
        let leanBytes := leanEnv.consts.get? leanAddr |>.map Ixon.ser |>.getD default
        let rustBytes := rustEnv.consts.get? rustAddr |>.map Ixon.ser |>.getD default
        mismatched := mismatched.push ⟨name, leanAddr, rustAddr, false, leanBytes, rustBytes⟩
      -- Check metadata regardless of addr match
      let leanMeta := leanNamed.constMeta.exprMetaByType
      let rustMeta := rustNamed.constMeta.exprMetaByType
      if leanMeta != rustMeta then
        metaMismatches := metaMismatches.push ⟨name, leanMeta, rustMeta⟩
      -- Full ConstantMeta comparison (catches all/ctx/lvls/hints differences)
      if leanNamed.constMeta != rustNamed.constMeta then
        fullMetaMismatches := fullMetaMismatches.push (name, leanNamed.constMeta, rustNamed.constMeta)
    | none =>
      missingInRust := missingInRust.push name

  -- Check for constants in Rust but not in Lean
  for (name, _) in rustEnv.named do
    if !leanEnv.named.contains name then
      missingInLean := missingInLean.push name

  {
    totalConstants := leanEnv.named.size
    matchingConstants := matching
    mismatchedConstants := mismatched
    metaMismatches
    fullMetaMismatches
    missingInRust
    missingInLean
  }

/-- Serialize a Lean Ixon.Env to bytes -/
def serializeEnv (env : Ixon.Env) : ByteArray :=
  Ixon.serEnv env

/-! ## Integrated Test -/

/-- Cross-implementation compilation test using the new CompilePhases API -/
def testCrossImpl : TestSeq :=
  .individualIO "Compilation Cross-Implementation" none (do
    let leanEnv ← get_env!
    let totalConsts := leanEnv.constants.toList.length

    IO.println s!"[Test] Cross-Implementation Compilation Test"
    IO.println s!"[Test] Environment has {totalConsts} constants"
    IO.println ""

    -- Step 1: Get all compilation phases from Rust in one call
    IO.println s!"[Step 1] Running Rust compilation pipeline (rsCompilePhases)..."
    let rustStart ← IO.monoMsNow
    let phases ← Ix.CompileM.rsCompilePhases leanEnv
    let rustTime := (← IO.monoMsNow) - rustStart

    IO.println s!"[Step 1]   Rust: {phases.rawEnv.consts.size} consts, {phases.condensed.blocks.size} blocks, {phases.compileEnv.constCount} compiled in {rustTime}ms"
    IO.println ""

    -- Step 2: Compile with Lean using Rust's rawEnv and condensed blocks
    IO.println s!"[Step 2] Running Lean parallel compilation..."
    let leanStart ← IO.monoMsNow

    match ← Ix.CompileM.compileEnvParallel phases.rawEnv phases.condensed (rustRef := none) (dbg := true) with
    | .error err =>
      let leanTime := (← IO.monoMsNow) - leanStart
      IO.println s!"[Step 2] Compilation failed after {leanTime}ms"
      if let some sysErr := err.systemError then
        IO.println s!"[Error] {sysErr}"
        return (false, 0, 0, some sysErr)
      return (false, 0, 0, some "Compilation failed")

    | .ok (leanIxonEnv, totalBytes) =>
      let leanTime := (← IO.monoMsNow) - leanStart
      IO.println s!"[Step 2]   Lean: {leanIxonEnv.constCount} constants, {fmtBytes totalBytes} in {leanTime}ms"
      IO.println ""

      -- Step 3: Compare compilation results
      IO.println s!"[Step 3] Comparing Lean and Rust results..."
      let compareStart ← IO.monoMsNow

      let result := compareEnvResults leanIxonEnv phases.compileEnv

      IO.print s!"[Step 3]   Compared {result.totalConstants} "
      let compareTime := (← IO.monoMsNow) - compareStart
      IO.println s!"constants in {compareTime}ms"

      if result.mismatchedConstants.isEmpty && result.missingInRust.isEmpty && result.missingInLean.isEmpty then
        IO.println s!"[Step 3]   All {result.matchingConstants} constants match! ✓"

        if !result.metaMismatches.isEmpty then
          IO.println s!"[Step 3]   Metadata mismatches: {result.metaMismatches.size} constants"
          -- Aggregate deltas
          let mut totB : Int := 0; let mut totL : Int := 0; let mut totR : Int := 0
          let mut totP : Int := 0; let mut totM : Int := 0
          let mut negCount := 0  -- constants where Rust has MORE metadata
          for mm in result.metaMismatches do
            let (lb, ll, lr, lp, lm) := mm.leanByType
            let (rb, rl, rr, rp, rm) := mm.rustByType
            let db := (Int.ofNat lb) - (Int.ofNat rb)
            let dl := (Int.ofNat ll) - (Int.ofNat rl)
            let dr := (Int.ofNat lr) - (Int.ofNat rr)
            let dp := (Int.ofNat lp) - (Int.ofNat rp)
            let dm := (Int.ofNat lm) - (Int.ofNat rm)
            totB := totB + db; totL := totL + dl; totR := totR + dr
            totP := totP + dp; totM := totM + dm
            if db < 0 || dl < 0 || dr < 0 || dp < 0 || dm < 0 then
              negCount := negCount + 1
          IO.println s!"[Step 3]   Totals: Δbinder={totB} Δlet={totL} Δref={totR} Δprj={totP} Δmdata={totM}"
          IO.println s!"[Step 3]   Constants where Rust > Lean: {negCount}"
          -- Show first 30 mismatches
          for mm in result.metaMismatches[:min 30 result.metaMismatches.size] do
            let (lb, ll, lr, lp, lm) := mm.leanByType
            let (rb, rl, rr, rp, rm) := mm.rustByType
            let db := (Int.ofNat lb) - (Int.ofNat rb)
            let dl := (Int.ofNat ll) - (Int.ofNat rl)
            let dr := (Int.ofNat lr) - (Int.ofNat rr)
            let dp := (Int.ofNat lp) - (Int.ofNat rp)
            let dm := (Int.ofNat lm) - (Int.ofNat rm)
            IO.println s!"  {mm.name}  Δbinder={db} Δlet={dl} Δref={dr} Δprj={dp} Δmdata={dm}"
          -- Detailed dump for first mismatch with Δref>0
          if let some mm := result.metaMismatches.find? (fun mm =>
            let (_, _, lr, _, _) := mm.leanByType
            let (_, _, rr, _, _) := mm.rustByType
            lr > rr) then
            IO.println s!"\n[Detail] {mm.name}"
            let leanNamed := leanIxonEnv.named.get! mm.name
            let rustNamed := phases.compileEnv.named.get! mm.name
            let dumpArena (label : String) (tag : String) (arena : Ixon.ExprMetaArena) : IO Unit := do
              IO.println s!"  {label} {tag}: {arena.nodes.size} nodes"
              for i in [:arena.nodes.size] do
                IO.println s!"    [{i}] {reprStr arena.nodes[i]!}"
            let dumpMeta (label : String) (cm : Ixon.ConstantMeta) : IO Unit := do
              match cm with
              | .defn _ _ _ _ _ arena typeRoot valueRoot => do
                dumpArena label "arena" arena
                IO.println s!"  {label} typeRoot={typeRoot} valueRoot={valueRoot}"
              | .axio _ _ arena typeRoot => do
                dumpArena label "arena" arena
                IO.println s!"  {label} typeRoot={typeRoot}"
              | .quot _ _ arena typeRoot => do
                dumpArena label "arena" arena
                IO.println s!"  {label} typeRoot={typeRoot}"
              | .ctor _ _ _ arena typeRoot => do
                dumpArena label "arena" arena
                IO.println s!"  {label} typeRoot={typeRoot}"
              | .recr _ _ _ _ _ arena typeRoot ruleRoots => do
                dumpArena label "arena" arena
                IO.println s!"  {label} typeRoot={typeRoot} ruleRoots={ruleRoots}"
              | .indc _ _ _ _ _ arena typeRoot => do
                dumpArena label "arena" arena
                IO.println s!"  {label} typeRoot={typeRoot}"
              | .empty => IO.println s!"  {label}: empty"
            dumpMeta "Lean" leanNamed.constMeta
            dumpMeta "Rust" rustNamed.constMeta
        else
          IO.println s!"[Step 3]   All metadata matches! ✓"

        -- Check full ConstantMeta equality (catches all/ctx/lvls/hints differences)
        if !result.fullMetaMismatches.isEmpty then
          IO.println s!"[Step 3]   Full ConstantMeta mismatches: {result.fullMetaMismatches.size}"
          for (name, leanCM, rustCM) in result.fullMetaMismatches[:min 5 result.fullMetaMismatches.size] do
            IO.println s!"  {name}:"
            -- Compare variant tags
            let leanTag := match leanCM with | .empty => "empty" | .defn .. => "defn" | .axio .. => "axio" | .quot .. => "quot" | .indc .. => "indc" | .ctor .. => "ctor" | .recr .. => "recr"
            let rustTag := match rustCM with | .empty => "empty" | .defn .. => "defn" | .axio .. => "axio" | .quot .. => "quot" | .indc .. => "indc" | .ctor .. => "ctor" | .recr .. => "recr"
            if leanTag != rustTag then
              IO.println s!"    VARIANT DIFFERS: Lean={leanTag} Rust={rustTag}"
            else
              IO.println s!"    variant: {leanTag}"
              -- Field-by-field comparison for common variants
              match leanCM, rustCM with
              | .defn ln ll lh la lc larena ltr lvr, .defn rn rl rh ra rc rarena rtr rvr => do
                if ln != rn then IO.println s!"    name DIFFERS: Lean={ln} Rust={rn}"
                if ll != rl then IO.println s!"    lvls DIFFERS: Lean={ll.size} Rust={rl.size}"
                if lh != rh then IO.println s!"    hints DIFFERS"
                if la != ra then IO.println s!"    all DIFFERS: Lean={la} Rust={ra}"
                if lc != rc then IO.println s!"    ctx DIFFERS: Lean={lc} Rust={rc}"
                if larena != rarena then IO.println s!"    arena DIFFERS: Lean={larena.nodes.size} Rust={rarena.nodes.size}"
                if ltr != rtr then IO.println s!"    typeRoot DIFFERS: Lean={ltr} Rust={rtr}"
                if lvr != rvr then IO.println s!"    valueRoot DIFFERS: Lean={lvr} Rust={rvr}"
              | .indc ln ll lctors la lc larena ltr, .indc rn rl rctors ra rc rarena rtr => do
                if ln != rn then IO.println s!"    name DIFFERS: Lean={ln} Rust={rn}"
                if ll != rl then IO.println s!"    lvls DIFFERS: Lean={ll.size} Rust={rl.size}"
                if lctors != rctors then IO.println s!"    ctors DIFFERS: Lean={lctors} Rust={rctors}"
                if la != ra then IO.println s!"    all DIFFERS: Lean={la} Rust={ra}"
                if lc != rc then IO.println s!"    ctx DIFFERS: Lean={lc} Rust={rc}"
                if larena != rarena then IO.println s!"    arena DIFFERS: Lean={larena.nodes.size} Rust={rarena.nodes.size}"
                if ltr != rtr then IO.println s!"    typeRoot DIFFERS: Lean={ltr} Rust={rtr}"
              | .ctor ln ll li larena ltr, .ctor rn rl ri rarena rtr => do
                if ln != rn then IO.println s!"    name DIFFERS: Lean={ln} Rust={rn}"
                if ll != rl then IO.println s!"    lvls DIFFERS: Lean={ll.size} Rust={rl.size}"
                if li != ri then IO.println s!"    induct DIFFERS: Lean={li} Rust={ri}"
                if larena != rarena then IO.println s!"    arena DIFFERS: Lean={larena.nodes.size} Rust={rarena.nodes.size}"
                if ltr != rtr then IO.println s!"    typeRoot DIFFERS: Lean={ltr} Rust={rtr}"
              | .recr ln ll lr la lc larena ltr lrr, .recr rn rl rr ra rc rarena rtr rrr => do
                if ln != rn then IO.println s!"    name DIFFERS: Lean={ln} Rust={rn}"
                if ll != rl then IO.println s!"    lvls DIFFERS: Lean={ll.size} Rust={rl.size}"
                if lr != rr then IO.println s!"    rules DIFFERS: Lean={lr} Rust={rr}"
                if la != ra then IO.println s!"    all DIFFERS: Lean={la} Rust={ra}"
                if lc != rc then IO.println s!"    ctx DIFFERS: Lean={lc} Rust={rc}"
                if larena != rarena then IO.println s!"    arena DIFFERS: Lean={larena.nodes.size} Rust={rarena.nodes.size}"
                if ltr != rtr then IO.println s!"    typeRoot DIFFERS: Lean={ltr} Rust={rtr}"
                if lrr != rrr then IO.println s!"    ruleRoots DIFFERS: Lean={lrr} Rust={rrr}"
              | _, _ => IO.println s!"    (other variant - use repr for details)"
        else
          IO.println s!"[Step 3]   All full ConstantMeta match! ✓"

        IO.println ""

        -- Step 4: Compare serialized environments
        IO.println s!"[Step 4] Comparing serialized environments..."
        let serStart ← IO.monoMsNow

        -- Count total ExprMeta entries and mdata sizes across all named constants
        let (leanTotalMetas, leanTotalMdata) := leanIxonEnv.named.fold (init := (0, 0)) fun (accMeta, accMdata) _ named =>
          let (metaCount, mdataSize) := named.constMeta.exprMetaStats
          (accMeta + metaCount, accMdata + mdataSize)
        let (rustTotalMetas, rustTotalMdata) := phases.compileEnv.named.fold (init := (0, 0)) fun (accMeta, accMdata) _ named =>
          let (metaCount, mdataSize) := named.constMeta.exprMetaStats
          (accMeta + metaCount, accMdata + mdataSize)

        -- Count ExprMeta by type: (binder, letBinder, ref, prj, mdata)
        let (leanBinder, leanLet, leanRef, leanPrj, leanMd) := leanIxonEnv.named.fold (init := (0, 0, 0, 0, 0)) fun (b, l, r, p, m) _ named =>
          let (b', l', r', p', m') := named.constMeta.exprMetaByType
          (b + b', l + l', r + r', p + p', m + m')
        let (rustBinder, rustLet, rustRef, rustPrj, rustMd) := phases.compileEnv.named.fold (init := (0, 0, 0, 0, 0)) fun (b, l, r, p, m) _ named =>
          let (b', l', r', p', m') := named.constMeta.exprMetaByType
          (b + b', l + l', r + r', p + p', m + m')

        IO.println s!"[Step 4]   Serializing Lean env ({leanIxonEnv.constCount} consts)..."
        IO.println s!"[Step 4]   Lean env has {leanIxonEnv.named.size} named, {leanIxonEnv.blobs.size} blobs, {leanIxonEnv.names.size} names"
        IO.println s!"[Step 4]   Lean total ExprMeta entries: {leanTotalMetas}, total mdata items: {leanTotalMdata}"
        IO.println s!"[Step 4]   Lean ExprMeta by type: binder={leanBinder}, letBinder={leanLet}, ref={leanRef}, prj={leanPrj}, mdata={leanMd}"

        -- Analyze blob sizes
        let leanBlobSizes := leanIxonEnv.blobs.toList.map (·.2.size)
        let leanTotalBlobData := leanBlobSizes.foldl (· + ·) 0
        let leanMaxBlob := leanBlobSizes.foldl max 0
        let leanAvgBlob := if leanBlobSizes.length > 0 then leanTotalBlobData / leanBlobSizes.length else 0
        let leanBig := leanBlobSizes.filter (· > 1000) |>.length
        let leanHuge := leanBlobSizes.filter (· > 100000) |>.length
        let leanTopSizes := leanBlobSizes.toArray.insertionSort (· > ·) |>.toList.take 10
        IO.println s!"[Step 4]   Lean blob stats: total={fmtBytes leanTotalBlobData}, max={fmtBytes leanMaxBlob}, avg={fmtBytes leanAvgBlob}, big(>1kB)={leanBig}, huge(>100kB)={leanHuge}"
        IO.println s!"[Step 4]   Lean top 10 blob sizes: {leanTopSizes.map fmtBytes}"

        let (leanBlobs, leanConsts, leanNames, leanNamed, leanComms) := Ixon.envSectionSizes leanIxonEnv
        IO.println s!"[Step 4]   Lean sections: blobs={fmtBytes leanBlobs}, consts={fmtBytes leanConsts}, names={fmtBytes leanNames}, named={fmtBytes leanNamed}, comms={fmtBytes leanComms}"
        let leanEnvBytes := serializeEnv leanIxonEnv
        IO.println s!"[Step 4]   Lean env done: {fmtBytes leanEnvBytes.size}"

        IO.println s!"[Step 4]   Serializing Rust env ({phases.compileEnv.constCount} consts)..."
        IO.println s!"[Step 4]   Rust env has {phases.compileEnv.named.size} named, {phases.compileEnv.blobs.size} blobs, {phases.compileEnv.names.size} names"
        IO.println s!"[Step 4]   Rust total ExprMeta entries: {rustTotalMetas}, total mdata items: {rustTotalMdata}"
        IO.println s!"[Step 4]   Rust ExprMeta by type: binder={rustBinder}, letBinder={rustLet}, ref={rustRef}, prj={rustPrj}, mdata={rustMd}"

        -- Analyze Rust blob sizes
        let rustBlobSizes := phases.compileEnv.blobs.toList.map (·.2.size)
        let rustTotalBlobData := rustBlobSizes.foldl (· + ·) 0
        let rustMaxBlob := rustBlobSizes.foldl max 0
        let rustAvgBlob := if rustBlobSizes.length > 0 then rustTotalBlobData / rustBlobSizes.length else 0
        let rustBig := rustBlobSizes.filter (· > 1000) |>.length
        let rustHuge := rustBlobSizes.filter (· > 100000) |>.length
        let rustTopSizes := rustBlobSizes.toArray.insertionSort (· > ·) |>.toList.take 10
        IO.println s!"[Step 4]   Rust blob stats: total={fmtBytes rustTotalBlobData}, max={fmtBytes rustMaxBlob}, avg={fmtBytes rustAvgBlob}, big(>1kB)={rustBig}, huge(>100kB)={rustHuge}"
        IO.println s!"[Step 4]   Rust top 10 blob sizes: {rustTopSizes.map fmtBytes}"

        let (rustBlobs, rustConsts, rustNames, rustNamed, rustComms) := Ixon.envSectionSizes phases.compileEnv
        IO.println s!"[Step 4]   Rust sections: blobs={fmtBytes rustBlobs}, consts={fmtBytes rustConsts}, names={fmtBytes rustNames}, named={fmtBytes rustNamed}, comms={fmtBytes rustComms}"
        let rustEnvBytes := serializeEnv phases.compileEnv
        IO.println s!"[Step 4]   Rust env done: {fmtBytes rustEnvBytes.size}"
        let serTime := (← IO.monoMsNow) - serStart

        IO.println s!"[Step 4]   Lean env: {fmtBytes leanEnvBytes.size}"
        IO.println s!"[Step 4]   Rust env: {fmtBytes rustEnvBytes.size}"
        IO.println s!"[Step 4]   Serialization time: {serTime}ms"

        if leanEnvBytes == rustEnvBytes then
          IO.println s!"[Step 4]   Serialized environments match exactly! ✓"
          IO.println ""

          return (true, 0, 0, none)
        else
          IO.println s!"[Step 4]   Serialized environments DIFFER"
          if let some diffPos := findFirstDiff leanEnvBytes rustEnvBytes then
            IO.println s!"[Step 4]   First difference at byte {diffPos}:"
            let leanByte := if diffPos < leanEnvBytes.size then s!"0x{String.ofList <| Nat.toDigits 16 (leanEnvBytes.get! diffPos).toNat}" else "EOF"
            let rustByte := if diffPos < rustEnvBytes.size then s!"0x{String.ofList <| Nat.toDigits 16 (rustEnvBytes.get! diffPos).toNat}" else "EOF"
            IO.println s!"[Step 4]     Lean: {leanByte}"
            IO.println s!"[Step 4]     Rust: {rustByte}"

          -- Find blobs in Rust but not in Lean
          let mut missingInLean : Array (Address × Nat) := #[]
          for (addr, bytes) in phases.compileEnv.blobs.toList do
            if !leanIxonEnv.blobs.contains addr then
              missingInLean := missingInLean.push (addr, bytes.size)
          if !missingInLean.isEmpty then
            IO.println s!"[Step 4]   Blobs in Rust but not Lean: {missingInLean.size}"
            for (addr, size) in missingInLean.toList.take 10 do
              -- Try to show content if small
              if let some bytes := phases.compileEnv.blobs.get? addr then
                if size < 100 then
                  let content := String.fromUTF8? bytes |>.getD s!"<binary {fmtBytes size}>"
                  IO.println s!"[Step 4]     {addr} ({fmtBytes size}): {content}"
                else
                  IO.println s!"[Step 4]     {addr} ({fmtBytes size})"

          -- Find blobs in Lean but not in Rust
          let mut missingInRust : Array (Address × Nat) := #[]
          for (addr, bytes) in leanIxonEnv.blobs.toList do
            if !phases.compileEnv.blobs.contains addr then
              missingInRust := missingInRust.push (addr, bytes.size)
          if !missingInRust.isEmpty then
            IO.println s!"[Step 4]   Blobs in Lean but not Rust: {missingInRust.size}"
            for (addr, size) in missingInRust.toList.take 10 do
              if let some bytes := leanIxonEnv.blobs.get? addr then
                if size < 100 then
                  let content := String.fromUTF8? bytes |>.getD s!"<binary {fmtBytes size}>"
                  IO.println s!"[Step 4]     {addr} ({fmtBytes size}): {content}"
                else
                  IO.println s!"[Step 4]     {addr} ({fmtBytes size})"

          IO.println ""
          -- Note: We expect this to fail until Lean generates metadata
          return (false, 0, 0, some s!"Serialized environments differ (Lean: {fmtBytes leanEnvBytes.size}, Rust: {fmtBytes rustEnvBytes.size})")
      else
        -- Report mismatches
        IO.println s!"[Step 3]   Found {result.mismatchedConstants.size} mismatches!"
        IO.println ""

        -- Show first mismatch in detail
        if let some first := result.mismatchedConstants[0]? then
          IO.println s!"[Mismatch] First discrepancy: {first.name}"
          IO.println s!"  Lean address: {first.leanAddr}"
          IO.println s!"  Rust address: {first.rustAddr}"
          IO.println ""

          IO.println s!"  Lean bytes ({fmtBytes first.leanBytes.size}):"
          IO.println s!"{hexDump first.leanBytes 128}"
          IO.println ""

          IO.println s!"  Rust bytes ({fmtBytes first.rustBytes.size}):"
          IO.println s!"{hexDump first.rustBytes 128}"
          IO.println ""

          if let some diffPos := findFirstDiff first.leanBytes first.rustBytes then
            IO.println s!"  First difference at byte {diffPos}:"
            let leanByte := if diffPos < first.leanBytes.size then s!"0x{String.ofList <| Nat.toDigits 16 (first.leanBytes.get! diffPos).toNat}" else "EOF"
            let rustByte := if diffPos < first.rustBytes.size then s!"0x{String.ofList <| Nat.toDigits 16 (first.rustBytes.get! diffPos).toNat}" else "EOF"
            IO.println s!"    Lean: {leanByte}"
            IO.println s!"    Rust: {rustByte}"
            IO.println ""

        if !result.missingInRust.isEmpty then
          IO.println s!"[Missing] {result.missingInRust.size} constants in Lean but not in Rust"
          for name in result.missingInRust.toList.take 5 do
            IO.println s!"  - {name}"
          if result.missingInRust.size > 5 then
            IO.println s!"  ... and {result.missingInRust.size - 5} more"
          IO.println ""

        if !result.missingInLean.isEmpty then
          IO.println s!"[Missing] {result.missingInLean.size} constants in Rust but not in Lean"
          for name in result.missingInLean.toList.take 5 do
            IO.println s!"  - {name}"
          if result.missingInLean.size > 5 then
            IO.println s!"  ... and {result.missingInLean.size - 5} more"
          IO.println ""

        return (false, 0, 0, some s!"Found {result.mismatchedConstants.size} mismatches")
  ) .done

/-! ## Test Suite -/

public def compileSuiteIO : List TestSeq := [
  testCrossImpl,
]

end Tests.Compile
