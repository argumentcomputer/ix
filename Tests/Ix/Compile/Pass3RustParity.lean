/-
  pass3-rust-parity: per-address parity of the Rust compiler's Pass 3 (M6R)
  against the Lean compiler's. Pass 3 is the only mode of both compilers
  since M6R slice 6.

  Per compile unit (the `pass3` suite's units: the aux-cert fixtures, the
  prototype's cases, the passes' fixtures, the twins), or for a whole file
  (`PARITY_FILE=<path>`, e.g. `Benchmarks/Compile/CompileInitStd.lean`):

  1. the Lean compiler (`compileLeanInput …`) and the Rust compiler through
     the FFI (`rsCompileEnvBytesFFI`) compile the same prepared constants;
  2. the two `Named` tables are joined by name and every name is classified:
     (a) identical (address, metadata, original, hints), (b) different,
     (c) on one side only;
  3. every name of (b) and (c) is a defect and fails the run. The constants
     each slice of M6R covers are reported with how many are identical
     (`slice-2 checked`: where the definitional passes O1-O6/O11a change the
     rewrite or record a decline; `slice-3 checked`: the clique table's
     members and carried lemmas and the hook's canonical constants under
     reserved names; `slice-4 checked`: the Lean names where a
     proof-justified pass fires or O11b applies, and their canonical
     constants). Until M6R slice 6 a difference could be owned by a later
     slice, by F1 or by their cascade, and the suite ran an `IX_PASS3=off`
     control with the legacy surgery on both sides; both are retired.
     (A failed block publishes nothing on either side since slice 2, so the
     names of a failed block are absent from both outputs.)
  4. the two compiles' failures (requested constants whose block failed) and
     their non-canonical sets (Lean `CompileEnv.p3NonCanonical`, Rust
     `CompileEnvStatus.nonCanonical`: the recorded declines with their
     causes) must be equal; a difference is a defect.
  5. **pack** (M6R slice 5, `Tests.Ix.Compile.PackParity`): on the Lean
     compile's artifact, the Rust unit view has the Lean view's tables (every
     name's unit, Pass 3's `_ix` names placed under their declaration); the
     Rust whole-unit bundle of one root per unit holding an `_ix` name is
     whole under the Lean view, and, for up to `PARITY_PACK_MAX` (default 10)
     of those roots per compile unit covering the reserved-name shapes,
     byte-identical to `ix pack`'s (`packWholeUnits`); a difference is a
     defect. `PARITY_PACK_ROOTS=<a>,<b>,…` adds roots, always compared (with
     `PARITY_FILE`: on Init+Std the whole-unit bundle of most roots, the
     clique hook's `_ix` units among them, gathers about 10,700 unit members,
     which the Lean completion packs one at a time from the 256 MB source, so
     the gate compares small roots there, with `PARITY_PACK_MAX=0`).

  Besides the `pass3` units, the `changed-set` suite's clique unit (the clique
  and ownership families together), the O11a decline inputs of `o11a-decline` (the
  withheld instance and the M1-h side conditions, hand-built closures) and the
  `validate-aux` corpus (`validateAuxClosure`, unit `corpus`: the `Mutual`,
  `Canonicity`, `LevelSpellings` and IxVM fixtures; added at M6R slice 6, whose
  flip of Rust's default exposed a Rust-only failure there, F1) are
  compared, so every recorded decline cause is exercised on both sides.

  Run: `lake test -- --ignored pass3-rust-parity`
  (`PARITY_ONLY=<stems>` restricts the units; `PARITY_FILE=<path>` runs one
  file's whole environment instead; `PARITY_SHOW=<n>` lists up to n names per
  class).
-/
import Ix.CompileM
import Ix.CompileDriver
import Ix.Compile.Pass
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.O11aDecline
import Tests.Ix.Compile.CliqueOwnership
import Tests.Ix.Compile.PackParity
import Tests.Ix.Compile.ValidateAux

open Lean

namespace Tests.Ix.Compile.Pass3RustParity

open Tests.Ix.Compile.Pass3 (CUnit unitOfFile ixN toLeanName auxCertFiles protoFiles passFiles
  pjPassFiles closureOf leanRejects)

abbrev IxName := _root_.Ix.Name

def sameNamed (a b : Ixon.Named) : Bool :=
  a.addr == b.addr && a.constMeta == b.constMeta && a.hints == b.hints &&
    (match a.original, b.original with
     | none, none => true
     | some (x, m), some (y, n) => x == y && m == n
     | _, _ => false)

/-- What differs between two entries of one name. -/
def diffNamed (a b : Ixon.Named) : String :=
  let parts : List String :=
    (if a.addr != b.addr then ["addr"] else []) ++
    (if a.constMeta != b.constMeta then ["meta"] else []) ++
    (if a.hints != b.hints then ["hints"] else []) ++
    (if (a.original.map (·.1)) != (b.original.map (·.1)) then ["original"] else
      if (a.original.map (·.2)) != (b.original.map (·.2)) then ["original-meta"] else [])
  ", ".intercalate parts

/-- The prefix before the first reserved component. -/
def beforeReserved (n : IxName) : Option IxName :=
  let cs := Ix.Compile.Pass.comps n
  match cs.findIdx? (fun c => match c with
      | .s x => Ix.Compile.Pass.isReservedComponent x
      | .n _ => false) with
  | some i => some (Ix.Compile.Pass.ofComps (cs.take i))
  | none => none

/-- The constants each slice of M6R covers in a Lean compile, from its own
records and its own rewrite functions (reported, as counts of identical
constants: every slice is implemented, so no difference is attributed to one). -/
structure Roots where
  slice2 : Std.HashSet IxName := {}
  slice3 : Std.HashSet IxName := {}
  slice4 : Std.HashSet IxName := {}

def computeRoots (cenv : Ix.CompileM.CompileEnv) (closure : List (Name × ConstantInfo)) :
    IO Roots := do
  let mut r : Roots := {}
  -- slice 3: the clique table (members and carried lemmas)
  for (n, (members, lemmas)) in cenv.p3Cliques do
    r := { r with slice3 := (members ++ lemmas).foldl (·.insert ·) (r.slice3.insert n) }
  -- slice 2: recorded declines
  for (n, _) in cenv.p3NonCanonical do
    r := { r with slice2 := r.slice2.insert n }
  -- slices 2 and 4: where the passes change a constant's rewrite
  let views0 : Std.HashMap IxName Ix.Compile.Pass.BlockView := {}
  let mut views := views0
  for (key, _) in cenv.p3Blocks do
    match Ix.Compile.Pass.viewOf cenv views key with
    | .ok v => views := views.insert key v
    | .error e => IO.eprintln s!"[parity] view of {key.pretty}: {e}"
  let blocks := Ix.Compile.Pass.optBlocks cenv views
  let lookup := Ix.Compile.Pass.expansionLookup cenv views
  for (n, _) in closure do
    let x := ixN n
    let some ci := cenv.env.get? x | continue
    if (Ix.Compile.Pass.headsIn cenv.p3Heads ci).isEmpty then continue
    if cenv.p3Heads.contains x then continue
    let base := Ix.Compile.Pass.rewriteBlock lookup #[(x, ci)]
    let withOpt := Ix.Compile.Pass.rewriteBlock lookup #[(x, ci)]
      (Ix.Compile.Pass.optLookup cenv blocks) (Ix.Compile.Pass.declineLookup cenv blocks)
    match base, withOpt with
    | .ok b, .ok o =>
      if !o.canon.isEmpty then
        r := { r with slice4 := r.slice4.insert x }
      -- O11b (a unit pass, slice 4): the canonical `noConfusion` pair `_ix`
      if !(Ix.Compile.Pass.unitPasses cenv views #[(x, ci)]).isEmpty then
        r := { r with slice4 := r.slice4.insert x }
      let bv := b.overlay.map (·.2)
      let ov := o.overlay.map (·.2)
      if bv != ov then r := { r with slice2 := r.slice2.insert x }
    | .error e, _ | _, .error e => IO.eprintln s!"[parity] rewrite of {x.pretty}: {e}"
  return r

structure Report where
  identical : Nat := 0
  different : Array (IxName × String) := #[]
  leanOnly : Array IxName := #[]
  rustOnly : Array IxName := #[]

/-- Join the two `Named` tables by name. Every name of (b) and (c) is a defect:
every slice of M6R is implemented (until slice 6 a difference could be owned
by a later slice, F1 or their cascade; that attribution is retired). -/
def compare (lean rust : Ixon.Env) : Report := Id.run do
  let mut rep : Report := {}
  for (n, a) in lean.named do
    if Tests.Ix.Compile.Pass3.isSyntheticMuts n then continue
    match rust.named.get? n with
    | some b =>
      if sameNamed a b then rep := { rep with identical := rep.identical + 1 }
      else rep := { rep with different := rep.different.push (n, diffNamed a b) }
    | none => rep := { rep with leanOnly := rep.leanOnly.push n }
  for (n, _) in rust.named do
    if Tests.Ix.Compile.Pass3.isSyntheticMuts n then continue
    if !lean.named.contains n then rep := { rep with rustOnly := rep.rustOnly.push n }
  return rep

/-- The synthetic `Muts` entries compared separately (their keys contain the
block address, so a moved block is a key on each side only). -/
def mutsCounts (lean rust : Ixon.Env) : Nat × Nat × Nat := Id.run do
  let mut same := 0
  let mut leanOnly := 0
  let mut rustOnly := 0
  for (n, a) in lean.named do
    if !Tests.Ix.Compile.Pass3.isSyntheticMuts n then continue
    match rust.named.get? n with
    | some b => if sameNamed a b then same := same + 1 else leanOnly := leanOnly + 1
    | none => leanOnly := leanOnly + 1
  for (n, _) in rust.named do
    if Tests.Ix.Compile.Pass3.isSyntheticMuts n && !lean.named.contains n then
      rustOnly := rustOnly + 1
  return (same, leanOnly, rustOnly)

def showN : IO Nat := do
  return ((← IO.getEnv "PARITY_SHOW").bind String.toNat?).getD 20

/-- The inputs of `o11a-decline` (`Tests.Ix.Compile.O11aDecline`): the
selected closure of `PassO2.SA._sizeOf_1` with and without the instance
`PassO2.SB._sizeOf_inst`, and one closure per side condition of M1-h. -/
def o11aUnits : IO (Array (String × Environment × List (Name × ConstantInfo))) := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/O2Split.lean"
  let full := Ix.EnvScope.collectSelectedDeps env [Tests.Ix.Compile.O11aDecline.root]
  let withheld := Tests.Ix.Compile.O11aDecline.dropWithDependents full [Tests.Ix.Compile.O11aDecline.inst]
  let mut out := #[("neighbour", env, full), ("withheld", env, withheld)]
  let senv ← getFileEnv "Tests/Ix/Compile/Pass/O11aSide.lean"
  for c in Tests.Ix.Compile.O11aDecline.sideCases do
    let seeds := c.root :: c.extra ++ c.sizeFn?.toList
    let mut cs := Ix.EnvScope.collectSelectedDeps senv seeds
    if let some k' := c.sizeFn? then
      cs ← IO.ofExcept (Tests.Ix.Compile.O11aDecline.replaceSizeFn cs c.inst k')
    out := out.push (c.label.replace " " "-", senv, cs)
  return out

/-- Compile one unit with both compilers and report; returns the defects. -/
def runOne (name : String) (env : Environment) (closure : List (Name × ConstantInfo)) :
    IO (Array String) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  let t0 ← IO.monoMsNow
  let out ← match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) with
    | .ok o => pure o
    | .error e => throw (IO.userError s!"{name}: Lean compile failed: {e}")
  let t1 ← IO.monoMsNow
  let dir ← IO.FS.createTempDir
  let path := dir / "rust.ixe"
  let constants ← IO.ofExcept input.prepare
  let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
  let t2 ← IO.monoMsNow
  let rustBytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  -- `PARITY_KEEP=<dir>`: keep both outputs (`lean.ixe`, `rust.ixe`) for an
  -- external digest; the caller deletes them
  if let some keep := ← IO.getEnv "PARITY_KEEP" then
    IO.FS.createDirAll keep
    IO.FS.writeBinFile (System.FilePath.mk keep / "lean.ixe") out.bytes
    IO.FS.writeBinFile (System.FilePath.mk keep / "rust.ixe") rustBytes
  let rust ← IO.ofExcept (Ixon.deEnv rustBytes)
  let lean ← IO.ofExcept (Ixon.deEnv out.bytes)
  let roots ← computeRoots out.cenv closure
  let rep := compare lean rust
  let (mSame, mLean, mRust) := mutsCounts lean rust
  let k ← showN
  let leanFails := out.cenv.ungrounded.size
  IO.println s!"[parity] {name}: lean {out.bytes.size} B ({t1 - t0} ms, {leanFails} failures), \
rust {rustBytes.size} B ({t2 - t1} ms, {status.ungrounded.size} failures); \
{if rustBytes == out.bytes then "BYTE-IDENTICAL" else "files differ"}"
  IO.println s!"[parity] {name}: (a) identical {rep.identical}, (b) different {rep.different.size}, \
(c) lean-only {rep.leanOnly.size}, rust-only {rep.rustOnly.size}; Muts entries same {mSame}, \
lean-only/different {mLean}, rust-only {mRust}"
  for (n, e) in (status.ungrounded.toList.take k) do
    IO.println s!"[parity] {name}:   rust failure {n}: {e.take 300}"
  -- slice 2 is checked, not attributed: the constants whose Lean rewrite the
  -- definitional passes change (or that carry a recorded decline), and how
  -- many of them are identical
  let s2 := roots.slice2.toArray
  let s2same := s2.filter fun n => match lean.named.get? n, rust.named.get? n with
    | some a, some b => sameNamed a b
    | _, _ => false
  IO.println s!"[parity] {name}: slice-2 checked: {s2.size} constant(s) the definitional passes \
change, {s2same.size} identical"
  let same (n : IxName) : Bool := match lean.named.get? n, rust.named.get? n with
    | some a, some b => sameNamed a b
    | _, _ => false
  let s3members := roots.slice3.toArray.filter (lean.named.contains ·)
  let s3canon := lean.named.toArray.filterMap fun (n, _) =>
    match beforeReserved n with
    | some b => if roots.slice3.contains b && !roots.slice3.contains n then some n else none
    | none => none
  IO.println s!"[parity] {name}: slice-3 checked: {s3members.size} member(s) and carried lemma(s), \
{(s3members.filter same).size} identical; {s3canon.size} canonical constant(s) under reserved \
names, {(s3canon.filter same).size} identical"
  -- slice 4: the Lean names where a proof-justified pass fires or O11b
  -- applies (they keep their baseline) and their canonical constants under
  -- reserved names (`c._ix`, `p._ix_retyped.s`, `fg`, O11b's pair)
  let s4names := roots.slice4.toArray.filter (lean.named.contains ·)
  let s4canon := lean.named.toArray.filterMap fun (n, _) =>
    match beforeReserved n with
    | some b => if roots.slice4.contains b && !roots.slice4.contains n then some n else none
    | none => none
  IO.println s!"[parity] {name}: slice-4 checked: {s4names.size} Lean name(s) with a \
proof-justified rewrite or O11b, {(s4names.filter same).size} identical; {s4canon.size} \
canonical constant(s) under reserved names, {(s4canon.filter same).size} identical"
  -- the failures and the non-canonical sets, compared by name (and cause)
  let leanFailed : Array String := (out.cenv.ungrounded.toArray.map (·.1.pretty)).qsort (· < ·)
  let rustFailed : Array String := status.ungrounded.map (·.1)
  let leanNC : Array (String × String) :=
    (out.cenv.p3NonCanonical.toArray.map fun (n, c) => (n.pretty, c)).qsort (fun a b => a.1 < b.1)
  let rustNC := status.nonCanonical
  IO.println s!"[parity] {name}: failures lean {leanFailed.size} / rust {rustFailed.size} \
{if leanFailed == rustFailed then "(same names)" else "(DIFFERENT)"}; non-canonical lean \
{leanNC.size} / rust {rustNC.size} {if leanNC == rustNC then "(same entries)" else "(DIFFERENT)"}"
  let mut extra : Array String := #[]
  if leanFailed != rustFailed then
    for n in leanFailed do
      if !rustFailed.contains n then
        let why := (out.cenv.ungrounded.toList.find? (·.1.pretty == n)).map fun p => (p.2.take 300).toString
        extra := extra.push s!"{name}: failure on the Lean side only: {n}: {why.getD ""}"
    for n in rustFailed do
      if !leanFailed.contains n then extra := extra.push s!"{name}: failure on the Rust side only: {n}"
  if leanNC != rustNC then
    for e in leanNC do
      if !rustNC.contains e then extra := extra.push s!"{name}: non-canonical entry on the Lean side only: {e.1}: {e.2}"
    for e in rustNC do
      if !leanNC.contains e then extra := extra.push s!"{name}: non-canonical entry on the Rust side only: {e.1}: {e.2}"
  -- 5. the whole-unit pack of the Lean artifact, Rust against Lean
  let packMax := (← IO.getEnv "PARITY_PACK_MAX").bind String.toNat?
  let packRoots : Array Name := ((((← IO.getEnv "PARITY_PACK_ROOTS").map (·.splitOn ",")).getD []).filter
    (!·.isEmpty)).toArray.map String.toName
  let packDir ← IO.FS.createTempDir
  let packPath := packDir / "lean.ixe"
  IO.FS.writeBinFile packPath out.bytes
  extra := extra ++ (← Tests.Ix.Compile.PackParity.run s!"{name}" packPath.toString
    (extra := packRoots) (maxLean := packMax.getD 10))
  IO.FS.removeDirAll packDir
  for (n, c) in leanNC.toList.take k do
    IO.println s!"[parity] {name}:   non-canonical {n}: {c}"
  let defects : Array (IxName × String) := rep.different.map (fun (n, d) => (n, s!"differs: {d}")) ++
    rep.leanOnly.map (·, "lean only") ++ rep.rustOnly.map (·, "rust only")
  for (n, why) in defects.toList.take (k * 5) do
    IO.println s!"[parity] {name}:   DEFECT {n.pretty} ({why})"
  return defects.map (fun (n, _) => s!"{name}: {n.pretty}") ++ extra

def run (env : Environment) : IO UInt32 := do
  -- both compilers in Pass 3, their only mode (M6R slice 6 deleted the legacy
  -- surgery and with it this suite's `IX_PASS3=off` control); a leftover
  -- `IX_PASS3=off` is refused
  match ← Ix.Compile.Pass.switchFromEnv with
    | .ok () => pure ()
    | .error msg =>
      IO.println s!"[parity] {msg}"
      return 2
  IO.println "[parity] mode: Pass 3 (both compilers)"
  let k ← showN
  let mut defects : Array String := #[]
  let mut failures : Array String := #[]
  if let some p := ← IO.getEnv "PARITY_FILE" then
    let fe ← getFileEnv p
    let closure := fe.constants.toList
    defects := defects ++ (← runOne p fe closure)
  else
    let only := ((← IO.getEnv "PARITY_ONLY").map (·.splitOn ",")).getD []
    let want := fun (s : String) => only.isEmpty || only.contains s
    for p in auxCertFiles ++ protoFiles ++ passFiles ++ pjPassFiles do
      let stem := (System.FilePath.mk p).fileStem.getD p
      if !want stem || leanRejects.contains stem || stem == "ReservedIx" then continue
      try
        let u ← unitOfFile p
        defects := defects ++ (← runOne stem u.env u.closure)
      catch e =>
        IO.println s!"[parity] FAIL {stem}: {e}"
        failures := failures.push s!"{stem}: {e}"
    if want "twins" then
      try
        let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
        defects := defects ++ (← runOne "twins" env (closureOf env seeds.toList))
      catch e =>
        IO.println s!"[parity] FAIL twins: {e}"
        failures := failures.push s!"twins: {e}"
    -- the `changed-set` suite's clique unit (M6R slice 5): the closure of the clique and
    -- ownership families together
    if want "cliques" then
      try
        let families := Tests.Ix.Compile.Twins.cliqueFamilies ++ Tests.Ix.Compile.Twins.ownershipFamilies
        let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env families
        let extra := [``Lean.Order.monotone_compose].filter env.contains
        defects := defects ++ (← runOne "cliques" env (closureOf env (seeds.toList ++ extra)))
      catch e =>
        IO.println s!"[parity] FAIL cliques: {e}"
        failures := failures.push s!"cliques: {e}"
    -- the clique-ownership cases (`clique-ownership`): each case's clique as
    -- a compile unit (its members' closure; WF8 with its caller and a
    -- neighbour, the caller refused by name on both sides)
    if want "clique-ownership" then
      let eqn := Tests.Ix.Compile.Transport.eqnCliques env
      let mut seen : Std.HashSet String := {}
      for c in Tests.Ix.Compile.CliqueOwnership.cases do
        if c.alter.isSome || seen.contains c.name then continue
        seen := seen.insert c.name
        let ns := Tests.Ix.Compile.CliqueOwnership.srcNs ++ c.name.toName
        let some (_, ms) := eqn.get? (ns ++ `first) | do
          IO.println s!"[parity] FAIL co-{c.name}: no clique recorded"
          failures := failures.push s!"co-{c.name}: no clique recorded"
          continue
        let extra := if c.name.startsWith "WF8" then #[ns ++ `caller, ns ++ `neighbour] else #[]
        try
          defects := defects ++ (← runOne s!"co-{c.name}" env (closureOf env (ms ++ extra).toList))
        catch e =>
          IO.println s!"[parity] FAIL co-{c.name}: {e}"
          failures := failures.push s!"co-{c.name}: {e}"
    -- the `validate-aux` corpus (`validateAuxClosure`: the `Mutual`, `Canonicity`,
    -- `LevelSpellings` and IxVM fixtures), whose `AuxOwnership` families exposed F1 at
    -- M6R slice 6 (Rust lacked Lean's Pass 3 exemption of the aux-ownership check; no
    -- unit here compiled them before)
    if want "corpus" then
      try
        defects := defects ++ (← runOne "corpus" env (validateAuxClosure env))
      catch e =>
        IO.println s!"[parity] FAIL corpus: {e}"
        failures := failures.push s!"corpus: {e}"
    -- the O11a decline inputs (`o11a-decline`): the neighbour and the
    -- withheld instance of `O2Split`, and the M1-h side conditions
    if want "o11a" then
      try
        let units ← o11aUnits
        for (label, uenv, cs) in units do
          defects := defects ++ (← runOne s!"o11a-{label}" uenv cs)
      catch e =>
        IO.println s!"[parity] FAIL o11a: {e}"
        failures := failures.push s!"o11a: {e}"
  IO.println s!"[parity] {defects.size} defect(s), {failures.size} unit failure(s)"
  for d in defects.toList.take (k * 5) do IO.println s!"[parity] DEFECT {d}"
  return if defects.isEmpty && failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3RustParity
