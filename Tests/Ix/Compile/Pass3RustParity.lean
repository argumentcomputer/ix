/-
  pass3-rust-parity: per-address parity of the Rust compiler's Pass 3 (M6R)
  against the Lean compiler's, with the switch on (`IX_PASS3=images`).

  Per compile unit (the `pass3` suite's units: the aux-cert fixtures, the
  prototype's cases, the passes' fixtures, the twins), or for a whole file
  (`PARITY_FILE=<path>`, e.g. `Benchmarks/Compile/CompileInitStd.lean`):

  1. the Lean compiler with Pass 3 (`compileLeanInput … (pass3? := some true)`)
     and the Rust compiler through the FFI (`rsCompileEnvBytesFFI`, which reads
     `IX_PASS3`; the run requires `IX_PASS3=images`) compile the same prepared
     constants;
  2. the two `Named` tables are joined by name and every name is classified:
     (a) identical (address, metadata, original, hints), (b) different,
     (c) on one side only;
  3. every name of (b) and (c) must be owned by a later slice of M6R, read off
     the Lean compile itself (slices 1 and 2 are implemented: the definitional
     passes O1-O6 and O11a are checked for identity, not attributed; a
     constant where only they change the rewrite is reported as such,
     `slice-2 checked`, for the record):
     * **slice 3** (clique transport): a member or carried lemma of the
       clique table (`CompileEnv.p3Cliques`), and the reserved names under a
       clique member (the hook's canonical constants);
     * **slice 4** (O7-O12, O11b): a constant where a proof-justified pass
       fires (`BlockRewrite.canon` non-empty: `PJ-FORM`) or the unit pass O11b
       applies (`unitPasses`), and its canonical form `c._ix`;
     * **F1** (lands with the flip `4c18e1b1`, not on this base): the image of
       a Lean theorem, which Rust stores as a theorem;
     * **cascade**: a name in the reverse-dependency cone of the names above
       whose metadata, hints and original metadata are equal on both sides
       (only referenced addresses moved)
       (through the Lean input's references; a reserved display name follows
       its Lean prefix).
     Anything else is a defect and fails the run (a failed block publishes
     nothing on either side since slice 2, so the names of a failed block are
     absent from both outputs).
  4. the two compiles' failures (requested constants whose block failed) and
     their non-canonical sets (Lean `CompileEnv.p3NonCanonical`, Rust
     `CompileEnvStatus.nonCanonical`: the recorded declines with their
     causes) must be equal; a difference is a defect.

  Besides the `pass3` units, the O11a decline inputs of `o11a-decline` (the
  withheld instance and the M1-h side conditions, hand-built closures) are
  compared, so every recorded decline cause is exercised on both sides.

  Run: `IX_PASS3=images lake test -- --ignored pass3-rust-parity` (`IX_PASS3=off` runs
  the same comparison with the legacy surgery on both sides, as a control)
  (`PARITY_ONLY=<stems>` restricts the units; `PARITY_FILE=<path>` runs one
  file's whole environment instead; `PARITY_SHOW=<n>` lists up to n names per
  class).
-/
import Ix.CompileM
import Ix.CompileDriver
import Ix.Compile.Pass
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.O11aDecline

open Lean

namespace Tests.Ix.Compile.Pass3RustParity

open Tests.Ix.Compile.Pass3 (CUnit unitOfFile ixN toLeanName auxCertFiles protoFiles passFiles
  pjPassFiles closureOf leanRejects)

abbrev IxName := _root_.Ix.Name

/-- The class of a differing name. -/
inductive Owner where
  | slice3 | slice4 | f1 | cascade | defect
  deriving BEq, Repr, Inhabited

def Owner.label : Owner → String
  | .slice3 => "slice 3 (clique transport)"
  | .slice4 => "slice 4 (O7-O12 PJ-FORM)"
  | .f1 => "F1 (flip 4c18e1b1)"
  | .cascade => "cascade of the above"
  | .defect => "DEFECT"

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

/-- The later-slice roots of a Lean switch-on compile, from its own records
and its own rewrite functions. -/
structure Roots where
  slice2 : Std.HashSet IxName := {}
  slice3 : Std.HashSet IxName := {}
  slice4 : Std.HashSet IxName := {}
  f1 : Std.HashSet IxName := {}

def computeRoots (cenv : Ix.CompileM.CompileEnv) (closure : List (Name × ConstantInfo)) :
    IO Roots := do
  let mut r : Roots := {}
  -- slice 3: the clique table (members and carried lemmas)
  for (n, (members, lemmas)) in cenv.p3Cliques do
    r := { r with slice3 := (members ++ lemmas).foldl (·.insert ·) (r.slice3.insert n) }
  -- slice 2: recorded declines
  for (n, _) in cenv.p3NonCanonical do
    r := { r with slice2 := r.slice2.insert n }
  -- F1: images of Lean theorems
  for (h, _) in cenv.p3Heads do
    if let some (.thmInfo _) := cenv.env.get? h then r := { r with f1 := r.f1.insert h }
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

/-- The reverse-dependency cone of `roots` over the Lean input. -/
def cone (closure : List (Name × ConstantInfo)) (roots : Std.HashSet IxName) :
    Std.HashSet IxName := Id.run do
  let mut rev : Std.HashMap IxName (Array IxName) := {}
  for (n, ci) in closure do
    let x := ixN n
    for r in ci.getUsedConstantsAsSet do
      rev := rev.insert (ixN r) ((rev.getD (ixN r) #[]).push x)
    match ci with
    | .ctorInfo cv => rev := rev.insert (ixN cv.induct) ((rev.getD (ixN cv.induct) #[]).push x)
    | .inductInfo iv =>
      for c in iv.ctors do rev := rev.insert x ((rev.getD x #[]).push (ixN c))
    | _ => pure ()
  let mut out : Std.HashSet IxName := {}
  let mut todo : Array IxName := roots.toArray
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if out.contains n then continue
    out := out.insert n
    for d in rev.getD n #[] do
      if !out.contains d then todo := todo.push d
  return out

structure Report where
  identical : Nat := 0
  different : Array (IxName × String) := #[]
  leanOnly : Array IxName := #[]
  rustOnly : Array IxName := #[]
  owners : Array (IxName × Owner) := #[]

def classify (roots : Roots) (coneSet : Std.HashSet IxName) (metaEqual : IxName → Bool)
    (n : IxName) : Owner :=
  let base := (beforeReserved n).getD n
  if roots.slice4.contains base || roots.slice4.contains n then .slice4
  else if roots.slice3.contains base || roots.slice3.contains n then .slice3
  else if roots.f1.contains n then .f1
  else if coneSet.contains base || coneSet.contains n then
    -- a cascade changes referenced addresses only: the metadata (names,
    -- binders, arena shape), the hints and the original stay equal
    if metaEqual n then .cascade else .defect
  else .defect

def compare (lean rust : Ixon.Env) (roots : Roots) (closure : List (Name × ConstantInfo)) :
    Report := Id.run do
  -- the definitional passes (slice 2) are implemented: their constants are
  -- not roots, they must be identical
  let all : Std.HashSet IxName :=
    roots.slice3.union roots.slice4 |>.union roots.f1
  let coneSet := cone closure all
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
  let names := rep.different.map (·.1) ++ rep.leanOnly ++ rep.rustOnly
  let metaEqual := fun n => match lean.named.get? n, rust.named.get? n with
    | some a, some b => a.constMeta == b.constMeta && a.hints == b.hints &&
        (a.original.map (·.2)) == (b.original.map (·.2))
    | _, _ => false
  rep := { rep with owners := names.map fun n => (n, classify roots coneSet metaEqual n) }
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

/-- Compile one unit both ways and report; returns the defects. -/
def runOne (name : String) (env : Environment) (closure : List (Name × ConstantInfo)) :
    IO (Array String) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  let t0 ← IO.monoMsNow
  let out ← match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) (pass3? := some ((← IO.getEnv "IX_PASS3") == some "images")) with
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
  let rep := compare lean rust roots closure
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
  for (n, c) in leanNC.toList.take k do
    IO.println s!"[parity] {name}:   non-canonical {n}: {c}"
  for o in [Owner.slice3, .slice4, .f1, .cascade, .defect] do
    let ns := rep.owners.filter (·.2 == o)
    if ns.isEmpty then continue
    IO.println s!"[parity] {name}:   {o.label}: {ns.size}"
    for (n, _) in ns.toList.take (if o == .defect then k * 5 else k) do
      let why := match rep.different.find? (·.1 == n) with
        | some (_, d) => s!"differs: {d}"
        | none => if rep.leanOnly.contains n then "lean only" else "rust only"
      IO.println s!"[parity] {name}:     {n.pretty} ({why})"
  let defects := rep.owners.filter (·.2 == .defect)
  return defects.map (fun (n, _) => s!"{name}: {n.pretty}") ++ extra

def run (env : Environment) : IO UInt32 := do
  -- the mode of both compiles: `IX_PASS3=images` (the gate) or `IX_PASS3=off`
  -- (the control: the legacy surgery on both sides, which must show no
  -- difference but those of the default path)
  let mode ← IO.getEnv "IX_PASS3"
  if mode != some "images" && mode != some "off" then
    IO.println "[parity] requires IX_PASS3=images (or IX_PASS3=off for the control)"
    return 2
  IO.println s!"[parity] mode IX_PASS3={mode.getD ""}"
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
