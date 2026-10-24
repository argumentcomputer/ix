/-
  pass3-tools: one evidence or diagnostic tool of the `pass3` suite, selected
  by exactly one of its variables (`Pass3Kernels.toolModes`). These print,
  record or re-check evidence; they approve nothing, and `pass3` refuses to
  run while one of their variables is set (lane G `6dcb793e`).

  - `PASS3_RECHECK=<dir>` (a `PASS3_KEEP` directory, possibly written by an
    older revision): rerun this revision's kernels on every unit's kept
    `out.ixe` with its kept `names.txt`, in meta mode and, with
    `PASS3_RECHECK_ANON`, in anonymous mode (check-rs subject-only), dumping
    the rows (`PASS3_FAILURES`) with run `meta` or `anon`;
    `PASS3_RECHECK_TAG` keeps concurrent rechecks' directories apart.
  - `PASS3_EXPECT_EMIT=<rows.tsv>,<recheck.tsv>[,<meta recheck.tsv>…]`:
    candidate rows of `Pass3Kernels.table` from a suite dump, its anonymous
    recheck and further meta rechecks (`Harness.emit`); to be reviewed.
  - `PASS3_CLOSURE=<file.lean>,<constant>`: compile the closure of one
    constant of a file, timing it.
  - `PASS3_VIEW=<file.lean>`: per changed block of the file's compile, Pass
    1's and the compiler's classes, the view's canonical recursors and the
    images.
  - `PASS3_FIND=<file.ixe>,<hex prefix>,…`: the named entries and constants
    whose address starts with a prefix.

  Not ported: `PASS3_SURGERED` (the surgery's rewritten constants, through
  `Ix.Tc`) and the library comparison `PASS3_LIB` (`pass3-lib`), which
  compared a switch-off output that no longer exists.

  Run with: `PASS3_<MODE>=… lake test -- pass3-tools` (tier `manual`).
-/
import Tests.Ix.Compile.Harness.Kernels
import Tests.Ix.Compile.Pass3Kernels
import Tests.Ix.Compile.Image

open Lean

namespace Tests.Ix.Compile.Pass3Tools

open Tests.Ix.Compile.Harness

/-- `PASS3_RECHECK=<dir>`: the kernels again on every kept output. -/
def runRecheck (d : System.FilePath) : IO UInt32 := do
  let anonToo := (← IO.getEnv "PASS3_RECHECK_ANON").isSome
  let tag := (← IO.getEnv "PASS3_RECHECK_TAG").getD ""
  let mut n := 0
  for e in ← d.readDir do
    let p := e.path
    unless ← p.isDir do continue
    let ixe := p / "out.ixe"
    let nf := p / "names.txt"
    unless (← ixe.pathExists) && (← nf.pathExists) do continue
    let names := ((← IO.FS.readFile nf).splitOn "\n").toArray.filter (!·.isEmpty)
    if names.isEmpty then continue
    let bytes ← IO.FS.readBinFile ixe
    for anon in (if anonToo then [false, true] else [false]) do
      let mode := if anon then "anon" else "meta"
      let rdir := p / s!"recheck{tag}-{mode}"
      IO.FS.createDirAll rdir
      let r ← kernelRun rdir bytes names (anon := anon) (skipDeps := true)
      dumpRuns e.fileName [(mode, r)]
      IO.println s!"[pass3-tools] recheck {e.fileName} {mode}: {r.failed.size} failure(s), \
checked {r.checked}"
      n := n + 1
  IO.println s!"[pass3-tools] recheck: {n} run(s)"
  return 0

/-- `PASS3_FIND=<file.ixe>,<prefix>,…`. -/
def runFind (path : String) (pfxs : List String) : IO UInt32 := do
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  for (n, nd) in env.named do
    let a := toString nd.addr
    if pfxs.any (a.startsWith ·) then
      IO.println s!"[pass3-tools] named {a} {n.pretty} meta={nd.constMeta.info.kindName}"
  for (a, _) in env.consts do
    if pfxs.any ((toString a).startsWith ·) then IO.println s!"[pass3-tools] const {a}"
  return 0

/-- `PASS3_VIEW=<file.lean>`. -/
def runView (path : String) : IO UInt32 := do
  let u ← unitOfFile path
  let out ← compileUnit u
  let inp := _root_.Ix.Compile.Pass.viewInput out.cenv
  for (_, all) in out.cenv.p3Blocks do
    IO.println s!"[pass3-tools] block {all.map (·.pretty)}"
    match _root_.Ix.Compile.Pass.buildView inp all with
    | .error e => IO.println s!"[pass3-tools]   view error: {e}"
    | .ok v =>
      IO.println s!"[pass3-tools]   Pass 1 classes \
{v.canon.components.map (·.classes.map (·.map (·.pretty)))}"
      for m in all do
        IO.println s!"[pass3-tools]   compiler classes of {m.pretty}: \
{(out.cenv.blocks.get? m).map (·.map (·.map (·.pretty)))}"
      for (n, c) in v.canonConsts do
        let n : _root_.Ix.Name := n
        if let .recInfo rv := c then
          IO.println s!"[pass3-tools]   view rec {n.pretty} : \
{Tests.Ix.Compile.Image.toLeanExpr rv.cnst.type}"
      for (n, b) in v.back do IO.println s!"[pass3-tools]   back {n.pretty} ↦ {b.pretty}"
      for r in _root_.Ix.Compile.Pass.imageKinds inp.const? all do
        if let some (.recInfo _) := inp.const? r then
          match v.image inp r with
          | .ok img => IO.println s!"[pass3-tools]   image {r.pretty} := \
{Tests.Ix.Compile.Image.toLeanExpr img.value}"
          | .error e => IO.println s!"[pass3-tools]   image {r.pretty}: {e}"
  return 0

/-- `PASS3_CLOSURE=<file.lean>,<constant>`. -/
def runClosure (path : String) (c : String) : IO UInt32 := do
  let env ← getFileEnv path
  let n := parseName c
  let closure := closureOf env [n]
  IO.println s!"[pass3-tools] closure of {c}: {closure.length} constants"
  let t0 ← IO.monoMsNow
  let out ← compileUnit { name := c, env, seeds := #[n], closure }
  IO.println s!"[pass3-tools] {out.bytes.size} bytes, {out.cenv.ungrounded.size} failures, \
{(← IO.monoMsNow) - t0} ms"
  return 0

/-- The runner: the one tool whose variable is set. Fails (exit 2) when no
mode, or more than one, is set, or the variable is malformed. -/
def tools : IO UInt32 := do
  let set ← Pass3Kernels.toolModes.filterM fun var => return (← IO.getEnv var).isSome
  unless set.length == 1 do
    IO.println s!"[pass3-tools] set exactly one of {Pass3Kernels.toolModes} (set: {set})"
    return 2
  if let some spec := ← IO.getEnv "PASS3_CLOSURE" then
    match spec.splitOn "," with
    | [p, c] => return ← runClosure p c
    | _ => IO.println "[pass3-tools] PASS3_CLOSURE=<file.lean>,<constant>"; return 2
  if let some p := ← IO.getEnv "PASS3_VIEW" then return ← runView p
  if let some spec := ← IO.getEnv "PASS3_FIND" then
    match spec.splitOn "," with
    | p :: pfxs@(_ :: _) => return ← runFind p pfxs
    | _ => IO.println "[pass3-tools] PASS3_FIND=<file.ixe>,<hex prefix>[,…]"; return 2
  if let some d := ← IO.getEnv "PASS3_RECHECK" then return ← runRecheck d
  if let some spec := ← IO.getEnv "PASS3_EXPECT_EMIT" then
    match spec.splitOn "," with
    | rows :: recheck :: more => return ← emit Pass3Kernels.defectOf rows recheck more
    | _ =>
      IO.println "[pass3-tools] PASS3_EXPECT_EMIT=<rows.tsv>,<recheck.tsv>[,<meta recheck.tsv>…]"
      return 2
  return 2

end Tests.Ix.Compile.Pass3Tools
