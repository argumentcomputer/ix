import Ix.Meta
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.SourceIngressStep
import Tests.Ix.Kernel.SourceIngressCompare

/-! # `kernel-source-ingress`: the Source-mode check on Lean environments

* `kernel-source-ingress --fixture`: the `lake test` suite
  `kernel-source-ingress` (`Tests.Ix.Kernel.SourceIngress`).
* `kernel-source-ingress [--workers n] [--rows path] [--ixe path] [--no-certs] [--fiber-hints] [--collapse]
  [--bundle-evidence] Module…`: the modules' environment (default `Init`), with
  `IxC.Kernel.PinGen.Certs` (the certificate theorems Source mode's evidence
  is made of, `Ix.LeanIngress.sourceEvidence`; not with `--no-certs`), loaded
  from this toolchain's `.olean` files, canonicalized (`Ix.CanonM`) and
  condensed (`Ix.GraphM`, `Ix.CondenseM`) on `n` workers (default 8), and
  checked in Source mode group by group (`Tests.Ix.Kernel.SourceIngressStep`)
  at Source mode's evidence (with `--bundle-evidence`, the committed bundle's,
  `Ix.RoleEvidence.bundleEvidence`, whatever the input carries). The
  certificate module's own constants are checked and reported like the
  others. The report (the input names of a derived shape the front door
  reserves, counts of constants and groups by outcome, constants by outcome
  and reason, the blocked constants' roots, the phases' times) goes to
  stdout; with `--rows`, one line per
  constant, `name<TAB>outcome<TAB>kind<TAB>reason`, goes to `path`.
  With `--ixe`, the same environment compiled by Ix's compiler (compiled to
  `path` first if there is no file there) is checked by the Ixon environment
  check under the default role table (`Ix.Kernel.Reader.defaultTable`), and
  the verdicts are compared constant by constant
  (`Tests.Ix.Kernel.SourceIngressCompare`); the differing constants go to
  `path.diff`, and the Ixon verdicts, one line per Lean name sorted by name,
  `name<TAB>outcome<TAB>reason`, to `path.rows`. With `--fiber-hints`, Source
  runs the artifact's hints, one per alias fiber (`Ix.LeanIngress.fiberHints`,
  `checkSourceHinted`), instead of Lean's per name. With `--collapse` (which implies
  `--fiber-hints`), the run is quotient Source's: the artifact's alias fibers
  (`Ix.LeanIngress.fiberAliasAt`, the role read off the default table) collapsed group by
  group, an alias group reported with its representative group's verdict. -/

namespace Tests.Ix.Kernel.SourceIngressMain

open Tests.Ix.Kernel.SourceIngressStep

/-- The module whose certificate theorems Source mode's evidence is. -/
def certsModule : Lean.Name := `IxC.Kernel.PinGen.Certs

structure Args where
  workers : Nat := 8
  rows : Option System.FilePath := none
  ixe : Option System.FilePath := none
  certs : Bool := true
  bundle : Bool := false
  fiberHints : Bool := false
  collapse : Bool := false
  modules : Array Lean.Name := #[]

partial def parse (a : Args) : List String → Except String Args
  | [] => pure a
  | "--workers" :: n :: rest => do
    let some k := n.toNat? | throw s!"bad worker count {n}"
    parse { a with workers := k } rest
  | "--rows" :: p :: rest => parse { a with rows := some p } rest
  | "--ixe" :: p :: rest => parse { a with ixe := some p } rest
  | "--no-certs" :: rest => parse { a with certs := false } rest
  | "--bundle-evidence" :: rest => parse { a with bundle := true } rest
  | "--fiber-hints" :: rest => parse { a with fiberHints := true } rest
  | "--collapse" :: rest => parse { a with collapse := true, fiberHints := true } rest
  | m :: rest =>
    if m.startsWith "--" then throw s!"unknown option {m}"
    else parse { a with modules := a.modules.push m.toName } rest

def main (args : List String) : IO UInt32 := do
  if args == ["--fixture"] then
    return ← LSpec.lspecIO (.ofList [("kernel-source-ingress", Tests.Ix.Kernel.SourceIngress.suite)]) []
  let a ← IO.ofExcept (parse {} args)
  let modules := if a.modules.isEmpty then #[`Init] else a.modules
  let t0 ← IO.monoMsNow
  let leanEnv ← getCompileEnv (if a.certs then modules.push certsModule else modules)
  let consts := leanEnv.constants.toList.toArray
  let t1 ← IO.monoMsNow
  let env ← IO.lazyPure fun _ => canon consts a.workers
  let t2 ← IO.monoMsNow
  let blocks ← IO.lazyPure fun _ => condense env (parallel := a.workers > 1)
  let t3 ← IO.monoMsNow
  IO.println s!"source-ingress: {modules}: {consts.size} Lean constants, {env.consts.size} \
    canonicalized, {blocks.blocks.size} components; load {t1 - t0} ms, canon {t2 - t1} ms, \
    condense {t3 - t2} ms"
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let bundled : Option (Ix.Kernel.Evidences .source) ← if a.bundle then do
      let (ev, whys) := Ix.RoleEvidence.bundleEvidenceReport ()
      IO.println s!"evidence: the committed bundle's (`Ix.RoleEvidence.bundleEvidence`)"
      for why in whys do IO.println s!"  bundle: {why}"
      pure (some ev)
    else pure none
  let artifact ← if a.fiberHints then do
      let some path := a.ixe | throw (IO.userError "--fiber-hints and --collapse need --ixe")
      unless ← path.pathExists do
        let t ← IO.monoMsNow
        let _ ← Ix.CompileM.rsCompileEnvBytes leanEnv path.toString
        IO.println s!"compiled {path} in {(← IO.monoMsNow) - t} ms"
      pure (some (← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))))
    else pure none
  let hints := artifact.map fun ixon => Ix.LeanIngress.fiberHintsMap ixon
  if let some m := hints then
    IO.println s!"hints: the artifact's per alias fiber (`Ix.LeanIngress.fiberHints`), {m.size} keys"
  let tA ← IO.monoMsNow
  let table ← IO.ofExcept (Ix.Kernel.Reader.defaultTable.mapError IO.userError)
  let roles := Ix.LeanIngress.roleAtMap table
  let collapse := if a.collapse then artifact.map (Ix.LeanIngress.fiberAliasAt · roles) else none
  if let some ixon := artifact then
    if a.collapse then
      IO.eprintln s!"collapse: quotient Source at the artifact's alias fibers \
        (`Ix.LeanIngress.fiberAliasAt`, the role read off the default table), \
        {(Ix.LeanIngress.fiberAliasAt ixon roles).size} names mapped to a representative \
        ({(← IO.monoMsNow) - tA} ms)"
  -- the bundle's evidence mentions input keys, which quotient Source renames onto the fiber
  -- representatives (`Ix.LeanIngress.evidenceSubst`, as `checkSourceCollapsedBundled` runs it)
  let evidence := match collapse with
    | some ρ => bundled.map (Ix.LeanIngress.evidenceSubst ρ)
    | none => bundled
  let r ← run pre env blocks a.workers (progress := true) (evidence := evidence) (hints := hints)
    (collapse := collapse)
  if a.collapse then
    IO.println s!"collapse: {r.aliases} groups were an earlier group's alias"
  let withEvidence := r.evidence.filter fun (_, es) => es.any fun
    | .proof _ => true | .defeq => false
  IO.println s!"evidence: {withEvidence.length} well-founded operations with proof evidence: \
    {withEvidence.map fun (r, es) => s!"{repr r} ({es.length})"}"
  for why in r.evidenceErrors do
    IO.println s!"  no evidence: {why}"
  let t4 ← IO.monoMsNow
  let c := r.counts
  IO.println s!"groups {r.rows.size}, declarations {r.decls} ({r.generated} generated by the \
    modeller, {r.projRewrites} projection rewrites)"
  IO.println s!"constants by outcome: {c.constants.toList}"
  IO.println s!"groups by outcome: {c.groups.toList}"
  IO.println s!"phases (ms): {r.times.toList}; source check total {t4 - t3} ms, wall {t4 - t0} ms"
  let reasons := c.reasons.toArray.qsort fun a b => a.2 > b.2
  for ((o, why), k) in reasons do
    IO.println s!"  {o} {k}: {why}"
  -- the roots of the blocked constants
  let mut roots : Std.HashMap String Nat := {}
  for row in r.rows do
    if row.outcome == "blocked" then roots := roots.insert row.reason (roots.getD row.reason 0 + row.names.size)
  for (root, k) in (roots.toArray.qsort fun a b => a.2 > b.2).extract 0 25 do
    IO.println s!"  blocked {k} behind {root}"
  if let some path := a.rows then
    let h ← IO.FS.Handle.mk path .write
    for row in r.rows do
      for n in row.names do
        h.putStrLn s!"{n}\t{row.outcome}\t{row.kind}\t{row.reason}"
    h.flush
  if let some path := a.ixe then
    unless ← path.pathExists do
      let t ← IO.monoMsNow
      let _ ← Ix.CompileM.rsCompileEnvBytes leanEnv path.toString
      IO.println s!"compiled {path} in {(← IO.monoMsNow) - t} ms"
    let t ← IO.monoMsNow
    let ixon ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
    let verdicts ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts ixon
    let cmp := Tests.Ix.Kernel.SourceIngressCompare.compare r.rows verdicts
    IO.println s!"ixon check (default role table) in {(← IO.monoMsNow) - t} ms: {verdicts.size} \
      constants with a verdict, {cmp.unmatched} source constants without one"
    for ((s, i), k) in cmp.pairs.toArray.qsort (fun a b => a.2 > b.2) do
      IO.println s!"  source {s}, ixon {i}: {k}"
    let h ← IO.FS.Handle.mk (path.toString ++ ".diff") .write
    for (n, so, sr, io, ir) in cmp.differing do
      h.putStrLn s!"{n}\t{so}\t{sr}\t{io}\t{ir}"
    h.flush
    let h ← IO.FS.Handle.mk (path.toString ++ ".rows") .write
    let named := (verdicts.toArray.map fun (n, v) => (toString n, v)).qsort (·.1 < ·.1)
    for (n, o, why) in named do
      h.putStrLn s!"{n}\t{o}\t{why}"
    h.flush
    let mut pairReasons : Std.HashMap String Nat := {}
    for (_, so, sr, io, ir) in cmp.differing do
      let key := s!"source {so} ({sr}) / ixon {io} ({ir})"
      pairReasons := pairReasons.insert key (pairReasons.getD key 0 + 1)
    for (k, n) in (pairReasons.toArray.qsort fun a b => a.2 > b.2).extract 0 30 do
      IO.println s!"  {n}: {k}"
  -- exit without tearing the environments down
  IO.Process.exit 0

end Tests.Ix.Kernel.SourceIngressMain

def main (args : List String) : IO UInt32 := Tests.Ix.Kernel.SourceIngressMain.main args
