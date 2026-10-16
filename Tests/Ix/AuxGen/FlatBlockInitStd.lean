import Tests.Ix.AuxGen.FlatBlockSource

/-! # The Source service environment on Init+Std (`lake exe IxTests --ignored auxgen-flat-initstd`)

AuxGen on IxC, M1, measured on the compiler's own input: what the service
costs and covers if a driver asks it, before each inductive block's aux
tail, for that block's groups and its canonical flat block (AUXGEN-IXC §3.2,
"incrementally in the driver"). Not wired into the drivers (that waits for
CQ2.14); this is the projection.

Init+Std is canonicalized and condensed as `kernel-source-ingress` does it,
and compiled by the driver (`compileEnvFold`, `--workers` tasks per wave, production
`Ix.Tc` kernel), whose environment the aux generator reads, as
`aux-gen-diff`'s patch gate does. Then, over every inductive block in
dependency order:
1. the service folds the block's groups and what they depend on
   (`Service.ensureNames`);
2. the block's canonical classes and recursors are generated
   (`generateAuxPatches`) and, where the layout is not Lean's, its flat
   block is built and installed, and σ is checked against `Key.map` (as in
   `auxgen-flat-source`).

Printed: each phase's time, the groups folded (of all), the inductive blocks
whose own groups Source mode accepted, the flat blocks needed and accepted,
the refusal reasons. Asserted: every flat block whose block's own groups
Source mode accepted is accepted, and σ fits `Key.map` on each.

`AUXGEN_CERTS=1` adds `IxC.Kernel.PinGen.Certs` to the input, as
`kernel-source-ingress` does: Source mode's evidence for the well-founded
`Nat` operations is those theorems, which the compiler's input does not carry. -/

namespace Tests.Ix.AuxGen.FlatBlockInitStd

open LSpec
open Ix.AuxGen.Source (Service Status)
open Tests.Ix.AuxGen.FlatBlockSource
open Tests.Ix.Kernel.SourceIngressStep (canon condense)

def workers : Nat := 32

def evaluate : IO (Array String × Array String) := do
  let certs := (← IO.getEnv "AUXGEN_CERTS") == some "1"
  let modules := #[`Init, `Std] ++ (if certs then #[`IxC.Kernel.PinGen.Certs] else #[])
  let t0 ← IO.monoMsNow
  let leanEnv ← getCompileEnv modules
  let consts := leanEnv.constants.toList.toArray
  let env ← IO.lazyPure fun _ => canon consts workers
  let blocks ← IO.lazyPure fun _ => condense env (parallel := true)
  let t1 ← IO.monoMsNow
  let (_, _, cenv) ← match ← IO.lazyPure fun _ => Ix.CompileM.compileEnvFold env blocks (width := workers) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"compile: {e}")
  let t2 ← IO.monoMsNow
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let mut svc ← IO.lazyPure fun _ => Service.create pre env blocks (workers := workers)
  let t3 ← IO.monoMsNow
  let lookup := cenv.env.consts.get?
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let mut ensureNs := 0
  let mut auxNs := 0
  let mut flatNs := 0
  let mut nBlocks := 0
  let mut ownAccepted := 0
  let mut needed := 0
  let mut accepted := 0
  let mut refusedWhy : Std.HashMap String Nat := {}
  let mut ownRefused : Std.HashMap String Nat := {}
  for (lo, members) in inductiveBlocks env blocks do
    nBlocks := nBlocks + 1
    let s0 ← IO.monoNanosNow
    svc ← IO.lazyPure fun _ => svc.ensureNames members
    let s1 ← IO.monoNanosNow
    ensureNs := ensureNs + (s1 - s0)
    let own := members.all fun n => (svc.statusOf? n).any (·.isAccepted)
    if own then ownAccepted := ownAccepted + 1
    else
      let why := (members.findSome? fun n => match svc.statusOf? n with
        | some (.refused r) => some (r.take 90).toString
        | some (.blocked _) => some "blocked"
        | _ => none).getD "?"
      ownRefused := bump ownRefused why
    match ← IO.lazyPure fun _ => blockAux cenv lo members with
    | .error e =>
      auxNs := auxNs + ((← IO.monoNanosNow) - s1)
      errors := errors.push s!"{lo.pretty}: aux generation: {e.take 200}"
    | .ok none => auxNs := auxNs + ((← IO.monoNanosNow) - s1)
    | .ok (some b) =>
      let s2 ← IO.monoNanosNow
      auxNs := auxNs + (s2 - s1)
      let nClasses := b.classes.size
      let auxNames := (b.out.canonicalRecs.extract nClasses b.out.canonicalRecs.size).map (·.1)
      let leanNested := match b.originalAll[0]?.bind lookup with
        | some (.inductInfo v) => v.numNested
        | _ => 0
      if Ix.AuxGen.Flat.needed b.classes b.originalAll auxNames leanNested then
        needed := needed + 1
        match Ix.AuxGen.Flat.build lookup b.classes b.out.canonicalRecs svc.sigma with
        | .error e => errors := errors.push s!"{lo.pretty}: build: {e}"
        | .ok fb =>
          svc ← IO.lazyPure fun _ => svc.installFlat fb
          match svc.flatStatus? (fb.firstName.getD default) with
          | some .accepted =>
            accepted := accepted + 1
            unless fits svc.sigma (sourceTerms lookup b) do
              errors := errors.push s!"{lo.pretty}: σ does not fit Key.map"
          | some (.refused why) =>
            refusedWhy := bump refusedWhy (why.take 120).toString
            if own then errors := errors.push s!"{lo.pretty}: flat block refused: {why.take 200}"
          | _ => errors := errors.push s!"{lo.pretty}: flat block not recorded"
      flatNs := flatNs + ((← IO.monoNanosNow) - s2)
  let (pending, acc, ref, blk) := svc.counts
  lines := lines.push s!"Init+Std{if certs then " + certificate theorems" else ""}: \
    {env.consts.size} constants, {svc.status.size} Source groups; load, canon and condense \
    {t1 - t0} ms; compile {t2 - t1} ms (parallel driver, {workers} workers)"
  lines := lines.push s!"service: create {t3 - t2} ms (groups, conversion, order, lowering, \
    evidence, prelude); folds on demand {ensureNs / 1000000} ms; aux generation \
    {auxNs / 1000000} ms; flat blocks {flatNs / 1000000} ms"
  lines := lines.push s!"groups folded: {acc} accepted, {ref} refused, {blk} blocked; {pending} of \
    {svc.status.size} never asked for"
  lines := lines.push s!"inductive blocks {nBlocks}: own groups accepted {ownAccepted}; flat \
    blocks needed {needed}, accepted {accepted}"
  for (why, k) in (ownRefused.toArray.qsort fun a b => a.2 > b.2).extract 0 12 do
    lines := lines.push s!"  block not accepted ({k}): {why}"
  let mut blockedBehind : Std.HashMap Nat Nat := {}
  for (st, i) in svc.status.zipIdx do
    match st with
    | .refused why =>
      lines := lines.push s!"  group refused: {svc.graph.groups[i]!.name}: {(why.take 160).toString}"
    | .blocked root => blockedBehind := blockedBehind.insert root (blockedBehind.getD root 0 + 1)
    | _ => pure ()
  for (root, k) in (blockedBehind.toArray.qsort fun a b => a.2 > b.2).extract 0 12 do
    lines := lines.push s!"  groups blocked behind {svc.graph.groups[root]!.name}: {k}"
  for (why, k) in (refusedWhy.toArray.qsort fun a b => a.2 > b.2).extract 0 12 do
    lines := lines.push s!"  flat block refused ({k}): {why}"
  return (errors, lines)

def run : IO UInt32 := do
  let (errors, lines) ← evaluate
  for l in lines do IO.println s!"[auxgen-flat-initstd] {l}"
  for e in errors.extract 0 40 do IO.println s!"[auxgen-flat-initstd] error: {e}"
  if errors.isEmpty then
    IO.println "[auxgen-flat-initstd] PASS"
    return 0
  IO.println s!"[auxgen-flat-initstd] FAIL: {errors.size} error(s)"
  return 1

end Tests.Ix.AuxGen.FlatBlockInitStd
