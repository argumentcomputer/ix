import Ix.CompileM
import Ix.Sharing.Exact

/-!
# Uniform optimizer on the hardest Init constants

Runs `Ix.Sharing.Exact.optimizeSharingUniformTable` for `w ∈ {1, 2, 3}` on the
named constants of an `.ixe` corpus (default: the ten slowest Init runs of
W3's corpus measurement and W3's listed `states` failures), with
`maxStates = 2^20`, and prints one line per run: certified or the error, the
wall time, the search states and the largest component.

```
lake exe uniform-hard <corpus.ixe> [name ...]
lake exe uniform-hard <corpus.ixe> --compare      # every constant, vs the enumeration
lake exe uniform-hard <corpus.ixe> --dump w name  # the largest component
lake exe uniform-hard <corpus.ixe> --tiered [name ...]  # tiered construction, both layouts
```
Limits can be overridden with `UNIFORM_STATES` / `UNIFORM_EVALS`.
-/

namespace Benchmarks.UniformHard

def defaultNames : List String := [
  "Lean.Grind.Config.mk.injEq",
  "Lean.Meta.Simp.Config.mk.injEq",
  "_private.Init.Data.Array.Extract.«0».Array.mem_extract_iff_getElem._proof_1_3",
  "_private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_eq_of._proof_1_21",
  "Nat.Internal.Linear.Poly.denote_eq_cancelAux",
  "_private.Init.Data.Int.LemmasAux.«0».Int.max_assoc._proof_1_1",
  "Int.Internal.Linear.cooper_right",
  "_private.Init.Data.BitVec.Lemmas.«0».BitVec.toInt_allOnes._proof_1_2",
  "_private.Init.Data.Vector.Extract.«0».Vector.extract_push._proof_1",
  "_private.Init.Data.String.Iterate.«0».String.Slice.ByteIterator.finitenessRelation._proof_1",
  "_private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_eq_of._proof_1_23",
  "_private.Init.Data.Vector.Extract.«0».Vector.extract_append_left._proof_1",
  "_private.Init.Data.Nat.Lemmas.«0».Nat.sub_add_sub_cancel._proof_1_1",
  "BitVec.srem_zero_of_dvd",
  "_private.Init.Data.Range.Polymorphic.IntLemmas.«0».Int.size_rco._proof_1_1",
  "_private.Init.Data.Range.Polymorphic.Nat.«0».Std.instLawfulRcoIntersectionNat_4._proof_1",
  "_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_4",
  "Nat.Internal.Linear.ExprCnstr.denote_toNormPoly",
  "List.min_findIdx_findIdx"]

/-- Short name of a head. -/
def headName : Ix.Sharing.Exact.Head → String
  | .sort i => s!"sort{i}"
  | .var i => s!"var{i}"
  | .ref i _ => s!"ref{i}"
  | .recur i _ => s!"rec{i}"
  | .prj _ f => s!"prj{f}"
  | .str _ => "str"
  | .nat _ => "nat"
  | .app => "app"
  | .lam _ => "lam"
  | .all .. => "all"
  | .letE _ => "let"

/-- The tiered construction on the named constants under both layouts: the
three candidate lengths, the winning width and the nominal-width length. -/
def tieredAll (corpus : String) (names : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile corpus
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let limits : Ix.Sharing.Exact.Limits := { maxStates := 1048576 }
  for name in names do
    let found := env.consts.toList.find? fun (addr, _) =>
      match env.addrToName.get? addr with
      | some n => toString n == name
      | none => false
    let some (_, lc) := found | IO.println s!"{name}: not found"
    let .ok c := lc.get | IO.println s!"{name}: decode error"
    for l in [Ix.Sharing.Exact.ShareLayout.tag4, .tagN] do
      let t0 ← IO.monoNanosNow
      let r ← IO.lazyPure fun _ => Ix.Sharing.Exact.canonicalSharingTieredTable l c.sharing
        (Ix.Sharing.Exact.constantInfoRoots c.info) limits
      let t1 ← IO.monoNanosNow
      let ms := (t1 - t0) / 1000000
      match r with
      | .ok r =>
        let nominal := (r.stats.candidateLengths.find? (·.1 == r.stats.nominalW)).map (·.2)
        IO.println s!"{name} {reprStr l}: final={r.stats.phase3LayoutBytes} w={r.stats.w} nominalW={r.stats.nominalW} nominal={nominal.getD 0} candidates={r.stats.candidateLengths} serialized={r.result.variableBytes} stored={hash r.phase1.stored} {ms} ms"
      | .error e => IO.println s!"{name} {reprStr l}: FAILED {repr e} {ms} ms"
      (← IO.getStdout).flush
  return 0

open Ix.Sharing.Exact in
/-- Print the largest uncertain component of a constant at width `w`. -/
def dumpComponent (w : Nat) (c : Ixon.Constant) : IO Unit := do
  let limits : Limits := {}
  let ex ← IO.ofExcept ((expand limits c.sharing (constantInfoRoots c.info) true).mapError (reprStr ·))
  let p := Prep.ofDag ex.dag
  let f := graphFacts ex.dag ex.roots
  let cand := searchCandidates p f w
  let b := uniformBounds p w cand
  let vis := visibleCounts ex.dag ex.roots cand
  let cls := classifyWith p f w b vis
  let comps := uncertainComponents ex.dag cls
  let some comp := comps.foldl (init := none) (fun acc m =>
    match acc with
    | none => some m
    | some a => if m.size > a.size then some m else acc) | IO.println "no component"
  IO.println s!"N={ex.dag.size} roots={ex.roots.size} comps={comps.map (·.size)}"
  let tag (x : Nat) : String :=
    if comp.contains x then s!"*{x}" else
    match cls[x]! with
    | .certainStored => s!"S{x}"
    | .certainExcluded => s!"x{x}"
    | .lowDegree => s!"l{x}"
    | .uncertain => s!"u{x}"
  for t in comp do
    let node := ex.dag.node t
    let g := storedGainC p b w t vis.1[t]! vis.2[t]!
    let ps := f.parents[t]!.map tag
    IO.println s!"{t} {headName node.head} deg={f.deg[t]!}/{vis.1[t]!} hd={f.headDeg[t]!}/{vis.2[t]!} occ={f.occ[t]!} size={p.base[t]!} spine={p.spineLen[t]!} inl⁻={b.inlineLB[t]!} m⁻={b.mergedLB[t]!} g={g} kids={node.children.map tag} parents={ps}"

/-- Every constant of the corpus at `w ∈ {1, 2, 3}`: certify with the
branch and bound (`maxStates = 2^20`), compare with the subset enumeration
where it finishes within `2^14` states (same stored set and model). -/
def compareAll (corpus : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile corpus
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let limits : Ix.Sharing.Exact.Limits := { maxStates := 1048576 }
  let refLimits : Ix.Sharing.Exact.Limits := { maxStates := 1 <<< 14, uniformSubsetSearch := true }
  let mut total := 0
  let mut certified := #[0, 0, 0]
  let mut refOk := #[0, 0, 0]
  let mut compared := #[0, 0, 0]
  let mut mismatches := 0
  let mut failures : Array String := #[]
  for (addr, lc) in env.consts.toList do
    let name := (env.addrToName.get? addr).map toString |>.getD "?"
    let some c := lc.get.toOption | continue
    total := total + 1
    for wi in [0:3] do
      let w := wi + 1
      let roots := Ix.Sharing.Exact.constantInfoRoots c.info
      let r ← IO.lazyPure fun _ => Ix.Sharing.Exact.optimizeSharingUniformTable w c.sharing roots limits
      match r with
      | .ok u =>
        certified := certified.modify wi (· + 1)
        let r2 ← IO.lazyPure fun _ =>
          Ix.Sharing.Exact.optimizeSharingUniformTable w c.sharing roots refLimits
        if let .ok v := r2 then
          refOk := refOk.modify wi (· + 1)
          compared := compared.modify wi (· + 1)
          unless u.stored == v.stored && u.result.modelBytes == v.result.modelBytes do
            mismatches := mismatches + 1
            IO.println s!"MISMATCH {name} w={w}: model {u.result.modelBytes} vs {v.result.modelBytes}"
      | .error e =>
        failures := failures.push s!"{name} w={w}: {repr e}"
        IO.println s!"FAILED {name} w={w}: {repr e}"
    if total % 5000 == 0 then
      IO.println s!"progress {total}: certified {certified} compared {compared} mismatches {mismatches}"
      (← IO.getStdout).flush
  IO.println s!"constants {total}; certified w=1,2,3: {certified}; compared with the enumeration: {compared}; mismatches {mismatches}; failures {failures.size}"
  return if mismatches == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  let some corpus := args.head? | do
    IO.eprintln "usage: uniform-hard <corpus.ixe> [name ...]"
    return 2
  if let [_, "--compare"] := args then return (← compareAll corpus)
  if let _ :: "--tiered" :: ns := args then
    return (← tieredAll corpus (if ns.isEmpty then defaultNames else ns))
  if let [_, "--dump", ws, name] := args then
    let bytes ← IO.FS.readBinFile corpus
    let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
    for (addr, lc) in env.consts.toList do
      if (env.addrToName.get? addr).map toString == some name then
        match lc.get with
        | .ok c => dumpComponent ws.toNat! c
        | .error e => IO.println s!"decode error {e}"
    return 0
  let names := match args.tail with
    | [] => defaultNames
    | ns => ns
  let bytes ← IO.FS.readBinFile corpus
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let evals := ((← IO.getEnv "UNIFORM_EVALS").bind (·.toNat?)).getD (1 <<< 30)
  let states := ((← IO.getEnv "UNIFORM_STATES").bind (·.toNat?)).getD 1048576
  let limits : Ix.Sharing.Exact.Limits := { maxStates := states, maxCostEvals := evals }
  for name in names do
    let found := env.consts.toList.find? fun (addr, _) =>
      match env.addrToName.get? addr with
      | some n => toString n == name
      | none => false
    match found with
    | none => IO.println s!"{name}: not found"
    | some (_, lc) =>
      match lc.get with
      | .error e => IO.println s!"{name}: decode error {e}"
      | .ok c =>
        for w in [1, 2, 3] do
          let t0 ← IO.monoNanosNow
          let r ← IO.lazyPure fun _ => Ix.Sharing.Exact.optimizeSharingUniformTable w c.sharing
            (Ix.Sharing.Exact.constantInfoRoots c.info) limits
          let t1 ← IO.monoNanosNow
          let ms := (t1 - t0) / 1000000
          match r with
          | .ok u =>
            let comp := u.components.foldl (fun acc m => max acc m.size) 0
            IO.println s!"{name} w={w}: certified model={u.result.modelBytes} stored={hash u.stored} cs={u.certainStored.size} unc={u.uncertain.size} states={u.statesVisited} comp={comp} {ms} ms"
          | .error e =>
            IO.println s!"{name} w={w}: FAILED {repr e} {ms} ms"
          (← IO.getStdout).flush
  return 0

end Benchmarks.UniformHard

def main (args : List String) : IO UInt32 := Benchmarks.UniformHard.main args
