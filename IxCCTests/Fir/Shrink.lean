import IxCCTests.Fir.Gen
import IxCCTests.Support.Repro

/-! # Ladders for LamGen and FoGen (MT.5)

The first-diverging-level ladders of the two generators whose programs go
through the middle end and Fir, Own and Cfg (`IxCCTests.Support.Repro`):

* **LamGen** (`Support.LamGen.gen`): the reference is Lam (`Lam.run`); then
  Anf after P1 and after each step of `Anf.Pipeline.produce`; then Fir, Own
  (immortal) and Cfg when the last Anf stage has no closures left (`Fir.lower`
  declines the rest, 06 `fir.closures`). Inputs `0`, `2`, `5`, as `tests-fir`'s
  LamGen part. Lam runs at clock 3000 and every later level at 64·3000 + 1
  (Lam → Anf adds one per root; the later passes keep or lower the clock).
* **FoGen** (`Fir.Gen.programTy`): the reference is the generated Anf
  program; then Fir, Own and Cfg (`Fir.Support.lower`), all at clock 3000
  (Fir finishes by Anf's clock, Own and Cfg in lock step). Inputs `0`, `1`,
  `2`, `3`, `5`, as `tests-fir`'s first-order part.

Each has a planted bug for the demonstrations, applied only by
`check true`: LamGen's swaps the operands of every `natSub`, `natBle` and
`natMod` in the last Anf stage (a broken middle-end step, level
`anf.planted`), FoGen's those of every `natSub` in the Cfg program (a
broken Own → Cfg lowering, level `cfg`). -/

namespace IxCCTests.Fir.Shrink

open IxCC IxCCTests.Lam IxCCTests.Anf IxCCTests.Fir
open IxCCTests.Support (RngM)
open IxCCTests.Support.Repro (Obs Failure Outcome Ladder obsOf firstDivergence)

/-! ## Planted bugs (test-side; production code is unchanged) -/

mutual
partial def swapSubE : Anf.Exp → Anf.Exp
  | .bind c b e => .bind c (swapSubB b) (swapSubE e)
  | .join n r b e => .join n r (swapSubE b) (swapSubE e)
  | .case x alts d => .case x (alts.map fun (.mk k n b) => .mk k n (swapSubE b)) (d.map swapSubE)
  | .tick e => .tick (swapSubE e)
  | e => e

partial def swapSubB : Anf.Bind → Anf.Bind
  | .prim p [a, b] => if [Lam.Prim.natSub, .natBle, .natMod].contains p then .prim p [b, a] else .prim p [a, b]
  | .fn ps b => .fn ps (swapSubE b)
  | b => b
end

/-- A broken middle-end step: the operands of every `natSub`, `natBle` and
`natMod` swapped. -/
def plantAnf (A : Anf.Program) : Anf.Program :=
  { A with globals := Src.NatMap.ofList (A.globalList.map fun (g, gd) => (g, { gd with body := swapSubE gd.body })) }

/-- A broken Own → Cfg lowering: every `natSub`'s operands swapped. -/
def plantCfg (C : Cfg.Program) : Cfg.Program :=
  { C with funs := Src.NatMap.ofList (C.funList.map fun (f, fd) => (f, { fd with
      blocks := fd.blocks.map fun b => { b with body := b.body.map fun
        | .bind x (.fir (.prim .natSub [a, c])) => .bind x (.fir (.prim .natSub [c, a]))
        | i => i } })) }

/-! ## LamGen -/

def lamClock : Nat := 3000

def lamInputs : List (List Nat) := [[0], [2], [5]]

def firstFailure (inputs : List (List Nat)) (ladder : List Nat → IO (List Obs)) : IO (Option Failure) := do
  for xs in inputs do
    if let some (level, expected, got) := firstDivergence (← ladder xs) then
      return some { input := xs, level, expected, got }
  return none

def lamCheck (planted : Bool) (_aux : List Nat) (seqs : Support.Shrink.Seqs) : IO Outcome := do
  let (LP, log) := RngM.replay (seqs[0]?.getD #[]) Support.LamGen.gen
  let seqs := #[log]
  let some p1 := (Anf.convert LP).toOption | return { seqs }
  let text := p1.render
  let base : Outcome := { seqs, size := text.length, text }
  unless Lam.wellFormed LP && Lam.modesOk LP do return base
  let .ok tr := Anf.Pipeline.produce {} LP | return base
  let stages := tr.stages.zipIdx.map fun ((s, A), i) => (s!"anf{i}.{s}", A)
  let some (_, last) := stages.getLast? | return base
  let stages := if planted then stages ++ [("anf.planted", plantAnf last)] else stages
  let final := ((stages.getLast?).map (·.2)).getD last
  let low := (lower final).toOption
  let down := 64 * lamClock + 1
  let ladder := fun (xs : List Nat) => do
    let mut obs : List Obs := []
    let rl ← runLam LP lamClock 0 xs
    obs := obs ++ [{ level := "lam", obs := obsOf rl fun v => reprStr (IxCC.Lam.readback LP v) }]
    for (name, A) in stages do
      let some ar := anfRoot LP A 0 | continue
      let ra ← runAnf A down ar xs
      obs := obs ++ [{ level := name, obs := obsOf ra fun v => reprStr (IxCC.Anf.readback A v) }]
    if let (some L, some ar) := (low, anfRoot LP final 0) then
      let rf ← runFir L.fir down ar xs
      let ro ← runOwn .immortal L.own down ar xs
      let rc ← runCfg .immortal L.cfg down ar xs
      obs := obs ++ [{ level := "fir", obs := obsOf rf fun v => reprStr (IxCC.Fir.readback v) },
        { level := "own", obs := obsOf ro fun (v, H) => reprStr (H.readback v) },
        { level := "cfg", obs := obsOf rc fun (v, H) => reprStr (H.readback v) }]
    return obs
  return { base with failure := ← firstFailure lamInputs ladder }

def lamGen : Ladder where
  generator := "lamgen"
  planted := "the operands of every natSub, natBle and natMod swapped in the last Anf stage (a broken middle-end step)"
  plantedLevel := "anf.planted"
  record := fun seed => #[(RngM.record (UInt64.ofNat seed) Support.LamGen.gen).2]
  check := lamCheck
  ofSeed := fun seed => ((Anf.convert (Support.LamGen.ofSeed seed)).toOption.map (·.render)).getD ""

/-! ## FoGen -/

def foClock : Nat := 3000

def foInputs : List (List Nat) := [[0], [1], [2], [3], [5]]

def foCheck (planted : Bool) (_aux : List Nat) (seqs : Support.Shrink.Seqs) : IO Outcome := do
  let ((A, _), log) := RngM.replay (seqs[0]?.getD #[]) Gen.programTy
  let seqs := #[log]
  let text := A.render
  let base : Outcome := { seqs, size := text.length, text }
  let .ok L := lower A | return base
  let cfg := if planted then plantCfg L.cfg else L.cfg
  let ladder := fun (xs : List Nat) => do
    let ra ← runAnf A foClock 0 xs
    let rf ← runFir L.fir foClock 0 xs
    let ro ← runOwn .immortal L.own foClock 0 xs
    let rc ← runCfg .immortal cfg foClock 0 xs
    return [{ level := "anf", obs := obsOf ra fun v => reprStr (IxCC.Anf.readback A v) },
      { level := "fir", obs := obsOf rf fun v => reprStr (IxCC.Fir.readback v) },
      { level := "own", obs := obsOf ro fun (v, H) => reprStr (H.readback v) },
      { level := "cfg", obs := obsOf rc fun (v, H) => reprStr (H.readback v) }]
  return { base with failure := ← firstFailure foInputs ladder }

def foGen : Ladder where
  generator := "fogen"
  planted := "every natSub's operands swapped in the Cfg program (a broken Own → Cfg lowering)"
  plantedLevel := "cfg"
  record := fun seed => #[(RngM.record (UInt64.ofNat (seed * 104729 + 7)) Gen.programTy).2]
  check := foCheck
  ofSeed := fun seed => (Gen.ofSeed seed).render

end IxCCTests.Fir.Shrink
