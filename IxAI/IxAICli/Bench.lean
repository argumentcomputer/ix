import IxAICli.Codegen
import IxAICli.RL
import IxAIBench.Baseline
import IxAIBench.Large
import IxAIBench.Typed
import IxAIBench.TypedXhard
import IxAIVerify.Trajectory

/-!
# `ixai bench`: IxBench dispatch

The v0 report's setup for a size (its triage and RL configs and its integrity checks: forged claims
and a tampered trajectory, refused natively), and the dispatch to the v0, M2b and Mathlib reports
of `IxAIBench`.
-/

namespace IxAICli

open IxAI IxAIVerify

/- Closed subterms such as `benchSetup "small"` or a reference training run would otherwise become
module initializers, run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

/-- The forged claims of `writeForged`, each checked against the specification natively: a claim
is refused when the specified value differs from the claimed one, which is what the Eval claim
checks. -/
def forgedChecks (c : IxAICore.Config) : List (String × String) :=
  let s := IxAICore.Triage.spec
  let m := IxAICore.train s c
  let cd := IxAICore.card s c m
  let f := forgedClaims c cd
  let verdict := fun (refused : Bool) => if refused then "pass (refused)" else "FAIL (accepted)"
  [("forged: card with `valid` accuracy +5 claimed as `card spec config model`", verdict (cd != f.inflated)),
   ("forged: model trained on inverted labels claimed as `train spec config`", verdict (m != f.relabeled)),
   ("forged: model trained one epoch longer claimed as `train spec config`", verdict (m != f.overtrained))]

/-- An honest trajectory of `defaultConfig` is accepted by `verifyRun`; the same run with one
parameter changed by 1/256 halfway, continued honestly from there and committed to its new final
weights, is refused. -/
def trajectoryCheck (_ : Unit) : String :=
  let s : DataSpec := {}
  let d := s.generate
  let c := defaultConfig
  let links : List (Link (MLP Fx) (List Nat)) := c.run d
  let claimOf := fun (ls : List (Link (MLP Fx) (List Nat))) =>
    ({ datasetRoot := d.root, config := c, finalCommit := (chainEnd c.init ls).commit } : TrainClaim)
  let k := links.length / 2
  let tampered := match links.drop k with
    | l :: rest =>
      let bumped := MLP.ofList c.hidden (match l.after.params with
        | p :: ps => (⟨p.raw + 1⟩ : Fx) :: ps
        | [] => [])
      let tail := (rest.map (·.input)).foldl (fun (acc : MLP Fx × Array (Link (MLP Fx) (List Nat))) idx =>
        let m' := c.stepFn d acc.1 idx
        (m', acc.2.push ⟨acc.1, idx, m'⟩)) (bumped, #[])
      links.take k ++ [{ l with after := bumped }] ++ tail.2.toList
    | [] => links
  let honest := verifyRun (claimOf links) d links
  let forged := verifyRun (claimOf tampered) d tampered
  if honest && !forged then s!"pass (honest {links.length}-step run accepted; tampered at step {k} refused)"
  else s!"FAIL (honest accepted {honest}, tampered accepted {forged})"

def benchSetup (size : String) : Option IxAIBench.Setup := do
  let c ← (triageConfigs.find? (·.1 == size)).map (·.2)
  let (rb, rc) ← (rlConfigs.find? (·.1 == size)).map (·.2)
  pure { size, triage := c, rlBase := rb, rl := rc
         checks := forgedChecks c ++ [("tampered training trajectory refused by `verifyRun` (`ixai check`)", trajectoryCheck ())] }

def bench (args : List String) : IO UInt32 := do
  let some full := (triageConfigs.find? (·.1 == "full")).map (·.2) | return 2
  match args with
  | [] => match benchSetup "small" with
    | some st => IxAIBench.run st
    | none => return 2
  | ["typed"] => IxAIBench.TypedBench.run
  | ["typed-sweep"] => IxAIBench.TypedBench.sweep
  | ["typed-cert"] => IxAIBench.TypedBench.runCert
  | ["typed-refute"] => IxAIBench.TypedBench.refuteStats IxAIBench.TypedBench.refuteSweep
  | ["typed-xhard"] => IxAIBench.TypedBench.runXhard
  | ["typed-xhard-sweep"] => IxAIBench.TypedBench.sweepXhard
  | ["export-xhard", dir] => IxAIBench.TypedBench.exportXhard dir
  | ["score-xhard", dir] => IxAIBench.TypedBench.scoreXhard dir
  | "mathlib-full" :: rest => IxAIBench.Large.main rest
  | [size] => match benchSetup size with
    | some st =>
      let c ← IxAIBench.run st
      if c != 0 || size != "full" then return c else IxAIBench.TypedBench.run
    | none => IO.eprintln s!"unknown size {size}; sizes: tiny, small, full, typed"; return 2
  | ["export", dir] => do
    let c ← IxAIBench.main full ["export", dir]
    if c != 0 then return c else IxAIBench.TypedBench.exportTo dir
  | ["score", dir] => do
    let c ← IxAIBench.main full ["score", dir]
    if c != 0 then return c else IxAIBench.TypedBench.score dir
  | rest => IxAIBench.main full rest

end IxAICli
