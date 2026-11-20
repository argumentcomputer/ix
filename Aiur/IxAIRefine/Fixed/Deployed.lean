import IxAIRefine.Fixed.Soundness
import IxAIRefine.Elab

/-! # The deployed step-only circuit

The per-step packages the prover ships (`IxAIAiur.run`, `IxAIAiur.exportWith`) are not compiled
from the two-entry preparation `IxAIRefine.Check` checks, but from `Modules.prepare` of
`IxAIAiur.source` with `Fixed::step` as its only entry, through `Prepared.compileOptimized`: a
`ModulesArtifact` whose specialization keeps only the functions `Fixed::step` reaches.
`Soundness.step_sound` is stated for a `GenericArtifact` of any specialization of
`IxAIStep.Fixed.source`, so the specialization is not the gap; the source is. This module states
the step theorems over the shipped object.

* `ObsFn.extend`: an observed derivation over a world stays one over any world that answers
  every function or map lookup the first answers, identically, and agrees with it on value
  typing and global declarations (`WorldExtends`). A derivation only enters callees whose
  lookup succeeded, so functions the smaller world lacks are never consulted.
* `step_sound_of_extends`: `Soundness.step_sound_eq` for a compilation of any source whose world
  `IxAIStep.Fixed.source.world` extends.
* `step_sound_deployed`: the same for the shipped `ModulesArtifact` of the step-only
  preparation.
* `train_of_deployed_steps`: 600 accepted claims of that one circuit, chained by their public
  inputs and outputs, end at `IxAICore.train`.

**What stays a hypothesis.** `StepOnlyParity`: that `Modules.prepare` of `IxAIAiur.source` for
`["Fixed::step"]` yields the source `IxAIStep.Fixed.source`. `Modules.prepare` resolves whole
modules, so the step-only preparation still contains `Fixed::train` and `Fixed::train_block`
and its source is the full one; its world is then `IxAIStep.Fixed.source.world` and
`WorldExtends.refl` instantiates `step_sound_of_extends`. Like the parity of the two-entry
preparation (`IxAIRefine.Check`), this is checked by evaluation when the module is elaborated,
not proved: `Modules.prepare` is too large to reduce in the kernel. -/

namespace IxAIStep.Fixed.Deployed

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Optimized
open IxAIStep.Fixed.Obs IxAIStep.Fixed.Specs IxAIStep.Fixed.TrainSpec IxAIStep.Fixed.Soundness
open IxAICore (Fx Model)

section World

variable {G : Type} [DecidableEq G]

/-- `big` answers every function or map lookup that `small` answers, with the same result, and
agrees with `small` on value typing and global declarations. -/
structure WorldExtends (small big : World G) : Prop where
  prepare : ∀ name args r, small.prepare name args = .ok r → big.prepare name args = .ok r
  typed : small.typed = big.typed
  constant : small.constant = big.constant
  constDepth : small.constDepth = big.constDepth

theorem WorldExtends.matchPattern {small big : World G} (h : WorldExtends small big) :
    small.matchPattern = big.matchPattern := by
  simp only [World.matchPattern, h.constant, h.constDepth]

theorem WorldExtends.selectArm {small big : World G} (h : WorldExtends small big)
    (types : Types) (heap : Heap G) (value : SourceValue G) :
    ∀ arms, selectArm small types heap value arms = selectArm big types heap value arms
  | [] => rfl
  | (_, _) :: arms => by
    simp only [SourceSemantics.selectArm]
    rw [h.matchPattern, h.selectArm types heap value arms]

/-- **World extension preserves observed derivations.** The calls recorded are the same. -/
theorem ObsFn.extend [Field G] {small big : World G} (h : WorldExtends small big) {name : String}
    {args : List (SourceValue G)} {before after : Heap G} {result : SourceValue G}
    {calls : List (SourceSemantics.Call G)}
    (observed : ObsFn small name args before result after calls) :
    ObsFn big name args before result after calls := by
  induction observed using ObsFn.rec
    (motive_1 := fun types locals expr before result after calls _ =>
      ObsExpr big types locals expr before result after calls)
    (motive_2 := fun types locals exprs before values after calls _ =>
      ObsArgs big types locals exprs before values after calls)
    (motive_4 := fun types locals expr before target result after calls _ =>
      ObsExit big types locals expr before target result after calls)
    (motive_5 := fun types locals exprs before target result after calls _ =>
      ObsArgsExit big types locals exprs before target result after calls) with
  | block _ ih => exact .block ih
  | blockExit _ ih => exact .blockExit ih
  | literal => exact .literal
  | var lookup => exact .var lookup
  | global lookup interpreted _ ih =>
      exact .global (by rw [← h.constant]; exact lookup) interpreted ih
  | tuple _ ih => exact .tuple ih
  | array _ ih => exact .array ih
  | «repeat» _ ih => exact .«repeat» ih
  | index _ projected ih => exact .index ih projected
  | slice _ sliced ih => exact .slice ih sliced
  | builtin _ applied ih => exact .builtin ih applied
  | update _ updated ih => exact .update ih updated
  | record _ ih => exact .record ih
  | member _ projected ih => exact .member ih projected
  | construct _ ih => exact .construct ih
  | constructAs _ ih => exact .constructAs ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ ih₁ ih₂ =>
      exact .letValue ih₁ (by rw [← h.matchPattern]; exact matched) ih₂
  | store _ ih => exact .store ih
  | load _ loaded ih => exact .load ih loaded
  | hint _ typed ih => exact .hint ih (by rw [← h.typed]; exact typed)
  | neg _ operation ih => exact .neg ih operation
  | binary _ _ operation ih₁ ih₂ => exact .binary ih₁ ih₂ operation
  | call _ _ ih₁ ih₂ => exact .call ih₁ ih₂
  | matchValue _ selected _ ih₁ ih₂ =>
      exact .matchValue ih₁ (by rw [← h.selectArm]; exact selected) ih₂
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | intro prepared _ ih => exact .intro (h.prepare _ _ _ prepared) ih
  | returned prepared _ ih => exact .returned (h.prepare _ _ _ prepared) ih
  | exit _ ih => exact .exit ih
  | exitPayload _ ih => exact .exitPayload ih
  | fromBlock different _ ih => exact .fromBlock different ih
  | fromGlobal lookup interpreted _ ih =>
      exact .fromGlobal (by rw [← h.constant]; exact lookup) interpreted ih
  | fromTuple _ ih => exact .fromTuple ih
  | fromArray _ ih => exact .fromArray ih
  | fromRepeat _ ih => exact .fromRepeat ih
  | fromIndex _ ih => exact .fromIndex ih
  | fromSlice _ ih => exact .fromSlice ih
  | fromBuiltin _ ih => exact .fromBuiltin ih
  | fromUpdate _ ih => exact .fromUpdate ih
  | fromRecord _ ih => exact .fromRecord ih
  | fromMember _ ih => exact .fromMember ih
  | fromConstruct _ ih => exact .fromConstruct ih
  | fromConstructAs _ ih => exact .fromConstructAs ih
  | fromProject _ ih => exact .fromProject ih
  | fromLetValue _ ih => exact .fromLetValue ih
  | letBody _ matched _ ih₁ ih₂ => exact .letBody ih₁ (by rw [← h.matchPattern]; exact matched) ih₂
  | fromStore _ ih => exact .fromStore ih
  | fromLoad _ ih => exact .fromLoad ih
  | fromHint _ ih => exact .fromHint ih
  | fromNeg _ ih => exact .fromNeg ih
  | binaryLeft _ ih => exact .binaryLeft ih
  | binaryRight _ _ ih₁ ih₂ => exact .binaryRight ih₁ ih₂
  | fromCall _ ih => exact .fromCall ih
  | fromMatchValue _ ih => exact .fromMatchValue ih
  | matchBody _ selected _ ih₁ ih₂ =>
      exact .matchBody ih₁ (by rw [← h.selectArm]; exact selected) ih₂
  | head _ ih => exact .head ih
  | tail _ _ ih₁ ih₂ => exact .tail ih₁ ih₂

omit [DecidableEq G] in
theorem WorldExtends.refl (world : World G) : WorldExtends world world :=
  ⟨fun _ _ _ h => h, rfl, rfl, rfl⟩

end World

/-! ## The step-only preparation

`Modules.prepare` resolves whole modules: with `["Fixed::step"]` as its entries it still
assembles every function of the `UInt8` and `Fixed` modules, `Fixed::train` and
`Fixed::train_block` included, and the source it prepares is `IxAIStep.Fixed.source`. Only the
selected entries (`Prepared.entries`) and the specialization of the compiled circuit (which keeps
the functions reachable from those entries) differ from the two-entry preparation. -/

/-- **Gap 3 for the deployed circuit.** Preparing `IxAIAiur.source` with `Fixed::step` as its
only entry, as `IxAIAiur.run` and `IxAIAiur.exportWith` do before compiling the shipped circuit,
yields the source `IxAIStep.Fixed.source`. Checked by evaluation below; not proved. -/
def StepOnlyParity : Prop :=
  ∀ stepOnly : Modules.Prepared (IxAIAiur.source.toField F),
    Modules.prepare (IxAIAiur.source.toField F) ["Fixed::step"] = .ok stepOnly →
      stepOnly.environment.source = IxAIStep.Fixed.source

/-- Whether the step-only preparation's source is `IxAIStep.Fixed.source`, part by part, and
whether its only entry is `Fixed::step`. -/
def stepParity : Except String (Bool × Bool × Bool) := do
  let input ← Elab.moduleProgram
  let prepared ← Aiur.Modules.prepare input ["Fixed::step"]
  let src := prepared.environment.source
  return (src.program == program, src.tables == coreTables, prepared.entries == ["Fixed::step"])

#eval show IO Unit from do
  let (prog, tables, entries) ← IO.ofExcept stepParity
  unless prog && tables && entries do
    throw (IO.userError
      s!"step-only source parity: program {prog}, tables {tables}, entries {entries}")
  IO.println "step-only source parity: program and static tables match Modules.prepare"

/-! ## Soundness of the deployed step claims -/

/-- **`Soundness.step_sound_eq` over any source whose world the full source's extends.** -/
theorem step_sound_of_extends {src : Source F} (extends_ : WorldExtends src.world source.world)
    {entries : List String} {specialized : Generic.Specialized src entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::step" ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} (hm : ModelOk m) {b : Batch} (hb : BatchOk b)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Circuit.Erasure.Signed compiled.system ⟨"Fixed::step", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.system ⟨"Fixed::step", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues [IxAIAiur.mat m.w1, IxAIAiur.vec m.b1, IxAIAiur.mat m.w2, IxAIAiur.vec m.b2,
        encXs b, encTs b, fxVal lr]))
    (decoded : output.decode specialized.program.enums = some result) :
    result = (encModel (m.step lr b)).mapAddress (fun _ => 0) ∧ ModelOk (m.step lr b) := by
  obtain ⟨value, heap, calls, ev, related, -⟩ :=
    prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed compiled certified bits
      plan activated entry valid signed rooted outside bound checked arguments decoded
  obtain ⟨hv, hm'⟩ := step_refines hlr hm hb (encModel_split m) (ObsFn.extend extends_ ev)
  exact ⟨represents_eq_of_pointerFree (hv ▸ related) (encModel_pointerFree _), hm'⟩

/-- **An accepted deployed `Fixed::step` claim outputs `Model.step`, as data.** The hypotheses
are over the shipped artifact: `stepOnly` is `Modules.prepare` of `IxAIAiur.source` for
`["Fixed::step"]` and `compiled` a `ModulesArtifact` of it (what `stepOnly.compileOptimized`
returns), whose circuit the memo checker accepts. With `StepOnlyParity`, the conclusion is
`Soundness.step_sound_eq`'s. -/
theorem step_sound_deployed (parity : StepOnlyParity)
    {stepOnly : Modules.Prepared (IxAIAiur.source.toField F)}
    (shipped : Modules.prepare (IxAIAiur.source.toField F) ["Fixed::step"] = .ok stepOnly)
    (compiled : ModulesArtifact stepOnly) (prepared : Physical.Prepared compiled.circuit.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::step" ∈ stepOnly.entries) {rom : WidthROM F} (valid : rom.Valid)
    {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} (hm : ModelOk m) {b : Batch} (hb : BatchOk b)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Circuit.Erasure.Signed compiled.circuit.system ⟨"Fixed::step", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.circuit.system ⟨"Fixed::step", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires
      (entryValues [IxAIAiur.mat m.w1, IxAIAiur.vec m.b1, IxAIAiur.mat m.w2, IxAIAiur.vec m.b2,
        encXs b, encTs b, fxVal lr]))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    result = (encModel (m.step lr b)).mapAddress (fun _ => 0) ∧ ModelOk (m.step lr b) :=
  step_sound_of_extends (by rw [parity stepOnly shipped]; exact WorldExtends.refl _)
    compiled.circuit prepared certified bits plan activated entry valid hlr hm hb signed rooted
    outside bound checked arguments decoded

/-- **600 accepted deployed step claims, chained by public IO, end at `IxAICore.train`.** One
shipped step circuit (`stepOnly`, `compiled`, ...) accepts, for every `i < 600`, a claim whose
arguments decode to the model `ms i`, batch `i` of `fullBatches` and `fullLr`, and whose output
decodes to the encoding of `ms (i + 1)`: claim `i`'s public output is claim `i + 1`'s public
model input. With `ms 0` the full configuration's initial model and every later `ms i` passing
the public check `modelOkB`, `ms 600` is the trained model. -/
theorem train_of_deployed_steps (parity : StepOnlyParity)
    {stepOnly : Modules.Prepared (IxAIAiur.source.toField F)}
    (shipped : Modules.prepare (IxAIAiur.source.toField F) ["Fixed::step"] = .ok stepOnly)
    (compiled : ModulesArtifact stepOnly) (prepared : Physical.Prepared compiled.circuit.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::step" ∈ stepOnly.entries)
    {ms : ℕ → Model} (h0 : ms 0 = fullInit) (hok : ∀ i < 600, modelOkB (ms (i + 1)) = true)
    {rom : ℕ → WidthROM F} (valid : ∀ i < 600, (rom i).Valid)
    {wires : ℕ → List (WireValue F)} {output : ℕ → WireValue F}
    (signed : ∀ i < 600,
      Circuit.Erasure.Signed compiled.circuit.system ⟨"Fixed::step", wires i, output i⟩)
    {root : ℕ → Circuit.Message F}
    (rooted : ∀ i < 600, Depth.erase cfg (root i) =
      Circuit.Erasure.message compiled.circuit.system ⟨"Fixed::step", wires i, output i⟩)
    (outside : ∀ i < 600, (root i).channel ∉ cfg.names)
    {rows : ℕ → List (Circuit.WeightedRow F)} (bound : ∀ i < 600, (rows i).length ≤ 2 ^ 39)
    (checked : ∀ i < 600,
      plan.checkMemo (Circuit.Erasure.rawROM (rom i)) (root i) (rows i) = .ok ())
    (arguments : ∀ i < 600, DecodesValues compiled.specialized.program.enums (wires i)
      (entryValues [IxAIAiur.mat (ms i).w1, IxAIAiur.vec (ms i).b1, IxAIAiur.mat (ms i).w2,
        IxAIAiur.vec (ms i).b2, encXs (fullBatches.getD i []), encTs (fullBatches.getD i []),
        fxVal fullLr]))
    (decoded : ∀ i < 600, (output i).decode compiled.specialized.program.enums =
      some ((encModel (ms (i + 1))).mapAddress (fun _ => 0))) :
    ms 600 = IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig := by
  refine train_of_steps h0 hok fun i hi hmi => ?_
  have hb : BatchOk (fullBatches.getD i []) := by
    have hlt : i < fullBatches.length := by rw [fullBatches_ok.1]; exact hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact fullBatches_ok.2 _ (List.getElem_mem hlt)
  exact step_sound_deployed parity shipped compiled prepared certified bits plan activated entry
    (valid i hi) fullLr_le hmi hb (signed i hi) (rooted i hi) (outside i hi) (bound i hi)
    (checked i hi) (arguments i hi) (decoded i hi)

end IxAIStep.Fixed.Deployed
