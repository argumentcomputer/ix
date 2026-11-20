import IxAIRefine.Fixed.Deployed

/-! # The deployed block circuit

The block packages the prover ships (`IxAIAiur.exportBlocks`) are compiled from
`Modules.prepare` of `IxAIAiur.source` with `Fixed::train_block` as its only entry. Each runs 20
steps on a model, `lr` and a group of 20 gathered batches; the run is 30 such claims, block `i`
on group `i` of `IxAIAiur.blocks20 fullBatches`, chained by their public inputs and outputs.
This module states for them what `Deployed` states for the step circuit.

* `block_refines`: an observed `Fixed::train_block` on a `ModelOk` model `m`, 20 `BatchOk`
  batches `blk` and `|lr| ≤ 2^8` returns `encModel (blk.foldl (Model.step lr) m)`, again
  `ModelOk`. `TrainSpec.train_block_chain` reads the 20 step derivations off the generated
  path lemma and `chain_spec_ok` folds `TrainSpec.step_refines` over them.
* `block_sound_of_extends`, `block_sound_eq`, `block_sound_deployed`: an accepted block claim
  outputs, as data, the encoding of that fold.
* `train_of_blocks`, `train_of_deployed_blocks`: 30 block claims, each output identified with the
  next claim's model, end at `IxAICore.train`.

**What stays a hypothesis.** `BlockOnlyParity`, the analogue of `Deployed.StepOnlyParity`: that
`Modules.prepare` of `IxAIAiur.source` for `["Fixed::train_block"]` yields the source
`IxAIStep.Fixed.source`. It is checked by evaluation when the module is elaborated
(`blockParity`), not proved. -/

namespace IxAIStep.Fixed.Blocks

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Optimized
open IxAIStep.Fixed.Obs IxAIStep.Fixed.Specs IxAIStep.Fixed.TrainSpec IxAIStep.Fixed.Soundness
open IxAIStep.Fixed.Deployed
open IxAICore (Fx Model)

/-! ## One block is 20 steps -/

/-- **A chain of observed steps is the fold of `Model.step`, and stays `ModelOk`.**
`TrainSpec.chain_spec` with the bound on the last model, which only the steps' derivations give:
`Fixed::upd` range-checks every parameter a step returns. -/
theorem chain_spec_ok {lr : Fx} (hlr : |lr.raw| ≤ 256) {bs : List Batch}
    (hbs : ∀ b ∈ bs, BatchOk b) :
    ∀ {m : Model} {v r : SourceValue F}, encModel m = v → StepChain (fxVal lr) v bs r →
      ModelOk m →
        r = encModel (bs.foldl (Model.step lr) m) ∧ ModelOk (bs.foldl (Model.step lr) m) := by
  induction bs with
  | nil =>
    intro m v r hv hc hm
    cases hc
    rw [List.foldl_nil]
    exact ⟨hv.symm, hm⟩
  | cons b bs ih =>
    intro m v r hv hc hm
    cases hc with
    | cons ev rest =>
      obtain ⟨hstep, hm'⟩ := step_refines hlr hm (hbs b (by simp)) hv ev
      rw [List.foldl_cons]
      exact ih (fun b' hb' => hbs b' (by simp [hb'])) hstep.symm rest hm'

/-- The arguments of `Fixed::train_block`: the model's four parameters, `lr`, and the group's
inputs and targets, in the order `IxAIAiur.exportBlocks` passes them. -/
abbrev blockValues (m : Model) (lr : Fx) (blk : List Batch) : List (SourceValue F) :=
  [IxAIAiur.mat m.w1, IxAIAiur.vec m.b1, IxAIAiur.mat m.w2, IxAIAiur.vec m.b2, fxVal lr,
    encBlockXs blk, encBlockTs blk]

/-- **One observed `Fixed::train_block` is 20 `Model.step`s**, and the result is again
`ModelOk`. -/
theorem block_refines {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} (hm : ModelOk m)
    {blk : List Batch} (hlen : blk.length = 20) (hbs : ∀ b ∈ blk, BatchOk b)
    {h h' : Heap F} {v : SourceValue F} {cs : List (SourceSemantics.Call F)}
    (ev : ObsFn W "Fixed::train_block" (blockValues m lr blk) h v h' cs) :
    v = encModel (blk.foldl (Model.step lr) m) ∧ ModelOk (blk.foldl (Model.step lr) m) :=
  chain_spec_ok hlr hbs (encModel_split m) (train_block_chain hlen ev) hm

/-! ## The block-only preparation -/

/-- **Source parity of the deployed block circuit.** Preparing `IxAIAiur.source` with
`Fixed::train_block` as its only entry, as `IxAIAiur.exportBlocks` does before compiling the
shipped circuit, yields the source `IxAIStep.Fixed.source`. Checked by evaluation below; not
proved. -/
def BlockOnlyParity : Prop :=
  ∀ blockOnly : Modules.Prepared (IxAIAiur.source.toField F),
    Modules.prepare (IxAIAiur.source.toField F) ["Fixed::train_block"] = .ok blockOnly →
      blockOnly.environment.source = IxAIStep.Fixed.source

/-- Whether the block-only preparation's source is `IxAIStep.Fixed.source`, part by part, and
whether its only entry is `Fixed::train_block`. -/
def blockParity : Except String (Bool × Bool × Bool) := do
  let input ← Elab.moduleProgram
  let prepared ← Aiur.Modules.prepare input ["Fixed::train_block"]
  let src := prepared.environment.source
  return (src.program == program, src.tables == coreTables,
    prepared.entries == ["Fixed::train_block"])

#eval show IO Unit from do
  let (prog, tables, entries) ← IO.ofExcept blockParity
  unless prog && tables && entries do
    throw (IO.userError
      s!"block-only source parity: program {prog}, tables {tables}, entries {entries}")
  IO.println "block-only source parity: program and static tables match Modules.prepare"

/-! ## Soundness of block claims -/

/-- **An accepted `Fixed::train_block` claim outputs 20 `Model.step`s, as data**, over any
source whose world the full source's extends. -/
theorem block_sound_of_extends {src : Source F} (extends_ : WorldExtends src.world source.world)
    {entries : List String} {specialized : Generic.Specialized src entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train_block" ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} (hm : ModelOk m)
    {blk : List Batch} (hlen : blk.length = 20) (hbs : ∀ b ∈ blk, BatchOk b)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Circuit.Erasure.Signed compiled.system ⟨"Fixed::train_block", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.system ⟨"Fixed::train_block", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues (blockValues m lr blk)))
    (decoded : output.decode specialized.program.enums = some result) :
    result = (encModel (blk.foldl (Model.step lr) m)).mapAddress (fun _ => 0) ∧
      ModelOk (blk.foldl (Model.step lr) m) := by
  obtain ⟨value, heap, calls, ev, related, -⟩ :=
    prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed compiled certified bits
      plan activated entry valid signed rooted outside bound checked arguments decoded
  obtain ⟨hv, hm'⟩ := block_refines hlr hm hlen hbs (ObsFn.extend extends_ ev)
  exact ⟨represents_eq_of_pointerFree (hv ▸ related) (encModel_pointerFree _), hm'⟩

/-- **An accepted `Fixed::train_block` claim outputs 20 `Model.step`s, as data.** The analogue of
`Soundness.step_sound_eq`, for a compilation of `IxAIStep.Fixed.source`. -/
theorem block_sound_eq {entries : List String}
    {specialized : Generic.Specialized IxAIStep.Fixed.source entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train_block" ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} (hm : ModelOk m)
    {blk : List Batch} (hlen : blk.length = 20) (hbs : ∀ b ∈ blk, BatchOk b)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Circuit.Erasure.Signed compiled.system ⟨"Fixed::train_block", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.system ⟨"Fixed::train_block", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues (blockValues m lr blk)))
    (decoded : output.decode specialized.program.enums = some result) :
    result = (encModel (blk.foldl (Model.step lr) m)).mapAddress (fun _ => 0) ∧
      ModelOk (blk.foldl (Model.step lr) m) :=
  block_sound_of_extends (WorldExtends.refl _) compiled prepared certified bits plan activated
    entry valid hlr hm hlen hbs signed rooted outside bound checked arguments decoded

/-- **An accepted deployed `Fixed::train_block` claim outputs 20 `Model.step`s, as data.** The
hypotheses are over the shipped artifact: `blockOnly` is `Modules.prepare` of `IxAIAiur.source`
for `["Fixed::train_block"]` and `compiled` a `ModulesArtifact` of it (what
`blockOnly.compileOptimized` returns), whose circuit the memo checker accepts. -/
theorem block_sound_deployed (parity : BlockOnlyParity)
    {blockOnly : Modules.Prepared (IxAIAiur.source.toField F)}
    (shipped : Modules.prepare (IxAIAiur.source.toField F) ["Fixed::train_block"] = .ok blockOnly)
    (compiled : ModulesArtifact blockOnly) (prepared : Physical.Prepared compiled.circuit.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train_block" ∈ blockOnly.entries) {rom : WidthROM F} (valid : rom.Valid)
    {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} (hm : ModelOk m)
    {blk : List Batch} (hlen : blk.length = 20) (hbs : ∀ b ∈ blk, BatchOk b)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed :
      Circuit.Erasure.Signed compiled.circuit.system ⟨"Fixed::train_block", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.circuit.system ⟨"Fixed::train_block", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires
      (entryValues (blockValues m lr blk)))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    result = (encModel (blk.foldl (Model.step lr) m)).mapAddress (fun _ => 0) ∧
      ModelOk (blk.foldl (Model.step lr) m) :=
  block_sound_of_extends (by rw [parity blockOnly shipped]; exact WorldExtends.refl _)
    compiled.circuit prepared certified bits plan activated entry valid hlr hm hlen hbs signed
    rooted outside bound checked arguments decoded

/-! ## Chaining block claims -/

/-- The full configuration's gathered batches in the 30 groups of 20 the block claims take,
as `IxAIAiur.exportBlocks` groups them. -/
def fullBlocks : List (List Batch) := IxAIAiur.blocks20 fullBatches

/-- 30 groups of 20 `BatchOk` batches, which together are `fullBatches`. -/
theorem fullBlocks_shape :
    fullBlocks.length = 30 ∧ (∀ blk ∈ fullBlocks, blk.length = 20 ∧ ∀ b ∈ blk, BatchOk b) ∧
      fullBlocks.flatten = fullBatches := by
  obtain ⟨hlen, hall⟩ := fullBatches_ok
  obtain ⟨h30, h20⟩ := chunk20_shape fullBatches.length 30 fullBatches (by omega) (by omega)
  refine ⟨h30, fun blk hblk => ⟨h20 blk hblk, fun b hb => hall b ?_⟩,
    chunk20_flatten fullBatches.length fullBatches (by omega)⟩
  rw [← chunk20_flatten fullBatches.length fullBatches (by omega)]
  exact List.mem_flatten.mpr ⟨blk, hblk, hb⟩

/-- **A chain of 30 block claims ends at `IxAICore.train`.** The analogue of
`Soundness.train_of_steps`: `ms i` is the model block claim `i` is stated over. If `ms 0` is the
full configuration's initial model, every later `ms i` passes the public check `modelOkB`, and
for every `i < 30` whose model is `ModelOk` the output of block `i` on group `i` of `fullBlocks`
with `fullLr` is, as data, the encoding of `ms (i + 1)` and a `ModelOk` model (the conclusion
of `block_sound_eq`, with the output identified with the next claim's model), then `ms 30` is the
trained model. -/
theorem train_of_blocks {ms : ℕ → Model} (h0 : ms 0 = fullInit)
    (hok : ∀ i < 30, modelOkB (ms (i + 1)) = true)
    (hblock : ∀ i < 30, ModelOk (ms i) →
      (encModel (ms (i + 1))).mapAddress (fun _ => (0 : F)) =
          (encModel ((fullBlocks.getD i []).foldl (Model.step fullLr) (ms i))).mapAddress
            (fun _ => 0) ∧
        ModelOk ((fullBlocks.getD i []).foldl (Model.step fullLr) (ms i))) :
    ms 30 = IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig := by
  obtain ⟨hlen, -, hflat⟩ := fullBlocks_shape
  have key : ∀ n ≤ 30, ModelOk (ms n) ∧
      ms n = (fullBlocks.take n).flatten.foldl (Model.step fullLr) fullInit := by
    intro n
    induction n with
    | zero => intro _; exact ⟨h0 ▸ modelOk_of fullInit_ok, by simp [h0]⟩
    | succ n ih =>
      intro hn
      obtain ⟨hmn, hfold⟩ := ih (by omega)
      obtain ⟨henc, hnext⟩ := hblock n (by omega) hmn
      have heq := model_eq_of_enc (modelOk_of (hok n (by omega))).2 hnext.2 henc
      refine ⟨heq ▸ hnext, ?_⟩
      have hlt : n < fullBlocks.length := by omega
      rw [heq, hfold, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
        List.flatten_append, List.foldl_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
        Option.getD_some]
  rw [(key 30 le_rfl).2, ← hlen, List.take_length, hflat, IxAICore.train_eq_foldl_gather]
  rfl

/-- **30 accepted deployed block claims, chained by public IO, end at `IxAICore.train`.** One
shipped block circuit (`blockOnly`, `compiled`, ...) accepts, for every `i < 30`, a claim whose
arguments decode to the model `ms i`, `fullLr` and group `i` of `fullBlocks`, and whose output
decodes to the encoding of `ms (i + 1)`: claim `i`'s public output is claim `i + 1`'s public
model input. With `ms 0` the full configuration's initial model and every later `ms i` passing
the public check `modelOkB`, `ms 30` is the trained model. -/
theorem train_of_deployed_blocks (parity : BlockOnlyParity)
    {blockOnly : Modules.Prepared (IxAIAiur.source.toField F)}
    (shipped : Modules.prepare (IxAIAiur.source.toField F) ["Fixed::train_block"] = .ok blockOnly)
    (compiled : ModulesArtifact blockOnly) (prepared : Physical.Prepared compiled.circuit.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train_block" ∈ blockOnly.entries)
    {ms : ℕ → Model} (h0 : ms 0 = fullInit) (hok : ∀ i < 30, modelOkB (ms (i + 1)) = true)
    {rom : ℕ → WidthROM F} (valid : ∀ i < 30, (rom i).Valid)
    {wires : ℕ → List (WireValue F)} {output : ℕ → WireValue F}
    (signed : ∀ i < 30,
      Circuit.Erasure.Signed compiled.circuit.system ⟨"Fixed::train_block", wires i, output i⟩)
    {root : ℕ → Circuit.Message F}
    (rooted : ∀ i < 30, Depth.erase cfg (root i) =
      Circuit.Erasure.message compiled.circuit.system ⟨"Fixed::train_block", wires i, output i⟩)
    (outside : ∀ i < 30, (root i).channel ∉ cfg.names)
    {rows : ℕ → List (Circuit.WeightedRow F)} (bound : ∀ i < 30, (rows i).length ≤ 2 ^ 39)
    (checked : ∀ i < 30,
      plan.checkMemo (Circuit.Erasure.rawROM (rom i)) (root i) (rows i) = .ok ())
    (arguments : ∀ i < 30, DecodesValues compiled.specialized.program.enums (wires i)
      (entryValues (blockValues (ms i) fullLr (fullBlocks.getD i []))))
    (decoded : ∀ i < 30, (output i).decode compiled.specialized.program.enums =
      some ((encModel (ms (i + 1))).mapAddress (fun _ => 0))) :
    ms 30 = IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig := by
  obtain ⟨hlen, hblks, -⟩ := fullBlocks_shape
  refine train_of_blocks h0 hok fun i hi hmi => ?_
  have hblk : (fullBlocks.getD i []).length = 20 ∧ ∀ b ∈ fullBlocks.getD i [], BatchOk b := by
    have hlt : i < fullBlocks.length := by rw [hlen]; exact hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact hblks _ (List.getElem_mem hlt)
  exact block_sound_deployed parity shipped compiled prepared certified bits plan activated entry
    (valid i hi) fullLr_le hmi hblk.1 hblk.2 (signed i hi) (rooted i hi) (outside i hi)
    (bound i hi) (checked i hi) (arguments i hi) (decoded i hi)

end IxAIStep.Fixed.Blocks
