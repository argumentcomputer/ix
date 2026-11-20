import IxAIRefine.Fixed.Deployed
import IxAIRefine.Fixed.Blocks

/-! # The environment of the combined training certificate

A combined certificate states, in one proof, that this environment typechecks (an IxVM CheckEnv
aggregate), that it contains a binding `b : AiurBinding` and the refinement theorem `b.statement`
names, and that an `aiurExec` aggregate under the program key `b.programKey` accepted
`b.executions` chained calls of `b.entry` from the encoding of the initial model to a model whose
encoding hashes to the certified digest. The certificate binds this file's constants by their
Ixon addresses: `b`'s address fixes the key string and, through its `refinement` field, the
theorem's address, and the theorem's statement fixes the spec (`IxAICore.train`,
`IxAICore.Triage.spec`, `IxAIAiur.fullConfig`) it concludes about.

Run claims are hashed as `aiur_exec` hashes them: `count ‖ H(m₀) ‖ H(mₙ) ‖ data root`, `H` the
BLAKE3 of the little-endian Goldilocks words of a model or of one execution's data. -/

namespace IxAICombined

open IxAIStep.Fixed IxAIStep.Fixed.TrainSpec


/-! ## Chains whose intermediate models are hidden

`train_of_deployed_steps` and `train_of_deployed_blocks` take `hok`, that every intermediate
model passes the public check `modelOkB`, because they identify each claim's integer model with
the previous claim's result through `model_eq_of_enc`, which needs both in range. An aggregated
run publishes only digests of the first and last models, so `hok` cannot be checked. The
variants below need no `hok`: they carry the specification's own models along the chain, which
`step_sound_deployed` and `block_sound_deployed` keep `ModelOk`, and identify claims only by
their field encodings. The conclusion is that the last claim's model encodes like the trained
model; with the final model in range (`modelOkB`, checked once by the verifier) it is the
trained model. -/

section Chain

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Optimized
open IxAIStep.Fixed.Obs IxAIStep.Fixed.Specs IxAIStep.Fixed.TrainSpec IxAIStep.Fixed.Soundness
open IxAIStep.Fixed.Deployed IxAIStep.Fixed.Blocks
open IxAICore (Fx Model)

theorem mapAddress_id {α A : Type} (v : Value α A) : v.mapAddress id = v := by
  cases v with
  | field => simp [Value.mapAddress]
  | ptr => simp [Value.mapAddress]
  | tuple items =>
      simp only [Value.mapAddress, Value.tuple.injEq]
      exact (List.map_congr_left fun item _ => mapAddress_id item).trans (List.map_id _)
  | construct _ _ items =>
      simp only [Value.mapAddress, Value.construct.injEq, true_and]
      exact (List.map_congr_left fun item _ => mapAddress_id item).trans (List.map_id _)
termination_by sizeOf v

theorem mapAddress_comp {α A B C : Type} (f : A → B) (g : B → C) (v : Value α A) :
    (v.mapAddress f).mapAddress g = v.mapAddress (g ∘ f) := by
  cases v with
  | field => simp [Value.mapAddress]
  | ptr => simp [Value.mapAddress]
  | tuple items =>
      simp only [Value.mapAddress, Value.tuple.injEq, List.map_map]
      exact List.map_congr_left fun item _ => mapAddress_comp f g item
  | construct _ _ items =>
      simp only [Value.mapAddress, Value.construct.injEq, true_and, List.map_map]
      exact List.map_congr_left fun item _ => mapAddress_comp f g item
termination_by sizeOf v

/-- Encodings of models carry no addresses, so erasing addresses loses nothing. -/
theorem encModel_eq_of_erased {a b : Model}
    (h : (encModel a).mapAddress (fun _ => (0 : F)) = (encModel b).mapAddress (fun _ => 0)) :
    encModel a = encModel b := by
  have back := congrArg (Value.mapAddress (fun _ : F => (0 : ℕ))) h
  rw [mapAddress_comp, mapAddress_comp,
    Value.mapAddress_free _ (encModel_pointerFree a) _ id,
    Value.mapAddress_free _ (encModel_pointerFree b) _ id, mapAddress_id, mapAddress_id] at back
  exact back

theorem params_eq_of_enc {a b : Model} (h : encModel a = encModel b) :
    IxAIAiur.mat a.w1 = IxAIAiur.mat b.w1 ∧ IxAIAiur.vec a.b1 = IxAIAiur.vec b.b1 ∧
      IxAIAiur.mat a.w2 = IxAIAiur.mat b.w2 ∧ IxAIAiur.vec a.b2 = IxAIAiur.vec b.b2 := by
  rw [encModel_split, encModel_split] at h
  simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using h

/-- **600 accepted deployed step claims, chained by public IO, encode `IxAICore.train`**, with
no hypothesis on the intermediate models. Claim `i`'s arguments decode to the model `ms i` and
its output to the encoding of `ms (i + 1)`; `ms 0` is the initial model. Then `ms 600` encodes,
as data, exactly like the trained model. -/
theorem train_of_deployed_steps_enc (parity : StepOnlyParity)
    {stepOnly : Modules.Prepared (IxAIAiur.source.toField F)}
    (shipped : Modules.prepare (IxAIAiur.source.toField F) ["Fixed::step"] = .ok stepOnly)
    (compiled : ModulesArtifact stepOnly) (prepared : Physical.Prepared compiled.circuit.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::step" ∈ stepOnly.entries)
    {ms : ℕ → Model} (h0 : ms 0 = TrainSpec.fullInit)
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
        IxAIAiur.vec (ms i).b2, TrainSpec.encXs (TrainSpec.fullBatches.getD i []),
        TrainSpec.encTs (TrainSpec.fullBatches.getD i []), fxVal TrainSpec.fullLr]))
    (decoded : ∀ i < 600, (output i).decode compiled.specialized.program.enums =
      some ((encModel (ms (i + 1))).mapAddress (fun _ => 0))) :
    encModel (ms 600) = encModel (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig) ∧
      TrainSpec.ModelOk (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig) := by
  have hlen := fullBatches_ok.1
  have key : ∀ n ≤ 600, encModel (ms n) =
      encModel ((TrainSpec.fullBatches.take n).foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit) ∧
      TrainSpec.ModelOk
        ((TrainSpec.fullBatches.take n).foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by simp [h0], by simpa using TrainSpec.modelOk_of TrainSpec.fullInit_ok⟩
    | succ n ih =>
      intro hn
      obtain ⟨henc, hok⟩ := ih (by omega)
      have hlt : n < TrainSpec.fullBatches.length := by omega
      have hb : TrainSpec.BatchOk (TrainSpec.fullBatches.getD n []) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact fullBatches_ok.2 _ (List.getElem_mem hlt)
      obtain ⟨e1, e2, e3, e4⟩ := params_eq_of_enc henc
      have args := arguments n (by omega)
      rw [e1, e2, e3, e4] at args
      obtain ⟨hout, hnext⟩ := step_sound_deployed parity shipped compiled prepared certified bits
        plan activated entry (valid n (by omega)) TrainSpec.fullLr_le hok hb (signed n (by omega))
        (rooted n (by omega)) (outside n (by omega)) (bound n (by omega)) (checked n (by omega))
        args (decoded n (by omega))
      have hstep : (TrainSpec.fullBatches.take (n + 1)).foldl (Model.step TrainSpec.fullLr)
          TrainSpec.fullInit = ((TrainSpec.fullBatches.take n).foldl (Model.step TrainSpec.fullLr)
            TrainSpec.fullInit).step TrainSpec.fullLr (TrainSpec.fullBatches.getD n []) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.foldl_append,
          List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
          Option.getD_some]
      rw [hstep]
      exact ⟨encModel_eq_of_erased hout, hnext⟩
  have htrain : IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig =
      (TrainSpec.fullBatches.take 600).foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit := by
    rw [← hlen, List.take_length, IxAICore.train_eq_foldl_gather]; rfl
  rw [htrain]
  exact key 600 le_rfl

/-- **30 accepted deployed block claims, chained by public IO, encode `IxAICore.train`**, with
no hypothesis on the intermediate models: `train_of_deployed_blocks` without `hok`. -/
theorem train_of_deployed_blocks_enc (parity : BlockOnlyParity)
    {blockOnly : Modules.Prepared (IxAIAiur.source.toField F)}
    (shipped : Modules.prepare (IxAIAiur.source.toField F) ["Fixed::train_block"] = .ok blockOnly)
    (compiled : ModulesArtifact blockOnly) (prepared : Physical.Prepared compiled.circuit.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train_block" ∈ blockOnly.entries)
    {ms : ℕ → Model} (h0 : ms 0 = TrainSpec.fullInit)
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
      (entryValues (blockValues (ms i) TrainSpec.fullLr (fullBlocks.getD i []))))
    (decoded : ∀ i < 30, (output i).decode compiled.specialized.program.enums =
      some ((encModel (ms (i + 1))).mapAddress (fun _ => 0))) :
    encModel (ms 30) = encModel (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig) ∧
      TrainSpec.ModelOk (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig) := by
  obtain ⟨hlen, hblks, hflat⟩ := fullBlocks_shape
  have key : ∀ n ≤ 30, encModel (ms n) =
      encModel ((fullBlocks.take n).flatten.foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit) ∧
      TrainSpec.ModelOk
        ((fullBlocks.take n).flatten.foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by simp [h0], by simpa using TrainSpec.modelOk_of TrainSpec.fullInit_ok⟩
    | succ n ih =>
      intro hn
      obtain ⟨henc, hok⟩ := ih (by omega)
      have hlt : n < fullBlocks.length := by omega
      have hblk : (fullBlocks.getD n []).length = 20 ∧
          ∀ b ∈ fullBlocks.getD n [], TrainSpec.BatchOk b := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact hblks _ (List.getElem_mem hlt)
      obtain ⟨e1, e2, e3, e4⟩ := params_eq_of_enc henc
      have args := arguments n (by omega)
      simp only [blockValues] at args
      rw [e1, e2, e3, e4] at args
      obtain ⟨hout, hnext⟩ := block_sound_deployed parity shipped compiled prepared certified bits
        plan activated entry (valid n (by omega)) TrainSpec.fullLr_le hok hblk.1 hblk.2
        (signed n (by omega)) (rooted n (by omega)) (outside n (by omega)) (bound n (by omega))
        (checked n (by omega)) args (decoded n (by omega))
      have hstep : (fullBlocks.take (n + 1)).flatten.foldl (Model.step TrainSpec.fullLr)
          TrainSpec.fullInit = (fullBlocks.getD n []).foldl (Model.step TrainSpec.fullLr)
            ((fullBlocks.take n).flatten.foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.flatten_append, List.foldl_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
          Option.getD_some]
      rw [hstep]
      exact ⟨encModel_eq_of_erased hout, hnext⟩
  have htrain : IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig =
      (fullBlocks.take 30).flatten.foldl (Model.step TrainSpec.fullLr) TrainSpec.fullInit := by
    rw [← hlen, List.take_length, hflat, IxAICore.train_eq_foldl_gather]; rfl
  rw [htrain]
  exact key 30 le_rfl

/-- A model that encodes like a `ModelOk` model and passes `modelOkB` is that model. -/
theorem eq_of_encModel_eq {m m' : Model} (hm : TrainSpec.modelOkB m = true)
    (hm' : TrainSpec.ModelOk m') (h : encModel m = encModel m') : m = m' :=
  model_eq_of_enc (TrainSpec.modelOk_of hm).2 hm'.2 (by rw [h])

end Chain

/-- An Aiur program whose accepted runs a refinement theorem of this environment turns into a
Lean statement. -/
structure AiurBinding where
  /-- BLAKE3 of the program's batch verifying key (its `stark-key` bytes), lowercase hex. -/
  programKey : String
  /-- The program entry every aggregated claim calls. -/
  entry : String
  /-- That entry's claim index: word 1 of each of its claims. -/
  entryIndex : Nat
  /-- How many chained executions make up the run. -/
  executions : Nat
  /-- What accepted runs of the program imply. -/
  statement : Prop
  refinement : statement

/-- The full run as 600 `Fixed::step` executions, each one SGD step on one batch.
`train_of_deployed_steps_enc` assumes `Deployed.StepOnlyParity`, checked by evaluation. -/
def stepRun : AiurBinding where
  programKey := "425433fea85958a1dae08e05665035cbdd1124f304f191370eedcb3647b72c75"
  entry := "Fixed::step"
  entryIndex := 0
  executions := 600
  statement := type_of% @train_of_deployed_steps_enc
  refinement := @train_of_deployed_steps_enc

/-- The full run as 30 `Fixed::train_block` executions of 20 steps each.
`train_of_deployed_blocks_enc` assumes `Blocks.BlockOnlyParity`, checked by evaluation. -/
def blockRun : AiurBinding where
  programKey := "d46caf1e358f9e28744a1163b2d25b2ea4de331870fcc78e1625119edfa1da58"
  entry := "Fixed::train_block"
  entryIndex := 0
  executions := 30
  statement := type_of% @train_of_deployed_blocks_enc
  refinement := @train_of_deployed_blocks_enc

open IxAICore IxAICore.Triage in
/-- The deployed gate never publishes a false formula, whatever the weights. -/
theorem publish_sound (g : Gate) (m : Model) (f : Formula) (h : act g m f = .publish) :
    f.valid = true :=
  act_publish_sound g m f h

open IxAICore IxAICore.Triage in
/-- The deployed gate publishes only formulas its model is confident about, whatever the
weights. -/
theorem publish_confident (g : Gate) (m : Model) (f : Formula) (h : act g m f = .publish) :
    confidence m f ≥ g.threshold :=
  act_publish_confident g m f h

open IxAICore IxAICore.Triage in
/-- The deployed gate defers exactly when its model is not confident, whatever the weights. -/
theorem defer_iff (g : Gate) (m : Model) (f : Formula) :
    act g m f = .defer ↔ confidence m f < g.threshold :=
  act_defer_iff g m f

end IxAICombined
