import IxAIRefine.Fixed.TrainSpec
import Aiur.Optimized.Observed

/-! # From an accepted trace to `IxAICore`

The backend's observed headline
(`Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed`)
turns acceptance of the memo checker over the depth-certified, grouped and activated circuits of
a compilation of `IxAIStep.Fixed.source` into an observed source derivation (`ObsFn`) of the
entry, whose value the trace's decoded ROM represents as the claimed result. The functional
specs then fix that value:

* `train_sound`: an accepted claim of `Fixed::train` on the full configuration's arguments
  represents `encModel (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig)`
  (`TrainSpec.train_refines`).
* `step_sound`: an accepted claim of `Fixed::step` on a `ModelOk` model, a `BatchOk` batch and
  `|lr| ≤ 2^8` represents `encModel (m.step lr b)`, and the next model is again `ModelOk`
  (`TrainSpec.step_refines`).

`train_sound_eq` and `step_sound_eq` state the same as equalities of the decoded output, since
`encModel` is pointer-free (`represents_eq_of_pointerFree`). `train_of_steps` chains 600 step
claims, each output identified with the next claim's model, to `IxAICore.train`.

Both cover every function the entry reaches, `Fixed::bound` included: its spec `bound_spec`
enters through `upd_spec`, which `step_spec` uses for every parameter a step returns.

What these statements take as hypotheses, and so leave to the prover's side: the accepted rows
(`checked`, with `rows.length ≤ 2^39`), which the Audit module's trust boundary obtains from an
accepting multi-stark proof; the root claim's encoding (`signed`, `rooted`, `outside`,
`arguments`, `decoded`); and that the circuits are a compilation of `IxAIStep.Fixed.source`
(`compiled`, `prepared`, `certified`, `plan`, `activated`), which `IxAIRefine.Check` checks by
evaluation against `Modules.prepare` of the host's source. -/

namespace IxAIStep.Fixed.Soundness

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Optimized
open IxAIStep.Fixed.Obs IxAIStep.Fixed.Specs IxAIStep.Fixed.TrainSpec
open IxAICore (Fx Model)

/-- **An accepted `Fixed::train` claim is `IxAICore.train`.** If the memo checker accepts, over
the depth-certified grouped circuits of a compilation of `IxAIStep.Fixed.source` with entry
`Fixed::train`, a root claim whose arguments decode to the full configuration's initial model,
learning rate and gathered batches and whose output decodes to `result`, then `result`
represents, in the trace's decoded ROM, the encoding of the specification's trained model. -/
theorem train_sound {entries : List String}
    {specialized : Generic.Specialized IxAIStep.Fixed.source entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train" ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Circuit.Erasure.Signed compiled.system ⟨"Fixed::train", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.system ⟨"Fixed::train", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues (trainValues (IxAIAiur.mat fullInit.w1) (IxAIAiur.vec fullInit.b1)
        (IxAIAiur.mat fullInit.w2) (IxAIAiur.vec fullInit.b2) fullLr fullBatches)))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ heap, Represents (compiled.traceROM rom) heap
      (encModel (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig)) result := by
  obtain ⟨value, heap, calls, ev, related, -⟩ :=
    prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed compiled certified bits
      plan activated entry valid signed rooted outside bound checked arguments decoded
  exact ⟨heap, train_refines ev ▸ related⟩

/-- **An accepted `Fixed::step` claim is `Model.step`.** The same as `train_sound` for one step
on a `ModelOk` model `m`, a `BatchOk` batch `b` and `|lr| ≤ 2^8`: `result` represents
`encModel (m.step lr b)`, and that model is again `ModelOk`. -/
theorem step_sound {entries : List String}
    {specialized : Generic.Specialized IxAIStep.Fixed.source entries}
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
    (∃ heap, Represents (compiled.traceROM rom) heap (encModel (m.step lr b)) result) ∧
      ModelOk (m.step lr b) := by
  obtain ⟨value, heap, calls, ev, related, -⟩ :=
    prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed compiled certified bits
      plan activated entry valid signed rooted outside bound checked arguments decoded
  obtain ⟨hv, hm'⟩ := step_refines hlr hm hb (encModel_split m) ev
  exact ⟨⟨heap, hv ▸ related⟩, hm'⟩

/-! ## The decoded result is the specification's model

`encModel` is built from field values and tuples only, so a representation of it relates no
addresses and the decoded result is the model's encoding as data: the value `entryValues`
assigns it, the same form in which a step's arguments are stated. -/

/-- A representation of a pointer-free source value is that value with its (absent) addresses
mapped to `0`. -/
theorem represents_eq_of_pointerFree {rom : Aiur.ROM F} {heap : Aiur.Heap F}
    {source : SourceValue F} {target : Value F} (related : Aiur.Represents rom heap source target) :
    source.pointerFree = true → target = source.mapAddress (fun _ => (0 : F)) := by
  induction related using Aiur.Represents.rec
    (motive_2 := fun sources targets _ =>
      (∀ value ∈ sources, value.pointerFree = true) →
        targets = sources.map (Value.mapAddress (fun _ => (0 : F)))) with
  | field => intro _; simp [Value.mapAddress]
  | tuple _ ih | construct _ ih =>
      intro free
      simp only [Value.mapAddress, Value.tuple.injEq, Value.construct.injEq, true_and]
      apply ih
      simpa [Value.pointerFree, Value.type, Ty.pointerFree] using free
  | ptr => simp [Value.pointerFree, Value.type, Ty.pointerFree]
  | nil => rfl
  | cons _ _ h t =>
      rename_i free
      simp only [List.map_cons]
      exact congrArg₂ List.cons (h (free _ (by simp))) (t (fun v mem => free v (by simp [mem])))

theorem encVec_pointerFree (xs : List Fx) : (encVec xs).pointerFree = true := by
  simp [encVec, fxVal, Value.pointerFree]

theorem encMat_pointerFree (xss : List (List Fx)) : (encMat xss).pointerFree = true := by
  simp only [encMat, Value.pointerFree, List.map_map, List.all_eq_true, List.mem_map,
    Function.comp_apply, id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun xs _ => encVec_pointerFree xs

theorem encModel_pointerFree (m : Model) : (encModel m).pointerFree = true := by
  simp [encModel, Value.pointerFree, encVec_pointerFree, encMat_pointerFree]

/-- **An accepted `Fixed::train` claim outputs `IxAICore.train`, as data.** Under the
hypotheses of `train_sound`, the decoded output `result` is the encoding of the specification's
trained model. -/
theorem train_sound_eq {entries : List String}
    {specialized : Generic.Specialized IxAIStep.Fixed.source entries}
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    {id : String → Except String ℕ} {cfg : Depth.Config}
    (certified : Depth.Certified cfg prepared.system) (bits : cfg.bits ≤ 24)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id)
    (activated : plan.WellFormedActivation)
    (entry : "Fixed::train" ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Circuit.Erasure.Signed compiled.system ⟨"Fixed::train", wires, output⟩)
    {root : Circuit.Message F}
    (rooted : Depth.erase cfg root =
      Circuit.Erasure.message compiled.system ⟨"Fixed::train", wires, output⟩)
    (outside : root.channel ∉ cfg.names)
    {rows : List (Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues (trainValues (IxAIAiur.mat fullInit.w1) (IxAIAiur.vec fullInit.b1)
        (IxAIAiur.mat fullInit.w2) (IxAIAiur.vec fullInit.b2) fullLr fullBatches)))
    (decoded : output.decode specialized.program.enums = some result) :
    result = (encModel (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig)).mapAddress
      (fun _ => 0) := by
  obtain ⟨heap, related⟩ := train_sound compiled prepared certified bits plan activated entry
    valid signed rooted outside bound checked arguments decoded
  exact represents_eq_of_pointerFree related (encModel_pointerFree _)

/-- **An accepted `Fixed::step` claim outputs `Model.step`, as data.** Under the hypotheses of
`step_sound`, the decoded output is the encoding of `m.step lr b`, which is again `ModelOk`. -/
theorem step_sound_eq {entries : List String}
    {specialized : Generic.Specialized IxAIStep.Fixed.source entries}
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
  obtain ⟨⟨heap, related⟩, hm'⟩ := step_sound compiled prepared certified bits plan activated
    entry valid hlr hm hb signed rooted outside bound checked arguments decoded
  exact ⟨represents_eq_of_pointerFree related (encModel_pointerFree _), hm'⟩

/-! ## Chaining step claims

The deployed run proves the 600 steps separately. `train_of_steps` is the chain statement: if
the models `ms i` a chain of step claims is stated over start at the full configuration's
initial model and each step's output, as data, is the next claim's model, then the last model
is `IxAICore.train`. The per-step hypothesis is what `step_sound_eq` gives for claim `i` once
its output is identified with the encoding of `ms (i + 1)`. Encodings of parameters below
`2^13` are injective, so equal encodings are equal models. -/

theorem map_inj_of {α β : Type} {f : α → β} :
    ∀ {l₁ l₂ : List α}, (∀ a ∈ l₁, ∀ b ∈ l₂, f a = f b → a = b) → l₁.map f = l₂.map f →
      l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, inj, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [inj a (by simp) b (by simp) h.1,
      map_inj_of (fun x hx y hy => inj x (by simp [hx]) y (by simp [hy])) h.2]

theorem fx_eq_of_enc {a b : Fx} (ha : SmallW a.raw) (hb : SmallW b.raw)
    (h : (fxVal a).mapAddress (fun _ => (0 : F)) = (fxVal b).mapAddress (fun _ => 0)) :
    a = b := by
  simp only [fxVal, Value.mapAddress, Value.field.injEq] at h
  have hab : |a.raw - b.raw| < 18446744069414584321 := by
    have ha' := abs_lt.mp ha
    have hb' := abs_lt.mp hb
    rw [abs_lt]; constructor <;> omega
  cases a; cases b
  exact congrArg Fx.mk (int_eq_of_cast_eq hab h)

theorem vec_eq_of_enc {xs ys : List Fx} (hx : VecW xs) (hy : VecW ys)
    (h : (encVec xs).mapAddress (fun _ => (0 : F)) = (encVec ys).mapAddress (fun _ => 0)) :
    xs = ys := by
  simp only [encVec, Value.mapAddress, Value.tuple.injEq, List.map_map] at h
  exact map_inj_of (fun a ha b hb e => fx_eq_of_enc (hx a ha) (hy b hb) e) h

theorem mat_eq_of_enc {xss yss : List (List Fx)} (hx : MatW xss) (hy : MatW yss)
    (h : (encMat xss).mapAddress (fun _ => (0 : F)) = (encMat yss).mapAddress (fun _ => 0)) :
    xss = yss := by
  simp only [encMat, Value.mapAddress, Value.tuple.injEq, List.map_map] at h
  exact map_inj_of (fun a ha b hb e => vec_eq_of_enc (hx a ha) (hy b hb) e) h

/-- Two models with parameters below `2^13` and equal encodings are equal. -/
theorem model_eq_of_enc {m m' : Model} (hm : ModelW m) (hm' : ModelW m')
    (h : (encModel m).mapAddress (fun _ => (0 : F)) = (encModel m').mapAddress (fun _ => 0)) :
    m = m' := by
  simp only [encModel, Value.mapAddress, Value.tuple.injEq, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases m; cases m'
  obtain ⟨w1, b1, w2, b2⟩ := hm
  obtain ⟨w1', b1', w2', b2'⟩ := hm'
  simp only [Model.mk.injEq]
  exact ⟨mat_eq_of_enc w1 w1' h1, vec_eq_of_enc b1 b1' h2, mat_eq_of_enc w2 w2' h3,
    vec_eq_of_enc b2 b2' h4⟩

/-- The full configuration's gathered batches: 600 batches, each `BatchOk`. -/
theorem fullBatches_ok : fullBatches.length = 600 ∧ ∀ b ∈ fullBatches, BatchOk b :=
  ⟨by rw [fullBatches, IxAICore.gather, List.length_map]; exact fullSchedule_shape.1,
    gather_ok fullExamples_ok fullDefault_ok fullSchedule_shape.2⟩

/-- **A chain of 600 step claims ends at `IxAICore.train`.** `ms i` is the model step claim `i`
is stated over. If `ms 0` is the full configuration's initial model, every later `ms i` passes
the public check `modelOkB`, and for every `i < 600` whose model is `ModelOk` the output of
step `i` on batch `i` of `fullBatches` with `fullLr` is, as data, the encoding of `ms (i + 1)`
and a `ModelOk` model (the conclusion of `step_sound_eq`, with the output identified with the
next claim's model), then `ms 600` is the trained model. -/
theorem train_of_steps {ms : ℕ → Model} (h0 : ms 0 = fullInit)
    (hok : ∀ i < 600, modelOkB (ms (i + 1)) = true)
    (hstep : ∀ i < 600, ModelOk (ms i) →
      (encModel (ms (i + 1))).mapAddress (fun _ => (0 : F)) =
          (encModel ((ms i).step fullLr (fullBatches.getD i []))).mapAddress (fun _ => 0) ∧
        ModelOk ((ms i).step fullLr (fullBatches.getD i []))) :
    ms 600 = IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig := by
  have hlen := fullBatches_ok.1
  have key : ∀ n ≤ 600, ModelOk (ms n) ∧
      ms n = (fullBatches.take n).foldl (Model.step fullLr) fullInit := by
    intro n
    induction n with
    | zero => intro _; exact ⟨h0 ▸ modelOk_of fullInit_ok, by simp [h0]⟩
    | succ n ih =>
      intro hn
      obtain ⟨hmn, hfold⟩ := ih (by omega)
      obtain ⟨henc, hnext⟩ := hstep n (by omega) hmn
      have heq := model_eq_of_enc (modelOk_of (hok n (by omega))).2 hnext.2 henc
      refine ⟨heq ▸ hnext, ?_⟩
      have hlt : n < fullBatches.length := by omega
      rw [heq, hfold, List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [(key 600 le_rfl).2, ← hlen, List.take_length, IxAICore.train_eq_foldl_gather]
  rfl

end IxAIStep.Fixed.Soundness
