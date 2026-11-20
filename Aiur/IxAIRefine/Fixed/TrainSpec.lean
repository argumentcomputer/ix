import IxAIRefine.Fixed.Magnitudes
import IxAICore.Gather

/-! # `Fixed::train` refines `IxAICore.train`

`Fixed::train` takes an initial model, a learning rate and 600 batches already gathered from the
training set, as 30 groups (`train_block`) of 20 batches, and folds `Fixed::step` over them in
order. This module proves that it computes the specification's training run.

* `train_spec`: every observed derivation of `Fixed::train` on an encoded model `m0`, `lr` and
  600 batches returns `encModel (batches.foldl (Model.step lr) m0)`, provided `m0` has the
  program's shapes and parameters below `2^13` (`ModelOk`), every batch has the program's
  shapes and inputs and targets at most `2^12` (`BatchOk`), and `|lr| ≤ 2^8`. Nothing is
  assumed of the intermediate models: `Fixed::upd` range-checks every parameter a step returns,
  so each step's result is again `ModelOk`.
* `train_refines_gather`: the same for batches `gather examples schedule d`, with the hypotheses
  stated as Boolean checks of the public inputs only: the initial model, the examples, the
  out-of-range default `d`, the schedule's shape, and `lr`.
* `train_refines`: for the full configuration, with no hypotheses, every observed derivation
  returns the encoding of `IxAICore.train IxAICore.Triage.spec fullConfig`. The checks of the
  initial model and of the default example are decided by evaluation; those of the 400 examples
  and the schedule's shape are proved for every draw of the random generator
  (`fullExamples_ok`, `fullSchedule_shape`), and `IxAICore.train_eq_foldl_gather` turns the fold into
  `IxAICore.train`.

The proof has three layers:

1. `step_refines` restates `step_spec` in the form the fold uses, deriving `step_spec`'s
   magnitude hypothesis from `ModelOk`, `BatchOk` and `lr` (`stepBounds_of_weights`) and
   returning `ModelOk` of the next model.
2. `StepChain` records a sequence of observed `Fixed::step` derivations, each one's result the
   next one's model. `chain_spec` proves by induction over the batches that a chain from
   `encModel m` ends at `encModel (bs.foldl (Model.step lr) m)`.
3. `train_block_chain` and `train_blocks` read such a chain off the generated path lemmas
   `«Fixed::train_block».obs` and `«Fixed::train».obs`, and `BlockChain.steps` joins the 30
   block chains into one chain over all 600 batches.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxAIStep.Fixed.TrainSpec

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxAIStep.Fixed.Obs IxAIStep.Fixed.Specs
open IxAICore (Fx Model)

/-- A batch: pairs of inputs and one-hot targets. -/
abbrev Batch := List (List Fx × List Fx)

/-! ## Encodings

The same values `IxAIAiur.trainArgs` passes, so the statements below are about the host's
actual arguments. -/

/-- A batch's inputs as a `[[Field; 8]; 20]` argument. -/
def encXs (b : Batch) : SourceValue F := IxAIAiur.mat (b.map (·.1))

/-- A batch's targets as a `[[Field; 11]; 20]` argument. -/
def encTs (b : Batch) : SourceValue F := IxAIAiur.mat (b.map (·.2))

/-- The inputs of a group of 20 batches, the argument `xs` of `Fixed::train_block`. -/
def encBlockXs (blk : List Batch) : SourceValue F := .tuple (blk.map encXs)

/-- The targets of a group of 20 batches, the argument `ts` of `Fixed::train_block`. -/
def encBlockTs (blk : List Batch) : SourceValue F := .tuple (blk.map encTs)

/-- The inputs of 30 groups, the argument `xs` of `Fixed::train`. -/
def encTrainXs (blks : List (List Batch)) : SourceValue F := .tuple (blks.map encBlockXs)

/-- The targets of 30 groups, the argument `ts` of `Fixed::train`. -/
def encTrainTs (blks : List (List Batch)) : SourceValue F := .tuple (blks.map encBlockTs)

/-- The arguments of `Fixed::train`: the model's four parameters, `lr`, and the batches in
groups of 20, exactly as `IxAIAiur.trainArgs` builds them. -/
abbrev trainValues (w1 b1 w2 b2 : SourceValue F) (lr : Fx) (batches : List Batch) :
    List (SourceValue F) :=
  [w1, b1, w2, b2, fxVal lr, encTrainXs (IxAIAiur.blocks20 batches),
    encTrainTs (IxAIAiur.blocks20 batches)]

/-! ## The step hypothesis

`step_spec` (`IxAIRefine.Fixed.StepSpecs`) takes the model's and the batch's shapes as six and
two separate hypotheses, the parameter bound `ModelW m`, and the magnitudes `StepBounds`.
`ModelDims` and `BatchDims` bundle the shapes; `stepBounds_of_weights` derives the magnitudes
from `ModelW`, `BatchSmall` and `|lr| ≤ 2^8`. `step_spec` and `step_dims` return the shapes and
`ModelW` of the next model, so `ModelOk` propagates along the run and only `BatchOk` is asked of
every step. `encModel m` is `.tuple [mat m.w1, vec m.b1, mat m.w2, vec m.b2]`
(`IxAIAiur.modelValue m`) by `rfl`. -/

/-- The model has the program's dimensions: 16 hidden units over 8 features, 11 outputs. -/
def ModelDims (m : Model) : Prop :=
  m.w1.length = 16 ∧ (∀ row ∈ m.w1, row.length = 8) ∧ m.b1.length = 16 ∧
    m.w2.length = 11 ∧ (∀ row ∈ m.w2, row.length = 16) ∧ m.b2.length = 11

/-- The batch has the program's dimensions: 20 examples of 8 inputs and 11 targets. -/
def BatchDims (b : Batch) : Prop :=
  b.length = 20 ∧ ∀ e ∈ b, e.1.length = 8 ∧ e.2.length = 11

/-- Every input and target of the batch is at most `2^12` in magnitude. -/
def BatchSmall (b : Batch) : Prop := ∀ e ∈ b, AllLe 4096 e.1 ∧ AllLe 4096 e.2

/-- What every model of the run satisfies: the program's shapes, parameters below `2^13`. -/
def ModelOk (m : Model) : Prop := ModelDims m ∧ ModelW m

/-- What every batch must satisfy: the program's shapes, inputs and targets at most `2^12`. -/
def BatchOk (b : Batch) : Prop := BatchDims b ∧ BatchSmall b

theorem encModel_split (m : Model) :
    encModel m = .tuple [IxAIAiur.mat m.w1, IxAIAiur.vec m.b1, IxAIAiur.mat m.w2,
      IxAIAiur.vec m.b2] := by
  first | rfl | simp [encModel, IxAIAiur.mat, IxAIAiur.vec, fxVal_eq_fx]

/-- **One observed `Fixed::step` is `Model.step`**, for a model given by its four encoded
parameters, and the next model is again `ModelOk`. -/
theorem step_refines {lr : Fx} (hlr : |lr.raw| ≤ 256) {m : Model} {b : Batch}
    (hm : ModelOk m) (hb : BatchOk b)
    {w1 b1 w2 b2 v : SourceValue F} (hmv : encModel m = .tuple [w1, b1, w2, b2])
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fixed::step" [w1, b1, w2, b2, encXs b, encTs b, fxVal lr] h v h' cs) :
    v = encModel (m.step lr b) ∧ ModelOk (m.step lr b) := by
  rw [encModel_split] at hmv
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true] at hmv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hmv
  obtain ⟨⟨hw1, hw1r, hb1, hw2, hw2r, hb2⟩, hW⟩ := hm
  obtain ⟨⟨hn, hex⟩, hsmall⟩ := hb
  have hbd := stepBounds_of_weights hw1r hw2 hw2r hn hW hsmall hlr
  obtain ⟨hv, hW'⟩ := step_spec hw1 hw1r hb1 hw2 hw2r hb2 hn hex hW hbd ev
  exact ⟨hv, step_dims hw1 hw1r hb1 hw2 hw2r hb2 hn, hW'⟩

/-! ## Chains of steps -/

/-- Observed derivations of `Fixed::step` threaded through a list of batches: each starts from
the previous one's result, the first from `v`, and the last returns `r`. -/
inductive StepChain (lr : SourceValue F) : SourceValue F → List Batch → SourceValue F → Prop
  | nil {v : SourceValue F} : StepChain lr v [] v
  | cons {w1 b1 w2 b2 v r : SourceValue F} {b : Batch} {bs : List Batch} {h h' : Heap F}
      {cs : List (Call F)}
      (ev : ObsFn W "Fixed::step" [w1, b1, w2, b2, encXs b, encTs b, lr] h v h' cs)
      (rest : StepChain lr v bs r) :
      StepChain lr (.tuple [w1, b1, w2, b2]) (b :: bs) r

theorem StepChain.append {lr v u r : SourceValue F} {bs cs : List Batch}
    (h1 : StepChain lr v bs u) (h2 : StepChain lr u cs r) : StepChain lr v (bs ++ cs) r := by
  revert h2
  induction h1 with
  | nil => intro h2; rw [List.nil_append]; exact h2
  | cons ev _ ih => intro h2; rw [List.cons_append]; exact StepChain.cons ev (ih h2)

/-- **A chain of observed steps is the fold of `Model.step`**, by induction over the batches. -/
theorem chain_spec {lr : Fx} (hlr : |lr.raw| ≤ 256) {bs : List Batch}
    (hbs : ∀ b ∈ bs, BatchOk b) :
    ∀ {m : Model} {v r : SourceValue F}, encModel m = v → StepChain (fxVal lr) v bs r →
      ModelOk m → r = encModel (bs.foldl (Model.step lr) m) := by
  induction bs with
  | nil =>
    intro m v r hv hc _
    cases hc
    rw [List.foldl_nil]
    exact hv.symm
  | cons b bs ih =>
    intro m v r hv hc hm
    cases hc with
    | cons ev rest =>
      obtain ⟨hstep, hm'⟩ := step_refines hlr hm (hbs b (by simp)) hv ev
      rw [List.foldl_cons]
      exact ih (fun b' hb' => hbs b' (by simp [hb'])) hstep.symm rest hm'

/-! ## Reading the chain off `train_block` and `train` -/

/-- Observed derivations of `Fixed::train_block` threaded through groups of batches. -/
inductive BlockChain (lr : SourceValue F) :
    SourceValue F → List (List Batch) → SourceValue F → Prop
  | nil {v : SourceValue F} : BlockChain lr v [] v
  | cons {w1 b1 w2 b2 v r : SourceValue F} {blk : List Batch} {blks : List (List Batch)}
      {h h' : Heap F} {cs : List (Call F)}
      (ev : ObsFn W "Fixed::train_block" [w1, b1, w2, b2, lr, encBlockXs blk, encBlockTs blk]
        h v h' cs)
      (rest : BlockChain lr v blks r) :
      BlockChain lr (.tuple [w1, b1, w2, b2]) (blk :: blks) r

/-- A list of length 30 is a literal of 30 elements. -/
theorem blocks_eq30 {α : Type} {l : List α} (h : l.length = 30) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
      x24 x25 x26 x27 x28 x29,
      l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
        x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ |
      ⟨x8, _ | ⟨x9, _ | ⟨x10, _ | ⟨x11, _ | ⟨x12, _ | ⟨x13, _ | ⟨x14, _ | ⟨x15, _ | ⟨x16, _ |
      ⟨x17, _ | ⟨x18, _ | ⟨x19, _ | ⟨x20, _ | ⟨x21, _ | ⟨x22, _ | ⟨x23, _ | ⟨x24, _ | ⟨x25,
      _ | ⟨x26, _ | ⟨x27, _ | ⟨x28, _ | ⟨x29, _ | ⟨x30, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h <;> omega)

/-- **`Fixed::train_block` is a chain of 20 steps.** -/
theorem train_block_chain {lr w1 b1 w2 b2 r : SourceValue F} {blk : List Batch}
    (hlen : blk.length = 20) {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fixed::train_block" [w1, b1, w2, b2, lr, encBlockXs blk, encBlockTs blk]
      h r h' cs) :
    StepChain lr (.tuple [w1, b1, w2, b2]) blk r := by
  obtain ⟨b0, b1', b2', b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
    b18, b19, rfl⟩ := IxAIStep.Fixed.Specs.list_eq20 hlen
  -- The one path of `«Fixed::train_block».obs` carries `xs = .tuple [x0, …, x19]`,
  -- `ts = .tuple [t0, …, t19]` and the 20 `Fixed::step` derivations, each on the previous
  -- one's result tuple. The proof uses no generated names: it splits the pattern equations,
  -- substitutes, and picks each step derivation by its arguments.
  cases «Fixed::train_block».obs ev
  simp only [encBlockXs, encBlockTs, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq,
    List.cons.injEq, and_true] at *
  casesm* _ ∧ _
  subst_vars
  iterate 20 (refine StepChain.cons (by assumption) ?_)
  exact StepChain.nil

/-- **`Fixed::train` is a chain of 30 blocks.** -/
theorem train_blocks {lr w1 b1 w2 b2 r : SourceValue F} {blks : List (List Batch)}
    (hlen : blks.length = 30) {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fixed::train" [w1, b1, w2, b2, lr, encTrainXs blks, encTrainTs blks]
      h r h' cs) :
    BlockChain lr (.tuple [w1, b1, w2, b2]) blks r := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
    k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, rfl⟩ := blocks_eq30 hlen
  -- As in `train_block_chain`, with the 30 `Fixed::train_block` derivations.
  cases «Fixed::train».obs ev
  simp only [encTrainXs, encTrainTs, List.map_cons, List.map_nil, Aiur.Value.tuple.injEq,
    List.cons.injEq, and_true] at *
  casesm* _ ∧ _
  subst_vars
  iterate 30 (refine BlockChain.cons (by assumption) ?_)
  exact BlockChain.nil

/-- The block chains of `train` join into one chain over every batch. -/
theorem BlockChain.steps {lr v r : SourceValue F} {blks : List (List Batch)}
    (hc : BlockChain lr v blks r) (hlen : ∀ blk ∈ blks, blk.length = 20) :
    StepChain lr v blks.flatten r := by
  revert hlen
  induction hc with
  | nil => intro _; exact StepChain.nil
  | cons ev _ ih =>
    intro hlen
    rw [List.flatten_cons]
    exact (train_block_chain (hlen _ (by simp)) ev).append
      (ih fun blk hb => hlen blk (by simp [hb]))

/-! ## Groups of 20 -/

theorem chunk20_flatten {α : Type} (fuel : Nat) (l : List α) (hl : l.length ≤ 20 * fuel) :
    (IxAICore.chunk 20 l fuel).flatten = l := by
  induction fuel generalizing l with
  | zero =>
    cases l with
    | nil => rfl
    | cons a l => simp at hl
  | succ fuel ih =>
    simp only [IxAICore.chunk]
    split
    · next he =>
      cases l with
      | nil => rfl
      | cons a l => simp at he
    · rw [List.flatten_cons, ih (l.drop 20) (by simp only [List.length_drop]; omega),
        List.take_append_drop]

theorem chunk20_shape {α : Type} (fuel n : Nat) (l : List α) (hl : l.length = 20 * n)
    (hn : n ≤ fuel) :
    (IxAICore.chunk 20 l fuel).length = n ∧ ∀ blk ∈ IxAICore.chunk 20 l fuel, blk.length = 20 := by
  induction fuel generalizing n l with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    cases l with
    | nil => exact ⟨rfl, fun blk hb => by simp [IxAICore.chunk] at hb⟩
    | cons a l => simp at hl
  | succ fuel ih =>
    simp only [IxAICore.chunk]
    split
    · next he =>
      cases l with
      | nil =>
        have hn0 : n = 0 := by simp only [List.length_nil] at hl; omega
        subst hn0
        exact ⟨rfl, fun blk hb => by simp at hb⟩
      | cons a l => simp at he
    · next he =>
      cases n with
      | zero =>
        cases l with
        | nil => simp at he
        | cons a l => simp at hl
      | succ n =>
        obtain ⟨hlen, hall⟩ := ih (n := n) (l := l.drop 20)
          (by simp only [List.length_drop]; omega) (by omega)
        refine ⟨by simp only [List.length_cons, hlen], ?_⟩
        intro blk hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp only [List.length_take]; omega
        · exact hall blk hb

/-! ## Training -/

/-- **`Fixed::train` folds `Model.step` over its batches.** An observed derivation of
`Fixed::train` on the encoded model `m0`, `lr` and 600 batches returns the encoding of
`batches.foldl (Model.step lr) m0`, when `m0` is `ModelOk`, every batch is `BatchOk` and
`|lr| ≤ 2^8`. -/
theorem train_spec {lr : Fx} (hlr : |lr.raw| ≤ 256) {m0 : Model} {batches : List Batch}
    (hlen : batches.length = 600) (hm0 : ModelOk m0) (hbs : ∀ b ∈ batches, BatchOk b)
    {w1 b1 w2 b2 : SourceValue F} (hm : encModel m0 = .tuple [w1, b1, w2, b2])
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::train" (trainValues w1 b1 w2 b2 lr batches) h r h' calls) :
    r = encModel (batches.foldl (Model.step lr) m0) := by
  obtain ⟨h30, h20⟩ := chunk20_shape batches.length 30 batches (by omega) (by omega)
  have hflat := chunk20_flatten batches.length batches (by omega)
  have hb : BlockChain (fxVal lr) (.tuple [w1, b1, w2, b2])
      (IxAICore.chunk 20 batches batches.length) r :=
    train_blocks h30 ev
  have hs := hb.steps h20
  rw [hflat] at hs
  exact chain_spec hlr hbs hm hs hm0

/-! ## Checks of the public inputs

Boolean forms of `ModelOk` and of one example's part of `BatchOk`, cheap enough to decide by
evaluation on the full configuration's initial model and examples. -/

/-- A parameter in the range `ModelW` asks for. -/
def paramB (a : Fx) : Bool := decide (-8191 ≤ a.raw) && decide (a.raw ≤ 8191)

/-- An input or target in the range `BatchSmall` asks for. -/
def inputB (a : Fx) : Bool := decide (-4096 ≤ a.raw) && decide (a.raw ≤ 4096)

/-- Decides `ModelOk`. -/
def modelOkB (m : Model) : Bool :=
  m.w1.length == 16 && m.w1.all (fun r => r.length == 8 && r.all paramB) &&
  m.b1.length == 16 && m.b1.all paramB &&
  m.w2.length == 11 && m.w2.all (fun r => r.length == 16 && r.all paramB) &&
  m.b2.length == 11 && m.b2.all paramB

/-- One example: 8 inputs and 11 targets, all at most `2^12` in magnitude. -/
def exampleOkB (e : List Fx × List Fx) : Bool :=
  e.1.length == 8 && e.2.length == 11 && e.1.all inputB && e.2.all inputB

theorem vecW_of {l : List Fx} (h : l.all paramB = true) : VecW l := by
  intro a ha
  have h1 := List.all_eq_true.mp h a ha
  simp only [paramB, Bool.and_eq_true, decide_eq_true_eq] at h1
  show |a.raw| < 2 ^ 13
  rw [abs_lt]
  constructor <;> norm_num <;> omega

theorem allLe_of {l : List Fx} (h : l.all inputB = true) : AllLe 4096 l := by
  intro a ha
  have h1 := List.all_eq_true.mp h a ha
  simp only [inputB, Bool.and_eq_true, decide_eq_true_eq] at h1
  rw [abs_le]
  exact h1

theorem modelOk_of {m : Model} (h : modelOkB m = true) : ModelOk m := by
  simp only [modelOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨hw1, hr1, hb1, hbb1, hw2, hr2, hb2, hbb2⟩ := h
  refine ⟨⟨hw1, fun row hr => (hr1 row hr).1, hb1, hw2, fun row hr => (hr2 row hr).1, hb2⟩,
    fun row hr => vecW_of ?_, vecW_of ?_, fun row hr => vecW_of ?_, vecW_of ?_⟩
  · exact List.all_eq_true.mpr (hr1 row hr).2
  · exact List.all_eq_true.mpr hbb1
  · exact List.all_eq_true.mpr (hr2 row hr).2
  · exact List.all_eq_true.mpr hbb2

theorem example_of {e : List Fx × List Fx} (h : exampleOkB e = true) :
    (e.1.length = 8 ∧ e.2.length = 11) ∧ AllLe 4096 e.1 ∧ AllLe 4096 e.2 := by
  simp only [exampleOkB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨h1, h2⟩, allLe_of h3, allLe_of h4⟩

theorem getD_mem_or {α : Type} : ∀ (l : List α) (i : ℕ) (d : α),
    IxAICore.getD l i d ∈ l ∨ IxAICore.getD l i d = d
  | [], _, _ => Or.inr rfl
  | _ :: _, 0, _ => Or.inl (by simp [IxAICore.getD])
  | _ :: as, i + 1, d => by
    rcases getD_mem_or as i d with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

/-- **Gathered batches are `BatchOk`** when every example and the default pass `exampleOkB` and
every scheduled batch has 20 indices. -/
theorem gather_ok {examples : Batch} {d : List Fx × List Fx} {schedule : List (List ℕ)}
    (hex : examples.all exampleOkB = true) (hd : exampleOkB d = true)
    (hs : ∀ idx ∈ schedule, idx.length = 20) :
    ∀ b ∈ IxAICore.gather examples schedule d, BatchOk b := by
  have he : ∀ i : ℕ, exampleOkB (IxAICore.getD examples i d) = true := by
    intro i
    rcases getD_mem_or examples i d with h | h
    · exact List.all_eq_true.mp hex _ h
    · rw [h]; exact hd
  intro b hb
  obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hb
  refine ⟨⟨by simp only [List.length_map]; exact hs idx hidx, ?_⟩, ?_⟩
  · intro e he'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he'
    exact (example_of (he i)).1
  · intro e he'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he'
    exact (example_of (he i)).2

/-- **`Fixed::train` computes training on gathered batches**, assuming only checks of the public
inputs: the initial model passes `modelOkB`, every example and the default pass `exampleOkB`,
the schedule has 600 batches of 20 indices, and `|lr| ≤ 2^8`. -/
theorem train_refines_gather {lr : Fx} {m0 : Model} {examples : Batch}
    {d : List Fx × List Fx} {schedule : List (List ℕ)} (hlr : |lr.raw| ≤ 256)
    (hm0 : modelOkB m0 = true) (hex : examples.all exampleOkB = true)
    (hd : exampleOkB d = true) (hs : schedule.length = 600)
    (hs20 : ∀ idx ∈ schedule, idx.length = 20)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::train"
      (trainValues (IxAIAiur.mat m0.w1) (IxAIAiur.vec m0.b1) (IxAIAiur.mat m0.w2)
        (IxAIAiur.vec m0.b2) lr (IxAICore.gather examples schedule d)) h r h' calls) :
    r = encModel ((IxAICore.gather examples schedule d).foldl (Model.step lr) m0) :=
  train_spec hlr (by rw [IxAICore.gather, List.length_map]; exact hs) (modelOk_of hm0)
    (gather_ok hex hd hs20) (encModel_split m0) ev

/-! ## The full configuration -/

theorem setAt_length {α : Type} :
    ∀ (l : List α) (i : ℕ) (v : α), (IxAICore.setAt l i v).length = l.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, i + 1, v => by simp [IxAICore.setAt, setAt_length as i v]

theorem shuffleAux_length {α : Type} [Inhabited α] :
    ∀ (n : ℕ) (l : List α) (r : IxAICore.Rng), (IxAICore.shuffleAux n l r).1.length = l.length
  | 0, _, _ => rfl
  | i + 1, l, r => by
    rcases hb : r.below (i + 2) with ⟨j, r'⟩
    simp only [IxAICore.shuffleAux, hb]
    rw [shuffleAux_length i, setAt_length, setAt_length]

/-- Every epoch of a schedule over 400 examples in batches of 20 is 20 batches of 20. -/
theorem schedule_go_shape (c : IxAICore.Config) (hb : c.batch = 20) (hs : c.trainSize = 400) :
    ∀ (e : ℕ) (r : IxAICore.Rng), (IxAICore.Config.schedule.go c e r).length = 20 * e ∧
      ∀ idx ∈ IxAICore.Config.schedule.go c e r, idx.length = 20
  | 0, r => by simp [IxAICore.Config.schedule.go]
  | e + 1, r => by
    rcases hsh : IxAICore.shuffle (List.range c.trainSize) r with ⟨perm, r'⟩
    have hperm : perm.length = 400 := by
      have h1 : (IxAICore.shuffle (List.range c.trainSize) r).1.length = c.trainSize := by
        simp only [IxAICore.shuffle]
        rw [shuffleAux_length, List.length_range]
      rw [hsh] at h1
      simpa [hs] using h1
    obtain ⟨hl, hall⟩ := chunk20_shape c.trainSize 20 perm (by omega) (by omega)
    obtain ⟨ihl, ihall⟩ := schedule_go_shape c hb hs e r'
    simp only [IxAICore.Config.schedule.go, hsh, hb]
    refine ⟨by rw [List.length_append, hl, ihl]; ring, ?_⟩
    intro idx hidx
    rcases List.mem_append.mp hidx with h | h
    · exact hall idx h
    · exact ihall idx h

/-- The full schedule: 600 batches of 20 indices. -/
theorem fullSchedule_shape :
    IxAIAiur.fullConfig.schedule.length = 600 ∧
      ∀ idx ∈ IxAIAiur.fullConfig.schedule, idx.length = 20 := by
  have h := schedule_go_shape IxAIAiur.fullConfig rfl rfl IxAIAiur.fullConfig.epochs
    (IxAICore.Rng.seeded (IxAIAiur.fullConfig.seed + 7))
  unfold IxAICore.Config.schedule
  exact ⟨h.1.trans (by decide), h.2⟩

/-- The full configuration's 400 training examples. -/
def fullExamples : Batch :=
  (IxAIAiur.fullConfig.data IxAICore.Triage.spec).map IxAICore.Triage.spec.example

/-- The example `gather` substitutes for an out-of-range index, as in `IxAICore.Config.stepFn`. -/
def fullDefault : List Fx × List Fx := IxAICore.Triage.spec.example default

/-- The full configuration's gathered batches: `gather examples schedule`. -/
def fullBatches : List Batch :=
  IxAICore.gather fullExamples IxAIAiur.fullConfig.schedule fullDefault

def fullLr : Fx := ⟨IxAIAiur.fullConfig.lrRaw⟩

def fullInit : Model := IxAIAiur.fullConfig.init IxAICore.Triage.spec

theorem fullInit_ok : modelOkB fullInit = true := by decide +kernel

/-! ### The examples

Evaluating the 400 examples in the kernel is slow: the kernel does not share the random
generator's state between the calls that thread it, so it recomputes it. The examples' bounds
hold for every formula the generator can draw instead: a formula of depth at most 3 has at most
15 nodes, every feature is at most its size, so every input is at most `15 · 256 = 3840`, and
the targets are one-hot. -/

open IxAICore (Formula) in
theorem atomCount_le (k : ℕ) : ∀ f : Formula, f.atomCount k ≤ f.size
  | .atom n => by
    show (if n == k then 1 else 0) ≤ 1
    split <;> omega
  | .top => by show 0 ≤ 1; omega
  | .imp a b => by
    show a.atomCount k + b.atomCount k ≤ a.size + b.size + 1
    have := atomCount_le k a
    have := atomCount_le k b
    omega
  | .and a b => by
    show a.atomCount k + b.atomCount k ≤ a.size + b.size + 1
    have := atomCount_le k a
    have := atomCount_le k b
    omega

open IxAICore (Formula) in
theorem impCount_le : ∀ f : Formula, f.impCount ≤ f.size
  | .atom _ => by show 0 ≤ 1; omega
  | .top => by show 0 ≤ 1; omega
  | .imp a b => by
    show a.impCount + b.impCount + 1 ≤ a.size + b.size + 1
    have := impCount_le a
    have := impCount_le b
    omega
  | .and a b => by
    show a.impCount + b.impCount ≤ a.size + b.size + 1
    have := impCount_le a
    have := impCount_le b
    omega

open IxAICore (Formula) in
theorem depth_le : ∀ f : Formula, f.depth ≤ f.size
  | .atom _ => by show 0 ≤ 1; omega
  | .top => by show 0 ≤ 1; omega
  | .imp a b => by
    show max a.depth b.depth + 1 ≤ a.size + b.size + 1
    have := depth_le a
    have := depth_le b
    have : max a.depth b.depth ≤ a.size + b.size := Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  | .and a b => by
    show max a.depth b.depth + 1 ≤ a.size + b.size + 1
    have := depth_le a
    have := depth_le b
    have : max a.depth b.depth ≤ a.size + b.size := Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

theorem leaf_size (k : ℕ) : (IxAICore.Formula.leaf k).size = 1 := by
  unfold IxAICore.Formula.leaf
  split <;> rfl

/-- A formula drawn at depth `d` has fewer than `2^(d+1)` nodes. -/
theorem gen_size : ∀ (d : ℕ) (r : IxAICore.Rng), (IxAICore.Formula.gen d r).1.size + 1 ≤ 2 ^ (d + 1)
  | 0, r => by
    rcases hk : r.below 4 with ⟨k, r'⟩
    simp only [IxAICore.Formula.gen, hk]
    rw [leaf_size]
    norm_num
  | d + 1, r => by
    rcases hk : r.below 5 with ⟨k, r1⟩
    rcases ha : IxAICore.Formula.gen d r1 with ⟨a, r2⟩
    rcases hb : IxAICore.Formula.gen d r2 with ⟨b, r3⟩
    have iha : a.size + 1 ≤ 2 ^ (d + 1) := by
      have := gen_size d r1
      rw [ha] at this
      exact this
    have ihb : b.size + 1 ≤ 2 ^ (d + 1) := by
      have := gen_size d r2
      rw [hb] at this
      exact this
    rw [IxAICore.Formula.gen, hk]
    simp only [ha, hb]
    have hp : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    rw [hp]
    split
    · omega
    · split
      · show a.size + b.size + 1 + 1 ≤ _
        omega
      · show a.size + b.size + 1 + 1 ≤ _
        omega

/-- Every state `sampleN` draws is drawn by one call of `sample`. -/
theorem sampleN_mem {σ : Type} (s : IxAICore.Spec σ) :
    ∀ (n : ℕ) (r : IxAICore.Rng) (x : σ), x ∈ (s.sampleN n r).1 → ∃ r', x = (s.sample r').1
  | 0, r, x, h => by simp [IxAICore.Spec.sampleN] at h
  | n + 1, r, x, h => by
    rcases h1 : s.sample r with ⟨y, r1⟩
    rcases h2 : s.sampleN n r1 with ⟨ys, r2⟩
    simp only [IxAICore.Spec.sampleN, h1, h2, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨r, by rw [h1]⟩
    · exact sampleN_mem s n r1 x (by rw [h2]; exact h)

theorem inputB_of {a : Fx} (h1 : -4096 ≤ a.raw) (h2 : a.raw ≤ 4096) : inputB a = true := by
  simp [inputB, h1, h2]

/-- **The example of a formula of at most 15 nodes passes `exampleOkB`.** -/
theorem exampleOkB_of_size {f : IxAICore.Formula} (hf : f.size ≤ 15) :
    exampleOkB (IxAICore.Triage.spec.example f) = true := by
  have hl : (IxAICore.Triage.spec.targets f).length = 11 := by
    simp only [IxAICore.Spec.targets, List.length_flatMap, List.length_map, List.length_range]
    first | rfl | decide
  have ht : ∀ a ∈ IxAICore.Triage.spec.targets f, inputB a = true := by
    intro a ha
    simp only [IxAICore.Spec.targets, List.mem_flatMap, List.mem_map] at ha
    obtain ⟨q, -, k, -, rfl⟩ := ha
    split <;> decide
  have h0 := atomCount_le 0 f
  have h1 := atomCount_le 1 f
  have h2 := atomCount_le 2 f
  have hi := impCount_le f
  have hd := depth_le f
  have hfeat : ∀ a ∈ IxAICore.Triage.spec.inputs f, inputB a = true := by
    intro a ha
    simp only [IxAICore.Spec.inputs, List.mem_map] at ha
    obtain ⟨n, hn, rfl⟩ := ha
    simp only [IxAICore.Triage.spec, IxAICore.Formula.features, List.mem_cons,
      List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply inputB_of <;> simp only [IxAICore.Fx.ofInt] <;> (try split) <;> omega
  simp only [exampleOkB, IxAICore.Spec.example, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true]
  refine ⟨⟨⟨?_, hl⟩, hfeat⟩, ht⟩
  simp [IxAICore.Spec.inputs, IxAICore.Triage.spec, IxAICore.Formula.features]

theorem triage_sample (r : IxAICore.Rng) :
    IxAICore.Triage.spec.sample r = IxAICore.Formula.gen 3 r := rfl

theorem sample_size (r : IxAICore.Rng) : (IxAICore.Triage.spec.sample r).1.size ≤ 15 := by
  rw [triage_sample]
  have h := gen_size 3 r
  rw [show (2 : ℕ) ^ (3 + 1) = 16 by norm_num] at h
  omega

/-- **Every sampled example passes `exampleOkB`**, for any number of draws and any seed. The
statement keeps `n` and `r` abstract: unifying the full configuration's examples with a
concrete `sampleN` makes the kernel evaluate the generator. -/
theorem examples_ok (n : ℕ) (r : IxAICore.Rng) :
    ((IxAICore.Triage.spec.sampleN n r).1.map IxAICore.Triage.spec.example).all exampleOkB =
      true := by
  apply List.all_eq_true.mpr
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  obtain ⟨r', rfl⟩ := sampleN_mem _ _ _ f hf
  exact exampleOkB_of_size (sample_size r')

theorem fullExamples_ok : fullExamples.all exampleOkB = true := by
  rw [fullExamples, IxAICore.Config.data]
  exact examples_ok _ _

theorem fullDefault_ok : exampleOkB fullDefault = true := by decide +kernel

theorem fullLr_le : |fullLr.raw| ≤ 256 := by
  show |(2 : ℤ)| ≤ 256
  norm_num

/-- **`Fixed::train` computes `IxAICore.train`.** On the full configuration's initial model,
learning rate and gathered batches, as `IxAIAiur.checkTrain` passes them, every observed
derivation of `Fixed::train` returns the encoding of
`IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig`. -/
theorem train_refines {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::train"
      (trainValues (IxAIAiur.mat fullInit.w1) (IxAIAiur.vec fullInit.b1)
        (IxAIAiur.mat fullInit.w2) (IxAIAiur.vec fullInit.b2) fullLr fullBatches) h r h' calls) :
    r = encModel (IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig) := by
  have hspec := train_refines_gather fullLr_le fullInit_ok fullExamples_ok fullDefault_ok
    fullSchedule_shape.1 fullSchedule_shape.2 ev
  rw [IxAICore.train_eq_foldl_gather]
  exact hspec

end IxAIStep.Fixed.TrainSpec
